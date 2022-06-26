#include "Deduplicator/DeduplicatorConsumer.hh"
#include "Visitors/DeclRefExprAndCallExprDDVisitor.hh"
#include "Visitors/ForwardDeclDDVisitor.hh"
#include "Visitors/MacroTransformationMapperVisitor.hh"
#include "Visitors/FunctionDefinitionDDVisitor.hh"
#include "Utils/ExpansionUtils.hh"
#include "Utils/TransformedDeclarationAnnotation.hh"

#include "clang/AST/ASTContext.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/Basic/SourceManager.h"

namespace Deduplicator
{

    DeduplicatorConsumer::DeduplicatorConsumer(DeduplicatorSettings DDSettings)
        : DDSettings(DDSettings) {}

    void DeduplicatorConsumer::HandleTranslationUnit(clang::ASTContext &Ctx)
    {
        auto &SM = Ctx.getSourceManager();
        auto &LO = Ctx.getLangOpts();
        auto RW = clang::Rewriter(SM, LO);
        auto TUD = Ctx.getTranslationUnitDecl();

        // Deduplicate struct/union/enum forward declarations (TagDecls)
        auto FDV = Visitors::ForwardDeclDDVisitor(RW);
        FDV.TraverseTranslationUnitDecl(TUD);

        // Map each transformed macro to its transformed declarations
        auto MTMV = Visitors::MacroTransformationMapperVisitor();
        MTMV.TraverseTranslationUnitDecl(TUD);
        auto &DeclToJSON = MTMV.getTransformedDeclToJSONAnnotationRef();

        std::map<std::string, clang::NamedDecl *> MacroHashToCanonDecl;
        auto &MacroHashToTransformedDecl = MTMV.getMacroHashToTransformedDeclsRef();
        // Map each transformed macro to its "canonical declaration", i.e.
        // the transformed declaration to keep when deduplicating
        for (auto &&it : MacroHashToTransformedDecl)
        {
            auto MacroHash = it.first;
            auto TransformedDecls = it.second;

            // Find the canonical decl, if one was already chosen in a prior run
            clang::NamedDecl *CanonD = nullptr;
            for (auto &&D : TransformedDecls)
            {
                // The decl should definitely be in the map, so do an
                // unconditional lookup
                if (DeclToJSON[D].contains("canonical"))
                {
                    CanonD = D;
                    break;
                }
            }
            // If we didn't find a canonical decl, then assign the last one in
            // the vector of transformed decls to be the canonical decl
            if (CanonD == nullptr)
            {
                CanonD = TransformedDecls.back();

                // Update the canonical decl's JSON annotation
                DeclToJSON[CanonD]["canonical"] = true;
                DeclToJSON[CanonD]["unique transformed invocations"] = 0;
            }
            MacroHashToCanonDecl[MacroHash] = CanonD;
        }

        // Map each transformed decl to its transformed
        // macro's canonical decl (which may just be itself)
        std::map<clang::NamedDecl *, clang::NamedDecl *> TransformedDeclToCanonicalDecl;
        for (auto &&it : MTMV.getTransformedDeclToMacroHashRef())
        {
            auto TD = it.first;
            auto MacroHash = it.second;
            auto CanonicalD = MacroHashToCanonDecl[MacroHash];

            TransformedDeclToCanonicalDecl[TD] = CanonicalD;
        }

        // Replace calls/var derefs to deduplicated definitions with their
        // canonical counterparts
        auto DRECEDV = Visitors::DeclRefExprAndCallExprDDVisitor(RW,
                                                                 TransformedDeclToCanonicalDecl,
                                                                 DeclToJSON);
        DRECEDV.TraverseTranslationUnitDecl(TUD);

        // Remove all noncanonical transformed definitions
        auto FDDV = Visitors::FunctionDefinitionDDVisitor(RW,
                                                          TransformedDeclToCanonicalDecl,
                                                          DeclToJSON);
        FDDV.TraverseTranslationUnitDecl(TUD);

        // Write changes to all canonical decls' JSON annotations
        for (auto &&it : MacroHashToCanonDecl)
        {
            auto ND = it.second;
            // Get the new annotation
            auto j = DeclToJSON[ND];
            // Dump it to a string
            auto newAnnotationString = Utils::escape_json(j.dump());

            auto &SM = Ctx.getSourceManager();
            // Remove the decl's old annotations
            // (decl expansion range doesn't include this)
            for (auto &&it : ND->attrs())
            {
                clang::SourceRange RemovalRange(
                    SM.getFileLoc(it->getLocation()),
                    SM.getFileLoc(it->getRange().getEnd()));
                auto failed = RW.RemoveText(RemovalRange);
                assert(!failed);
            }

            // Get the decl's expansion range
            auto ReplacementRange = clang::SourceRange(
                SM.getFileLoc(ND->getBeginLoc()),
                SM.getFileLoc(ND->getEndLoc()));

            // Replace the decl's annotation with the new one
            ND->dropAttrs();
            auto Atty = clang::AnnotateAttr::Create(Ctx, newAnnotationString);
            ND->addAttr(Atty);

            // Print the new decl to a string
            std::string S;
            llvm::raw_string_ostream SS(S);
            ND->print(SS);

            // Replace the old decl with the new one
            auto failed = RW.ReplaceText(ReplacementRange, SS.str());
            assert(!failed);
        }

        // Rewrite changes, or print them to stdout
        if (DDSettings.OverwriteFiles)
        {
            RW.overwriteChangedFiles();
        }
        else
        {
            // Print the results of the rewriting for the current file
            if (auto RewriteBuf = RW.getRewriteBufferFor(SM.getMainFileID()))
            {
                RewriteBuf->write(llvm::outs());
            }
            else
            {
                llvm::errs() << "No changes\n";
            }
        }
    }
} // namespace Deduplicator
