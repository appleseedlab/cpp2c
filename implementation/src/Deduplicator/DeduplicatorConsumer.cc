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
        // Map each transformed macro to its "canonical declaration", i.e.
        // the transformed declaration to keep when deduplicating
        for (auto &&it : MTMV.getMacroHashToTransformedDeclsRef())
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
            // If we didn't find a canonical decl, then assign the first one in
            // the vector of transformed decls to be the canonical decl
            if (CanonD == nullptr)
            {
                CanonD = TransformedDecls.front();

                // Update the canonical decl's JSON annotation
                DeclToJSON[CanonD]["canonical"] = true;
                DeclToJSON[CanonD]["deduped definitions"] = 0U;
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

        // Remove all noncanonical transformed definitions
        auto FDDV = Visitors::FunctionDefinitionDDVisitor(RW,
                                                          TransformedDeclToCanonicalDecl,
                                                          DeclToJSON);
        FDDV.TraverseTranslationUnitDecl(TUD);

        // Replace calls/var derefs to deduplicated definitions with their
        // canonical counterparts
        auto DRECEDV = Visitors::DeclRefExprAndCallExprDDVisitor(RW, TransformedDeclToCanonicalDecl);
        DRECEDV.TraverseTranslationUnitDecl(TUD);

        // Write changes to all canonical decls' JSON annotations
        for (auto &&it : MacroHashToCanonDecl)
        {
            auto ND = it.second;
            // Get the new annotation
            auto j = DeclToJSON[ND];
            // Dump it to a string
            auto newAnnotationString = Utils::escape_json(j.dump());

            // Replace the decl's annotation with the new one
            ND->dropAttrs();
            auto Atty = clang::AnnotateAttr::Create(Ctx, newAnnotationString);
            ND->addAttr(Atty);

            // Print the new decl to a string
            std::string S;
            llvm::raw_string_ostream SS(S);
            ND->print(SS);

            auto &SM = Ctx.getSourceManager();
            // Get the range the decl originally covered
            auto ReplacementRange = SM.getExpansionRange(ND->getSourceRange());

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
