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

        std::map<std::string, clang::Decl *> MacroHashToCanonDecl;
        // Map each transformed macro to its "canonical declaration", i.e.
        // the transformed declaration to keep when deduplicating
        // Also map each transformed decl to its macro hash
        for (auto &&it : MTMV.getTransformedMacroMapRef())
        {
            auto MacroHash = it.first;
            auto TransformedDecls = it.second;

            // Find the canonical decl, if one was already chosen in a prior run
            clang::Decl *CanonD = nullptr;
            for (auto &&D : TransformedDecls)
            {
                if (Utils::getFirstAnnotationOrEmpty(D).find("canonical") != std::string::npos)
                {
                    CanonD = D;
                }
            }
            // If we didn't find a canonical decl, then assign the first one in
            // the vector of transformed decls to be the canonical decl
            if (CanonD == nullptr)
            {
                CanonD = TransformedDecls.front();

                // Get the range the decl originally covered
                auto ReplacementRange = SM.getExpansionRange(CanonD->getSourceRange());

                // Get the current JSON annotation
                auto annotation = Utils::getFirstAnnotationOrEmpty(CanonD);
                auto j = Utils::annotationStringToJson(annotation);
                // Add the field '"canonical" : true' to it
                j["canonical"] = true;
                auto newAnnotationString = Utils::escape_json(j.dump());

                // Replace the decl's annotation with the new one
                CanonD->dropAttrs();
                auto Atty = clang::AnnotateAttr::Create(Ctx, newAnnotationString);
                CanonD->addAttr(Atty);

                // Print the new decl to a string
                std::string S;
                llvm::raw_string_ostream SS(S);
                CanonD->print(SS);

                // Replace the old decl with the new one
                auto failed = RW.ReplaceText(ReplacementRange, SS.str());
                if (failed)
                {
                    llvm::errs() << "Failed to remove attribute range: ";
                    ReplacementRange.getAsRange().dump(SM);
                }
            }
            MacroHashToCanonDecl[MacroHash] = CanonD;
        }

        // Create a set of all the canonical decls
        // Should all be unique anyway
        std::set<clang::Decl *> CanonicalDecls;
        for (auto &&it : MacroHashToCanonDecl)
        {
            auto CD = it.second;
            CanonicalDecls.insert(CD);
        }
        // Create a set of all transformed declaration names
        std::set<std::string> TransformedDeclNames;
        for (auto &&it : MTMV.getTransformedDeclToMacroHashRef())
        {
            auto D = it.first;
            if (auto ND = clang::dyn_cast_or_null<clang::NamedDecl>(D))
            {
                TransformedDeclNames.insert(ND->getNameAsString());
            }
        }

        // Visit each function definiton, and remove those which have a
        // previous declaration without the key "canonical" in their
        // JSON annotation
        auto FDDV = Visitors::FunctionDefinitionDDVisitor(RW, TransformedDeclNames, CanonicalDecls);
        FDDV.TraverseTranslationUnitDecl(TUD);

        // Map each transformed decl name to the name of its transformed
        // macro's canonical decl (which may just be itself)
        std::map<std::string, std::string> TransformedDeclNameToCanonicalName;
        for (auto &&it : MTMV.getTransformedDeclToMacroHashRef())
        {
            auto TD = it.first;
            auto TransformedName = clang::dyn_cast<clang::NamedDecl>(TD)->getNameAsString();

            auto MacroHash = it.second;
            auto CanonicalD = MacroHashToCanonDecl[MacroHash];
            auto CanonicalName = clang::dyn_cast<clang::NamedDecl>(CanonicalD)->getNameAsString();

            TransformedDeclNameToCanonicalName[TransformedName] = CanonicalName;
        }

        // Replace calls/var derefs to deduplicated definitions with their
        // canonical counterparts
        auto DRECEDV = Visitors::DeclRefExprAndCallExprDDVisitor(RW, TransformedDeclNameToCanonicalName);
        DRECEDV.TraverseTranslationUnitDecl(TUD);

        // TODO
        // Add the number of deduplicated decls to the JSON annotation
        // of each canonical decl

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
