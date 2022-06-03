#include "AnnotationRemover/AnnotationRemoverConsumer.hh"
#include "Visitors/CollectCpp2CAnnotatedDeclsVisitor.hh"

#include "clang/Rewrite/Core/Rewriter.h"

namespace AnnotationRemover
{

    AnnotationRemoverConsumer::AnnotationRemoverConsumer(
        AnnotationRemoverSettings ARSettings) : ARSettings(ARSettings) {}

    void AnnotationRemoverConsumer::HandleTranslationUnit(clang::ASTContext &Ctx)
    {
        auto TUD = Ctx.getTranslationUnitDecl();
        Visitors::CollectCpp2CAnnotatedDeclsVisitor DAC(Ctx);
        DAC.TraverseTranslationUnitDecl(TUD);

        auto &SM = Ctx.getSourceManager();
        auto &LO = Ctx.getLangOpts();
        clang::Rewriter RW(SM, LO);
        for (auto D : DAC.getDeclsRef())
        {
            // Get the range the decl originally covered
            auto ReplacementRange = SM.getExpansionRange(D->getSourceRange());
            // Remove all its attributes
            D->dropAttrs();
            // Print the new decl to a string
            std::string S;
            llvm::raw_string_ostream SS(S);
            D->print(SS);
            // Rewrite the old decl with the new one
            auto failed = RW.ReplaceText(ReplacementRange, SS.str());
            if (failed)
            {
                llvm::errs() << "Failed to remove attribute range: ";
                ReplacementRange.getAsRange().dump(SM);
            }
        }

        if (ARSettings.OverwriteFiles)
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
} // namespace AnnotationRemover
