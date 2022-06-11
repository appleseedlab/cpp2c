#include "Visitors/FunctionDefinitionDDVisitor.hh"
#include "Utils/ExpansionUtils.hh"

namespace Visitors
{

    FunctionDefinitionDDVisitor::FunctionDefinitionDDVisitor(
        clang::Rewriter &RW,
        std::set<std::string> &TransformedDeclNames,
        std::set<clang::Decl *> &CanonicalDecls)
        : RW(RW),
          TransformedDeclNames(TransformedDeclNames),
          CanonicalDecls(CanonicalDecls) {}

    bool FunctionDefinitionDDVisitor::VisitNamedDecl(clang::NamedDecl *ND)
    {
        // Only visit transformed definitions
        if (TransformedDeclNames.find(ND->getNameAsString()) ==
            TransformedDeclNames.end())
        {
            return true;
        }

        // Only visit function definitions and variable initializations
        if (
            (!llvm::isa_and_nonnull<clang::FunctionDecl>(ND) ||
             !clang::dyn_cast_or_null<clang::FunctionDecl>(ND)->isThisDeclarationADefinition()) &&
            (!llvm::isa_and_nonnull<clang::VarDecl>(ND) ||
             !clang::dyn_cast_or_null<clang::VarDecl>(ND)->hasInit()))
        {
            return true;
        }

        // Get the previous declaration (should be a single one)
        if (auto PD = ND->getPreviousDecl())
        {
            // Only erase noncanonical decls
            if (CanonicalDecls.find(PD) == CanonicalDecls.end())
            {
                // Not sure if it matters if I use ND, FD, or PD here
                auto &Ctx = ND->getASTContext();
                auto &SM = Ctx.getSourceManager();
                auto PDRange = SM.getExpansionRange(PD->getSourceRange());
                auto FDRange = SM.getExpansionRange(ND->getSourceRange());
                // Extend ranges by 1 to account for trailing semicolon
                PDRange.setEnd(PDRange.getEnd().getLocWithOffset(1));
                FDRange.setEnd(FDRange.getEnd().getLocWithOffset(1));
                bool failed;
                failed = RW.RemoveText(PDRange);
                assert(!failed);
                RW.RemoveText(FDRange);
                assert(!failed);
            }
        }
        return true;
    }

} // namespace Visitors
