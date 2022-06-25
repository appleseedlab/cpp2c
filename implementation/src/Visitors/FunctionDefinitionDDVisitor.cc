#include "Visitors/FunctionDefinitionDDVisitor.hh"
#include "Utils/ExpansionUtils.hh"

namespace Visitors
{

    FunctionDefinitionDDVisitor::FunctionDefinitionDDVisitor(
        clang::Rewriter &RW,
        std::map<clang::NamedDecl *, clang::NamedDecl *> &TransformedDeclToCanonicalDecl,
        std::map<clang::NamedDecl *, nlohmann::json> &TransformedDeclToJSON)
        : RW(RW),
          TransformedDeclToCanonicalDecl(TransformedDeclToCanonicalDecl),
          TransformedDeclToJSON(TransformedDeclToJSON) {}

    bool FunctionDefinitionDDVisitor::VisitNamedDecl(clang::NamedDecl *ND)
    {
        // Only visit function definitions and variable initializations
        if (
            (!llvm::isa_and_nonnull<clang::FunctionDecl>(ND) ||
             !clang::dyn_cast_or_null<clang::FunctionDecl>(ND)->isThisDeclarationADefinition()) &&
            (!llvm::isa_and_nonnull<clang::VarDecl>(ND) ||
             !clang::dyn_cast_or_null<clang::VarDecl>(ND)->hasInit()))
        {
            return true;
        }

        // Get the previous declaration (should be the single declaration
        // for this transformed definition since we emit one transformed
        // decl and def per transformation)
        if (auto TransformedDecl = clang::dyn_cast_or_null<clang::NamedDecl>(ND->getPreviousDecl()))
        {
            // Only erase transformed, noncanonical decls
            if ((TransformedDeclToCanonicalDecl.find(TransformedDecl) != TransformedDeclToCanonicalDecl.end()) &&
                (!TransformedDeclToJSON[TransformedDecl].contains("canonical")))
            {
                auto &SM = RW.getSourceMgr();
                auto TransformedDeclRange = SM.getExpansionRange(TransformedDecl->getSourceRange());
                auto FDRange = SM.getExpansionRange(ND->getSourceRange());
                // Extend ranges by 1 to account for trailing semicolon
                TransformedDeclRange.setEnd(TransformedDeclRange.getEnd().getLocWithOffset(1));
                FDRange.setEnd(FDRange.getEnd().getLocWithOffset(1));
                bool failed;
                failed = RW.RemoveText(TransformedDeclRange);
                assert(!failed);
                RW.RemoveText(FDRange);
                assert(!failed);

                // Update the deduplication count for this transformed decl's
                // canonical decl
                auto CanonD = TransformedDeclToCanonicalDecl[TransformedDecl];
                TransformedDeclToJSON[CanonD]["deduped definitions"] = TransformedDeclToJSON[CanonD]["deduped definitions"].get<unsigned int>() + 1;
            }
        }
        return true;
    }

} // namespace Visitors
