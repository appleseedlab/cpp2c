#include "Visitors/FunctionDefinitionDDVisitor.hh"
#include "Deduplicator/DeduplicatorConstants.hh"
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
        if (auto PD = clang::dyn_cast_or_null<clang::NamedDecl>(ND->getPreviousDecl()))
        {
            // Only consider defs of a transformed decl
            if ((TransformedDeclToCanonicalDecl.find(PD) != TransformedDeclToCanonicalDecl.end()))
            {
                auto TransformedDecl = PD;
                auto TransformedDef = ND;
                // Only erase noncanonical defs and decls
                if (!TransformedDeclToJSON[TransformedDecl].contains(Deduplicator::Keys::CANONICAL))
                {
                    auto &SM = RW.getSourceMgr();
                    auto TransformedDeclRange = clang::SourceRange(
                        SM.getFileLoc(TransformedDecl->getBeginLoc()),
                        SM.getFileLoc(TransformedDecl->getEndLoc()));

                    // Add 1 to decl range end for trailing semicolon
                    TransformedDeclRange.setEnd(TransformedDeclRange.getEnd().getLocWithOffset(1));

                    auto TransformedDefinitionRange = clang::SourceRange(
                        SM.getFileLoc(TransformedDef->getBeginLoc()),
                        SM.getFileLoc(TransformedDef->getEndLoc()));

                    bool failed;

                    failed = RW.RemoveText(TransformedDeclRange);
                    assert(!failed);
                    failed = RW.RemoveText(TransformedDefinitionRange);
                    assert(!failed);
                }
            }
        }
        return true;
    }

} // namespace Visitors
