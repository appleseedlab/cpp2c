#include "Visitors/CollectReferencingDREs.hh"

namespace Visitors
{
    CollectReferencingDREs::CollectReferencingDREs(
        std::set<clang::NamedDecl *> &References)
        : References(References) {}

    bool CollectReferencingDREs::VisitDeclRefExpr(clang::DeclRefExpr *DRE)
    {
        if (References.find(DRE->getFoundDecl()) != References.end() ||
            References.find(clang::dyn_cast_or_null<clang::NamedDecl>(DRE->getFoundDecl()->getPreviousDecl())) != References.end())
        {
            DREs.insert(DRE);
        }
        return true;
    }

    std::set<clang::DeclRefExpr *> &CollectReferencingDREs::getDREsRef()
    {
        return DREs;
    }

} // namespace Visitors
