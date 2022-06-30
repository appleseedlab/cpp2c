#pragma once

#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"

#include <set>
#include <string>

namespace Visitors
{
    // Visitor class which collects the names of all DeclRefExprs
    // that references one of the passed decls
    class CollectReferencingDREs
        : public clang::RecursiveASTVisitor<CollectReferencingDREs>
    {
    private:
        std::set<clang::NamedDecl *> &References;
        std::set<clang::DeclRefExpr *> DREs;

    public:
        explicit CollectReferencingDREs(std::set<clang::NamedDecl *> &References);

        bool VisitDeclRefExpr(clang::DeclRefExpr *DRE);

        std::set<clang::DeclRefExpr *> &getDREsRef();
    };
} // namespace Visitors