// DeclRefExprAndCallExprDDVisitor.hh
// Replaces decl refs / calls to deduplicated decls with the name
// of their transformed macro's canonical decl

#pragma once

#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Rewrite/Core/Rewriter.h"

namespace Visitors
{
    class DeclRefExprAndCallExprDDVisitor
        : public clang::RecursiveASTVisitor<DeclRefExprAndCallExprDDVisitor>
    {
    private:
        clang::Rewriter &RW;
        std::map<std::string, std::string> &TransformedDeclNameToCanonicalName;

    public:
        explicit DeclRefExprAndCallExprDDVisitor(
            clang::Rewriter &RW,
            std::map<std::string, std::string> &TransformedDeclNameToCanonicalName);

        bool VisitExpr(clang::Expr *E);
    };
} // namespace Visitors