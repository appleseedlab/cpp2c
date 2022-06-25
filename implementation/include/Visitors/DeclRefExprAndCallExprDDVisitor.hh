// DeclRefExprAndCallExprDDVisitor.hh
// Replaces decl refs / calls to deduplicated decls with the name
// of their transformed macro's canonical decl

#pragma once

#include "nlohmann/single_include/json.hpp"

#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Rewrite/Core/Rewriter.h"

namespace Visitors
{
    class DeclRefExprAndCallExprDDVisitor
        : public clang::RecursiveASTVisitor<DeclRefExprAndCallExprDDVisitor>
    {
    private:
        clang::Rewriter &RW;
        std::map<clang::NamedDecl *, clang::NamedDecl *> &TransformedDeclToCanonicalDecl;
        std::map<clang::NamedDecl *, nlohmann::json> &TransformedDeclToJSON;

    public:
        explicit DeclRefExprAndCallExprDDVisitor(
            clang::Rewriter &RW,
            std::map<clang::NamedDecl *, clang::NamedDecl *> &TransformedDeclToCanonicalDecl,
            std::map<clang::NamedDecl *, nlohmann::json> &TransformedDeclToJSON);

        bool VisitDeclRefExpr(clang::DeclRefExpr *DRE);
    };
} // namespace Visitors