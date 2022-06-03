#pragma once

#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Rewrite/Core/Rewriter.h"

namespace Visitors
{
    class DeanonymizerVisitor
        : public clang::RecursiveASTVisitor<DeanonymizerVisitor>
    {
        // Visitor class which makes any anonymous struct/union/enum
        // declarations that are declared under a typedef not anonymous
    private:
        clang::ASTContext &Ctx;
        clang::Rewriter &RW;

    public:
        explicit DeanonymizerVisitor(
            clang::ASTContext &Ctx,
            clang::Rewriter &RW);

        bool VisitTypedefDecl(clang::TypedefDecl *TD);
    };
} // namespace Visitors