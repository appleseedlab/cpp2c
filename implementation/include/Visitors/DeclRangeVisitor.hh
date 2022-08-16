#pragma once

#include "clang/AST/RecursiveASTVisitor.h"

#include <vector>

namespace Visitors
{
    class DeclRangeVisitor
        : public clang::RecursiveASTVisitor<DeclRangeVisitor>
    {
        // Collects source ranges of all decls in the AST
    private:
        clang::ASTContext &Ctx;
        std::vector<clang::SourceRange> DeclRanges;

    public:
        explicit DeclRangeVisitor(clang::ASTContext &Ctx);
        
        bool VisitDecl(clang::Decl *D);
        
        std::vector<clang::SourceRange> &getDeclRangesRef();
    };
} // namespace Visitors