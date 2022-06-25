// ForwardDeclDDVisitor.hh
// Deduplicates struct/union/enum forward decls emitted by Cpp2C

#pragma once

#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Rewrite/Core/Rewriter.h"

namespace Visitors
{
    class ForwardDeclDDVisitor
        : public clang::RecursiveASTVisitor<ForwardDeclDDVisitor>
    {
    private:
        clang::Rewriter &RW;

    public:
        explicit ForwardDeclDDVisitor(clang::Rewriter &RW);

        bool VisitTagDecl(clang::TagDecl *TD);
    };
} // namespace Visitors