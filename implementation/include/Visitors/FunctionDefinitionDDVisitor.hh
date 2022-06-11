// FunctionDefinitionDDVisitor.hh
// Deduplicates transformed function definitions by removing each
// transformed macro's "non-canonical" transformations

#pragma once

#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Rewrite/Core/Rewriter.h"

#include <map>

namespace Visitors
{
    class FunctionDefinitionDDVisitor
        : public clang::RecursiveASTVisitor<FunctionDefinitionDDVisitor>
    {
    private:
        clang::Rewriter &RW;
        std::set<std::string> &TransformedDeclNames;
        std::set<clang::Decl *> &CanonicalDecls;

    public:
        explicit FunctionDefinitionDDVisitor(
            clang::Rewriter &RW,
            std::set<std::string> &TransformedDeclNames,
            std::set<clang::Decl *> &CanonicalDecls);

        bool VisitNamedDecl(clang::NamedDecl *ND);
    };
} // namespace Visitors