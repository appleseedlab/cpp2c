// FunctionDefinitionDDVisitor.hh
// Deduplicates transformed function definitions by removing each
// transformed macro's "non-canonical" transformations

#pragma once

#include "nlohmann/single_include/json.hpp"

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
        std::map<clang::NamedDecl *, clang::NamedDecl *> &TransformedDeclToCanonicalDecl;
        std::map<clang::NamedDecl *, nlohmann::json> &TransformedDeclToJSON;

    public:
        explicit FunctionDefinitionDDVisitor(
            clang::Rewriter &RW,
            std::map<clang::NamedDecl *, clang::NamedDecl *> &TransformedDeclToCanonicalDecl,
            std::map<clang::NamedDecl *, nlohmann::json> &TransformedDeclToJSON);

        bool VisitNamedDecl(clang::NamedDecl *ND);
    };
} // namespace Visitors