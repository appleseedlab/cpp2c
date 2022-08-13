#pragma once

#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Rewrite/Core/Rewriter.h"

#include <map>
#include <string>

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
        
        // Mapping from anonymous TagDecls to the names to use to
        // deanonymize them.
        // We need this to handle structs that are anonymous, typedef'd,
        // and then have their typedefs typedef'd.
        // if we were to naively deanonymize every anonymous struct we see,
        // we would deanonymize such structs twice.
        std::map<const clang::TagDecl *, std::string> TagDeclToName;

    public:
        explicit DeanonymizerVisitor(
            clang::ASTContext &Ctx,
            clang::Rewriter &RW);

        bool VisitTypedefDecl(clang::TypedefDecl *TD);

        // Actually deanonymizes all typedef'd anonymous struct it finds.
        void Deanonymize();
    };
} // namespace Visitors