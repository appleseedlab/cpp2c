#pragma once

#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Rewrite/Core/Rewriter.h"

#include <set>
#include <string>

namespace Visitors
{
    // Visitor class which collects all declarations with annotations
    // emitted by Cpp2C
    class CollectCpp2CAnnotatedDeclsVisitor
        : public clang::RecursiveASTVisitor<CollectCpp2CAnnotatedDeclsVisitor>
    {
    private:
        clang::ASTContext &Ctx;
        std::vector<clang::NamedDecl *> Decls;

    public:
        explicit CollectCpp2CAnnotatedDeclsVisitor(clang::ASTContext &Ctx);

        // Collect struct/union/enum forward declarations
        // and transformed function declarations
        bool VisitNamedDecl(clang::NamedDecl *D);

        std::vector<clang::NamedDecl *> &getDeclsRef();
    };
} // namespace Visitors