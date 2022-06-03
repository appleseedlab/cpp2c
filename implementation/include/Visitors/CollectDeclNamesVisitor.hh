#pragma once

#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"

#include <set>
#include <string>

namespace Visitors
{
    // Visitor class which collects the names of all variables and functions
    // declared in a program
    class CollectDeclNamesVisitor
        : public clang::RecursiveASTVisitor<CollectDeclNamesVisitor>
    {
    private:
        clang::ASTContext *Ctx;
        std::set<std::string> *FunctionNames;
        std::set<std::string> *VarNames;

    public:
        explicit CollectDeclNamesVisitor(
            clang::CompilerInstance *CI,
            std::set<std::string> *FunctionNames,
            std::set<std::string> *VarNames);

        bool VisitFunctionDecl(clang::FunctionDecl *FDecl);

        bool VisitVarDecl(clang::VarDecl *VD);
    };
} // namespace Visitors