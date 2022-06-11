// MacroTransformationMapperVisitor.hh
// Maps hashes of transformed macro definitions to a vector of the
// declarations of the functions/variables they were transformed to,
// and maps transformed decls to the hashes of the macros they were
// transformed from

#pragma once

#include "clang/AST/RecursiveASTVisitor.h"

#include <map>

namespace Visitors
{
    class MacroTransformationMapperVisitor
        : public clang::RecursiveASTVisitor<MacroTransformationMapperVisitor>
    {
    private:
        std::map<std::string, std::vector<clang::Decl *>> TransformedMacroMap;
        std::map<clang::Decl *, std::string> TransformedDeclToMacroHash;

    public:
        bool VisitDecl(clang::Decl *D);

        std::map<std::string, std::vector<clang::Decl *>> &getTransformedMacroMapRef();
        std::map<clang::Decl *, std::string> &getTransformedDeclToMacroHashRef();
    };
} // namespace Visitors