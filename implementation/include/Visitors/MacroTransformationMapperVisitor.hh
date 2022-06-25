// MacroTransformationMapperVisitor.hh
// Maps hashes of transformed macro definitions to a vector of the
// declarations of the functions/variables they were transformed to,
// and maps transformed decls to the hashes of the macros they were
// transformed from

#pragma once

#include "nlohmann/single_include/json.hpp"

#include "clang/AST/RecursiveASTVisitor.h"

#include <map>

namespace Visitors
{
    class MacroTransformationMapperVisitor
        : public clang::RecursiveASTVisitor<MacroTransformationMapperVisitor>
    {
    private:
        std::map<std::string, std::vector<clang::NamedDecl *>> MacroHashToTransformedDecls;
        std::map<clang::NamedDecl *, std::string> TransformedDeclToMacroHash;
        std::map<clang::NamedDecl *, nlohmann::json> TransformedDeclToJSONAnnotation;

    public:
        bool VisitNamedDecl(clang::NamedDecl *ND);

        std::map<std::string, std::vector<clang::NamedDecl *>> &getMacroHashToTransformedDeclsRef();
        std::map<clang::NamedDecl *, std::string> &getTransformedDeclToMacroHashRef();
        std::map<clang::NamedDecl *, nlohmann::json> &getTransformedDeclToJSONAnnotationRef();
    };
} // namespace Visitors