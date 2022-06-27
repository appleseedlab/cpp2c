#include "Visitors/MacroTransformationMapperVisitor.hh"
#include "Utils/ExpansionUtils.hh"
#include "Utils/TransformedDeclarationAnnotation.hh"

#include "nlohmann/single_include/json.hpp"

namespace Visitors
{
    bool MacroTransformationMapperVisitor::VisitNamedDecl(clang::NamedDecl *ND)
    {
        // Only visit transformed decls, not definitions
        if (auto VD = clang::dyn_cast_or_null<clang::VarDecl>(ND))
        {
            if (VD->hasInit())
            {
                return true;
            }
        }
        else if (auto FD = clang::dyn_cast_or_null<clang::FunctionDecl>(ND))
        {
            if (FD->isThisDeclarationADefinition())
            {
                return true;
            }
        }

        // Get this decl's first annotation
        std::string annotation = Utils::getFirstAnnotationOrEmpty(ND);
        // Check that this annotation is in fact one that was
        // emitted by Cpp2C
        if (annotation.find("emitted by CPP2C") != std::string::npos)
        {
            nlohmann::json j = Utils::annotationStringToJson(annotation);

            // Create the unique macro hash based on data in
            // the JSON object
            Utils::TransformedDeclarationAnnotation TDA;
            Utils::from_json(j, TDA);
            std::string hash = Utils::hashTDA(TDA);

            // Add it to the list of transformed declarations for
            // this macro
            MacroHashToTransformedDecls[hash].push_back(ND);
            // Map this transformed decl to its macro hash
            TransformedDeclToMacroHash[ND] = hash;
            // Map this transformed decl to its JSON annotation
            TransformedDeclToJSONAnnotation[ND] = j;
        }
        return true;
    }

    std::map<std::string, std::vector<clang::NamedDecl *>>
        &MacroTransformationMapperVisitor::getMacroHashToTransformedDeclsRef()
    {
        return MacroHashToTransformedDecls;
    }

    std::map<clang::NamedDecl *, std::string>
        &MacroTransformationMapperVisitor::getTransformedDeclToMacroHashRef()
    {
        return TransformedDeclToMacroHash;
    }

    std::map<clang::NamedDecl *, nlohmann::json>
        &MacroTransformationMapperVisitor::getTransformedDeclToJSONAnnotationRef()
    {
        return TransformedDeclToJSONAnnotation;
    }

} // namespace Visitors
