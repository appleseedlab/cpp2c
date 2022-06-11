#include "Visitors/MacroTransformationMapperVisitor.hh"
#include "Utils/ExpansionUtils.hh"
#include "Utils/TransformedDeclarationAnnotation.hh"

#include "nlohmann/single_include/json.hpp"

namespace Visitors
{
    bool MacroTransformationMapperVisitor::VisitDecl(clang::Decl *D)
    {
        // Only visit transformed decls, not definitions
        if (auto VD = clang::dyn_cast_or_null<clang::VarDecl>(D))
        {
            if (VD->hasInit())
            {
                return true;
            }
        }
        else if (auto FD = clang::dyn_cast_or_null<clang::FunctionDecl>(D))
        {
            if (FD->isThisDeclarationADefinition())
            {
                return true;
            }
        }

        // Get this decl's first annotation
        std::string annotation = Utils::getFirstAnnotationOrEmpty(D);
        // Check that this annotation is in fact one that was
        // emitted by Cpp2C
        if (annotation.find("emitted by CPP2C") != std::string::npos)
        {
            try
            {
                nlohmann::json j = Utils::annotationStringToJson(annotation);

                // Create the unique macro hash based on data in
                // the JSON object
                Utils::TransformedDeclarationAnnotation TDA;
                Utils::from_json(j, TDA);
                std::string hash = Utils::hashTDA(TDA);

                // Add it to the list of transformed declarations for
                // this macro
                TransformedMacroMap[hash].push_back(D);
                TransformedDeclToMacroHash[D] = hash;
            }
            catch (nlohmann::json::parse_error &e)
            {
                llvm::errs() << e.what() << "\n";
                return true;
            }
        }
        return true;
    }

    std::map<std::string, std::vector<clang::Decl *>>
        &MacroTransformationMapperVisitor::getTransformedMacroMapRef()
    {
        return TransformedMacroMap;
    }

    std::map<clang::Decl *, std::string>
        &MacroTransformationMapperVisitor::getTransformedDeclToMacroHashRef()
    {
        return TransformedDeclToMacroHash;
    }

} // namespace Visitors
