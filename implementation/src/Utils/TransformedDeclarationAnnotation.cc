#include "Utils/TransformedDeclarationAnnotation.hh"

namespace Utils
{

    void to_json(
        nlohmann::json &j,
        const TransformedDeclarationAnnotation &TDA)
    {
        j = nlohmann::json{
            {"emitted by CPP2C", true},
            {"macro name", TDA.NameOfOriginalMacro},
            {"macro type", TDA.MacroType},
            {"macro definition realpath", TDA.MacroDefinitionRealPath},
            {"macro definition number", TDA.MacroDefinitionNumber},
            {"transformed definition realpath", TDA.TransformedDefinitionRealPath},
            {"transformed signature", TDA.TransformedSignature}};
    }

    void from_json(
        const nlohmann::json &j,
        TransformedDeclarationAnnotation &TDA)
    {
        j.at("macro name").get_to(TDA.NameOfOriginalMacro);
        j.at("macro type").get_to(TDA.MacroType);
        j.at("macro definition realpath").get_to(TDA.MacroDefinitionRealPath);
        j.at("macro definition number").get_to(TDA.MacroDefinitionNumber);
        j.at("transformed definition realpath").get_to(TDA.TransformedDefinitionRealPath);
        j.at("transformed signature").get_to(TDA.TransformedSignature);
    }

    std::string escape_json(const std::string &s)
    {
        std::ostringstream o;
        for (auto c = s.cbegin(); c != s.cend(); c++)
        {
            if (*c == '"')
            {
                o << "\\\"";
            }
            else if (*c == '\\')
            {
                o << "\\\\";
            }
            else if (('\x00' <= *c && *c <= '\x1f'))
            {
                // NOTE: Clang will actually throw an error if it sees a unicode
                // character, so we emit an underscore instead
                // o << "\\u"
                //   << std::hex << std::setw(4) << std::setfill('0') << static_cast<int>(*c);
                o << "_";
            }
            else
            {
                o << *c;
            }
        }
        return o.str();
    }

    std::string hashTDAOriginalMacro(const TransformedDeclarationAnnotation &TDA)
    {
        return TDA.NameOfOriginalMacro + ";" +
               TDA.MacroType + ";" +
               TDA.MacroDefinitionRealPath + ";" +
               std::to_string(TDA.MacroDefinitionNumber);
    }

    std::string hashTDA(const TransformedDeclarationAnnotation &TDA)
    {
        return TDA.NameOfOriginalMacro + ";" +
               TDA.MacroType + ";" +
               TDA.MacroDefinitionRealPath + ";" +
               std::to_string(TDA.MacroDefinitionNumber) + ';' +
               TDA.TransformedDefinitionRealPath + ';' +
               TDA.TransformedSignature;
    }

    std::string hashTDAFromJSON(const nlohmann::json &j)
    {
        TransformedDeclarationAnnotation TDA;
        from_json(j, TDA);
        return hashTDA(TDA);
    }

    std::string getFirstAnnotationOrEmpty(clang::Decl *D)
    {
        for (auto &&it : D->attrs())
        {
            if (auto Atty = clang::dyn_cast_or_null<clang::AnnotateAttr>(it))
            {
                return Atty->getAnnotation().str();
            }
        }
        return "";
    }

    nlohmann::json annotationStringToJson(std::string annotation)
    {
        // Remove all the parts of the annotation around the JSON string
        std::size_t JSONBegin = annotation.find_first_of('{');
        std::size_t JSONEnd = annotation.find_last_of('}');
        auto JSONLen = JSONEnd - JSONBegin + 1;
        auto JSONString = annotation.substr(JSONBegin, JSONLen);
        return nlohmann::json::parse(JSONString);
    }

} // namespace Utils
