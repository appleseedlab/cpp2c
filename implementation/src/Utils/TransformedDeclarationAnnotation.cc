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
            {"macro definition file", TDA.MacroDefinitionDefinitionFileName},
            {"macro definition number", TDA.MacroDefinitionNumber},
            {"transformed signature", TDA.TransformedSignature}};
    }

    void from_json(
        const nlohmann::json &j,
        TransformedDeclarationAnnotation &TDA)
    {
        j.at("macro name").get_to(TDA.NameOfOriginalMacro);
        j.at("macro type").get_to(TDA.MacroType);
        j.at("macro definition file").get_to(TDA.MacroDefinitionDefinitionFileName);
        j.at("macro definition number").get_to(TDA.MacroDefinitionNumber);
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
               TDA.MacroDefinitionDefinitionFileName + ";" +
               std::to_string(TDA.MacroDefinitionNumber);
    }

    std::string hashTDA(const TransformedDeclarationAnnotation &TDA)
    {
        return TDA.NameOfOriginalMacro + ";" +
               TDA.MacroType + ";" +
               TDA.TransformedSignature + ';' +
               TDA.MacroDefinitionDefinitionFileName + ";" +
               std::to_string(TDA.MacroDefinitionNumber);
    }

} // namespace Utils
