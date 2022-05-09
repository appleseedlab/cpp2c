
#include "Callbacks/MacroNameCollector.hh"
#include "Utils/ExpansionUtils.hh"

namespace Callbacks
{
    using namespace clang;
    using namespace std;
    using Utils::hashMacro;
    using Utils::isInStdHeader;

    MacroNameCollector::MacroNameCollector(
        set<string> &MacroNames,
        set<string> &MultiplyDefinedMacros,
        map<string, set<string>> &MacroDefinitionToTransformedDefinitionPrototypes,
        SourceManager &SM,
        const LangOptions &LO,
        bool OnlyCollectNotDefinedInStdHeaders)
        : MacroNames(MacroNames),
          MultiplyDefinedMacros(MultiplyDefinedMacros),
          MacroDefinitionToTransformedDefinitionPrototypes(MacroDefinitionToTransformedDefinitionPrototypes),
          SM(SM),
          LO(LO),
          OnlyCollectNotDefinedInStdHeaders(OnlyCollectNotDefinedInStdHeaders){};

    void MacroNameCollector::MacroDefined(const Token &MacroNameTok, const MacroDirective *MD)
    {
        if (const IdentifierInfo *II = MacroNameTok.getIdentifierInfo())
        {
            string MacroName = II->getName().str();
            MacroNames.insert(MacroName);
            if (MD && MD->getPrevious())
            {
                MultiplyDefinedMacros.insert(MacroName);
            }
        }
        // TODO: Only emit macro definition if verbose
        llvm::errs() << "CPP2C:"
                     << "Macro Definition,"
                     << '"' << hashMacro(MD->getMacroInfo(), SM, LO) << '"' << ','
                     << MD->getMacroInfo()->getDefinitionLoc().printToString(SM) << "\n";

        if (OnlyCollectNotDefinedInStdHeaders)
        {
            if (auto MI = MD->getMacroInfo())
            {
                if (!isInStdHeader(MI->getDefinitionLoc(), SM))
                {
                    string key = hashMacro(MD->getMacroInfo(), SM, LO);
                    MacroDefinitionToTransformedDefinitionPrototypes[key] = {};
                }
            }
        }
        else
        {
            string key = hashMacro(MD->getMacroInfo(), SM, LO);
            MacroDefinitionToTransformedDefinitionPrototypes[key] = {};
        }
    }
} // namespace Callbacks
