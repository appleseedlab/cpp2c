
#include "Callbacks/MacroNameCollector.hh"
#include "Utils/ExpansionUtils.hh"
#include "Utils/Logging/TransformerMessages.hh"

namespace Callbacks
{
    using namespace clang;
    using namespace std;
    using Utils::hashMacro;
    using Utils::isInStdHeader;
    using Utils::Logging::emitMacroDefinitionMessage;

    MacroNameCollector::MacroNameCollector(
        set<string> &MacroNames,
        set<string> &MultiplyDefinedMacros,
        SourceManager &SM,
        const LangOptions &LO)
        : MacroNames(MacroNames),
          MultiplyDefinedMacros(MultiplyDefinedMacros),
          SM(SM),
          LO(LO){};

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
        emitMacroDefinitionMessage(llvm::errs(), MD, SM, LO);
    }
} // namespace Callbacks
