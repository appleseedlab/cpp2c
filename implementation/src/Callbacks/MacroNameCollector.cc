
#include "Callbacks/MacroNameCollector.hh"
#include "Utils/ExpansionUtils.hh"
#include "Utils/Logging/TransformerMessages.hh"

namespace Callbacks
{
    using namespace clang;
    using namespace std;

    MacroNameCollector::MacroNameCollector(
        set<string> &MacroNames,
        set<string> &MultiplyDefinedMacros,
        bool Verbose,
        SourceManager &SM,
        const LangOptions &LO)
        : MacroNames(MacroNames),
          MultiplyDefinedMacros(MultiplyDefinedMacros),
          Verbose(Verbose),
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
            if (Verbose)
            {
                Utils::Logging::emitMacroDefinitionMessage(llvm::errs(), MacroName, MD, SM, LO);
            }
        }
    }
} // namespace Callbacks
