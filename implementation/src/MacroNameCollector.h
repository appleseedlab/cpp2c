#include "clang/Lex/PPCallbacks.h"

using namespace clang;
using namespace std;

class MacroNameCollector : public PPCallbacks
{

private:
    set<string> &MacroNames;
    set<string> &MultiplyDefinedMacros;

public:
    MacroNameCollector(set<string> &MacroNames,
                       set<string> &MultiplyDefinedMacros)
        : MacroNames(MacroNames),
          MultiplyDefinedMacros(MultiplyDefinedMacros){};

    void MacroDefined(
        const Token &MacroNameTok, const MacroDirective *MD) override
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
    }
};