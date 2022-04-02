#pragma once

#include <map>
#include <set>
#include <string>

using namespace clang;
using namespace std;

class MacroNameCollector : public PPCallbacks
{

private:
    set<string> &MacroNames;
    set<string> &MultiplyDefinedMacros;
    map<string, set<string>> &MacroNamePlusTypeToTransformedDefinitionPrototypes;

public:
    MacroNameCollector(set<string> &MacroNames,
                       set<string> &MultiplyDefinedMacros,
                       map<string, set<string>> &MacroNamePlusTypeToTransformedDefinitionPrototypes)
        : MacroNames(MacroNames),
          MultiplyDefinedMacros(MultiplyDefinedMacros),
          MacroNamePlusTypeToTransformedDefinitionPrototypes(MacroNamePlusTypeToTransformedDefinitionPrototypes){};

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