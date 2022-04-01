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
    map<string, unsigned> &MacroNameTypeToCount;

public:
    MacroNameCollector(set<string> &MacroNames,
                       set<string> &MultiplyDefinedMacros,
                       map<string, unsigned> &MacroNameTypeToCount)
        : MacroNames(MacroNames),
          MultiplyDefinedMacros(MultiplyDefinedMacros),
          MacroNameTypeToCount(MacroNameTypeToCount){};

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
            string key = MacroName;
            if (auto MI = MD->getMacroInfo())
            {
                key += "+";
                key += MI->isObjectLike() ? "ObjectLike" : "FunctionLike";
            }
            if (MacroNameTypeToCount.find(key) == MacroNameTypeToCount.end())
            {
                MacroNameTypeToCount[key] = 0;
            }
            MacroNameTypeToCount[key] += 1;
        }
    }
};