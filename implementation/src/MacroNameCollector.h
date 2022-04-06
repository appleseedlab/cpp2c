#pragma once

#include <map>
#include <set>
#include <string>

using namespace clang;
using namespace std;

bool isInStdHeader(SourceLocation L, SourceManager &SM)
{
    auto FN = SM.getFilename(L);
    return (FN.str() == "" ||
            FN.startswith("/usr/include") ||
            FN.startswith("/usr/lib"));
}

string hashMacro(const MacroInfo *MI, SourceManager &SM, const LangOptions &LO)
{
    string key = MI->isObjectLike()
                     ? "ObjectLike"
                     : "FunctionLike";
    key += "+";
    string def =
        Lexer::getSourceText(
            Lexer::getAsCharRange(
                SourceRange(
                    MI->getDefinitionLoc(),
                    MI->getDefinitionEndLoc()),
                SM, LO),
            SM, LO)
            .str();
    key += def;

    // https://stackoverflow.com/a/26559133/6824430
    string result;
    size_t const len(key.length());
    result.reserve(len + 100); // assume up to 100 double quotes...
    // Use double quotes to escape special characters
    for (size_t idx(0); idx < len; ++idx)
    {
        if (key[idx] == '"')
        {
            result += "\"\"";
        }
        else if (key[idx] == '\'')
        {
            result += "''";
        }
        else if (key[idx] == '\\')
        {
            result += "\\\\";
        }
        else if (key[idx] == '\n')
        {
            result += "";
        }
        else if (key[idx] == '\t')
        {
            result += "\"\t";
        }
        else
        {
            result += key[idx];
        }
    }
    return result;
}

class MacroNameCollector : public PPCallbacks
{

private:
    set<string> &MacroNames;
    set<string> &MultiplyDefinedMacros;
    map<string, set<string>> &MacroDefinitionToTransformedDefinitionPrototypes;
    SourceManager &SM;
    const LangOptions &LO;
    bool OnlyCollectNotDefinedInStdHeaders;

public:
    MacroNameCollector(set<string> &MacroNames,
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
};