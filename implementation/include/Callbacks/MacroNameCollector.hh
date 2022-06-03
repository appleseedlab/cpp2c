#pragma once

#include "clang/Basic/LangOptions.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Lex/MacroInfo.h"
#include "clang/Lex/PPCallbacks.h"
#include "clang/Lex/Token.h"

#include <map>
#include <set>
#include <string>

namespace Callbacks
{
    class MacroNameCollector : public clang::PPCallbacks
    {

    private:
        std::set<std::string> &MacroNames;
        std::set<std::string> &MultiplyDefinedMacros;
        clang::SourceManager &SM;
        const clang::LangOptions &LO;

    public:
        MacroNameCollector(std::set<std::string> &MacroNames,
                           std::set<std::string> &MultiplyDefinedMacros,
                           clang::SourceManager &SM,
                           const clang::LangOptions &LO);

        void MacroDefined(const clang::Token &MacroNameTok, const clang::MacroDirective *MD) override;
    };
} // namespace Callbacks
