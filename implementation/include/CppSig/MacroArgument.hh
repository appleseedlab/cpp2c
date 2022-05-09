#pragma once

#include "Utils/SourceRangeCollection.hh"

#include "clang/AST/Expr.h"
#include "clang/Basic/SourceLocation.h"

#include <set>
#include <string>

namespace CppSig
{
    // A macro argument
    class MacroArgument
    {
        friend class MacroExpansionNode;
        friend class MacroForest;

        // The name of the argument
        std::string Name;

        // The spelling ranges of the argument's tokens where the calling
        // macro was invoked. For instance, for the invocation
        // `FOO(BAR, BAZ)`, would be the locations where BAR and BAZ
        // were invoked (I think?)
        Utils::SourceRangeCollection TokenRanges;

        // Set of AST node(s) that this argument parses to once expanded.
        // There could be multiple AST nods if the argument is appears
        // multiple times in the body, or none if the argument is unused.
        std::set<const clang::Stmt *> Stmts;

        // Where the argument is spelled in the source code according to Clang.
        clang::SourceLocation SpellingLoc;

        // The raw text behind this macro argument
        std::string RawText;

    public:
        MacroArgument(const std::string &Name);
        std::string getName();
        Utils::SourceRangeCollection getTokenRanges();
        Utils::SourceRangeCollection *getTokenRangesPtr();
        Utils::SourceRangeCollection &getTokenRangesRef();
        std::set<const clang::Stmt *> getStmts();
        std::set<const clang::Stmt *> &getStmtsRef();
        std::string getRawText();
    };
} // namespace CppSig