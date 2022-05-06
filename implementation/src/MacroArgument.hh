#pragma once

#include <set>

#include "clang/AST/Stmt.h"

#include "SourceRangeCollection.hh"

using namespace std;
using namespace clang;

// A macro argument
class MacroArgument
{
    friend class Cpp2CConsumer;
    friend class MacroExpansionNode;
    friend class MacroForest;
    friend class TransformedDefinition;

    // The name of the argument
    string Name;

    // The spelling ranges of the argument's tokens where the calling
    // macro was invoked. For instance, for the invocation
    // `FOO(BAR, BAZ)`, would be the locations where BAR and BAZ
    // were invoked (I think?)
    SourceRangeCollection TokenRanges;

    // Set of AST node(s) that this argument parses to once expanded.
    // There could be multiple AST nods if the argument is appears
    // multiple times in the body, or none if the argument is unused.
    set<const Stmt *> Stmts;

    // Where the argument is spelled in the source code according to Clang.
    SourceLocation SpellingLoc;

    // The raw text behind this macro argument
    string RawText;

public:
    MacroArgument(const std::string &Name);
    set<const Stmt *> getStmts();
};