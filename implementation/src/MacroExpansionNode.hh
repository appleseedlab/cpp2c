#pragma once

#include <set>

#include "clang/Basic/SourceManager.h"
#include "clang/Lex/MacroInfo.h"

#include "MacroArgument.hh"
#include "SourceRangeCollection.hh"

using namespace std;
using namespace clang;
using namespace llvm;

// A forest of Expansions
class MacroExpansionNode
{
    friend class TransformedDefinition;
    friend class Cpp2CConsumer;
    friend class MacroForest;

    // How deeply this node is nested in terms of macro invocations
    // TODO: Confirm if this starts at 0
    unsigned NestingLevel;

    // The root of this macro forest (i.e., the top-level expansion)
    MacroExpansionNode *Root;

    // The direct parent expansion of this expansion.
    // If this expansion is the root, then its parent expansion is
    // the nullptr
    MacroExpansionNode *Parent; //<! Direct Parent Expansion

    // Vector of macros that were expanded directly under this expansion
    vector<MacroExpansionNode *> Children;

    // Only valid for the root.
    // Vector of all macros that were expanded under this expansion.
    // Includes all descendants; not just direct ones, and the root itself.
    vector<MacroExpansionNode *> SubtreeNodes;

    // Name of the invoked macro
    string Name;

    // Where the macro was defined
    SourceRange DefinitionRange;

    // Where the macro was spelled (i.e, the source range that the call
    // covers pre-expansion, I think)
    SourceRange SpellingRange;

    // Collection of the spelling ranges of all the tokens
    // in all the macro's arguments.
    // Ranges of overlapping tokens (end == begin) are merged
    SourceRangeCollection ArgSpellingLocs;

    // Pointer to the macro's info
    MacroInfo *MI;

    // Vector of the macro's arguments
    vector<MacroArgument> Arguments;

    // Raw text of the macro's definition
    string DefinitionText;

    // Set of AST node(s) that were found to have been directly
    // expanded from this macro. If the macro is unambiguous, this
    // should only be one
    set<const Stmt *> Stmts;

public:
    MacroExpansionNode *getRoot();
    MacroExpansionNode *getParent();
    string getName();
    SourceRange getDefinitionRange();
    SourceRange getSpellingRange();
    SourceRangeCollection getArgSpellingLocs();
    MacroInfo *getMI();
    vector<MacroArgument> getArguments();
    set<const Stmt *> getStmts();

    // Dump information about the node and its argument
    void dump(SourceManager &SM);

    // Dump the node to llvm::errs() and then recursively dump its children
    void dump_tree(unsigned depth) const;
};

// Dumps the given prefix to llvm::errs() and the the given Range object
// (e.g., SourceRange, CharSourceRange, etc.) to it as well
template <typename T>
static void dumpRange(SourceManager &SM, std::string prefix, T &Range)
{
    errs() << "| " << prefix;
    Range.dump(SM);
}
