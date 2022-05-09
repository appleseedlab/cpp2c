#pragma once

#include "MacroArgument.hh"
#include "Utils/SourceRangeCollection.hh"

#include "clang/AST/Expr.h"
#include "clang/Basic/SourceLocation.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Lex/MacroInfo.h"

#include "llvm/Support/raw_ostream.h"

#include <set>
#include <string>
#include <vector>

namespace CppSig
{
    // A forest of Expansions
    class MacroExpansionNode
    {
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
        std::vector<MacroExpansionNode *> Children;

        // Only valid for the root.
        // Vector of all macros that were expanded under this expansion.
        // Includes all descendants; not just direct ones, and the root itself.
        std::vector<MacroExpansionNode *> SubtreeNodes;

        // Name of the invoked macro
        std::string Name;

        // Where the macro was defined
        clang::SourceRange DefinitionRange;

        // Where the macro was spelled (i.e, the source range that the call
        // covers pre-expansion, I think)
        clang::SourceRange SpellingRange;

        // Collection of the spelling ranges of all the tokens
        // in all the macro's arguments.
        // Ranges of overlapping tokens (end == begin) are merged
        Utils::SourceRangeCollection ArgSpellingLocs;

        // Pointer to the macro's info
        clang::MacroInfo *MI;

        // Vector of the macro's arguments
        std::vector<MacroArgument> Arguments;

        // Raw text of the macro's definition
        std::string DefinitionText;

        // Set of AST node(s) that were found to have been directly
        // expanded from this macro. If the macro is unambiguous, this
        // should only be one
        std::set<const clang::Stmt *> Stmts;

    public:
        MacroExpansionNode *getRoot();
        MacroExpansionNode *getParent();
        std::vector<MacroExpansionNode *> getSubtreeNodes();
        std::vector<MacroExpansionNode *> &getSubtreeNodesRef();
        std::string getName();
        clang::SourceRange getDefinitionRange();
        clang::SourceRange getSpellingRange();
        Utils::SourceRangeCollection getArgSpellingLocs();
        clang::MacroInfo *getMI();
        std::string getDefinitionText();
        std::vector<MacroArgument> getArguments();
        std::vector<MacroArgument> &getArgumentsRef();
        std::set<const clang::Stmt *> getStmts();
        std::set<const clang::Stmt *> &getStmtsRef();

        // Dump information about the node and its argument
        void dump(clang::SourceManager &SM);

        // Dump the node to llvm::errs() and then recursively dump its children
        void dump_tree(unsigned depth) const;
    };

    // Dumps the given prefix to llvm::errs() and the the given Range object
    // (e.g., SourceRange, CharSourceRange, etc.) to it as well
    template <typename T>
    static void dumpRange(clang::SourceManager &SM, std::string prefix, T &Range)
    {
        llvm::errs() << "| " << prefix;
        Range.dump(SM);
    }
} // namespace CppSig