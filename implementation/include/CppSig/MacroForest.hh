#pragma once

#include "CppSig/MacroArgument.hh"
#include "CppSig/MacroExpansionNode.hh"
#include "Utils/SourceRangeCollection.hh"

#include "clang/AST/ASTContext.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Lex/MacroArgs.h"
#include "clang/Lex/PPCallbacks.h"

namespace CppSig
{
    class MacroExpansionNode;

    // Forest of all macro expansions in a program.
    // A "forest" of macro expansions is the tree obtained by expanding a single
    // expansion, then recursively expanding all its arguments (whether they are
    // macros or not) and nested macro invocations.
    // This class is actually more of a forest of forests, since it contains
    // all root expansions (and thus their forests) in a program.
    // I use the term "forest" to denote an arbitrary
    // macro expansion forest. I use the term "MacroForest" to denote the forest
    // of all macro expansions in a program.
    class MacroForest : public clang::PPCallbacks
    {
    public:
        // A vector of all macro expansions that are root expansions
        typedef std::vector<MacroExpansionNode *> Roots;

    private:
        // Destructor
        ~MacroForest();

        // The Clang CompilerInstance
        clang::CompilerInstance &CI;

        // Whether to emit debug messages to stderr
        bool Verbose;

        // The roots of all macro expansions in a program
        Roots &MacroRoots;

        // The Clang AST context
        clang::ASTContext &Ctx;

        // Stack for keeping track of nested expansions
        std::vector<MacroExpansionNode *> InvocationStack;

        // Stack for keeping track of which macro argument expansion we are in
        // If we are in one, the back of this stack is the current expansion
        // depth
        std::vector<unsigned> inMacroArgExpansion;

        // Given a beginning and ending source location in a program,
        // returns the range spanned by their spelling locations in the
        // program's original source code
        clang::SourceRange getSpellingRange(clang::SourceLocation S, clang::SourceLocation E);

    public:
        // Copy constructor
        // Gets the Ctx from CI
        MacroForest(
            clang::CompilerInstance &CI,
            bool Verbose,
            Roots &roots);

        // Callback called when the preprocessor encounters a macro expansion.
        // Adds the expansion to the MacroForest
        void MacroExpands(
            const clang::Token &MacroNameTok,
            const clang::MacroDefinition &MD,
            clang::SourceRange Range,
            const clang::MacroArgs *Args) override;
    };
} // namespace CppSig