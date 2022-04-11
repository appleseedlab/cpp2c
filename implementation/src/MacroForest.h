#pragma once

#include "MacroNameCollector.h"

using namespace clang;
using namespace llvm;
using namespace std;

void insertIntoForest(ASTContext *Ctx, const Stmt *S, set<const Stmt *> &Forest)
{
    assert(S != nullptr);

    // Have we already recorded a Parent statement? => Skip this one
    const Stmt *ParentStmt = S;
    while (ParentStmt)
    {
        const auto &Parents = Ctx->getParents(*ParentStmt);
        // FIXME: This happens from time to time
        if (Parents.size() > 1)
        {
            return;
        }
        assert(Parents.size() <= 1); // C++?

        if (Parents.size() == 0)
        {
            // llvm::errs() << "Searched to the top\n";
            break;
        }

        if (const Stmt *S = Parents[0].get<Stmt>())
        {
            if (Forest.find(S) != Forest.end())
            {
                return;
            }
            ParentStmt = S;
        }
        else
        {
            break;
        }
    }

    Forest.insert(S);
}

// Vector of SourceRanges objects
class SourceRangeCollection : public vector<SourceRange>
{
public:
    // Returns true if one of the ranges in this vector of source ranges
    // contains Loc, false otherwise
    bool contains(const SourceLocation &Loc) const
    {
        for (const auto &Range : *this)
        {
            if (Range.getBegin() <= Loc && Loc <= Range.getEnd())
            {
                return true;
            }
        }
        return false;
    }

    // Dumps all the ranges in the vector to llvm::errs()
    void dump(SourceManager &SM)
    {
        for (const auto &Range : *this)
        {
            Range.print(llvm::errs(), SM);
            llvm::errs() << ", ";
        }
    }
};

// Dumps the given prefix to llvm::errs() and the the given Range object
// (e.g., SourceRange, CharSourceRange, etc.) to it as well
template <typename T>
static void dumpRange(SourceManager &SM, std::string prefix, T &Range)
{
    errs() << "| " << prefix;
    Range.dump(SM);
}

// Forest of all macro expansions in a program.
// A "forest" of macro expansions is the tree obtained by expanding a single
// expansion, then recursively expanding all its arguments (whether they are
// macros or not) and nested macro invocations.
// This class is actually more of a forest of forests, since it contains
// all root expansions (and thus their forests) in a program.
// I (Brent Pappas), use the term "forest" to denote an arbitrary
// macro expansion forest. I use the term "MacroForest" to denote the forest
// of all macro expansions in a program.
class MacroForest : public PPCallbacks
{
public:
    // A macro argument
    struct Argument
    {
        Argument(const std::string &Name) : Name(Name) {}
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
    };

    // A forest of Expansions
    struct Node
    {
        // How deeply this node is nested in terms of macro invocations
        // TODO: Confirm if this starts at 0
        unsigned NestingLevel;

        // The root of this macro forest (i.e., the top-level expansion)
        Node *Root;

        // The direct parent expansion of this expansion.
        // If this expansion is the root, then its parent expansion is
        // the nullptr
        Node *Parent; //<! Direct Parent Expansion

        // Vector of macros that were expanded directly under this expansion
        vector<Node *> Children;

        // Only valid for the root.
        // Vector of all macros that were expanded under this expansion.
        // Includes all descendants; not just direct ones, and the root itself.
        vector<Node *> SubtreeNodes;

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
        vector<Argument> Arguments;

        // Raw text of the macro's definition
        string DefinitionText;

        // Dump information about the node and its argument
        void dump(SourceManager &SM)
        {
            errs() << "Node " << Name << " argc: "
                   << Arguments.size() << " nesting: "
                   << NestingLevel << '\n';
            dumpRange(SM, "DefinitionRange: ", DefinitionRange);
            dumpRange(SM, "SpellingRange: ", SpellingRange);
            for (auto &Arg : Arguments)
            {
                dumpRange(SM, Arg.Name + " = ", Arg.TokenRanges);
                errs() << '\n';
            }
        }

        // Dump the node to llvm::errs() and then recursively dump its children
        void dump_tree(unsigned depth = 0) const
        {
            // Indent "depth" number of spaces
            for (unsigned i = 0; i < depth; i++)
            {
                errs() << " ";
            }
            if (depth > 0)
            {
                errs() << "`- ";
            }
            errs() << "Expansion " << Name
                   << " argc: " << Arguments.size()
                   << " nesting: " << NestingLevel << '\n';

            // Dump children at 1 more indentation level
            for (const auto &Child : Children)
                Child->dump_tree(depth + 1);
        }

        // Set of AST node(s) that were found to have been directly
        // expanded from this macro. If the macro is unambiguous, this
        // should only be one
        set<const Stmt *> Stmts;

        // The number of expected AST nodes each argument should map to
        map<string, unsigned> ExpectedASTNodesForArg;
    };

    // A vector of all macro expansions that are root expansions
    typedef vector<Node *> Roots;

private:
    // The Clang CompilerInstance
    CompilerInstance &CI;

    // The roots of all macro expansions in a program
    Roots &MacroRoots;

    // The Clang AST context
    ASTContext &Ctx;

    // Stack for keeping track of nested expansions
    vector<Node *> InvocationStack;

    // Stack for keeping track of which macro argument expansion we are in
    // If we are in one, the back of this stack is the current expansion
    // depth
    vector<unsigned> inMacroArgExpansion;

    // Given a beginning and ending source location in a program,
    // returns the range spanned by their spelling locations in the
    // program's original source code
    SourceRange getSpellingRange(SourceLocation S, SourceLocation E)
    {
        return SourceRange(Ctx.getFullLoc(S).getSpellingLoc(),
                           Ctx.getFullLoc(E).getSpellingLoc());
    }

public:
    // Copy constructor
    // Gets the Ctx from CI
    MacroForest(CompilerInstance &CI, Roots &roots)
        : CI(CI),
          MacroRoots(roots),
          Ctx(CI.getASTContext()){};

    // Callback called when the preprocessor encounters a macro expansion.
    // Adds the expansion to the MacroForest
    void MacroExpands(const Token &MacroNameTok,
                      const MacroDefinition &MD,
                      SourceRange Range,
                      const MacroArgs *Args) override
    {
        // Create the new node for the expansion
        Node *Expansion = new Node();

        // Get the macro's name
        IdentifierInfo *II = MacroNameTok.getIdentifierInfo();
        Expansion->Name = II->getName().str();

        // Get the macro's info
        MacroInfo *MI = MD.getMacroInfo();
        Expansion->MI = MI;

        // Get the macro's definition range and spelling range
        SourceRange DefinitionRange(MI->getDefinitionLoc(),
                                    MI->getDefinitionEndLoc());
        SourceRange SpellingRange = getSpellingRange(Range.getBegin(),
                                                     Range.getEnd());
        Expansion->DefinitionRange = DefinitionRange;
        Expansion->SpellingRange = SpellingRange;

        // Get the source manager
        SourceManager &SM = Ctx.getSourceManager();

        // Get the language options
        const LangOptions &LO = Ctx.getLangOpts();

        // Record the raw text of the macro definition
        {
            Expansion->DefinitionText = "";
            int i = 0;
            for (auto &&Tok : MI->tokens())
            {
                if (i != 0)
                {
                    Expansion->DefinitionText += " ";
                }
                Expansion->DefinitionText += Lexer::getSpelling(Tok, SM, LO);
                i += 1;
            }
        }

        // TODO: Only emit macro expansions if verbose
        {
            auto SpellingLoc = SpellingRange.getBegin();
            errs() << "CPP2C:"
                   << "Macro Expansion,"
                   << "\"" << hashMacro(MD.getMacroInfo(), SM, LO) << "\","
                   << SpellingLoc.printToString(SM) << "\n";
        }

        // ATTENTION: If we are in a macro-argument expansion, we have to
        // store our expansion stack beforehand as we would pop too much here.
        // Hope that is correct?
        // TODO: Come back to this
        Roots InvocationStackCopy;
        if (inMacroArgExpansion.size() > 0)
        {
            InvocationStackCopy = InvocationStack;
        }

        // Pop Element, if the current Spelling Location is not included
        // in the last definition range.
        // ATTENTION!: We only compare the end of the spelling range, as
        // the beginning (the macro name), could have been passed as an
        // argument.
        // TODO: Come back to this
        unsigned protected_entries = (inMacroArgExpansion.size()
                                          ? inMacroArgExpansion.back() - 1
                                          : 0);

        // If the current spelling range is not located in the file (e.g.,
        // foo_##ARG##_bar), we do not pop anything
        // TODO: Come back to this
        if (SM.isWrittenInScratchSpace(SpellingRange.getEnd()))
        {
            protected_entries = InvocationStack.size();
        }
        // TODO: Come back to this
        while (InvocationStack.size() > protected_entries)
        {
            // ATTENTION!: We have to look only at the DefinitionRange of
            // the parent node. If we would look at the SpellingRange
            // also, we would put Macros that are passed as arguments
            // below the callee. However, Macros are expanded, before they
            // are passed downwards. THIS WAS AN UGLY BUG.
            if (InvocationStack.back()
                    ->DefinitionRange.fullyContains(SpellingRange.getEnd()))
            {
                break;
            }

            InvocationStack.pop_back();
        }

        // Set the current expansion's nesting level to the depth of the
        // invocation stack (i.e., how deep we are into recursive macro
        // expansions)
        Expansion->NestingLevel = InvocationStack.size();

        // If the invocation stack is not empty, then we must add this
        // expansion to the forest we are currently building
        if (!InvocationStack.empty())
        {
            // Set the current expansion's parent to the previous expansion
            Expansion->Parent = InvocationStack.back();
            // Add the current expansion to its parent's list of children
            Expansion->Parent->Children.push_back(Expansion);
            // The expansion root is at the front of the InvocationStack.
            // Add the current expansion to the root's list of all nested
            // expansions.
            InvocationStack.front()->SubtreeNodes.push_back(Expansion);
        }
        // If the invocation stack is empty, then we must add a new root
        // to the MacroForest
        else
        {
            // Add the current expansion to the list of expansions under
            // the root (which in this case is the expansion itself)
            Expansion->SubtreeNodes.push_back(Expansion);
            // Set the root node's parent to nullptr
            Expansion->Parent = nullptr;
            // Add the current expansion to the list of all macro roots in the
            // program
            this->MacroRoots.push_back(Expansion);
        }

        // Push this Node onto the Stack. This has to happen before we
        // expand the arguments as this could invoke further expansions.
        InvocationStack.push_back(Expansion);

        // The node at the front of the InvocationStack is the root
        Expansion->Root = InvocationStack.front();

        // Collect the Macro Arguments

        // Initialize the argument count to zero
        unsigned argc = 0;
        // If the macro has arguments, then set argc to the count of them
        if (Args)
        {
            argc = Args->getNumMacroArguments();
        }

        // Iterate the macro arguments
        for (unsigned i = 0; i < argc; i++)
        {
            string ArgName;
            // If the current argument number is less than the number of
            // written macro arguments, then obtain the name of this argument
            if (i < MI->getNumParams())
            {
                ArgName = MI->params()[i]->getName().str();
            }
            // If the current argument number is greater than the number of
            // written macro arguments, then this argument must have been
            // passed to a variadic macro
            else
            {
                ArgName = "__VA_ARGS__";
            }
            Expansion->ExpectedASTNodesForArg.emplace(ArgName, 0);

            // Use emplace to simultaneously construct the argument and
            // push it to the back of the current expansion's argument list
            Expansion->Arguments.emplace_back(ArgName);
            // Get the argument that was just constructed
            Argument &Argument = Expansion->Arguments.back();

            // Iterate all tokens of the Arguments and collect SourceRanges

            // TODO: Not sure why we push the InvocationStack size
            // just to almost immediately pop it?
            inMacroArgExpansion.push_back(InvocationStack.size());
            // Get the argument's token stream pre-expansion.
            // For some reason have to use a const_cast for this to work.
            auto &Tokens = const_cast<MacroArgs *>(Args)
                               ->getPreExpArgument(i, CI.getPreprocessor());
            inMacroArgExpansion.pop_back();

            // Record the raw text behind this argument
            Argument.RawText = "";
            auto Tok = Args->getUnexpArgument(i);
            int numTokens = Args->getArgLength(Tok);
            for (int j = 0; j < numTokens; j++)
            {
                if (j != 0)
                {
                    Argument.RawText += " ";
                }
                Argument.RawText += Lexer::getSpelling(*Tok, SM, LO);
                Tok++;
            }

            // Store the spelling location for this argument
            if (Tokens.size() > 0)
            {
                Argument.SpellingLoc = Tokens.front().getLocation();
            }

            // Iterate the argument's pre-expansion tokens

            SourceRange CurrentRange;
            for (const auto &Token : Tokens)
            {
                // Get the spelling range of this token
                SourceRange TokenRange = getSpellingRange(Token.getLocation(),
                                                          Token.getEndLoc());
                // Merge Source Ranges, Perhaps

                // If the current source range is valid, then try to merge
                // it with previous ranges.
                // Basically this algorithm, but simplified since the ranges
                // are inherently sorted by starting location:
                // https://leetcode.com/problems/merge-intervals/solution/
                // Might be able to clean this code up? Don't want to break
                // it though... Yeah this code is sort of messy, why use a
                // temp var and extra push_back at the end when we can just
                // refer to the last element of the list directly?
                if (CurrentRange.isValid())
                {
                    // If the current range overlaps with the range of the
                    // current token, then extend the current range to the
                    // end of the current token and move on to the next
                    // token immediately
                    if (CurrentRange.getEnd() == TokenRange.getBegin())
                    {
                        // Extend CurrentRange Range
                        CurrentRange = SourceRange(CurrentRange.getBegin(),
                                                   TokenRange.getEnd());
                        continue;
                    }
                    // If the current range does not overlap with the range
                    // of the current token, then we must record the current
                    // range now before moving on to the next token
                    else
                    {
                        Argument.TokenRanges.push_back(CurrentRange);
                        Expansion->ArgSpellingLocs.push_back(CurrentRange);
                    }
                }
                CurrentRange = TokenRange;
            }

            // If the current range is valid (i.e. has a corresponding
            // location in the source code), then add it to the argument's
            // token ranges and the expansion's argument spelling locations
            if (CurrentRange.isValid())
            {
                // Add the current range to the argument's list of token ranges
                Argument.TokenRanges.push_back(CurrentRange);
                // Add the current range to the list of spelling locations
                // for the current expansion's arguments
                Expansion->ArgSpellingLocs.push_back(CurrentRange);
            }
        }

        // Reset the InvocationStack if we were expanded in a macro.
        // TODO: Come back to this
        if (inMacroArgExpansion.size() > 0)
        {
            InvocationStack = InvocationStackCopy;
        }

        // Record the expected number of expanions to be found for each arg
        for (auto &&Tok : MD.getMacroInfo()->tokens())
        {
            auto LO = Ctx.getLangOpts();
            SourceLocation b(Tok.getLocation()), e(Tok.getEndLoc());
            string ArgName = string(SM.getCharacterData(b),
                                    SM.getCharacterData(e) - SM.getCharacterData(b));
            if (Expansion->ExpectedASTNodesForArg.find(ArgName) !=
                Expansion->ExpectedASTNodesForArg.end())
            {
                Expansion->ExpectedASTNodesForArg[ArgName] += 1;
            }
        }
    }
};