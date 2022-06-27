#include "CppSig/MacroForest.hh"
#include "Utils/ExpansionUtils.hh"
#include "Utils/Logging/TransformerMessages.hh"

#include "clang/Lex/Lexer.h"

namespace CppSig
{

    MacroForest::~MacroForest()
    {
        for (auto &&it : MacroRoots)
        {
            delete it;
        }
    }

    MacroForest::MacroForest(
        clang::CompilerInstance &CI,
        bool Verbose,
        Roots &roots)
        : CI(CI),
          Verbose(Verbose),
          MacroRoots(roots),
          Ctx(CI.getASTContext()){};

    clang::SourceRange MacroForest::getSpellingRange(
        clang::SourceLocation S,
        clang::SourceLocation E)
    {
        return clang::SourceRange(Ctx.getFullLoc(S).getSpellingLoc(),
                                  Ctx.getFullLoc(E).getSpellingLoc());
    }

    void MacroForest::MacroExpands(
        const clang::Token &MacroNameTok,
        const clang::MacroDefinition &MD,
        clang::SourceRange Range,
        const clang::MacroArgs *Args)
    {
        // Create the new node for the expansion
        MacroExpansionNode *Expansion = new MacroExpansionNode();

        // Get the macro's name
        clang::IdentifierInfo *II = MacroNameTok.getIdentifierInfo();
        Expansion->Name = II->getName().str();

        // Get the macro's info
        clang::MacroInfo *MI = MD.getMacroInfo();
        Expansion->MI = MI;

        // Get the macro's definition range and spelling range
        clang::SourceRange DefinitionRange(MI->getDefinitionLoc(),
                                           MI->getDefinitionEndLoc());
        clang::SourceRange SpellingRange = getSpellingRange(Range.getBegin(),
                                                            Range.getEnd());
        Expansion->DefinitionRange = DefinitionRange;
        Expansion->SpellingRange = SpellingRange;

        // Count the number of times this macro has been defined
        // up to this point
        Expansion->DefinitionNumber = Utils::countMacroDefinitions(MD);

        // Get the source manager
        clang::SourceManager &SM = Ctx.getSourceManager();

        // Get the language options
        const clang::LangOptions &LO = Ctx.getLangOpts();

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
                Expansion->DefinitionText += clang::Lexer::getSpelling(Tok, SM, LO);
                i += 1;
            }
        }

        if (Verbose)
        {
            Utils::Logging::emitMacroExpansionMessage(llvm::errs(), Expansion->getName(), SpellingRange, MD, SM, LO);
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
            std::string ArgName;
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

            // Use emplace to simultaneously construct the argument and
            // push it to the back of the current expansion's argument list
            Expansion->Arguments.emplace_back(ArgName);
            // Get the argument that was just constructed
            MacroArgument &Argument = Expansion->Arguments.back();

            // Iterate all tokens of the Arguments and collect SourceRanges

            // TODO: Not sure why we push the InvocationStack size
            // just to almost immediately pop it?
            inMacroArgExpansion.push_back(InvocationStack.size());
            // Get the argument's token stream pre-expansion.
            // For some reason have to use a const_cast for this to work.
            auto &Tokens = const_cast<clang::MacroArgs *>(Args)
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
                Argument.RawText += clang::Lexer::getSpelling(*Tok, SM, LO);
                Tok++;
            }

            // Store the spelling location for this argument
            if (Tokens.size() > 0)
            {
                Argument.SpellingLoc = Tokens.front().getLocation();
            }

            // Iterate the argument's pre-expansion tokens

            clang::SourceRange CurrentRange;
            for (const auto &Token : Tokens)
            {
                // Get the spelling range of this token
                clang::SourceRange TokenRange = getSpellingRange(Token.getLocation(),
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
                        CurrentRange = clang::SourceRange(CurrentRange.getBegin(),
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
    }
} // namespace CppSig
