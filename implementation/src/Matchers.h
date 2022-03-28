// Copied from Dietrich

#pragma once

#include <string>
#include <vector>
#include <set>

#include "clang/Frontend/CompilerInstance.h"
#include "clang/AST/ASTContext.h"
#include "clang/Lex/PPCallbacks.h"
#include "clang/Lex/Lexer.h"
#include "clang/ASTMatchers/ASTMatchers.h"

namespace clang
{
    namespace ast_matchers
    {

        template <typename T>
        inline SourceLocation getSpecificLocation(const T &Node)
        {
            return Node.getBeginLoc();
        }

        template <>
        inline SourceLocation getSpecificLocation<Stmt>(const Stmt &Node)
        {
            if (const auto E = dyn_cast<Expr>(&Node))
                return E->getExprLoc();
            else
                return Node.getBeginLoc();
        }

        template <>
        inline SourceLocation getSpecificLocation<DynTypedNode>(const DynTypedNode &Node)
        {
            if (const Stmt *S = Node.get<clang::Stmt>())
                return getSpecificLocation(*S);
            // Actually this is Incorrect. However, as long as our complete match chain does not
            // support all this, this brings more problems than it solves. (Top-Level Defintions)
            // else if (const Decl *S = Node.get<clang::Decl>())
            //    return getSpecificLocation(*S);
            // else if (const TypeLoc *S = Node.get<clang::TypeLoc>())
            //    return getSpecificLocation(*S);
            else
                return SourceLocation();
        }

        AST_POLYMORPHIC_MATCHER_P(inSourceRangeCollection,
                                  AST_POLYMORPHIC_SUPPORTED_TYPES(Decl, Stmt, TypeLoc),
                                  SourceRangeCollection *, Ranges)
        {
            SourceLocation Loc = getSpecificLocation(Node);

            auto &Context = Finder->getASTContext();
            SourceLocation SpellingLoc = Context.getFullLoc(Loc).getSpellingLoc();

            return Ranges->contains(SpellingLoc);
        }

        /// Usable as: Matcher<Decl>, Matcher<Stmt>, Matcher<TypeLoc>
        AST_POLYMORPHIC_MATCHER(isExpansion,
                                AST_POLYMORPHIC_SUPPORTED_TYPES(Decl, Stmt, TypeLoc))
        {
            return getSpecificLocation(Node).isMacroID();
        }

        /// Usable as: Matcher<Decl>, Matcher<Stmt>, Matcher<TypeLoc>
        AST_POLYMORPHIC_MATCHER(isExpansionRoot,
                                AST_POLYMORPHIC_SUPPORTED_TYPES(Decl, Stmt, TypeLoc))
        {
            SourceLocation Loc = getSpecificLocation(Node);
            if (!Loc.isMacroID())
                return false;

            auto &Context = Finder->getASTContext();
            SourceLocation ELoc = Context.getFullLoc(Loc).getExpansionLoc();

            for (const auto &Parent : Context.getParents(Node))
            {
                SourceLocation PLoc = getSpecificLocation(Parent);
                SourceLocation PELoc = Context.getFullLoc(PLoc).getExpansionLoc();

                // Parent comes from the same expansion as the child
                // => Our node cannot be an expansion root
                if (ELoc == PELoc)
                {
                    return false;
                }
                // PELoc.dump(SM);
                // Parent.dump(llvm::errs(), Context);
            }
            // ELoc.dump(SM);
            // Node.dump();

            return true;
        }

        AST_POLYMORPHIC_MATCHER_P(inMacroForestExpansion,
                                  AST_POLYMORPHIC_SUPPORTED_TYPES(Decl, Stmt, TypeLoc),
                                  MacroForest::Node *, Expansion)
        {
            // assert(Expansion->Parent == nullptr &&
            //        "Matcher works only with the toplevel expansion");
            SourceLocation Loc = getSpecificLocation(Node);

            auto &Context = Finder->getASTContext();
            auto &SM = Context.getSourceManager();

            // All Nodes that stem from the same top-level expansion share
            // an Expansion location. This Expansion location is included
            // in the SpellingRange of that MatchForest::Node
            // ATTENTION: This is for safety, we should only be called in this context.
            SourceLocation ExpansionLoc = Context.getFullLoc(Loc).getExpansionLoc();
            if (!Expansion->Root->SpellingRange.fullyContains(ExpansionLoc))
                return false;

            bool verbose = false;
            // if (Expansion->Name == "raw_spin_lock_init") {
            //     llvm::errs() << "------ \n";
            //     Node.dumpColor();

            //     LangOptions m_lo;

            //     SourceLocation L = Loc;
            //     while (L.isMacroID()) {
            //         auto fullloc = Context.getFullLoc(L);
            //         auto expinfo = SM.getSLocEntry(fullloc.getFileID()).getExpansion();
            //         StringRef name = clang::Lexer::getImmediateMacroName(L, SM, m_lo);
            //         llvm::errs() << name <<  " ";
            //         expinfo.getSpellingLoc().dump(SM);

            //         SourceLocation MacroTrace;
            //         if (SM.isMacroArgExpansion(L))
            //             MacroTrace = SM.getImmediateExpansionRange(L).getBegin();
            //         else
            //             MacroTrace = L;

            //         SourceRange spellingRange(Context.getFullLoc(expinfo.getExpansionLocStart()).getSpellingLoc(),
            //                                   Context.getFullLoc(expinfo.getExpansionLocEnd()).getSpellingLoc());

            //         llvm::errs() << "     isMacroArgExpansion=" << expinfo.isMacroArgExpansion()
            //                      << "\n    spellingRange=";
            //         spellingRange.dump(SM);
            //         llvm::errs() << "     MacroTrace: ";
            //         MacroTrace.dump(SM);

            //         // Go up;
            //         L = SM.getImmediateMacroCallerLoc(L);
            //     }

            //     MacroForest::Node * N = Expansion;
            //     Expansion->Root->dump_tree();
            //     while (N) {
            //         llvm::errs() << "= " << N->Name << '\n';
            //         llvm::errs() << "D "; N->DefinitionRange.dump(SM);
            //         llvm::errs() << "S "; N->SpellingRange.dump(SM);
            //         llvm::errs() << "A ";N->ArgSpellingLocs.dump(SM);
            //         llvm::errs() << '\n';
            //         N = N->Parent;
            //     }

            //     verbose = true;
            // }

            // Co-Walk the Macro Backtrace and MacroForest Backtrace
            SourceLocation L = Loc;
            MacroForest::Node *N = Expansion;

            bool matched_expansion_stack = false;
            while (L.isMacroID())
            {
                auto FullLoc = Context.getFullLoc(L);
                auto ExpInfo = SM.getSLocEntry(FullLoc.getFileID()).getExpansion();

                SourceLocation MacroTrace;
                if (SM.isMacroArgExpansion(L))
                    MacroTrace = SM.getImmediateExpansionRange(L).getBegin();
                else
                    MacroTrace = L;

                SourceLocation SpellingLocation = Context.getFullLoc(L).getSpellingLoc();
                bool found = false;
                if (N->DefinitionRange.fullyContains(SpellingLocation) || N->SpellingRange.fullyContains(SpellingLocation) || N->ArgSpellingLocs.contains(SpellingLocation))
                {
                    found = true;
                }

                // If we are still at the bottom of our Expansion-Tree Chain,
                // it could be, that this macro fully forwarded its body to
                // another macro. In this case, the expansion-stack at the AST
                // node starts at a deeper level. In thse cases, we are
                // allowed to go up, until we hit our first Expansion-Tree Node
                // (see tests/nested2.c)
                if (!found && N == Expansion)
                {
                    L = SM.getImmediateMacroCallerLoc(L);
                    continue;
                }

                if (!found)
                {
                    if (verbose)
                        llvm::errs() << "NOMATCH " << N->Name << "\n";
                    return false;
                }

                matched_expansion_stack = true;

                if (!N->Parent)
                    break;

                // If we have a Parent, this Macro must be spelled in the parent
                {
                    if (!ExpInfo.isMacroArgExpansion())
                    {
                        SourceRange spellingRange(Context.getFullLoc(ExpInfo.getExpansionLocStart()).getSpellingLoc(),
                                                  Context.getFullLoc(ExpInfo.getExpansionLocEnd()).getSpellingLoc());
                        if (N->SpellingRange != spellingRange)
                        {
                            return false;
                        }
                    }
                }

                // Co-Walk both Trees
                if (!ExpInfo.isMacroArgExpansion())
                    N = N->Parent;
                L = SM.getImmediateMacroCallerLoc(L);
            }
            if (verbose)
            {
                llvm::errs() << "MATCHED: " << matched_expansion_stack << '\n';
            }
            return matched_expansion_stack;
        }

    }
} // Namespaces
