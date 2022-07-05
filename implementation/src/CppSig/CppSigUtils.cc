#include "CppSig/CppSigUtils.hh"
#include "Utils/ExpansionUtils.hh"
#include "Callbacks/NodeCollector.hh"
#include "Callbacks/ForestCollector.hh"
#include "Matchers/Matchers.hh"

// CppSigUtils.cc

namespace CppSig
{
    using clang::ASTContext;
    using clang::SourceLocation;
    using clang::SourceManager;
    using clang::Stmt;
    using std::make_unique;
    using std::unique_ptr;
    using std::vector;
    using Utils::isInStdHeader;
    using namespace clang::ast_matchers;
    using Callbacks::NodeCollector;

    void removeExpansionsNotInMainFile(
        MacroForest::Roots &Expansions,
        SourceManager &SM,
        bool OnlyCollectNotDefinedInStdHeaders)
    {
        Expansions.erase(
            remove_if(Expansions.begin(),
                      Expansions.end(),
                      [&SM, &OnlyCollectNotDefinedInStdHeaders](MacroExpansionNode *N)
                      {
                          // Only look at expansions in source files
                          SourceLocation Loc = N->getSpellingRange().getBegin();
                          if (!SM.isInMainFile(Loc) || SM.isWrittenInScratchSpace(Loc))
                          {
                              return true;
                          }

                          // Only look at expansions of macros defined in
                          // source files (non-builtin macros and non-
                          // standard header macros)
                          if (OnlyCollectNotDefinedInStdHeaders)
                          {
                              return isInStdHeader(N->getMI()->getDefinitionLoc(), SM);
                          }

                          return false;
                      }),
            Expansions.end());
    }

    unique_ptr<vector<const Stmt *>> findMacroASTRoots(ASTContext &Ctx)
    {
        vector<const Stmt *> MacroRoots;
        MatchFinder Finder;
        NodeCollector<Stmt> callback("stmt", MacroRoots);
        Finder.addMatcher(
            stmt(clang::ast_matchers::isExpansionRoot()).bind("stmt"),
            &callback);
        Finder.matchAST(Ctx);
        return make_unique<vector<const Stmt *>>(MacroRoots);
    }

    void populateExpansionsWhoseTopLevelStmtIsThisStmt(
        const Stmt *ST,
        CppSig::MacroForest::Roots &ExpansionRoots,
        clang::ASTContext &Ctx)
    {

        SourceManager &SM = Ctx.getSourceManager();
        SourceLocation ExpansionLoc = SM.getExpansionLoc(ST->getBeginLoc());
        MacroExpansionNode *ExpansionRoot = nullptr;
        for (auto E : ExpansionRoots)
        {
            // Check if the ExpansionRoot and the Node have the
            // same Expansion Location. Previously, we checked if
            // the ExpansionLoc was contained in the Spelling
            // Range. However, this might even span files if macro
            // name and argument list are composed in a macro.
            SourceLocation NodeExpansionLoc =
                SM.getExpansionLoc(E->getSpellingRange().getBegin());
            if (NodeExpansionLoc == ExpansionLoc)
            {
                ExpansionRoot = E;
                break;
            }
        }

        if (ExpansionRoot == nullptr)
        {
            return;
        }

        for (auto Expansion : ExpansionRoot->getSubtreeNodesRef())
        {
            clang::ast_matchers::MatchFinder ExpansionFinder;
            Callbacks::ForestCollector callback(Ctx, Expansion->getStmtsRef());
            auto MacroStmt = stmt(unless(implicitCastExpr()),
                                  inMacroForestExpansion(Expansion))
                                 .bind("stmt");
            auto Matcher = stmt(forEachDescendant(MacroStmt));
            // Order Matters!
            ExpansionFinder.addMatcher(MacroStmt, &callback);
            ExpansionFinder.addMatcher(Matcher, &callback);
            ExpansionFinder.match(*ST, Ctx);
        }
    }

    void matchArguments(
        ASTContext &Ctx,
        CppSig::MacroForest::Roots &ExpansionRoots)
    {
        for (auto ToplevelExpansion : ExpansionRoots)
        {
            for (auto Expansion : ToplevelExpansion->getSubtreeNodesRef())
            {
                for (auto ST : Expansion->getStmtsRef())
                { // most of the time only a single one.
                    for (auto &Arg : Expansion->getArgumentsRef())
                    {
                        auto MatcherArg = stmt(
                                              unless(implicitCastExpr()),
                                              inSourceRangeCollection(Arg.getTokenRangesPtr()))
                                              .bind("stmt");
                        auto Matcher = stmt(forEachDescendant(MatcherArg));
                        MatchFinder ArgumentFinder;
                        Callbacks::ForestCollector callback(Ctx, Arg.getStmtsRef());
                        ArgumentFinder.addMatcher(MatcherArg, &callback);
                        ArgumentFinder.addMatcher(Matcher, &callback);
                        ArgumentFinder.match(*ST, Ctx);
                    }
                }
            }
        }
    }

} // namespace CppSig
