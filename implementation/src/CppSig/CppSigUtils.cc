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
                          SourceLocation Loc = N->getSpellingRange().getBegin();
                          // TODO: Make it a flag whether to only look at expansions
                          // in source files or not.
                          // This just grabs all expansions in the compilation unit.
                          if (SM.isWrittenInScratchSpace(Loc))
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

    std::string getType(clang::ASTContext &Ctx, const Stmt *ST)
    {
        // Taken from Dietrich
        if (const auto E = clang::dyn_cast<clang::Expr>(ST))
        {
            clang::QualType T = E->getType();
            return T.getDesugaredType(Ctx).getCanonicalType().getAsString();
        }
        return "@stmt";
    }

    std::string formatExpansionSignature(
        clang::ASTContext &Ctx,
        MacroExpansionNode *Expansion)
    {
        // Taken from Dietrich
        // NOTE: Also see TransformedDefinition::getExpansionSignatureOrDeclaration.

        // Format return type (if any)
        std::stringstream ss;
        auto &Stmts = Expansion->getStmtsRef();

        if (Stmts.size() == 1)
        {
            ss << getType(Ctx, *Stmts.begin());
        }
        else if (Stmts.size() > 1)
        {
            ss << "@stmt";
        }
        else
        {
            ss << "?";
        }

        ss << " " << Expansion->getName();

        // Format arguments

        if (Expansion->getMI()->isFunctionLike())
        {
            std::string spacer = "";
            ss << "(";
            for (auto &Arg : Expansion->getArgumentsRef())
            {
                ss << spacer;
                spacer = ", ";
                std::set<std::string> ArgTypes;
                for (const auto *ST : Arg.getStmtsRef())
                {
                    ArgTypes.insert(getType(Ctx, ST));
                }
                if (ArgTypes.size() != 1)
                    ss << "?";
                else
                    ss << *ArgTypes.begin();
                ss << " " << Arg.getName();
            }
            ss << ")";
        }
        return ss.str();
    }

} // namespace CppSig
