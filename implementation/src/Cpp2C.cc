#include "clang/AST/ASTContext.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ParentMapContext.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendPluginRegistry.h"
#include "clang/Lex/Lexer.h"
#include "clang/Lex/MacroArgs.h"
#include "clang/Lex/PPCallbacks.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/Rewrite/Frontend/Rewriters.h"

#include "llvm/Support/raw_ostream.h"

#include "CollectDeclNamesVisitor.h"
#include "ExpansionUtils.h"
#include "MacroForest.h"
#include "MacroNameCollector.h"
#include "Matchers.h"
#include "TransformedDefinition.h"

#include <iostream>
#include <map>

using namespace clang;
using namespace llvm;
using namespace std;

using namespace clang::ast_matchers;

// This file is hardly a paragon of pulchritude, but the logic is correct
// and so far Cpp2C works without issue

struct PluginSettings
{
    bool OverwriteFiles = false;
    bool Verbose = false;
    bool UnifyMacrosWithSameSignature = false;
    raw_fd_ostream *StatsFile = nullptr;
    raw_fd_ostream *MacroDefinitionStatsFile = nullptr;
};

template <typename K, typename V>
void printMapToCSV(llvm::raw_fd_ostream &os, map<K, V> &csv)
{
    unsigned i = 0;
    for (auto &&pair : csv)
    {
        if (i > 0)
        {
            os << ", ";
        }
        os << pair.first;
        i++;
    }
    os << "\n";

    i = 0;
    for (auto &&pair : csv)
    {
        if (i > 0)
        {
            os << ", ";
        }
        os << pair.second;
        i++;
    }
    os << "\n";
}

void printMapToJSON(llvm::raw_fd_ostream &os, map<string, set<string>> &m)
{
    os << "{\n";
    unsigned i = 0;
    for (auto &&pair : m)
    {
        if (i > 0)
        {
            os << ",\n";
        }
        os << "    \""
           << pair.first
           << "\": [";

        unsigned j = 0;
        for (auto &&it : pair.second)
        {
            if (j > 0)
            {
                os << ", ";
            }
            os << '"' << it << '"';

            j++;
        }
        os << ']';

        i++;
    }
    os << "\n}\n";
}

// A Matcher callback, that collects all AST Nodes that were matched
// and bound to BindName
template <typename T>
class NodeCollector : public MatchFinder::MatchCallback
{
    std::string BindName;
    std::vector<const T *> &Nodes;

public:
    NodeCollector(std::string BindName, std::vector<const T *> &Nodes)
        : BindName(BindName), Nodes(Nodes){};

    void
    run(const clang::ast_matchers::MatchFinder::MatchResult &Result) final
    {
        const auto *E = Result.Nodes.getNodeAs<T>(BindName);
        if (E)
        {
            Nodes.push_back(E);
        }
    }
};

class ForestCollector : public MatchFinder::MatchCallback
{
    ASTContext &Context;
    std::set<const Stmt *> &Forest;

public:
    ForestCollector(ASTContext &Context, std::set<const Stmt *> &Forest)
        : Context(Context), Forest(Forest){};

    virtual void
    run(const clang::ast_matchers::MatchFinder::MatchResult &Result) final
    {
        const auto *E = Result.Nodes.getNodeAs<Stmt>("stmt");
        assert(E != nullptr);

        // Have we already recorded a Parent statement? => Skip this one
        const Stmt *ParentStmt = E;
        while (ParentStmt)
        {
            const auto &Parents = Context.getParents(*ParentStmt);
            // FIXME: This happens from time to time
            if (Parents.size() > 1)
            {
                // E->getBeginLoc().dump(Context.getSourceManager());
                // E->dump();
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
            else if (const TypeLoc *TL = Parents[0].get<TypeLoc>())
            {
                (void)TL;
                return; // WE DO NOT COLLECT NODES BELOW TypeLoc
            }
            else
            { // Parent is not a stmt -> break
                // llvm::errs() << "UNKNOWN?\n";
                // auto &Parent = Parents[0];
                // Parent.dump(llvm::errs(), Context);
                // abort();
                break;
            }
        }

        Forest.insert(E);
    }
};

// AST consumer which calls the visitor class to perform the transformation
class Cpp2CConsumer : public ASTConsumer
{
private:
    CompilerInstance *CI;
    Preprocessor &PP;
    MacroForest::Roots ExpansionRoots;
    set<string> MacroNames;
    set<string> MultiplyDefinedMacros;
    map<string, set<string>> MacroNamePlusTypeToTransformedDefinitionPrototypes;

    // To give it access to members
    friend class PluginCpp2CAction;

    PluginSettings Cpp2CSettings;

public:
    explicit Cpp2CConsumer(CompilerInstance *CI, PluginSettings Cpp2CSettings)
        : CI(CI), PP(CI->getPreprocessor()), Cpp2CSettings(Cpp2CSettings) {}

    virtual void HandleTranslationUnit(ASTContext &Ctx)
    {
        auto begin_time = std::chrono::high_resolution_clock::now();

        Rewriter RW;
        SourceManager &SM = Ctx.getSourceManager();
        const LangOptions &LO = Ctx.getLangOpts();
        RW.setSourceMgr(SM, LO);

        TranslationUnitDecl *TUD = Ctx.getTranslationUnitDecl();

        map<string, unsigned> Stats = NewTransformationStats();

        // Collect the names of all the variables and functions
        // defined in the program
        set<string> FunctionNames;
        set<string> VarNames;

        CollectDeclNamesVisitor CDNvisitor(CI, &FunctionNames, &VarNames);
        CDNvisitor.TraverseTranslationUnitDecl(TUD);

        // Step 0: Remove all Macro Roots that are not expanded
        // in the main file
        ExpansionRoots.erase(
            remove_if(ExpansionRoots.begin(),
                      ExpansionRoots.end(),
                      [&SM](const MacroForest::Node *N)
                      {
                          // Only look at source files
                          SourceLocation Loc = N->SpellingRange.getBegin();
                          return !SM.isInMainFile(Loc) ||
                                 SM.isWrittenInScratchSpace(Loc);
                      }),
            ExpansionRoots.end());

        Stats[TopLevelExpansionsInMainFile] = ExpansionRoots.size();

        for (auto &&TLE : ExpansionRoots)
        {
            if (TLE->MI->isObjectLike())
            {
                Stats[TopLevelObjectLikeMacroExpansionsInMainFile] += 1;
            }
            else
            {
                Stats[TopLevelFunctionLikeMacroExpansionsInMainFile] += 1;
            }
        }

        // Step 1: Find Top-Level Macro Expansions
        if (Cpp2CSettings.Verbose)
        {
            errs() << "Step 1: Search for macro AST roots\n";
        }
        std::vector<const Stmt *> MacroRoots;
        {
            MatchFinder Finder;
            NodeCollector<Stmt> callback("stmt", MacroRoots);
            Finder.addMatcher(
                stmt(isExpansionRoot()).bind("stmt"),
                &callback);
            Finder.matchAST(Ctx);
        }

        // Step 2: Find the AST statements that were directly expanded
        // from the top-level expansions
        if (Cpp2CSettings.Verbose)
        {
            errs() << "Step 2: Search for " << ExpansionRoots.size()
                   << " top-level expansions in "
                   << MacroRoots.size() << " AST macro roots\n";
        }
        for (const auto ST : MacroRoots)
        {
            SourceLocation ExpansionLoc = SM.getExpansionLoc(ST->getBeginLoc());
            MacroForest::Node *ExpansionRoot = nullptr;
            for (auto E : ExpansionRoots)
            {
                // Check if the ExpansionRoot and the Node have the
                // same Expansion Location. Previously, we checked if
                // the ExpansionLoc was contained in the Spelling
                // Range. However, this might even span files if macro
                // name and argument list are composed in a macro.
                SourceLocation NodeExpansionLoc =
                    SM.getExpansionLoc(E->SpellingRange.getBegin());
                if (NodeExpansionLoc == ExpansionLoc)
                {
                    ExpansionRoot = E;
                    break;
                }
            }
            if (ExpansionRoot == nullptr)
            {
                if (Cpp2CSettings.Verbose)
                {

                    StringRef Name = clang::Lexer::getImmediateMacroName(ST->getBeginLoc(), SM, LO);
                    errs() << "     Skipped macro expansion "
                           << Name << "\n";
                }
                continue;
            }

            // llvm::errs() << "     Match macro "
            //        << ExpansionRoot->Name
            //        << " with "
            //        << ExpansionRoot->SubtreeNodes.size()
            //        << " (nested) expansions\n";
            // ExpansionRoot->SpellingRange.dump(SM);
            // ExpansionLoc.dump(SM);

            if (Cpp2CSettings.Verbose)
            {
                ST->dumpColor();
            }

            // llvm::errs() << "Collecting AST nodes for root expansion " << ExpansionRoot->Name << "\n";
            for (auto Expansion : ExpansionRoot->SubtreeNodes)
            {
                // llvm::errs() << "Collecting AST nodes for sub expansion " << Expansion->Name << "\n";
                MatchFinder ExpansionFinder;
                ForestCollector callback(Ctx, Expansion->Stmts);
                auto MacroStmt = stmt(unless(implicitCastExpr()),
                                      inMacroForestExpansion(Expansion))
                                     .bind("stmt");
                auto Matcher = stmt(forEachDescendant(MacroStmt));
                // Order Matters!
                ExpansionFinder.addMatcher(MacroStmt, &callback);
                ExpansionFinder.addMatcher(Matcher, &callback);
                ExpansionFinder.match(*ST, Ctx);
                // for (auto &&Stm : Expansion->Stmts)
                // {
                //     llvm::errs() << "AST node for sub-expansion " << Expansion->Name << "\n";
                //     Stm->dumpColor();
                // }
                // llvm::errs() << "\n";
            }
            // llvm::errs() << "\n";
            // llvm::errs() << "\n";
        }

        // Step 3 : Within Subtrees, Match the Arguments
        if (Cpp2CSettings.Verbose)
        {
            errs() << "Step 3: Find Arguments \n";
        }
        for (auto ToplevelExpansion : ExpansionRoots)
        {
            for (auto Expansion : ToplevelExpansion->SubtreeNodes)
            {
                for (auto ST : Expansion->Stmts)
                { // most of the time only a single one.
                    for (auto &Arg : Expansion->Arguments)
                    {
                        auto MatcherArg = stmt(
                                              unless(implicitCastExpr()),
                                              inSourceRangeCollection(&Arg.TokenRanges))
                                              .bind("stmt");
                        auto Matcher = stmt(forEachDescendant(MatcherArg));
                        MatchFinder ArgumentFinder;
                        ForestCollector callback(Ctx, Arg.Stmts);
                        ArgumentFinder.addMatcher(MatcherArg, &callback);
                        ArgumentFinder.addMatcher(Matcher, &callback);
                        ArgumentFinder.match(*ST, Ctx);
                    }
                }
            }
        }

        // Mapping of macro names to all emitted transformed definitions for
        // that macro.This enables to quickly check for duplicate
        // identical transformations
        map<SourceLocation, vector<struct TransformedDefinition>>
            MacroDefinitionLocationToTransformedDefinition;

        set<string> TransformedPrototypes;
        set<pair<string, const FunctionDecl *>>
            TransformedDefinitionsAndFunctionDeclExpandedIn;

        // Step 4: Transform hygienic and transformable macros.
        if (Cpp2CSettings.Verbose)
        {
            errs() << "Step 4: Transform hygienic and transformable macros \n";
        }

        for (auto TopLevelExpansion : ExpansionRoots)
        {

            // Check that expanded macro is not multiply defined or redefined
            if (MultiplyDefinedMacros.find(TopLevelExpansion->Name) !=
                MultiplyDefinedMacros.end())
            {
                if (Cpp2CSettings.Verbose)
                {
                    errs() << "Skipping expansion of "
                           << TopLevelExpansion->Name
                           << " because the macro is multiply-defined or "
                           << "redefined \n";
                }
                Stats[TopLevelExpansionsOfMultiplyOrRedefinedDefinedMacros] += 1;
                if (TopLevelExpansion->MI->isObjectLike())
                {
                    Stats[MultiplyOrRedefinedOLMExpansions] += 1;
                }
                else
                {
                    Stats[MultiplyOrRedefinedFLMExpansions] += 1;
                }
                continue;
            }

            {
                auto E = dyn_cast_or_null<Expr>(*TopLevelExpansion->Stmts.begin());
                if (E && E->HasSideEffects(Ctx))
                {
                    Stats[TopLevelExpansionsWithSideEffects] += 1;
                    if (TopLevelExpansion->MI->isObjectLike())
                    {
                        Stats[TopLevelOLMExpansionsWithSideEffects] += 1;
                    }
                    else
                    {
                        Stats[TopLevelFLMExpansionsWithSideEffects] += 1;
                    }
                }
            }

            // Don't transform expansions appearing where a const expr
            // is required
            if (mustBeConstExpr(Ctx, *TopLevelExpansion->Stmts.begin()))
            {
                if (Cpp2CSettings.Verbose)
                {
                    errs() << "Not transforming expansion of "
                           << TopLevelExpansion->Name + " @ "
                           << (*(TopLevelExpansion->Stmts.begin()))->getBeginLoc().printToString(SM)
                           << " because needed to be a const expr\n";
                }
                Stats[ConstExprExpansionsFound] += 1;
                continue;
            }

            // Don't transform unhygienic expansions
            if (!isExpansionHygienic(&Ctx, PP, TopLevelExpansion, Stats,
                                     Cpp2CSettings.Verbose))
            {
                Stats[TopLevelUnhygienicExpansions] += 1;
                if (TopLevelExpansion->MI->isObjectLike())
                {
                    Stats[UnhygienicOLMs] += 1;
                }
                else
                {
                    Stats[UnhygienicFLMs] += 1;
                }
                continue;
            }
            else
            {
                Stats[HygienicExpansions] += 1;
                if (TopLevelExpansion->MI->isObjectLike())
                {
                    Stats[HygienicOLMExpansions] += 1;
                }
                else
                {
                    Stats[HygienicFLMExpansions] += 1;
                }
            }

            auto ST = *TopLevelExpansion->Stmts.begin();
            auto E = dyn_cast_or_null<Expr>(ST);
            assert(E != nullptr);

            // Transform object-like macros which reference global vars
            // into nullary functions, since global var initializations
            // must be const expressions and thus cannot contains vars
            // FIXME: Technically we should also check for function calls,
            // but this doesn't matter right now since we don't transform
            // expansions containing function calls anyway
            bool TransformToVar =
                TopLevelExpansion->MI->isObjectLike() &&
                !containsGlobalVars(E);

            // Create the transformed definition.
            // Note that this generates the transformed definition as well.
            struct TransformedDefinition TD =
                NewTransformedDefinition(Ctx, TopLevelExpansion,
                                         TransformToVar);

            // Don't transform expansions which:
            // 1) Change the R-value associated with the L-value of a symbol
            //    in one of their arguments
            // 2) Retrieve the L-value of a symbol in one of their arguments
            bool writesToRValueFromArg = false;
            bool readsLValueFromArg = false;
            set<const Stmt *> LValuesFromArgs;
            set<const Stmt *> StmtsThatChangeRValue;
            set<const Stmt *> StmtsThatReadLValue;
            for (auto &&it : TopLevelExpansion->Arguments)
            {
                collectLValuesSpelledInRange(Ctx, ST, it.TokenRanges, &LValuesFromArgs);
            }

            collectStmtsThatChangeRValue(ST, &StmtsThatChangeRValue);
            for (auto &&StmtThatChangesRValue : StmtsThatChangeRValue)
            {
                for (auto &&LVal : LValuesFromArgs)
                {
                    if (auto UO = dyn_cast_or_null<clang::UnaryOperator>(StmtThatChangesRValue))
                    {

                        if (containsStmt(UO, LVal))
                        {
                            writesToRValueFromArg = true;
                            break;
                        }
                    }
                    else if (auto BO = dyn_cast_or_null<BinaryOperator>(StmtThatChangesRValue))
                    {
                        if (containsStmt(BO->getLHS(), LVal))
                        {
                            writesToRValueFromArg = true;
                            break;
                        }
                    }
                    else
                    {
                        // NOTE: This shouldn't happen? What do we do here?
                        assert(false);
                    }
                }
                if (writesToRValueFromArg)
                {
                    break;
                }
            }
            if (writesToRValueFromArg)
            {
                if (Cpp2CSettings.Verbose)
                {
                    errs() << "Not transforming "
                           << TopLevelExpansion->Name
                           << " @ "
                           << (*(TopLevelExpansion->Stmts.begin()))->getBeginLoc().printToString(SM)
                           << " because it writes to an R-value from "
                           << "from its arguments\n";
                }
                Stats[TopLevelExpansionsThatWriteToRValueFromSymbolInArgument] += 1;
                continue;
            }

            collectStmtsThatReadLValue(ST, &StmtsThatReadLValue);
            for (auto &&StmtThatReadsLValue : StmtsThatReadLValue)
            {
                for (auto &&LVal : LValuesFromArgs)
                {

                    if (containsStmt(StmtThatReadsLValue, LVal))
                    {
                        readsLValueFromArg = true;
                        break;
                    }
                }
                if (readsLValueFromArg)
                {
                    break;
                }
            }
            if (readsLValueFromArg)
            {
                if (Cpp2CSettings.Verbose)
                {
                    errs() << "Not transforming "
                           << TopLevelExpansion->Name
                           << " @ "
                           << (*(TopLevelExpansion->Stmts.begin()))->getBeginLoc().printToString(SM)
                           << " because it reads an L-value from "
                           << "from its arguments\n";
                }
                Stats[TopLevelExpansionsThatReadFromLValueFromSymbolInArgument] += 1;
                continue;
            }

            // Don't transform expansions which would be transformed to vars,
            // but contain function calls in their initializers
            if (TD.IsVar && containsFunctionCalls(E))
            {
                if (Cpp2CSettings.Verbose)
                {
                    errs() << "Not transforming "
                           << TopLevelExpansion->Name
                           << " @ "
                           << (*(TopLevelExpansion->Stmts.begin()))->getBeginLoc().printToString(SM)
                           << " because it would have been transformed to "
                           << "a var with a call in its initializer\n";
                }
                Stats[TopLevelExpansionsTransformedToVarWithCallInInitializer] += 1;
                continue;
            }

            // Don't transform definitions which contain array types
            if (TD.hasArrayTypes())
            {
                if (Cpp2CSettings.Verbose)
                {
                    errs() << "Not transforming "
                           << TopLevelExpansion->Name
                           << " @ "
                           << (*(TopLevelExpansion->Stmts.begin()))->getBeginLoc().printToString(SM)
                           << " because it involved array types\n";
                }
                Stats[TopLevelExpansionsWithArrayTypesInSignature] += 1;
                continue;
            }

            // Don't transform definitions which would become void vars
            if (TD.IsVar &&
                (TD.VarOrReturnType.isNull() ||
                 TD.VarOrReturnType.getAsString() == "void"))
            {
                if (Cpp2CSettings.Verbose)
                {
                    errs() << "Not transforming "
                           << TopLevelExpansion->Name
                           << " @ "
                           << (*(TopLevelExpansion->Stmts.begin()))->getBeginLoc().printToString(SM)
                           << " because it was a var with type void\n";
                }
                Stats[TopLevelExpansionsTransformedToVarWithNullOrVoidType] += 1;
                continue;
            }

            // Perform function-specific checks
            if (!TD.IsVar)
            {
                auto Parents = Ctx.getParents(*E);
                if (Parents.size() > 1)
                {
                    continue;
                }

                // Check that function call is not on LHS of assignment
                bool isLHSOfAssignment = false;
                while (Parents.size() > 0)
                {
                    auto P = Parents[0];
                    if (auto BO = P.get<BinaryOperator>())
                    {
                        if (BO->isAssignmentOp())
                        {
                            if (SM.getExpansionRange(BO->getLHS()->getSourceRange()).getAsRange().fullyContains(SM.getExpansionRange(E->getSourceRange()).getAsRange()))
                            {
                                isLHSOfAssignment = true;
                                break;
                            }
                        }
                    }
                    Parents = Ctx.getParents(P);
                }
                if (isLHSOfAssignment)
                {
                    if (Cpp2CSettings.Verbose)
                    {
                        errs() << "Not transforming "
                               << TopLevelExpansion->Name
                               << " @ "
                               << (*(TopLevelExpansion->Stmts.begin()))->getBeginLoc().printToString(SM)
                               << " because it was a function call used as "
                               << "an L-value\n";
                    }
                    Stats[TopLevelExpansionsTransformedToFunctionCallUsedAsLHSOfAssign] += 1;
                    continue;
                }

                // Check that function call is not the operand of an inc or dec
                Parents = Ctx.getParents(*E);
                bool isOperandOfDecOrInc = false;
                while (Parents.size() > 0)
                {
                    auto P = Parents[0];
                    if (auto UO = P.get<clang::UnaryOperator>())
                    {
                        if (UO->isIncrementDecrementOp())
                        {
                            isOperandOfDecOrInc = true;
                            break;
                        }
                    }
                    Parents = Ctx.getParents(P);
                }
                if (isOperandOfDecOrInc)
                {
                    if (Cpp2CSettings.Verbose)
                    {
                        errs() << "Not transforming "
                               << TopLevelExpansion->Name
                               << " @ "
                               << (*(TopLevelExpansion->Stmts.begin()))->getBeginLoc().printToString(SM)
                               << " because it was a function call used as "
                               << "an L-value\n";
                    }
                    Stats[TopLevelExpansionsTransformedToFunctionCallAsOperandOfDecOrInc] += 1;
                    continue;
                }

                // Check that function call is not the operand of address of
                // (&)
                Parents = Ctx.getParents(*E);
                bool isOperandOfAddressOf = false;
                while (Parents.size() > 0)
                {
                    auto P = Parents[0];
                    if (auto UO = P.get<clang::UnaryOperator>())
                    {
                        if (UO->getOpcode() == clang::UnaryOperator::Opcode::UO_AddrOf)
                        {
                            isOperandOfAddressOf = true;
                            break;
                        }
                    }
                    Parents = Ctx.getParents(P);
                }
                if (isOperandOfAddressOf)
                {
                    if (Cpp2CSettings.Verbose)
                    {
                        errs() << "Not transforming "
                               << TopLevelExpansion->Name
                               << " @ "
                               << (*(TopLevelExpansion->Stmts.begin()))->getBeginLoc().printToString(SM)
                               << " because it was a function call used as "
                               << "an L-value\n";
                    }
                    Stats[TopLevelExpansionsTransformedToFunctionCallAsOperandOfAddressOf] += 1;
                    continue;
                }
            }

            // Check that the transformed definition does not have a
            // is not a function pointer type
            if (TD.hasFunctionTypes())
            {
                if (Cpp2CSettings.Verbose)
                {
                    errs() << "Not transforming "
                           << TopLevelExpansion->Name
                           << " @ "
                           << (*(TopLevelExpansion->Stmts.begin()))->getBeginLoc().printToString(SM)
                           << " because it had function/void pointer type \n";
                }
                Stats[TopLevelExpansionsWithFunctionPointerType] += 1;
                continue;
            }

            if (isa_and_nonnull<clang::StringLiteral>(*(TopLevelExpansion->Stmts.begin())))
            {
                if (Cpp2CSettings.Verbose)
                {
                    errs() << "Not transforming "
                           << TopLevelExpansion->Name
                           << " @ "
                           << (*(TopLevelExpansion->Stmts.begin()))->getBeginLoc().printToString(SM)
                           << " because it was a string literal \n";
                }
                Stats[TopLevelExpansionsToStringLiteral] += 1;
                continue;
            }

            auto FD = getFunctionDeclStmtExpandedIn(Ctx, *TopLevelExpansion->Stmts.begin());

            if (FD == nullptr ||
                !RW.isRewritable(FD->getBeginLoc()) ||
                !SM.isInMainFile(FD->getBeginLoc()))
            {
                if (Cpp2CSettings.Verbose)
                {
                    errs() << "Not transforming "
                           << TopLevelExpansion->Name
                           << " @ "
                           << (*(TopLevelExpansion->Stmts.begin()))->getBeginLoc().printToString(SM)
                           << " because it was not expanded inside a function "
                           << "definition\n";
                }
                Stats[TransformationLocationNotRewritable] += 1;
                continue;
            }

            //// Transform the expansion

            // If an identical transformation for this expansion exists,
            // use it; otherwise generate a unique name for this transformation
            // and insert its definition into the program
            string EmittedName = "";
            if (Cpp2CSettings.UnifyMacrosWithSameSignature)
            {
                // If we are unifying macros, then we have to check
                // all transformed definitions for an identical one
                for (auto &&MacroLocationAndTransformedDefinitions : MacroDefinitionLocationToTransformedDefinition)
                {
                    for (auto &&ETD : MacroLocationAndTransformedDefinitions.second)
                    {
                        // Find which, if any, of the prior transformation
                        // definitions of this macro are identical to the one
                        // we are considering adding to the program.
                        if (ETD.IsVar == TD.IsVar &&
                            ETD.VarOrReturnType == TD.VarOrReturnType &&
                            ETD.ArgTypes == TD.ArgTypes &&
                            ETD.InitializerOrDefinition == TD.InitializerOrDefinition)
                        {
                            EmittedName = ETD.EmittedName;
                            break;
                        }
                        // Found a match?
                        if (EmittedName != "")
                        {
                            break;
                        }
                    }
                }
            }
            else
            {
                // Otherwise, we can use the macro definition location to
                // quickly find any identical prior transformations
                if (MacroDefinitionLocationToTransformedDefinition.find(TD.Expansion->MI->getDefinitionLoc()) !=
                    MacroDefinitionLocationToTransformedDefinition.end())
                {
                    // Find which, if any, of the prior transformation
                    // definitions of this macro are identical to the one
                    // we are considering adding to the program.
                    for (auto &&ETD : MacroDefinitionLocationToTransformedDefinition[TD.Expansion->MI->getDefinitionLoc()])
                    {
                        if (ETD.IsVar == TD.IsVar &&
                            ETD.VarOrReturnType == TD.VarOrReturnType &&
                            ETD.ArgTypes == TD.ArgTypes &&
                            ETD.InitializerOrDefinition == TD.InitializerOrDefinition)
                        {
                            EmittedName = ETD.EmittedName;
                            break;
                        }
                    }
                }
            }

            // If EmittedName is not empty at this point, then we found a match
            if (EmittedName != "")
            {
                if (Cpp2CSettings.Verbose)
                {
                    errs() << "Not emitting a definition for " +
                                  TopLevelExpansion->Name +
                                  " because an identical "
                                  "definition already exists\n";
                }
                Stats[DedupedDefinitions] += 1;
                if (TopLevelExpansion->MI->isObjectLike())
                {
                    Stats[DedupedOLMDefinitions] += 1;
                }
                else
                {
                    Stats[DedupedFLMDefinitions] += 1;
                }
            }
            // Otherwise, we need to generate a unique name for this
            // transformation and emit its definition
            else
            {
                string Basename = getNameForExpansionTransformation(
                    SM, TopLevelExpansion,
                    TransformToVar);
                EmittedName = Basename;
                unsigned suffix = 0;
                while (FunctionNames.find(EmittedName) != FunctionNames.end() &&
                       VarNames.find(EmittedName) != VarNames.end() &&
                       MacroNames.find(EmittedName) != MacroNames.end())
                {
                    EmittedName = Basename + "_" + to_string(suffix);
                    suffix += 1;
                }
                FunctionNames.insert(EmittedName);
                VarNames.insert(EmittedName);
                MacroNames.insert(EmittedName);

                TD.EmittedName = EmittedName;

                string TransformedSignature =
                    TD.getExpansionSignatureOrDeclaration(Ctx, false);

                string FullTransformationDefinition =
                    TransformedSignature + TD.InitializerOrDefinition;

                TransformedPrototypes.insert(TransformedSignature + ";");
                TransformedDefinitionsAndFunctionDeclExpandedIn.emplace(FullTransformationDefinition, FD);
                // Record the number of unique definitions emitted for this
                // macro definition
                {
                    string key = TopLevelExpansion->Name;
                    key += "+";
                    key += TopLevelExpansion->MI->isObjectLike() ? "ObjectLike" : "FunctionLike";
                    // Set the emitted name to the empty string right before
                    // recording the signature so that we get an anonymous
                    // signature
                    string temp = TD.EmittedName;
                    TD.EmittedName = "";
                    MacroNamePlusTypeToTransformedDefinitionPrototypes[key].insert(TD.getExpansionSignatureOrDeclaration(Ctx, true));
                    TD.EmittedName = temp;
                }

                MacroDefinitionLocationToTransformedDefinition[TD.Expansion->MI->getDefinitionLoc()]
                    .push_back(TD);

                Stats[EmittedDefinitions] += 1;
                if (TopLevelExpansion->MI->isObjectLike())
                {
                    Stats[EmittedOLMDefinitions] += 1;
                }
                else
                {
                    Stats[EmittedFLMDefinitions] += 1;
                }
            }

            // Rewrite the invocation into a function call or var ref
            string CallOrRef = EmittedName;
            if (!TransformToVar)
            {
                CallOrRef += "(";
                unsigned i = 0;
                for (auto &&Arg : TopLevelExpansion->Arguments)
                {
                    if (i >= 1)
                    {
                        CallOrRef += ", ";
                    }

                    // Reconstruct the actual arguments from their tokens
                    for (auto &&TR : Arg.TokenRanges)
                    {
                        auto CTR = CharSourceRange::getCharRange(TR);
                        string ArgSourceText =
                            Lexer::getSourceText(CTR, SM, LO).str();
                        CallOrRef += ArgSourceText + " ";
                    }

                    i += 1;
                }
                CallOrRef += ")";
            }
            SourceRange InvocationRange = TopLevelExpansion->SpellingRange;
            RW.ReplaceText(InvocationRange, StringRef(CallOrRef));

            Stats[TransformedTopLevelExpansions] += 1;
            if (TopLevelExpansion->MI->isObjectLike())
            {
                Stats[TransformedTopLevelObjectLikeMacroExpansions] += 1;
            }
            else
            {
                Stats[TransformedTopLevelFunctionLikeMacroExpansions] += 1;
            }

            if (E->HasSideEffects(Ctx))
            {
                Stats[TransformedTopLevelExpansionsWithSideEffects] += 1;
                if (TopLevelExpansion->MI->isObjectLike())
                {
                    Stats[TransformedOLMExpansionsWithSideEffects] += 1;
                }
                else
                {
                    Stats[TransformedFLMExpansionsWithSideEffects] += 1;
                }
            }
        }

        // Emit transformed definitions after functions in which they appear
        for (auto &&it : TransformedDefinitionsAndFunctionDeclExpandedIn)
        {
            auto StartOfFD = it.second->getBeginLoc();
            // RW.InsertTextAfter(
            //     SM.getLocForEndOfFile(SM.getMainFileID()),
            //     StringRef(it + "\n\n"));
            RW.InsertTextBefore(
                StartOfFD,
                StringRef(it.first + "\n\n"));
            if (Cpp2CSettings.Verbose)
            {
                errs() << "Emitted a definition: "
                       << it.first + "\n";
            }
        }

        // Get size of the file in bytes
        Stats[FileSize] = SM.getFileEntryForID(SM.getMainFileID())->getSize();

        if (Cpp2CSettings.OverwriteFiles)
        {
            RW.overwriteChangedFiles();
        }
        else
        {
            // Print the results of the rewriting for the current file
            if (const RewriteBuffer *RewriteBuf =
                    RW.getRewriteBufferFor(SM.getMainFileID()))
            {
                RewriteBuf->write(outs());
            }
            else
            {
                RW.getEditBuffer(SM.getMainFileID()).write(outs());
            }
        }

        auto end_time = std::chrono::high_resolution_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::microseconds>(
                            end_time - begin_time)
                            .count();
        Stats[TransformationTime] = duration;

        // Dump the transformation stats to CSV
        if (Cpp2CSettings.StatsFile != nullptr)
        {
            printMapToCSV(*(Cpp2CSettings.StatsFile), Stats);
            Cpp2CSettings.StatsFile->flush();
        }

        // Dump the macro definition stats to JSON
        if (Cpp2CSettings.MacroDefinitionStatsFile != nullptr)
        {
            printMapToJSON(*(Cpp2CSettings.MacroDefinitionStatsFile),
                           MacroNamePlusTypeToTransformedDefinitionPrototypes);
            Cpp2CSettings.MacroDefinitionStatsFile->flush();
        }
    }
};

// Wrap everything into a plugin
class PluginCpp2CAction : public PluginASTAction
{

protected:
    unique_ptr<ASTConsumer>
    CreateASTConsumer(CompilerInstance &CI,
                      StringRef file) override
    {
        auto &PP = CI.getPreprocessor();
        auto Cpp2C = make_unique<Cpp2CConsumer>(&CI, Cpp2CSettings);

        MacroNameCollector *MNC = new MacroNameCollector(
            Cpp2C->MacroNames,
            Cpp2C->MultiplyDefinedMacros,
            Cpp2C->MacroNamePlusTypeToTransformedDefinitionPrototypes);
        MacroForest *MF = new MacroForest(CI, Cpp2C->ExpansionRoots);
        PP.addPPCallbacks(unique_ptr<PPCallbacks>(MNC));
        PP.addPPCallbacks(unique_ptr<PPCallbacks>(MF));

        // Return the consumer to initiate the transformation
        return Cpp2C;
    }

    bool ParseArgs(const CompilerInstance &CI,
                   const vector<string> &args) override
    {
        for (auto it = args.begin(); it != args.end(); ++it)
        {
            std::string arg = *it;
            if (arg == "-ow" || arg == "-overwrite-files")
            {
                Cpp2CSettings.OverwriteFiles = true;
            }
            else if (arg == "-v" || arg == "--verbose")
            {
                Cpp2CSettings.Verbose = true;
            }
            else if (arg == "-u" || arg == "--unify-macros-with-different-names")
            {
                Cpp2CSettings.UnifyMacrosWithSameSignature = true;
            }
            else if (arg == "-ds" || arg == "-dump-stats")
            {
                error_code str_err;
                ++it;
                assert(it != args.end());
                Cpp2CSettings.StatsFile = new raw_fd_ostream(*it, str_err);
                if (str_err.value() != 0)
                {
                    errs() << str_err.message() << '\n';
                    exit(-1);
                }
            }
            else if (arg == "-dmds" || arg == "-dump-macro-definition-stats")
            {
                error_code str_err;
                ++it;
                assert(it != args.end());
                Cpp2CSettings.MacroDefinitionStatsFile = new raw_fd_ostream(*it, str_err);
                if (str_err.value() != 0)
                {
                    errs() << str_err.message() << '\n';
                    exit(-1);
                }
            }
            else
            {
                errs() << "Unknown argument: " << arg << '\n';
                exit(-1);
            }
        }
        return true;
    }

    // Necessary for ANYTHING to print to stderr
    ActionType getActionType() override
    {
        return ActionType::AddBeforeMainAction;
    }

private:
    PluginSettings Cpp2CSettings;
};

//-----------------------------------------------------------------------------
// Registration
//-----------------------------------------------------------------------------
static FrontendPluginRegistry::Add<PluginCpp2CAction>
    X("cpp2c", "Transform CPP macros to C functions");
