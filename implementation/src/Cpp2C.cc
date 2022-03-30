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
        set<pair<string, const FunctionDecl *>> TransformedDefinitionsAndFunctionDeclExpandedIn;

        // Step 4: Transform hygienic macros.
        if (Cpp2CSettings.Verbose)
        {
            errs() << "Step 4: Transform hygienic macros \n";
        }

        for (auto TopLevelExpansion : ExpansionRoots)
        {
            // Don't transform expansions appearing where a const expr
            // is required
            bool NeedConst =
                mustBeConstExpr(Ctx, *TopLevelExpansion->Stmts.begin());

            // Don't transform unhygienic expansions
            if (NeedConst ||
                !isExpansionHygienic(&Ctx, PP, TopLevelExpansion, Stats,
                                     Cpp2CSettings.Verbose,
                                     MultiplyDefinedMacros))
            {
                if (NeedConst)
                {
                    if (Cpp2CSettings.Verbose)
                    {
                        errs() << "Not transforming expansion of "
                               << TopLevelExpansion->Name + " @ "
                               << (*(TopLevelExpansion->Stmts.begin()))->getBeginLoc().printToString(SM)
                               << " because needed to be a const expr\n";
                    }
                    Stats[ConstExprExpansionsFound] += 1;
                }

                Stats[UntransformedTopLevelExpansions] += 1;
                if (TopLevelExpansion->MI->isObjectLike())
                {
                    Stats[UntransformedTopLevelObjectLikeMacroExpansions] += 1;
                }
                else
                {
                    Stats[UntransformedTopLevelFunctionLikeMacroExpansions] += 1;
                }
                continue;
            }

            //// Transform the expansion

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

            // Don't transform definitions which rely on user-defined types
            // if (TD.hasNonBuiltinTypes())
            // {
            //     if (Cpp2CSettings.Verbose)
            //     {
            //         errs() << "Not transforming "
            //                << TopLevelExpansion->Name
            //                << " @ "
            //                << (*(TopLevelExpansion->Stmts.begin()))->getBeginLoc().printToString(SM)
            //                << " because it involved user-defined types\n";
            //     }
            //     // TODO: Emit stats
            //     continue;
            // }

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
                // TODO: Emit stats
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
                // TODO: Emit stats
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
                    // TODO: Emit stats
                    continue;
                }

                // Check that function call is not the operand of an inc or dec
                Parents = Ctx.getParents(*E);
                bool isOperandOfDecOrInc = false;
                while (Parents.size() > 0)
                {
                    auto P = Parents[0];
                    if (auto UO = P.get<UnaryOperator>())
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
                    // TODO: Emit stats
                    continue;
                }
            }

            // Check that type is not a function pointer or void pointer
            if (TD.VarOrReturnType.getTypePtr() &&
                (TD.VarOrReturnType.getTypePtr()->isFunctionPointerType() ||
                 TD.VarOrReturnType.getTypePtr()->isVoidPointerType()))
            {

                if (Cpp2CSettings.Verbose)
                {
                    errs() << "Not transforming "
                           << TopLevelExpansion->Name
                           << " @ "
                           << (*(TopLevelExpansion->Stmts.begin()))->getBeginLoc().printToString(SM)
                           << " because it had function/void pointer type \n";
                }
                // TODO: Emit stats
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
                // TODO: Emit stats
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
                // TODO: Emit stats
                continue;
            }

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
                    TD.getExpansionSignatureOrDeclaration(Ctx);

                string FullTransformationDefinition =
                    TransformedSignature + TD.InitializerOrDefinition;

                TransformedPrototypes.insert(TransformedSignature + ";");
                TransformedDefinitionsAndFunctionDeclExpandedIn.emplace(FullTransformationDefinition, FD);

                MacroDefinitionLocationToTransformedDefinition[TD.Expansion->MI->getDefinitionLoc()]
                    .push_back(TD);

                Stats[EmittedDefinitions] += 1;
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

        // Emit transformed prototypes at the start of the file
        // TODO: Emit after #includes
        // NOTE: In C, we can actually emit multiple declarations of a global
        // var so long as the only one with an initializer is the last one
        // for (auto &&it : TransformedPrototypes)
        // {
        //     RW.InsertText(
        //         SM.getLocForStartOfFile(SM.getMainFileID()),
        //         StringRef(it + "\n\n"));
        //     if (Cpp2CSettings.Verbose)
        //     {
        //         errs() << "Emitted a prototype: "
        //                << it + "\n";
        //     }
        // }

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
            Cpp2C->MultiplyDefinedMacros);
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
