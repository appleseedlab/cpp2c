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

// TODO: Add transformation of object-like macros to variables to soundness
// proof

struct PluginSettings
{
    bool OverwriteFiles = false;
    bool Verbose = false;
    bool UnifyMacrosWithDifferentNames = false;
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
        // TODO: Use macro definition location as the key instead
        map<string, vector<struct TransformedDefinition>>
            MacroNameToEmittedTransformedDefinitions;

        // Step 4: Transform hygienic macros.
        if (Cpp2CSettings.Verbose)
        {
            errs() << "Step 4: Transform hygienic macros \n";
        }

        for (auto TopLevelExpansion : ExpansionRoots)
        {

            if (!isExpansionHygienic(&Ctx, PP, TopLevelExpansion, Stats,
                                     Cpp2CSettings.Verbose,
                                     MultiplyDefinedMacros))
            {
                Stats[UntransformedTopLevelExpansions] += 1;
                if (TopLevelExpansion->MI->isObjectLike())
                {

                    Stats[UntransformedTopLevelObjectLikeMacroExpansions] += 1;
                }
                else
                {
                    Stats[UntransformedTopLevelFunctionLikeMacroExpansions]++;
                }
                continue;
            }

            if (mustBeConstExpr(Ctx, *TopLevelExpansion->Stmts.begin()))
            {
                Stats[UntransformedTopLevelExpansions] += 1;
                if (TopLevelExpansion->MI->isObjectLike())
                {

                    Stats[UntransformedTopLevelObjectLikeMacroExpansions] += 1;
                }
                else
                {
                    Stats[UntransformedTopLevelFunctionLikeMacroExpansions]++;
                }
                Stats[ConstExprExpansionsFound] += 1;
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
                containsVars(E);

            // Create the transformed definition.
            // Note that this generates the transformed definition as well.
            struct TransformedDefinition TD =
                NewTransformedDefinition(&Ctx, TopLevelExpansion,
                                         TransformToVar);

            // If an identical transformation for this expansion exists,
            // use it; otherwise generate a unique name for this transformation
            // and insert its definition into the program
            string EmittedName = "";
            if (Cpp2CSettings.UnifyMacrosWithDifferentNames)
            {
                // If we are ignoring macro names, then we have to check
                // all transformed definitions for an identical one
                for (auto &&MacroNameAndTransformedDefinitions : MacroNameToEmittedTransformedDefinitions)
                {
                    for (auto &&ETD : MacroNameAndTransformedDefinitions.second)
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
                // Otherwise, we can use the macro name to quickly find
                // any identical prior transformations
                if (MacroNameToEmittedTransformedDefinitions.find(TD.OriginalMacroName) !=
                    MacroNameToEmittedTransformedDefinitions.end())
                {
                    // Find which, if any, of the prior transformation
                    // definitions of this macro are identical to the one
                    // we are considering adding to the program.
                    for (auto &&ETD : MacroNameToEmittedTransformedDefinitions[TD.OriginalMacroName])
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
                    getExpansionSignature(&Ctx, TopLevelExpansion,
                                          TransformToVar,
                                          EmittedName);
                string FullTransformationDefinition =
                    TransformedSignature + TD.InitializerOrDefinition + "\n\n";

                // Emit the transformation to the top of the file in which
                // the macro was expanded.
                // If we were to emit the transformation at the top of the
                // file in which the macro was defined, we may end up writing
                // the transformation to a header file. This would be bad
                // because that header file may be included by other files
                // with vars/functions/macros that have the same identifier
                // as the transformed name
                SourceLocation StartOfFile = SM.getLocForStartOfFile(
                    SM.getFileID(TopLevelExpansion->SpellingRange.getBegin()));

                // Emit transformed definitions that refer to global
                // vars after the global var is declared
                // NOTE: An invariant at this point is that any vars in
                // the expansion are global vars
                if (containsVars(E))
                {
                    SourceLocation EndOfDecl = StartOfFile;
                    auto VD =
                        findLastDefinedVar(E);
                    assert(VD != nullptr);
                    // If the decl has an initialization, then the
                    // transformation location is just beyond it; otherwise
                    // its after the decl itself
                    if (VD->hasInit())
                    {
                        auto Init = VD->getInit();
                        EndOfDecl = Init->getEndLoc();
                    }
                    else
                    {
                        EndOfDecl = VD->getEndLoc();
                    }
                    // Go to the spot right after the semicolon at the end of
                    // this decl
                    auto NextTok =
                        Lexer::findNextToken(EndOfDecl, SM, LO);
                    assert(NextTok.hasValue());
                    auto Semicolon = NextTok.getValue();

                    // Check that emitting the transformation here
                    // doesn't cause us to emit the transformation outside
                    // of the main file
                    if (!SM.isInMainFile(Semicolon.getLocation()))
                    {
                        Stats[TopLevelExpanionsWithTransformationsNotInMainFile] += 1;
                        continue;
                    }
                    // Insert the full transformation into the program after
                    // last-declared decl of var in the expression.
                    RW.InsertTextAfterToken(
                        Semicolon.getLocation(),
                        StringRef("\n\n" + FullTransformationDefinition));
                }
                else
                {
                    // Insert the full transformation at the start
                    // of the program
                    RW.InsertText(StartOfFile,
                                  StringRef(FullTransformationDefinition));
                }

                MacroNameToEmittedTransformedDefinitions[TD.OriginalMacroName].push_back(TD);
                if (Cpp2CSettings.Verbose)
                {
                    errs() << "Emitted a definition: " +
                                  EmittedName + "\n";
                }
                Stats[EmittedDefinitions] += 1;
            }

            // Rewrite the invocation into a function call
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
                        CallOrRef += ArgSourceText;
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
                Cpp2CSettings.UnifyMacrosWithDifferentNames = true;
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
