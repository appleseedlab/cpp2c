#include "clang/AST/ASTContext.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ParentMapContext.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendPluginRegistry.h"
#include "clang/Lex/MacroArgs.h"
#include "clang/Lex/PPCallbacks.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/Rewrite/Frontend/Rewriters.h"

#include "llvm/Support/raw_ostream.h"

#include "CollectDeclNamesVisitor.h"
#include "CSubsetExpansionASTRootsCollector.h"
#include "CSubsetFindLastDefinedVar.h"
#include "CSubsetHasSideEffects.h"
#include "CSubsetExprAndSubExprsSpelledInRanges.h"
#include "CSubsetContainsLocalVars.h"
#include "CSubsetContainsVars.h"
#include "CSubsetInMacroForestExpansionCollector.h"
#include "CSubsetInSourceRangeCollectionCollector.h"
#include "MacroForest.h"
#include "MacroNameCollector.h"

#include <iostream>

using namespace clang;
using namespace llvm;
using namespace std;

using namespace clang::ast_matchers;

// This file is hardly a paragon of pulchritude, but the logic is correct
// and so far Cpp2C works without issue

// TODO: Add transformation of object-like macros to variables to soundness
// proof

// Headers for dumping transformation stats to CSV
string
    TopLevelExpansionsInMainFile = "Top Level Expansions In Main File",
    TopLevelObjectLikeMacroExpansionsInMainFile = "Top Level Object-like Macro Expansions Found",
    TopLevelFunctionLikeMacroExpansionsInMainFile = "Top Level Function-like Macro Expansions Found",
    TopLevelExpansionsWithNoExpansionRoot = "Top Level Expanions with No Expansion Root",
    TopLevelExpansionsWithMultipleExpansionRoots = "Top Level Expansions with Multiple Expansion Roots",
    TopLevelExpansionsWithMultipleASTNodes = "Top Level Expansions with Multiple AST Nodes",
    TopLevelExpansionsWithAmbiguousSignature = "Top Level Expansions with an Ambiguous Signature",
    TopLevelExpansionsThatDidNotExpandToAnExpression = "Top Level Expansions that did not Expand to an Expression",
    TopLevelExpansionsWithUnalignedBody = "Top Level Expansions with an Unaligned Body",
    TopLevelExpansionsWithExpressionEndNotAtEndOfExpansion = "Top Level Expansions with an Expression that did not End at the End of the Expansion",
    TopLevelExpansionsOfMultiplyDefinedMacros = "Top Level Expansions of Multiply Defined (or Redefined) Macros",
    TopLevelExpanionsWithUnexpandedArgument = "Top Level Expansions with an Unexpanded Argument",
    TopLevelExpansionsWithMismatchingArgumentExpansionsAndASTNodes = "Top Level Expansions with Mismatching Argument Expansions and AST Nodes",
    TopLevelExpansionsWithInconsistentArgumentExpansions = "Top Level Expansions with Inconsistent Argument Expansions",
    TopLevelExpansionsWithArgumentsWhoseASTNodesHaveSpellingLocationsNotInArgumentTokenRanges = "Top Level Expansions with Arguments whose AST Nodes have Spelling Locations not in Argument Token Rages",
    TopLevelExpansionsWithLocalVars = "Top Level Expansions with Local Vars",
    TopLevelExpansionsWithSideEffects = "Top Level Expansions with Side-effects",
    TransformedTopLevelExpansions = "Successfully Transformed Top Level Expansions",
    TransformedTopLevelObjectLikeMacroExpansions = "Successfully Transformed Top Level Object-like Macro Expansions",
    TransformedTopLevelFunctionLikeMacroExpansions = "Successfully Transformed Top Level Function-like Macro Expansions",
    UntransformedTopLevelExpansions = "Top Level Expansions not Transformed",
    UntransformedTopLevelObjectLikeMacroExpansions = "Top Level Object-like Expansions not Transformed",
    UntransformedTopLevelFunctionLikeMacroExpansions = "Top Level Function-like Expansions not Transformed",
    TopLevelExpanionsWithTransformationsNotInMainFile = "Top Level Expansions with Transformations Not In Main File (not transformed)",
    TransformationTime = "Transformation Time (ms)",
    FileSize = "File Size (bytes)";

struct PluginSettings
{
    bool OverwriteFiles = false;
    bool Verbose = false;
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

string getType(ASTContext *Ctx, const Stmt *ST)
{
    if (const auto E = dyn_cast_or_null<Expr>(ST))
    {
        QualType T = E->getType();
        return T.getDesugaredType(*Ctx).getCanonicalType().getAsString();
    }
    return "@stmt";
}

bool expansionHasUnambiguousSignature(ASTContext *Ctx,
                                      MacroForest::Node *Expansion)
{
    if (Expansion->Stmts.size() != 1)
    {
        return false;
    }
    if (Expansion->MI->isFunctionLike())
    {
        for (auto &Arg : Expansion->Arguments)
        {
            std::set<std::string> ArgTypes;
            for (const auto *ST : Arg.Stmts)
            {
                ArgTypes.insert('"' + getType(Ctx, ST) + '"');
            }
            if (ArgTypes.size() != 1)
            {
                return false;
            }
        }
    }
    return true;
}

bool isExpansionHygienic(ASTContext *Ctx,
                         Preprocessor &PP,
                         MacroForest::Node *TopLevelExpansion,
                         map<string, unsigned> &Stats,
                         PluginSettings Cpp2CSettings,
                         set<string> &MultiplyDefinedMacros)
{
    // Check that the expansion maps to a single expansion
    if (TopLevelExpansion->SubtreeNodes.size() < 0)
    {
        if (Cpp2CSettings.Verbose)
        {
            errs() << "Skipping expanion of "
                   << TopLevelExpansion->Name
                   << " because it did not "
                      "have an expansion\n";
        }
        Stats[TopLevelExpansionsWithNoExpansionRoot] += 1;
        return false;
    }

    // Check that macro contains no nested expansions
    if (TopLevelExpansion->SubtreeNodes.size() > 1)
    {
        if (Cpp2CSettings.Verbose)
        {
            errs() << "Skipping expanion of "
                   << TopLevelExpansion->Name
                   << " because it contained multiple expansions\n";
        }
        Stats[TopLevelExpansionsWithMultipleExpansionRoots] += 1;
        return false;
    }

    // Check that the expansion maps to a single AST expression
    if (TopLevelExpansion->Stmts.size() != 1)
    {
        if (Cpp2CSettings.Verbose)
        {
            errs() << "Skipping expanion of "
                   << TopLevelExpansion->Name
                   << " because it did not "
                      "have a single AST node\n";
        }
        Stats[TopLevelExpansionsWithMultipleASTNodes] += 1;
        return false;
    }

    // Check that expansion has an unambiguous signature
    if (!expansionHasUnambiguousSignature(Ctx, TopLevelExpansion))
    {
        if (Cpp2CSettings.Verbose)
        {
            errs() << "Skipping expanion of "
                   << TopLevelExpansion->Name
                   << " because its function signature was "
                      "ambiguous \n";
        }
        Stats[TopLevelExpansionsWithAmbiguousSignature] += 1;
        return false;
    }

    auto ST = *TopLevelExpansion->Stmts.begin();
    auto E = dyn_cast_or_null<Expr>(ST);

    if (!E)
    {
        if (Cpp2CSettings.Verbose)
        {
            errs() << "Skipping expanion of "
                   << TopLevelExpansion->Name
                   << " because it did not "
                      "expand to an expression\n";
        }
        Stats[TopLevelExpansionsThatDidNotExpandToAnExpression] += 1;
        return false;
    }

    auto ExpansionBegin = TopLevelExpansion->SpellingRange.getBegin();
    auto ExpansionEnd = TopLevelExpansion->SpellingRange.getEnd();

    SourceManager &SM = Ctx->getSourceManager();

    auto ExpressionRange = SM.getExpansionRange(E->getSourceRange());
    auto ExpressionBegin = ExpressionRange.getBegin();
    auto ExpressionEnd = ExpressionRange.getEnd();

    // Check that expression is completely covered by expansion
    if (!(ExpansionBegin == ExpressionBegin &&
          ExpansionEnd == ExpressionEnd))
    {
        if (Cpp2CSettings.Verbose)
        {
            errs() << "Skipping expanion of "
                   << TopLevelExpansion->Name
                   << " because its expression did not align perfectly "
                      "with its expansion\n";
        }
        Stats[TopLevelExpansionsWithUnalignedBody] += 1;
        return false;
    }

    // It would be better to check that the number of tokens in the
    // expression is >= to the number of tokens in the macro
    // definition, but we don't an easy way of accessing the number
    // of tokens in an arbitrary expression
    if (!PP.isAtEndOfMacroExpansion(E->getEndLoc()))
    {
        if (Cpp2CSettings.Verbose)
        {
            errs() << "Skipping expanion of "
                   << TopLevelExpansion->Name
                   << " because its expression's end did not extend to "
                      "end of its expansion\n";
        }
        Stats[TopLevelExpansionsWithExpressionEndNotAtEndOfExpansion] += 1;
        return false;
    }

    // Check that expanded macro is not multiply defined
    if (MultiplyDefinedMacros.find(TopLevelExpansion->Name) !=
        MultiplyDefinedMacros.end())
    {
        if (Cpp2CSettings.Verbose)
        {
            errs() << "Skipping expanion of "
                   << TopLevelExpansion->Name
                   << " because the macro is multiply-defined\n";
        }
        Stats[TopLevelExpansionsOfMultiplyDefinedMacros] += 1;
        return false;
    }

    // Check that each argument is expanded the expected number of
    // times, and that if it has multiple expansions, they all
    // expand to the same tree
    for (auto &&Arg : TopLevelExpansion->Arguments)
    {
        if (Arg.Stmts.size() == 0)
        {
            if (Cpp2CSettings.Verbose)
            {
                errs() << "Skipping expanion of "
                       << TopLevelExpansion->Name
                       << " because its argument "
                       << Arg.Name << " was not expanded\n";
            }
            Stats[TopLevelExpanionsWithUnexpandedArgument] += 1;
            return false;
        }

        // Check that we found the expected number of expansions
        // for this argument
        unsigned ExpectedExpansions =
            TopLevelExpansion->ExpectedASTNodesForArg[Arg.Name];
        unsigned ActualExpansions = Arg.Stmts.size();
        if (ActualExpansions != ExpectedExpansions)
        {
            if (Cpp2CSettings.Verbose)
            {
                errs() << "Skipping expanion of "
                       << TopLevelExpansion->Name
                       << " because its argument "
                       << Arg.Name << " was not expanded the "
                       << "expected number of times: "
                       << ExpectedExpansions << " vs " << ActualExpansions
                       << "\n";
            }
            Stats[TopLevelExpansionsWithMismatchingArgumentExpansionsAndASTNodes] += 1;
            return false;
        }

        auto ArgFirstExpansion = *Arg.Stmts.begin();
        for (auto ArgExpansion : Arg.Stmts)
        {
            if (!compareTrees(Ctx, ArgFirstExpansion, ArgExpansion))
            {
                if (Cpp2CSettings.Verbose)
                {
                    errs() << "Skipping expanion of "
                           << TopLevelExpansion->Name
                           << " because its argument "
                           << Arg.Name << " was not expanded to "
                           << "a consistent AST structure\n";
                }
                Stats[TopLevelExpansionsWithInconsistentArgumentExpansions] += 1;
                return false;
            }

            // Check that spelling location of the AST node and
            // all its subexpressions fall within the range
            // argument's token ranges
            // FIXME: This may render invocations
            // which contain invocations as arguments as
            // untransformable, but that doesn't make the
            // transformation unsound
            auto ArgExpression = dyn_cast_or_null<Expr>(ArgExpansion);
            assert(nullptr != ArgExpression);
            if (!CSubsetExprAndSubExprsSpelledInRanges::exprAndSubExprsSpelledInRanges(
                    Ctx, ArgExpression, &Arg.TokenRanges))
            {
                if (Cpp2CSettings.Verbose)
                {
                    errs() << "Skipping expanion of "
                           << TopLevelExpansion->Name
                           << " because its argument "
                           << Arg.Name << " was matched with an AST node "
                           << "with an expression or subexpression "
                           << "with a spelling location outside of the "
                           << "spelling locations of the arg's "
                           << "token ranges\n";
                }
                Stats[TopLevelExpansionsWithArgumentsWhoseASTNodesHaveSpellingLocationsNotInArgumentTokenRanges] += 1;
                return false;
            }
        }
    }

    // Check that the expansion does not contain local variables
    if (CSubsetContainsLocalVars::containsLocalVars(Ctx, E))
    {
        if (Cpp2CSettings.Verbose)
        {
            errs() << "Skipping expanion of "
                   << TopLevelExpansion->Name
                   << " because its expression contained local vars\n";
        }
        Stats[TopLevelExpansionsWithLocalVars] += 1;
        return false;
    }

    // Check that the expansion does not contain side-effects
    if (CSubsetHasSideEffects::hasSideEffects(Ctx, E))
    {
        if (Cpp2CSettings.Verbose)
        {
            errs() << "Skipping expanion of "
                   << TopLevelExpansion->Name
                   << " because its expression had side-effects\n";
        }
        Stats[TopLevelExpansionsWithSideEffects] += 1;
        return false;
    }

    return true;
}

string getTransformedName(SourceManager &SM,
                          MacroForest::Node *Expansion,
                          bool TransformToVar)
{
    string Filename =
        SM.getFilename(Expansion->SpellingRange.getBegin()).str();

    string transformType = TransformToVar ? "var" : "function";

    // Remove non-alphanumeric characters from the filename
    Filename.erase(remove_if(Filename.begin(), Filename.end(),
                             [](auto const &c) -> bool
                             { return !isalnum(c); }),
                   Filename.end());

    // Prepend the name with the name of the file that the macro was spelled
    // in (with non-alphanumerics removed).
    // We do this to ensure that transformation names are unique across files
    // FIXME: This solution isn't perfect. Example: abc_1.c and abc1.c would
    // both erase to abc1c. If both of these files contained an expansion
    // of macro from a header that they both included, that macro would be
    // transformed to a global var/function with the same name in each of them.
    // We would then get new errors if we try to link these transformed files
    // together.
    return Filename + "_" + Expansion->Name + "_" + transformType;
}

string getExpansionSignature(ASTContext *Ctx,
                             MacroForest::Node *Expansion,
                             bool TransformToVar,
                             string TransformedName)
{
    assert(expansionHasUnambiguousSignature(Ctx, Expansion));

    string Signature = getType(Ctx, *Expansion->Stmts.begin());
    Signature += " " + TransformedName;
    if (!TransformToVar)
    {

        Signature += "(";
        unsigned i = 0;
        for (auto &&Arg : Expansion->Arguments)
        {
            string ArgType = getType(Ctx, *(Arg.Stmts.begin()));
            if (i >= 1)
            {
                Signature += ", ";
            }
            Signature += Arg.Name;
            i += 1;
        }
        Signature += ")";
    }
    // Add const qualifier if the expansion was transformed to a global var
    if (TransformToVar)
    {
        Signature = "const " + Signature;
    }
    return Signature;
}

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

        // Map for recording transformation statistics
        string CSVHeaders[] = {
            TopLevelExpansionsInMainFile,
            TopLevelObjectLikeMacroExpansionsInMainFile,
            TopLevelFunctionLikeMacroExpansionsInMainFile,
            TopLevelExpansionsWithNoExpansionRoot,
            TopLevelExpansionsWithMultipleExpansionRoots,
            TopLevelExpansionsWithMultipleASTNodes,
            TopLevelExpansionsWithAmbiguousSignature,
            TopLevelExpansionsThatDidNotExpandToAnExpression,
            TopLevelExpansionsWithUnalignedBody,
            TopLevelExpansionsWithExpressionEndNotAtEndOfExpansion,
            TopLevelExpansionsOfMultiplyDefinedMacros,
            TopLevelExpanionsWithUnexpandedArgument,
            TopLevelExpansionsWithMismatchingArgumentExpansionsAndASTNodes,
            TopLevelExpansionsWithInconsistentArgumentExpansions,
            TopLevelExpansionsWithArgumentsWhoseASTNodesHaveSpellingLocationsNotInArgumentTokenRanges,
            TopLevelExpansionsWithLocalVars,
            TopLevelExpansionsWithSideEffects,
            TransformedTopLevelExpansions,
            TransformedTopLevelObjectLikeMacroExpansions,
            TransformedTopLevelFunctionLikeMacroExpansions,
            UntransformedTopLevelExpansions,
            UntransformedTopLevelObjectLikeMacroExpansions,
            UntransformedTopLevelFunctionLikeMacroExpansions,
            TopLevelExpanionsWithTransformationsNotInMainFile,
            TransformationTime,
            FileSize};
        map<string, unsigned int> Stats;
        for (auto &&Header : CSVHeaders)
        {
            Stats.emplace(Header, 0);
        }

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
        // Use Cpp2C's visitor to only collect roots in the
        // C language subset instead of using a matcher
        if (Cpp2CSettings.Verbose)
        {
            errs() << "Step 1: Search for Macro AST Roots in C subset\n";
        }
        vector<const Stmt *> MacroRoots;
        CSubsetExpansionASTRootsCollector CSEARC(&Ctx, MacroRoots);
        CSEARC.VisitAST();

        // Step 2: Find the AST statements that were directly expanded
        // from the top-level expansions
        if (Cpp2CSettings.Verbose)
        {
            errs() << "Step 2: Search for " << ExpansionRoots.size()
                   << " Top-Level Expansions in "
                   << MacroRoots.size() << " AST-Macro Roots (in the C subset) \n";
        }
        for (const auto ST : MacroRoots)
        {
            SourceLocation STExpansionLoc =
                SM.getExpansionLoc(ST->getBeginLoc());
            MacroForest::Node *ExpansionRoot = nullptr;
            for (auto Expansion : ExpansionRoots)
            {
                // Check if the ExpansionRoot and the Node have the
                // same Expansion Location. Previously, we checked if
                // the STExpansionLoc was contained in the Spelling
                // Range. However, this might even span files if macro
                // name and argument list are composed in a macro.
                SourceLocation NodeExpansionLoc =
                    SM.getExpansionLoc(Expansion->SpellingRange.getBegin());
                if (NodeExpansionLoc == STExpansionLoc)
                {
                    // Found the expansion that this expression was expanded
                    // from
                    ExpansionRoot = Expansion;
                    break;
                }
            }

            // If ExpansionRoot is still nulltpr at this point, then we could
            // not find an expansion root that this statement expanded from
            if (ExpansionRoot == nullptr)
            {
                if (Cpp2CSettings.Verbose)
                {
                    StringRef Name =
                        Lexer::getImmediateMacroName(ST->getBeginLoc(), SM, LO);
                    errs() << "     Skipped macro expansion "
                           << Name << "\n";
                }
                continue;
            }
            if (Cpp2CSettings.Verbose)
            {
                errs() << "     Match macro "
                       << ExpansionRoot->Name
                       << " with "
                       << ExpansionRoot->SubtreeNodes.size()
                       << " (nested) expansions\n";
            }
            for (auto Expansion : ExpansionRoot->SubtreeNodes)
            {
                CSubsetInMacroForestExpansionCollector CSIMFEC(
                    &Ctx,
                    Expansion->Stmts, Expansion);

                CSIMFEC.VisitStmt(ST);
            }
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
                {
                    // most of the time only a single one.
                    for (auto &Arg : Expansion->Arguments)
                    {
                        CSubsetInSourceRangeCollectionCollector CSISRCC(
                            &Ctx, Arg.Stmts, &Arg.TokenRanges);
                        CSISRCC.VisitStmt(ST);
                    }
                }
            }
        }

        std::set<void *> dumpedNodes;
        dumpedNodes.insert(nullptr);

        map<string, string> TransformedDefinitionToName;
        // Step 4: Transform hygienic macros.
        if (Cpp2CSettings.Verbose)
        {
            errs() << "Step 4: Transform hygienic macros \n";
        }

        for (auto TopLevelExpansion : ExpansionRoots)
        {

            if (!isExpansionHygienic(&Ctx, PP, TopLevelExpansion, Stats,
                                     Cpp2CSettings, MultiplyDefinedMacros))
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
                !CSubsetContainsVars::containsVars(&Ctx, E);

            // Generate the function body
            SourceLocation MacroBodyBegin =
                TopLevelExpansion->MI->tokens().front().getLocation();
            SourceLocation MacroBodyEnd = Lexer::getLocForEndOfToken(
                TopLevelExpansion->DefinitionRange.getEnd(), 0, SM, LO);

            SourceRange MacroBodyRange =
                SourceRange(MacroBodyBegin, MacroBodyEnd);
            CharSourceRange MacroBodyCharRange =
                CharSourceRange::getCharRange(MacroBodyRange);
            string TransformedBody = Lexer::getSourceText(
                                         MacroBodyCharRange, SM, LO)
                                         .str();
            string TransformedDefinition =
                (TransformToVar
                     ? " = " + TransformedBody + ";"
                     : " { return " + TransformedBody + "; }");

            // If an identical transformation for this expansion exists,
            // use it; otherwise generate a unique name for this transformation
            // and insert its definition into the program
            string TransformedName;
            if (TransformedDefinitionToName.find(TransformedDefinition) !=
                TransformedDefinitionToName.end())
            {
                TransformedName =
                    TransformedDefinitionToName[TransformedDefinition];
            }
            else
            {
                string Basename = getTransformedName(SM, TopLevelExpansion,
                                                     TransformToVar);
                TransformedName = Basename;
                unsigned suffix = 0;
                while (FunctionNames.find(TransformedName) != FunctionNames.end() &&
                       VarNames.find(TransformedName) != VarNames.end() &&
                       MacroNames.find(TransformedName) != MacroNames.end())
                {
                    TransformedName = Basename + "_" + to_string(suffix);
                    suffix += 1;
                }
                FunctionNames.insert(TransformedName);
                VarNames.insert(TransformedName);
                MacroNames.insert(TransformedName);
                TransformedDefinitionToName[TransformedDefinition] =
                    TransformedName;

                string TransformedSignature =
                    getExpansionSignature(&Ctx, TopLevelExpansion,
                                          TransformToVar,
                                          TransformedName);
                string FullTransformationDefinition =
                    TransformedSignature + TransformedDefinition + "\n\n";

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
                if (CSubsetContainsVars::containsVars(&Ctx, E))
                {
                    SourceLocation EndOfDecl = StartOfFile;
                    auto VD =
                        CSubsetFindLastDefinedVar::findLastDefinedVar(&Ctx, E);
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
            }

            // Rewrite the invocation into a function call
            string CallOrRef = TransformedName;
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
                llvm::errs() << "Unknown argument: " << arg << '\n';
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