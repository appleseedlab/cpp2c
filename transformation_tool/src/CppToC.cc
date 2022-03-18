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

// TODO: Add transformation of object-like macros to variables to soundness
// proof

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

void printExpansionSignature(ASTContext *Ctx,
                             MacroForest::Node *Expansion,
                             llvm::raw_ostream &os)
{
    os << "[";

    if (Expansion->Stmts.size() == 1)
    {
        os << '"' << getType(Ctx, *Expansion->Stmts.begin()) << '"';
    }
    else if (Expansion->Stmts.size() > 1)
    {
        os << "\"@stmt\"";
    }
    else
    {
        os << "None";
    }

    if (Expansion->MI->isFunctionLike())
    {
        for (auto &Arg : Expansion->Arguments)
        {
            os << ", [\"" << Arg.Name << "\"";
            std::set<std::string> ArgTypes;
            for (const auto *ST : Arg.Stmts)
            {
                ArgTypes.insert('"' + getType(Ctx, ST) + '"');
            }
            if (ArgTypes.size() == 0)
                os << ", None";
            else if (ArgTypes.size() == 1)
                os << ", " << *ArgTypes.begin();
            else
            {
                for (auto &T : ArgTypes)
                {
                    os << ", " << T;
                }
            }
            os << "]";
        }
    }
    os << "]";
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
class CppToCConsumer : public ASTConsumer
{
private:
    CompilerInstance *CI;
    Preprocessor &PP;
    MacroForest::Roots ExpansionRoots;
    set<string> MacroNames;
    set<string> MultiplyDefinedMacros;
    // To give it access to members
    friend class PluginCppToCAction;

public:
    explicit CppToCConsumer(CompilerInstance *CI)
        : CI(CI), PP(CI->getPreprocessor()) {}

    virtual void HandleTranslationUnit(ASTContext &Ctx)
    {
        auto begin_time = std::chrono::high_resolution_clock::now();

        Rewriter RW;
        SourceManager &SM = Ctx.getSourceManager();
        const LangOptions &LO = Ctx.getLangOpts();
        RW.setSourceMgr(SM, LO);

        TranslationUnitDecl *TUD = Ctx.getTranslationUnitDecl();

        // Map for recording transformation statistics

        string
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
            TransformationTime = "Transformation Time (ms)";
        string CSVHeaders[] = {
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
            TransformationTime};
        map<string, unsigned int> Stats;
        for (auto &&Header : CSVHeaders)
        {
            Stats.emplace(Header, 0);
        }

        // Collect the names of all the variables and functions
        // defined in the program
        set<string>
            FunctionNames;
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

        // Step 1: Find Top-Level Macro Expansions
        // Use Cpp2C's visitor to only collect roots in the
        // C language subset instead of using a matcher
        errs() << "Step 1: Search for Macro AST Roots in C subset\n";
        vector<const Stmt *> MacroRoots;
        CSubsetExpansionASTRootsCollector CSEARC(&Ctx, MacroRoots);
        CSEARC.VisitAST();

        // Step 2: Find the AST statements that were directly expanded
        // from the top-level expansions
        errs() << "Step 2: Search for " << ExpansionRoots.size()
               << " Top-Level Expansions in "
               << MacroRoots.size() << " AST-Macro Roots (in the C subset) \n";
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
                // StringRef Name =
                //     Lexer::getImmediateMacroName(ST->getBeginLoc(), SM, LO);
                // errs() << "     Skipped macro expansion "
                //        << Name << "\n";
                Stats[TopLevelExpansionsWithNoExpansionRoot] += 1;
                continue;
            }

            // errs() << "     Match macro "
            //        << ExpansionRoot->Name
            //        << " with "
            //        << ExpansionRoot->SubtreeNodes.size()
            //        << " (nested) expansions\n";

            for (auto Expansion : ExpansionRoot->SubtreeNodes)
            {
                CSubsetInMacroForestExpansionCollector CSIMFEC(
                    &Ctx,
                    Expansion->Stmts, Expansion);

                CSIMFEC.VisitStmt(ST);
            }
        }

        // Step 3 : Within Subtrees, Match the Arguments
        errs() << "Step 3: Find Arguments \n";
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

        // Step 4: Print macro function signatures
        // for (auto ToplevelExpansion : ExpansionRoots)
        // {
        //     for (auto Expansion : ToplevelExpansion->SubtreeNodes)
        //     {
        //         // Skip Expansions that are not a single subtree

        //         // if (m_settings.only_toplevel_macros &&
        //         //     !(Expansion == ToplevelExpansion))
        //         //     continue;

        //         // SANITY CHECK: This is a sanity check that ensures
        //         // the structural integrity of the dumped tree.
        //         if (dumpedNodes.find(Expansion->Parent) == dumpedNodes.end())
        //         {
        //             assert(false);
        //         }
        //         dumpedNodes.insert(Expansion);

        //         Expansion->Root->SpellingRange.print(errs(), SM);
        //         errs() << ";" << Expansion->Name;
        //         errs() << ";" << Expansion->MI->isFunctionLike();
        //         errs() << ";" << Expansion->Arguments.size();
        //         // Dump the structure of our macro expansion-tree
        //         errs() << ";" << (void *)Expansion << ";"
        //                << (void *)Expansion->Parent;
        //         errs() << ";" << Expansion->Stmts.size() << ";";
        //         if (Expansion->Stmts.size() > 0)
        //         {
        //             printExpansionSignature(&Ctx, Expansion, errs());
        //         }
        //         errs() << "\n";
        //     }
        // }

        map<string, string> TransformedDefinitionToName;
        // Step 5: Determine which macros are hygienic.
        for (auto TopLevelExpansion : ExpansionRoots)
        {
            // Check that the expansion maps to a single expansion
            if (TopLevelExpansion->SubtreeNodes.size() < 0)
            {
                // errs() << "Skipping expanion of "
                //        << TopLevelExpansion->Name
                //        << " because it did not "
                //           "have an expansion\n";
                Stats[TopLevelExpansionsWithNoExpansionRoot] += 1;
                continue;
            }

            // Check that macro contains no nested expansions
            if (TopLevelExpansion->SubtreeNodes.size() > 1)
            {
                // errs() << "Skipping expanion of "
                //        << TopLevelExpansion->Name
                //        << " because it contained multiple expansions\n";
                Stats[TopLevelExpansionsWithMultipleExpansionRoots] += 1;
                continue;
            }

            // Check that the expansion maps to a single AST expression
            if (TopLevelExpansion->Stmts.size() != 1)
            {
                // errs() << "Skipping expanion of "
                //        << TopLevelExpansion->Name
                //        << " because it did not "
                //           "have a single AST node\n";
                Stats[TopLevelExpansionsWithMultipleASTNodes] += 1;
                continue;
            }

            // Check that expansion has an unambiguous signature
            if (!expansionHasUnambiguousSignature(&Ctx, TopLevelExpansion))
            {
                // errs() << "Skipping expanion of "
                //        << TopLevelExpansion->Name
                //        << " because its function signature was "
                //           "ambiguous \n";
                Stats[TopLevelExpansionsWithAmbiguousSignature] += 1;
                continue;
            }

            auto ST = *TopLevelExpansion->Stmts.begin();
            auto E = dyn_cast_or_null<Expr>(ST);

            if (!E)
            {
                // errs() << "Skipping expanion of "
                //        << TopLevelExpansion->Name
                //        << " because it did not "
                //           "expand to an expression\n";
                Stats[TopLevelExpansionsThatDidNotExpandToAnExpression] += 1;
                continue;
            }

            auto ExpansionBegin = TopLevelExpansion->SpellingRange.getBegin();
            auto ExpansionEnd = TopLevelExpansion->SpellingRange.getEnd();

            auto ExpressionRange =
                SM.getExpansionRange(E->getSourceRange());
            auto ExpressionBegin = ExpressionRange.getBegin();
            auto ExpressionEnd = ExpressionRange.getEnd();

            // Check that expression is completely covered by expansion
            if (!(ExpansionBegin == ExpressionBegin &&
                  ExpansionEnd == ExpressionEnd))
            {
                // errs() << "Skipping expanion of "
                //        << TopLevelExpansion->Name
                //        << " because its expression did not align perfectly "
                //           "with its expansion\n";
                Stats[TopLevelExpansionsWithUnalignedBody] += 1;
                continue;
            }

            // It would be better to check that the number of tokens in the
            // expression is >= to the number of tokens in the macro
            // definition, but we don't an easy way of accessing the number
            // of tokens in an arbitrary expression
            if (!PP.isAtEndOfMacroExpansion(E->getEndLoc()))
            {
                // errs() << "Skipping expanion of "
                //        << TopLevelExpansion->Name
                //        << " because its expression's end did not extend to "
                //           "end of its expansion\n";
                Stats[TopLevelExpansionsWithExpressionEndNotAtEndOfExpansion] += 1;
                continue;
            }

            // Check that expanded macro is not multiply defined
            if (MultiplyDefinedMacros.find(TopLevelExpansion->Name) !=
                MultiplyDefinedMacros.end())
            {
                // errs() << "Skipping expanion of "
                //        << TopLevelExpansion->Name
                //        << " because the macro is multiply-defined\n";
                Stats[TopLevelExpansionsOfMultiplyDefinedMacros] += 1;
                continue;
            }

            // Check that each argument is expanded the expected number of
            // times, and that if it has multiple expansions, they all
            // expand to the same tree
            {
                bool hasUnhygienicArg = false;
                for (auto &&Arg : TopLevelExpansion->Arguments)
                {
                    if (Arg.Stmts.size() == 0)
                    {
                        // errs() << "Skipping expanion of "
                        //        << TopLevelExpansion->Name
                        //        << " because its argument "
                        //        << Arg.Name << " was not expanded\n";
                        Stats[TopLevelExpanionsWithUnexpandedArgument] += 1;
                        hasUnhygienicArg = true;
                        break;
                    }

                    // Check that we found the expected number of expansions
                    // for this argument
                    unsigned ExpectedExpansions =
                        TopLevelExpansion->ExpectedASTNodesForArg[Arg.Name];
                    unsigned ActualExpansions = Arg.Stmts.size();
                    if (ActualExpansions != ExpectedExpansions)
                    {
                        // errs() << "Skipping expanion of "
                        //        << TopLevelExpansion->Name
                        //        << " because its argument "
                        //        << Arg.Name << " was not expanded the "
                        //        << "expected number of times: "
                        //        << ExpectedExpansions << " vs " << ActualExpansions
                        //        << "\n";
                        Stats[TopLevelExpansionsWithMismatchingArgumentExpansionsAndASTNodes] += 1;
                        hasUnhygienicArg = true;
                        break;
                    }

                    auto ArgFirstExpansion = *Arg.Stmts.begin();
                    for (auto ArgExpansion : Arg.Stmts)
                    {
                        if (!compareTrees(&Ctx, ArgFirstExpansion, ArgExpansion))
                        {
                            // errs() << "Skipping expanion of "
                            //        << TopLevelExpansion->Name
                            //        << " because its argument "
                            //        << Arg.Name << " was not expanded to "
                            //        << "a consistent AST structure\n";
                            Stats[TopLevelExpansionsWithInconsistentArgumentExpansions] += 1;
                            hasUnhygienicArg = true;
                            break;
                        }

                        // Check that spelling location of the AST node and
                        // all its subexpressions fall within the range
                        // argument's token ranges
                        // FIXME: This may render invocations
                        // which contain invocations as arguments as
                        // untransformable, but that doesn't make the
                        // transformation unsound
                        // errs() << "Token ranges: ";
                        // Arg.TokenRanges.dump(SM);
                        // errs() << "\n";
                        auto ArgExpression = dyn_cast_or_null<Expr>(ArgExpansion);
                        assert(nullptr != ArgExpression);
                        if (!CSubsetExprAndSubExprsSpelledInRanges::exprAndSubExprsSpelledInRanges(
                                &Ctx, ArgExpression, &Arg.TokenRanges))
                        {

                            // errs() << "Skipping expanion of "
                            //        << TopLevelExpansion->Name
                            //        << " because its argument "
                            //        << Arg.Name << " was matched with an AST node "
                            //        << "with an expression or subexpression "
                            //        << "with a spelling location outside of the "
                            //        << "spelling locations of the arg's "
                            //        << "token ranges\n";
                            Stats[TopLevelExpansionsWithArgumentsWhoseASTNodesHaveSpellingLocationsNotInArgumentTokenRanges] += 1;
                            hasUnhygienicArg = true;
                            break;
                        }
                    }
                    if (hasUnhygienicArg)
                    {
                        break;
                    }
                }
                if (hasUnhygienicArg)
                {
                    continue;
                }
            }

            // Check that the expansion does not contain local variables
            if (CSubsetContainsLocalVars::containsLocalVars(&Ctx, E))
            {
                // errs() << "Skipping expanion of "
                //        << TopLevelExpansion->Name
                //        << " because its expression contained local vars\n";
                Stats[TopLevelExpansionsWithLocalVars] += 1;
                continue;
            }

            // Check that the expansion does not contain side-effects
            if (CSubsetHasSideEffects::hasSideEffects(&Ctx, E))
            {
                // errs() << "Skipping expanion of "
                //        << TopLevelExpansion->Name
                //        << " because its expression had side-effects\n";
                Stats[TopLevelExpansionsWithSideEffects] += 1;
                continue;
            }

            //// Transform the expansion

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

                    // Insert the full transformation into the program after
                    // last-declared decl of var in the expression
                    // TODO: Check that emitting the transformation here
                    // doesn't cause us to emit the transformation outside
                    // of the main file
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
        }

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

        // Maybe it would better to just overwrite the files directly?
        // RW.overwriteChangedFiles();

        auto end_time = std::chrono::high_resolution_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::microseconds>(
                            end_time - begin_time)
                            .count();
        Stats[TransformationTime] = duration;

        // Dump the transformation stats to CSV
        printMapToCSV(errs(), Stats);
    }
};

// Wrap everything into a plugin
class PluginCppToCAction : public PluginASTAction
{

protected:
    unique_ptr<ASTConsumer>
    CreateASTConsumer(CompilerInstance &CI,
                      StringRef file) override
    {
        auto &PP = CI.getPreprocessor();
        auto Cpp2C = make_unique<CppToCConsumer>(&CI);

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
        return true;
    }

    // Necessary for ANYTHING to print to stderr
    ActionType getActionType() override
    {
        return ActionType::AddBeforeMainAction;
    }
};

//-----------------------------------------------------------------------------
// Registration
//-----------------------------------------------------------------------------
static FrontendPluginRegistry::Add<PluginCppToCAction>
    X("cpp-to-c", "Transform CPP macros to C functions");
