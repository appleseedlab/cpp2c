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

#include "CollectDeclNamesVisitor.hh"
#include "ExpansionUtils.hh"
#include "ForestCollector.hh"
#include "MacroExpansionNode.hh"
#include "MacroForest.hh"
#include "MacroNameCollector.hh"
#include "Matchers.hh"
#include "NodeCollector.hh"
#include "TransformedDefinition.hh"

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
    bool OnlyCollectNotDefinedInStdHeaders = true;
};

string HYGIENE = "Hygiene",
       ENVIRONMENT_CAPTURE = "Environment capture",
       PARAMETER_SIDE_EFFECTS = "Parameter side-effects",
       UNSUPPORTED_CONSTRUCT = "Unsupported construct";
void emitUntransformedMessage(
    ASTContext &Ctx,
    MacroExpansionNode *Expansion,
    string Category,
    string Reason)
{
    SourceManager &SM = Ctx.getSourceManager();
    const LangOptions &LO = Ctx.getLangOpts();
    auto ST = Expansion->getStmts().size() > 0 ? *Expansion->getStmts().begin() : nullptr;
    string s = getNameOfTopLevelVarOrFunctionDeclStmtExpandedIn(Ctx, ST);
    errs() << "CPP2C:"
           << "Untransformed Expansion,"
           << "\"" << hashMacro(Expansion->getMI(), SM, LO) << "\","
           << Expansion->getSpellingRange().getBegin().printToString(SM) << ","
           << s << ","
           << Category << ","
           << Reason << "\n";
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
    map<string, set<string>> MacroDefinitionToTransformedDefinitionPrototypes;

    // To give it access to members
    friend class PluginCpp2CAction;

    PluginSettings Cpp2CSettings;

public:
    explicit Cpp2CConsumer(CompilerInstance *CI, PluginSettings Cpp2CSettings)
        : CI(CI), PP(CI->getPreprocessor()), Cpp2CSettings(Cpp2CSettings) {}

    virtual void HandleTranslationUnit(ASTContext &Ctx)
    {
        // auto begin_time = std::chrono::high_resolution_clock::now();

        Rewriter RW;
        SourceManager &SM = Ctx.getSourceManager();
        const LangOptions &LO = Ctx.getLangOpts();
        RW.setSourceMgr(SM, LO);

        TranslationUnitDecl *TUD = Ctx.getTranslationUnitDecl();

        // Collect the names of all the variables and functions
        // defined in the program
        set<string> FunctionNames;
        set<string> VarNames;

        CollectDeclNamesVisitor CDNvisitor(CI, &FunctionNames, &VarNames);
        CDNvisitor.TraverseTranslationUnitDecl(TUD);

        bool OnlyCollectNotDefinedInStdHeaders =
            Cpp2CSettings.OnlyCollectNotDefinedInStdHeaders;

        // Step 0: Remove all Macro Roots that are not expanded
        // in the main file
        ExpansionRoots.erase(
            remove_if(ExpansionRoots.begin(),
                      ExpansionRoots.end(),
                      [&SM, &OnlyCollectNotDefinedInStdHeaders](const MacroExpansionNode *N)
                      {
                          // Only look at expansions source files
                          SourceLocation Loc = N->SpellingRange.getBegin();

                          // Only look at expansions of macros defined in
                          // source files (non-builtin macros and non-
                          // standard header macros)
                          auto definedInAllowedLocation =
                              (!OnlyCollectNotDefinedInStdHeaders) ||
                              (!isInStdHeader(N->MI->getDefinitionLoc(), SM));

                          return !definedInAllowedLocation ||
                                 !SM.isInMainFile(Loc) ||
                                 SM.isWrittenInScratchSpace(Loc);
                      }),
            ExpansionRoots.end());

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
            MacroExpansionNode *ExpansionRoot = nullptr;
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
        // that macro. This enables to quickly check for duplicate
        // identical transformations
        map<SourceLocation, vector<TransformedDefinition *>>
            MacroDefinitionLocationToTransformedDefinition;

        set<string> TransformedPrototypes;
        set<pair<string, const FunctionDecl *>>
            TransformedDefinitionsAndFunctionDeclExpandedIn;

        // Step 4: Transform macros that satisfy these four requirements:
        // 1) Hygiene
        // 2) No environment capture
        // 3) No side-effects in parameters
        // 4) Not unsupported (e.g., not L-value independent, Clang doesn't support rewriting, etc.)
        if (Cpp2CSettings.Verbose)
        {
            errs() << "Step 4: Transform hygienic and transformable macros \n";
        }

        for (auto TopLevelExpansion : ExpansionRoots)
        {

            //// Hygiene
            {
                // Don't transform expansions appearing where a const expr
                // is required
                if (mustBeConstExpr(Ctx, *TopLevelExpansion->Stmts.begin()))
                {
                    if (Cpp2CSettings.Verbose)
                    {
                        emitUntransformedMessage(Ctx, TopLevelExpansion, HYGIENE, "Const expr required");
                    }
                    continue;
                }

                // Check that the expansion maps to a single expansion
                if (TopLevelExpansion->SubtreeNodes.size() < 1)
                {
                    if (Cpp2CSettings.Verbose)
                    {
                        emitUntransformedMessage(Ctx, TopLevelExpansion, HYGIENE, "No expansion found");
                    }
                    continue;
                }

                // Check that expansion maps to one statement
                if (TopLevelExpansion->Stmts.size() != 1)
                {
                    if (Cpp2CSettings.Verbose)
                    {
                        emitUntransformedMessage(Ctx, TopLevelExpansion, HYGIENE,
                                                 "AST Nodes != 1. Equal to " + to_string(TopLevelExpansion->Stmts.size()));
                    }
                    continue;
                }

                // Check that expansion has an unambiguous signature
                if (!expansionHasUnambiguousSignature(Ctx, TopLevelExpansion))
                {
                    if (Cpp2CSettings.Verbose)
                    {
                        emitUntransformedMessage(Ctx, TopLevelExpansion, HYGIENE, "Ambiguous function signature");
                    }
                    continue;
                }

                auto ST = *TopLevelExpansion->Stmts.begin();
                auto E = dyn_cast_or_null<Expr>(ST);

                // Check that the expansion expands to an expression
                if (!E)
                {
                    if (Cpp2CSettings.Verbose)
                    {
                        emitUntransformedMessage(Ctx, TopLevelExpansion, HYGIENE, "Did not expand to an expression");
                    }
                    continue;
                }

                // Check that expression is completely covered by the expansion
                {
                    auto ExpansionBegin = TopLevelExpansion->SpellingRange.getBegin();
                    auto ExpansionEnd = TopLevelExpansion->SpellingRange.getEnd();

                    auto ExpressionRange = SM.getExpansionRange(E->getSourceRange());
                    auto ExpressionBegin = ExpressionRange.getBegin();
                    auto ExpressionEnd = ExpressionRange.getEnd();

                    if (!(ExpansionBegin == ExpressionBegin &&
                          ExpansionEnd == ExpressionEnd))
                    {
                        if (Cpp2CSettings.Verbose)
                        {
                            emitUntransformedMessage(Ctx, TopLevelExpansion, HYGIENE, "Expansion range != Expression range");
                        }
                        continue;
                    }

                    // It would be better to check that the number of tokens in the
                    // expression is >= to the number of tokens in the macro
                    // definition, but we don't have an easy way of accessing the number
                    // of tokens in an arbitrary expression
                    if (!PP.isAtEndOfMacroExpansion(E->getEndLoc()))
                    {
                        if (Cpp2CSettings.Verbose)
                        {
                            emitUntransformedMessage(Ctx, TopLevelExpansion, HYGIENE, "Expression end not at expansion end");
                        }
                        continue;
                    }
                }

                // Check that the arguments are hygienic
                {
                    bool hasUnhygienicArg = false;
                    for (auto &&Arg : TopLevelExpansion->Arguments)
                    {
                        if (Arg.Stmts.size() == 0)
                        {
                            if (Cpp2CSettings.Verbose)
                            {
                                emitUntransformedMessage(Ctx, TopLevelExpansion, HYGIENE,
                                                         "No statement for argument: " + Arg.Name);
                            }
                            hasUnhygienicArg = true;
                            break;
                        }

                        auto ArgFirstExpansion = *Arg.Stmts.begin();
                        for (auto ArgExpansion : Arg.Stmts)
                        {
                            if (!compareTrees(Ctx, ArgFirstExpansion, ArgExpansion) &&
                                false)
                            {
                                if (Cpp2CSettings.Verbose)
                                {
                                    emitUntransformedMessage(Ctx, TopLevelExpansion, HYGIENE,
                                                             "Argument " + Arg.Name + " not expanded to a consistent AST structure");
                                }
                                hasUnhygienicArg = true;
                                break;
                            }

                            // Check that spelling location of the AST node and
                            // all its subexpressions fall within the range of
                            // the argument's token ranges
                            // FIXME: This may render invocations
                            // which contain invocations as arguments as
                            // untransformable, but that doesn't make the
                            // transformation unsound, and we can still get
                            // those expansions on subsequent runs
                            if (!StmtAndSubStmtsSpelledInRanges(Ctx, ArgExpansion,
                                                                Arg.TokenRanges))
                            {
                                if (Cpp2CSettings.Verbose)
                                {
                                    emitUntransformedMessage(Ctx, TopLevelExpansion, HYGIENE,
                                                             "Argument " + Arg.Name + " matched with an AST node "
                                                                                      "with an expression outside the spelling location "
                                                                                      "of the arg's token ranges");
                                }
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
            }

            auto ST = *TopLevelExpansion->Stmts.begin();
            auto E = dyn_cast_or_null<Expr>(ST);
            assert(E != nullptr);

            // Transform object-like macros which reference global vars,
            // call functions, or expand to void-type expressions
            // into nullary functions, since global vars cannot do
            // any of those
            bool TransformToVar =
                TopLevelExpansion->MI->isObjectLike() &&
                !containsGlobalVars(E) &&
                !containsFunctionCalls(E) &&
                getDesugaredCanonicalType(Ctx, ST).getAsString() != "void";

            // Create the transformed definition
            TransformedDefinition *TD =
                new TransformedDefinition(Ctx, TopLevelExpansion, TransformToVar);

            //// Environment capture
            {
                if (containsLocalVars(Ctx, E))
                {
                    vector<const DeclRefExpr *> DREs;
                    collectLocalVarDeclRefExprs(E, &DREs);
                    bool hasEnvironmentCapture = false;
                    for (auto &&DRE : DREs)
                    {
                        bool varComesFromArg = false;
                        // Check all the macros arguments for the variable
                        for (auto &&Arg : TopLevelExpansion->Arguments)
                        {
                            for (auto &&S : Arg.Stmts)
                            {
                                if (containsDeclRefExpr(S, DRE))
                                {
                                    varComesFromArg = true;
                                    break;
                                }
                            }
                            if (varComesFromArg)
                            {
                                break;
                            }
                        }

                        if (!varComesFromArg)
                        {
                            if (Cpp2CSettings.Verbose)
                            {
                                emitUntransformedMessage(Ctx, TopLevelExpansion, ENVIRONMENT_CAPTURE, "Captures environment");
                            }
                            hasEnvironmentCapture = true;
                        }
                        if (hasEnvironmentCapture)
                        {
                            break;
                        }
                    }
                    if (hasEnvironmentCapture)
                    {
                        continue;
                    }
                }
            }

            //// Parameter side-effects and L-Value Independence
            {
                // Don't transform expansions which:
                // 1)   Change the R-value associated with the L-value of a symbol
                //      in one of their arguments
                // 2)   Return the L-value of a symbol in one of their arguments
                //      in the *body* of the definition; e.g., FOO(&x) is fine, but
                //          #define FOO(x) &x
                //          FOO(x)
                //      is not
                // We don't expansions like this because they require that
                // the L-value of the operand symbol be the same for the
                // inlined symbol and the symbol for the local variable we
                // create for the expression containing it it in the
                // transformed code, and they will not be.
                bool writesToRValueFromArg = false;
                bool returnsLValueFromArg = false;
                set<const Stmt *> LValuesFromArgs;
                set<const Stmt *> StmtsThatChangeRValue;
                set<const Stmt *> StmtsThatReturnLValue;
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
                        emitUntransformedMessage(Ctx, TopLevelExpansion, PARAMETER_SIDE_EFFECTS, "Writes to R-value of symbol from arguments");
                    }
                    continue;
                }

                collectStmtsThatReturnLValue(ST, &StmtsThatReturnLValue);
                for (auto &&StmtThatReturnsLValue : StmtsThatReturnLValue)
                {
                    bool isOk = false;
                    // We can allow this statement if the entire expression
                    // came from a single argument
                    for (auto &&it : TopLevelExpansion->Arguments)
                    {
                        if (StmtAndSubStmtsSpelledInRanges(Ctx, StmtThatReturnsLValue, it.TokenRanges))
                        {
                            isOk = true;
                            break;
                        }
                    }
                    // If this expansion is ok, don't proceed with the check
                    if (isOk)
                    {
                        break;
                    }

                    for (auto &&LVal : LValuesFromArgs)
                    {
                        if (containsStmt(StmtThatReturnsLValue, LVal))
                        {
                            returnsLValueFromArg = true;
                            break;
                        }
                    }
                    if (returnsLValueFromArg)
                    {
                        break;
                    }
                }
                if (returnsLValueFromArg)
                {
                    if (Cpp2CSettings.Verbose)
                    {
                        emitUntransformedMessage(Ctx, TopLevelExpansion, UNSUPPORTED_CONSTRUCT, "Contains an expression that returns L-value of symbol from arguments");
                    }
                    continue;
                }

                // Perform function-specific checks
                if (!TD->IsVar)
                {
                    auto Parents = Ctx.getParents(*E);
                    if (Parents.size() > 1)
                    {
                        emitUntransformedMessage(Ctx, TopLevelExpansion, UNSUPPORTED_CONSTRUCT, "Expansion on C++ code?");
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
                            emitUntransformedMessage(Ctx, TopLevelExpansion, UNSUPPORTED_CONSTRUCT, "Expansion on LHS of assignment");
                        }
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
                            emitUntransformedMessage(Ctx, TopLevelExpansion, UNSUPPORTED_CONSTRUCT, "Expansion operand of -- or ++");
                        }
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
                            emitUntransformedMessage(Ctx, TopLevelExpansion, UNSUPPORTED_CONSTRUCT, "Expansion operand of &");
                        }
                        continue;
                    }
                }
            }

            // Get the location to emit the transformed definition
            auto FD = getFunctionDeclStmtExpandedIn(Ctx, *TopLevelExpansion->Stmts.begin());

            //// Unsupported constructs
            {
                // Don't transform definitions with signatures with array types
                // TODO: We should be able to transform these so long as we
                // properly transform array types to pointers
                if (TD->hasArrayTypes())
                {
                    if (Cpp2CSettings.Verbose)
                    {
                        emitUntransformedMessage(Ctx, TopLevelExpansion, UNSUPPORTED_CONSTRUCT, "Transformed signature includes array types");
                    }
                    continue;
                }

                // Check that the transformed definition's signature
                // does not include function types or function pointer
                // types.
                // Returning a function is unhygienic, but function parameters
                // are fine.
                // TODO: We could allow function parameters if we could
                // emit the names of parameters correctly, and we could possibly
                // allow function return types if we cast them to pointers
                if (TD->hasFunctionTypes())
                {
                    if (Cpp2CSettings.Verbose)
                    {
                        emitUntransformedMessage(Ctx, TopLevelExpansion, UNSUPPORTED_CONSTRUCT, "Transformed signature includes function or function pointer types");
                    }
                    continue;
                }

                // Check that this expansion is not string literal, because it
                // may have been used in a place where a string literal is
                // required, e.g., as the format string to printf
                // TODO:    I think we should be able to transform these if we could fix
                //          transforming array types
                if (isa_and_nonnull<clang::StringLiteral>(ST))
                {
                    if (Cpp2CSettings.Verbose)
                    {
                        emitUntransformedMessage(Ctx, TopLevelExpansion, UNSUPPORTED_CONSTRUCT, "Expansion is a string literal");
                    }
                    continue;
                }

                // Check that expansion is inside a function, because if it
                // isn't none of the constructs we transform to
                // (var and function call) would be valid at the global scope
                if (FD == nullptr)
                {
                    if (Cpp2CSettings.Verbose)
                    {
                        emitUntransformedMessage(Ctx, TopLevelExpansion, UNSUPPORTED_CONSTRUCT, "Expansion not inside a function definition");
                    }
                    continue;
                }

                // TODO: Record this rewrite location somewhere so we can
                // just reference it later when we go to emit the
                // transformed definition
                // TODO: There has to be a smarter way of generating the transformed definition's rewrite location
                auto TransformedDefinitionLoc = SM.getExpansionLoc(FD->getBeginLoc());

                if (!RW.isRewritable(TransformedDefinitionLoc))
                {
                    if (Cpp2CSettings.Verbose)
                    {
                        emitUntransformedMessage(Ctx, TopLevelExpansion, UNSUPPORTED_CONSTRUCT, "Transformed definition not in a rewritable location");
                    }
                    continue;
                }

                if (!SM.isInMainFile(TransformedDefinitionLoc))
                {
                    if (Cpp2CSettings.Verbose)
                    {
                        emitUntransformedMessage(Ctx, TopLevelExpansion, UNSUPPORTED_CONSTRUCT, "Transformed definition location not in main file");
                    }
                    continue;
                }

                if (
                    !RW.isRewritable(TopLevelExpansion->SpellingRange.getBegin()) ||
                    !RW.isRewritable(TopLevelExpansion->SpellingRange.getEnd()))
                {
                    if (Cpp2CSettings.Verbose)
                    {
                        emitUntransformedMessage(Ctx, TopLevelExpansion, UNSUPPORTED_CONSTRUCT, "Expansion not in a rewritable location");
                    }
                    continue;
                }

                if (
                    !SM.isInMainFile(TopLevelExpansion->SpellingRange.getBegin()) ||
                    !SM.isInMainFile(TopLevelExpansion->SpellingRange.getEnd()))
                {
                    if (Cpp2CSettings.Verbose)
                    {
                        emitUntransformedMessage(Ctx, TopLevelExpansion, UNSUPPORTED_CONSTRUCT, "Transformed expansion not in main file");
                    }
                    continue;
                }
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
                        if (ETD->IsVar == TD->IsVar &&
                            ETD->VarOrReturnType == TD->VarOrReturnType &&
                            ETD->ArgTypes == TD->ArgTypes &&
                            ETD->InitializerOrDefinition == TD->InitializerOrDefinition)
                        {
                            EmittedName = ETD->EmittedName;
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
                if (MacroDefinitionLocationToTransformedDefinition.find(TD->Expansion->MI->getDefinitionLoc()) !=
                    MacroDefinitionLocationToTransformedDefinition.end())
                {
                    // Find which, if any, of the prior transformation
                    // definitions of this macro are identical to the one
                    // we are considering adding to the program.
                    for (auto &&ETD : MacroDefinitionLocationToTransformedDefinition[TD->Expansion->MI->getDefinitionLoc()])
                    {
                        if (ETD->IsVar == TD->IsVar &&
                            ETD->VarOrReturnType == TD->VarOrReturnType &&
                            ETD->ArgTypes == TD->ArgTypes &&
                            ETD->InitializerOrDefinition == TD->InitializerOrDefinition)
                        {
                            EmittedName = ETD->EmittedName;
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

                TD->EmittedName = EmittedName;

                string TransformedSignature =
                    TD->getExpansionSignatureOrDeclaration(Ctx, false);

                string FullTransformationDefinition =
                    TransformedSignature + TD->InitializerOrDefinition;

                TransformedPrototypes.insert(TransformedSignature + ";");
                TransformedDefinitionsAndFunctionDeclExpandedIn.emplace(FullTransformationDefinition, FD);
                // TODO: Only emit transformed definition if verbose
                {
                    TD->EmittedName = "";
                    string TransformedSignatureNoName =
                        TD->getExpansionSignatureOrDeclaration(Ctx, true);
                    errs() << "CPP2C:"
                           << "Transformed Definition,"
                           << "\"" << hashMacro(TopLevelExpansion->MI, SM, LO) << "\","
                           << "\"" << TransformedSignatureNoName << "\""
                           << ","
                           << EmittedName << "\n";
                    TD->EmittedName = EmittedName;
                }
                // Record the number of unique definitions emitted for this
                // macro definition
                {
                    string key = hashMacro(TopLevelExpansion->MI, SM, LO);
                    // Set the emitted name to the empty string right before
                    // recording the signature so that we get an anonymous
                    // signature
                    string temp = TD->EmittedName;
                    TD->EmittedName = "";
                    MacroDefinitionToTransformedDefinitionPrototypes[key].insert(TD->getExpansionSignatureOrDeclaration(Ctx, true));
                    TD->EmittedName = temp;
                }

                (MacroDefinitionLocationToTransformedDefinition[TD->Expansion->MI->getDefinitionLoc()]).push_back(TD);
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

                    CallOrRef += Arg.RawText;

                    i += 1;
                }
                CallOrRef += ")";
            }
            SourceRange InvocationRange = TopLevelExpansion->SpellingRange;
            bool rewriteFailed = RW.ReplaceText(InvocationRange, StringRef(CallOrRef));
            assert(!rewriteFailed);

            // TODO: Only emit transformed expansion if verbose
            {
                auto s = getNameOfTopLevelVarOrFunctionDeclStmtExpandedIn(Ctx, ST);
                errs() << "CPP2C:"
                       << "Transformed Expansion,"
                       << "\"" << hashMacro(TopLevelExpansion->MI, SM, LO) << "\","
                       << TopLevelExpansion->SpellingRange.getBegin().printToString(SM) << ","
                       << s << "\n";
            }
        }

        // Emit transformed definitions after functions in which they appear
        for (auto &&it : TransformedDefinitionsAndFunctionDeclExpandedIn)
        {
            auto StartOfFD = it.second->getBeginLoc();
            // NOTE: This has some coupling with an earlier check
            // that the spelling location of the start fo the function decl
            // is rewritable
            auto RewriteLoc = SM.getExpansionLoc(StartOfFD);
            // RW.InsertTextAfter(
            //     SM.getLocForEndOfFile(SM.getMainFileID()),
            //     StringRef(it + "\n\n"));
            bool rewriteFailed = RW.InsertTextBefore(
                RewriteLoc,
                StringRef(it.first + "\n\n"));
            assert(!rewriteFailed);
            if (Cpp2CSettings.Verbose)
            {
                errs() << "Emitted a definition: "
                       << it.first + "\n";
            }
        }

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

        // auto end_time = std::chrono::high_resolution_clock::now();
        // auto duration = std::chrono::duration_cast<std::chrono::microseconds>(
        //                     end_time - begin_time)
        //                     .count();
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

        // Note: There is a little bit of coupling here with getting
        // the source manager and lang options from the CO
        MacroNameCollector *MNC = new MacroNameCollector(
            Cpp2C->MacroNames,
            Cpp2C->MultiplyDefinedMacros,
            Cpp2C->MacroDefinitionToTransformedDefinitionPrototypes,
            CI.getSourceManager(),
            CI.getLangOpts(),
            Cpp2CSettings.OnlyCollectNotDefinedInStdHeaders);
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
            if (arg == "-ow" || arg == "--overwrite-files")
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
            else if (arg == "-shm" || arg == "--standard-header-macros")
            {
                Cpp2CSettings.OnlyCollectNotDefinedInStdHeaders = false;
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
