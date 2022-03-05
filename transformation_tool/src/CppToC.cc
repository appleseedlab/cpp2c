#include "clang/AST/ASTContext.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ParentMapContext.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendPluginRegistry.h"
#include "clang/Lex/PPCallbacks.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/Rewrite/Frontend/Rewriters.h"

#include "llvm/Support/raw_ostream.h"

#include <iostream>

using namespace clang;
using namespace llvm;
using namespace std;

using namespace clang::ast_matchers;

// TODO: We may want to transform object-like macro as well, as they see
// more usage than nullary function-like macros. Ideally we would add the
// soundness of this proof to the transformation as well.

// TODO: Refactor and remove global variables

// Source code rewriter
Rewriter RW;

SourceManager *SM;

Preprocessor *PP;

// Set of all function names declared in a program
set<string> FunctionNames;
// Set of all macro names declared in a program
set<string> MacroNames;
// Set of all multiply-defined macros
set<string> MultiplyDefinedMacros;
// List of all macro expansion ranges
list<SourceRange> ExpansionRanges;
// Set of starting locations for all expansion ranges that contain
// the start of another locations
set<SourceLocation> StartLocationsOfExpansionsContainingStartOfOtherExpansion;
// Set of starting locations for all expansion ranges that are contained
// within another expansion
set<SourceLocation> StartLocationsOFExpansionsContainedInOtherExpansion;
// Mapping from starting locations of macro expansions to names of all macros
// starting at that location
map<SourceLocation, list<string>> ExpansionStartLocationToMacroNames;

// Map for memoizing results of isExprInCSubset
map<Expr *, bool> EInCSub;

// Map for memoizing results of exprContainsLocalVars
map<Expr *, bool> EContainsLocalVars;

// Enum for different types of expression included in our C language subset
// Link: https://tinyurl.com/yc3mzv8o
enum class CSubsetExpr
{
    // Use for initializers
    INVALID,
    // Needed to work around implicit casts
    IMPLICIT_CAST,

    Num,
    Var,
    ParenExpr,
    UnExpr,
    BinExpr,
    Assign,
    CallOrInvocation
};
constexpr const char *CSubsetExprToString(CSubsetExpr CSE)
{
    switch (CSE)
    {
    case CSubsetExpr::INVALID:
        return "INVALID";
    case CSubsetExpr::IMPLICIT_CAST:
        return "IMPLICIT_CAST";
    case CSubsetExpr::Num:
        return "Num";
    case CSubsetExpr::Var:
        return "Var";
    case CSubsetExpr::ParenExpr:
        return "ParenExpr";
    case CSubsetExpr::UnExpr:
        return "UnExpr";
    case CSubsetExpr::BinExpr:
        return "BinExpr";
    case CSubsetExpr::Assign:
        return "Assign";
    case CSubsetExpr::CallOrInvocation:
        return "CallOrInvocation";
    default:
        throw std::invalid_argument("Unimplemented CSubsetExpr type");
    }
}

// Kinds of smart pointers;
// https://tinyurl.com/y8hbbdwq

// Returns true if a given source location is contained within a
// a given source range
bool isInRange(SourceLocation &L, SourceRange &SR2)
{
    SourceLocation B2 = SR2.getBegin();
    SourceLocation E2 = SR2.getEnd();

    return B2 <= L && L <= E2;
}

// Preprocessor callback to collect information about macro expansions
class MacroExpansionCollector : public PPCallbacks
{
public:
    void MacroExpands(const Token &MacroNameTok,
                      const MacroDefinition &MD,
                      SourceRange Range,
                      const MacroArgs *Args)
    {
        string MacroName = MacroNameTok.getIdentifierInfo()->getName().str();
        // errs() << "Found macro expansion: " << MacroName << "\n";

        auto ExpansionRange = SM->getExpansionRange(Range).getAsRange();
        auto B = ExpansionRange.getBegin();
        for (auto &&OtherExpansionRange : ExpansionRanges)
        {
            auto OB = OtherExpansionRange.getBegin();
            if (isInRange(B, OtherExpansionRange))
            {
                list<string> OtherMacroNames =
                    ExpansionStartLocationToMacroNames[OtherExpansionRange.getBegin()];
                if (OtherMacroNames.size() == 0)
                {
                    // errs() << "Error: " << MacroName
                    //        << " was found to expand"
                    //           " within another expansion, but no"
                    //           " other expansion could be found\n ";
                }
                else if (OtherMacroNames.size() == 1)
                {
                    // errs() << MacroName << " expands in "
                    //        << OtherMacroNames.front() << "\n";
                }
                else if (OtherMacroNames.size() > 1)
                {
                    // errs() << MacroName
                    //        << " expands in another expansion,"
                    //           " but it could not be determined specifically"
                    //           " which one\n";
                }
                StartLocationsOfExpansionsContainingStartOfOtherExpansion.insert(OB);
                StartLocationsOFExpansionsContainedInOtherExpansion.insert(B);
            }
        }

        ExpansionStartLocationToMacroNames[B].push_back(MacroName);
        ExpansionRanges.push_back(ExpansionRange);
    }
};

// Preprocessor callback for collecting macro definitions
class MacroDefinitionCollector : public PPCallbacks
{
public:
    map<string, const MacroDirective *> MacroNameToDirective;

    // Hook called whenever a macro definition is seen.
    void MacroDefined(const Token &MacroNameTok, const MacroDirective *MD)
    {
        IdentifierInfo *II = MacroNameTok.getIdentifierInfo();
        string MacroName = II->getName().str();

        // Add this macro name to the set of macro names used in the program
        MacroNames.insert(MacroName);

        // Check if this macros is multiply-defined
        if (MD->getPrevious() == nullptr)
        {
            MultiplyDefinedMacros.insert(MacroName);
        }
    }
};

// Visitor class which collects the names of all functions declared in a
// program
class CollectFunctionNamesVisitor
    : public RecursiveASTVisitor<CollectFunctionNamesVisitor>
{
private:
    ASTContext *Ctx;

public:
    explicit CollectFunctionNamesVisitor(CompilerInstance *CI)
        : Ctx(&(CI->getASTContext()))
    {
    }

    bool VisitFunctionDecl(FunctionDecl *FDecl)
    {
        string functionName = FDecl
                                  ->getNameInfo()
                                  .getName()
                                  .getAsString();
        FunctionNames.insert(functionName);

        return true;
    }
};

// Returns true if the given expression is in our C language subset,
// false otherwise.
// TODO: Maybe we can remove this function and just return INVALID
// on the classify function instead? Would make things a lot simpler
bool isExprInCSubset(Expr *E)
{
    // We use a map to memoize results
    auto Entry = EInCSub.find(E);
    if (Entry != EInCSub.end())
    {
        // errs() << "Expression already checked: ";
        // E->dumpColor();
        return Entry->second;
    }

    bool result = false;

    // IMPLICIT
    if (auto Imp = dyn_cast<ImplicitCastExpr>(E))
    {
        result = isExprInCSubset(Imp->getSubExpr());
    }
    // Num
    else if (auto Num = dyn_cast<IntegerLiteral>(E))
    {
        result = true;
    }
    // Var
    else if (auto Var = dyn_cast<clang::DeclRefExpr>(E))
    {
        result = true;
    }
    // ParenExpr
    else if (auto ParenExpr_ = dyn_cast<ParenExpr>(E))
    {
        if (auto E0 = ParenExpr_->getSubExpr())
        {
            result = isExprInCSubset(E0);
        }
    }
    // UnExpr
    else if (auto UnExpr = dyn_cast<clang::UnaryOperator>(E))
    {
        auto OC = UnExpr->getOpcode();
        if (OC == UO_Plus || OC == UO_Minus)
        {
            if (auto E0 = UnExpr->getSubExpr())
            {
                result = isExprInCSubset(E0);
            }
        }
    }
    // BinExpr
    else if (auto BinExpr = dyn_cast<clang::BinaryOperator>(E))
    {
        auto OC = BinExpr->getOpcode();
        if (OC == BO_Add || OC == BO_Sub || OC == BO_Mul || OC == BO_Div)
        {
            auto E1 = BinExpr->getLHS();
            auto E2 = BinExpr->getRHS();
            if (E1 && E2)
            {
                result = isExprInCSubset(E1) && isExprInCSubset(E2);
            }
        }
        // Assign
        else if (OC == BO_Assign)
        {
            // Can we just use dyn_cast here (Can the LHS be NULL?)?
            if (auto X = dyn_cast_or_null<DeclRefExpr>(BinExpr->getLHS()))
            {
                // Check that LHS is just a variable
                if (isa<VarDecl>(X->getDecl()))
                {
                    auto E2 = BinExpr->getRHS();
                    result = isExprInCSubset(E2);
                }
            }
        }
    }
    // CallOrInvocation (function call)
    else if (auto CallOrInvocation = dyn_cast<CallExpr>(E))
    {
        result = true;
    }
    EInCSub[E] = result;
    return result;
}

// Returns true if the given variable declaration is for a global variable,
// false otherwise
bool isGlobalVariable(VarDecl *VD)
{
    return VD->hasGlobalStorage() && !VD->isStaticLocal();
}

// Returns true if the given expression contains any non-global variables,
// false otherwise.
bool exprContainsLocalVars(Expr *E)
{
    // We use a map to memoize results
    auto Entry = EContainsLocalVars.find(E);
    if (Entry != EContainsLocalVars.end())
    {
        return Entry->second;
    }

    bool result = true;

    // IMPLICIT
    if (auto Imp = dyn_cast<ImplicitCastExpr>(E))
    {
        if (auto E0 = Imp->getSubExpr())
        {
            result = exprContainsLocalVars(E0);
        }
    }
    // Num
    else if (auto Num = dyn_cast<IntegerLiteral>(E))
    {
        result = false;
    }
    // Var
    else if (auto Var = dyn_cast<clang::DeclRefExpr>(E))
    {
        if (auto VD = dyn_cast<VarDecl>(Var->getDecl()))
        {
            result = !isGlobalVariable(VD);
        }
    }
    // ParenExpr
    else if (auto ParenExpr_ = dyn_cast<ParenExpr>(E))
    {
        if (auto E0 = ParenExpr_->getSubExpr())
        {
            result = exprContainsLocalVars(E0);
        }
    }
    // UnExpr
    else if (auto UnExpr = dyn_cast<clang::UnaryOperator>(E))
    {
        auto OC = UnExpr->getOpcode();
        if (OC == UO_Plus || OC == UO_Minus)
        {
            if (auto E0 = UnExpr->getSubExpr())
            {
                result = exprContainsLocalVars(E0);
            }
        }
    }
    // BinExpr
    else if (auto BinExpr = dyn_cast<clang::BinaryOperator>(E))
    {
        auto OC = BinExpr->getOpcode();
        if (OC == BO_Add || OC == BO_Sub || OC == BO_Mul || OC == BO_Div)
        {
            auto E1 = BinExpr->getLHS();
            auto E2 = BinExpr->getRHS();
            if (E1 && E2)
            {
                result = exprContainsLocalVars(E1) || exprContainsLocalVars(E2);
            }
        }
        // Assign
        else if (OC == BO_Assign)
        {
            // Can we just use dyn_cast here (Can the LHS be NULL?)
            if (auto X = dyn_cast_or_null<DeclRefExpr>(BinExpr->getLHS()))
            {
                // TODO: Ensure that the LHS is a var
                if (auto VD = dyn_cast<VarDecl>(X->getDecl()))
                {
                    result = !isGlobalVariable(VD);
                    // If the variable being assigned to is not a local var,
                    // then we must still check the RHS for a local var
                    if (!result)
                    {
                        auto E2 = BinExpr->getRHS();
                        result = exprContainsLocalVars(E2);
                    }
                }
            }
        }
    }
    // CallOrInvocation (function call)
    else if (auto CallOrInvocation = dyn_cast<CallExpr>(E))
    {
        result = false;
        for (auto &&Arg : CallOrInvocation->arguments())
        {
            if (exprContainsLocalVars(Arg))
            {
                result = true;
                break;
            }
        }
    }
    EContainsLocalVars[E] = result;
    return result;
}

// Returns the C language subset syntax node that this expression
// corresponds to
CSubsetExpr classifyExpr(Expr *E)
{
    // Check that the expression is in our language subset
    if (!isExprInCSubset(E))
    {
        return CSubsetExpr::INVALID;
    }

    // Since at this point we already know the expression is in the
    // language subset, we only need to perform a minimal number
    // of checks to classify it

    // IMPLICIT
    if (auto Imp = dyn_cast<ImplicitCastExpr>(E))
    {
        return CSubsetExpr::IMPLICIT_CAST;
    }
    // Num
    else if (dyn_cast<IntegerLiteral>(E))
    {
        return CSubsetExpr::Num;
    }
    // Var
    else if (dyn_cast<clang::DeclRefExpr>(E))
    {
        return CSubsetExpr::Var;
    }
    // ParenExpr
    else if (dyn_cast<ParenExpr>(E))
    {
        return CSubsetExpr::ParenExpr;
    }
    // UnExpr
    else if (dyn_cast<clang::UnaryOperator>(E))
    {
        return CSubsetExpr::UnExpr;
    }
    // BinExpr or Assign
    else if (auto BinExpr = dyn_cast<clang::BinaryOperator>(E))
    {
        auto OC = BinExpr->getOpcode();

        // BinExpr
        if (OC != BO_Assign)
        {
            return CSubsetExpr::BinExpr;
        }
        // Assign
        else
        {
            return CSubsetExpr::Assign;
        }
    }
    // CallOrInvocation (function call)
    else if (auto CallOrInvocation = dyn_cast<CallExpr>(E))
    {
        return CSubsetExpr::CallOrInvocation;
    }

    return CSubsetExpr::INVALID;
}

// Determines if an expression is a result of macro expansion,
// and if so, then tries to transform the invocation into a function call.
// Returns true if the invocation was transformed; false if the expression
// was not the result of a macro expansion or if the invocation was not
// transformed for some other reason
// TODO
enum class TransformationResult
{
    TRANSFORMED,
    NOT_TRANSFORMED,
    CONTAINS_NESTED_INVOCATIONS,
    CONTAINED_IN_INVOCATION,
    ERROR
};
TransformationResult transformEntireExpr(Expr *E)
{
    CSubsetExpr CSE = classifyExpr(E);

    // Check if the entire expression came from a macro expansion
    auto B = E->getBeginLoc();
    auto EL = E->getEndLoc();
    if (PP->isAtStartOfMacroExpansion(B) && PP->isAtEndOfMacroExpansion(EL))
    {
        // Get the beginning of the expansion
        // errs() << "Found an expression that begins at an expansion\n";
        auto ER = SM->getExpansionRange(E->getSourceRange()).getAsRange();
        auto EB = ER.getBegin();

        // Don't transform transform expansions with nested expansions
        if (StartLocationsOfExpansionsContainingStartOfOtherExpansion.find(EB) !=
            StartLocationsOfExpansionsContainingStartOfOtherExpansion.end())
        {
            errs() << "Found an invocation with nested invocations\n";
            return TransformationResult::CONTAINS_NESTED_INVOCATIONS;
        }

        // Don't transform nested expansions
        // FIXME: Not necessary but would be nice if this worked
        if (StartLocationsOFExpansionsContainedInOtherExpansion.find(EB) !=
            StartLocationsOFExpansionsContainedInOtherExpansion.end())
        {
            errs() << "Found a nested invocation\n";
            return TransformationResult::CONTAINED_IN_INVOCATION;
        }

        // Try to unambiguously determine the macro
        // that this expansion refers to
        if (ExpansionStartLocationToMacroNames.find(EB) !=
            ExpansionStartLocationToMacroNames.end())
        {
            list<string> MacroNames = ExpansionStartLocationToMacroNames[EB];
            if (MacroNames.size() == 0)
            {
                errs() << "Error: Clang reported a macro invocation"
                          " at this location but none found\n";

                return TransformationResult::ERROR;
            }
            else if (MacroNames.size() == 1)
            {
                string MacroName = MacroNames.front();
                errs() << "Found an unambiguous invocation of "
                       << MacroName << "\n";
            }
            else if (MacroNames.size() > 1)
            {
                errs() << "Could not unambiguously determine"
                       << " macro invocation to transform\n";

                return TransformationResult::ERROR;
            }
        }
    }
    // Check that the invoked macro is an object-like macro or a nullary
    // function-like macro
    // TODO: Allow for function-like macros with 1 argument whose
    // body is a single variable

    // Check that the expression does not have side-effects
    if (CSE == CSubsetExpr::Assign || CSE == CSubsetExpr::CallOrInvocation)
    {
        // Report that the invocation was not transformed so we can try
        // to transform subexpression that may not have side-effects
        return TransformationResult::NOT_TRANSFORMED;
    }

    // TODO: Check if macro is hygienic (the previous step may have
    // already done this?)

    // Check that the expression does not share variables with the
    // caller environment
    if (exprContainsLocalVars(E))
    {
        errs() << "Found an expression containing local or captured var(s)\n";
        return TransformationResult::NOT_TRANSFORMED;
    }

    // Transform the expansion into a function call
    // TODO

    // Define the called function and add it to the list of functions
    // defined in the program.
    // Make sure to give it a unique name.
    // TODO: Transform object-like macros into global variables instead?
    // TODO

    return TransformationResult::NOT_TRANSFORMED;
}

// NOTE:
// These functions are it - The trick now is to extract potential
// macro invocations from expressions
void TransformExpr(Expr *E);
void TransformStmt(Stmt *S);
void TransformProgram(TranslationUnitDecl *TUD);

// Transforms all eligible macro invocations in the given expression into
// C function calls
void TransformExpr(Expr *E)
{
    // Step 1: Classify the expression
    CSubsetExpr CSE = classifyExpr(E);

    // Don't transform expressions not in the language
    if (CSE == CSubsetExpr::INVALID)
    {
        return;
    }

    // Step 2: Try to transform the entire expression
    errs() << "Transforming a " << CSubsetExprToString(CSE) << "\n";
    TransformationResult result = transformEntireExpr(E);

    // Step 3: If we could not transform the entire expression,
    // then try to transform its subexpressions.
    // Note that we don't have to check subexpressions for being in
    // the language subset since isExprInCSubset handles that recursively
    if (result == TransformationResult::NOT_TRANSFORMED)
    {
        // errs() << "No change made to " << CSubsetExprToString(CSE) << "\n";
        // IMPLICIT
        if (auto Imp = dyn_cast<ImplicitCastExpr>(E))
        {
            if (auto E0 = Imp->getSubExpr())
            {
                TransformStmt(E0);
            }
        }
        // Num
        else if (auto Num = dyn_cast<IntegerLiteral>(E))
        {
            // Do nothing since Num does not have any subexpressions
        }
        // Var
        else if (auto Var = dyn_cast<clang::DeclRefExpr>(E))
        {
            // Do nothing since Var does not have any subexpressions
        }
        // ParenExpr
        else if (auto ParenExpr_ = dyn_cast<ParenExpr>(E))
        {
            if (auto E0 = ParenExpr_->getSubExpr())
            {
                TransformStmt(E0);
            }
        }
        // UnExpr
        else if (auto UnExpr = dyn_cast<clang::UnaryOperator>(E))
        {
            auto OC = UnExpr->getOpcode();
            if (OC == UO_Plus || OC == UO_Minus)
            {
                if (auto E0 = UnExpr->getSubExpr())
                {
                    TransformExpr(E0);
                }
            }
        }
        // BinExpr
        else if (auto BinExpr = dyn_cast<clang::BinaryOperator>(E))
        {
            auto OC = BinExpr->getOpcode();
            if (OC == BO_Add || OC == BO_Sub || OC == BO_Mul || OC == BO_Div)
            {
                auto E1 = BinExpr->getLHS();
                auto E2 = BinExpr->getRHS();
                if (E1 && E2)
                {
                    TransformExpr(E1);
                    TransformExpr(E2);
                }
            }
            // Assign
            else if (OC == BO_Assign)
            {
                // Can we just use dyn_cast here (Can the LHS be NULL?)
                if (auto X = dyn_cast_or_null<DeclRefExpr>(BinExpr->getLHS()))
                {
                    auto E2 = BinExpr->getRHS();
                    TransformExpr(E2);
                }
            }
        }
        // CallOrInvocation (function call)
        else if (auto CallOrInvocation = dyn_cast<CallExpr>(E))
        {
            for (auto &&Arg : CallOrInvocation->arguments())
            {
                TransformExpr(Arg);
            }
        }
    }
}

// Transforms all eligible macro invocations in the given statement into
// C function calls
void TransformStmt(Stmt *S)
{
    // Note: Should we not transfor a stmt at all if any of its
    // substatements are not in the C language subset?

    // ExprStmt
    if (auto ES = dyn_cast<Expr>(S))
    {
        // errs() << "Transforming an ExprStmt\n";
        TransformExpr(ES);
    }
    // IfElseStmt
    else if (auto IfElseStmt = dyn_cast<IfStmt>(S))
    {
        // Check for else branch
        Expr *E = IfElseStmt->getCond();
        Stmt *S1 = IfElseStmt->getThen();
        Stmt *S2 = IfElseStmt->getElse();
        if (E && S1 && S2)
        {
            // errs() << "Transforming an IfElseStmt\n";
            TransformExpr(E);
            TransformStmt(S1);
            TransformStmt(S2);
        }
    }
    // WhileStmt
    else if (auto WhileStmt_ = dyn_cast<WhileStmt>(S))
    {
        Expr *E = WhileStmt_->getCond();
        Stmt *S1 = WhileStmt_->getBody();
        if (E && S1)
        {
            // errs() << "Transforming a WhileStmt\n";
            TransformExpr(E);
            TransformStmt(S1);
        }
    }
    // CompoundStmt
    else if (auto CS = dyn_cast<CompoundStmt>(S))
    {
        // errs() << "Transforming a CompoundStmt\n";
        for (auto &&S : CS->children())
        {
            TransformStmt(S);
        }
    }
}

// Transforms all eligible macro invocations in a program into C function calls
void TransformProgram(TranslationUnitDecl *TUD, SourceManager &SM)
{
    // This probably won't happen, but to be safe
    if (!TUD)
    {
        return;
    }

    // Visit all function definitions in the program
    for (auto D : TUD->decls())
    {
        SourceLocation L = D->getLocation();
        // Check that this definition is in the main file
        // Not sure if we should use this condition or the one below it
        // if (!SM.isWrittenInMainFile)
        if (!SM.isInMainFile(L))
        {
            continue;
        }

        if (auto FD = dyn_cast<FunctionDecl>(D))
        {
            if (FD->isThisDeclarationADefinition())
            {
                // errs() << "Transforming a function definition\n";
                auto FBody = FD->getBody();
                TransformStmt(FBody);
            }
        }
    }
}

// AST consumer which calls the visitor class to perform the transformation
class CppToCConsumer : public ASTConsumer
{
private:
    CompilerInstance *CI;

public:
    explicit CppToCConsumer(CompilerInstance *CI)
        : CI(CI) {}

    virtual void HandleTranslationUnit(ASTContext &Ctx)
    {
        auto begin_time = std::chrono::high_resolution_clock::now();

        TranslationUnitDecl *TUD = Ctx.getTranslationUnitDecl();
        // Collect the names of all the functions defined in the program
        CollectFunctionNamesVisitor CFVvisitor(CI);
        CFVvisitor.TraverseTranslationUnitDecl(TUD);

        // Transform the program
        TransformProgram(TUD, Ctx.getSourceManager());

        // Print the results of the rewriting for the current file
        const RewriteBuffer *RewriteBuf =
            RW.getRewriteBufferFor(Ctx.getSourceManager().getMainFileID());
        if (RewriteBuf != nullptr)
        {
        }
        else
        {
            outs() << "No changes to AST\n";
        }

        auto end_time = std::chrono::high_resolution_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::microseconds>(
                            end_time - begin_time)
                            .count();
        errs() << "Finished in " << duration << " microseconds."
               << "\n";
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
        SM = &(CI.getSourceManager());
        PP = &(CI.getPreprocessor());
        MacroExpansionCollector *MIC = new MacroExpansionCollector();
        MacroDefinitionCollector *MDC = new MacroDefinitionCollector();
        PP->addPPCallbacks(unique_ptr<PPCallbacks>(MIC));
        PP->addPPCallbacks(unique_ptr<PPCallbacks>(MDC));
        return make_unique<CppToCConsumer>(&CI);
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
