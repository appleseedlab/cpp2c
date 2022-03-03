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

// Source code rewriter
Rewriter RW;

// Map for memoizing results of IsExprInCSubset
map<Expr *, bool> EInCSub;

// Enum for different types of expression included in our C language subset
// Link: https://tinyurl.com/yc3mzv8o
enum class CSubsetExpr
{
    // Use for initializers
    INVALID,

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
        throw std::invalid_argument("Unimplemented CSubsetExpr");
    }
}

// Kinds of smart pointers;
// https://tinyurl.com/y8hbbdwq

// Visitor class which collects the names of all functions declared in a
// program
class CollectFunctionNamesVisitor : public RecursiveASTVisitor<CollectFunctionNamesVisitor>
{
private:
    ASTContext *Ctx;
    // Set of all function names declared in a program
    set<string> FunctionNames;

public:
    explicit CollectFunctionNamesVisitor(CompilerInstance *CI)
        : Ctx(&(CI->getASTContext())),
          FunctionNames() {}

    virtual bool VisitFunctionDecl(FunctionDecl *FDecl)
    {
        string functionName = FDecl
                                  ->getNameInfo()
                                  .getName()
                                  .getAsString();
        FunctionNames.insert(functionName);

        return true;
    }

    set<string> getFunctionNames()
    {
        return FunctionNames;
    }
};

// Preprocessor callback for collecting macro definitions
class MacroDefinitionCollector : public PPCallbacks
{
public:
    map<string, const MacroDirective *> MacroNameToDirective;
    set<string> MultiplyDefinedMacros;

    /// Hook called whenever a macro definition is seen.
    void MacroDefined(const Token &MacroNameTok, const MacroDirective *MD)
    {
        IdentifierInfo *II = MacroNameTok.getIdentifierInfo();
        string MacroName = II->getName().str();

        // Check if this macros is multiply-defined
        if (MD->getPrevious() == nullptr)
        {
            MultiplyDefinedMacros.insert(MacroName);
        }

        // Record this macro 's definition
        MacroNameToDirective.emplace(MacroName, MD);
    }
};

// Returns true if the given expression is in our C language subset,
// false otherwise.
bool IsExprInCSubset(Expr *E)
{
    // We use a map to memoize results
    auto Entry = EInCSub.find(E);
    if (Entry != EInCSub.end())
    {
        errs() << "Expression already checked: ";
        E->dumpColor();
        return Entry->second;
    }

    bool result = false;

    // Num
    if (auto Num = dyn_cast<IntegerLiteral>(E))
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
            result = IsExprInCSubset(E0);
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
                result = IsExprInCSubset(E0);
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
                result = IsExprInCSubset(E1) && IsExprInCSubset(E2);
            }
        }
        // Assign
        else if (OC == BO_Assign)
        {
            // Can we just use dyn_cast here (Can the LHS be NULL?)
            if (auto X = dyn_cast_or_null<DeclRefExpr>(BinExpr->getLHS()))
            {
                auto E2 = BinExpr->getRHS();
                result = IsExprInCSubset(E2);
            }
        }
    }
    // CallOrInvocation (function call)
    else if (auto CallOrInvocation = dyn_cast<CallExpr>(E))
    {
        result = true;
        for (auto &&Arg : CallOrInvocation->arguments())
        {
            if (!IsExprInCSubset(Arg))
            {
                result = false;
            }
            break;
        }
    }
    EInCSub[E] = result;
    return result;
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
    // Check that the expression is in our language subset
    if (!IsExprInCSubset(E))
    {
        return;
    }

    // Step 1: Classify the expression
    CSubsetExpr CSE = CSubsetExpr::INVALID;
    // Since at this point we already know the expression is in the
    // language subset, we only need to perform a minimal number
    // of checks to classify it
    // Num
    if (dyn_cast<IntegerLiteral>(E))
    {
        CSE = CSubsetExpr::Num;
    }
    // Var
    else if (dyn_cast<clang::DeclRefExpr>(E))
    {
        CSE = CSubsetExpr::Var;
    }
    // ParenExpr
    else if (dyn_cast<ParenExpr>(E))
    {
        CSE = CSubsetExpr::ParenExpr;
    }
    // UnExpr
    else if (dyn_cast<clang::UnaryOperator>(E))
    {
        CSE = CSubsetExpr::UnExpr;
    }
    // BinExpr or Assign
    else if (auto BinExpr = dyn_cast<clang::BinaryOperator>(E))
    {
        auto OC = BinExpr->getOpcode();

        // BinExpr
        if (OC != BO_Assign)
        {
            CSE = CSubsetExpr::BinExpr;
        }
        // Assign
        else
        {
            CSE = CSubsetExpr::Assign;
        }
    }
    // CallOrInvocation (function call)
    else if (auto CallOrInvocation = dyn_cast<CallExpr>(E))
    {
        CSE = CSubsetExpr::CallOrInvocation;
    }

    errs() << "Found a " << CSubsetExprToString(CSE) << "\n";

    // Step 2: Try to transform the entire expression
    // TODO
    bool transformedE = false;
    errs() << "Potentially transforming a "
           << CSubsetExprToString(CSE) << "\n";

    // Step 3: If we could not transform the entire expression,
    // then try to transform its subexpressions.
    // Note that we don't have to check subexpressions for being in
    // the language subset since IsExprInCSubset handles that recursively
    if (!transformedE)
    {
        errs() << "Did not transform a " << CSubsetExprToString(CSE) << "\n";
        // Num
        if (auto Num = dyn_cast<IntegerLiteral>(E))
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
    // Is this right?
    // ExprStmt
    if (auto ES = dyn_cast<Expr>(S))
    {
        errs() << "Transforming an ExprStmt\n";
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
            errs() << "Transforming an IfElseStmt\n";
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
            errs() << "Transforming a WhileStmt\n";
            TransformExpr(E);
            TransformStmt(S1);
        }
    }
    // CompoundStmt
    else if (auto CS = dyn_cast<CompoundStmt>(S))
    {
        errs() << "Transforming a CompoundStmt\n";
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
                errs() << "Transforming a function definition\n";
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
        CFVvisitor.TraverseDecl(TUD);

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
        Preprocessor &PP = CI.getPreprocessor();
        MacroDefinitionCollector *MDC = new MacroDefinitionCollector();
        PP.addPPCallbacks(unique_ptr<PPCallbacks>(MDC));
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
