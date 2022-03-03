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

// Kinds of smart pointers;
// https://tinyurl.com/y8hbbdwq

// Visitor class which collects the names of all functions declared in a
// program
class CollectFunctionNamesVisitor
    : public RecursiveASTVisitor<CollectFunctionNamesVisitor>
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

// Matcher callback that collects all function definitions
class FunctionDefinitionCollector : public MatchFinder::MatchCallback
{
public:
    vector<const Decl *> &Definitions;

    FunctionDefinitionCollector(vector<const Decl *> &Definitions)
        : Definitions(Definitions){};

    virtual void run(const MatchFinder::MatchResult &Result) final
    {
        if (auto D = Result.Nodes.getNodeAs<Decl>("FDecl"))
        {
            Definitions.push_back(D);
        }
    }
};

// NOTE:
// These functions are it - The trick now is extract the macro invocation
// from each of them
void TransformExpr(Expr *E);
void TransformStmt(Stmt *S);

// Transforms all eligible macro invocations in the given expression into
// C function calls
void TransformExpr(Expr *E)
{
    // Num
    if (auto Num = dyn_cast<IntegerLiteral>(E))
    {
        errs() << "Transformed a Num\n";
    }
    // Var
    else if (auto Var = dyn_cast<clang::DeclRefExpr>(E))
    {
        errs() << "Transformed a Var\n";
    }
    // ParenExpr
    else if (auto ParenExpr_ = dyn_cast<ParenExpr>(E))
    {
        if (auto E0 = ParenExpr_->getSubExpr())
        {
            errs() << "Transforming a ParenExpr\n";
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
                errs() << "Transforming a UnExpr\n";
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
                errs() << "Transforming a BinExpr\n";
                TransformExpr(E1);
                TransformExpr(E2);
            }
        }
        // AssignExpr
        else if (OC == BO_Assign)
        {
            // Can the LHS be null?
            if (auto X = dyn_cast_or_null<DeclRefExpr>(BinExpr->getLHS()))
            {
                errs() << "Transforming an AssignExpr\n";
                auto E2 = BinExpr->getRHS();
                TransformExpr(E2);
            }
        }
    }
    else if (auto CallOrInvocation = dyn_cast<CallExpr>(E))
    {
        errs() << "Transforming a CallOrInvocation (function call)\n";
        for (auto &&Arg : CallOrInvocation->arguments())
        {
            TransformExpr(Arg);
        }
    }
    // CallOrInvocation (function call)
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

        // Collect the names of all the functions defined in the program
        CollectFunctionNamesVisitor CFVvisitor(CI);
        CFVvisitor.TraverseDecl(Ctx.getTranslationUnitDecl());

        // Match the AST for function definitions
        errs() << "Step 1: Find function definitions\n";
        vector<const Decl *> FDs;
        {
            MatchFinder Finder;
            FunctionDefinitionCollector callback(FDs);
            auto FDeclMatcher =
                functionDecl(
                    isExpansionInMainFile(),
                    isDefinition(),
                    hasBody(compoundStmt()))
                    .bind("FDecl");
            Finder.addMatcher(FDeclMatcher, &callback);
            Finder.matchAST(Ctx);
        }

        errs() << "Found " << FDs.size() << " function(s):\n";
        for (auto &&FD : FDs)
        {
            if (auto ND = dyn_cast<NamedDecl>(FD))
            {
                errs() << "    " << ND->getNameAsString() << "\n";
            }
        }

        // Step 2: Traverse definitions and only check those nodes which
        // are a part of our language subset
        for (auto &&FD : FDs)
        {
            Stmt *Body = FD->getBody();
            TransformStmt(Body);
        }

        // Step 3: Print the results of the rewriting for the current file
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
