#include "clang/AST/ASTContext.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ParentMapContext.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendPluginRegistry.h"

#include "llvm/Support/raw_ostream.h"

#include <iostream>

using namespace clang;
using namespace std;

class CollectFunctionNamesVisitor
    : public RecursiveASTVisitor<CollectFunctionNamesVisitor>
{
private:
    ASTContext *astContext;

public:
    set<string> functionNames;

    explicit CollectFunctionNamesVisitor(CompilerInstance *CI)
        : astContext(&(CI->getASTContext())) {}

    virtual bool VisitFunctionDecl(FunctionDecl *function)
    {
        string functionName = function
                                  ->getNameInfo()
                                  .getName()
                                  .getAsString();
        functionNames.insert(functionName);

        return true;
    }
};

class PrintFunctionNamesConsumer : public clang::ASTConsumer
{
private:
    CollectFunctionNamesVisitor *visitor;

public:
    explicit PrintFunctionNamesConsumer(CompilerInstance *CI)
        : visitor(new CollectFunctionNamesVisitor(CI)) {}

    virtual void HandleTranslationUnit(ASTContext &Context)
    {
        visitor->TraverseDecl(Context.getTranslationUnitDecl());

        for (string functionName : visitor->functionNames)
        {
            llvm::errs() << functionName << "\n";
        }
    }
};

// Wrap everything into a plugin
class PluginCppToCAction : public PluginASTAction
{
protected:
    unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI,
                                              StringRef file) override
    {

        // llvm::errs() << "\n\n\n\n\n\n\n"
        //              << "TESTING TESTING TESTING"
        //              << "\n\n\n\n\n\n\n";

        return make_unique<PrintFunctionNamesConsumer>(&CI);
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
