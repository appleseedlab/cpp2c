#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"

using namespace clang;
using namespace std;

// Visitor class which collects the names of all variables and functions
// declared in a program
class CollectDeclNamesVisitor
    : public RecursiveASTVisitor<CollectDeclNamesVisitor>
{
private:
    ASTContext *Ctx;
    set<string> *FunctionNames;
    set<string> *VarNames;

public:
    explicit CollectDeclNamesVisitor(
        CompilerInstance *CI, set<string> *FunctionNames,
        set<string> *VarNames)
        : Ctx(&(CI->getASTContext())), FunctionNames(FunctionNames),
          VarNames(VarNames)
    {
    }

    bool VisitFunctionDecl(FunctionDecl *FDecl)
    {
        string functionName = FDecl
                                  ->getNameInfo()
                                  .getName()
                                  .getAsString();
        FunctionNames->insert(functionName);

        return true;
    }

    bool VisitVarDecl(VarDecl *VD)
    {
        string VarName = VD->getName().str();
        VarNames->insert(VarName);
        return true;
    }
};