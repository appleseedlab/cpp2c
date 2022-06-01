#include "Visitors/CollectDeclNamesVisitor.hh"

namespace Visitors
{
    using namespace clang;
    using namespace std;

    CollectDeclNamesVisitor::CollectDeclNamesVisitor(
        CompilerInstance *CI,
        set<string> *FunctionNames,
        set<string> *VarNames)
        : Ctx(&(CI->getASTContext())), FunctionNames(FunctionNames), VarNames(VarNames) {}

    bool CollectDeclNamesVisitor::VisitFunctionDecl(FunctionDecl *FDecl)
    {
        string functionName = FDecl
                                  ->getNameInfo()
                                  .getName()
                                  .getAsString();
        FunctionNames->insert(functionName);

        return true;
    }

    bool CollectDeclNamesVisitor::VisitVarDecl(VarDecl *VD)
    {
        string VarName = VD->getName().str();
        VarNames->insert(VarName);
        return true;
    }
}