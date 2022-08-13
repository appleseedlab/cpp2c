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
        llvm::errs() << "Collecting a FunctionDecl name\n";
        string functionName = FDecl->getName().str();
        FunctionNames->insert(functionName);
        return true;
    }

    bool CollectDeclNamesVisitor::VisitVarDecl(VarDecl *VD)
    {
        llvm::errs() << "Collecting a VarDecl name\n";
        string VarName = VD->getName().str();
        VarNames->insert(VarName);
        return true;
    }
}