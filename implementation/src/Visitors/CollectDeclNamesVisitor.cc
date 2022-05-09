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

        // llvm::outs() << functionName << "\n";
        // for (auto &&it : FDecl->attrs())
        // {
        //     string attrName = it->getAttrName()->getName().str();
        //     llvm::outs() << attrName << "\n";

        //     if (attrName.compare("annotate") == 0)
        //     {
        //         string SS;
        //         llvm::raw_string_ostream S(SS);
        //         it->printPretty(
        //             S,
        //             Ctx->getPrintingPolicy());
        //         string annotation = S.str();
        //         unsigned posOfFirstQuote = annotation.find('"');
        //         unsigned lengthOfQuotedSubstring = annotation.rfind('"') - posOfFirstQuote + 1;
        //         annotation = annotation.substr(posOfFirstQuote, lengthOfQuotedSubstring);
        //         llvm::outs() << annotation << "\n";
        //     }
        // }

        return true;
    }

    bool CollectDeclNamesVisitor::VisitVarDecl(VarDecl *VD)
    {
        string VarName = VD->getName().str();
        VarNames->insert(VarName);
        return true;
    }
}