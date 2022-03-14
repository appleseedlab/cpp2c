#include "CSubsetVisitor.h"

// Returns true if the given variable declaration is for a global variable,
// false otherwise
bool isGlobalVariable(const VarDecl *VD)
{
    return VD->hasGlobalStorage() && !VD->isStaticLocal();
}

// Visitor for checking if a program, statement, or expression in the
// Cpp2C C subset has local variables.
class CSubsetContainsLocalVars : public CSubsetVisitor
{
private:
    bool result = false;

public:
    CSubsetContainsLocalVars(ASTContext *Ctx) : CSubsetVisitor(Ctx){};

    void VisitVar(const VarDecl *Var)
    {
        result = result || !isGlobalVariable(Var);
    }

    bool getResult() { return result; }

    static bool containsLocalVars(ASTContext *Ctx, const Expr *E)
    {
        CSubsetContainsLocalVars Checker(Ctx);
        Checker.VisitExpr(E);
        return Checker.getResult();
    }
};
