#include "CSubsetVisitor.h"

// Visitor for checking if a program, statement, or expression in the
// Cpp2C C subset has variables.
class CSubsetContainsVars : public CSubsetVisitor
{
private:
    bool result = false;

public:
    CSubsetContainsVars(ASTContext *Ctx) : CSubsetVisitor(Ctx){};

    void VisitVar(const VarDecl *Var)
    {
        result = true;
    }

    bool getResult() { return result; }

    static bool containsVars(ASTContext *Ctx, const Expr *E)
    {
        CSubsetContainsVars Checker(Ctx);
        Checker.VisitExpr(E);
        return Checker.getResult();
    }
};
