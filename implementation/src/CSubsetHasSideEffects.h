// Visitor for checking if a program, statement, or expression in the
// Cpp2C C subset has side-effects.

#include "CSubsetVisitor.h"

class CSubsetHasSideEffects : CSubsetVisitor
{
private:
    bool result = false;

public:
    CSubsetHasSideEffects(ASTContext *Ctx) : CSubsetVisitor(Ctx){};

    virtual void VisitAssign(const BinaryOperator *Assign)
    {
        result = true;
    }

    virtual void VisitCallOrInvocation(const CallExpr *CallOrInvocation)
    {
        result = true;
    }

    bool getResult() { return result; }

    static bool hasSideEffects(ASTContext *Ctx, const Stmt *S)
    {
        CSubsetHasSideEffects Checker(Ctx);
        Checker.VisitStmt(S);
        return Checker.getResult();
    }

    static bool hasSideEffects(ASTContext *Ctx, const Expr *E)
    {
        CSubsetHasSideEffects Checker(Ctx);
        Checker.VisitExpr(E);
        return Checker.getResult();
    }
};