#include "CSubsetVisitor.h"

// Visitor to check if a given expression is in the C language subset
class CSubsetExprInCSubset : public CSubsetVisitor
{
private:
    bool result = false;

public:
    CSubsetExprInCSubset(ASTContext *Ctx) : CSubsetVisitor(Ctx){};

    void VisitStmt(const Stmt *S)
    {
        if (auto E = dyn_cast<Expr>(S))
        {
            VisitExpr(E);
        }
        // Don't check other syntactic types
    }

    virtual void VisitImplicit(const ImplicitCastExpr *Implicit)
    {
        VisitExpr(Implicit->getSubExpr());
    }

    virtual void VisitNum(const IntegerLiteral *Num) { result = true; }

    virtual void VisitVar(const VarDecl *Var) { result = true; }

    virtual void VisitParenExpr(const ParenExpr *ParenExpr_)
    {
        VisitExpr(ParenExpr_->getSubExpr());
    }

    virtual void VisitUnExpr(const UnaryOperator *UnExpr)
    {
        VisitExpr(UnExpr->getSubExpr());
    }

    virtual void VisitBinExpr(const BinaryOperator *BinExpr)
    {
        VisitExpr(BinExpr->getLHS());
        if (result)
        {
            VisitExpr(BinExpr->getRHS());
        }
    }

    virtual void VisitAssign(const BinaryOperator *Assign)
    {
        VisitExpr(Assign->getLHS());
        if (result)
        {
            VisitExpr(Assign->getRHS());
        }
    }

    virtual void VisitCallOrInvocation(const CallExpr *CallOrInvocation)
    {
        // This is liberal
        result = true;
    }

    bool getResult()
    {
        return result;
    }

    static bool isExprInCSubset(ASTContext *Ctx, const Expr *E)
    {
        CSubsetExprInCSubset Checker(Ctx);
        Checker.VisitExpr(E);
        return Checker.getResult();
    }
};
