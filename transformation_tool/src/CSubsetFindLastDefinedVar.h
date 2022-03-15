#include "CSubsetVisitor.h"

// Visitor to find the last defined var in a program, statement, or expression
// in Cpp2C C subset.
class CSubsetFindLastDefinedVar : public CSubsetVisitor
{
private:
    const VarDecl *VD = nullptr;

public:
    CSubsetFindLastDefinedVar(ASTContext *Ctx) : CSubsetVisitor(Ctx){};

    void VisitVar(const VarDecl *Var)
    {
        if ((nullptr == VD) || (Var->getLocation() > VD->getLocation()))
        {
            VD = Var;
        }
    }

    const VarDecl *getVD() { return VD; }

    static const VarDecl *findLastDefinedVar(ASTContext *Ctx, const Expr *E)
    {
        CSubsetFindLastDefinedVar Checker(Ctx);
        Checker.VisitExpr(E);
        return Checker.getVD();
    }
};
