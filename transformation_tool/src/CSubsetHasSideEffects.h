// Visitor for checking if a program, statement, or expression in the
// Cpp2C C subset has side-effects.

#include "CSubsetVisitor.h"

class CSubsetHasSideEffects : CSubsetVisitor
{
private:
    bool result = false;

public:
    virtual void VisitAssign(const BinaryOperator *Assign)
    {
        result = true;
    }

    virtual void VisitCallOrInvocation(const CallExpr *CallOrInvocation)
    {
        result = true;
    }

    bool getResult() { return result; }
};