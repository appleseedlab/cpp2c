#include "CSubsetVisitor.h"

// Returns true if the given variable declaration is for a global variable,
// false otherwise
bool isGlobalVariable(VarDecl *VD)
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
    void VisitVar(VarDecl *Var)
    {
        result = !isGlobalVariable(Var);
    }

    bool getResult() { return result; }
};
