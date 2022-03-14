#include "CSubsetVisitor.h"
#include "CSubsetExprInCSubset.h"
#include "clang/AST/ASTTypeTraits.h"
#include "MacroForest.h"

using namespace clang;
using namespace std;

bool isExpansionRoot(ASTContext &Ctx, const Stmt *S)
{
    SourceLocation Loc = getSpecificLocation(*S);
    if (!Loc.isMacroID())
    {
        return false;
    }

    SourceLocation ELoc = Ctx.getFullLoc(Loc).getExpansionLoc();

    for (const auto &Parent : Ctx.getParents(*S))
    {
        if (auto *PE = Parent.get<Stmt>())
        {
            SourceLocation PLoc = getSpecificLocation(*PE);
            SourceLocation PELoc = Ctx.getFullLoc(PLoc).getExpansionLoc();

            // Parent comes from the same expansion as the child
            // => Our node cannot be an expansion root
            if (ELoc == PELoc)
            {
                return false;
            }
        }
    }

    return true;
}

// Collects all the expressions in the AST that are in the Cpp2C C subset
// and are the root expressions of a macro expansion.
class CSubsetExpansionASTRootsCollector : public CSubsetVisitor
{
private:
    vector<const Stmt *> &ExpansionASTRoots;

public:
    explicit CSubsetExpansionASTRootsCollector(
        ASTContext *Ctx,
        vector<const Stmt *> &ExpansionASTRoots)
        : CSubsetVisitor(Ctx),
          ExpansionASTRoots(ExpansionASTRoots){};

    void VisitStmt(const Stmt *S)
    {
        // Add the expression to the list of roots if applicable, then
        // check sub expressions (we should not find any more roots under
        // this one but to be safe we check them)
        if (isa<Expr>(S) &&
            CSubsetExprInCSubset::isExprInCSubset(Ctx, dyn_cast<Expr>(S)) &&
            isExpansionRoot(*Ctx, S))
        {
            ExpansionASTRoots.push_back(S);
        }

        CSubsetVisitor::VisitStmt(S);
    }

    void VisitExpr(const Expr *E)
    {
        const Stmt *S = dyn_cast<Stmt>(E);
        if (CSubsetExprInCSubset::isExprInCSubset(Ctx, E) &&
            isExpansionRoot(*Ctx, E))
        {
            ExpansionASTRoots.push_back(S);
        }

        CSubsetVisitor::VisitExpr(E);
    }
};