#include "CSubsetVisitor.h"
#include "MacroForest.h"

using namespace std;

bool exprInSourceRangeCollection(ASTContext *Ctx, const Expr *E,
                                 SourceRangeCollection *Ranges)
{
    SourceLocation Loc = E->getExprLoc();
    SourceLocation SpellingLoc = Ctx->getFullLoc(Loc).getSpellingLoc();
    return Ranges->contains(SpellingLoc);
}

// FIXME: Right now we may collect nodes which are not in the C subset.
// This is fine for now though because we only call this visitor on expressions
// which we have already found to be in the subset.
class CSubsetExprAndSubExprsSpelledInRanges : public CSubsetVisitor
{
private:
    SourceRangeCollection *Ranges;
    bool result = true;

public:
    CSubsetExprAndSubExprsSpelledInRanges(
        ASTContext *Ctx, SourceRangeCollection *Ranges)
        : CSubsetVisitor(Ctx), Ranges(Ranges){};

    void VisitExpr(const Expr *E)
    {
        result = result && exprInSourceRangeCollection(Ctx, E, Ranges);
        CSubsetVisitor::VisitExpr(E);
    }

    bool getResult() { return result; }

    static bool exprAndSubExprsSpelledInRanges(
        ASTContext *Ctx, const Expr *E, SourceRangeCollection *Ranges)
    {
        CSubsetExprAndSubExprsSpelledInRanges Checker(Ctx, Ranges);
        Checker.VisitExpr(E);
        return Checker.getResult();
    }
};
