#include "CSubsetVisitor.h"
#include "MacroForest.h"

using namespace std;

bool inSourceRangeCollection(ASTContext *Ctx, const Stmt *S,
                             SourceRangeCollection *Ranges)
{
    SourceLocation Loc = getSpecificLocation(*S);
    SourceLocation SpellingLoc = Ctx->getFullLoc(Loc).getSpellingLoc();
    return Ranges->contains(SpellingLoc);
}

// FIXME: Right now we may collect nodes which are not in the C subset.
// This is fine for now though because we only call this visitor on expressions
// which we have already found to be in the subset.
class CSubsetInSourceRangeCollectionCollector : public CSubsetVisitor
{
private:
    set<const Stmt *> &Forest;
    SourceRangeCollection *Ranges;

public:
    CSubsetInSourceRangeCollectionCollector(
        ASTContext *Ctx, set<const Stmt *> &Forest,
        SourceRangeCollection *Ranges)
        : CSubsetVisitor(Ctx), Forest(Forest), Ranges(Ranges){};

    void VisitStmt(const Stmt *S)
    {
        if (inSourceRangeCollection(Ctx, S, Ranges))
        {
            insertIntoForest(Ctx, S, Forest);
        }
        CSubsetVisitor::VisitStmt(S);
    }

    void VisitExpr(const Expr *E)
    {
        const Stmt *S = dyn_cast<Stmt>(E);
        if (inSourceRangeCollection(Ctx, S, Ranges))
        {
            insertIntoForest(Ctx, S, Forest);
        }
        CSubsetVisitor::VisitExpr(E);
    }
};
