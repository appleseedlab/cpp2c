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
