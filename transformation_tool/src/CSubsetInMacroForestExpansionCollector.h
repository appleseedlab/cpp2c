#include "CSubsetVisitor.h"
#include "MacroForest.h"

bool isInMacroForestExpansion(
    ASTContext *Ctx,
    const Stmt *S,
    MacroForest::Node *Expansion)
{
    SourceLocation Loc = getSpecificLocation(*S);
    auto &SM = Ctx->getSourceManager();

    // All Nodes that stem from the same top-level expansion share
    // an Expansion location. This Expansion location is included
    // in the SpellingRange of that MatchForest::Node
    // ATTENTION: This is for safety, we should only be called in this context.
    SourceLocation ExpansionLoc = Ctx->getFullLoc(Loc).getExpansionLoc();
    if (!Expansion->Root->SpellingRange.fullyContains(ExpansionLoc))
    {
        return false;
    }

    // Co-Walk the Macro Backtrace and MacroForest Backtrace
    SourceLocation L = Loc;
    MacroForest::Node *N = Expansion;

    bool matched_expansion_stack = false;
    while (L.isMacroID())
    {
        auto FullLoc = Ctx->getFullLoc(L);
        auto ExpInfo = SM.getSLocEntry(FullLoc.getFileID()).getExpansion();

        SourceLocation MacroTrace;
        if (SM.isMacroArgExpansion(L))
            MacroTrace = SM.getImmediateExpansionRange(L).getBegin();
        else
            MacroTrace = L;

        SourceLocation SpellingLocation = Ctx->getFullLoc(L).getSpellingLoc();
        bool found = false;
        if (N->DefinitionRange.fullyContains(SpellingLocation) || N->SpellingRange.fullyContains(SpellingLocation) || N->ArgSpellingLocs.contains(SpellingLocation))
        {
            found = true;
        }

        // If we are still at the bottom of our Expansion-Tree Chain,
        // it could be, that this macro fully forwarded its body to
        // another macro. In this case, the expansion-stack at the AST
        // node starts at a deeper level. In thse cases, we are
        // allowed to go up, until we hit our first Expansion-Tree Node
        // (see tests/nested2.c)
        if (!found && N == Expansion)
        {
            L = SM.getImmediateMacroCallerLoc(L);
            continue;
        }

        if (!found)
        {
            return false;
        }

        matched_expansion_stack = true;

        if (!N->Parent)
            break;

        // If we have a Parent, this Macro must be spelled in the parent
        {
            if (!ExpInfo.isMacroArgExpansion())
            {
                SourceRange spellingRange(Ctx->getFullLoc(ExpInfo.getExpansionLocStart()).getSpellingLoc(),
                                          Ctx->getFullLoc(ExpInfo.getExpansionLocEnd()).getSpellingLoc());
                if (N->SpellingRange != spellingRange)
                {
                    return false;
                }
            }
        }

        // Co-Walk both Trees
        if (!ExpInfo.isMacroArgExpansion())
        {
            N = N->Parent;
        }
        L = SM.getImmediateMacroCallerLoc(L);
    }
    return matched_expansion_stack;
}


// FIXME: Right now we may collect nodes which are not in the C subset.
// This is fine for now though because we only call this visitor on expressions
// which we have already found to be in the subset.
class CSubsetInMacroForestExpansionCollector
    : public CSubsetVisitor
{
private:
    set<const Stmt *> &Forest;
    MacroForest::Node *Expansion;

public:
    CSubsetInMacroForestExpansionCollector(ASTContext *Ctx,
                                           set<const Stmt *> &Forest,
                                           MacroForest::Node *Expansion)
        : CSubsetVisitor(Ctx), Forest(Forest), Expansion(Expansion){};

    void VisitStmt(const Stmt *S) override
    {
        if (isInMacroForestExpansion(Ctx, S, Expansion))
        {
            insertIntoForest(Ctx, S, Forest);
        }

        CSubsetVisitor::VisitStmt(S);
    }

    void VisitExpr(const Expr *E) override
    {
        const Stmt *S = dyn_cast<Stmt>(E);
        if (isInMacroForestExpansion(Ctx, S, Expansion))
        {
            insertIntoForest(Ctx, S, Forest);
        }
        CSubsetVisitor::VisitExpr(E);
    }
};