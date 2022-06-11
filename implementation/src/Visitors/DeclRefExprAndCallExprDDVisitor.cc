#include "Visitors/DeclRefExprAndCallExprDDVisitor.hh"

#include "clang/Basic/SourceManager.h"

namespace Visitors
{
    DeclRefExprAndCallExprDDVisitor::DeclRefExprAndCallExprDDVisitor(
        clang::Rewriter &RW,
        std::map<std::string, std::string> &TransformedDeclNameToCanonicalName)
        : RW(RW),
          TransformedDeclNameToCanonicalName(TransformedDeclNameToCanonicalName) {}

    bool DeclRefExprAndCallExprDDVisitor::VisitExpr(clang::Expr *E)
    {
        // Get the name of the referenced deduped decl
        std::string ReferencedName;
        if (auto DRE = clang::dyn_cast_or_null<clang::DeclRefExpr>(E))
        {
            ReferencedName = DRE->getFoundDecl()->getNameAsString();
        }
        else if (auto CE = clang::dyn_cast_or_null<clang::CallExpr>(E))
        {
            ReferencedName = CE->getDirectCallee()->getNameAsString();
        }
        // Only visit DeclRefExpr and CallExpr
        else
        {
            return true;
        }

        // Check that wer are replacing a transformed decl name
        if (TransformedDeclNameToCanonicalName.find(ReferencedName) !=
            TransformedDeclNameToCanonicalName.end())
        {
            // Replace the first n characters of the expression,
            // where n is the length of the referenced name,
            // with the name of the canonical decl
            auto CanonicalName = TransformedDeclNameToCanonicalName[ReferencedName];

            auto &SM = RW.getSourceMgr();
            auto Begin = SM.getExpansionLoc(E->getBeginLoc());
            // Important: Need to subtract 1 here for range to be correct
            auto End = Begin.getLocWithOffset(ReferencedName.length() - 1);
            auto RewriteRange = clang::SourceRange(Begin, End);

            bool failed = RW.ReplaceText(RewriteRange, CanonicalName);
            assert(!failed);
        }

        return true;
    }
} // namespace Visitors
