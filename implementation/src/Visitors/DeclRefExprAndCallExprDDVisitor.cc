#include "Visitors/DeclRefExprAndCallExprDDVisitor.hh"

#include "clang/Basic/SourceManager.h"

namespace Visitors
{
    DeclRefExprAndCallExprDDVisitor::DeclRefExprAndCallExprDDVisitor(
        clang::Rewriter &RW,
        std::map<clang::NamedDecl *, clang::NamedDecl *> &TransformedDeclToCanonicalDecl)
        : RW(RW),
          TransformedDeclToCanonicalDecl(TransformedDeclToCanonicalDecl) {}

    bool DeclRefExprAndCallExprDDVisitor::VisitExpr(clang::Expr *E)
    {
        // Get the name of the referenced deduped decl
        clang::NamedDecl *ReferencedDecl = nullptr;
        if (auto DRE = clang::dyn_cast_or_null<clang::DeclRefExpr>(E))
        {
            ReferencedDecl = DRE->getFoundDecl();
        }
        else if (auto CE = clang::dyn_cast_or_null<clang::CallExpr>(E))
        {
            ReferencedDecl = CE->getDirectCallee();
        }
        // Only visit DeclRefExpr and CallExpr
        else
        {
            return true;
        }

        // Our mapping is strictly from _declarations_ to _declarations_,
        // and does not include definitions.
        // However, (I think) the referenced decl we just found may be a
        // definition; if this is the case, then it would be the second decl
        // we emitted for this transformed decl and def.
        // So set it to its previous decl
        // (which is guaranteed to be just a declaration) instead.
        // This may all be unnecessary, but better safe than sorry!
        if (auto PD = ReferencedDecl->getPreviousDecl())
        {
            ReferencedDecl = clang::dyn_cast_or_null<clang::NamedDecl>(PD);
        }

        // Check that wer are replacing a transformed decl
        if (TransformedDeclToCanonicalDecl.find(ReferencedDecl) !=
            TransformedDeclToCanonicalDecl.end())
        {
            auto CanonicalDecl = TransformedDeclToCanonicalDecl[ReferencedDecl];

            // Replace the first n characters of the expression,
            // where n is the length of the referenced name,
            // with the name of the canonical decl
            std::string CanonicalName = CanonicalDecl->getNameAsString();
            std::string ReferencedName = ReferencedDecl->getNameAsString();

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
