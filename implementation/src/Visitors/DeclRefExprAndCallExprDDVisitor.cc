#include "Visitors/DeclRefExprAndCallExprDDVisitor.hh"

#include "Utils/ExpansionUtils.hh"

#include "clang/Basic/SourceManager.h"

namespace Visitors
{
    DeclRefExprAndCallExprDDVisitor::DeclRefExprAndCallExprDDVisitor(
        clang::Rewriter &RW,
        std::map<clang::NamedDecl *, clang::NamedDecl *> &TransformedDeclToCanonicalDecl,
        std::map<clang::NamedDecl *, nlohmann::json> &TransformedDeclToJSON)
        : RW(RW),
          TransformedDeclToCanonicalDecl(TransformedDeclToCanonicalDecl),
          TransformedDeclToJSON(TransformedDeclToJSON) {}

    bool DeclRefExprAndCallExprDDVisitor::VisitDeclRefExpr(clang::DeclRefExpr *DRE)
    {
        // Get the name of the referenced deduped decl
        clang::NamedDecl *ReferencedDecl = DRE->getFoundDecl();

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

        // Check that we are replacing a transformed decl
        if (TransformedDeclToCanonicalDecl.find(ReferencedDecl) !=
            TransformedDeclToCanonicalDecl.end())
        {

            // Are we trying to replace a call/declref inside a
            // noncanonical transformed definition?
            auto &Ctx = ReferencedDecl->getASTContext();
            // TODO: Remove this const cast
            auto DeclExpandedIn = const_cast<clang::NamedDecl *>(Utils::getTopLevelNamedDeclStmtExpandedIn(Ctx, DRE));
            // Again, make sure we get the decl, not the def
            if (auto PD = DeclExpandedIn->getPreviousDecl())
            {
                DeclExpandedIn = clang::dyn_cast_or_null<clang::NamedDecl>(PD);
            }

            // Don't replace calls inside of deduped definitions
            if ((TransformedDeclToJSON.find(DeclExpandedIn) != TransformedDeclToJSON.end()) &&
                !TransformedDeclToJSON[DeclExpandedIn].contains("canonical"))
            {
                return true;
            }

            auto CanonicalDecl = TransformedDeclToCanonicalDecl[ReferencedDecl];
            // Replace the first n characters of the expression,
            // where n is the length of the referenced name,
            // with the name of the canonical decl
            std::string CanonicalName = CanonicalDecl->getNameAsString();
            std::string ReferencedName = ReferencedDecl->getNameAsString();

            auto &SM = RW.getSourceMgr();
            auto Begin = SM.getFileLoc(DRE->getExprLoc());
            bool failed = RW.ReplaceText(Begin, ReferencedName.size(), CanonicalName);
            TransformedDeclToJSON[CanonicalDecl]["unique transformed invocations"] = TransformedDeclToJSON[CanonicalDecl]["unique transformed invocations"].get<int>() + 1;
            assert(!failed);
            // llvm::errs() << "Replaced " << ReferencedName << " with " << CanonicalName << " in " << DeclExpandedIn->getNameAsString() << "\n";
        }

        return true;
    }
} // namespace Visitors
