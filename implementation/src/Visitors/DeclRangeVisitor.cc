#include "Visitors/DeclRangeVisitor.hh"

#include "clang/Basic/SourceManager.h"

#include <vector>

namespace Visitors
{

    DeclRangeVisitor::DeclRangeVisitor(clang::ASTContext &Ctx) :
        Ctx(Ctx) {}

    bool DeclRangeVisitor::VisitDecl(clang::Decl *D)
    {
        if (!D)
        {
            return true;
        }

        this->DeclRanges.push_back(D->getSourceRange());

        return true;
    }

    std::vector<clang::SourceRange>
    &DeclRangeVisitor::getDeclRangesRef()
    {
        return this->DeclRanges;
    }
} // namespace Visitors
