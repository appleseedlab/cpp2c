#include "Visitors/ForwardDeclDDVisitor.hh"
#include "Utils/ExpansionUtils.hh"

#include "clang/Basic/SourceManager.h"

namespace Visitors
{

    ForwardDeclDDVisitor::ForwardDeclDDVisitor(clang::Rewriter &RW) : RW(RW) {}

    bool ForwardDeclDDVisitor::VisitTagDecl(clang::TagDecl *TD)
    {
        // Don't remove definitions
        if (TD->isThisDeclarationADefinition())
        {
            return true;
        }
        // Don't remove declarations which have no declarations before them
        if (TD->getPreviousDecl() == NULL)
        {
            return true;
        }

        // Remove declarations which:
        // 1)   Are annotated with the tag "CPP2C"
        // 2)   Have a previous decl
        std::string s = Utils::getFirstAnnotationOrEmpty(TD);
        if (s.find("CPP2C") != std::string::npos)
        {
            if (TD->getPreviousDecl() != NULL)
            {
                auto &SM = RW.getSourceMgr();
                auto Range = SM.getExpansionRange(TD->getSourceRange());
                // Increment end loc by 1 to remove semicolon after declaration
                Range.setEnd(Range.getEnd().getLocWithOffset(1));

                bool failed = RW.RemoveText(Range);
                assert(!failed);
            }
        }
        return true;
    }
} // namespace Visitors