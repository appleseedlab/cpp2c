#include "Visitors/DeanonymizerVisitor.hh"
#include "Utils/ExpansionUtils.hh"

#include "clang/Basic/SourceManager.h"

namespace Visitors
{

    DeanonymizerVisitor::DeanonymizerVisitor(
        clang::ASTContext &Ctx,
        clang::Rewriter &RW) : Ctx(Ctx), RW(RW) {}

    bool DeanonymizerVisitor::VisitTypedefDecl(
        clang::TypedefDecl *TD)
    {
        // Is this typedef hiding a struct/union/enum decl?
        clang::QualType QT = TD->getUnderlyingType();
        const clang::Type *T = QT.getTypePtr();
        if (T &&
            (T->isStructureType() ||
            T->isUnionType() ||
            T->isEnumeralType()))
        {
            llvm::errs() << "Found an typedef of a struct/union/enum " << TD->getName().str() << "\n";
            // Is this type an anonymous type?
            const clang::TagDecl *TaD = T->getAsTagDecl();
            if (TaD && TaD->getDeclName().isEmpty())
            {
                if (TagDeclToName.find(TaD) != TagDeclToName.end()) {
                    llvm::errs() << "Already deanonymized this tag decl\n";
                    return true;
                }

                auto TDName = TD->getName();
                llvm::errs() << "typedef'd struct/union/enum " << TDName.str() << " is anonymous\n";

                // If so, then rewrite it to not be anonymous by
                // inserting the typedef name just before the definition
                // of the struct/union/enum
                auto &SM = Ctx.getSourceManager();
                auto Def = TaD->getDefinition();

                if (Def == nullptr)
                {
                    llvm::errs() << "Deanonymizing a typedef'd struct/union/enum without a definition: " << TDName.str() << "\n";
                }
                else
                {
                    llvm::errs() << "Deanonymizing a typedef'd struct/union/enum with a definition: " << TDName.str() << "\n";

                    auto LBraceLoc = Def->getBraceRange().getBegin();
                    LBraceLoc = SM.getExpansionLoc(LBraceLoc);

                    // Don't rewrite in standard headers
                    if (!Utils::isInStdHeader(LBraceLoc, SM))
                    {
                        auto RWText = TDName.str() + " ";
                        TagDeclToName[TaD] = RWText;
                    }
                }
            }
        }
        return true;
    }

    void DeanonymizerVisitor::Deanonymize() {
        auto &SM = Ctx.getSourceManager();
        for (auto &&it : TagDeclToName) {
            auto TaD = it.first;
            auto RWText = it.second;
            auto Def = TaD->getDefinition();
            if (Def != nullptr) {
                auto LBraceLoc = Def->getBraceRange().getBegin();
                LBraceLoc = SM.getExpansionLoc(LBraceLoc);
                // Don't rewrite in standard headers
                if (!Utils::isInStdHeader(LBraceLoc, SM))
                {
                    llvm::errs() << "Deanonymized struct to name "
                                    << RWText
                                    << '\n';
                    bool failed = RW.InsertTextBefore(LBraceLoc, RWText);
                    if (failed)
                    {
                        llvm::errs() << "Failed to deanonymize struct/union/enum "
                                     << RWText << "\n";
                        assert(false);
                    }
                }
            }

        }
    }
} // namespace Visitors
