#include "Visitors/CollectCpp2CAnnotatedDeclsVisitor.hh"

namespace Visitors
{
    CollectCpp2CAnnotatedDeclsVisitor::CollectCpp2CAnnotatedDeclsVisitor(
        clang::ASTContext &Ctx) : Ctx(Ctx) {}

    bool CollectCpp2CAnnotatedDeclsVisitor::VisitDecl(clang::Decl *D)
    {
        // We only annotate these types, so only check them
        if (!(llvm::isa_and_nonnull<clang::TagDecl>(D) ||
              llvm::isa_and_nonnull<clang::FunctionDecl>(D) ||
              llvm::isa_and_nonnull<clang::VarDecl>(D)))
        {
            return true;
        }

        auto PP = Ctx.getPrintingPolicy();
        for (auto &&it : D->attrs())
        {
            if (auto attrName = it->getAttrName())
            {
                std::string attrNameStr = attrName->getName().str();
                if (attrNameStr == "annotate")
                {
                    std::string SS;
                    llvm::raw_string_ostream S(SS);
                    it->printPretty(S, PP);
                    std::string annotation = S.str();
                    // All the annotations we emit contain the substring
                    // "CPP2C".
                    // Hopefully this is not a common substring in other annotations?
                    if (annotation.find("CPP2C") != std::string::npos)
                    {
                        Decls.push_back(D);
                    }
                }
            }
        }
        return true;
    }

    std::vector<clang::Decl *> &CollectCpp2CAnnotatedDeclsVisitor::getDeclsRef()
    {
        return Decls;
    }

} // namespace Visitors
