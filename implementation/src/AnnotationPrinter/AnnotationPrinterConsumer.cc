#include "AnnotationPrinter/AnnotationPrinterConsumer.hh"
#include "Visitors/CollectCpp2CAnnotatedDeclsVisitor.hh"
#include "Utils/TransformedDeclarationAnnotation.hh"

namespace AnnotationPrinter
{

    void AnnotationPrinterConsumer::HandleTranslationUnit(clang::ASTContext &Ctx)
    {
        auto CADV = Visitors::CollectCpp2CAnnotatedDeclsVisitor(Ctx);
        auto TUD = Ctx.getTranslationUnitDecl();
        CADV.TraverseTranslationUnitDecl(TUD);
        auto &AnnotatedDecls = CADV.getDeclsRef();

        // Print the output as a JSON array
        llvm::outs() << "[ ";
        unsigned int i = 0;
        for (auto &&D : AnnotatedDecls)
        {
            // Only consider var and func decls, not tag decls
            if (llvm::isa_and_nonnull<clang::TagDecl>(D))
            {
                continue;
            }

            if (i > 0)
            {
                llvm::outs() << ", ";
            }

            std::string annotation = Utils::getFirstAnnotationOrEmpty(D);
            nlohmann::json j = Utils::annotationStringToJson(annotation);
            llvm::outs() << j.dump();

            i += 1;
        }
        llvm::outs() << " ]";
    }

} // namespace AnnotationPrinter
