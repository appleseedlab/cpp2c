#pragma once

#include "clang/AST/ASTConsumer.h"

namespace AnnotationPrinter
{
    // AST consumer which calls the visitor class to print annotations
    class AnnotationPrinterConsumer : public clang::ASTConsumer
    {

    public:
        virtual void HandleTranslationUnit(clang::ASTContext &Ctx);
    };
} // namespace AnnotationPrinter
