#pragma once

#include "AnnotationRemover/AnnotationRemoverSettings.hh"

#include "clang/AST/ASTConsumer.h"
#include "clang/Frontend/CompilerInstance.h"

namespace AnnotationRemover
{
    // AST consumer which calls the visitor class to perform the transformation
    class AnnotationRemoverConsumer : public clang::ASTConsumer
    {

    private:
        AnnotationRemoverSettings ARSettings;

    public:
        explicit AnnotationRemoverConsumer(AnnotationRemoverSettings ARSettings);

        virtual void HandleTranslationUnit(clang::ASTContext &Ctx);
    };
} // namespace AnnotationRemover
