#pragma once

#include "Deduplicator/DeduplicatorSettings.hh"

#include "clang/AST/ASTConsumer.h"

namespace Deduplicator
{
    // AST consumer that removes duplicate
    // transformed declarations and definitions
    class DeduplicatorConsumer : public clang::ASTConsumer
    {

    private:
        DeduplicatorSettings DDSettings;

    public:
        explicit DeduplicatorConsumer(DeduplicatorSettings DDSettings);

        virtual void HandleTranslationUnit(clang::ASTContext &Ctx);
    };
} // namespace Deduplicator
