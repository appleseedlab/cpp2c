#pragma once

#include "Cpp2C/Cpp2CCommand.hh"
#include "Transformer/TransformerSettings.hh"
#include "Deduplicator/DeduplicatorSettings.hh"
#include "AnnotationRemover/AnnotationRemoverSettings.hh"

#include "clang/Frontend/CompilerInstance.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/Frontend/FrontendAction.h"

#include <memory>
#include <string>
#include <vector>

namespace Cpp2C
{
    class Cpp2CAction : public clang::PluginASTAction
    {

    protected:
        std::unique_ptr<clang::ASTConsumer>
        CreateASTConsumer(
            clang::CompilerInstance &CI,
            llvm::StringRef file) override;

        bool ParseArgs(
            const clang::CompilerInstance &CI,
            const std::vector<std::string> &args) override;

        // Necessary for ANYTHING to print to stderr
        clang::PluginASTAction::ActionType getActionType() override;

    private:
        Cpp2CCommand Command = HELP;
        Transformer::TransformerSettings TSettings;
        Deduplicator::DeduplicatorSettings DDSettings;
        AnnotationRemover::AnnotationRemoverSettings ARSettings;
    };

} // namespace Transformer
