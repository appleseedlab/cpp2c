#pragma once

#include "Transformer/TransformerSettings.hh"

#include "clang/Frontend/CompilerInstance.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/Frontend/FrontendAction.h"

#include <memory>
#include <string>
#include <vector>

namespace Transformer
{
    class TransformerAction : public clang::PluginASTAction
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
        TransformerSettings TSettings;
    };

} // namespace Transformer
