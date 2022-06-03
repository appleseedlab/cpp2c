// TransformerMessages.hh
// Messages to emit during the transformation step

#pragma once

#include "CppSig/MacroExpansionNode.hh"
#include "Transformer/TransformedDefinition.hh"

#include "clang/Basic/LangOptions.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Lex/MacroInfo.h"
#include "clang/AST/ASTContext.h"
#include "llvm/Support/raw_ostream.h"

#include <string>

namespace Utils
{
    namespace Logging
    {

        void emitUntransformedMessage(
            llvm::raw_fd_ostream &OS,
            clang::ASTContext &Ctx,
            CppSig::MacroExpansionNode *Expansion,
            std::string Category,
            std::string Reason);

        void emitMacroDefinitionMessage(
            llvm::raw_fd_ostream &OS,
            const clang::MacroDirective *MD,
            clang::SourceManager &SM,
            const clang::LangOptions &LO);

        void emitMacroExpansionMessage(
            llvm::raw_fd_ostream &OS,
            clang::SourceRange SpellingRange,
            const clang::MacroDefinition &MD,
            clang::SourceManager &SM,
            const clang::LangOptions &LO);

        void emitTransformedDefinitionMessage(
            llvm::raw_fd_ostream &OS,
            Transformer::TransformedDefinition *TD,
            clang::ASTContext &Ctx,
            clang::SourceManager &SM,
            const clang::LangOptions &LO);

        void emitTransformedExpansionMessage(
            llvm::raw_fd_ostream &OS,
            CppSig::MacroExpansionNode *Expansion,
            clang::ASTContext &Ctx,
            clang::SourceManager &SM,
            const clang::LangOptions &LO);

    } // namespace Logging

} // namespace Utils
