#pragma once

#include "CppSig/MacroExpansionNode.hh"

#include "clang/AST/ASTContext.h"
#include "clang/Lex/Preprocessor.h"

namespace Transformer
{
    // Checks if a given macro expansion is syntactically well-formed.
    // If so, returns the empty string.
    // If not, returns an error message.
    std::string isWellFormed(
        CppSig::MacroExpansionNode *Expansion,
        clang::ASTContext &Ctx,
        clang::Preprocessor &PP);

    // Checks if a given macro expansion captures any variables from its
    // environment.
    // If so, returns an error message.
    // If not, returns the empty string.
    std::string isEnvironmentCapturing(
        CppSig::MacroExpansionNode *Expansion,
        clang::ASTContext &Ctx);

} // namespace Transformer