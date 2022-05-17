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

    // Checks if a given macro expansion does not have parameter side-effects
    // and is L-value independent.
    // If so, returns an error message.
    // If not, returns the empty string.
    //
    // Don't transform expansions which:
    // 1)   Change the R-value associated with the L-value of a symbol
    //      in one of their arguments
    // 2)   Return the L-value of a symbol in one of their arguments
    //      in the *body* of the definition; e.g., FOO(&x) is fine, but
    //          #define FOO(x) &x
    //          FOO(x)
    //      is not
    // We don't transform expansions like this because they require that
    // the L-value of the operand symbol be the same for the
    // inlined symbol and the symbol for the local variable we
    // create for the expression containing it it in the
    // transformed code, and they will not be.
    std::string isParamSEFreeAndLValueIndependent(
        CppSig::MacroExpansionNode *Expansion,
        clang::ASTContext &Ctx);

} // namespace Transformer