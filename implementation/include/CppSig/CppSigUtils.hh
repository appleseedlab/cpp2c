#pragma once

// CppSigUtils.hh
// Miscellaneous functionality related to CppSig
// Originally taken from Dietrich and edited by Brent Pappas

#include "CppSig/MacroForest.hh"

#include "clang/AST/Stmt.h"
#include "clang/AST/ASTContext.h"

#include <memory>
#include <vector>

namespace CppSig
{
    // Removes all Expansions that are not expanded in the main file,
    // and possibly those of macros that are defined in standard
    // headers as well
    void removeExpansionsNotInMainFile(
        CppSig::MacroForest::Roots &Expansions,
        clang::SourceManager &SM,
        bool OnlyCollectNotDefinedInStdHeaders);

    // Given an AST, returns all nodes in that AST that are expansion roots
    std::unique_ptr<std::vector<const clang::Stmt *>>
    findMacroASTRoots(clang::ASTContext &Ctx);

    // Populates the Stmts member of each MacroExpansionNode in ExpansionRoots
    // whose expansion root is the given AST node
    void populateExpansionsWhoseTopLevelStmtIsThisStmt(
        const clang::Stmt *ST,
        CppSig::MacroForest::Roots &ExpansionRoots,
        clang::ASTContext &Ctx);

    void matchArguments(
        clang::ASTContext &Ctx,
        CppSig::MacroForest::Roots &ExpansionRoots);

    // If ST is an Expr, then returns its desugared canonical type.
    // Otherwise, returns "@stmt"
    std::string getType(clang::ASTContext &Ctx, const clang::Stmt *ST);

    // Formats a macro expansion which has at least one statement,
    // but is not guaranteed to be transformable
    std::string formatExpansionSignature(
        clang::ASTContext &Ctx,
        CppSig::MacroExpansionNode *Expansion);

} // namespace CppSig
