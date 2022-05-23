#pragma once

#include "CppSig/MacroExpansionNode.hh"
#include "SourceRangeCollection.hh"

#include "clang/AST/ASTContext.h"
#include "clang/Basic/LangOptions.h"
#include "clang/Lex/MacroInfo.h"

#include <set>
#include <string>
#include <vector>

namespace Utils
{
    using CppSig::MacroExpansionNode;

    // Returns true if the given expansion transforms to a variable, false
    // otherwise
    //
    // Transform object-like macros which reference global vars,
    // call functions, or expand to void-type expressions
    // into nullary functions, since global vars initializers cannot contain
    // any of those constcuts
    bool transformsToVar(
        CppSig::MacroExpansionNode *Expansion,
        clang::ASTContext &Ctx);

    // Hashes a macro based on its name, type, and definition text
    std::string hashMacro(
        const clang::MacroInfo *MI,
        clang::SourceManager &SM,
        const clang::LangOptions &LO);

    // Returns true if the given SourceLocation is in a standard header file
    bool isInStdHeader(
        clang::SourceLocation L,
        clang::SourceManager &SM);

    // Gets the desugared, canonical QualType of the given Stmt*
    clang::QualType getDesugaredCanonicalType(
        clang::ASTContext &Ctx,
        const clang::Stmt *ST);

    // Returns true if the given macro expansion has a single, unambiguous
    // function signature; false otherwise
    bool expansionHasUnambiguousSignature(
        clang::ASTContext &Ctx,
        MacroExpansionNode *Expansion);

    // Returns true if the given variable declaration is a global variable,
    // false otherwise
    bool isGlobalVar(const clang::VarDecl *VD);

    // Returns true if the the given expression references any global variables
    bool containsGlobalVars(const clang::Expr *E);

    // Returns true if the given expression contains any function calls
    bool containsFunctionCalls(const clang::Expr *E);

    // Returns a pointer to the last-defined global var references in the
    // given expression, or nullptr if the expression does not reference any
    // global vars
    const clang::VarDecl *findLastDefinedGlobalVar(const clang::Expr *E);

    // Returns true if the two Stmts have the same structure, false
    // otherwise
    bool compareTrees(
        clang::ASTContext &Ctx,
        const clang::Stmt *S1,
        const clang::Stmt *S2);

    // Returns true if the given Stmt and all its sub Stmts have a spelling
    // location in range of any of the source ranges in the given
    // SourceRangeCollection
    bool StmtAndSubStmtsSpelledInRanges(
        clang::ASTContext &Ctx,
        const clang::Stmt *S,
        SourceRangeCollection &Ranges);

    void collectLValuesSpelledInRange(
        clang::ASTContext &Ctx,
        const clang::Stmt *S,
        SourceRangeCollection &Ranges,
        std::set<const clang::Stmt *> *LValuesFromArgs);

    bool containsStmt(
        const clang::Stmt *Haystack,
        const clang::Stmt *Needle);

    void collectStmtsThatChangeRValue(
        const clang::Stmt *S,
        std::set<const clang::Stmt *> *StmtsThatChangeRValue);
    void collectStmtsThatReturnLValue(
        const clang::Stmt *S,
        std::set<const clang::Stmt *> *StmtsThatReturnLValue);

    // Returns true if the given expression references any local variables
    bool containsLocalVars(clang::ASTContext &Ctx, const clang::Expr *E);

    // Returns true if the given expression contains the unary address of (&)
    // operator
    bool containsAddressOf(const clang::Expr *E);

    // Returns true if the given Decl is a top-level Decl;
    // i.e., it does not appear within a function
    bool isaTopLevelDecl(clang::ASTContext &Ctx, const clang::Decl *D);

    // Returns true if the given Decl is const-qualified
    // or for a static local variable
    bool isaStaticOrConstDecl(clang::ASTContext &Ctx, const clang::Decl *D);

    // Returns true if an expression must be a constant expression;
    // i.e., it or its parent expresssion is a global variable initializer,
    // enum initializer, array size initializer, case label, or
    // bit width specifier
    bool mustBeConstExpr(clang::ASTContext &Ctx, const clang::Stmt *S);

    // Finds all the references to local vars in the given expression, and pushes
    // them all to the back of the given vector
    void collectLocalVarDeclRefExprs(
        const clang::Expr *E,
        std::vector<const clang::DeclRefExpr *> *DREs);

    // Returns true if the given Stmt referenceds any decls
    bool containsDeclRefExpr(const clang::Stmt *S, const clang::DeclRefExpr *DRE);

    // Returns a pointer to the FunctionDecl that the given statement
    // was expanded in
    const clang::FunctionDecl *getFunctionDeclStmtExpandedIn(clang::ASTContext &Ctx, const clang::Stmt *S);

    std::string getNameOfTopLevelVarOrFunctionDeclStmtExpandedIn(clang::ASTContext &Ctx, const clang::Stmt *S);

    std::string getUniqueNameForExpansionTransformation(
        CppSig::MacroExpansionNode *Expansion,
        std::set<std::string> &UsedSymbols,
        clang::ASTContext &Ctx);

} // namespace Utils
