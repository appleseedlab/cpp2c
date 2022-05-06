#pragma once

#include "clang/AST/Type.h"
#include "clang/AST/Expr.h"

#include "MacroExpansionNode.hh"

using namespace std;
using namespace clang;

// Hashes a macro based on its name, type, and definition text
string hashMacro(const MacroInfo *MI, SourceManager &SM, const LangOptions &LO);

// Returns true if the given SourceLocation is in a standard header file
bool isInStdHeader(SourceLocation L, SourceManager &SM);

// Gets the desugared, canonical QualType of the given Stmt*
QualType getDesugaredCanonicalType(ASTContext &Ctx, const Stmt *ST);

// Returns true if the given macro expansion has a single, unambiguous
// function signature; false otherwise
bool expansionHasUnambiguousSignature(ASTContext &Ctx,
                                      MacroExpansionNode *Expansion);

// Returns true if the given variable declaration is a global variable,
// false otherwise
bool isGlobalVar(const VarDecl *VD);

// Returns true if the the given expression references any global variables
bool containsGlobalVars(const Expr *E);

// Returns true if the given expression contains any function calls
bool containsFunctionCalls(const Expr *E);

// Returns a pointer to the last-defined global var references in the
// given expression, or nullptr if the expression does not reference any
// global vars
const VarDecl *findLastDefinedGlobalVar(const Expr *E);

// Returns true if the two Stmts have the same structure, false
// otherwise
bool compareTrees(ASTContext &Ctx, const Stmt *S1, const Stmt *S2);

// Returns true if the given Stmt and all its sub Stmts have a spelling
// location in range of any of the source ranges in the given
// SourceRangeCollection
bool StmtAndSubStmtsSpelledInRanges(ASTContext &Ctx, const Stmt *S,
                                    SourceRangeCollection &Ranges);

void collectLValuesSpelledInRange(ASTContext &Ctx,
                                  const Stmt *S,
                                  SourceRangeCollection &Ranges,
                                  set<const Stmt *> *LValuesFromArgs);

bool containsStmt(const Stmt *Haystack, const Stmt *Needle);

void collectStmtsThatChangeRValue(const Stmt *S,
                                  set<const Stmt *> *StmtsThatChangeRValue);
void collectStmtsThatReturnLValue(const Stmt *S,
                                  set<const Stmt *> *StmtsThatReturnLValue);

// Returns true if the given expression references any local variables
bool containsLocalVars(ASTContext &Ctx, const Expr *E);

// Returns true if the given expression contains the unary address of (&)
// operator
bool containsAddressOf(const Expr *E);

// Returns true if the given Decl is a top-level Decl;
// i.e., it does not appear within a function
bool isaTopLevelDecl(ASTContext &Ctx, const Decl *D);

// Returns true if the given Decl is const-qualified
// or for a static local variable
bool isaStaticOrConstDecl(ASTContext &Ctx, const Decl *D);

// Returns true if an expression must be a constant expression;
// i.e., it or its parent expresssion is a global variable initializer,
// enum initializer, array size initializer, case label, or
// bit width specifier
bool mustBeConstExpr(ASTContext &Ctx, const Stmt *S);

// Finds all the references to local vars in the given expression, and pushes
// them all to the back of the given vector
void collectLocalVarDeclRefExprs(const Expr *E,
                                 vector<const DeclRefExpr *> *DREs);

// Returns true if the given Stmt referenceds any decls
bool containsDeclRefExpr(const Stmt *S, const DeclRefExpr *DRE);

// Returns a pointer to the FunctionDecl that the given statement
// was expanded in
const FunctionDecl *getFunctionDeclStmtExpandedIn(ASTContext &Ctx, const Stmt *S);

string getNameOfTopLevelVarOrFunctionDeclStmtExpandedIn(ASTContext &Ctx, const Stmt *S);

string getNameForExpansionTransformation(SourceManager &SM,
                                         MacroExpansionNode *Expansion,
                                         bool TransformToVar);
