#pragma once

#include <set>

#include "clang/AST/ASTContext.h"

#include "Constants.h"
#include "MacroForest.h"
#include "Matchers.h"

using namespace std;
using namespace clang;
using namespace llvm;

// Gets the desugared, canonical QualType of the given Stmt*
QualType getDesugaredCanonicalType(ASTContext &Ctx, const Stmt *ST)
{
    if (const auto E = dyn_cast_or_null<Expr>(ST))
    {
        QualType T = E->getType();
        return T.getDesugaredType(Ctx).getCanonicalType();
    }
    return QualType();
}

// Returns true if the given macro expansion has a single, unambiguous
// function signature; false otherwise
bool expansionHasUnambiguousSignature(ASTContext &Ctx,
                                      MacroForest::Node *Expansion)
{
    if (Expansion->Stmts.size() != 1)
    {
        return false;
    }
    if (Expansion->MI->isFunctionLike())
    {
        for (auto &Arg : Expansion->Arguments)
        {
            std::set<std::string> ArgTypes;
            for (const auto *ST : Arg.Stmts)
            {
                auto QT = getDesugaredCanonicalType(Ctx, ST);
                ArgTypes.insert('"' + QT.getAsString() + '"');
            }
            if (ArgTypes.size() != 1)
            {
                return false;
            }
        }
    }
    return true;
}

// Returns true if the given variable declaration is a global variable,
// false otherwise
bool isGlobalVar(const VarDecl *VD)
{
    if (!VD)
    {
        return false;
    }
    return (VD->hasGlobalStorage()) && (!VD->isStaticLocal());
}

// Returns true if the the given expression references any global variables
bool containsGlobalVars(const Expr *E)
{
    if (!E)
    {
        return false;
    }

    if (auto DRE = dyn_cast_or_null<DeclRefExpr>(E))
    {
        if (auto VD = dyn_cast_or_null<VarDecl>(DRE->getDecl()))
        {
            if (isGlobalVar(VD))
            {
                return true;
            }
        }
    }

    for (auto &&it : E->children())
    {
        if (containsGlobalVars(dyn_cast_or_null<Expr>(it)))
        {
            return true;
        }
    }

    return false;
}

// Returns true if the given expression contains any function calls
bool containsFunctionCalls(const Expr *E)
{
    if (!E)
    {
        return false;
    }

    if (auto DRE = dyn_cast_or_null<CallExpr>(E))
    {
        return true;
    }

    for (auto &&it : E->children())
    {
        if (containsFunctionCalls(dyn_cast_or_null<Expr>(it)))
        {
            return true;
        }
    }

    return false;
}

// Returns a pointer to the last-defined global var references in the
// given expression, or nullptr if the expression does not reference any
// global vars
const VarDecl *findLastDefinedGlobalVar(const Expr *E)
{
    const VarDecl *result = nullptr;
    if (!E)
    {
        return result;
    }

    if (auto DRE = dyn_cast_or_null<DeclRefExpr>(E))
    {
        if (auto VD = dyn_cast_or_null<VarDecl>(DRE->getDecl()))
        {
            if (isGlobalVar(VD))
            {
                result = VD;
            }
        }
    }

    for (auto &&it : E->children())
    {
        auto childResult = findLastDefinedGlobalVar(dyn_cast_or_null<Expr>(it));
        if ((!result) ||
            ((childResult) &&
             (childResult->getLocation() > result->getLocation())))
        {
            result = childResult;
        }
    }

    return result;
}

// Returns true if the two Stmts have the same structure, false
// otherwise
bool compareTrees(ASTContext &Ctx, const Stmt *S1, const Stmt *S2)
{
    // TODO: Check for semantic equivalence, right now this
    // just checks for structural equivalence
    if (!S1 && !S2)
    {
        return true;
    }
    if (!S1 || !S2)
    {
        return false;
    }
    auto it1 = S1->child_begin();
    auto it2 = S2->child_begin();
    while (it1 != S1->child_end() && it2 != S2->child_end())
    {
        if (!compareTrees(Ctx, *it1, *it2))
        {
            return false;
        }
        it1++;
        it2++;
    }
    return it1 == S1->child_end() && it2 == S2->child_end();
}

// Returns true if the given Stmt and all its sub Stmts have a spelling
// location in range of any of the source ranges in the given
// SourceRangeCollection
bool StmtAndSubStmtsSpelledInRanges(ASTContext &Ctx, const Stmt *S,
                                    SourceRangeCollection &Ranges)
{
    if (!S)
    {
        return true;
    }

    SourceLocation Loc = clang::ast_matchers::getSpecificLocation(*S);
    SourceLocation SpellingLoc = Ctx.getFullLoc(Loc).getSpellingLoc();
    if (!Ranges.contains(SpellingLoc))
    {
        return false;
    }

    for (auto &&it : S->children())
    {
        if (!StmtAndSubStmtsSpelledInRanges(Ctx, it, Ranges))
        {
            return false;
        }
    }

    return true;
}

void collectLValuesSpelledInRange(ASTContext &Ctx,
                                  const Stmt *S,
                                  SourceRangeCollection &Ranges,
                                  set<const Stmt *> *LValuesFromArgs)
{
    if (!S)
    {
        return;
    }

    if (auto E = dyn_cast_or_null<Expr>(S))
    {
        if (E->isLValue())
        {
            if (StmtAndSubStmtsSpelledInRanges(Ctx, S, Ranges))
            {
                LValuesFromArgs->insert(S);
            }
        }
    }

    for (auto &&it : S->children())
    {
        collectLValuesSpelledInRange(Ctx, it, Ranges, LValuesFromArgs);
    }
}

bool containsStmt(const Stmt *Haystack, const Stmt *Needle)
{
    if (!Haystack)
    {
        return false;
    }
    if (Haystack == Needle)
    {
        return true;
    }
    for (auto &&it : Haystack->children())
    {
        if (containsStmt(it, Needle))
        {
            return true;
        }
    }
    return false;
}

void collectStmtsThatChangeRValue(const Stmt *S,
                                  set<const Stmt *> *StmtsThatChangeRValue)
{
    if (!S)
    {
        return;
    }

    if (auto BO = dyn_cast_or_null<BinaryOperator>(S))
    {
        if (BO->isAssignmentOp())
        {
            StmtsThatChangeRValue->insert(S);
        }
    }
    else if (auto UO = dyn_cast_or_null<clang::UnaryOperator>(S))
    {
        if (UO->isIncrementDecrementOp())
        {
            StmtsThatChangeRValue->insert(S);
        }
    }

    for (auto &&it : S->children())
    {
        collectStmtsThatChangeRValue(it, StmtsThatChangeRValue);
    }
}

void collectStmtsThatReadLValue(const Stmt *S,
                                set<const Stmt *> *StmtsThatReadLValue)
{
    if (!S)
    {
        return;
    }

    else if (auto UO = dyn_cast_or_null<clang::UnaryOperator>(S))
    {
        if (UO->getOpcode() == clang::UnaryOperator::Opcode::UO_AddrOf)
        {
            StmtsThatReadLValue->insert(S);
        }
    }

    for (auto &&it : S->children())
    {
        collectStmtsThatReadLValue(it, StmtsThatReadLValue);
    }
}

// Returns true if the given expression references any local variables
bool containsLocalVars(ASTContext &Ctx, const Expr *E)
{
    if (!E)
    {
        return false;
    }

    if (auto DeclRef = dyn_cast_or_null<DeclRefExpr>(E))
    {
        if (auto VD = dyn_cast_or_null<VarDecl>(DeclRef->getDecl()))
        {
            if (!isGlobalVar(VD))
            {
                return true;
            }
        }
    }

    for (auto &&it : E->children())
    {
        if (containsLocalVars(Ctx, dyn_cast_or_null<Expr>(it)))
        {
            return true;
        }
    }

    return false;
}

// Returns true if the given expression contains the unary address of (&)
// operator
bool containsAddressOf(const Expr *E)
{
    if (!E)
    {
        return false;
    }

    if (auto UO = dyn_cast_or_null<clang::UnaryOperator>(E))
    {
        if (UO->getOpcode() == clang::UnaryOperator::Opcode::UO_AddrOf)
        {
            return true;
        }
    }

    for (auto &&it : E->children())
    {
        if (containsAddressOf(dyn_cast_or_null<Expr>(it)))
        {
            return true;
        }
    }
    return false;
}

// Returns true if the given Decl is a top-level Decl;
// i.e., it does not appear within a function
bool isaTopLevelDecl(ASTContext &Ctx, const Decl *D)
{
    if (!D)
    {
        return false;
    }

    // C++ code may have multiple parents
    auto parents = Ctx.getParents(*D);
    for (auto &&it : parents)
    {
        if (it.get<TranslationUnitDecl>())
        {
            return true;
        }
    }

    return false;
}

// Returns true if the given Decl is const-qualified
// or for a static local variable
bool isaStaticOrConstDecl(ASTContext &Ctx, const Decl *D)
{
    if (!D)
    {
        return false;
    }

    if (auto VD = dyn_cast_or_null<VarDecl>(D))
    {
        if (VD->getType().isConstQualified() || VD->isStaticLocal())
        {
            return true;
        }
    }

    return false;
}

// Returns true if an expression must be a constant expression;
// i.e., it or its parent expresssion is a global variable initializer,
// enum initializer, array size initializer, case label, or
// bit width specifier
bool mustBeConstExpr(ASTContext &Ctx, const Stmt *S)
{
    if (!S)
    {
        return false;
    }

    if (isa_and_nonnull<ConstantExpr>(S))
    {
        return true;
    }

    for (auto &&it : Ctx.getParents(*S))
    {
        if (mustBeConstExpr(Ctx, it.get<Stmt>()) ||
            (isaTopLevelDecl(Ctx, it.get<Decl>()) &&
             !it.get<FunctionDecl>()) ||
            isaStaticOrConstDecl(Ctx, it.get<Decl>()))
        {
            return true;
        }
    }
    return false;
}

// Finds all the references to local vars in the given expression, and pushes
// them all to the back of the given vector
void collectLocalVarDeclRefExprs(const Expr *E,
                                 vector<const DeclRefExpr *> *DREs)
{
    if (!E)
    {
        return;
    }

    if (auto DRE = dyn_cast_or_null<DeclRefExpr>(E))
    {
        if (auto VD = dyn_cast_or_null<VarDecl>(DRE->getDecl()))
        {
            if (!isGlobalVar(VD))
            {
                DREs->push_back(DRE);
            }
        }
    }

    for (auto &&it : E->children())
    {
        collectLocalVarDeclRefExprs(dyn_cast_or_null<Expr>(it), DREs);
    }
}

// Returns true if the given Stmt referenceds any decls
bool containsDeclRefExpr(const Stmt *S, const DeclRefExpr *DRE)
{
    assert(DRE != nullptr);
    if (!S)
    {
        return false;
    }

    if (dyn_cast_or_null<DeclRefExpr>(S) == DRE)
    {
        return true;
    }

    for (auto &&it : S->children())
    {
        if (containsDeclRefExpr(it, DRE))
        {
            return true;
        }
    }
    return false;
}

// Returns a pointer to the FunctionDecl that the given statement
// was expanded in
const FunctionDecl *getFunctionDeclStmtExpandedIn(ASTContext &Ctx, const Stmt *S)
{
    if (!S)
    {
        return nullptr;
    }

    for (auto &&it : Ctx.getParents(*S))
    {
        if (auto FD = it.get<FunctionDecl>())
        {
            return FD;
        }
        else if (auto FD = getFunctionDeclStmtExpandedIn(Ctx, it.get<Stmt>()))
        {
            return FD;
        }
    }
    return nullptr;
}

// Returns true if the given expansion is hygienic.
// If it's not, records the reason why not in the given map
// NOTE: We define hygienic macros as those which meet the following conditions:
//       1) The entire expansions maps to a single argument
//       2) Their arguments expand to a single expression
//       3) They do not capture variables from their environment
bool isExpansionHygienic(ASTContext *Ctx,
                         Preprocessor &PP,
                         MacroForest::Node *TopLevelExpansion,
                         map<string, unsigned> &Stats,
                         bool Verbose)
{
    // Check that the expansion maps to a single expansion
    if (TopLevelExpansion->SubtreeNodes.size() < 1)
    {
        if (Verbose)
        {
            errs() << "Skipping expansion of "
                   << TopLevelExpansion->Name
                   << " because it did not "
                      "have an expansion\n";
        }
        Stats[TopLevelExpansionsWithNoExpansionRoot] += 1;
        return false;
    }

    // Check if macro contains nested expansions
    if (TopLevelExpansion->SubtreeNodes.size() > 1)
    {
        Stats[TopLevelExpansionsWithNestedExpansions] += 1;
    }

    // Check that the expansion maps to a single AST expression
    if (TopLevelExpansion->Stmts.size() != 1)
    {
        if (Verbose)
        {
            errs() << "Skipping expansion of "
                   << TopLevelExpansion->Name
                   << " because it did not "
                      "have a single AST node\n";
        }
        Stats[TopLevelExpansionsWithMultipleASTNodes] += 1;
        return false;
    }

    // Check that expansion has an unambiguous signature
    if (!expansionHasUnambiguousSignature(*Ctx, TopLevelExpansion))
    {
        if (Verbose)
        {
            errs() << "Skipping expansion of "
                   << TopLevelExpansion->Name
                   << " because its function signature was "
                      "ambiguous \n";
        }
        Stats[TopLevelExpansionsWithAmbiguousSignature] += 1;
        return false;
    }

    auto ST = *TopLevelExpansion->Stmts.begin();
    auto E = dyn_cast_or_null<Expr>(ST);

    if (!E)
    {
        if (Verbose)
        {
            errs() << "Skipping expansion of "
                   << TopLevelExpansion->Name
                   << " because it did not "
                      "expand to an expression\n";
        }
        Stats[TopLevelExpansionsThatDidNotExpandToAnExpression] += 1;
        return false;
    }

    auto ExpansionBegin = TopLevelExpansion->SpellingRange.getBegin();
    auto ExpansionEnd = TopLevelExpansion->SpellingRange.getEnd();

    SourceManager &SM = Ctx->getSourceManager();

    auto ExpressionRange = SM.getExpansionRange(E->getSourceRange());
    auto ExpressionBegin = ExpressionRange.getBegin();
    auto ExpressionEnd = ExpressionRange.getEnd();

    // Check that expression is completely covered by expansion
    if (!(ExpansionBegin == ExpressionBegin &&
          ExpansionEnd == ExpressionEnd))
    {
        if (Verbose)
        {
            errs() << "Skipping expansion of "
                   << TopLevelExpansion->Name
                   << " because its expression did not align perfectly "
                      "with its expansion\n";
        }
        Stats[TopLevelExpansionsWithUnalignedBody] += 1;
        return false;
    }

    // It would be better to check that the number of tokens in the
    // expression is >= to the number of tokens in the macro
    // definition, but we don't have an easy way of accessing the number
    // of tokens in an arbitrary expression
    if (!PP.isAtEndOfMacroExpansion(E->getEndLoc()))
    {
        if (Verbose)
        {
            errs() << "Skipping expansion of "
                   << TopLevelExpansion->Name
                   << " because its expression's end did not extend to "
                      "end of its expansion\n";
        }
        Stats[TopLevelExpansionsWithExpressionEndNotAtEndOfExpansion] += 1;
        return false;
    }

    // Check that each argument is expanded the expected number of
    // times, and that if it has multiple expansions, they all
    // expand to the same tree
    for (auto &&Arg : TopLevelExpansion->Arguments)
    {
        if (Arg.Stmts.size() == 0)
        {
            if (Verbose)
            {
                errs() << "Skipping expansion of "
                       << TopLevelExpansion->Name
                       << " because its argument "
                       << Arg.Name << " was not expanded\n";
            }
            Stats[TopLevelExpansionsWithUnexpandedArgument] += 1;
            return false;
        }

        // Check that we found the expected number of expansions
        // for this argument
        unsigned ExpectedExpansions =
            TopLevelExpansion->ExpectedASTNodesForArg[Arg.Name];
        unsigned ActualExpansions = Arg.Stmts.size();
        if (ActualExpansions != ExpectedExpansions)
        {
            if (Verbose)
            {
                errs() << "Skipping expansion of "
                       << TopLevelExpansion->Name
                       << " because its argument "
                       << Arg.Name << " was not expanded the "
                       << "expected number of times: "
                       << ExpectedExpansions << " vs " << ActualExpansions
                       << "\n";
            }
            Stats[TopLevelExpansionsWithMismatchingArgumentExpansionsAndASTNodes] += 1;
            return false;
        }

        auto ArgFirstExpansion = *Arg.Stmts.begin();
        for (auto ArgExpansion : Arg.Stmts)
        {
            if (
                !compareTrees(*Ctx, ArgFirstExpansion, ArgExpansion) &&
                false)
            {
                if (Verbose)
                {
                    errs() << "Skipping expansion of "
                           << TopLevelExpansion->Name
                           << " because its argument "
                           << Arg.Name << " was not expanded to "
                           << "a consistent AST structure\n";
                }
                Stats[TopLevelExpansionsWithInconsistentArgumentExpansions] += 1;
                return false;
            }

            // Check that spelling location of the AST node and
            // all its subexpressions fall within the range
            // argument's token ranges
            // FIXME: This may render invocations
            // which contain invocations as arguments as
            // untransformable, but that doesn't make the
            // transformation unsound
            if (!StmtAndSubStmtsSpelledInRanges(*Ctx, ArgExpansion,
                                                Arg.TokenRanges))
            {
                if (Verbose)
                {
                    errs() << "Skipping expansion of "
                           << TopLevelExpansion->Name
                           << " because its argument "
                           << Arg.Name << " was matched with an AST node "
                           << "with an expression or subexpression "
                           << "with a spelling location outside of the "
                           << "spelling locations of the arg's "
                           << "token ranges\n";
                }
                Stats[TopLevelExpansionsWithArgumentsWhoseASTNodesHaveSpellingLocationsNotInArgumentTokenRanges] += 1;
                return false;
            }
        }
    }

    // Check that any local vars that the expansion contains come from its
    // arguments
    if (containsLocalVars(*Ctx, E))
    {
        vector<const DeclRefExpr *> DREs;
        collectLocalVarDeclRefExprs(E, &DREs);
        for (auto &&DRE : DREs)
        {
            bool varComesFromArg = false;
            // Check all the macros arguments for the variable
            for (auto &&Arg : TopLevelExpansion->Arguments)
            {
                for (auto &&S : Arg.Stmts)
                {
                    if (containsDeclRefExpr(S, DRE))
                    {
                        varComesFromArg = true;
                        break;
                    }
                }
                if (varComesFromArg)
                {
                    break;
                }
            }

            if (!varComesFromArg)
            {
                if (Verbose)
                {
                    errs() << "Skipping expansion of "
                           << TopLevelExpansion->Name
                           << " because its expression contained local vars "
                           << "that did not come from its arguments\n";
                }
                Stats[TopLevelExpansionsWithLocalVarsInBody] += 1;
                if (TopLevelExpansion->MI->isObjectLike())
                {
                    Stats[OLMsWithLocalVarsInBody] += 1;
                }
                else
                {
                    Stats[FLMsWithLocalVarsInBody] += 1;
                }
                return false;
            }
        }
    }

    return true;
}

string getNameForExpansionTransformation(SourceManager &SM,
                                         MacroForest::Node *Expansion,
                                         bool TransformToVar)
{
    // TODO: Add a flag to optionally prepend the transformed name with
    // the filepath. If we are only transforming a single compilation unit,
    // we shouldn't need to prepend the function name with the path
    // to the file the macro was expanded in. This would make
    // the transformed definition name cleaner
    string Filename =
        SM.getFilename(Expansion->SpellingRange.getBegin()).str();

    string transformType = TransformToVar ? "var" : "function";

    // Remove non-alphanumeric characters from the filename
    Filename.erase(remove_if(Filename.begin(), Filename.end(),
                             [](auto const &c) -> bool
                             { return !isalnum(c); }),
                   Filename.end());

    // Prepend the name with the name of the file that the macro was spelled
    // in (with non-alphanumerics removed).
    // We do this to ensure that transformation names are unique across files
    // FIXME: This solution isn't perfect. Example: abc_1.c and abc1.c would
    // both erase to abc1c. If both of these files contained an expansion
    // of macro from a header that they both included, that macro would be
    // transformed to a global var/function with the same name in each of them.
    // We would then get new errors if we try to link these transformed files
    // together.
    return Filename + "_" + Expansion->Name + "_" + transformType;
}
