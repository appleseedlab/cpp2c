#pragma once

#include <set>

#include "clang/AST/ASTContext.h"

#include "Constants.h"
#include "MacroForest.h"
#include "Matchers.h"

using namespace std;
using namespace clang;
using namespace llvm;

string getType(ASTContext *Ctx, const Stmt *ST)
{
    if (const auto E = dyn_cast_or_null<Expr>(ST))
    {
        QualType T = E->getType();
        return T.getDesugaredType(*Ctx).getCanonicalType().getAsString();
    }
    return "@stmt";
}

bool expansionHasUnambiguousSignature(ASTContext *Ctx,
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
                ArgTypes.insert('"' + getType(Ctx, ST) + '"');
            }
            if (ArgTypes.size() != 1)
            {
                return false;
            }
        }
    }
    return true;
}

bool isGlobalVar(const VarDecl *VD)
{
    if (!VD)
    {
        return false;
    }
    return (VD->hasGlobalStorage()) && (!VD->isStaticLocal());
}

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

bool containsAddressOf(const Expr *E)
{
    if (!E)
    {
        return false;
    }

    if (auto UO = dyn_cast_or_null<UnaryOperator>(E))
    {
        if (UO->getOpcode() == UnaryOperator::Opcode::UO_AddrOf)
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
             !it.get<FunctionDecl>()))
        {
            return true;
        }
    }
    return false;
}

void collectLocalVarDeclRefExprs(const Expr *E, vector<const DeclRefExpr *> *DREs)
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

bool isExpansionHygienic(ASTContext *Ctx,
                         Preprocessor &PP,
                         MacroForest::Node *TopLevelExpansion,
                         map<string, unsigned> &Stats,
                         bool Verbose,
                         set<string> &MultiplyDefinedMacros)
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
        Stats[TopLevelExpansionsWithMultipleExpansionRoots] += 1;
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
    if (!expansionHasUnambiguousSignature(Ctx, TopLevelExpansion))
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
    // definition, but we don't an easy way of accessing the number
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

    // Check that expanded macro is not multiply defined
    if (MultiplyDefinedMacros.find(TopLevelExpansion->Name) !=
        MultiplyDefinedMacros.end())
    {
        if (Verbose)
        {
            errs() << "Skipping expansion of "
                   << TopLevelExpansion->Name
                   << " because the macro is multiply-defined or "
                   << "redefined \n";
        }
        Stats[TopLevelExpansionsOfMultiplyDefinedMacros] += 1;
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
            // auto ArgExpression = dyn_cast_or_null<Expr>(ArgExpansion);
            // assert(nullptr != ArgExpression);
            // if (!CSubsetExprAndSubExprsSpelledInRanges::exprAndSubExprsSpelledInRanges(
            //         Ctx, ArgExpression, &Arg.TokenRanges))
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
                return false;
            }
        }
    }

    // Check that the expansion does not contain the address (&) operator
    if (containsAddressOf(E))
    {
        if (Verbose)
        {
            errs() << "Skipping expansion of "
                   << TopLevelExpansion->Name
                   << " because its expression contained address of (&) \n";
        }
        Stats[TopLevelExpansionsWithAddressOf] += 1;
        return false;
    }

    // Check that the expansion does not contain side-effects
    // if (CSubsetHasSideEffects::hasSideEffects(Ctx, E))
    if (E->HasSideEffects(*Ctx))
    {
        if (Verbose)
        {
            errs() << "Skipping expansion of "
                   << TopLevelExpansion->Name
                   << " because its expression had side-effects\n";
        }
        Stats[TopLevelExpansionsWithSideEffects] += 1;
        return false;
    }

    return true;
}

string getNameForExpansionTransformation(SourceManager &SM,
                                         MacroForest::Node *Expansion,
                                         bool TransformToVar)
{
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

string getExpansionSignature(ASTContext *Ctx,
                             MacroForest::Node *Expansion,
                             bool TransformToVar,
                             string TransformedName)
{
    assert(expansionHasUnambiguousSignature(Ctx, Expansion));

    string Signature = getType(Ctx, *Expansion->Stmts.begin());
    Signature += " " + TransformedName;
    if (!TransformToVar)
    {

        Signature += "(";
        unsigned i = 0;
        for (auto &&Arg : Expansion->Arguments)
        {
            string ArgType = getType(Ctx, *(Arg.Stmts.begin()));
            if (i >= 1)
            {
                Signature += ", ";
            }
            Signature += ArgType + " " + Arg.Name;
            i += 1;
        }
        Signature += ")";
    }
    // Add const qualifier if the expansion was transformed to a global var
    // if (TransformToVar)
    // {
    //     Signature = "const " + Signature;
    // }
    return Signature;
}
