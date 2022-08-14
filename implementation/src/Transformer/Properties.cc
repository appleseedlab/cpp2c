#include "Transformer/Properties.hh"
#include "Utils/ExpansionUtils.hh"

#include "clang/ASTMatchers/ASTMatchFinder.h"

#include <vector>
#include <set>
#include <string>
#include <algorithm>
#include <cctype>

namespace Transformer
{
    using clang::BinaryOperator;
    using clang::DeclRefExpr;
    using clang::dyn_cast_or_null;
    using clang::Expr;
    using clang::Rewriter;
    using clang::Stmt;
    using clang::UnaryOperator;
    using llvm::isa_and_nonnull;
    using namespace Utils;

    std::string isWellFormed(
        CppSig::MacroExpansionNode *Expansion,
        clang::ASTContext &Ctx,
        clang::Preprocessor &PP)
    {
        clang::SourceManager &SM = Ctx.getSourceManager();

        // Don't transform expansions appearing where a const expr
        // is required
        if (mustBeConstExpr(Ctx, *Expansion->getStmtsRef().begin()))
        {
            return "Const expr required";
        }

        // Check that the expansion maps to a single expansion
        if (Expansion->getSubtreeNodesRef().size() < 1)
        {
            return "No expansion found";
        }

        // Check that expansion maps to one statement
        if (Expansion->getStmtsRef().size() != 1)
        {
            return "AST Nodes != 1. Equal to " + std::to_string(Expansion->getStmtsRef().size());
        }

        // Check that expansion has an unambiguous signature
        if (!expansionHasUnambiguousSignature(Ctx, Expansion))
        {
            return "Ambiguous function signature";
        }

        auto ST = *Expansion->getStmtsRef().begin();
        auto E = dyn_cast_or_null<Expr>(ST);

        // Check that the expansion expands to an expression
        if (!E)
        {
            return "Did not expand to an expression";
        }

        // Check that expression is completely covered by the expansion
        {
            auto ExpansionBegin = Expansion->getSpellingRange().getBegin();
            auto ExpansionEnd = Expansion->getSpellingRange().getEnd();

            auto ExpressionRange = SM.getExpansionRange(E->getSourceRange());
            auto ExpressionBegin = ExpressionRange.getBegin();
            auto ExpressionEnd = ExpressionRange.getEnd();

            if (!(ExpansionBegin == ExpressionBegin &&
                  ExpansionEnd == ExpressionEnd))
            {
                return "Expansion range != Expression range";
            }

            // It would be better to check that the number of tokens in the
            // expression is >= to the number of tokens in the macro
            // definition, but we don't have an easy way of accessing the number
            // of tokens in an arbitrary expression
            if (!PP.isAtEndOfMacroExpansion(E->getEndLoc()))
            {
                return "Expression end not at expansion end";
            }
        }

        // Check that the arguments are well-formed
        {
            for (auto &&Arg : Expansion->getArgumentsRef())
            {
                if (Arg.getStmtsRef().size() == 0)
                {
                    return "No statement for argument: " + Arg.getName();
                }

                auto ArgFirstExpansion = *Arg.getStmtsRef().begin();
                for (auto ArgExpansion : Arg.getStmtsRef())
                {
                    // TODO: Check this condition?
                    if (!compareTrees(Ctx, ArgFirstExpansion, ArgExpansion) && false)
                    {
                        return "Argument " + Arg.getName() + " not expanded to a consistent AST structure";
                    }

                    // Check that spelling location of the AST node and
                    // all its subexpressions fall within the range of
                    // the argument's token ranges
                    // FIXME: This may render invocations
                    // which contain invocations as arguments as
                    // untransformable, but that doesn't make the
                    // transformation unsound, and we can still get
                    // those expansions on subsequent runs
                    if (!StmtAndSubStmtsSpelledInRanges(Ctx, ArgExpansion,
                                                        Arg.getTokenRangesRef()))
                    {
                        return "Argument " + Arg.getName() +
                               " matched with an AST node "
                               "with an expression outside the spelling location "
                               "of the arg's token ranges";
                    }
                }
            }
        }

        return "";
    }

    std::string isEnvironmentCapturing(
        CppSig::MacroExpansionNode *Expansion,
        clang::ASTContext &Ctx)
    {
        auto ST = *Expansion->getStmtsRef().begin();
        auto E = dyn_cast_or_null<Expr>(ST);
        assert(E != nullptr);

        if (containsLocalVars(Ctx, E))
        {
            std::vector<const DeclRefExpr *> DREs;
            collectLocalVarDeclRefExprs(E, &DREs);
            for (auto &&DRE : DREs)
            {
                bool varComesFromArg = false;
                // Check all the macros arguments for the variable
                for (auto &&Arg : Expansion->getArgumentsRef())
                {
                    for (auto &&S : Arg.getStmtsRef())
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
                    return "Captures environment";
                }
            }
        }

        return "";
    }

    std::string isParamSEFreeAndLValueIndependent(
        CppSig::MacroExpansionNode *Expansion,
        clang::ASTContext &Ctx)
    {
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

        auto ST = *Expansion->getStmtsRef().begin();
        auto E = dyn_cast_or_null<Expr>(ST);
        assert(E != nullptr);

        std::set<const Stmt *> LValuesFromArgs;
        for (auto &&it : Expansion->getArgumentsRef())
        {
            collectLValuesSpelledInRange(Ctx, ST, it.getTokenRangesRef(), &LValuesFromArgs);
        }

        std::set<const Stmt *> StmtsThatChangeRValue;
        collectStmtsThatChangeRValue(ST, &StmtsThatChangeRValue);
        for (auto &&StmtThatChangesRValue : StmtsThatChangeRValue)
        {
            for (auto &&LVal : LValuesFromArgs)
            {
                if (auto UO = dyn_cast_or_null<clang::UnaryOperator>(StmtThatChangesRValue))
                {

                    if (containsStmt(UO, LVal))
                    {
                        return "Writes to R-value of symbol from arguments in unary expression";
                    }
                }
                else if (auto BO = dyn_cast_or_null<BinaryOperator>(StmtThatChangesRValue))
                {
                    if (containsStmt(BO->getLHS(), LVal))
                    {
                        return "Writes to R-value of symbol from arguments in a binary expression";
                    }
                }
                else
                {
                    // NOTE: This shouldn't happen? What do we do here?
                    assert(false);
                }
            }
        }

        std::set<const Stmt *> StmtsThatReturnLValue;
        collectStmtsThatReturnLValue(ST, &StmtsThatReturnLValue);
        for (auto &&StmtThatReturnsLValue : StmtsThatReturnLValue)
        {
            bool isOk = false;
            // We can allow this statement if the entire expression
            // came from a single argument
            for (auto &&it : Expansion->getArgumentsRef())
            {
                if (StmtAndSubStmtsSpelledInRanges(Ctx, StmtThatReturnsLValue, it.getTokenRangesRef()))
                {
                    isOk = true;
                    break;
                }
            }
            // If this expansion is ok, don't proceed with the check
            if (isOk)
            {
                // TODO: Should this be continue instead?
                break;
            }

            for (auto &&LVal : LValuesFromArgs)
            {
                if (containsStmt(StmtThatReturnsLValue, LVal))
                {
                    return "Contains an expression that returns L-value of symbol from arguments";
                }
            }
        }

        clang::SourceManager &SM = Ctx.getSourceManager();

        // Perform function-specific checks
        if (!transformsToVar(Expansion, Ctx))
        {
            auto Parents = Ctx.getParents(*E);
            if (Parents.size() > 1)
            {
                return "Expansion on C++ code?";
            }

            // Check that function call is not on LHS of assignment
            while (Parents.size() > 0)
            {
                auto P = Parents[0];
                if (auto BO = P.get<clang::BinaryOperator>())
                {
                    if (BO->isAssignmentOp())
                    {
                        if (SM.getExpansionRange(BO->getLHS()->getSourceRange()).getAsRange().fullyContains(SM.getExpansionRange(E->getSourceRange()).getAsRange()))
                        {
                            return "Expansion on LHS of assignment";
                        }
                    }
                }
                Parents = Ctx.getParents(P);
            }

            // Check that function call is not the operand of an inc or dec
            Parents = Ctx.getParents(*E);
            while (Parents.size() > 0)
            {
                auto P = Parents[0];
                if (auto UO = P.get<clang::UnaryOperator>())
                {
                    if (UO->isIncrementDecrementOp())
                    {
                        return "Expansion operand of -- or ++";
                    }
                }
                Parents = Ctx.getParents(P);
            }

            // Check that function call is not the operand of address of
            // (&)
            Parents = Ctx.getParents(*E);
            while (Parents.size() > 0)
            {
                auto P = Parents[0];
                if (auto UO = P.get<clang::UnaryOperator>())
                {
                    if (UO->getOpcode() == clang::UnaryOperator::Opcode::UO_AddrOf)
                    {
                        return "Expansion operand of &";
                    }
                }
                Parents = Ctx.getParents(P);
            }
        }

        return "";
    }

    std::string isUnsupportedConstruct(
        Transformer::TransformedDefinition *TD,
        clang::ASTContext &Ctx,
        Rewriter &RW)
    {
        // Don't transform definitions with signatures with array types
        // TODO: We should be able to transform these so long as we
        // properly transform array types to pointers
        if (TD->hasArrayTypes())
        {
            return "Transformed signature includes array types";
        }

        // Check that the transformed definition's signature
        // does not include function types or function pointer
        // types.
        // Returning a function is unhygienic, but function parameters
        // are fine.
        // TODO: We could allow function parameters if we could
        // emit the names of parameters correctly, and we could possibly
        // allow function return types if we cast them to pointers
        if (TD->hasFunctionTypes())
        {
            return "Transformed signature includes function or function pointer types";
        }

        // Don't transform functions that contain embedded anonymous
        // struct types
        // TODO: still transform if the embedded type is not anonymous
        if (TD->hasEmbeddedTagDeclTypes())
        {
            return "Transformed signature includes embedded type\n";
        }

        auto ST = *TD->getExpansion()->getStmtsRef().begin();
        auto E = dyn_cast_or_null<Expr>(ST);
        assert(E != nullptr);

        // Check that this expansion is not string literal, because it
        // may have been used in a place where a string literal is
        // required, e.g., as the format string to printf
        // TODO:    I think we should be able to transform these if we could fix
        //          transforming array types
        if (isa_and_nonnull<clang::StringLiteral>(ST))
        {
            return "Expansion is a string literal";
        }

        // Don't transform variadic macros
        {
            for (auto &&Arg : TD->getExpansion()->getArgumentsRef())
            {
                std::string lower;
                std::transform(Arg.getName().begin(),
                               Arg.getName().end(),
                               lower.begin(), std::towlower);
                if (lower.find("__va") != std::string::npos)
                {
                    return "Variadic macro";
                }
            }
        }

        // Check that expansion is inside a function, because if it
        // isn't none of the constructs we transform to
        // (var and function call) would be valid at the global scope
        if (getFunctionDeclStmtExpandedIn(Ctx, ST) == nullptr)
        {
            return "Expansion not inside a function definition";
        }

        // Check that the transformed declaration location is allowed
        {
            auto TransformedDeclarationLoc = TD->getTransformedDeclarationLocation(Ctx);
            if (!RW.isRewritable(TransformedDeclarationLoc))
            {
                return "Transformed declaration not in a rewritable location";
            }
        }

        clang::SourceManager &SM = Ctx.getSourceManager();

        // Check that the transformed definition location is allowed
        {
            auto TransformedDefinitionLoc = TD->getTransformedDefinitionLocation(Ctx);
            if (!RW.isRewritable(TransformedDefinitionLoc))
            {
                return "Transformed definition not in a rewritable location";
            }
            if (!SM.isInMainFile(TransformedDefinitionLoc))
            {
                return "Transformed definition location not in main file";
            }
        }

        // Check that transformed expansion range is allowed
        {
            if (!RW.isRewritable(TD->getInvocationReplacementRange().getBegin()) ||
                !RW.isRewritable(TD->getInvocationReplacementRange().getEnd()))
            {
                return "Expansion not in a rewritable location";
            }

            if (!SM.isInMainFile(TD->getInvocationReplacementRange().getBegin()) ||
                !SM.isInMainFile(TD->getInvocationReplacementRange().getEnd()))
            {
                return "Transformed expansion not in main file";
            }
        }

        return "";
    }

} // namespace Transformer
