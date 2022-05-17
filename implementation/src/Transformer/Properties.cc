#include "Transformer/Properties.hh"
#include "Utils/ExpansionUtils.hh"

#include <vector>

namespace Transformer
{
    using clang::DeclRefExpr;
    using clang::dyn_cast_or_null;
    using clang::Expr;
    using Utils::collectLocalVarDeclRefExprs;
    using Utils::compareTrees;
    using Utils::containsDeclRefExpr;
    using Utils::containsLocalVars;
    using Utils::expansionHasUnambiguousSignature;
    using Utils::mustBeConstExpr;

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

} // namespace Transformer
