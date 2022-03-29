#pragma once

#include "clang/AST/ASTContext.h"
#include "clang/AST/Expr.h"
#include "clang/AST/Stmt.h"
#include "clang/Basic/SourceManager.h"

#include <set>

using namespace std;

using namespace clang;

// Copied from clang/AST/OperationKinds.def
const set<BinaryOperator::Opcode> CSubSetBinOpsNonAssign =
    {
        // [C++ 5.5] Pointer-to-member operators.
        // BO_PtrMemD, // ".*"
        // BO_PtrMemI, // "->*"
        // [C99 6.5.5] Multiplicative operators.
        BO_Mul,  // "*"
        BO_Div,  // "/"
        BO_Rem,  // "%"
                 // [C99 6.5.6] Additive operators.
        BO_Add,  // "+"
        BO_Sub,  // "-"
                 // [C99 6.5.7] Bitwise shift operators.
                 // BO_Shl,       // "<<"
                 // BO_Shr,       // ">>"
                 // C++20 [expr.spaceship] Three-way comparison operator.
                 // BO_Cmp, // "<=>"
                 // [C99 6.5.8] Relational operators.
        BO_LT,   // "<"
        BO_GT,   // ">"
        BO_LE,   // "<="
        BO_GE,   // ">="
                 // [C99 6.5.9] Equality operators.
        BO_EQ,   // "=="
        BO_NE,   // "!="
                 // [C99 6.5.10] Bitwise AND operator.
                 // BO_And, // "&"
                 // [C99 6.5.11] Bitwise XOR operator.
                 // BO_Xor, // "^"
                 // [C99 6.5.12] Bitwise OR operator.
                 // BO_Or, // "|"
                 // [C99 6.5.13] Logical AND operator.
        BO_LAnd, // "&&"
                 // [C99 6.5.14] Logical OR operator.
        BO_LOr,  // "||"
                 // [C99 6.5.16] Assignment operators.
                 // [C99 6.5.17] Comma operator.
                 // BO_Comma, // ","
};
const set<BinaryOperator::Opcode> CSubSetBinOpsAssign =
    {
        BO_Assign,    // "="
        BO_MulAssign, // "*="
        BO_DivAssign, // "/="
        BO_RemAssign, // "%="
        BO_AddAssign, // "+="
        BO_SubAssign, // "-="
                      // BO_ShlAssign, // "<<="
                      // BO_ShrAssign, // ">>="
                      // BO_AndAssign, // "&="
                      // BO_XorAssign, // "^="
                      // BO_OrAssign,  // "|="
};

bool isBinOpNonAssignInCSubset(BinaryOperator::Opcode OC)
{
    return CSubSetBinOpsNonAssign.find(OC) != CSubSetBinOpsNonAssign.end();
}

bool isBinOpAssignInCSubset(BinaryOperator::Opcode OC)
{
    return CSubSetBinOpsAssign.find(OC) != CSubSetBinOpsAssign.end();
}

// Abstract class for the Cpp2C visitor.
// Only visits statements and expressions in the Cpp2C C language subset.
class CSubsetVisitor
{
protected:
    ASTContext *Ctx;

public:
    CSubsetVisitor(ASTContext *Ctx) : Ctx(Ctx){};

    virtual ~CSubsetVisitor(){};

    virtual void VisitAST()
    {
        if (!Ctx)
        {
            return;
        }
        auto TUD = Ctx->getTranslationUnitDecl();
        VisitTranslationUnitDecl(TUD);
    }

    virtual void VisitTranslationUnitDecl(const TranslationUnitDecl *TUD)
    {
        if (!TUD)
        {
            return;
        }

        // Visit all function definitions in the program
        for (auto D : TUD->decls())
        {
            if (auto FD = dyn_cast_or_null<FunctionDecl>(D))
            {
                if (FD->isThisDeclarationADefinition())
                {
                    VisitFunctionDecl(FD);
                }
            }
        }
    }

    virtual void VisitFunctionDecl(const FunctionDecl *FD)
    {
        if (!FD)
        {
            return;
        }
        if (auto FBody = FD->getBody())
        {
            VisitStmt(FBody);
        }
    }

    virtual void VisitStmt(const Stmt *S)
    {
        if (!S)
        {
            return;
        }

        // ExprStmt
        if (auto ExprStmt = dyn_cast_or_null<Expr>(S))
        {
            VisitExpr(ExprStmt);
        }
        // IfElseStmt
        else if (auto IfElse = dyn_cast_or_null<IfStmt>(S))
        {
            // Check for else branch
            VisitIfElse(IfElse);
        }
        // WhileStmt
        else if (auto While = dyn_cast_or_null<WhileStmt>(S))
        {
            VisitWhile(While);
        }
        // CompoundStmt
        else if (auto Compound = dyn_cast_or_null<CompoundStmt>(S))
        {
            VisitCompound(Compound);
        }
        // ForStmt (Not in formal proof)
        else if (auto For = dyn_cast_or_null<ForStmt>(S))
        {
            VisitFor(For);
        }
        // SwitchStmt (Not in formal proof)
        else if (auto Switch = dyn_cast_or_null<SwitchStmt>(S))
        {
            VisitSwitch(Switch);
        }
        // CaseStmt (Not in formal proof)
        else if (auto Case = dyn_cast_or_null<SwitchCase>(S))
        {
            // We don't need a separeate visitor for labeled cases
            // and default cases, because we just the substatement either way
            VisitCase(Case);
        }
    }

    virtual void VisitExpr(const Expr *E)
    {
        if (!E)
        {
            return;
        }

        // IMPLICIT
        if (auto Implicit = dyn_cast_or_null<ImplicitCastExpr>(E))
        {
            VisitImplicit(Implicit);
        }
        // Num
        else if (auto Num = dyn_cast_or_null<IntegerLiteral>(E))
        {
            VisitNum(Num);
        }
        // Var
        else if (auto DRF = dyn_cast_or_null<clang::DeclRefExpr>(E))
        {
            if (auto Var = dyn_cast_or_null<VarDecl>(DRF->getDecl()))
            {
                if (Var->getType().getAsString().compare("int") == 0)
                {
                    VisitVar(Var);
                }
            }
        }
        // ParenExpr
        else if (auto ParenExpr_ = dyn_cast_or_null<ParenExpr>(E))
        {
            VisitParenExpr(ParenExpr_);
        }
        // UnExpr
        else if (auto UnExpr = dyn_cast_or_null<UnaryOperator>(E))
        {
            auto OC = UnExpr->getOpcode();
            if (OC == UO_Plus || OC == UO_Minus)
            {
                VisitUnExpr(UnExpr);
            }
        }
        // BinExpr
        else if (auto BinExpr = dyn_cast_or_null<BinaryOperator>(E))
        {
            auto OC = BinExpr->getOpcode();
            if (isBinOpNonAssignInCSubset(OC))
            {
                auto E1 = BinExpr->getLHS();
                auto E2 = BinExpr->getRHS();
                if (E1 && E2)
                {
                    VisitBinExpr(BinExpr);
                }
            }
            // Assign
            else if (isBinOpAssignInCSubset(OC))
            {
                const BinaryOperator *Assign = BinExpr;
                if (auto X = dyn_cast_or_null<DeclRefExpr>(BinExpr->getLHS()))
                {
                    auto D = X->getDecl();
                    // Check that LHS is just a variable
                    if (llvm::isa_and_nonnull<VarDecl>(D) &&
                        D->getType().getAsString().compare("int") == 0)
                    {
                        VisitAssign(Assign);
                    }
                }
            }
        }
        // CallOrInvocation (function call)
        else if (auto CallOrInvocation = dyn_cast_or_null<CallExpr>(E))
        {
            VisitCallOrInvocation(CallOrInvocation);
        }
    }

    virtual void VisitIfElse(const IfStmt *IfElse)
    {
        VisitExpr(IfElse->getCond());
        VisitStmt(IfElse->getThen());
        VisitStmt(IfElse->getElse());
    };

    virtual void VisitWhile(const WhileStmt *While)
    {
        VisitExpr(While->getCond());
        VisitStmt(While->getBody());
    }

    virtual void VisitCompound(const CompoundStmt *Compound)
    {
        for (auto &&S : Compound->children())
        {
            VisitStmt(S);
        }
    }

    virtual void VisitFor(const ForStmt *For)
    {
        VisitStmt(For->getInit());
        VisitExpr(For->getCond());
        VisitExpr(For->getInc());
        VisitStmt(For->getBody());
    }

    virtual void VisitSwitch(const SwitchStmt *Switch)
    {
        VisitExpr(Switch->getCond());
        VisitStmt(Switch->getBody());
    }

    virtual void VisitCase(const SwitchCase *Case)
    {
        // Don't visit switch case subexpression because we may transform
        // it to a non-constant expression
        VisitStmt(Case->getSubStmt());
    }

    virtual void VisitImplicit(const ImplicitCastExpr *Implicit)
    {
        VisitExpr(Implicit->getSubExpr());
    }

    virtual void VisitNum(const IntegerLiteral *Num) {}

    virtual void VisitVar(const VarDecl *Var) {}

    virtual void VisitParenExpr(const ParenExpr *ParenExpr_)
    {
        VisitExpr(ParenExpr_->getSubExpr());
    }

    virtual void VisitUnExpr(const UnaryOperator *UnExpr)
    {
        VisitExpr(UnExpr->getSubExpr());
    }

    virtual void VisitBinExpr(const BinaryOperator *BinExpr)
    {
        VisitExpr(BinExpr->getLHS());
        VisitExpr(BinExpr->getRHS());
    }

    virtual void VisitAssign(const BinaryOperator *Assign)
    {
        VisitExpr(Assign->getLHS());
        VisitExpr(Assign->getRHS());
    }

    virtual void VisitCallOrInvocation(const CallExpr *CallOrInvocation)
    {
        // NOTE: This extends the Coq language by including function calls
        // which have arguments that are not in the language
        for (auto &&Arg : CallOrInvocation->arguments())
        {
            VisitExpr(Arg);
        }
    }
};

// Given two expressions in the C language subset, return true if they are
// equal, and false if they are not equal
bool compareTrees(ASTContext *Ctx, const Expr *E1, const Expr *E2)
{
    if (!E1 && !E2)
    {
        return true;
    }
    if (!E1 || !E2)
    {
        return true;
    }

    // IMPLICIT
    if (auto Implicit1 = dyn_cast_or_null<ImplicitCastExpr>(E1))
    {
        if (auto Implicit2 = dyn_cast_or_null<ImplicitCastExpr>(E2))
        {
            return compareTrees(Ctx, Implicit1->getSubExpr(),
                                Implicit2->getSubExpr());
        }
    }
    // Num
    else if (auto Num1 = dyn_cast_or_null<IntegerLiteral>(E1))
    {
        if (auto Num2 = dyn_cast_or_null<IntegerLiteral>(E2))
        {
            return Num1->getValue().eq(Num2->getValue());
        }
    }
    // Var
    else if (auto DRF1 = dyn_cast_or_null<clang::DeclRefExpr>(E1))
    {
        if (auto Var1 = dyn_cast_or_null<VarDecl>(DRF1->getDecl()))
        {
            if (Var1->getType().getAsString().compare("int") == 0)
            {
                if (auto DRF2 = dyn_cast_or_null<clang::DeclRefExpr>(E2))
                {
                    if (auto Var2 = dyn_cast_or_null<VarDecl>(DRF2->getDecl()))
                    {
                        if (Var2->getType().getAsString().compare("int") == 0)
                        {
                            return Var1->getName().equals(Var2->getName());
                        }
                    }
                }
            }
        }
    }
    // ParenExpr
    else if (auto ParenExpr_1 = dyn_cast_or_null<ParenExpr>(E1))
    {
        if (auto ParenExpr_2 = dyn_cast_or_null<ParenExpr>(E2))
        {
            return compareTrees(Ctx, ParenExpr_1->getSubExpr(),
                                ParenExpr_2->getSubExpr());
        }
    }
    // UnExpr
    else if (auto UnExpr1 = dyn_cast_or_null<UnaryOperator>(E1))
    {
        auto OC1 = UnExpr1->getOpcode();
        if (OC1 == UO_Plus || OC1 == UO_Minus)
        {
            if (auto UnExpr2 = dyn_cast_or_null<UnaryOperator>(E2))
            {
                auto OC2 = UnExpr2->getOpcode();
                if (OC2 == UO_Plus || OC2 == UO_Minus)
                {
                    return OC1 == OC2 &&
                           compareTrees(Ctx, UnExpr1->getSubExpr(),
                                        UnExpr2->getSubExpr());
                }
            }
        }
    }
    // BinExpr
    else if (auto BinExpr1 = dyn_cast_or_null<BinaryOperator>(E1))
    {
        auto OC1 = BinExpr1->getOpcode();
        if (isBinOpNonAssignInCSubset(OC1))
        {
            auto E1_1 = BinExpr1->getLHS();
            auto E2_1 = BinExpr1->getRHS();
            if (E1_1 && E2_1)
            {
                if (auto BinExpr2 = dyn_cast_or_null<BinaryOperator>(E2))
                {
                    auto OC2 = BinExpr2->getOpcode();
                    if (isBinOpNonAssignInCSubset(OC1))
                    {
                        auto E1_2 = BinExpr2->getLHS();
                        auto E2_2 = BinExpr2->getRHS();
                        if (E1_2 && E2_2)
                        {
                            return OC1 == OC2 &&
                                   compareTrees(Ctx, E1_1, E1_2) &&
                                   compareTrees(Ctx, E2_1, E2_2);
                        }
                    }
                }
            }
        }
        // Assign
        else if (OC1 == BO_Assign)
        {
            // FIXME: We don't transform assignments or call invocations
            // anyway, so for now we can just return false
            return false;
        }
    }
    // CallOrInvocation (function call)
    else if (llvm::isa_and_nonnull<CallExpr>(E1))
    {
        // FIXME: We don't transform assignments or call invocations
        // anyway, so for now we can just return false
        return false;
    }

    return false;
}

// Given two statements in the C language subset, return true if they are
// equal, and false if they are not equal
bool compareTrees(ASTContext *Ctx, const Stmt *S1, const Stmt *S2)
{
    // Can const pointers be nullptr?
    if (S1 == nullptr && S2 == nullptr)
    {
        return true;
    }
    if (S1 == nullptr || S2 == nullptr)
    {
        return false;
    }

    // ExprStmt
    if (auto ExprStmt1 = dyn_cast_or_null<Expr>(S1))
    {
        if (auto ExprStmt2 = dyn_cast_or_null<Expr>(S2))
        {
            return compareTrees(Ctx, ExprStmt1, ExprStmt2);
        }
    }

    // FIXME: We don't need to check statements right now since we
    // expect arguments to be expressions, but we should to be complete

    return false;
}
