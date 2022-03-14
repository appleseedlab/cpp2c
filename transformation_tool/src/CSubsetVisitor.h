#pragma once

#include "clang/AST/ASTContext.h"
#include "clang/AST/Expr.h"
#include "clang/AST/Stmt.h"
#include "clang/Basic/SourceManager.h"

using namespace clang;

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
            if (auto FD = dyn_cast<FunctionDecl>(D))
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
        if (auto ExprStmt = dyn_cast<Expr>(S))
        {
            VisitExpr(ExprStmt);
        }
        // IfElseStmt
        else if (auto IfElse = dyn_cast<IfStmt>(S))
        {
            // Check for else branch
            const Expr *E = IfElse->getCond();
            const Stmt *S1 = IfElse->getThen();
            const Stmt *S2 = IfElse->getElse();
            if (E && S1 && S2)
            {
                VisitIfElse(IfElse);
            }
        }
        // WhileStmt
        else if (auto While = dyn_cast<WhileStmt>(S))
        {
            const Expr *E = While->getCond();
            const Stmt *S1 = While->getBody();
            if (E && S1)
            {
                VisitWhile(While);
            }
        }
        // CompoundStmt
        else if (auto Compound = dyn_cast<CompoundStmt>(S))
        {
            VisitCompound(Compound);
        }
    }

    virtual void VisitExpr(const Expr *E)
    {
        if (!E)
        {
            return;
        }

        // IMPLICIT
        if (auto Implicit = dyn_cast<ImplicitCastExpr>(E))
        {
            VisitImplicit(Implicit);
        }
        // Num
        else if (auto Num = dyn_cast<IntegerLiteral>(E))
        {
            VisitNum(Num);
        }
        // Var
        else if (auto DRF = dyn_cast<clang::DeclRefExpr>(E))
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
        else if (auto ParenExpr_ = dyn_cast<ParenExpr>(E))
        {
            VisitParenExpr(ParenExpr_);
        }
        // UnExpr
        else if (auto UnExpr = dyn_cast<UnaryOperator>(E))
        {
            auto OC = UnExpr->getOpcode();
            if (OC == UO_Plus || OC == UO_Minus)
            {
                VisitUnExpr(UnExpr);
            }
        }
        // BinExpr
        else if (auto BinExpr = dyn_cast<BinaryOperator>(E))
        {
            auto OC = BinExpr->getOpcode();
            if (OC == BO_Add || OC == BO_Sub || OC == BO_Mul || OC == BO_Div)
            {
                auto E1 = BinExpr->getLHS();
                auto E2 = BinExpr->getRHS();
                if (E1 && E2)
                {
                    VisitBinExpr(BinExpr);
                }
            }
            // Assign
            else if (OC == BO_Assign)
            {
                const BinaryOperator *Assign = BinExpr;
                if (auto X = dyn_cast<DeclRefExpr>(BinExpr->getLHS()))
                {
                    auto D = X->getDecl();
                    // Check that LHS is just a variable
                    if (isa<VarDecl>(D) &&
                        D->getType().getAsString().compare("int") == 0)
                    {
                        VisitAssign(Assign);
                    }
                }
            }
        }
        // CallOrInvocation (function call)
        else if (auto CallOrInvocation = dyn_cast<CallExpr>(E))
        {
            // NOTE: This extends the Coq language by including function calls
            // which have arguments that are not in the language
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
        for (auto &&Arg : CallOrInvocation->arguments())
        {
            VisitExpr(Arg);
        }
    }
};
