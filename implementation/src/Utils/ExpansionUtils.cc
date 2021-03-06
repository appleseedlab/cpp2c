#include "Utils/ExpansionUtils.hh"

#include "clang/AST/ASTTypeTraits.h"
#include "clang/AST/ASTContext.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/AST/ParentMapContext.h"
#include "clang/Lex/Lexer.h"

#include <chrono>

namespace Utils
{
    using CppSig::MacroExpansionNode;
    using namespace clang;
    using namespace llvm;
    using namespace std;

    bool transformsToVar(
        MacroExpansionNode *Expansion,
        ASTContext &Ctx)
    {
        auto ST = *Expansion->getStmtsRef().begin();
        auto E = dyn_cast_or_null<Expr>(ST);
        assert(E != nullptr);
        return Expansion->getMI()->isObjectLike() &&
               !containsGlobalVars(E) &&
               !containsFunctionCalls(E) &&
               getDesugaredCanonicalType(Ctx, ST).getAsString() != "void";
    }

    inline SourceLocation getStmtOrExprLocation(const Stmt &Node)
    {
        if (const auto E = dyn_cast_or_null<Expr>(&Node))
            return E->getExprLoc();
        else
            return Node.getBeginLoc();
    }

    bool isInStdHeader(SourceLocation L, SourceManager &SM)
    {
        auto FN = SM.getFilename(L);
        return (FN.str() == "" ||
                FN.startswith("/usr/include") ||
                FN.startswith("/usr/lib"));
    }

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
                                          MacroExpansionNode *Expansion)
    {
        if (Expansion->getStmts().size() != 1)
        {
            return false;
        }
        if (Expansion->getMI()->isFunctionLike())
        {
            for (auto &Arg : Expansion->getArguments())
            {
                std::set<std::string> ArgTypes;
                for (const auto *ST : Arg.getStmts())
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

        if (isa_and_nonnull<CallExpr>(E))
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

        SourceLocation Loc = getStmtOrExprLocation(*S);
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

    void collectStmtsThatReturnLValue(const Stmt *S,
                                      set<const Stmt *> *StmtsThatReturnLValue)
    {
        if (!S)
        {
            return;
        }

        if (auto UO = dyn_cast_or_null<clang::UnaryOperator>(S))
        {
            if (UO->getOpcode() == clang::UnaryOperator::Opcode::UO_AddrOf)
            {
                StmtsThatReturnLValue->insert(S);
            }
        }

        for (auto &&it : S->children())
        {
            collectStmtsThatReturnLValue(it, StmtsThatReturnLValue);
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

        auto Parents = Ctx.getParents(*S);
        while (Parents.size() != 0)
        {
            // Since we only transform C code, we only have to look at one parent
            auto P = Parents.begin();
            if (auto FD = P->get<FunctionDecl>())
            {
                return FD;
            }
            Parents = Ctx.getParents(*P);
        }

        return nullptr;
    }

    const clang::NamedDecl *getTopLevelNamedDeclStmtExpandedIn(ASTContext &Ctx, const Stmt *S)
    {
        if (!S)
        {
            return nullptr;
        }

        Ctx.getParents(*S);
        auto P = (Ctx.getParents(*S).begin());
        // Walk the statement tree up to the top level declarations
        while (P)
        {
            if (auto D = P->get<Decl>())
            {
                if (D->getParentFunctionOrMethod() == nullptr)
                {
                    // Found a top level declaration
                    if (auto ND = dyn_cast_or_null<clang::NamedDecl>(D))
                    {
                        return ND;
                    }
                }
            }
            P = (Ctx.getParents(*P).begin());
        }

        return nullptr;
    }

    string getUniqueNameForExpansionTransformation(
        MacroExpansionNode *Expansion,
        set<string> &UsedSymbols,
        ASTContext &Ctx)
    {
        // Generate a unique name using a timetamp
        auto t = std::chrono::system_clock::now();
        string transformType = transformsToVar(Expansion, Ctx) ? "var" : "function";
        string baseName = Expansion->getName() + "_" + std::to_string(t.time_since_epoch().count()) + transformType;
        string uniqueName = baseName;
        unsigned suffix = 0;
        while (UsedSymbols.find(uniqueName) != UsedSymbols.end())
        {
            uniqueName = baseName + "_" + to_string(suffix);
            suffix += 1;
        }
        return uniqueName;

        /*

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

        */
    }

    clang::QualType getPointeeType(clang::QualType T)
    {
        // Remove all pointers until we get down to the base type
        auto PointeeType = T;
        while (PointeeType.getTypePtr()->isPointerType())
        {
            PointeeType = PointeeType.getTypePtr()->getPointeeType();
        }
        return PointeeType;
    }

    bool containsConditionalEvaluation(const clang::Expr *E)
    {
        if (!E)
        {
            return false;
        }
        if (auto BO = clang::dyn_cast_or_null<clang::BinaryOperator>(E))
        {
            if (BO->getOpcode() == clang::BinaryOperator::Opcode::BO_LAnd ||
                BO->getOpcode() == clang::BinaryOperator::Opcode::BO_LOr)
            {
                return true;
            }
        }
        else if (llvm::isa_and_nonnull<clang::ConditionalOperator>(E))
        {
            return true;
        }
        for (auto &&it : E->children())
        {
            if (auto Ec = clang::dyn_cast_or_null<clang::Expr>(it))
            {
                if (containsConditionalEvaluation(Ec))
                {
                    return true;
                }
            }
        }
        return false;
    }

    std::size_t countMacroDefinitions(
        clang::SourceManager &SM,
        const clang::MacroDefinition &MD)
    {
        size_t count = 1;
        auto temp = MD.getLocalDirective()->getPrevious();
        while (temp != nullptr)
        {
            if (temp->getKind() == clang::MacroDirective::Kind::MD_Define &&
                (SM.getFileID(MD.getLocalDirective()->getLocation()) ==
                 SM.getFileID(temp->getLocation())))
            {
                count++;
            }
            temp = temp->getPrevious();
        }
        return count;
    }

    std::size_t countMacroDefinitions(
        clang::SourceManager &SM,
        const clang::MacroDirective &MD)
    {
        size_t count = 1;
        auto temp = MD.getPrevious();
        while (temp != nullptr)
        {
            if (temp->getKind() == clang::MacroDirective::Kind::MD_Define &&
                (SM.getFileID(MD.getLocation()) ==
                 SM.getFileID(temp->getLocation())))

            {
                count++;
            }
            temp = temp->getPrevious();
        }
        return count;
    }

    std::string fileRealPathOrEmpty(clang::SourceManager &SM, clang::SourceLocation L)
    {
        auto FI = SM.getFileEntryForID(SM.getFileID(L));
        return FI ? FI->tryGetRealPathName().str() : "";
    }

} // namespace Utils
