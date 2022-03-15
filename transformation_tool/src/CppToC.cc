#include "clang/AST/ASTContext.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ParentMapContext.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendPluginRegistry.h"
#include "clang/Lex/MacroArgs.h"
#include "clang/Lex/PPCallbacks.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/Rewrite/Frontend/Rewriters.h"

#include "llvm/Support/raw_ostream.h"

#include "CollectDeclNamesVisitor.h"
#include "CSubsetExpansionASTRootsCollector.h"
#include "CSubsetHasSideEffects.h"
#include "CSubsetContainsLocalVars.h"
#include "CSubsetInMacroForestExpansionCollector.h"
#include "CSubsetInSourceRangeCollectionCollector.h"
#include "MacroForest.h"
#include "MacroNameCollector.h"

#include <iostream>

using namespace clang;
using namespace llvm;
using namespace std;

using namespace clang::ast_matchers;

// TODO: Add transformation of object-like macros to variables to soundness
// proof

string getType(ASTContext *Ctx, const Stmt *ST)
{
    if (const auto E = dyn_cast<Expr>(ST))
    {
        QualType T = E->getType();
        return T.getDesugaredType(*Ctx).getCanonicalType().getAsString();
    }
    return "@stmt";
}

void printExpansionSignature(ASTContext *Ctx,
                             MacroForest::Node *Expansion,
                             llvm::raw_ostream &os)
{
    os << "[";

    if (Expansion->Stmts.size() == 1)
    {
        os << '"' << getType(Ctx, *Expansion->Stmts.begin()) << '"';
    }
    else if (Expansion->Stmts.size() > 1)
    {
        os << "\"@stmt\"";
    }
    else
    {
        os << "None";
    }

    if (Expansion->MI->isFunctionLike())
    {
        for (auto &Arg : Expansion->Arguments)
        {
            os << ", [\"" << Arg.Name << "\"";
            std::set<std::string> ArgTypes;
            for (const auto *ST : Arg.Stmts)
            {
                ArgTypes.insert('"' + getType(Ctx, ST) + '"');
            }
            if (ArgTypes.size() == 0)
                os << ", None";
            else if (ArgTypes.size() == 1)
                os << ", " << *ArgTypes.begin();
            else
            {
                for (auto &T : ArgTypes)
                {
                    os << ", " << T;
                }
            }
            os << "]";
        }
    }
    os << "]";
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

string getExpansionSignature(ASTContext *Ctx,
                             MacroForest::Node *Expansion,
                             string TransformedName)
{
    assert(expansionHasUnambiguousSignature(Ctx, Expansion));

    string Signature = getType(Ctx, *Expansion->Stmts.begin());
    Signature += " " + TransformedName;
    if (Expansion->MI->isFunctionLike())
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
            Signature += Arg.Name;
            i += 1;
        }
        Signature += ")";
    }
    return Signature;
}

// AST consumer which calls the visitor class to perform the transformation
class CppToCConsumer : public ASTConsumer
{
private:
    CompilerInstance *CI;
    Preprocessor &PP;
    MacroForest::Roots ExpansionRoots;
    set<string> MacroNames;
    set<string> MultiplyDefinedMacros;
    // To give it access to members
    friend class PluginCppToCAction;

public:
    explicit CppToCConsumer(CompilerInstance *CI)
        : CI(CI), PP(CI->getPreprocessor()) {}

    virtual void HandleTranslationUnit(ASTContext &Ctx)
    {
        auto begin_time = std::chrono::high_resolution_clock::now();

        Rewriter RW;
        SourceManager &SM = Ctx.getSourceManager();
        const LangOptions &LO = Ctx.getLangOpts();
        RW.setSourceMgr(SM, LO);

        TranslationUnitDecl *TUD = Ctx.getTranslationUnitDecl();

        // Collect the names of all the variables and functions
        // defined in the program
        set<string> FunctionNames;
        set<string> VarNames;

        CollectDeclNamesVisitor CDNvisitor(CI, &FunctionNames, &VarNames);
        CDNvisitor.TraverseTranslationUnitDecl(TUD);

        // Step 0: Remove all Macro Roots that are not expanded
        // in the main file
        ExpansionRoots.erase(
            remove_if(ExpansionRoots.begin(),
                      ExpansionRoots.end(),
                      [&SM](const MacroForest::Node *N)
                      {
                          // Only look at source files
                          SourceLocation Loc = N->SpellingRange.getBegin();
                          return !SM.isInMainFile(Loc) ||
                                 SM.isWrittenInScratchSpace(Loc);
                      }),
            ExpansionRoots.end());

        // Step 1: Find Top-Level Macro Expansions
        // Use Cpp2C's visitor to only collect roots in the
        // C language subset instead of using a matcher
        errs() << "Step 1: Search for Macro AST Roots in C subset\n";
        vector<const Stmt *> MacroRoots;
        CSubsetExpansionASTRootsCollector CSEARC(&Ctx, MacroRoots);
        CSEARC.VisitAST();

        // Step 2: Find the AST statements that were directly expanded
        // from the top-level expansions
        errs() << "Step 2: Search for " << ExpansionRoots.size()
               << " Top-Level Expansions in "
               << MacroRoots.size() << " AST-Macro Roots (in the C subset) \n";
        for (const auto ST : MacroRoots)
        {
            SourceLocation STExpansionLoc =
                SM.getExpansionLoc(ST->getBeginLoc());
            MacroForest::Node *ExpansionRoot = nullptr;
            for (auto Expansion : ExpansionRoots)
            {
                // Check if the ExpansionRoot and the Node have the
                // same Expansion Location. Previously, we checked if
                // the STExpansionLoc was contained in the Spelling
                // Range. However, this might even span files if macro
                // name and argument list are composed in a macro.
                SourceLocation NodeExpansionLoc =
                    SM.getExpansionLoc(Expansion->SpellingRange.getBegin());
                if (NodeExpansionLoc == STExpansionLoc)
                {
                    // Found the expansion that this expression was expanded
                    // from
                    ExpansionRoot = Expansion;
                    break;
                }
            }

            // If ExpansionRoot is still nulltpr at this point, then we could
            // not find an expansion root that this statement expanded from
            if (ExpansionRoot == nullptr)
            {
                // StringRef Name =
                //     Lexer::getImmediateMacroName(ST->getBeginLoc(), SM, LO);
                // errs() << "     Skipped macro expansion "
                //        << Name << "\n";
                continue;
            }

            // errs() << "     Match macro "
            //        << ExpansionRoot->Name
            //        << " with "
            //        << ExpansionRoot->SubtreeNodes.size()
            //        << " (nested) expansions\n";

            for (auto Expansion : ExpansionRoot->SubtreeNodes)
            {
                CSubsetInMacroForestExpansionCollector CSIMFEC(
                    &Ctx,
                    Expansion->Stmts, Expansion);

                CSIMFEC.VisitStmt(ST);
            }
        }

        // Step 3 : Within Subtrees, Match the Arguments
        errs() << "Step 3: Find Arguments \n";
        for (auto ToplevelExpansion : ExpansionRoots)
        {
            for (auto Expansion : ToplevelExpansion->SubtreeNodes)
            {
                for (auto ST : Expansion->Stmts)
                {
                    // most of the time only a single one.
                    for (auto &Arg : Expansion->Arguments)
                    {
                        CSubsetInSourceRangeCollectionCollector CSISRCC(
                            &Ctx, Arg.Stmts, &Arg.TokenRanges);
                        CSISRCC.VisitStmt(ST);
                    }
                }
            }
        }

        std::set<void *> dumpedNodes;
        dumpedNodes.insert(nullptr);

        // Step 4: Print macro function signatures
        // for (auto ToplevelExpansion : ExpansionRoots)
        // {
        //     for (auto Expansion : ToplevelExpansion->SubtreeNodes)
        //     {
        //         // Skip Expansions that are not a single subtree

        //         // if (m_settings.only_toplevel_macros &&
        //         //     !(Expansion == ToplevelExpansion))
        //         //     continue;

        //         // SANITY CHECK: This is a sanity check that ensures
        //         // the structural integrity of the dumped tree.
        //         if (dumpedNodes.find(Expansion->Parent) == dumpedNodes.end())
        //         {
        //             assert(false);
        //         }
        //         dumpedNodes.insert(Expansion);

        //         Expansion->Root->SpellingRange.print(errs(), SM);
        //         errs() << ";" << Expansion->Name;
        //         errs() << ";" << Expansion->MI->isFunctionLike();
        //         errs() << ";" << Expansion->Arguments.size();
        //         // Dump the structure of our macro expansion-tree
        //         errs() << ";" << (void *)Expansion << ";"
        //                << (void *)Expansion->Parent;
        //         errs() << ";" << Expansion->Stmts.size() << ";";
        //         if (Expansion->Stmts.size() > 0)
        //         {
        //             printExpansionSignature(&Ctx, Expansion, errs());
        //         }
        //         errs() << "\n";
        //     }
        // }

        // Step 5: Determine which macros are hygienic.
        for (auto TopLevelExpansion : ExpansionRoots)
        {
            // Check that the expansion maps to a single expansion
            if (TopLevelExpansion->SubtreeNodes.size() < 0)
            {
                // errs() << "Skipping expanion of "
                //        << TopLevelExpansion->Name
                //        << " because it did not "
                //           "have an expansion\n";
                continue;
            }

            // Check that macro contains no nested expansions
            if (TopLevelExpansion->SubtreeNodes.size() > 1)
            {
                // errs() << "Skipping expanion of "
                //        << TopLevelExpansion->Name
                //        << " because it contained multiple expansions\n";
                continue;
            }

            // Check that the expansion maps to a single AST expression
            if (TopLevelExpansion->Stmts.size() != 1)
            {
                // errs() << "Skipping expanion of "
                //        << TopLevelExpansion->Name
                //        << " because it did not "
                //           "have a single AST node\n";
                continue;
            }

            // Check that expansion has an unambiguous signature
            if (!expansionHasUnambiguousSignature(&Ctx, TopLevelExpansion))
            {
                // errs() << "Skipping expanion of "
                //        << TopLevelExpansion->Name
                //        << " because its function signature was "
                //           "ambiguous \n";
                continue;
            }

            auto ST = *TopLevelExpansion->Stmts.begin();
            auto E = dyn_cast<Expr>(ST);

            if (!E)
            {
                // errs() << "Skipping expanion of "
                //        << TopLevelExpansion->Name
                //        << " because it did not "
                //           "expand to an expression\n";
                continue;
            }

            auto ExpansionBegin = TopLevelExpansion->SpellingRange.getBegin();
            auto ExpansionEnd = TopLevelExpansion->SpellingRange.getEnd();

            auto ExpressionRange =
                SM.getExpansionRange(E->getSourceRange());
            auto ExpressionBegin = ExpressionRange.getBegin();
            auto ExpressionEnd = ExpressionRange.getEnd();

            // Check that expression is completely covered by expansion
            if (!(ExpansionBegin == ExpressionBegin &&
                  ExpansionEnd == ExpressionEnd))
            {
                // errs() << "Skipping expanion of "
                //        << TopLevelExpansion->Name
                //        << " because its expression did not align perfectly "
                //           "with its expansion\n";
                continue;
            }

            // It would be better to check that the number of tokens in the
            // expression is >= to the number of tokens in the macro
            // definition, but we don't an easy way of accessing the number
            // of tokens in an arbitrary expression
            if (!PP.isAtEndOfMacroExpansion(E->getEndLoc()))
            {
                // errs() << "Skipping expanion of "
                //        << TopLevelExpansion->Name
                //        << " because its expression's end did not extend to "
                //           "end of its expansion\n";
                continue;
            }

            // Check that expanded macro is not multiply defined
            if (MultiplyDefinedMacros.find(TopLevelExpansion->Name) !=
                MultiplyDefinedMacros.end())
            {
                // errs() << "Skipping expanion of "
                //        << TopLevelExpansion->Name
                //        << " because the macro is multiply-defined\n";
                continue;
            }

            // TODO: Check that each argument is expanded at least once,
            // and that if it has multiple expansions, they all expand to
            // the same tree
            {
                bool hasUnhygienicArg = false;
                for (auto &&Arg : TopLevelExpansion->Arguments)
                {
                    if (Arg.Stmts.size() == 0)
                    {
                        // errs() << "Skipping expanion of "
                        //        << TopLevelExpansion->Name
                        //        << " because its argument "
                        //        << Arg.Name << " was not expanded\n";
                        hasUnhygienicArg = true;
                        break;
                    }

                    // Check that we found the expected number of expansions
                    // for this argument
                    unsigned ExpectedExpansions =
                        TopLevelExpansion->ExpectedASTNodesForArg[Arg.Name];
                    unsigned ActualExpansions = Arg.Stmts.size();
                    if (ActualExpansions != ExpectedExpansions)
                    {
                        // errs() << "Skipping expanion of "
                        //        << TopLevelExpansion->Name
                        //        << " because its argument "
                        //        << Arg.Name << " was not expanded the "
                        //        << "expected number of times: "
                        //        << ExpectedExpansions << " vs " << ActualExpansions
                        //        << "\n";

                        hasUnhygienicArg = true;
                        break;
                    }

                    auto ArgFirstExpansion = *Arg.Stmts.begin();
                    for (auto ArgExpansion : Arg.Stmts)
                    {
                        if (!compareTrees(&Ctx, ArgFirstExpansion, ArgExpansion))
                        {
                            // errs() << "Skipping expanion of "
                            //        << TopLevelExpansion->Name
                            //        << " because its argument "
                            //        << Arg.Name << " was not expanded to "
                            //        << "a consistent AST structure\n";
                            hasUnhygienicArg = true;
                            break;
                        }
                    }
                    if (hasUnhygienicArg)
                    {
                        break;
                    }
                }
                if (hasUnhygienicArg)
                {
                    continue;
                }
            }

            // Check that the expansion does not contain local variables
            if (CSubsetContainsLocalVars::containsLocalVars(&Ctx, E))
            {
                // errs() << "Skipping expanion of "
                //        << TopLevelExpansion->Name
                //        << " because its expression contained local vars\n";
                continue;
            }

            // Check that the expansion does not contain side-effects
            if (CSubsetHasSideEffects::hasSideEffects(&Ctx, E))
            {
                // errs() << "Skipping expanion of "
                //        << TopLevelExpansion->Name
                //        << " because its expression had side-effects\n";
                continue;
            }

            //// Transform the expansion

            // Generate a unique name
            string transformType =
                TopLevelExpansion->MI->isFunctionLike() ? "_function" : "_var";
            string TransformedName = TopLevelExpansion->Name + transformType;
            unsigned suffix = 0;
            while (FunctionNames.find(TransformedName) != FunctionNames.end() &&
                   VarNames.find(TransformedName) != VarNames.end() &&
                   MacroNames.find(TransformedName) != MacroNames.end())
            {
                TransformedName = TopLevelExpansion->Name +
                                  transformType + "_" + to_string(suffix);
                suffix += 1;
            }
            FunctionNames.insert(TransformedName);
            VarNames.insert(TransformedName);
            MacroNames.insert(TransformedName);

            // Generate the function signature
            string TransformedSignature =
                getExpansionSignature(&Ctx, TopLevelExpansion, TransformedName);

            // Generate the function body
            SourceLocation MacroBodyBegin =
                TopLevelExpansion->MI->tokens().front().getLocation();
            SourceLocation MacroBodyEnd = Lexer::getLocForEndOfToken(
                TopLevelExpansion->DefinitionRange.getEnd(), 0, SM, LO);

            SourceRange MacroBodyRange =
                SourceRange(MacroBodyBegin, MacroBodyEnd);
            CharSourceRange MacroBodyCharRange =
                CharSourceRange::getCharRange(MacroBodyRange);
            string TransformedBody = Lexer::getSourceText(
                                         MacroBodyCharRange, SM, LO)
                                         .str();
            string TransformedDefinition =
                (TopLevelExpansion->MI->isObjectLike()
                     ? " = " + TransformedBody + ";"
                     : " { return " + TransformedBody + "; }");

            // Insert the transformed function definition into the program
            SourceLocation DefinitionEnd =
                TopLevelExpansion->DefinitionRange.getEnd();
            // string FunctionDefinition =
            //     "\n" + TransformedSignature + TransformedDefinition;
            // RW.InsertTextAfterToken(DefinitionEnd,
            //                         StringRef(FunctionDefinition));
            TransformedDefinition =
                TransformedSignature + TransformedDefinition + "\n\n";
            SourceLocation StartOfFile = SM.getLocForStartOfFile(
                SM.getFileID(DefinitionEnd));
            RW.InsertText(StartOfFile, StringRef(TransformedDefinition));

            // Rewrite the invocation into a function call
            string CallOrRef = TransformedName;
            if (TopLevelExpansion->MI->isFunctionLike())
            {
                CallOrRef += "(";
                unsigned i = 0;
                for (auto &&Arg : TopLevelExpansion->Arguments)
                {
                    if (i >= 1)
                    {
                        CallOrRef += ", ";
                    }
                    CallOrRef += Arg.Name;
                    i += 1;
                }
                CallOrRef += ")";
            }
            SourceRange InvocationRange = TopLevelExpansion->SpellingRange;
            RW.ReplaceText(InvocationRange, StringRef(CallOrRef));

            // TODO: Don't issue a transformation if an identical
            // transformation has already been issued; use that one instead
        }

        // Print the results of the rewriting for the current file
        if (const RewriteBuffer *RewriteBuf =
                RW.getRewriteBufferFor(SM.getMainFileID()))
        {
            RewriteBuf->write(outs());
        }
        else
        {
            outs() << "No changes to AST\n";
        }

        auto end_time = std::chrono::high_resolution_clock::now();
        auto duration = std::chrono::duration_cast<std::chrono::microseconds>(
                            end_time - begin_time)
                            .count();
        errs() << "Finished in " << duration << " microseconds."
               << "\n";
    }
};

// Wrap everything into a plugin
class PluginCppToCAction : public PluginASTAction
{

protected:
    unique_ptr<ASTConsumer>
    CreateASTConsumer(CompilerInstance &CI,
                      StringRef file) override
    {
        auto &PP = CI.getPreprocessor();
        auto Cpp2C = make_unique<CppToCConsumer>(&CI);

        MacroNameCollector *MNC = new MacroNameCollector(
            Cpp2C->MacroNames,
            Cpp2C->MultiplyDefinedMacros);
        MacroForest *MF = new MacroForest(CI, Cpp2C->ExpansionRoots);
        PP.addPPCallbacks(unique_ptr<PPCallbacks>(MNC));
        PP.addPPCallbacks(unique_ptr<PPCallbacks>(MF));

        // Return the consumer to initiate the transformation
        return Cpp2C;
    }

    bool ParseArgs(const CompilerInstance &CI,
                   const vector<string> &args) override
    {
        return true;
    }

    // Necessary for ANYTHING to print to stderr
    ActionType getActionType() override
    {
        return ActionType::AddBeforeMainAction;
    }
};

//-----------------------------------------------------------------------------
// Registration
//-----------------------------------------------------------------------------
static FrontendPluginRegistry::Add<PluginCppToCAction>
    X("cpp-to-c", "Transform CPP macros to C functions");
