#include "clang/AST/ASTContext.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ParentMapContext.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendPluginRegistry.h"
#include "clang/Lex/PPCallbacks.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/Rewrite/Frontend/Rewriters.h"

#include "llvm/Support/raw_ostream.h"

#include <iostream>

using namespace clang;
using namespace llvm;
using namespace std;

using MacroNameToInfoPtrMap = map<string, MacroInfo *>;
using LineNumberToMacroNameMap = map<unsigned int, string>;

// TODO: We may want to transform object-like macro as well, as they see
// more usage than nullary function-like macros. Ideally we would add the
// soundness of this proof to the transformation as well.

// Source code rewriter
Rewriter RW;

// Kinds of smart pointers;
// https://tinyurl.com/y8hbbdwq

// Visitor class which collects the names of all functions declared in a
// program
class CollectFunctionNamesVisitor
    : public RecursiveASTVisitor<CollectFunctionNamesVisitor>
{
private:
    ASTContext *Ctx;
    // Set of all function names declared in a program
    // We use a shared_ptr smart pointer so that:
    // a) The freeing of memory is handled automatically
    // b) We can share this pointer across objects
    set<string> FunctionNames;

public:
    explicit CollectFunctionNamesVisitor(CompilerInstance *CI)
        : Ctx(&(CI->getASTContext())),
          FunctionNames() {}

    virtual bool VisitFunctionDecl(FunctionDecl *FDecl)
    {
        string functionName = FDecl
                                  ->getNameInfo()
                                  .getName()
                                  .getAsString();
        FunctionNames.insert(functionName);

        return true;
    }

    set<string> getFunctionNames()
    {
        return FunctionNames;
    }
};

// Visitor class which performs the CppToC transformation
// Visits and transforms the body of each function defined in the program
class CppToCVisitor
    : public RecursiveASTVisitor<CppToCVisitor>
{
private:
    ASTContext *Ctx;
    SourceManager *SM;
    set<string> FunctionNames;
    MacroNameToInfoPtrMap *MacroNamesToMacroInfo;
    LineNumberToMacroNameMap *LineNumbersToMacroNames;
    set<SourceLocation> RewrittenInvocationLocations;
    list<SourceRange> ConstantExpressionRanges;

    struct RewriteInfo
    {
        // Expansion location
        SourceLocation EL;
        // Spelling line number
        unsigned int SpLN;
        // Macro info
        MacroInfo *MI;
        // Macro name
        string MacroName;
    };

    list<RewriteInfo> RewriteInfos;

public:
    explicit CppToCVisitor(
        CompilerInstance *CI,
        MacroNameToInfoPtrMap *MacroNamesToMacroInfo,
        LineNumberToMacroNameMap *LineNumbersToMacroNames)
        : Ctx(&(CI->getASTContext())),
          SM(&(CI->getSourceManager())),
          MacroNamesToMacroInfo(MacroNamesToMacroInfo),
          LineNumbersToMacroNames(LineNumbersToMacroNames)
    {
        RW.setSourceMgr(*SM, CI->getLangOpts());
    }

    // Record locations of case labels and bit fields
    // to prevent transforming them
    virtual bool VisitConstantExpr(ConstantExpr *CE)
    {
        // Get the source range for this constant expression
        SourceRange SR(CE->getSourceRange());

        // Get the range of characters over which the
        // expression was ultimately expanded
        CharSourceRange ECR(SM->getExpansionRange(SR));

        // Conver the char range to a source range
        SourceRange ESR(ECR.getAsRange());

        // Add this source range to this list of source ranges for
        // constant expressions visited so far
        ConstantExpressionRanges.push_back(ESR);

        return true;
    }

    // Record the locations of global variable declarations
    // and array declarations to prevent transforming them
    virtual bool VisitVarDecl(VarDecl *VD)
    {
        // Check if we have encountered a top level declaration
        // or an array declaration
        if (!VD->isLocalVarDecl() || isa<ConstantArrayType>(VD->getType()))
        {
            // Get the source range for this declaration
            SourceRange SR(VD->getSourceRange());

            // Get the range of characters over which the
            // declaration was ultimately expanded
            CharSourceRange ECR(SM->getExpansionRange(SR));

            // Conver the char range to a source range
            SourceRange ESR(ECR.getAsRange());

            // Add this source range to this list of source ranges for
            // constant expressions visited so far
            ConstantExpressionRanges.push_back(ESR);
        }

        return true;
    }

    virtual bool VisitExpr(Expr *E)
    {

        // TODO: Fix this to work for macros defined across multiple lines?

        // If this invocations has side-effects, don't transform it
        if (E->HasSideEffects(*Ctx))
        {
            return true;
        }

        SourceLocation EBL = E->getBeginLoc();
        unsigned int SpLN = SM->getSpellingLineNumber(EBL);

        // If this expression did not come from a macro, don't transform it
        if (!EBL.isMacroID())
        {
            return true;
        }

        std::map<unsigned int, std::string>::iterator Entry =
            LineNumbersToMacroNames->find(SpLN);

        // If this macro was not defined in the source file, don't
        // transform it
        if (Entry == LineNumbersToMacroNames->end())
        {
            return true;
        }

        string MacroName = Entry->second;
        MacroInfo *MI = MacroNamesToMacroInfo->find(MacroName)->second;

        SourceLocation EL(SM->getExpansionLoc(EBL));
        unsigned int ELN(SM->getExpansionLineNumber(EL));

        // If this macro was invoked before it was defined, don't transform it
        // NOTE: This check may be superfluous? Can this even happen?
        // I think this may account for multiply defined macros
        // (at least in cases we care about)
        if (ELN < SpLN)
        {
            return true;
        }

        // Only transform object-like macros and nullary function-like macros
        if (!MI->isObjectLike() && !MI->param_empty())
        {
            return true;
        }

        // TODO: For this to work with macros that have arguments, it will
        // have to check that the number of tokens in the definition
        // and expansion match, not the number of characters
        SourceLocation BeginPlusDefLen(
            EBL.getLocWithOffset(MI->getDefinitionLength(*SM) - 1));
        SourceLocation EEL(E->getEndLoc());
        if (BeginPlusDefLen != EEL)
        {
            return true;
        }

        // Record this rewrite in the list of potential rewrites
        // to perform
        struct RewriteInfo ri =
            {
                .EL = EL,
                .SpLN = SpLN,
                .MI = MI,
                .MacroName = MacroName};
        RewriteInfos.push_back(ri);

        return true;
    }

    void performRewrites()
    {
        LangOptions LO = Ctx->getLangOpts();

        for (auto &&ri : RewriteInfos)
        {

            // If we have already transformed this expansion (i.e., this
            // invocation), don't transform it again
            if (RewrittenInvocationLocations.find(ri.EL) !=
                RewrittenInvocationLocations.end())
            {
                continue;
            }

            // Only rewrite macro expansions which don't overlap
            // with a constant expression
            bool WithinConstExpr = false;
            for (SourceRange &SR : ConstantExpressionRanges)
            {
                errs() << "CE source range" << SR.printToString(*SM) << "\n";
                if (SM->isPointWithin(ri.EL, SR.getBegin(), SR.getEnd()))
                {
                    WithinConstExpr = true;
                    break;
                }
            }
            if (WithinConstExpr)
            {
                continue;
            }
            errs() << "Expr begin source location" << ri.EL.printToString(*SM)
                   << "\n";

            // Get the start of the macro definition line
            SourceLocation DefLineBegin = SM->translateLineCol(
                SM->getMainFileID(), ri.SpLN, 1);

            // TODO: Find a more stable way of getting the end of
            // the macro definition line.
            // Right now this won't work if the macro definition
            // contains more than 1000 characters
            SourceLocation DefLineEnd = SM->translateLineCol(
                SM->getMainFileID(), ri.SpLN, 1000);

            // Convert the location to a character range for replacement
            CharSourceRange DefCharSourceRange =
                Lexer::getAsCharRange(DefLineBegin, *SM, LO);

            // Set the end of the range to the end of the macro definition line
            DefCharSourceRange.setEnd(DefLineEnd);

            // Get the start of the macro definition
            SourceLocation DefBegin(ri.MI->getDefinitionLoc());
            // The starting point we get from MI->getDefinitionLoc is the start
            // of the defined macro's name.
            // We want the point just beyond the macro's name, plus its open
            // and close parens for formals (if it's a function-like macro,
            // since by this point we know the macro has no parameters),
            // plus one more space for the start of the first token in the
            // macro's definition
            unsigned int offset = ri.MI->isObjectLike() ? 1 : 3;
            DefBegin = DefBegin.getLocWithOffset(
                ri.MacroName.length() + offset);

            // Get the end of the macro's definition
            SourceLocation StartOfTokenAtDefEnd(ri.MI->getDefinitionEndLoc());
            SourceLocation DefEnd(
                Lexer::getLocForEndOfToken(StartOfTokenAtDefEnd, 0, *SM, LO));

            // Get the macro body as a string
            string MacroBody(
                SM->getCharacterData(DefBegin),
                SM->getCharacterData(DefEnd) - SM->getCharacterData(DefBegin));

            // Generate a unique name for the transformed macro
            string FunctionName(ri.MacroName + "_function");
            // Keep incrementing the number at the end of the function name
            // until the name becomes unique
            for (int i = 0;
                 FunctionNames.find(FunctionName) != FunctionNames.end() ||
                 MacroNamesToMacroInfo->find(FunctionName) !=
                     MacroNamesToMacroInfo->end();
                 i++)
            {
                FunctionName = ri.MacroName + "_function" + to_string(i);
            }

            // Generate the definition of the transformed function.
            // Since we are transforming an int, we know that the return type
            // of this invocation is int.
            // TODO: Determine how we can use Dietrich's algorithm and
            // implementation to infer the types of non-integer macros.
            string FunctionDef(
                "int " + FunctionName + "() { return " + MacroBody + "; }");

            // Add the new function definition to the source code.
            RW.InsertTextAfterToken(StartOfTokenAtDefEnd, "\n" + FunctionDef);

            // Compute the range of source code that includes the macro invocation
            // NOTE: For some reason we have to subtract one here? Not sure why...
            offset = ri.MI->isObjectLike() ? 0 : 2;
            SourceRange MacroInvocationRange(
                ri.EL, ri.EL.getLocWithOffset(ri.MacroName.length() + offset - 1));

            // Replace macro invocation with function call
            RW.ReplaceText(MacroInvocationRange, FunctionName + "()");

            // Add the new function to the list of functions defined in the program
            FunctionNames.insert(FunctionName);

            // Add the expansion/invocation to the set of those already transformed
            RewrittenInvocationLocations.insert(ri.EL);
        }
    }

    void setFunctionNames(set<string> FunctionNames)
    {
        this->FunctionNames = FunctionNames;
    }
};

// AST consumer which calls the visitor class to perform the transformation
class CppToCConsumer : public clang::ASTConsumer
{
private:
    CompilerInstance *CI;
    CollectFunctionNamesVisitor *CFVvisitor;
    CppToCVisitor *CTCvisitor;

public:
    explicit CppToCConsumer(CompilerInstance *CI)
        : CI(CI),
          CFVvisitor(new CollectFunctionNamesVisitor(CI)) {}

    virtual void HandleTranslationUnit(ASTContext &Ctx)
    {
        // Collect the names of all the macros defined in the program
        Preprocessor &PP = CI->getPreprocessor();
        SourceManager &SM = CI->getSourceManager();
        FileID MFID = SM.getMainFileID();

        MacroNameToInfoPtrMap *MacroNamesToMacroInfo =
            new MacroNameToInfoPtrMap();
        LineNumberToMacroNameMap *LineNumbersToMacroNames =
            new LineNumberToMacroNameMap();
        for (auto &&Macro : PP.macros())
        {
            const IdentifierInfo *II = Macro.getFirst();
            SourceLocation DL = PP.getMacroInfo(II)->getDefinitionLoc();

            // Is this macro defined in the source file?
            // FIXME: We actually want the names of all macro that are defined,
            // not just those defined in the program. This would let us check
            // if the name of a transformed function we would generate
            // conflicts with the name of an existing macro.
            // If we do this, however, then we would have to check in the
            // transformation visitor if the macro is defined in the source
            // file before transforming.
            if (SM.isInFileID(DL, MFID))
            {
                string MacroName = Macro.getFirst()->getName().str();
                MacroInfo *MI = PP.getMacroInfo(II);

                unsigned int SpLN = SM.getSpellingLineNumber(DL);
                auto MNMIEntry = pair<string, MacroInfo *>(MacroName, MI);
                auto LNMNEntry = pair<unsigned int, string>(SpLN, MacroName);

                MacroNamesToMacroInfo->insert(MNMIEntry);
                LineNumbersToMacroNames->insert(LNMNEntry);
            }
        }

        // Collect the names of all the functions defined in the program
        CFVvisitor->TraverseDecl(Ctx.getTranslationUnitDecl());

        CTCvisitor = new CppToCVisitor(CI,
                                       MacroNamesToMacroInfo,
                                       LineNumbersToMacroNames);

        // Give the transformer the set of declared functions
        CTCvisitor->setFunctionNames(CFVvisitor->getFunctionNames());

        // Gather transformations
        CTCvisitor->TraverseDecl(Ctx.getTranslationUnitDecl());

        // Perform the transformations
        CTCvisitor->performRewrites();

        // TODO: Give the CTC visitor the set of functions defined
        // in the program, and call its visit method to transform all the
        // function definitions in the program
        // Print the results of the rewriting for the current file
        const RewriteBuffer *RewriteBuf =
            RW.getRewriteBufferFor(Ctx.getSourceManager().getMainFileID());
        if (RewriteBuf != nullptr)
        {
            RewriteBuf->write(outs());
        }
        else
        {
            outs() << "No changes to AST\n";
        }

        delete MacroNamesToMacroInfo;
        delete LineNumbersToMacroNames;
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
        return make_unique<CppToCConsumer>(&CI);
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
