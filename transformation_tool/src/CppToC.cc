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

// Source code rewriter
Rewriter RW;

// Kinds of smart pointers;
// https://docs.microsoft.com/en-us/cpp/cpp/smart-pointers-modern-cpp?view=msvc-170#kinds-of-smart-pointers

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

    // Step 1:  Visit function definitions
    //          This is done by the superclass
    // Step 2:  Visit expressions and statements
    //          (In Clang, expression is a type of statement)

    // Identity transform
    virtual bool VisitIntegerLiteral(IntegerLiteral *I)
    {
        SourceLocation SL = I->getLocation();
        unsigned int SpLN = SM->getSpellingLineNumber(SL);

        // If this integer did not come from a macro, don't transform it
        if (!SL.isMacroID())
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

        // Only transform function-like macros
        if (!MI->isFunctionLike())
        {
            return true;
        }

        // Only transform function-like macros with no arguments
        if (!MI->param_empty())
        {
            return true;
        }

        // Get the start of the macro definition line
        SourceLocation DefLineBegin = SM->translateLineCol(
            SM->getMainFileID(), SpLN, 1);

        // TODO: Find a more stable way of getting the end of
        // the macro definition line.
        // Right now this won't work if the macro definition
        // contains more than 1000 characters
        SourceLocation DefLineEnd = SM->translateLineCol(
            SM->getMainFileID(), SpLN, 1000);

        LangOptions LO = Ctx->getLangOpts();

        // Convert the location to a character range for replacement
        CharSourceRange DefCharSourceRange =
            Lexer::getAsCharRange(DefLineBegin, *SM, LO);

        // Set the end of the range to the end of the macro definition line
        DefCharSourceRange.setEnd(DefLineEnd);

        // Get the start of the macro definition
        SourceLocation DefBegin(MI->getDefinitionLoc());
        // The starting point we get from MI->getDefinitionLoc is the start
        // of the defined macro's name.
        // We want the point just beyond the macro's name, plus its open
        // and close parens for formals (since by this point we know the
        // macro has no parameters), plus one more space for the start of
        // the first token in the macro's definition
        DefBegin = DefBegin.getLocWithOffset(MacroName.length() + 3);
        // errs() << "\n"
        //        << DefBegin.printToString(*SM) << "\n";

        // Get the end of the macro's definition
        SourceLocation StartOfTokenAtDefEnd(MI->getDefinitionEndLoc());
        SourceLocation DefEnd(
            Lexer::getLocForEndOfToken(StartOfTokenAtDefEnd, 0, *SM, LO));

        // Get the macro body as a string
        string MacroBody(
            SM->getCharacterData(DefBegin),
            SM->getCharacterData(DefEnd) - SM->getCharacterData(DefBegin));
        // errs() << MacroBody << "\n";

        // TODO: Add the new function definition to the source
        // code and list of function names in the program instead
        // of replacing the macro definition

        // FIXME: If a macro contains multiple integers then we perform
        // multiple replacements. We should only perform one
        RW.ReplaceText(
            DefCharSourceRange,
            "int " + MacroName + "() { return " + MacroBody + "; }");
        return true;
    }

    // Identity transform: We can't transform macros into functions
    // where a constant expression is expected
    // TODO: Find out if this prevents transformation of children
    virtual bool VisitConstantExpr(ConstantExpr *CE)
    {
        return true;
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
            if (SM.isInFileID(DL, MFID))
            {
                string MacroName = Macro.getFirst()->getName().str();
                MacroInfo *MI = PP.getMacroInfo(II);

                unsigned int SpLN = SM.getSpellingLineNumber(DL);
                auto MNMIEntry = pair<string, MacroInfo *>(MacroName, MI);
                auto LNMNEntry = pair<unsigned int, string>(SpLN, MacroName);

                MacroNamesToMacroInfo->insert(MNMIEntry);
                LineNumbersToMacroNames->insert(LNMNEntry);
                // errs() << MacroName << "\n";
            }
        }

        // Collect the names of all the functions defined in the program
        CFVvisitor->TraverseDecl(Ctx.getTranslationUnitDecl());

        CTCvisitor = new CppToCVisitor(CI,
                                       MacroNamesToMacroInfo,
                                       LineNumbersToMacroNames);

        // Give the transformer the set of declared functions
        CTCvisitor->setFunctionNames(CFVvisitor->getFunctionNames());

        // Run the transformer
        CTCvisitor->TraverseDecl(Ctx.getTranslationUnitDecl());

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
