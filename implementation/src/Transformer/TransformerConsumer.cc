#include "Transformer/Properties.hh"
#include "Callbacks/MacroNameCollector.hh"
#include "Utils/Logging/TransformerMessages.hh"
#include "Transformer/TransformedDefinition.hh"
#include "Transformer/TransformerConsumer.hh"
#include "Transformer/TransformerSettings.hh"
#include "Utils/TransformedDeclarationAnnotation.hh"
#include "Utils/ExpansionUtils.hh"
#include "CppSig/MacroExpansionNode.hh"
#include "CppSig/CppSigUtils.hh"
#include "Visitors/CollectDeclNamesVisitor.hh"
#include "Visitors/DeanonymizerVisitor.hh"

#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/Lex/Lexer.h"
#include "clang/Lex/Preprocessor.h"

#include <sstream>
#include <iomanip>

namespace Transformer
{
    using namespace clang;
    using namespace std;
    using namespace llvm;
    using namespace Utils;
    using namespace Utils::Logging;
    using namespace CppSig;
    using namespace Visitors;
    using namespace Callbacks;

    string SYNTAX = "Syntactic well-formedness",
           ENVIRONMENT_CAPTURE = "Environment capture",
           PARAMETER_SIDE_EFFECTS = "Parameter side-effects",
           UNSUPPORTED_CONSTRUCT = "Unsupported construct";

    TransformerConsumer::TransformerConsumer(
        CompilerInstance *CI,
        TransformerSettings TSettings)
        : CI(CI),
          TSettings(TSettings)
    {
        // In the constructor, set up the preprocessor callbacks that
        // will be needed during the transformation
        Preprocessor &PP = CI->getPreprocessor();
        MacroNameCollector *MNC = new MacroNameCollector(
            MacroNames,
            MultiplyDefinedMacros,
            TSettings.Verbose,
            CI->getSourceManager(),
            CI->getLangOpts());
        CppSig::MacroForest *MF = new MacroForest(*CI, ExpansionRoots);
        PP.addPPCallbacks(unique_ptr<PPCallbacks>(MNC));
        PP.addPPCallbacks(unique_ptr<PPCallbacks>(MF));
    }

    void TransformerConsumer::HandleTranslationUnit(ASTContext &Ctx)
    {
        Rewriter RW;
        SourceManager &SM = Ctx.getSourceManager();
        const LangOptions &LO = Ctx.getLangOpts();
        RW.setSourceMgr(SM, LO);
        Preprocessor &PP = CI->getPreprocessor();

        TranslationUnitDecl *TUD = Ctx.getTranslationUnitDecl();

        // Collect the names of all the variables, functions, and macros
        // defined in the program
        set<string> UsedSymbols;
        {
            set<string> FunctionNames;
            set<string> VarNames;
            CollectDeclNamesVisitor CDNvisitor(CI, &FunctionNames, &VarNames);
            CDNvisitor.TraverseTranslationUnitDecl(TUD);
            UsedSymbols.insert(FunctionNames.begin(), FunctionNames.end());
            UsedSymbols.insert(VarNames.begin(), VarNames.end());
            UsedSymbols.insert(MacroNames.begin(), MacroNames.end());
        }

        // Make all anonymous structs/union behind typedefs not anonymous
        {
            DeanonymizerVisitor DV(Ctx, RW);
            DV.TraverseTranslationUnitDecl(TUD);
        }

        // Step 0: Remove all Macro Roots that are not expanded
        // in the main file
        // (and maybe those that are defined in std headers)
        removeExpansionsNotInMainFile(
            ExpansionRoots, SM, TSettings.OnlyCollectNotDefinedInStdHeaders);

        // Step 1: Find Top-Level Macro Expansions
        if (TSettings.Verbose)
        {
            errs() << "Step 1: Search for macro AST roots\n";
        }
        auto ExpansionASTRoots = findMacroASTRoots(Ctx);

        // Step 2: Find the AST statements that were directly expanded
        // from the top-level expansions
        if (TSettings.Verbose)
        {
            errs() << "Step 2: Search for " << ExpansionRoots.size()
                   << " top-level expansions in "
                   << ExpansionASTRoots->size() << " AST macro roots\n";
        }
        for (auto ST : *ExpansionASTRoots)
        {
            populateExpansionsWhoseTopLevelStmtIsThisStmt(ST, ExpansionRoots, Ctx);
        }

        // Step 3 : Within Subtrees, Match the Arguments
        if (TSettings.Verbose)
        {
            errs() << "Step 3: Find Arguments \n";
        }
        matchArguments(Ctx, ExpansionRoots);

        // Step 4: Transform macros that satisfy these four requirements:
        // 1) Syntactic well-formedness
        // 2) No environment capture
        // 3) No side-effects in parameters
        // 4) Not unsupported (e.g., not L-value independent, Clang doesn't support rewriting, etc.)
        if (TSettings.Verbose)
        {
            errs() << "Step 4: Transform hygienic and transformable macros \n";
        }

        for (auto TopLevelExpansion : ExpansionRoots)
        {
            // Syntactic well-formedness
            string errMsg = isWellFormed(TopLevelExpansion, Ctx, PP);
            if (errMsg != "")
            {
                if (TSettings.Verbose)
                {
                    emitUntransformedMessage(errs(), Ctx, TopLevelExpansion, SYNTAX, errMsg);
                }
                continue;
            }

            // Environment capture
            errMsg = isEnvironmentCapturing(TopLevelExpansion, Ctx);
            if (errMsg != "")
            {
                if (TSettings.Verbose)
                {
                    emitUntransformedMessage(errs(), Ctx, TopLevelExpansion, ENVIRONMENT_CAPTURE, errMsg);
                }
                continue;
            }

            // Parameter side-effects and L-Value Independence
            errMsg = isParamSEFreeAndLValueIndependent(TopLevelExpansion, Ctx);
            if (errMsg != "")
            {
                if (TSettings.Verbose)
                {
                    emitUntransformedMessage(errs(), Ctx, TopLevelExpansion, PARAMETER_SIDE_EFFECTS, errMsg);
                }
                continue;
            }

            // Create the transformed definition
            TransformedDefinition *TD = new TransformedDefinition(Ctx, TopLevelExpansion);

            // Unsupported constructs
            errMsg = isUnsupportedConstruct(TD, Ctx, RW);
            if (errMsg != "")
            {
                if (TSettings.Verbose)
                {
                    emitUntransformedMessage(errs(), Ctx, TopLevelExpansion, UNSUPPORTED_CONSTRUCT, errMsg);
                }
                // IMPORTANT.
                // TODO: Change unsupported construct to accept a
                // MacroExpansionNode instead of a TransformedDefinition
                // so that we don't need this delete
                delete TD;
                continue;
            }

            //// Transform the expansion
            // 1.   Generate a unique name for the transformed declaration
            // 2.   Emit the transformed declaration at the start of the file
            //      the macro was defined in
            //          a)  Forward declare any structs and unions
            //              in the signature
            // 3.   Replace the invocation with the transformed call or
            //      var ref
            // 4.   Emit the transformed definition before the definition
            //      of the function in which the original macro was called

            // Generate a unique name for this transformed macro
            {
                string EmittedName = getUniqueNameForExpansionTransformation(TopLevelExpansion, UsedSymbols, Ctx);
                UsedSymbols.insert(EmittedName);
                TD->EmittedName = EmittedName;
            }

            // Emit declaration
            {
                // Create the annotation and convert it to json
                TransformedDeclarationAnnotation TDA = {
                    .NameOfOriginalMacro = TD->getExpansion()->getName(),
                    .MacroType = TD->getExpansion()->getMI()->isObjectLike() ? "object-like" : "function-like",
                    .MacroDefinitionDefinitionFileName = SM.getFilename(TD->getExpansion()->getDefinitionRange().getBegin()).str(),
                    .MacroDefinitionNumber = TD->getExpansion()->getDefinitionNumber(),
                    .TransformedSignature = TD->getExpansionSignatureOrDeclaration(Ctx, false),
                };
                nlohmann::json j = TDA;

                // Create the full declaration
                std::ostringstream transformedDefinition;
                transformedDefinition
                    << TD->getExpansionSignatureOrDeclaration(Ctx, true)
                    << "\n"
                    << "    __attribute__((annotate(\""
                    << escape_json(j.dump())
                    << "\")));\n\n";

                // Can only get this from a macro defined callback
                auto TransformedDeclarationLoc = TD->getTransformedDeclarationLocation(Ctx);
                bool rewriteFailed = RW.InsertTextBefore(
                    TransformedDeclarationLoc,
                    StringRef(transformedDefinition.str()));
                assert(!rewriteFailed);

                // Forward declare structs/unions/enums in signature
                auto structNamesInSignature = TD->getStructUnionEnumTypesInSignature();
                for (auto &&it : structNamesInSignature)
                {
                    // Annotate forward declarations with the fact
                    // that they came from Cpp2C
                    auto T = it.getTypePtrOrNull();
                    if (T == nullptr)
                    {
                        assert(false && "nullptr error");
                    }
                    string prefix = (T->isStructureType()
                                         ? "struct"
                                     : T->isUnionType() ? "union"
                                                        : "enum");
                    size_t prefixLength = prefix.length();
                    string annotation = " __attribute__((annotate(\"CPP2C\"))) ";

                    string annotatedFwdDecl = "";
                    string typeString = it.getDesugaredType(Ctx).getCanonicalType().getUnqualifiedType().getAsString();
                    size_t prefixLoc = typeString.find(prefix);
                    if (prefixLoc != string::npos)
                    {
                        // If the struct or union keyword is present, then we have
                        // to emit the annotation after it
                        annotatedFwdDecl = typeString.insert(prefixLoc + prefixLength, annotation);
                    }
                    else
                    {
                        // If a keyword is not present, then we have to emit
                        // it as well at the start of the forward declaration
                        annotatedFwdDecl = typeString.insert(0, prefix + annotation);
                    }
                    RW.InsertTextBefore(
                        SM.getLocForStartOfFile(SM.getFileID(TransformedDeclarationLoc)),
                        StringRef(annotatedFwdDecl + ";\n\n"));
                }
            }

            // Replace invocation with a call or var ref
            {
                string CallOrRef = TD->EmittedName;
                if (!TD->IsVar)
                {
                    CallOrRef += "(";
                    unsigned i = 0;
                    for (auto &&Arg : TopLevelExpansion->getArgumentsRef())
                    {
                        if (i >= 1)
                        {
                            CallOrRef += ", ";
                        }

                        CallOrRef += Arg.getRawText();

                        i += 1;
                    }
                    CallOrRef += ")";
                }
                bool rewriteFailed = RW.ReplaceText(
                    TD->getInvocationReplacementRange(), StringRef(CallOrRef));
                assert(!rewriteFailed);
                // TODO: Only emit transformed expansion if verbose
                if (TSettings.Verbose)
                {
                    emitTransformedExpansionMessage(errs(), TopLevelExpansion, Ctx, SM, LO);
                }
            }

            // Emit transformed definition
            {
                // Emit each transformed definition before the
                // definition of the function in which it is called.
                string TransformedSignature = TD->getExpansionSignatureOrDeclaration(Ctx, true);
                string FullTransformationDefinition = TransformedSignature + TD->InitializerOrDefinition;

                // NOTE: This has some coupling with an earlier check
                // that the spelling location of the start fo the function decl
                // is rewritable
                bool rewriteFailed = RW.InsertTextBefore(
                    TD->getTransformedDefinitionLocation(Ctx),
                    StringRef(FullTransformationDefinition + "\n\n"));
                assert(!rewriteFailed);
                // TODO: Only emit transformed definition if verbose
                if (TSettings.Verbose)
                {
                    emitTransformedDefinitionMessage(errs(), TD, Ctx, SM, LO);
                }
            }

            // Free the TransformedDefinition object since it is no longer needed at this point
            delete TD;
        }

        if (TSettings.OverwriteFiles)
        {
            RW.overwriteChangedFiles();
        }
        else
        {
            // Print the results of the rewriting for the current file
            if (const RewriteBuffer *RewriteBuf = RW.getRewriteBufferFor(SM.getMainFileID()))
            {
                RewriteBuf->write(outs());
            }
            else
            {
                RW.getEditBuffer(SM.getMainFileID()).write(outs());
            }
        }
    }

} // namespace Transformer