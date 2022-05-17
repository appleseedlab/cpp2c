#include "Transformer/Properties.hh"
#include "Callbacks/MacroNameCollector.hh"
#include "Utils/Logging/TransformerMessages.hh"
#include "Transformer/TransformedDefinition.hh"
#include "Transformer/TransformerConsumer.hh"
#include "Transformer/TransformerSettings.hh"
#include "Utils/ExpansionUtils.hh"
#include "CppSig/MacroExpansionNode.hh"
#include "CppSig/CppSigUtils.hh"
#include "Visitors/CollectDeclNamesVisitor.hh"

#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/Lex/Lexer.h"
#include "clang/Lex/Preprocessor.h"

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
            MacroDefinitionToTransformedDefinitionPrototypes,
            CI->getSourceManager(),
            CI->getLangOpts(),
            TSettings.OnlyCollectNotDefinedInStdHeaders);
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

        // Collect the names of all the variables and functions
        // defined in the program
        set<string> FunctionNames;
        set<string> VarNames;
        {
            CollectDeclNamesVisitor CDNvisitor(CI, &FunctionNames, &VarNames);
            CDNvisitor.TraverseTranslationUnitDecl(TUD);
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

        // Mapping of macro names to all emitted transformed definitions for
        // that macro. This enables to quickly check for duplicate
        // identical transformations
        map<SourceLocation, vector<TransformedDefinition *>>
            MacroDefinitionLocationToTransformedDefinition;

        set<string> TransformedPrototypes;
        set<pair<string, const FunctionDecl *>>
            TransformedDefinitionsAndFunctionDeclExpandedIn;

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

            // Get the location to emit the transformed definition
            // NOTE: There is some coupling here with isUnsupportedConstruct.
            // That function guarantees that FD is not null.
            auto FD = getFunctionDeclStmtExpandedIn(Ctx, *TopLevelExpansion->getStmtsRef().begin());

            //// Transform the expansion

            // If an identical transformation for this expansion exists,
            // use it; otherwise generate a unique name for this transformation
            // and insert its definition into the program
            string EmittedName = "";
            if (TSettings.UnifyMacrosWithSameSignature)
            {
                // If we are unifying macros, then we have to check
                // all transformed definitions for an identical one
                for (auto &&MacroLocationAndTransformedDefinitions : MacroDefinitionLocationToTransformedDefinition)
                {
                    for (auto &&ETD : MacroLocationAndTransformedDefinitions.second)
                    {
                        // Find which, if any, of the prior transformation
                        // definitions of this macro are identical to the one
                        // we are considering adding to the program.
                        if (ETD->IsVar == TD->IsVar &&
                            ETD->VarOrReturnType == TD->VarOrReturnType &&
                            ETD->ArgTypes == TD->ArgTypes &&
                            ETD->InitializerOrDefinition == TD->InitializerOrDefinition)
                        {
                            EmittedName = ETD->EmittedName;
                            break;
                        }
                        // Found a match?
                        if (EmittedName != "")
                        {
                            break;
                        }
                    }
                }
            }
            else
            {
                // Otherwise, we can use the macro definition location to
                // quickly find any identical prior transformations
                if (MacroDefinitionLocationToTransformedDefinition.find(TD->Expansion->getMI()->getDefinitionLoc()) !=
                    MacroDefinitionLocationToTransformedDefinition.end())
                {
                    // Find which, if any, of the prior transformation
                    // definitions of this macro are identical to the one
                    // we are considering adding to the program.
                    for (auto &&ETD : MacroDefinitionLocationToTransformedDefinition[TD->Expansion->getMI()->getDefinitionLoc()])
                    {
                        if (ETD->IsVar == TD->IsVar &&
                            ETD->VarOrReturnType == TD->VarOrReturnType &&
                            ETD->ArgTypes == TD->ArgTypes &&
                            ETD->InitializerOrDefinition == TD->InitializerOrDefinition)
                        {
                            EmittedName = ETD->EmittedName;
                            break;
                        }
                    }
                }
            }

            // If EmittedName is not empty at this point, then we found a match
            if (EmittedName != "")
            {
                if (TSettings.Verbose)
                {
                    errs() << "Not emitting a definition for " +
                                  TopLevelExpansion->getName() +
                                  " because an identical "
                                  "definition already exists\n";
                }
            }
            // Otherwise, we need to generate a unique name for this
            // transformation and emit its definition
            else
            {
                string Basename = getNameForExpansionTransformation(
                    SM, TopLevelExpansion, TD->IsVar);
                EmittedName = Basename;
                unsigned suffix = 0;
                while (FunctionNames.find(EmittedName) != FunctionNames.end() &&
                       VarNames.find(EmittedName) != VarNames.end() &&
                       MacroNames.find(EmittedName) != MacroNames.end())
                {
                    EmittedName = Basename + "_" + to_string(suffix);
                    suffix += 1;
                }
                FunctionNames.insert(EmittedName);
                VarNames.insert(EmittedName);
                MacroNames.insert(EmittedName);

                TD->EmittedName = EmittedName;

                string TransformedSignature =
                    TD->getExpansionSignatureOrDeclaration(Ctx, false);

                string FullTransformationDefinition =
                    TransformedSignature + TD->InitializerOrDefinition;

                TransformedPrototypes.insert(TransformedSignature + ";");
                TransformedDefinitionsAndFunctionDeclExpandedIn.emplace(FullTransformationDefinition, FD);
                // TODO: Only emit transformed definition if verbose
                emitTransformedDefinitionMessage(errs(), TD, Ctx, SM, LO);

                // Record the number of unique definitions emitted for this
                // macro definition
                {
                    string key = hashMacro(TopLevelExpansion->getMI(), SM, LO);
                    // Set the emitted name to the empty string right before
                    // recording the signature so that we get an anonymous
                    // signature
                    string temp = TD->EmittedName;
                    TD->EmittedName = "";
                    MacroDefinitionToTransformedDefinitionPrototypes[key].insert(TD->getExpansionSignatureOrDeclaration(Ctx, true));
                    TD->EmittedName = temp;
                }

                (MacroDefinitionLocationToTransformedDefinition[TD->Expansion->getMI()->getDefinitionLoc()]).push_back(TD);
            }

            // Rewrite the invocation into a function call or var ref
            string CallOrRef = EmittedName;
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
            SourceRange InvocationRange = TopLevelExpansion->getSpellingRange();
            bool rewriteFailed = RW.ReplaceText(InvocationRange, StringRef(CallOrRef));
            assert(!rewriteFailed);

            // TODO: Only emit transformed expansion if verbose
            emitTransformedExpansionMessage(errs(), TopLevelExpansion, Ctx, SM, LO);
        }

        // Free allocated TransformedDefinition objects
        for (auto &&it : MacroDefinitionLocationToTransformedDefinition)
        {
            for (auto &&TD : it.second)
            {
                delete TD;
            }
        }

        // Emit transformed definitions after functions in which they appear
        for (auto &&it : TransformedDefinitionsAndFunctionDeclExpandedIn)
        {
            auto StartOfFD = it.second->getBeginLoc();
            // NOTE: This has some coupling with an earlier check
            // that the spelling location of the start fo the function decl
            // is rewritable
            auto RewriteLoc = SM.getExpansionLoc(StartOfFD);
            // RW.InsertTextAfter(
            //     SM.getLocForEndOfFile(SM.getMainFileID()),
            //     StringRef(it + "\n\n"));
            bool rewriteFailed = RW.InsertTextBefore(
                RewriteLoc,
                StringRef(it.first + "\n\n"));
            assert(!rewriteFailed);
            if (TSettings.Verbose)
            {
                errs() << "Emitted a definition: "
                       << it.first + "\n";
            }
        }

        if (TSettings.OverwriteFiles)
        {
            RW.overwriteChangedFiles();
        }
        else
        {
            // Print the results of the rewriting for the current file
            if (const RewriteBuffer *RewriteBuf =
                    RW.getRewriteBufferFor(SM.getMainFileID()))
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