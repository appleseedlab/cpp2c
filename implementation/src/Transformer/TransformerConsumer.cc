#include "Transformer/Properties.hh"
#include "Callbacks/MacroNameCollector.hh"
#include "Callbacks/IncludeCollector.hh"
#include "Utils/Logging/TransformerMessages.hh"
#include "Transformer/TransformedDefinition.hh"
#include "Transformer/TransformerConsumer.hh"
#include "Transformer/TransformerSettings.hh"
#include "Utils/TransformedDeclarationAnnotation.hh"
#include "Utils/ExpansionUtils.hh"
#include "CppSig/MacroExpansionNode.hh"
#include "CppSig/CppSigUtils.hh"
#include "Visitors/CollectDeclNamesVisitor.hh"
// #include "Visitors/DeanonymizerVisitor.hh"
#include "Visitors/CollectCpp2CAnnotatedDeclsVisitor.hh"
#include "Visitors/DeclRangeVisitor.hh"

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
           UNSUPPORTED_CONSTRUCT = "Unsupported construct",
           TURNED_OFF_CONSTRUCT = "Turned off construct";

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
        CppSig::MacroForest *MF = new MacroForest(*CI,
                                                  TSettings.Verbose,
                                                  ExpansionRoots);
        Callbacks::IncludeCollector *IC =
            new IncludeCollector(IncludeLocToFileRealPath);
        PP.addPPCallbacks(unique_ptr<PPCallbacks>(MNC));
        PP.addPPCallbacks(unique_ptr<PPCallbacks>(MF));
        PP.addPPCallbacks(unique_ptr<PPCallbacks>(IC));
    }

    void TransformerConsumer::debugMsg(std::string s)
    {
        if (TSettings.Verbose)
        {
            llvm::errs() << s;
        }
    }

    void TransformerConsumer::HandleTranslationUnit(ASTContext &Ctx)
    {
        Rewriter RW;
        SourceManager &SM = Ctx.getSourceManager();
        const LangOptions &LO = Ctx.getLangOpts();
        RW.setSourceMgr(SM, LO);
        Preprocessor &PP = CI->getPreprocessor();

        TranslationUnitDecl *TUD = Ctx.getTranslationUnitDecl();

        // If we are deduplicating, then map the hashes of all macros
        // transformed in a prior run to their transformed
        // signatures
        std::map<std::string, std::set<std::string>> MHashToOriginalTransformedSigs;
        std::map<std::string, std::set<std::string>> MHashToAllTransformedSigs;
        std::map<std::string, clang::NamedDecl *> MHashPlusSigToTransformedDecl;
        std::map<std::string, Utils::TransformedDeclarationAnnotation> MHashPlusSigToTransformedDeclTDA;
        std::map<std::string, std::string> MHashPlusSigToName;
        std::map<std::string, std::set<std::string>> MHashPlusSigToDefRealPaths;

        debugMsg("Deserializing CPP2C annotations\n");
        if (TSettings.DeduplicateWhileTransforming)
        {
            Visitors::CollectCpp2CAnnotatedDeclsVisitor CADV(Ctx);
            CADV.TraverseTranslationUnitDecl(TUD);
            auto &TransformedDecls = CADV.getDeclsRef();
            for (auto &&D : TransformedDecls)
            {
                bool isTransformedDecl = false;
                // Only consider transformed *declarations* of functions and
                // variables, not definitions/initializations
                if (auto FD = clang::dyn_cast_or_null<clang::FunctionDecl>(D))
                {
                    isTransformedDecl = !FD->isThisDeclarationADefinition();
                }
                else if (auto VD = clang::dyn_cast_or_null<clang::VarDecl>(D))
                {
                    isTransformedDecl = VD->getInit() == nullptr;
                    if (VD->getInit() != nullptr)
                    {
                        VD->getInit()->dumpColor();
                    }
                }
                if (isTransformedDecl)
                {
                    // Get this decl's first annotation
                    std::string annotation = Utils::getFirstAnnotationOrEmpty(D);
                    nlohmann::json j = Utils::annotationStringToJson(annotation);

                    // Create the unique macro hash based on data in
                    // the JSON object
                    Utils::TransformedDeclarationAnnotation TDA;
                    Utils::from_json(j, TDA);
                    std::string MacroHash = Utils::hashTDAOriginalMacro(TDA);
                    std::string TDAHash = Utils::hashTDA(TDA);

                    // Add this sig to the map of transformed sigs for this macro
                    auto Sig = TDA.TransformedSignature;
                    MHashToOriginalTransformedSigs[MacroHash].insert(Sig);
                    MHashToAllTransformedSigs[MacroHash].insert(Sig);

                    auto MHashPlusSig = MacroHash + Sig;
                    // Map this sig to the decl we found
                    MHashPlusSigToTransformedDecl[MHashPlusSig] = D;
                    // Map this sig to its decl's original TDA
                    MHashPlusSigToTransformedDeclTDA[MHashPlusSig] = TDA;
                    // Map this sig to the name of the decl we found
                    MHashPlusSigToName[MHashPlusSig] = D->getName().str();
                    // Map this sig to the def real paths in the decl we found
                    MHashPlusSigToDefRealPaths[MHashPlusSig] = TDA.TransformedDefinitionRealPaths;
                }
            }
        }
        debugMsg("Done deserializing CPP2C annotations\n");

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
        debugMsg("Done collecting used symbol names\n");

        // debugMsg("Deanonymizing tag decls\n");
        // // Make all anonymous tag decls behind typedefs not anonymous
        // {
        //     DeanonymizerVisitor DV(Ctx, RW);
        //     DV.TraverseTranslationUnitDecl(TUD);
        //     DV.Deanonymize();
        // }
        // debugMsg("Done deanonymizing tag decls\n");

        // Collect set of file IDs that are not #include'd in a declaration
        std::set<std::string> AllowedMacroDefFileRealPaths;
        {

            // Collect decl ranges
            debugMsg("Collecting decl ranges\n");
            Visitors::DeclRangeVisitor DRV(Ctx);
            DRV.TraverseTranslationUnitDecl(TUD);
            auto &DeclRanges = DRV.getDeclRangesRef();
            debugMsg("Done collecting decl ranges\n");

            // Initially allow all files
            for (auto &&it : IncludeLocToFileRealPath)
            {
                AllowedMacroDefFileRealPaths.insert(it.second);
            }

            // Remove files #include'd inside decls
            for (auto &&it : IncludeLocToFileRealPath)
            {
                clang::SourceLocation Loc = it.first;
                for (auto DeclRange : DeclRanges)
                {
                    auto B = DeclRange.getBegin();
                    auto E = DeclRange.getEnd();
                    if (B <= Loc && Loc <= E)
                    {
                        AllowedMacroDefFileRealPaths.erase(it.second);
                    }
                }
            }

            // Allow macros defined in main file
            clang::FileID MainFID = SM.getMainFileID();
            auto FE= SM.getFileEntryForID(MainFID);
            if (FE)
            {
                auto MainFileRealPath = FE->tryGetRealPathName().str();
                AllowedMacroDefFileRealPaths.insert(MainFileRealPath);
            }
        }

        // Step 0: Remove all Macro Roots that are not expanded
        // in the main file
        // (and maybe those that are defined in std headers)
        debugMsg("Step 0: Remove macro roots not in main file\n");
        removeExpansionsNotInMainFile(
            ExpansionRoots, SM, TSettings.OnlyCollectNotDefinedInStdHeaders);
        debugMsg("Finished step 0\n");

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

        // Emit potentially transformable expansions
        if (TSettings.Verbose)
        {
            for (auto TopLevelExpansion : ExpansionRoots)
            {
                std::string RawSig = formatExpansionSignature(Ctx, TopLevelExpansion);
                std::string MHash = TopLevelExpansion->getMacroHash();
                debugMsg("CPP2C:Potentially Transformable Macro Expansion\t" + MHash + '\t' + RawSig + "\n");
            }
        }

        // Step 4: Transform macros that satisfy these requirements:
        // 1) Syntactic well-formedness
        // 2) No environment capture
        // 3) No side-effects in parameters
        // 4) Not turned off (e.g., conditional evaluation)
        // 5) Not unsupported (e.g., not L-value independent, Clang doesn't support rewriting, etc.)
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

            // Turned off construct
            // Currently the only construct that can be toggled is
            // conditional evaluation (i.e., &&, ||, and ternary).
            // This is turned off to prevent the accidental introduction
            // of undefined behavior
            if (!TSettings.TransformConditionalEvaluation)
            {
                if (auto E = clang::dyn_cast_or_null<clang::Expr>(*TopLevelExpansion->getStmtsRef().begin()))
                {
                    if (Utils::containsConditionalEvaluation(E))
                    {
                        if (TSettings.Verbose)
                        {
                            emitUntransformedMessage(errs(), Ctx, TopLevelExpansion, TURNED_OFF_CONSTRUCT, "Conditional evaluation turned off");
                        }
                        continue;
                    }
                }
            }

            // Create the transformed definition
            TransformedDefinition *TD = new TransformedDefinition(Ctx, TopLevelExpansion);

            // Unsupported constructs
            errMsg = isUnsupportedConstruct(TD, Ctx, RW, AllowedMacroDefFileRealPaths);
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

            // Create the annotation and convert it to json
            std::set<std::string> realPaths;
            realPaths.insert(Utils::fileRealPathOrEmpty(SM, TD->getTransformedDefinitionLocation(Ctx)));
            TransformedDeclarationAnnotation TDA = {
                .NameOfOriginalMacro = TD->getExpansion()->getName(),
                .MacroType = TD->getExpansion()->getMI()->isObjectLike() ? "object-like" : "function-like",
                .MacroDefinitionRealPath = Utils::fileRealPathOrEmpty(SM, SM.getFileLoc(TD->getExpansion()->getMI()->getDefinitionLoc())),
                .MacroDefinitionNumber = TD->getExpansion()->getDefinitionNumber(),
                .TransformedDefinitionRealPaths = realPaths,
                .TransformedSignature = TD->getExpansionSignatureOrDeclaration(Ctx, false),
            };
            nlohmann::json j;
            Utils::to_json(j, TDA);
            std::string MacroHash = Utils::hashTDAOriginalMacro(TDA);
            std::string EmittedName = "";

            debugMsg("Trying to find an already-emitted name for " + MacroHash + "\n");
            bool foundPreviousDecl = false;
            bool previousDeclInSameFile = false;
            // Try to find an already-emitted name for this transformation
            if (TSettings.DeduplicateWhileTransforming)
            {
                if (MHashToAllTransformedSigs.find(MacroHash) !=
                    MHashToAllTransformedSigs.end())
                {
                    auto AllTransformedSigsForThisMacro = MHashToAllTransformedSigs.at(MacroHash);
                    auto Sig = TDA.TransformedSignature;
                    if (AllTransformedSigsForThisMacro.find(Sig) !=
                        AllTransformedSigsForThisMacro.end())
                    {
                        auto MHashPlusSig = MacroHash + Sig;
                        // We found a valid pre-existing transformed definition
                        debugMsg("Looking up name for " + MHashPlusSig + "\n");
                        EmittedName = MHashPlusSigToName.at(MHashPlusSig);
                        foundPreviousDecl = true;
                        // Check if the realpath for this transformed decl
                        // (only 1 at this point) is in the list of realpaths for this
                        // transformed decl
                        if (MHashPlusSigToDefRealPaths.find(MHashPlusSig) !=
                            MHashPlusSigToDefRealPaths.end())
                        {
                            if (MHashPlusSigToDefRealPaths.at(MHashPlusSig).find(*TDA.TransformedDefinitionRealPaths.begin()) !=
                                MHashPlusSigToDefRealPaths.at(MHashPlusSig).end())
                            {
                                previousDeclInSameFile = true;
                            }
                        }
                    }
                }
            }
            debugMsg("Done trying to find an emitted name for " + MacroHash + "\n");
            // Generate a unique name for this transformed macro if we haven't found one yet,
            // and add it to the appropriate mappings
            if (EmittedName == "")
            {
                debugMsg("Generating a unique decl for " + MacroHash + "\n");
                auto Sig = TDA.TransformedSignature;
                auto MHashPlusSig = MacroHash + Sig;
                EmittedName = getUniqueNameForExpansionTransformation(TopLevelExpansion, UsedSymbols, Ctx);
                MHashToAllTransformedSigs[MacroHash].insert(TDA.TransformedSignature);
                MHashPlusSigToName[MHashPlusSig] = EmittedName;
                // Only 1 realpath at this point, so we do an unconditional dereference
                MHashPlusSigToDefRealPaths[MHashPlusSig].insert(*TDA.TransformedDefinitionRealPaths.begin());
                debugMsg("Done generating a unique decl for " + MacroHash + "\n");
            }
            UsedSymbols.insert(EmittedName);
            TD->EmittedName = EmittedName;

            // Emit declaration if we did not find a decl for this transformation yet
            if (!foundPreviousDecl)
            {
                // Create the full declaration
                // Add the static keyword to the start of the declaration
                // This is to handle the edge case where we emit the same transformed definition
                // to different files that first compiled, and *then* linked later
                // Write the new decl
                std::ostringstream transformedDefinition;
                transformedDefinition
                    << "static "
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
                        // If the struct/union/enum keyword is present, then we have
                        // to emit the annotation after it
                        annotatedFwdDecl = typeString.insert(prefixLoc + prefixLength, annotation);
                    }
                    else
                    {
                        // If a keyword is not present, then we have to emit
                        // it as well at the start of the forward declaration
                        annotatedFwdDecl = typeString.insert(0, prefix + annotation);
                    }
                    auto failed = RW.InsertTextBefore(
                        SM.getLocForStartOfFile(SM.getFileID(TransformedDeclarationLoc)),
                        StringRef(annotatedFwdDecl + ";\n\n"));
                    assert(!failed);
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

                auto FD = Utils::getTopLevelNamedDeclStmtExpandedIn(Ctx, (*TopLevelExpansion->getStmtsRef().begin()));
                assert(FD != nullptr);
                debugMsg("CPP2C:Transformed Expansion\t" +
                         MacroHash + "\t" +
                         EmittedName + "\t" +
                         FD->getName().str() + "\t" +
                         TDA.TransformedSignature + "\t" +
                         (TD->IsVar ? "var" : "func") + "\n");
            }

            // Emit transformed definition if the previously emitted transformed definition
            // for this macro (if any) is not in the same file as the one we are currently in
            if (!foundPreviousDecl || !previousDeclInSameFile)
            {
                // Emit each transformed definition before the
                // definition of the function in which it is called.
                string TransformedSignature = TD->getExpansionSignatureOrDeclaration(Ctx, true);
                string FullTransformationDefinition = "static " + TransformedSignature + TD->InitializerOrDefinition;

                // NOTE: This has some coupling with an earlier check
                // that the spelling location of the start of the function decl
                // is rewritable
                bool rewriteFailed = RW.InsertTextBefore(
                    TD->getTransformedDefinitionLocation(Ctx),
                    StringRef(FullTransformationDefinition + "\n\n"));
                assert(!rewriteFailed);
                if (TSettings.Verbose)
                {
                    emitTransformedDefinitionMessage(errs(), TD, Ctx, SM, LO);
                }
                if (TSettings.DeduplicateWhileTransforming)
                {
                    auto MHashPlusSig = MacroHash + TDA.TransformedSignature;
                    MHashPlusSigToDefRealPaths[MHashPlusSig].insert(*TDA.TransformedDefinitionRealPaths.begin());
                };
            }

            // Free the TransformedDefinition object since it is no longer needed at this point
            delete TD;
        }

        // Finally, update any declarations which had new definition realpaths added to them
        if (TSettings.DeduplicateWhileTransforming)
        {
            for (auto &&it : MHashToOriginalTransformedSigs)
            {
                auto MacroHash = it.first;
                auto OriginalSigs = it.second;
                for (auto &&Sig : OriginalSigs)
                {
                    auto MHashPlusSig = MacroHash + Sig;
                    // Check if the set of transformed definition realpaths we now have recorded
                    // for this signature is the same as the set of transformed definition
                    // realpaths it was annotated with originally
                    auto OriginalDefRealPaths = MHashPlusSigToTransformedDeclTDA.at(MHashPlusSig).TransformedDefinitionRealPaths;
                    // Check that we emitted any definitions for this macro at all
                    if (MHashPlusSigToDefRealPaths.find(MHashPlusSig) !=
                        MHashPlusSigToDefRealPaths.end())
                    {
                        auto UpdatedDefRealPaths = MHashPlusSigToDefRealPaths.at(MHashPlusSig);
                        assert(UpdatedDefRealPaths.size() >= OriginalDefRealPaths.size());
                        if (OriginalDefRealPaths != UpdatedDefRealPaths)
                        {
                            assert(UpdatedDefRealPaths.size() > OriginalDefRealPaths.size());
                            // Rewrite the corresponding decl with the new annotation
                            debugMsg("Looking up declaration for " + MHashPlusSig + "\n");
                            auto D = MHashPlusSigToTransformedDecl.at(MHashPlusSig);
                            // We assign directly instead of unioning the two sets because
                            // at this point the updated set should be a strict superset
                            // of the original set
                            auto NewTDA = MHashPlusSigToTransformedDeclTDA.at(MHashPlusSig);
                            NewTDA.TransformedDefinitionRealPaths = UpdatedDefRealPaths;

                            auto Attr = clang::dyn_cast<clang::AnnotateAttr>(*D->attrs().begin());

                            nlohmann::json j;
                            Utils::to_json(j, NewTDA);
                            auto newAnnotationString = "annotate(\"" + Utils::escape_json(j.dump()) + "\")";

                            // Replace the old annotation with the new one
                            auto failed = RW.ReplaceText(Attr->getRange(), llvm::StringRef(newAnnotationString));
                            assert(!failed);
                        }
                    }
                }
            }
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