#include "Transformer/TransformerAction.hh"
#include "Transformer/TransformerConsumer.hh"
#include "Callbacks/MacroNameCollector.hh"
#include "CppSig/MacroForest.hh"

namespace Transformer
{
    using namespace std;
    using namespace clang;

    unique_ptr<ASTConsumer>
    TransformerAction::CreateASTConsumer(
        CompilerInstance &CI,
        StringRef file)
    {
        auto &PP = CI.getPreprocessor();
        auto Cpp2C = make_unique<TransformerConsumer>(&CI, Cpp2CSettings);

        // Note: There is a little bit of coupling here with getting
        // the source manager and lang options from the CO
        Callbacks::MacroNameCollector *MNC = new Callbacks::MacroNameCollector(
            Cpp2C->MacroNames,
            Cpp2C->MultiplyDefinedMacros,
            Cpp2C->MacroDefinitionToTransformedDefinitionPrototypes,
            CI.getSourceManager(),
            CI.getLangOpts(),
            Cpp2CSettings.OnlyCollectNotDefinedInStdHeaders);
        CppSig::MacroForest *MF = new CppSig::MacroForest(CI, Cpp2C->ExpansionRoots);
        PP.addPPCallbacks(unique_ptr<PPCallbacks>(MNC));
        PP.addPPCallbacks(unique_ptr<PPCallbacks>(MF));

        // Return the consumer to initiate the transformation
        return Cpp2C;
    }

    bool TransformerAction::ParseArgs(const CompilerInstance &CI,
                                      const vector<string> &args)
    {
        for (auto it = args.begin(); it != args.end(); ++it)
        {
            std::string arg = *it;
            if (arg == "-ow" || arg == "--overwrite-files")
            {
                Cpp2CSettings.OverwriteFiles = true;
            }
            else if (arg == "-v" || arg == "--verbose")
            {
                Cpp2CSettings.Verbose = true;
            }
            else if (arg == "-u" || arg == "--unify-macros-with-different-names")
            {
                Cpp2CSettings.UnifyMacrosWithSameSignature = true;
            }
            else if (arg == "-shm" || arg == "--standard-header-macros")
            {
                Cpp2CSettings.OnlyCollectNotDefinedInStdHeaders = false;
            }
            else
            {
                llvm::errs() << "Unknown argument: " << arg << '\n';
                exit(-1);
            }
        }
        return true;
    }

    // Necessary for ANYTHING to print to stderr
    PluginASTAction::ActionType TransformerAction::getActionType()
    {
        return ActionType::AddBeforeMainAction;
    }

} // namespace Transformer
