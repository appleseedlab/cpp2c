#include "Transformer/TransformerAction.hh"
#include "Transformer/TransformerConsumer.hh"

namespace Transformer
{
    using namespace std;
    using namespace clang;

    unique_ptr<ASTConsumer>
    TransformerAction::CreateASTConsumer(
        CompilerInstance &CI,
        StringRef file)
    {
        unique_ptr<TransformerConsumer> Transformer = make_unique<TransformerConsumer>(&CI, TSettings);

        // Return the consumer to initiate the transformation
        return Transformer;
    }

    bool TransformerAction::ParseArgs(const CompilerInstance &CI,
                                      const vector<string> &args)
    {
        for (auto it = args.begin(); it != args.end(); ++it)
        {
            std::string arg = *it;
            if (arg == "-ow" || arg == "--overwrite-files")
            {
                TSettings.OverwriteFiles = true;
            }
            else if (arg == "-v" || arg == "--verbose")
            {
                TSettings.Verbose = true;
            }
            else if (arg == "-shm" || arg == "--standard-header-macros")
            {
                TSettings.OnlyCollectNotDefinedInStdHeaders = false;
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
