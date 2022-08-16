#include "Callbacks/IncludeCollector.hh"

namespace Callbacks
{
    IncludeCollector::IncludeCollector(
        std::map<clang::SourceLocation, std::string>
        &IncludeLocToFileRealPath)
        : IncludeLocToFileRealPath(IncludeLocToFileRealPath){};

    void IncludeCollector::InclusionDirective (
        clang::SourceLocation HashLoc,
        const clang::Token &IncludeTok,
        llvm::StringRef FileName,
        bool IsAngled,
        clang::CharSourceRange FilenameRange,
        llvm::Optional<clang::FileEntryRef> File,
        llvm::StringRef SearchPath,
        llvm::StringRef RelativePath,
        const clang::Module *Imported,
        clang::SrcMgr::CharacteristicKind FileType)
        {
            if (File.hasValue())
            {
                std::string FileRealPath = File
                                           .getValue()
                                           .getFileEntry()
                                           .tryGetRealPathName()
                                           .str();
                IncludeLocToFileRealPath[HashLoc] = FileRealPath;
            }
        }
} // namespace Callbacks
