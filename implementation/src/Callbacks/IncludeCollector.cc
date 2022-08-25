#include "Callbacks/IncludeCollector.hh"

namespace Callbacks
{
    IncludeCollector::IncludeCollector(
        std::map<clang::SourceLocation, std::string>
        &IncludeLocToFileRealPath)
        : IncludeLocToFileRealPath(IncludeLocToFileRealPath){};

    void IncludeCollector::InclusionDirective(
        clang::SourceLocation HashLoc,
        const clang::Token &IncludeTok,
        llvm::StringRef FileName,
        bool IsAngled,
        clang::CharSourceRange FilenameRange,
        const clang::FileEntry *File,
        llvm::StringRef SearchPath,
        llvm::StringRef RelativePath,
        const clang::Module *Imported,
        clang::SrcMgr::CharacteristicKind FileType)
        {
            if (File)
            {
                std::string FileRealPath = File
                                           ->tryGetRealPathName()
                                           .str();
                llvm::errs() << "Visiting include of " << FileRealPath << "\n";
                IncludeLocToFileRealPath[HashLoc] = FileRealPath;
            }
        }
} // namespace Callbacks
