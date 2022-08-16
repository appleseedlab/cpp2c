#pragma once

#include "clang/Basic/FileManager.h"
#include "clang/Basic/LLVM.h"
#include "clang/Basic/Module.h"
#include "clang/Basic/SourceLocation.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Lex/PPCallbacks.h"
#include "clang/Lex/Token.h"

#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/Optional.h"

#include <vector>

namespace Callbacks
{
    class IncludeCollector : public clang::PPCallbacks
    {
    private:
        std::map<clang::SourceLocation, std::string> &IncludeLocToFileRealPath;

    public:

        IncludeCollector(
            std::map<clang::SourceLocation, std::string>
            &IncludeLocToFileRealPath);

        void InclusionDirective (
            clang::SourceLocation HashLoc,
            const clang::Token &IncludeTok,
            llvm::StringRef FileName,
            bool IsAngled,
            clang::CharSourceRange FilenameRange,
            llvm::Optional<clang::FileEntryRef> File,
            llvm::StringRef SearchPath,
            llvm::StringRef RelativePath,
            const clang::Module *Imported,
            clang::SrcMgr::CharacteristicKind FileType);
    };
} // namespace Callbacks
