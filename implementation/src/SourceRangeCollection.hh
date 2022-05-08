#pragma once

#include "clang/Basic/SourceLocation.h"

#include <vector>

// Vector of SourceRanges objects
class SourceRangeCollection : public std::vector<clang::SourceRange>
{
public:
    // Returns true if one of the ranges in this vector of source ranges
    // contains Loc, false otherwise
    bool contains(const clang::SourceLocation &Loc) const;

    // Dumps all the ranges in the vector to llvm::errs()
    void dump(clang::SourceManager &SM);
};