#pragma once

#include <vector>

#include "clang/Basic/SourceLocation.h"

#include "llvm/Support/raw_ostream.h"

using namespace std;
using namespace clang;

// Vector of SourceRanges objects
class SourceRangeCollection : public vector<SourceRange>
{
public:
    // Returns true if one of the ranges in this vector of source ranges
    // contains Loc, false otherwise
    bool contains(const SourceLocation &Loc) const;

    // Dumps all the ranges in the vector to llvm::errs()
    void dump(SourceManager &SM);
};