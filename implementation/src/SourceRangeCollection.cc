#include "SourceRangeCollection.hh"

#include "llvm/Support/raw_ostream.h"

bool SourceRangeCollection::contains(const clang::SourceLocation &Loc) const
{
    for (const auto &Range : *this)
    {
        if (Range.getBegin() <= Loc && Loc <= Range.getEnd())
        {
            return true;
        }
    }
    return false;
}

void SourceRangeCollection::dump(clang::SourceManager &SM)
{
    for (const auto &Range : *this)
    {
        Range.print(llvm::errs(), SM);
        llvm::errs() << ", ";
    }
}