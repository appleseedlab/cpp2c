#include "SourceRangeCollection.hh"

bool SourceRangeCollection::contains(const SourceLocation &Loc) const
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

void SourceRangeCollection::dump(SourceManager &SM)
{
    for (const auto &Range : *this)
    {
        Range.print(llvm::errs(), SM);
        llvm::errs() << ", ";
    }
}