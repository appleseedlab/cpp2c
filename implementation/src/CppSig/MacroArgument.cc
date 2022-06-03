#include "CppSig/MacroArgument.hh"

using clang::Stmt;
using std::set;
using std::string;

namespace CppSig
{
    MacroArgument::MacroArgument(const string &Name) : Name(Name) {}

    set<const Stmt *> MacroArgument::getStmts()
    {
        return Stmts;
    }

    set<const Stmt *> &MacroArgument::getStmtsRef()
    {
        return Stmts;
    }

    Utils::SourceRangeCollection MacroArgument::getTokenRanges()
    {
        return TokenRanges;
    }

    Utils::SourceRangeCollection *MacroArgument::getTokenRangesPtr()
    {
        return &TokenRanges;
    }

    Utils::SourceRangeCollection &MacroArgument::getTokenRangesRef()
    {
        return TokenRanges;
    }

    string MacroArgument::getName()
    {
        return Name;
    }

    string MacroArgument::getRawText()
    {
        return RawText;
    }
} // namespace Cppsig