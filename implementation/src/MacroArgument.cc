#include "MacroArgument.hh"

using clang::Stmt;
using std::set;
using std::string;

MacroArgument::MacroArgument(const string &Name) : Name(Name) {}

set<const Stmt *> MacroArgument::getStmts()
{
    return Stmts;
}