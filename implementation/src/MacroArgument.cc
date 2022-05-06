#include "MacroArgument.hh"

MacroArgument::MacroArgument(const string &Name) : Name(Name) {}

set<const Stmt *> MacroArgument::getStmts()
{
    return Stmts;
}