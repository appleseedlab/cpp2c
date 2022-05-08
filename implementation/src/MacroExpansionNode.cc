#include "MacroExpansionNode.hh"

using clang::MacroInfo;
using clang::SourceManager;
using clang::SourceRange;
using clang::Stmt;
using llvm::errs;
using std::set;
using std::string;
using std::vector;

void MacroExpansionNode::dump(SourceManager &SM)
{
    errs() << "Node " << Name << " argc: "
           << Arguments.size() << " nesting: "
           << NestingLevel << '\n';
    dumpRange<SourceRange>(SM, "DefinitionRange: ", DefinitionRange);
    dumpRange(SM, "SpellingRange: ", SpellingRange);
    for (auto &Arg : Arguments)
    {
        dumpRange(SM, Arg.Name + " = ", Arg.TokenRanges);
        errs() << '\n';
    }
}

void MacroExpansionNode::dump_tree(unsigned depth = 0) const
{
    // Indent "depth" number of spaces
    for (unsigned i = 0; i < depth; i++)
    {
        errs() << " ";
    }
    if (depth > 0)
    {
        errs() << "`- ";
    }
    errs() << "Expansion " << Name
           << " argc: " << Arguments.size()
           << " nesting: " << NestingLevel << '\n';

    // Dump children at 1 more indentation level
    for (const auto &Child : Children)
        Child->dump_tree(depth + 1);
}

MacroExpansionNode *MacroExpansionNode::getRoot()
{
    return Root;
}

MacroExpansionNode *MacroExpansionNode::getParent()
{
    return Parent;
}

string MacroExpansionNode::getName()
{
    return Name;
}
vector<MacroArgument> MacroExpansionNode::getArguments()
{
    return Arguments;
}

SourceRange MacroExpansionNode::getDefinitionRange()
{
    return DefinitionRange;
}

SourceRange MacroExpansionNode::getSpellingRange()
{
    return SpellingRange;
}

SourceRangeCollection MacroExpansionNode::getArgSpellingLocs()
{
    return ArgSpellingLocs;
}

MacroInfo *MacroExpansionNode::getMI()
{
    return MI;
}

set<const Stmt *> MacroExpansionNode::getStmts()
{
    return Stmts;
}