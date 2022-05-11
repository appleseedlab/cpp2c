#include "CppSig/MacroExpansionNode.hh"

namespace CppSig
{
    using clang::MacroInfo;
    using clang::SourceManager;
    using clang::SourceRange;
    using clang::Stmt;
    using llvm::errs;
    using std::set;
    using std::string;
    using std::vector;

    MacroExpansionNode::~MacroExpansionNode()
    {
        for (auto &&it : SubtreeNodes)
        {
            delete it;
        }
    }

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

    vector<MacroExpansionNode *> MacroExpansionNode::getSubtreeNodes()
    {
        return SubtreeNodes;
    }

    vector<MacroExpansionNode *> &MacroExpansionNode::getSubtreeNodesRef()
    {
        return SubtreeNodes;
    }

    string MacroExpansionNode::getName()
    {
        return Name;
    }

    string MacroExpansionNode::getDefinitionText()
    {
        return DefinitionText;
    }

    vector<MacroArgument> MacroExpansionNode::getArguments()
    {
        return Arguments;
    }

    vector<MacroArgument> &MacroExpansionNode::getArgumentsRef()
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

    Utils::SourceRangeCollection MacroExpansionNode::getArgSpellingLocs()
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

    set<const Stmt *> &MacroExpansionNode::getStmtsRef()
    {
        return Stmts;
    }
} // namespace CppSig
