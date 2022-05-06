// A Matcher callback, that collects all AST Nodes that were matched
// and bound to BindName
// Note: Template classes and functions must be declared in header files:
// https://www.cplusplus.com/doc/oldtutorial/templates/

#pragma once

template <typename T>
class NodeCollector : public clang::ast_matchers::MatchFinder::MatchCallback
{
    std::string BindName;
    std::vector<const T *> &Nodes;

public:
    NodeCollector(std::string BindName, std::vector<const T *> &Nodes)
        : BindName(BindName), Nodes(Nodes){};

    void run(const clang::ast_matchers::MatchFinder::MatchResult &Result) final
    {
        const auto *E = Result.Nodes.getNodeAs<T>(BindName);
        if (E)
        {
            Nodes.push_back(E);
        }
    }
};