#pragma once

#include "clang/ASTMatchers/ASTMatchFinder.h"

namespace Callbacks
{
    class ForestCollector : public clang::ast_matchers::MatchFinder::MatchCallback
    {
        clang::ASTContext &Context;
        std::set<const clang::Stmt *> &Forest;

    public:
        ForestCollector(clang::ASTContext &Context, std::set<const clang::Stmt *> &Forest);

        virtual void run(const clang::ast_matchers::MatchFinder::MatchResult &Result) final;
    };
} // namespace Callbacks