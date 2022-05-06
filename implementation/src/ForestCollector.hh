#pragma once

#include "clang/ASTMatchers/ASTMatchFinder.h"

using namespace clang;

class ForestCollector : public clang::ast_matchers::MatchFinder::MatchCallback
{
    ASTContext &Context;
    std::set<const Stmt *> &Forest;

public:
    ForestCollector(ASTContext &Context, std::set<const Stmt *> &Forest);

    virtual void run(const clang::ast_matchers::MatchFinder::MatchResult &Result) final;
};