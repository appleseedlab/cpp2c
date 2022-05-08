// Taken from Dietrich

#include "ForestCollector.hh"

using clang::ASTContext;
using clang::Stmt;
using clang::TypeLoc;

ForestCollector::ForestCollector(ASTContext &Context, std::set<const Stmt *> &Forest)
    : Context(Context), Forest(Forest){};

void ForestCollector::run(const clang::ast_matchers::MatchFinder::MatchResult &Result)
{
    const auto *E = Result.Nodes.getNodeAs<Stmt>("stmt");
    assert(E != nullptr);

    // Have we already recorded a Parent statement? => Skip this one
    const Stmt *ParentStmt = E;
    while (ParentStmt)
    {
        const auto &Parents = Context.getParents(*ParentStmt);
        // FIXME: This happens from time to time
        if (Parents.size() > 1)
        {
            // E->getBeginLoc().dump(Context.getSourceManager());
            // E->dump();
            return;
        }
        assert(Parents.size() <= 1); // C++?

        if (Parents.size() == 0)
        {
            break;
        }

        if (const Stmt *S = Parents[0].get<Stmt>())
        {
            if (Forest.find(S) != Forest.end())
            {
                return;
            }
            ParentStmt = S;
        }
        else if (const TypeLoc *TL = Parents[0].get<TypeLoc>())
        {
            (void)TL;
            return; // WE DO NOT COLLECT NODES BELOW TypeLoc
        }
        else
        {
            // Parent is not a stmt -> break
            // llvm::errs() << "UNKNOWN?\n";
            // auto &Parent = Parents[0];
            // Parent.dump(llvm::errs(), Context);
            // abort();
            break;
        }
    }

    Forest.insert(E);
}