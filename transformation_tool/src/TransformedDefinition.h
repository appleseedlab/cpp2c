#pragma once

#include "clang/Lex/Lexer.h"

#include "MacroForest.h"

using namespace std;
using namespace clang;

struct TransformedDefinition
{
    // The name of the original macro that this transformation came from
    string OriginalMacroName;
    // Whether this transformation is to a variable or a function
    bool IsVar;
    // The type of the variable we transform to, or the type of the function if we are
    // transforming to a function
    string VarOrReturnType;
    // A vector of the types of the transformed function's arguments
    vector<string> ArgTypes;
    // The body of the transformed definition
    string InitializerOrDefinition;
    // The name used when emitting this definition
    string EmittedName;
};

struct TransformedDefinition NewTransformedDefinition(
    ASTContext *Ctx, MacroForest::Node *Expansion, bool IsVar)
{
    auto &SM = Ctx->getSourceManager();
    auto &LO = Ctx->getLangOpts();

    struct TransformedDefinition TD;
    TD.OriginalMacroName = Expansion->Name;
    TD.IsVar = IsVar;
    assert(Expansion->Stmts.size() == 1);
    TD.VarOrReturnType = getType(Ctx, *(Expansion->Stmts.begin()));
    for (auto &&Arg : Expansion->Arguments)
    {
        // Note that we don't assert that the argument has only one stmt.
        // This is because the argument may have been asserted multiple times.
        string ArgType = getType(Ctx, *(Arg.Stmts.begin()));
        TD.ArgTypes.push_back(ArgType);
    }

    // Generate the transformed body
    SourceLocation MacroBodyBegin =
        Expansion->MI->tokens().front().getLocation();
    SourceLocation MacroBodyEnd =
        Lexer::getLocForEndOfToken(
            Expansion->DefinitionRange.getEnd(), 0, SM, LO);

    SourceRange MacroBodyRange = SourceRange(MacroBodyBegin, MacroBodyEnd);
    CharSourceRange MacroBodyCharRange =
        CharSourceRange::getCharRange(MacroBodyRange);
    string TransformedBody =
        Lexer::getSourceText(MacroBodyCharRange, SM, LO).str();

    string InitializerOrDefinition =
        (IsVar
             ? " = " + TransformedBody + ";"
             : " { return " + TransformedBody + "; }");

    TD.InitializerOrDefinition = InitializerOrDefinition;

    return TD;
}
