#pragma once

#include "MacroForest.h"

using namespace std;
using namespace clang;

struct TransformedDefinition
{
    // The name of the file that the original macro was defined in
    string SourceFileName;
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
    string Body;
    // The name used when emitting this definition
    string EmittedName;
};

struct TransformedDefinition NewTransformedDefinition(
    ASTContext *Ctx, MacroForest::Node *Expansion, bool IsVar)
{
    auto &SM = Ctx->getSourceManager();

    struct TransformedDefinition TD;
    TD.SourceFileName =
        SM.getFilename(Expansion->SpellingRange.getBegin()).str();
    TD.OriginalMacroName = Expansion->Name;
    TD.IsVar = IsVar;
    // TODO: Finish

    return TD;
}
