#pragma once

#include "clang/Lex/Lexer.h"

#include "MacroForest.hh"

using namespace std;
using namespace clang;

struct TransformedDefinition
{
    // The original expansion that we are transforming
    MacroForest::Node *Expansion;
    // The name of the original macro that this transformation came from
    string OriginalMacroName;
    // Whether this transformation is to a variable or a function
    bool IsVar;
    // The type of the variable we transform to, or the type of the function if we are
    // transforming to a function
    QualType VarOrReturnType;
    // A vector of the types of the transformed function's arguments
    vector<QualType> ArgTypes;
    // The body of the transformed definition
    string InitializerOrDefinition;
    // The name used when emitting this definition
    string EmittedName;

    // Gets the signature for this transformed expansion if it's a function;
    // otherwise gets the declaration
    string getExpansionSignatureOrDeclaration(ASTContext &Ctx, bool CanBeAnonymous);

    // Returns true if any of the transformed definition's types are
    // user-defined, false otherwise
    bool hasNonBuiltinTypes();

    bool hasArrayTypes();

    bool hasFunctionTypes();
};

struct TransformedDefinition NewTransformedDefinition(
    ASTContext &Ctx,
    MacroForest::Node *Expansion,
    bool IsVar)
{
    struct TransformedDefinition TD;
    TD.Expansion = Expansion;
    TD.OriginalMacroName = Expansion->Name;
    TD.IsVar = IsVar;
    assert(Expansion->Stmts.size() == 1);
    TD.VarOrReturnType = getDesugaredCanonicalType(Ctx, *(Expansion->Stmts.begin()));
    for (auto &&Arg : Expansion->Arguments)
    {
        // Note that we don't assert that the argument has only one stmt.
        // This is because the argument may have been asserted multiple times.
        QualType ArgType = getDesugaredCanonicalType(Ctx, *(Arg.Stmts.begin()));
        TD.ArgTypes.push_back(ArgType);
    }

    // Generate the transformed body
    string TransformedBody = Expansion->DefinitionText;

    string InitializerOrDefinition =
        (IsVar
             ? " = " + TransformedBody + ";"
             : " { return " + TransformedBody + "; }");

    TD.InitializerOrDefinition = InitializerOrDefinition;

    return TD;
}

string TransformedDefinition::getExpansionSignatureOrDeclaration(
    ASTContext &Ctx,
    bool CanBeAnonymous)
{
    assert(expansionHasUnambiguousSignature(Ctx, this->Expansion));
    assert(CanBeAnonymous || this->EmittedName != "");

    // Decls begin with the type of the var/return type of function
    string Signature = this->VarOrReturnType.getAsString();

    if (EmittedName != "")
    {
        Signature += " " + this->EmittedName;
    }

    // If it's not a var, then add formal params
    if (!this->IsVar)
    {
        Signature += "(";
        unsigned i = 0;
        for (auto &&Arg : Expansion->Arguments)
        {
            if (i >= 1)
            {
                Signature += ", ";
            }
            QualType ArgType =
                getDesugaredCanonicalType(Ctx, *(Arg.Stmts.begin()));
            string TString = ArgType.getAsString();
            // NOTE: This doesn't work for function types
            Signature += TString + " " + Arg.Name;
            i += 1;
        }
        Signature += ")";
    }
    return Signature;
}

bool TransformedDefinition::hasNonBuiltinTypes()
{
    if (auto T = this->VarOrReturnType.getTypePtr())
    {
        if (!T->isBuiltinType())
        {
            return true;
        }
    }

    for (auto &&it : this->ArgTypes)
    {
        if (auto T = it.getTypePtr())
        {
            if (!T->isBuiltinType())
            {
                return true;
            }
        }
    }
    return false;
}

bool TransformedDefinition::hasArrayTypes()
{
    if (auto T = this->VarOrReturnType.getTypePtr())
    {
        if (T->isArrayType())
        {
            return true;
        }
    }

    for (auto &&it : this->ArgTypes)
    {
        if (auto T = it.getTypePtr())
        {
            if (T->isArrayType())
            {
                return true;
            }
        }
    }
    return false;
}

bool TransformedDefinition::hasFunctionTypes()
{
    if (auto T = this->VarOrReturnType.getTypePtr())
    {
        if (T->isFunctionPointerType() || T->isFunctionType())
        {
            return true;
        }
    }

    for (auto &&it : this->ArgTypes)
    {
        if (auto T = it.getTypePtr())
        {
            if (T->isFunctionPointerType() || T->isFunctionType())
            {
                return true;
            }
        }
    }
    return false;
}