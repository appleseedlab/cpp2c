#include "ExpansionUtils.hh"
#include "TransformedDefinition.hh"

using namespace clang;

TransformedDefinition::TransformedDefinition(
    ASTContext &Ctx,
    MacroExpansionNode *Expansion,
    bool IsVar)
{
    this->Expansion = Expansion;
    this->OriginalMacroName = Expansion->Name;
    this->IsVar = IsVar;
    assert(Expansion->Stmts.size() == 1);
    this->VarOrReturnType = getDesugaredCanonicalType(Ctx, *(Expansion->Stmts.begin()));
    for (auto &&Arg : Expansion->Arguments)
    {
        // Note that we don't assert that the argument has only one stmt.
        // This is because the argument may have been asserted multiple times.
        QualType ArgType = getDesugaredCanonicalType(Ctx, *(Arg.Stmts.begin()));
        this->ArgTypes.push_back(ArgType);
    }

    // Generate the transformed body
    string TransformedBody = Expansion->DefinitionText;

    string InitializerOrDefinition =
        (IsVar
             ? " = " + TransformedBody + ";"
             : " { return " + TransformedBody + "; }");

    this->InitializerOrDefinition = InitializerOrDefinition;
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