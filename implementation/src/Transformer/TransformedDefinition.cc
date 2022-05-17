#include "Utils/ExpansionUtils.hh"
#include "Transformer/TransformedDefinition.hh"

namespace Transformer
{
    using clang::ASTContext;
    using clang::dyn_cast_or_null;
    using clang::Expr;
    using clang::QualType;
    using clang::Stmt;
    using CppSig::MacroExpansionNode;
    using std::string;
    using Utils::containsFunctionCalls;
    using Utils::containsGlobalVars;
    using Utils::expansionHasUnambiguousSignature;
    using Utils::getDesugaredCanonicalType;
    using Utils::transformsToVar;

    TransformedDefinition::TransformedDefinition(
        ASTContext &Ctx,
        MacroExpansionNode *Expansion)
    {
        this->Expansion = Expansion;
        this->OriginalMacroName = Expansion->getName();
        assert(Expansion->getStmts().size() == 1);

        this->IsVar = transformsToVar(this->Expansion, Ctx);
        this->VarOrReturnType = getDesugaredCanonicalType(Ctx, *(Expansion->getStmts().begin()));
        for (auto &&Arg : Expansion->getArguments())
        {
            // Note that we don't assert that the argument has only one stmt.
            // This is because the argument may have been asserted multiple times.
            QualType ArgType = getDesugaredCanonicalType(Ctx, *(Arg.getStmts().begin()));
            this->ArgTypes.push_back(ArgType);
        }

        // Generate the transformed body
        string TransformedBody = Expansion->getDefinitionText();

        string InitializerOrDefinition =
            (this->IsVar
                 ? " = " + TransformedBody + ";"
                 : " { return " + TransformedBody + "; }");

        this->InitializerOrDefinition = InitializerOrDefinition;
    }

    string TransformedDefinition::getEmittedName() { return EmittedName; }
    MacroExpansionNode *TransformedDefinition::getExpansion() { return Expansion; }

    std::string TransformedDefinition::getExpansionSignatureOrDeclaration(
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
            for (auto &&Arg : Expansion->getArguments())
            {
                if (i >= 1)
                {
                    Signature += ", ";
                }
                QualType ArgType =
                    getDesugaredCanonicalType(Ctx, *(Arg.getStmts().begin()));
                string TString = ArgType.getAsString();
                // NOTE: This doesn't work for function types
                Signature += TString + " " + Arg.getName();
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
} // namespace Transformer