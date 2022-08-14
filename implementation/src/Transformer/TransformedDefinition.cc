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
    using Utils::getFunctionDeclStmtExpandedIn;
    using Utils::getPointeeType;
    using Utils::transformsToVar;

    TransformedDefinition::TransformedDefinition(
        ASTContext &Ctx,
        MacroExpansionNode *Expansion)
        : Expansion(Expansion),
          OriginalMacroName(Expansion->getName()),
          IsVar(transformsToVar(Expansion, Ctx)),
          VarOrReturnType(getDesugaredCanonicalType(Ctx, *(Expansion->getStmts().begin())))
    {
        for (auto &&Arg : Expansion->getArguments())
        {
            // Note that we don't assert that the argument has only one stmt.
            // This is because the argument may have been expanded multiple times.
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
    void TransformedDefinition::setEmittedName(string s) { EmittedName = s; }
    MacroExpansionNode *TransformedDefinition::getExpansion() { return Expansion; }

    std::string TransformedDefinition::getExpansionSignatureOrDeclaration(
        ASTContext &Ctx,
        bool includeEmittedName)
    {
        assert(expansionHasUnambiguousSignature(Ctx, Expansion));

        // Decls begin with the type of the var/return type of function
        string Signature = "";

        // Check if return type is a struct/union/enum
        {
            // TODO: Maybe we should remove const here as well?
            QualType ReturnTypePointeeType = getPointeeType(VarOrReturnType);
            auto RTPT = ReturnTypePointeeType.getTypePtr();
            string TString = VarOrReturnType.getAsString();
            // Add struct/union/enum before type name if not present
            if (RTPT->isStructureType() &&
                TString.find("struct") == string::npos)
            {
                TString = "struct " + TString;
            }
            else if (RTPT->isUnionType() &&
                     TString.find("union") == string::npos)
            {
                TString = "union " + TString;
            }
            else if (RTPT->isEnumeralType() &&
                     TString.find("enum") == string::npos)
            {
                TString = "enum " + TString;
            }

            Signature = TString;
        }

        if (includeEmittedName)
        {
            Signature += " " + EmittedName;
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
                auto ST = *(Arg.getStmts().begin());
                QualType ArgType = getDesugaredCanonicalType(Ctx, ST);
                string TString = ArgType.getAsString();

                // TODO: This is a hack
                // Manually remove const qualifiers from parameters only
                // We make sure we only remove from parameters by including
                // the space after the const keyword
                {
                    auto i = TString.find("const ");
                    if (i != string::npos)
                    {
                        TString.erase(i, string("const ").length());
                    }
                }

                QualType ArgPointeeType = getPointeeType(ArgType);
                auto APTP = ArgPointeeType.getTypePtr();
                // Add struct/union/enum before type name if not present
                if (APTP->isStructureType() &&
                    TString.find("struct") == string::npos)
                {
                    TString = "struct " + TString;
                }
                else if (APTP->isUnionType() &&
                         TString.find("union") == string::npos)
                {
                    TString = "union " + TString;
                }
                else if (APTP->isEnumeralType() &&
                         TString.find("enum") == string::npos)
                {
                    TString = "enum " + TString;
                }
                // NOTE: This doesn't work for function types
                Signature += TString + " " + Arg.getName();
                i += 1;
            }
            Signature += ")";
        }
        return Signature;
    }

    bool TransformedDefinition::inTypeSignature(
        std::function<bool(clang::QualType)> pred)
    {
        if (pred(this->VarOrReturnType)) {
            return true;
        }
        for (clang::QualType it : this->ArgTypes) {
            if (pred(it)) {
                return true;
            }
        }
        return false;
    }

    std::vector<QualType> TransformedDefinition::getStructUnionEnumTypesInSignature()
    {
        std::vector<QualType> typesToCheck;
        typesToCheck.push_back(this->VarOrReturnType);
        typesToCheck.insert(typesToCheck.end(), this->ArgTypes.begin(), this->ArgTypes.end());

        std::vector<QualType> result;

        for (auto &&it : typesToCheck)
        {
            auto PointeeType = getPointeeType(it);
            if (PointeeType->isStructureType() ||
                PointeeType->isUnionType() ||
                PointeeType->isEnumeralType())
            {
                result.push_back(PointeeType);
            }
        }

        return result;
    }

    clang::SourceLocation TransformedDefinition::getTransformedDeclarationLocation(ASTContext &Ctx)
    {
        auto &SM = Ctx.getSourceManager();
        auto DefinitionSpellingLoc = SM.getSpellingLoc(Expansion->getMI()->getDefinitionLoc());
        return SM.getLocForStartOfFile(SM.getFileID(DefinitionSpellingLoc));
    }

    clang::SourceLocation TransformedDefinition::getTransformedDefinitionLocation(ASTContext &Ctx)
    {
        auto &SM = Ctx.getSourceManager();
        auto FD = getFunctionDeclStmtExpandedIn(Ctx, *Expansion->getStmtsRef().begin());
        assert(FD != nullptr && "Containing function definition is null");
        return SM.getExpansionLoc(FD->getBeginLoc());
    }

    clang::SourceRange TransformedDefinition::getInvocationReplacementRange()
    {
        return Expansion->getSpellingRange();
    }

} // namespace Transformer