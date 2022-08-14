#pragma once

#include "CppSig/MacroExpansionNode.hh"

#include "clang/AST/ASTContext.h"
#include "clang/AST/Type.h"

#include <string>
#include <vector>
#include <functional>

namespace Transformer
{
    class TransformedDefinition
    {
        friend class TransformerConsumer;

        // The original expansion that we are transforming
        CppSig::MacroExpansionNode *Expansion;
        // The name of the original macro that this transformation came from
        std::string OriginalMacroName;
        // Whether this transformation is to a variable or a function
        bool IsVar;
        // The type of the variable we transform to, or the return type of the
        // function if we are transforming to a function
        clang::QualType VarOrReturnType;
        // A vector of the types of the transformed function's arguments
        std::vector<clang::QualType> ArgTypes;
        // The body of the transformed definition
        std::string InitializerOrDefinition;
        // The name used when emitting this definition
        std::string EmittedName;

    public:
        TransformedDefinition(
            clang::ASTContext &Ctx,
            CppSig::MacroExpansionNode *Expansion);

        std::string getEmittedName();
        void setEmittedName(std::string s);
        CppSig::MacroExpansionNode *getExpansion();

        // Gets the signature for this transformed expansion if it's a function;
        // otherwise gets the declaration
        std::string getExpansionSignatureOrDeclaration(
            clang::ASTContext &Ctx,
            bool includeEmittedName);

        // gets all the types in the transformed definition's signature
        std::vector<clang::QualType> getTypesInSignature();

        // Checks if the given predicate holds for any of the types
        // in the transformed definition's type signature.
        bool inTypeSignature(std::function<bool(const clang::Type *T)> pred);

        // Returns the full types of any structs/unions/enums in the
        // transformed definition's signature as a QualType vector
        std::vector<clang::QualType> getStructUnionEnumTypesInSignature();

        // Returns the location that the transformed declaration of this macro
        // should be emitted to
        clang::SourceLocation getTransformedDeclarationLocation(clang::ASTContext &Ctx);

        // Returns the location that the transformed definition of this macro
        // should be emitted to
        clang::SourceLocation getTransformedDefinitionLocation(clang::ASTContext &Ctx);

        // Returns the range that the transformed invocation of this macro
        // should replace
        clang::SourceRange getInvocationReplacementRange();
    };
}
