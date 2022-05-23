#pragma once

#include "CppSig/MacroExpansionNode.hh"

#include "clang/AST/ASTContext.h"
#include "clang/AST/Type.h"

#include <string>
#include <vector>

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

        // Returns true if the transformed function signature contains a
        // user-defined type
        bool hasNonBuiltinTypes();

        // Returns true if the transformed function signature contains a
        // an array type
        bool hasArrayTypes();

        // Returns true if the transformed function signature contains a function
        // type or function pointer type
        bool hasFunctionTypes();

        // Returns the full types of any structs and unions in the transformed
        // definition's signature as a vector of strings
        std::vector<std::string> getNamesOfStructAndUnionTypesInSignature();

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
