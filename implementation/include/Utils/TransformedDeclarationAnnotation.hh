#pragma once

#include "nlohmann/single_include/json.hpp"

#include "clang/AST/ASTContext.h"
#include "clang/AST/Attr.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Rewrite/Core/Rewriter.h"

#include <string>
#include <stddef.h>

namespace Utils
{
    // Struct representing annotations of transformed declarations.
    // We use a struct instead of a class here because this struct is shared
    // by many parts of Cpp2C, structs have public access by default, and
    // the main purpose of this type is to organize data
    struct TransformedDeclarationAnnotation
    {
        // Name of the original macro that this transformed declaration
        // came from
        std::string NameOfOriginalMacro;

        // Should either be <object-like> or <function-like>
        std::string MacroType;

        // Real path to the file in which the original macro was defined
        std::string MacroDefinitionRealPath;

        // Definition number of the original macro
        std::size_t MacroDefinitionNumber;

        // Real path to the file the transformed declaration's
        // corresponding definition was emitted to
        std::string TransformedDefinitionRealPath;

        // The signature of the transformed delcaration, without
        // the name of the variable/function itself
        std::string TransformedSignature;
    };

    // Functions for serializing/deserializing to/from JSON
    // See https://github.com/nlohmann/json#basic-usage
    void to_json(
        nlohmann::json &j,
        const TransformedDeclarationAnnotation &TDA);
    void from_json(
        const nlohmann::json &j,
        TransformedDeclarationAnnotation &TDA);

    // This enables us to wrap the emitted JSON string in another string
    // https://stackoverflow.com/questions/7724448/simple-json-string-escape-for-c
    std::string escape_json(const std::string &s);

    // Hashes the original macro that a TransformedDeclarationAnnotation was
    // transformed from to a string
    std::string hashTDAOriginalMacro(const TransformedDeclarationAnnotation &TDA);

    // Hashes a given TransformedDeclarationAnnotation instance to a string
    std::string hashTDA(const TransformedDeclarationAnnotation &TDA);

    // Hashes a given TransformedDeclarationAnnotation JSON annotation to a string
    std::string hashTDAFromJSON(const nlohmann::json &j);

    // Given a pointer to a Decl, returns the string representation of
    // the Decl's first 'annotate' attribute, or the empty string
    // if it doesn't have one
    std::string getFirstAnnotationOrEmpty(clang::Decl *);

    // Given an entire annotation string, extracts the braced portion of the
    // string, parses it to JSON, and the returns the parsed value
    nlohmann::json annotationStringToJson(std::string anno);

} // namespace Utils
