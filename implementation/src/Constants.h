#pragma once

#include <string>
#include <map>

// Headers for dumping transformation stats to CSV
std::string
    TopLevelExpansionsInMainFile = "Total Expansions In Main File",
    TopLevelObjectLikeMacroExpansionsInMainFile = "OLM Expansions",
    TopLevelFunctionLikeMacroExpansionsInMainFile = "FLM Expansions",
    TopLevelExpansionsWithNoExpansionRoot = "No Expansion Root",
    TopLevelExpansionsWithMultipleExpansionRoots = "Multiple Expansion Roots",
    TopLevelExpansionsWithMultipleASTNodes = "Multiple AST Nodes",
    TopLevelExpansionsWithAmbiguousSignature = "Ambiguous Signature",
    TopLevelExpansionsThatDidNotExpandToAnExpression = "Did not Expand to an Expression",
    TopLevelExpansionsWithUnalignedBody = "Unaligned Body",
    TopLevelExpansionsWithExpressionEndNotAtEndOfExpansion = "Expression not Expansion End",
    TopLevelExpansionsOfMultiplyDefinedMacros = "Multiply/Redefined Macro Expansions",
    TopLevelExpansionsWithUnexpandedArgument = "Unexpanded Argument",
    TopLevelExpansionsWithMismatchingArgumentExpansionsAndASTNodes = "Mismatching Argument Expansions and AST Nodes",
    TopLevelExpansionsWithInconsistentArgumentExpansions = "Inconsistent Argument Expansions",
    TopLevelExpansionsWithArgumentsWhoseASTNodesHaveSpellingLocationsNotInArgumentTokenRanges = "Argument AST Nodes have Spelling Locations not in Argument Token Ranges",
    TopLevelExpansionsWithLocalVarsInBody = "Contains Local Vars",
    TopLevelExpansionsWithSideEffects = "Side-effects",
    TransformedTopLevelExpansions = "Total Transformed Expansions",
    TransformedTopLevelObjectLikeMacroExpansions = "Transformed OLM Expansions",
    TransformedTopLevelFunctionLikeMacroExpansions = "Transformed FLM Expansions",
    UntransformedTopLevelExpansions = "Total Untransformed Expansions",
    UntransformedTopLevelObjectLikeMacroExpansions = "Untransformed OLM Expansions",
    UntransformedTopLevelFunctionLikeMacroExpansions = "Untransformed FLM Expansions",
    TopLevelExpansionsContainingGlobalVarDeclaredInMacroInMainFile = "Contains Global Var Declared Inside Macro Inside Main File",
    TransformationTime = "Transformation Time (ms)",
    FileSize = "File Size (bytes)",
    DedupedDefinitions = "Deduped Transformed Definitions",
    EmittedDefinitions = "Emitted Transformed Definitions",
    ConstExprExpansionsFound = "Constant Expression Required",
    TopLevelExpansionsWithAddressOf = "Contains Address Of (&)",
    TopLevelExpansionsContainingGlobalVarsNotDeclaredInDirectlyIncludedFile = "Contains Global Var Not Declared In Directly Included File";

std::map<string, unsigned> NewTransformationStats()
{
    // Map for recording transformation statistics
    string CSVHeaders[] = {
        TopLevelExpansionsInMainFile,
        TopLevelObjectLikeMacroExpansionsInMainFile,
        TopLevelFunctionLikeMacroExpansionsInMainFile,
        TopLevelExpansionsWithNoExpansionRoot,
        TopLevelExpansionsWithMultipleExpansionRoots,
        TopLevelExpansionsWithMultipleASTNodes,
        TopLevelExpansionsWithAmbiguousSignature,
        TopLevelExpansionsThatDidNotExpandToAnExpression,
        TopLevelExpansionsWithUnalignedBody,
        TopLevelExpansionsWithExpressionEndNotAtEndOfExpansion,
        TopLevelExpansionsOfMultiplyDefinedMacros,
        TopLevelExpansionsWithUnexpandedArgument,
        TopLevelExpansionsWithMismatchingArgumentExpansionsAndASTNodes,
        TopLevelExpansionsWithInconsistentArgumentExpansions,
        TopLevelExpansionsWithArgumentsWhoseASTNodesHaveSpellingLocationsNotInArgumentTokenRanges,
        TopLevelExpansionsWithLocalVarsInBody,
        TopLevelExpansionsWithSideEffects,
        TransformedTopLevelExpansions,
        TransformedTopLevelObjectLikeMacroExpansions,
        TransformedTopLevelFunctionLikeMacroExpansions,
        UntransformedTopLevelExpansions,
        UntransformedTopLevelObjectLikeMacroExpansions,
        UntransformedTopLevelFunctionLikeMacroExpansions,
        TopLevelExpansionsContainingGlobalVarDeclaredInMacroInMainFile,
        TransformationTime,
        FileSize,
        DedupedDefinitions,
        EmittedDefinitions,
        ConstExprExpansionsFound,
        TopLevelExpansionsWithAddressOf,
        TopLevelExpansionsContainingGlobalVarsNotDeclaredInDirectlyIncludedFile};

    map<string, unsigned int> Stats;
    for (auto &&Header : CSVHeaders)
    {
        Stats.emplace(Header, 0);
    }
    return Stats;
}