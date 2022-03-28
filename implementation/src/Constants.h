#pragma once

#include <string>
#include <map>

// Headers for dumping transformation stats to CSV
std::string
    TopLevelExpansionsInMainFile = "Top Level Expansions In Main File",
    TopLevelObjectLikeMacroExpansionsInMainFile = "Top Level Object-like Macro Expansions Found",
    TopLevelFunctionLikeMacroExpansionsInMainFile = "Top Level Function-like Macro Expansions Found",
    TopLevelExpansionsWithNoExpansionRoot = "Top Level Expanions with No Expansion Root",
    TopLevelExpansionsWithMultipleExpansionRoots = "Top Level Expansions with Multiple Expansion Roots",
    TopLevelExpansionsWithMultipleASTNodes = "Top Level Expansions with Multiple AST Nodes",
    TopLevelExpansionsWithAmbiguousSignature = "Top Level Expansions with an Ambiguous Signature",
    TopLevelExpansionsThatDidNotExpandToAnExpression = "Top Level Expansions that did not Expand to an Expression",
    TopLevelExpansionsWithUnalignedBody = "Top Level Expansions with an Unaligned Body",
    TopLevelExpansionsWithExpressionEndNotAtEndOfExpansion = "Top Level Expansions with an Expression that did not End at the End of the Expansion",
    TopLevelExpansionsOfMultiplyDefinedMacros = "Top Level Expansions of Multiply Defined (or Redefined) Macros",
    TopLevelExpanionsWithUnexpandedArgument = "Top Level Expansions with an Unexpanded Argument",
    TopLevelExpansionsWithMismatchingArgumentExpansionsAndASTNodes = "Top Level Expansions with Mismatching Argument Expansions and AST Nodes",
    TopLevelExpansionsWithInconsistentArgumentExpansions = "Top Level Expansions with Inconsistent Argument Expansions",
    TopLevelExpansionsWithArgumentsWhoseASTNodesHaveSpellingLocationsNotInArgumentTokenRanges = "Top Level Expansions with Arguments whose AST Nodes have Spelling Locations not in Argument Token Rages",
    TopLevelExpansionsWithLocalVars = "Top Level Expansions with Local Vars",
    TopLevelExpansionsWithSideEffects = "Top Level Expansions with Side-effects",
    TransformedTopLevelExpansions = "Successfully Transformed Top Level Expansions",
    TransformedTopLevelObjectLikeMacroExpansions = "Successfully Transformed Top Level Object-like Macro Expansions",
    TransformedTopLevelFunctionLikeMacroExpansions = "Successfully Transformed Top Level Function-like Macro Expansions",
    UntransformedTopLevelExpansions = "Top Level Expansions not Transformed",
    UntransformedTopLevelObjectLikeMacroExpansions = "Top Level Object-like Expansions not Transformed",
    UntransformedTopLevelFunctionLikeMacroExpansions = "Top Level Function-like Expansions not Transformed",
    TopLevelExpanionsWithTransformationsNotInMainFile = "Top Level Expansions with Transformations Not In Main File (not transformed)",
    TransformationTime = "Transformation Time (ms)",
    FileSize = "File Size (bytes)",
    DedupedDefinitions = "Deduped Transformed Definitions",
    EmittedDefinitions = "Emitted Transformed Definitions",
    ConstExprExpansionsFound = "Top Level Expansions to Constant Expressions";

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
        TopLevelExpanionsWithUnexpandedArgument,
        TopLevelExpansionsWithMismatchingArgumentExpansionsAndASTNodes,
        TopLevelExpansionsWithInconsistentArgumentExpansions,
        TopLevelExpansionsWithArgumentsWhoseASTNodesHaveSpellingLocationsNotInArgumentTokenRanges,
        TopLevelExpansionsWithLocalVars,
        TopLevelExpansionsWithSideEffects,
        TransformedTopLevelExpansions,
        TransformedTopLevelObjectLikeMacroExpansions,
        TransformedTopLevelFunctionLikeMacroExpansions,
        UntransformedTopLevelExpansions,
        UntransformedTopLevelObjectLikeMacroExpansions,
        UntransformedTopLevelFunctionLikeMacroExpansions,
        TopLevelExpanionsWithTransformationsNotInMainFile,
        TransformationTime,
        FileSize,
        DedupedDefinitions,
        EmittedDefinitions,
        ConstExprExpansionsFound};

    map<string, unsigned int> Stats;
    for (auto &&Header : CSVHeaders)
    {
        Stats.emplace(Header, 0);
    }
    return Stats;
}