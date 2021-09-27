'''
inferences.py

Inference functions for inferring more information about macros.
Each inference expects at minimum a list of MacroInferences to infer
more information about.
Some functions require more arguments, e.g., a cursor to the C AST
in which the macro is defined.
Any preconditions for an inference to run correctly are listed in its
function docstring.
Each inference returns a new list of updated MacroInferences.
'''

import dataclasses
import os
import re
from typing import List, Set

from clang.cindex import Index, Token, TokenKind, TranslationUnit

from macro_classifier.macro_classification import MacroClassification
from macro_classifier.macro_inferences import MacroInferences


def infer_macros_used_in_static_conditionals(
        macro_inferences: List[MacroInferences],
        c_files: List[str]) -> List[MacroInferences]:
    '''
    Check whether macros appear in static conditionals in any of a given
    list of c files

    TODO:   Handle macros which appear in multiple files or
            in a file other than the one in which they were defined

    Args:
        macro_inferences:   The list of MacroInference objects to check.
        c_files:            The names of the C files to check for static
                            conditionals in.
    Returns:
        result:             A copy of macro_inferences, with macros
                            who appear in static conditionals updated
                            so that their appears_in_static_conditionals
                            field is set to True. Such macros are also
                            classified as ConfigurationMacros.
    '''

    # Only check macros which have not already been classified
    macros_to_check = [
        mi for mi in macro_inferences if mi.classification is None]
    macro_identifiers_in_static_conditionals: Set[MacroInferences] = set()
    macro_names = [mi.macro_facts.identifier for mi in macros_to_check]

    for c_file in c_files:
        # Create the Clang translation unit for the given C file
        index: Index = Index.create()
        tu: TranslationUnit = index.parse(c_file,
                                          options=TranslationUnit.PARSE_DETAILED_PROCESSING_RECORD)

        # Get the list of all the tokens in the file
        file_len = os.path.getsize(c_file)
        extent = tu.get_extent(c_file, (1, file_len))
        all_tokens = tu.get_tokens(extent=extent)

        # Set up variables for a LL(1) parser
        cur_tok: Token = None
        next_tok: Token = None

        # Methods for advancing and conditionally advancing the parser
        def advance() -> None:
            nonlocal cur_tok, next_tok, all_tokens
            cur_tok, next_tok = next_tok, next(all_tokens, None)

        def accept(kind: TokenKind) -> bool:
            nonlocal cur_tok, next_tok, all_tokens
            if next_tok and next_tok.kind == kind:
                advance()
                return True
            return False

        # Call advance once here to set up the parser
        advance()
        while next_tok:
            if accept(TokenKind.PUNCTUATION):
                # NOTE: This assumes that conditional directives
                #       appear at the start of a line
                if cur_tok.spelling == '#' and cur_tok.location.column == 1:
                    # May have encountered a conditional directive
                    advance()
                    if cur_tok and cur_tok.spelling in ['if', 'ifdef']:
                        static_conditional_line = cur_tok.location.line
                        advance()
                        # Add all macros found on this line to the set of
                        # macros whose names appear in a a static conditional
                        while cur_tok and cur_tok.location.line == static_conditional_line:
                            if (
                                cur_tok.kind == TokenKind.IDENTIFIER
                                and cur_tok.spelling in macro_names
                            ):
                                macro_identifiers_in_static_conditionals.add(
                                    cur_tok.spelling)
                            advance()
            else:
                advance()

    # Copy results into a new list
    result: List[MacroInferences] = [
        dataclasses.replace(mi)
        for mi in macro_inferences
    ]

    # Update new list of MacroInferences
    # This could have been done in the initialization with a list
    # comprehension, but it would be a bit verbose
    for mi in result:
        mi.appears_in_static_conditional = False
        if (mi.macro_facts.identifier in
                macro_identifiers_in_static_conditionals):
            mi.appears_in_static_conditional = True
            mi.classification = MacroClassification.ConfigurationMacro
    return result


def infer_macros_using_stringification(
        macro_inferences: List[MacroInferences]) -> List[MacroInferences]:
    '''
    Checks each macro's body for the the stringification operator '#'

    Args:
        macro_inferences:   The list of MacroInference objects to check.

    Returns:
        result:             A copy of macro_inferences, with each macro
                            whose body contains the stringification operator
                            updated so that their body_contains_stringification
                            field is set to True. Such macros are also
                            classified as StringificationMacros.
    '''

    double_quote_pattern = re.compile(r'\\"|"(?:\\"|[^"])*"|(#)')
    single_quote_pattern = re.compile(r"\\'|'(?:\\'|[^'])*'|(#)")

    result = [dataclasses.replace(mi) for mi in macro_inferences]
    for mi in result:
        mi.body_contains_stringification = False

        dq_search = double_quote_pattern.findall(mi.macro_facts.body)
        if '#' not in dq_search:
            continue

        sq_search = single_quote_pattern.findall(mi.macro_facts.body)
        if '#' not in sq_search:
            continue

        mi.body_contains_stringification = True
        if mi.classification is not None:
            continue

        mi.classification = MacroClassification.StringificationMacro

    return result


def infer_macros_using_token_pasting(
        macro_inferences: List[MacroInferences]) -> List[MacroInferences]:
    '''
    Checks each macro's body for the the token pasting operator '#'

    Args:
        macro_inferences:   The list of MacroInference objects to check.

    Returns:
        result:             A copy of macro_inferences, with each macro
                            whose body contains the token pasting operator
                            updated so that their body_contains_token_pasting
                            field is set to True. Such macros are also
                            classified as TokenPastingMacros.
    '''

    double_quote_pattern = re.compile(r'\\"|"(?:\\"|[^"])*"|(##)')
    single_quote_pattern = re.compile(r"\\'|'(?:\\'|[^'])*'|(##)")

    result = [dataclasses.replace(mi) for mi in macro_inferences]
    for mi in result:
        mi.body_contains_token_pasting = False

        dq_search = double_quote_pattern.findall(mi.macro_facts.body)
        if '##' not in dq_search:
            continue

        sq_search = single_quote_pattern.findall(mi.macro_facts.body)
        if '##' not in sq_search:
            continue

        mi.body_contains_token_pasting = True
        if mi.classification is not None:
            continue

        mi.classification = MacroClassification.TokenPastingMacro

    return result


def infer_variadic_macros(
    macro_inferences: List[MacroInferences]
) -> List[MacroInferences]:
    '''
    Checks each macro's parameter list for '...', and marks those
    that have it as variadic macros

    Args:
        macro_inferences:   The list of MacroInference objects to check

    Returns:
        result:             A copy of macro_inferences, with each macro
                            whose parameters includes '...' updated so
                            that their variadic field is set to True.
                            Such macros are also classified as
                            VariadicMacros.
    '''

    result = [dataclasses.replace(mi) for mi in macro_inferences]

    for mi in result:
        mi.variadic = False
        if '...' in mi.macro_facts.parameters:
            mi.variadic = True
        if mi.classification is not None:
            mi.classification = MacroClassification.VariadicMacro

    return result

