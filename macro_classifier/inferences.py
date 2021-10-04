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
from pycparser.c_lexer import CLexer
from pycparser.ply.lex import LexToken, lex

from macro_classifier.macro_classification import MacroClassification
from macro_classifier.macro_inferences import MacroInferences
from macro_fact_collector.macro_facts import MacroKind


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
        macro_inferences:   The list of MacroInference objects to check.

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


def infer_free_variables(
    macro_inferences: List[MacroInferences]
) -> List[MacroInferences]:
    '''
    Infers the list of free variables in a macro's body,
    and updates each macro's mapping of free variables so that
    each free variable is mapped initially to an empty set of strings.

    Args:
        macro_inferences:   The list of MacroInference objects to check.

    Returns:
        result:             A copy of macro_inferences, with each macro's
                            free_variable_identifiers_to_types field
                            updated so that each free variable in the macro's
                            body is mapped to an empty set of strings.
    '''

    result = [dataclasses.replace(mi) for mi in macro_inferences]

    macro_names: Set[str] = {
        mi.macro_facts.identifier for mi in macro_inferences}

    # These functions need to be passed to the CLexer constructor
    # NOTE: Maybe we can use these for something?
    def error_func(msg, line, col):
        pass

    def on_lbrace_func():
        pass

    def on_rbrace_func():
        pass

    def type_lookup_func(type_):
        pass

    for mi in result:
        lexer = CLexer(error_func, on_lbrace_func,
                       on_rbrace_func, type_lookup_func)
        lexer.build()
        lexer.input(mi.macro_facts.body)
        while (token := lexer.token()):
            if not isinstance(token, LexToken):
                continue
            # Only check identifier tokens
            if token.type != 'ID':
                continue
            # Check that identifier is not found in parameters
            if token.value in mi.macro_facts.parameters:
                continue
            # Check that identifier is not actually
            # the name of another macro
            if token.value in macro_names:
                continue

            mi.free_variable_identifiers_to_types[token.value] = set()

    return result


def infer_parameters_used(
    macro_inferences: List[MacroInferences]
) -> List[MacroInferences]:
    '''
    Infers the parameters used in a macro's body,
    and updates each macro's mapping of parameters so that
    each used parameter is mapped initially to an empty set of strings.

    Args:
        macro_inferences:   The list of MacroInference objects to check.

    Returns:
        result:             A copy of macro_inferences, with each macro's
                            parameter_identifiers_to_types field
                            updated so that each parameter used in the macro's
                            body is mapped to an empty set of strings.
                            Those that are not used are mapped to a set of
                            strings containing the string "void *".
    '''

    result = [dataclasses.replace(mi) for mi in macro_inferences]

    # These functions need to be passed to the CLexer constructor
    # NOTE: Maybe we can use these for something?
    def error_func(msg, line, col):
        pass

    def on_lbrace_func():
        pass

    def on_rbrace_func():
        pass

    def type_lookup_func(type_):
        pass

    for mi in result:

        # Initialize all parameters's set of types to {'void *'}
        # in the case they are not used
        for parameter in mi.macro_facts.parameters:
            mi.parameter_identifiers_to_types[parameter] = {'void *'}

        lexer = CLexer(error_func, on_lbrace_func,
                       on_rbrace_func, type_lookup_func)
        lexer.build()
        lexer.input(mi.macro_facts.body)
        while (token := lexer.token()):
            if not isinstance(token, LexToken):
                continue
            # Only check identifier tokens
            if token.type != 'ID':
                continue
            # Check that identifier is found in parameters
            if token.value not in mi.macro_facts.parameters:
                continue

            mi.parameter_identifiers_to_types[token.value] = set()

    return result


def infer_constant_literal_macros(
        macro_inferences: List[MacroInferences]
) -> List[MacroInferences]:
    '''
    Checks each macro to see if its body is composed only of constant literals.
    If so, then the MacroInference object's parsed_type field is updated to the
    parsed type and the macro is classified as either a 
    ConstantExpressionObjectMacro or a ConstantExpressionFunctionMacro.

    Args:
        macro_inferences:   The list of MacroInference objects to check.

    Returns:
        result:             A copy of macro_inferences, with each macro
                            that is a constant updated with their correct
                            inference information.
    '''

    int_patterns = [
        r'''(?P<BINARY_NUMBER>(?:0b|0B)[01]+)''',
        r'''(?P<OCTAL_NUMBER>(?:0)[0-7]+)''',
        r'''(?P<HEX_NUMBER>(?:0x|0X)[0-9a-fA-F]+)''',
        r'''(?P<DEC_NUMBER>(?:\d+))''',
    ]
    int_suffix_patterns = [
        r'''(?P<UNSIGNED_SUFFIX>u|U)''',
        r'''(?P<LONG_SUFFIX>l|L)''',
        r'''(?P<UNSIGNED_LONG_SUFFIX>ul|lu|Ul|lU|uL|Lu|UL|LU)''',
        r'''(?P<LONG_LONG_SUFFIX>l|ll|L|LL)''',
        r'''(?P<UNSIGNED_LONG_LONG_SUFFIX>ull|llu|Ull|llU|uLL|LLu|ULL|LLU)''',
    ]
    int_pattern = f'''^(?:{'|'.join(int_patterns)})(?:{'|'.join(int_suffix_patterns)})?$'''

    double_patterns = [
        r'''(?P<DOUBLE_OPTIONAL_LEADING_DIGIT>(:?\d+)?\.(:?\d+)(:?[eE][+-](:?\d+))?)''',
        r'''(?P<DOUBLE_OPTIONAL_FRACTIONAL>(:?\d+)\.(:?\d+)?(:?[eE][+-](:?\d+))?)''',
    ]
    double_suffix_patterns = [
        r'''(?P<FLOAT_SUFFIX>f|F)''',
        r'''(?P<LONG_DOUBLE_SUFFIX>l|L)'''
    ]
    double_pattern = f'''^(?:{'|'.join(double_patterns)})(?:{'|'.join(double_suffix_patterns)})?$'''

    char_pattern = r'''^(?P<CHAR_PATTERN>[luU]?'(?:[0-9a-zA-Z]|[!"#$%&'()*+,\-./:;<=>?@[\]^_`{|}~ \t\n\r\x0b\x0c]|\\\\)')$'''

    string_pattern = r'''^(?P<STRING_LITERAL>(?P<STRING_PREFIX>u8|L|u|U)?"(?:(?:\\\S)|(?:[0-9a-zA-Z]|[!#$%&'()*+,\-./:;<=>?@[\]^_`{|}~ \t\n\r\x0b\x0c]))*")'''
    string_literal_pattern = re.compile(string_pattern)

    patterns = [
        int_pattern,
        double_pattern,
        char_pattern,
        string_pattern
    ]

    pattern_str = '|'.join(patterns)
    pattern = re.compile(pattern_str)

    result = [dataclasses.replace(mi) for mi in macro_inferences]

    for mi in result:
        body = mi.macro_facts.body.strip()
        if (m := pattern.match(body)):
            groups = m.groupdict()

            if (groups['BINARY_NUMBER'] or
                    groups['OCTAL_NUMBER'] or
                    groups['HEX_NUMBER'] or
                    groups['DEC_NUMBER']
                ):
                mi.parsed_type = 'int'
                if groups['UNSIGNED_SUFFIX']:
                    mi.parsed_type = 'unsigned'
                elif groups['LONG_SUFFIX']:
                    mi.parsed_type = 'long'
                elif groups['UNSIGNED_LONG_SUFFIX']:
                    mi.parsed_type = 'unsigned long'
                elif groups['LONG_LONG_SUFFIX']:
                    mi.parsed_type = 'long long'

            if (groups['DOUBLE_OPTIONAL_LEADING_DIGIT'] or
                    groups['DOUBLE_OPTIONAL_FRACTIONAL']
                ):
                mi.parsed_type = 'double'
                if groups['FLOAT_SUFFIX']:
                    mi.parsed_type = 'float'
                elif groups['LONG_DOUBLE_SUFFIX']:
                    mi.parsed_type = 'long double'

            if groups['CHAR_PATTERN']:
                mi.parsed_type = 'char'

            if groups['STRING_LITERAL']:
                while string_literal_pattern.match(body):
                    # Check if valid compound string
                    body = string_literal_pattern.sub('', body)
                    body = body.lstrip()
                if not body:
                    mi.parsed_type = 'char *'
                else:
                    # If the body is not a well-formed string, the macro cannot
                    # be converted
                    mi.classification = MacroClassification.InconvertibleTypeExpressionObjectMacro

            # Only classify macros that weren't previously classified as
            # inconvertible
            if mi.classification is None:
                if mi.macro_facts.kind == MacroKind.ObjectLike:
                    mi.classification = MacroClassification.ConstantExpressionObjectMacro
                elif mi.macro_facts.kind == MacroKind.FunctionLike:
                    mi.classification = MacroClassification.ConstantExpressionFunctionMacro

    return result
