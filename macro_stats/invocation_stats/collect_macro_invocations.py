'''collect_macro_invocations.py

Collects data on macro invocations in a given C file
and writes the results to a CSV file.
'''

from typing import Dict, Literal, Set

import begin
from clang import cindex as ci

# TODO: Make sure that multiply-defined macros are treated properly when
#       recording invocations stats
# NOTE: For now we assume that if a macro contains comments,
#       the comments will only appear at the end of the definition
# NOTE: Maybe we should just collect data on the number of transformations
#       performed in the transformer directly? What have we to gain by
#       using a separate tool?


def collect_invocation_stats(fn: str):
    index = ci.Index.create()
    tu: ci.TranslationUnit = index.parse(fn)
    cursor: ci.Cursor = tu.cursor

    macro_names_types: Dict[str, Literal['object-like', 'function-like']] = {}
    integer_macro_names: Set[str] = set()

    tokens = [t for t in cursor.get_tokens()]

    num_object_like_integer_invocations = 0
    num_function_like_integer_invocations = 0

    for i, cur in enumerate(tokens):
        if (i-2 >= 0 and tokens[i - 2].spelling == '#' and
                i-1 >= 0 and tokens[i - 1].spelling == 'define'):
            # Found a macro definition
            macro_name: str = cur.spelling
            end_of_cur_tok: int = cur.location.column + len(macro_name)
            # Is it an object-like or function-like macro?
            if i + 1 < len(tokens) is not None:

                next_tok = tokens[i + 1]
                # If the next token is an opening paren and comes
                # immediately after the macro name, then we have
                # encountered a macro identifier
                if (next_tok.location.column == end_of_cur_tok
                        and next_tok.spelling == '('):
                    macro_names_types[macro_name] = 'function-like'

                    # Check if body of function-like macro is an integer
                    # Advance to end of formals
                    j = i + 1
                    while j < len(tokens) and tokens[j].spelling != ')':
                        j += 1
                    if j + 1 < len(tokens):
                        next_tok = tokens[j + 1]
                        if next_tok.kind == ci.TokenKind.LITERAL:
                            # Does this macro contain more than just a single
                            # integer in its definition?
                            if j + 2 < len(tokens):
                                next_next_tok = tokens[j + 2]
                                nnl = next_next_tok.location.line
                                cl = cur.location.line
                                if nnl > cl or \
                                        next_next_tok.kind == ci.TokenKind.COMMENT:
                                    integer_macro_names.add(macro_name)
                            else:
                                # Macro is defined on last line of file
                                integer_macro_names.add(macro_name)

                else:
                    macro_names_types[macro_name] = 'object-like'

                    # Check if body of object-like macro is an integer
                    if next_tok.kind == ci.TokenKind.LITERAL:
                        # Does this macro contain more than just a single
                        # integer in its definition?
                        if i + 2 < len(tokens):
                            next_next_tok = tokens[i + 2]
                            nnl = next_next_tok.location.line
                            cl = cur.location.line
                            if nnl > cl or \
                                    next_next_tok.kind == ci.TokenKind.COMMENT:
                                integer_macro_names.add(macro_name)
                        else:
                            # Macro is defined on last line of file
                            integer_macro_names.add(macro_name)
            else:
                macro_names_types[macro_name] = 'object-like'

        elif (cur.kind == ci.TokenKind.IDENTIFIER and
              cur.spelling in integer_macro_names):
            # Found a macro invocation
            macro_name = cur.spelling
            if macro_names_types[macro_name] == 'object-like':
                num_object_like_integer_invocations += 1
            else:
                num_function_like_integer_invocations += 1

        elif (i-2 >= 0 and tokens[i - 2].spelling == '#' and
                i-1 >= 0 and tokens[i - 1].spelling == 'include'):
            # Found an include: Process it before proceeding
            file_to_include: str = cur.spelling
            file_to_include = file_to_include.strip('"')
            num_object_like_integer_invocations_from_include, \
                num_function_like_integer_invocations_from_include, \
                macro_names_types_from_include, \
                integer_macro_names_from_include \
                = collect_invocation_stats(file_to_include)
            # Add the list of macro definitions found to the list of macros
            # that could be invoked in this file, and the number of
            # invocations found in the included file to the cumulative
            # results in this file
            num_object_like_integer_invocations += num_object_like_integer_invocations_from_include
            num_function_like_integer_invocations += num_function_like_integer_invocations_from_include
            macro_names_types |= macro_names_types_from_include
            integer_macro_names |= integer_macro_names_from_include

    return num_object_like_integer_invocations, \
        num_function_like_integer_invocations, \
        macro_names_types, integer_macro_names


@begin.start
def main(filename: str):
    num_object_like_integer_invocations, \
        num_function_like_integer_invocations, _, _ \
        = collect_invocation_stats(filename)
    print("Object-like integer invocations,",
          "Function-like integer invocations")
    print(num_object_like_integer_invocations,
          num_function_like_integer_invocations)
