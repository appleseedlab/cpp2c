'''
collect_macro_facts.py

Reads in a preprocessor statistics file produced by SuperC
and returns a JSON file containing data on each of the macros
defined and used in the file that SuperC originally analyzed
'''

import os
from collections import deque
from typing import Deque, List, Tuple

from clang.cindex import (Cursor, CursorKind, Index, SourceLocation,
                          TranslationUnit)

from macro_fact_collector.macro_facts import Location, MacroFact, MacroKind


def collect_macro_facts(c_file: str) -> List[MacroFact]:
    '''
    Reads in the name of a CPP stats file and returns
    a list of the macro facts found.

    Args:
        c_file:     The filepath to the C file that was analyzed

    Returns:
        results:    A list of all the macro facts in the c file
    '''
    index: Index = Index.create()
    translation_unit: TranslationUnit = index.parse(
        c_file, options=TranslationUnit.PARSE_DETAILED_PROCESSING_RECORD)
    root_cursor: Cursor = translation_unit.cursor

    macro_names_locations: Deque[Tuple[str, SourceLocation]] = deque()

    results: List[MacroFact] = []

    for cur in root_cursor.walk_preorder():
        source_location: SourceLocation = cur.location
        if source_location.file is None:
            continue
        if os.path.basename(source_location.file.name) != os.path.basename(c_file):
            continue
        if cur.kind == CursorKind.MACRO_DEFINITION:
            macro_names_locations.append((cur.displayname, source_location))

    c_file_lines: List[str]
    with open(c_file, "r") as fp:
        c_file_lines = fp.readlines()

    for name, source_location in macro_names_locations:
        location: Location = Location(c_file,
                                      source_location.line,
                                      source_location.line,
                                      source_location.column)
        start_line: int = source_location.line
        column: int = source_location.column
        identifier: str = name
        # TODO: Use SuperC to infer count of definitions under same static
        # conditional
        definition_count: int = 1
        end_line: int = start_line
        body: str = ""
        parameters = []
        kind: MacroKind

        current_line = c_file_lines[start_line-1]
        # Skip to definition
        current_line = current_line[column-1:]
        # Check for parentheses to determine if object or function-like macro
        if current_line[len(name)] == '(':
            # Fill in parameters and skip parameters to definition for
            # function-like macros
            parameters_list = current_line[current_line.find(
                "(")+1:current_line.find(")")]
            parameters = [parameter.strip()
                          for parameter in parameters_list.split(",")]
            kind = MacroKind.FunctionLike
            current_line = current_line[current_line.find(")")+1:]
        else:
            kind = MacroKind.ObjectLike
            # Skip to definition for object macros
            current_line = current_line[len(name):]

        # Fill in body with definition
        # NOTE: Maybe comments in macro definitions should be preserved
        # somehow?

        # Emulate a do-while loop.
        # See bottom of while loop for comment on why this is done
        while True:
            # First strip single line comments, being sure to retain // in strings
            in_string = False
            comment_start = len(current_line) + 1
            for i, char in enumerate(current_line):
                if (
                        # We have not already started a comment
                        comment_start == len(current_line) + 1
                        # We are starting a comment
                        and char == r'/'
                        and i + 1 < len(current_line)
                        and current_line[i+1] == r'/'):
                    comment_start = i
                if char == r'"':
                    in_string = not in_string
                # Ignore //s in strings
                if in_string:
                    comment_start = len(current_line) + 1
            current_line = current_line[:comment_start]

            # Next remove multi-line comments /*...*/
            # Assumes that these comments don't actually span
            # multiple lines; more for comments that have a specified
            # start and end point
            line_no_comments = ['\0' for _ in current_line]
            i = 0
            k = 0
            in_comment = False
            while i < len(current_line):
                if (
                        not in_comment
                        and current_line[i] == r'/'
                        and i + 1 < len(current_line)
                        and current_line[i+1] == r'*'):
                    in_comment = True
                    i += 2
                    continue

                if (
                        in_comment
                        and current_line[i] == r'*'
                        and i + 1 < len(current_line)
                        and current_line[i+1] == r'/'):
                    in_comment = False
                    i += 2
                    continue

                if in_comment:
                    i += 1
                    continue

                line_no_comments[k] = current_line[i]
                i += 1
                k += 1

            current_line = ''.join(line_no_comments).rstrip('\0')

            body += current_line.lstrip().rstrip("\\\n").rstrip()

            # Check if this macro spans multiple lines, and remove
            # comments from the next line if so.
            # We use the do-while loop form so that the first line
            # always gets its comments removed
            if current_line.endswith("\\\n") and end_line < len(c_file_lines):
                end_line += 1
                current_line = c_file_lines[end_line-1]
            else:
                break

        fact = MacroFact(location, definition_count, identifier,
                         body, kind, parameters)

        fact.location.end_line = end_line
        results.append(fact)
    return results
