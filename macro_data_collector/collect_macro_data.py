'''
collect_macro_data.py

Reads in a preprocessor statistics file produced by SuperC
and returns a JSON file containing data on each of the macros
defined and used in the file that SuperC originally analyzed
'''

import os
import re
from typing import List

from macro_data_collector.constants import RegexGroupNames, SuperCOutputStrings
from macro_data_collector.directives import (DefineDirective, FunctionDefine,
                                             MacroDataList, ObjectDefine)


def collect_macro_data(stats_file: str, c_file: str) -> MacroDataList:
    '''
    Reads in the name of a CPP stats file and the name of the C file
    that it references, and returns a comprehensive list of the macro data
    found in that file

    Args:
        stats_file: The filepath to the CPP stats file
        c_file:     The filepath to the C file that was analyzed

    Returns:
        results:    A list of all the macro usage data in the c file
    '''
    # RegEx pattern for matching statistic data.
    # Currently only matches for define directive data, but can be
    # expanded to match other kinds of data by just adding a new pattern
    # to recognize that data to the list. It's easier to make a new pattern
    # first with a long string literal, and then replace the group names and SuperC
    # strings with constants

    # I'm not sure if the use of enums here is good practice,
    # or actually an anti-pattern since it splits the regular
    # expression up across multiple lines. This may also be a benefit since
    # it prevents the line of code with the pattern in it from getting too long
    stats_pattern = re.compile(
        '|'.join([
            r"(?P<" + RegexGroupNames.DEFINE +
            r">" + SuperCOutputStrings.DEFINE +
            r" (?P<" + RegexGroupNames.IDENTIFIER +
            r">[_a-zA-Z][_a-zA-Z0-9]{0,30}) (?P<" + RegexGroupNames.TYPE +
            r">" + SuperCOutputStrings.VAR + r"|" +
            SuperCOutputStrings.FUN + r") (?P<" + RegexGroupNames.SRC +
            r">(?:\<" + SuperCOutputStrings.COMMAND_LINE +
            r"\>)|(?:.*\.(?:c|h))):(?P<" + RegexGroupNames.LINE +
            r">\d+):(?P<" + RegexGroupNames.COLUMN +
            r">\d+) (?P<" + RegexGroupNames.DEFINITION_COUNT + r">\d+))",
        ])
    )
    results = []
    c_file_lines: List[str]
    with open(c_file, "r") as fp:
        c_file_lines = fp.readlines()
    with open(stats_file, "r") as fp:
        for line in fp:
            match_ = re.match(stats_pattern, line)
            # For now skip other CPP directives
            if match_ is None:
                continue
            if match_.group(RegexGroupNames.DEFINE) is not None:
                # Found a #define directive
                src = match_.group(RegexGroupNames.SRC)
                # Only concerned with macros defined in the specified C file
                if src == SuperCOutputStrings.COMMAND_LINE or os.path.basename(src) != os.path.basename(c_file):
                    continue
                start_line = int(match_.group(RegexGroupNames.LINE))
                column = int(match_.group(RegexGroupNames.COLUMN))
                identifier = match_.group(RegexGroupNames.IDENTIFIER)
                type_ = match_.group(RegexGroupNames.TYPE)
                definition_count = int(match_.group(
                    RegexGroupNames.DEFINITION_COUNT))
                end_line = start_line
                body = ""
                usage: DefineDirective
                if type_ == SuperCOutputStrings.VAR:
                    usage = ObjectDefine(
                        c_file, start_line, end_line, column, definition_count, identifier, body)
                else:
                    usage = FunctionDefine(
                        c_file, start_line, end_line, column, definition_count, identifier, body, [])
                # Fill in definition
                current_line = c_file_lines[start_line-1]
                # Skip to definition
                current_line = current_line[current_line.find(
                    identifier)+len(identifier):]
                # Fill in parameters and skip parameters to definition for
                # function-like macros
                if type_ == SuperCOutputStrings.FUN:
                    parameters_list = current_line[current_line.find(
                        "(")+1:current_line.find(")")]
                    parameters = parameters_list.split(",")
                    usage.parameters = [parameter.strip()
                                        for parameter in parameters]

                    current_line = current_line[current_line.find(")")+1:]
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

                usage.body = body
                usage.end_line = end_line
                results.append(usage)
    return results
