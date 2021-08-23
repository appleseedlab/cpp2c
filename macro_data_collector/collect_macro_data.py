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
from macro_data_collector.directives import (DefineDirective, FunctionDefine, MacroDataList,
                                             ObjectDefine)


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
                line = int(match_.group(RegexGroupNames.LINE))
                column = int(match_.group(RegexGroupNames.COLUMN))
                identifier = match_.group(RegexGroupNames.IDENTIFIER)
                type_ = match_.group(RegexGroupNames.TYPE)
                definition_count = int(match_.group(
                    RegexGroupNames.DEFINITION_COUNT))
                body = ""
                usage: DefineDirective
                if type_ == SuperCOutputStrings.VAR:
                    usage = ObjectDefine(
                        c_file, line, column, definition_count, identifier, body)
                else:
                    usage = FunctionDefine(
                        c_file, line, column, definition_count, identifier, body, [])
                # Fill in definition
                current_line = c_file_lines[line-1]
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
                body += current_line.lstrip().rstrip("\\\n")
                while current_line.endswith("\\\n") and line < len(c_file_lines):
                    line += 1
                    current_line = c_file_lines[line-1]
                    body += current_line.lstrip().rstrip("\\\n")

                usage.body = body
                results.append(usage)
    return results
