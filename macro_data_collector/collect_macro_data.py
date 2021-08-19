'''
collect_macro_data.py

Reads in a preprocessor statistics file produced by SuperC
and returns a JSON file containing data on each of the macros
defined and used in the file that SuperC originally analyzed
'''

import os
import re
from typing import List

from constants import RegexGroupName, SuperCOutputString
from directives import (DefineDirective, FunctionDefine, MacroDataList,
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
            r"(?P<" + RegexGroupName.DEFINE.value +
            r">" + SuperCOutputString.DEFINE.value + r" (?P<" + RegexGroupName.IDENTIFIER.value +
            r">[_a-zA-Z][_a-zA-Z0-9]{0,30}) (?P<" + RegexGroupName.TYPE.value +
            r">" + SuperCOutputString.VAR.value + r"|" +
            SuperCOutputString.FUN.value + r") (?P<" + RegexGroupName.SRC.value +
            r">(?:\<" + SuperCOutputString.COMMAND_LINE.value + r"\>)|(?:.*\.(?:c|h))):(?P<" + RegexGroupName.LINE.value +
            r">\d+):(?P<" + RegexGroupName.COLUMN.value +
            r">\d+) (?P<" + RegexGroupName.DEFINITION_COUNT.value + r">\d+))",
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
            if match_.group(RegexGroupName.DEFINE.value) is not None:
                # Found a #define directive
                src = match_.group(RegexGroupName.SRC.value)
                # Only concerned with macros defined in the specified C file
                if src == "<command-line>" or os.path.basename(src) != os.path.basename(c_file):
                    continue
                line = int(match_.group(RegexGroupName.LINE.value))
                column = int(match_.group(RegexGroupName.COLUMN.value))
                identifier = match_.group(RegexGroupName.IDENTIFIER.value)
                type_ = match_.group(RegexGroupName.TYPE.value)
                definition_count = int(match_.group(
                    RegexGroupName.DEFINITION_COUNT.value))
                body = ""
                usage: DefineDirective
                if type_ == SuperCOutputString.VAR.value:
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
                if type_ == SuperCOutputString.FUN.value:
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
