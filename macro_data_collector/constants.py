'''
constants.py

Contains constant values used throughout the program
'''

from enum import Enum

class SuperCOutputString(Enum):
    '''Enum for strings outputted by SuperC'''
    DEFINE = "define"
    COMMAND_LINE = "command-line"
    VAR = "var"
    FUN = "fun"


class RegexGroupName(Enum):
    '''Enum for regular expression group names'''
    DEFINE = "define"
    IDENTIFIER = "identifier"
    TYPE = "type"
    SRC = "src"
    LINE = "line"
    COLUMN = "column"
    DEFINITION_COUNT = "definition_count"
