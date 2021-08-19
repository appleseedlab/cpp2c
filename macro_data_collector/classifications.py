'''
classifications.py

Classes for classifying macros
'''

from dataclasses import dataclass
from enum import Enum
from typing import NewType, Union

from macro_data_collector import directives


class CType(Enum):
    INT = "int"
    CHAR = "char"
    STRING = "string"


CTypeValue = NewType("CTypeValue", str)


@dataclass
class ClassifiedMacro():
    '''Class for macros that have been classified'''
    macro: directives.DefineDirective


@dataclass
class SimpleConstantObject(ClassifiedMacro):
    '''Class for simple constant object macros'''
    # Note: This string should be a value frmo the CType enum
    # The datatype is not CType enum due to the way enums interact with
    # dataclasses
    ctype: CTypeValue
    value: Union[int, float, str]


@dataclass
class UnclassifiableMacro(ClassifiedMacro):
    '''Class for macros that don't fit other classifications'''
    pass
