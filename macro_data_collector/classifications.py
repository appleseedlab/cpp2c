'''
classifications.py

Classes for classifying macros
'''

from dataclasses import dataclass
from enum import Enum
from typing import NewType, Union

from macro_data_collector import directives


class CType(Enum):
    '''
    Enum for C data types.
    Types take from:
    https://www.tutorialspoint.com/cprogramming/c_data_types.htm
    '''
    CHAR = "char"
    UNSIGNED_CHAR = "unsigned char"
    SIGNED_CHAR = "signed char"
    INT = "int"
    UNSIGNED_INT = "unsigned int"
    SHORT = "short"
    UNSIGNED_SHORT = "unsigned short"
    LONG = "long"
    UNSIGNED_LONG = "unsigned long"
    FLOAT = "float"
    DOUBLE = "double"
    LONG_DOUBLE = "long double"

    STRING = "char *"


CTypeValue = NewType("CTypeValue", str)


@dataclass
class ClassifiedMacro():
    '''Class for macros that have been classified'''
    macro: directives.DefineDirective


@dataclass
class SimpleConstantObject(ClassifiedMacro):
    '''Class for simple constant object macros'''
    # Note: This string should be a value from the CType enum
    # The datatype is not CType enum due to the fact that dataclasses
    # containing enums cannot be easily converted to dicts with the asdict
    # function
    ctype: CTypeValue
    value: str


@dataclass
class NumberMacro(SimpleConstantObject):
    '''Class for simple constant object macros defined to a number value'''
    value: Union[int, float]
    base: int = 10


@dataclass
class CharMacro(SimpleConstantObject):
    '''Class for simple constant object macros defined to a char value'''
    value: str


@dataclass
class StringMacro(SimpleConstantObject):
    value: str

    def __init__(self, macro: directives.DefineDirective, value: str):
        super(StringMacro, self).__init__(macro, CType.STRING.value, value)


@dataclass
class UnclassifiableMacro(ClassifiedMacro):
    '''Class for macros that don't fit other classifications'''
    pass
