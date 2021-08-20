'''
classify_macros.py

Roughly classifies macros based on their types and definitions.
'''

from typing import Union
from macro_data_collector import directives
from macro_data_collector.classifications import (CharMacro, ClassifiedMacro, CType, NumberMacro, StringMacro,
                                                  UnclassifiableMacro)
import re

# Notice the [^0]. This is to prevent recognizing octals as ints
INT_PATTERN = re.compile(r"^[+-]?[^0]\d*$")
FLOAT_PATTERN = re.compile(r"^[+-]?(((\d+)?\.(\d+))|((\d+)\.(\d+)?))$")
BINARY_PATTERN = re.compile(r"^[+-]?0(b|B)[01]+$")
OCTAL_PATTERN = re.compile(r"^[+-]?0[0-7]+$")
HEX_PATTERN = re.compile(r"^[+-]?0(x|X)[0-9A-Fa-f]+$")


def get_ctype_from_number(val: Union[int, float], is_int: bool) -> CType:
    '''
    Returns a number's corresponding C data type

    Args:
        val:        The value to get the C type for
        is_int:     Whether the number is an int or a float

    Returns:
        ctype:      The C type for the given values

    Raises:
        ValueError: If a macro is defined to an invalid number
    '''
    # TODO: Refactor for a better way of identifying ints vs floats.
    # Passing the type as a boolean argument seems error-prone.
    if is_int:
        if 0 <= val <= 255:
            return CType.UNSIGNED_CHAR
        elif -128 <= val <= 127:
            return CType.SIGNED_CHAR
        elif -32_768 <= val <= 32_767:
            return CType.SHORT
        elif 0 <= val <= 65_535:
            return CType.UNSIGNED_SHORT
        elif -2_147_483_648 <= val <= 2_147_484_647:
            return CType.INT
        elif 0 <= val <= 4_294_967_295:
            return CType.UNSIGNED_INT
        elif -9223372036854775808 <= val <= 9223372036854775807:
            return CType.LONG
        elif 0 <= val <= 18446744073709551615:
            return CType.UNSIGNED_LONG
        elif -3.40282e+38 <= val <= 3.40282e+38:
            return CType.FLOAT
        elif -1.79769e+308 <= val <= 1.79769e+308:
            return CType.DOUBLE
        elif -1.1E+4932 <= val <= 1.1E+4932:
            return CType.LONG_DOUBLE
        else:
            raise ValueError(f"Invalid C number: {val}")
    # Floats
    if -3.40282e+38 <= val <= 3.40282e+38:
        return CType.FLOAT
    elif -1.79769e+308 <= val <= 1.79769e+308:
        return CType.DOUBLE
    elif -1.1E+4932 <= val <= 1.1E+4932:
        return CType.LONG_DOUBLE
    else:
        raise ValueError(f"Invalid C number: {val}")


def classify_macro(macro: directives.CPPDirective) -> ClassifiedMacro:
    '''
    Roughly classifies a CPP directive and returns a classified macro

    Args:
        macro:  The macro to classify

    Returns: The macro along with its classification

    Raises:
        ValueError: If a macro is defined to an invalid value
    '''
    # TODO: Need a way of ignoring comments in macro bodies...
    if isinstance(macro, directives.ObjectDefine):
        # Classifying an object-like macro
        if re.match(INT_PATTERN, macro.body):
            val = int(macro.body)
            ctype = get_ctype_from_number(val, True)
            return NumberMacro(macro, ctype.value, val)
        elif re.match(FLOAT_PATTERN, macro.body):
            val = float(macro.body)
            ctype = get_ctype_from_number(val, False)
            return NumberMacro(macro, ctype.value, val)
        elif re.match(BINARY_PATTERN, macro.body):
            val = int(macro.body, base=2)
            ctype = get_ctype_from_number(val, True)
            return NumberMacro(macro, ctype.value, base=2)
        elif re.match(OCTAL_PATTERN, macro.body):
            val = int(macro.body, base=8)
            ctype = get_ctype_from_number(val, True)
            return NumberMacro(macro, ctype.value, base=8)
        elif re.match(HEX_PATTERN, macro.body):
            val = int(macro.body, base=16)
            ctype = get_ctype_from_number(val, True)
            return NumberMacro(macro, ctype.value, base=16)

        # Single character char
        # TODO: Make sure this recognizes control characters
        # and the single quote character correctly
        elif (len(macro.body) == 3
              and macro.body[0] == "'"
              and macro.body[1] in [chr(i) for i in range(32, 127)]
              and macro.body[2] == "'"):
            return CharMacro(macro, CType.CHAR.value, macro.body)

        # TODO: Determine if a macro body is actually a valid string.
        # Currently just checking if the body begins and ends
        # with double quotes...
        elif (macro.body[0] == '"'
              and macro.body[-1] == '"'):
            return StringMacro(macro, macro.body)

    elif isinstance(macro, directives.FunctionDefine):
        # Classifying a function-like macro
        pass
    return UnclassifiableMacro(macro)
