'''
constants.py

Contains constant values used throughout the program
'''


class SuperCOutputStrings():
    '''Strings outputted by SuperC'''
    DEFINE = "define"
    COMMAND_LINE = "command-line"
    VAR = "var"
    FUN = "fun"


class RegexGroupNames():
    '''Regular expression group names'''
    DEFINE = "define"
    IDENTIFIER = "identifier"
    TYPE = "type"
    SRC = "src"
    LINE = "line"
    COLUMN = "column"
    DEFINITION_COUNT = "definition_count"

class CLimits():
    CHAR_BIT =	8	                    # Defines the number of bits in a byte.
    SCHAR_MIN = - 128	                # Defines the minimum value for a signed char.
    SCHAR_MAX = + 127	                # Defines the maximum value for a signed char.
    UCHAR_MAX =	255	                    # Defines the maximum value for an unsigned char.
    CHAR_MIN = - 128	                # Defines the minimum value for type char and its value will be equal to SCHAR_MIN if char represents negative values, otherwise zero.
    CHAR_MAX = + 127	                # Defines the value for type char and its value will be equal to SCHAR_MAX if char represents negative values, otherwise UCHAR_MAX.
    MB_LEN_MAX =	16	                # Defines the maximum number of bytes in a multi-byte character.
    SHRT_MIN = - 32768	                # Defines the minimum value for a short int.
    SHRT_MAX = + 32767	                # Defines the maximum value for a short int.
    USHRT_MAX =	65535	                # Defines the maximum value for an unsigned short int.
    INT_MIN = - 2147483648	            # Defines the minimum value for an int.
    INT_MAX = + 2147483647	            # Defines the maximum value for an int.
    UINT_MAX =	4294967295	            # Defines the maximum value for an unsigned int.
    LONG_MIN = - 9223372036854775808	# Defines the minimum value for a long int.
    LONG_MAX = + 9223372036854775807	# Defines the maximum value for a long int.
    ULONG_MAX =	18446744073709551615	# Defines the maximum value for an unsigned long int.
    FLT_MAX = 3.40282346638528859811704183484516925e+38
    DBL_MAX = 1.79769313486231570814527423731704357e+308
    LDBL_MAX = 1.18973149535723176502126385303097021e+4932
