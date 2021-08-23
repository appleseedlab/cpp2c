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
    SCHAR_MIN = - 128
    SCHAR_MAX = + 127
    UCHAR_MAX = 255
    CHAR_MIN = - 128
    CHAR_MAX = + 127
    SHRT_MIN = - 32768
    SHRT_MAX = + 32767
    USHRT_MAX = 65535
    INT_MIN = - 2147483648
    INT_MAX = + 2147483647
    UINT_MAX = 4294967295
    LONG_MIN = - 9223372036854775808
    LONG_MAX = + 9223372036854775807
    ULONG_MAX = 18446744073709551615
    FLT_MAX = 3.40282346638528859811704183484516925e+38
    DBL_MAX = 1.79769313486231570814527423731704357e+308
    LDBL_MAX = 1.18973149535723176502126385303097021e+4932
