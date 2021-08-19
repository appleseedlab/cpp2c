'''
classify_macros.py

Roughly classifies macros based on their types and definitions.
'''

from macro_data_collector import directives
from macro_data_collector.classifications import (ClassifiedMacro, CType,
                                                  SimpleConstantObject, UnclassifiableMacro)


def classify_macro(macro: directives.CPPDirective) -> ClassifiedMacro:
    '''
    Roughly classifies a CPP directive and returns a classified macro

    Args:
        macro:  The macro to classify

    Returns: The macro along with its classification
    '''
    if isinstance(macro, directives.ObjectDefine):
        # Classifying an object-like macro
        if macro.body.isdecimal():
            return SimpleConstantObject(macro, CType.INT.value, int(macro.body))
        else:
            ...
    elif isinstance(macro, directives.FunctionDefine):
        # Classifying a function-like macro
        ...
    return UnclassifiableMacro(macro)
