'''
classify_macros.py

Roughly classifies macros based on their types and definitions.
'''

from typing import Union

from pycparser.c_ast import Constant, UnaryOp
from pycparser.c_parser import CParser
from macro_data_collector import directives
from macro_classifier.classifications import ClassifiedMacro, SimpleConstantMacro, UnclassifiableMacro


def classify_macro(macro: directives.CPPDirective) -> ClassifiedMacro:
    '''
    Roughly classifies a CPP directive and returns a classified macro

    Args:
        macro:  The macro to classify

    Returns: The macro along with its classification
    '''

    if isinstance(macro, directives.ObjectDefine):
        # First, try to parse the body as a literal.
        # Since C requires that literals be placed inside functions, first
        # wrap the literal in a function
        try:
            c_function = "void f() {" + macro.body + ";}"
            block_item: Union[Constant, UnaryOp] = CParser().parse(
                c_function).ext[0].body.block_items[0]
            constant: Constant
            value: str
            if isinstance(block_item, UnaryOp):
                constant = block_item.expr
                value = block_item.op + constant.value
            elif isinstance(block_item, Constant):
                constant = block_item
                value = constant.value
            else:
                raise ValueError(
                    "Object define macro body is not a constant"
                    " or unary operation:", macro)
            return SimpleConstantMacro(macro, constant.type, value)
        except:
            return UnclassifiableMacro(macro)

    return UnclassifiableMacro(macro)
