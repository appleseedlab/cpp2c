'''
classify_macros.py

Roughly classifies macros based on their types and definitions.
'''

from typing import Union

from macro_data_collector import directives
from pycparser.c_ast import BinaryOp, Constant, TernaryOp, UnaryOp
from pycparser.c_parser import CParser

from macro_classifier.classifications import (ClassifiedMacro, CType,
                                              SimpleConstantMacro,
                                              SimplePassByValueFunctionMacro,
                                              UnclassifiableMacro)

# TODO: Support more types of expressions
Expression = Union[Constant, UnaryOp, BinaryOp, TernaryOp]

# NOTE: pycparser offers a way to make your own visitor class by subclassing
# a provided template. This could be useful See c_ast.py:109

def parse_expression_type(expression: Expression) -> Union[CType, None]:
    if isinstance(expression, Constant):
        return parse_constant_type(expression)
    elif isinstance(expression, UnaryOp):
        return parse_unary_op_type(expression)
    elif isinstance(expression, BinaryOp):
        return parse_binary_op_type(expression)
    elif isinstance(expression, TernaryOp):
        return parse_ternary_op_type(expression)
    return None


def parse_constant_type(constant: Constant) -> CType:
    return constant.type


def parse_unary_op_type(unary_op: UnaryOp) -> CType:
    return parse_expression_type(unary_op.expr)


def parse_binary_op_type(binary_op: BinaryOp) -> CType:
    # Reference for implicit type casting hierarchy:
    # https://www.guru99.com/c-type-casting.html
    if binary_op.op in ['||', '&&']:
        return 'int'
    left_type = parse_expression_type(binary_op.left)
    right_type = parse_expression_type(binary_op.right)
    hierarchy = [
        'long double',
        'double',
        'float',
        'unsigned long long int',
        'long long int',
        'unsigned long int',
        'long int',
        'unsigned int',
        'int',
        'unsigned short',
        'short',
        'unsigned char',
        'char',
    ]
    for type_ in hierarchy:
        if left_type == type_ or right_type == type_:
            return type_
    return None


def parse_ternary_op_type(ternary_op: TernaryOp) -> CType:
    # TODO: Figure out a better way of determining the return type...
    return parse_expression_type(ternary_op.iftrue)


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
            type_: CType = parse_expression_type(block_item)
            if type_ is None:
                raise ValueError(
                    "Object define macro body is not a constant"
                    " expression:", macro)
            return SimpleConstantMacro(macro, type_, macro.body)
        except:
            return UnclassifiableMacro(macro)
    elif isinstance(macro, directives.FunctionDefine):
        # TODO: Correctly classify simple pass-by-value function-like macros
        return SimplePassByValueFunctionMacro(macro, 'void *', ['void *' for _ in macro.parameters])

    return UnclassifiableMacro(macro)
