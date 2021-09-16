'''
classify_macros.py

Roughly classifies macros based on their types and definitions.
'''

from collections import deque
from os.path import basename
from typing import Deque, Dict, List, Set, Union

from clang.cindex import Cursor, CursorKind, Index, TranslationUnit
from macro_data_collector import directives
from pycparser.c_ast import BinaryOp, Constant, TernaryOp, UnaryOp
from pycparser.c_parser import CParser

from macro_classifier.clang_utils import FileLineCol, get_file_line_col
from macro_classifier.classifications import (ClassifiedMacro, CType,
                                              SimpleConstantMacro,
                                              SimpleExpressionMacro,
                                              SimplePassByValueFunctionMacro,
                                              UnclassifiableMacro)

# TODO: Support more types of expressions.
# Maybe just use Clang instead of pycparser?
Expression = Union[Constant, UnaryOp, BinaryOp, TernaryOp]

# NOTE: pycparser offers a way to make your own visitor class by
# subclassing a provided template. This could be useful See c_ast.py:109


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
        return SimplePassByValueFunctionMacro(
            macro, 'void *',
            ['void *' for _ in macro.parameters])

    return UnclassifiableMacro(macro)


def check_case_label_for_macro_instantiations(
        root: Cursor,
        location_instantiation_mapping: Dict[FileLineCol, Cursor]
) -> Set[str]:
    '''
    Checks for a given case statement's label for macro instantations.

    Args:
        root:           The case statement whose label to check.
        switch_number:  The number of the switch statement this
                        case statement is nested under.
        case_number:    The number of the case statement in the
                        parent switch statement.

    Returns:
        found_instantiations:   A set of the names of
                                macro instantiations found.

    Raises:
        ValueError:     If the passed cursor is None or not
                        a case statement.
    '''
    if not root:
        raise ValueError("Cursor is None")
    if root.kind != CursorKind.CASE_STMT:
        raise ValueError("Cursor is not a case statement")

    # Case label will be the first child of the case statement
    label: Cursor = next(root.get_children())

    found_instantiations: Set[Cursor] = set()
    cursor: Cursor
    for cursor in label.walk_preorder():
        file_line_col = get_file_line_col(cursor)
        # Check if location of child corresponds to a macro instantiation
        instantiation = location_instantiation_mapping.get(file_line_col)
        if instantiation is not None:
            found_instantiations.add(instantiation.displayname)

    return found_instantiations


def check_macros_in_case_labels(
    root: Cursor,
    c_file: str,
    name_to_macro: Dict[str, ClassifiedMacro],
    location_to_instantation: Dict[FileLineCol, Cursor],
) -> None:

    if root is None:
        return

    child: Cursor
    switch_statements: List[Cursor] = [
        child for child
        in root.walk_preorder()
        if child.location.file is not None and
        basename(child.location.file.name) == basename(c_file)
        and child.kind == CursorKind.SWITCH_STMT
    ]

    for i, switch_statement in enumerate(switch_statements, 1):
        q: Deque[Cursor] = deque()
        # Don't add the switch itself because it would be skipped otherwise
        q.extend(switch_statement.get_children())
        while q:
            cur: Cursor = q.pop()

            # Don't check nested switches here since they
            # will be checked in another iteration of the for loop
            if cur.kind == CursorKind.SWITCH_STMT:
                continue

            if cur.kind == CursorKind.CASE_STMT:
                macro_names = check_case_label_for_macro_instantiations(
                    cur, location_to_instantation)
                for name in macro_names:
                    # Use key operator instead of get method to raise error
                    # if name not found
                    classified_macro = name_to_macro[name]
                    # Update the enum grouping for this classified macro
                    if isinstance(classified_macro, SimpleExpressionMacro):
                        classified_macro.used_as_case_label = True
                        # NOTE: Currently, macro names are grouped
                        # into an enum with the last set of switch statement
                        # case labels in which they were found.
                        # This will still work even if a macro is used in
                        # multiple switch statements, but perhaps the enum
                        # group names of macros used like this should indicate
                        # that they are used in multiple switch statements?
                        enum_group_name = f'Switch{i}CaseLabels'
                        classified_macro.enum_group_name = enum_group_name

            for child in cur.get_children():
                q.append(child)


def check_macro_usage(classified_macros: List[ClassifiedMacro],
                      c_file: str) -> None:
    '''
    Checks how each macro in a list of classified macros is used in the C
    file in which they are defined, and updates each classified macro
    accordingly.

    Current requirements:
        - Each macro is only defined once.
        - Each macro is defined in the same file in which it is used.

    Args:
        classified_macros:  The list of classified macros defined and used in
                            the given C file.

    '''

    # Map each macro macro's name to itself for quick lookup
    name_to_macro: Dict[str, ClassifiedMacro] = {
        cm.macro.identifier: cm
        for cm in classified_macros
    }

    index: Index = Index.create()
    tu = index.parse(
        c_file, options=TranslationUnit.PARSE_DETAILED_PROCESSING_RECORD)
    root_cursor: Cursor = tu.cursor

    # Map each macro instation's location to itself for quick lookup
    # These should all be found directly under the root node
    location_to_instantation: Dict[FileLineCol, Cursor] = {
        get_file_line_col(child): child
        for child in root_cursor.get_children()
        if child.location.file is not None and
        basename(child.location.file.name) == basename(c_file)
        and child.kind == CursorKind.MACRO_INSTANTIATION
    }

    check_macros_in_case_labels(
        root_cursor, c_file, name_to_macro, location_to_instantation)
