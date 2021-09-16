'''
classifications.py

Classes for classifying macros
'''

from dataclasses import dataclass
from typing import List, NewType

from macro_data_collector import directives

CType = NewType('CType', str)


@dataclass
class ClassifiedMacro():
    '''
    Class for macros that have been classified.

    A classified macro is one for which its corresponding C construct has been
    determined. Each classified macro class has an `emit` method that returns
    a string representing the converted macro. `emit` should not be called
    until the AST has been examined, as this may alter how a macro should
    be converted.

    # Qualifications

    - All convertible macro types must be defined within the same file that
      they are used.
    - Macros are not multiply defined, i.e., they are only defined once.
    - The definition of any convertible macro must not end in a semicolon.
    '''
    macro: directives.DefineDirective


@dataclass
class SimpleConstantMacro(ClassifiedMacro):
    '''
    Class for simple constant object macros.

    These are object-like macros whose bodies contain a
    single C literal value, e.g., 42, 'c', or "Hello, World!".

    This type of macro will either be converted to C a constant or enum
    (if the macro is used as a case label in a switch statement).

    # Examples

    From https://github.com/kokke/tiny-AES-c/blob/12e7744b4919e9d55de75b7ab566326a1c8e7a67/test.c#L7
    ```c
    #define CBC 1
    #define CTR 1
    #define ECB 1
    ```

    '''
    c_type: CType
    used_as_case_label: bool = False
    enum_group_name: str = ""
    emitted = False

    def emit(self) -> str:
        '''
        Emit the C declaration and initialization for the converted macro.
        The result will either be a C constant or an enum.
        '''
        c_type = self.c_type
        # NOTE: The mapping of 'string' to 'char *' is done here,
        # but should it be done in the __init__ method?
        if c_type == "string":
            c_type = "char *"
        if self.used_as_case_label:
            # NOTE: This only emits the enum *value*, not the whole enum.
            # This assumes that the caller to the emit method will emit
            # the enum declaration (e.g., `enum MacroEnums{<emits>};`)
            self.emitted = True
            return f"{self.macro.identifier} = {self.macro.body}"
        self.emitted = True
        return f"const {c_type} {self.macro.identifier} = {self.macro.body};"


# Simple expression macros are macros whose bodies contain expressions
# whose terms are only constants. Since they are functionally the same
# as simple constant macros, we use a type alias
SimpleExpressionMacro = SimpleConstantMacro


# TODO: Complete class for simple pass-by-value function-like macros
@dataclass
class SimplePassByValueFunctionMacro(ClassifiedMacro):
    '''
    Class for simple pass-by-value function-like macros.

    These are function-like macros whose bodies only reference
    the values of the arguments passed to them, and don't reference
    variables from outer scopes (i.e., no side-effects).

    This type of macro will be converted to a C function whose return
    type will be inferrred from its usage in the AST.

    # Example

    From `ext/async/sqlite3async.c` from SQLite source code
    ```c
    /* Useful macros used in several places */
    # define MIN(x,y) ((x)<(y)?(x):(y))
    # define MAX(x,y) ((x)>(y)?(x):(y))
    ```
    '''
    macro: directives.FunctionDefine
    return_type: CType
    parameter_types: List[CType]
    emitted: bool = False

    def emit(self) -> str:
        '''
        Emit the C declaration and definition of the converted macro.
        The result will be a C function.
        '''
        # TODO: Infer correct return type and parameter types from AST
        # Currently, the classifier assigns 'void *' to all types
        result = f"{self.return_type} {self.macro.identifier}("
        for i, (c_type, parameter) in enumerate(zip(self.parameter_types, self.macro.parameters)):
            if i > 0:
                result += ", "
            result += f"{c_type} {parameter}"
        result += (
            ") {"
            f"return {self.macro.body};"
            "}"
        )
        self.emitted = True
        return result

# TODO: Add support for type aliasing macros


@ dataclass
class UnclassifiableMacro(ClassifiedMacro):
    '''Class for macros that don't fit other classifications'''
    pass
