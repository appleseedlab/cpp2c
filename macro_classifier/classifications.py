'''
classifications.py

Classes for classifying macros
'''

from dataclasses import dataclass

from macro_data_collector import directives


@dataclass
class ClassifiedMacro():
    '''
    Class for macros that have been classified.

    A classified macro is one for which its corresponding C construct has been
    determined. Each classified macro class has an `emit` method that returns
    a string representing the converted macro. `emit` should not be called
    until the AST has been examined, as this may alter how a macro should
    be converted.
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

    ## Examples
    
    From https://github.com/kokke/tiny-AES-c/blob/12e7744b4919e9d55de75b7ab566326a1c8e7a67/test.c#L7
    ```c
    #define CBC 1
    #define CTR 1
    #define ECB 1
    ```

    '''
    c_type: str
    value: str
    # TODO: Read AST to determine if an object macro is used as a case label
    used_as_case_label: bool = False
    # TODO: Group object macros used as case labels in the same switch
    # statement in the same enum
    enum_group_name: str = ""

    def emit(self) -> str:
        '''
        Emit the C declaration and initialization for the converted macro.
        The result will either be a C constant or an enum.
        '''
        c_type = self.c_type
        if c_type == "string":
            c_type = "char *"
        if self.used_as_case_label:
            # TODO: Emit all object defines used as case labels in the
            # same switch statement to values in the same enum
            # TODO: Raise an error if a macro was used as a case label
            # but its C type isn't numeric (can this even be done?)
            pass

        return f"const {c_type} {self.macro.identifier} = {self.value};"


# TOOD: Complete class for simple pass-by-value function-like macros
@dataclass
class SimplePassByValueFunctionMacro(ClassifiedMacro):
    '''
    Class for simple pass-by-value function-like macros.

    These are function-like macros whose bodies only reference
    the values of the arguments passed to them, and don't reference
    variables from outer scopes.

    This type of macro will be converted to a C function whose return
    type will be inferrred from its usage in the AST.

    ## Example
    
    From `ext/async/sqlite3async.c` from SQLite source code
    ```c
    /* Useful macros used in several places */
    #define MIN(x,y) ((x)<(y)?(x):(y))
    #define MAX(x,y) ((x)>(y)?(x):(y))
    ```
    '''
    return_type: str

    def emit(self) -> str:
        '''
        Emit the C declaration and definition of the converted macro.
        The result will be a C function.
        '''
        ...


@dataclass
class UnclassifiableMacro(ClassifiedMacro):
    '''Class for macros that don't fit other classifications'''
    pass
