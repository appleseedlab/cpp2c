'''
classifications.py

Classes for classifying macros
'''

from dataclasses import dataclass

from macro_data_collector import directives


@dataclass
class ClassifiedMacro():
    '''Class for macros that have been classified'''
    macro: directives.DefineDirective


@dataclass
class SimpleConstantMacro(ClassifiedMacro):
    '''Class for simple constant object macros'''
    ctype: str
    value: str
    # TODO: Read AST to determine if an object macro is used as a case label
    used_as_case_label: bool = False
    # TODO: Group object macros used as case labels in the same switch
    # statement in the same enum
    enum_group_name: str = ""

    def emit(self) -> str:
        '''Emit the C declaration and initialization for the macro'''
        ctype = self.ctype
        if ctype == "string":
            ctype = "char *"
        if self.used_as_case_label:
            # TODO: Emit all object defines used as case labels in the
            # same switch statement to values in the same enum
            pass

        return f"const {ctype} {self.macro.identifier} = {self.value};"


@dataclass
class UnclassifiableMacro(ClassifiedMacro):
    '''Class for macros that don't fit other classifications'''
    pass
