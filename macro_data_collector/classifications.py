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


@dataclass
class UnclassifiableMacro(ClassifiedMacro):
    '''Class for macros that don't fit other classifications'''
    pass
