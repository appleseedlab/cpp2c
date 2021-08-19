from dataclasses import dataclass
from typing import List, NewType

Identifier = NewType("Identifier", str)


@dataclass
class CPPDirective():
    '''Base class for CPP directives'''
    file: str
    line: int
    column: int


@dataclass
class DefineDirective(CPPDirective):
    '''Base class for CPP define directives'''
    definition_count: int
    identifier: Identifier
    body: str


@dataclass
class ObjectDefine(DefineDirective):
    '''
    Class for definitions of object-like macros.
    Used only for classification purposes and does not contain any
    additional attributes from its parent class (DefineDirective)'''
    pass


@dataclass
class FunctionDefine(DefineDirective):
    '''Class for definition sof function-like macros'''
    parameters: List[Identifier]


MacroDataList = NewType("MacroDataList", List[CPPDirective])
