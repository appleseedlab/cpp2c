'''
macro_facts.py

Dataclasses for storing macro facts.
Macro facts include information that is inherent to the macro.
'''

from dataclasses import dataclass
from typing import List


# Using a dataclass here instead of an enum so that
# asdict will work when called on MacroFact objects
@dataclass
class MacroKind:
    ObjectLike = "object-like"
    FunctionLike = "function-like"


@dataclass
class Location:
    file: str
    start_line: int
    end_line: int
    column: int


@dataclass
class MacroFact:
    location: Location
    definition_count_under_same_static_conditional: int
    identifier: str
    body: str
    kind: MacroKind
    parameters: List[str]
