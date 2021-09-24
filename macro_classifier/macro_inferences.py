'''
macro_inferences.py

Dataclasses for storing macro inferences.
Macro inferences include information that cannot reliably be determined
from the macro's definition alone, and must be determined by examining
macro's instantiation(s) in the AST, trying to parse its definition as an
AST fragment, and more.
'''

from collections import defaultdict
from dataclasses import dataclass, field
from typing import DefaultDict, Optional, Set

from macro_fact_collector.macro_facts import MacroFacts

from macro_classifier.macro_classification import MacroClassification


# Dataclass replacement for an enum so that it can be serializable
@dataclass
class ASTFragment:
    BlockItemList = 'block-item-list'
    CompoundStatement = 'compound-statement'
    IterationStatement = 'iteration-statement'
    Expression = 'expression'
    Type = 'type'


@dataclass
class MacroInferences:
    macro_facts: MacroFacts
    ast_fragment: Optional[ASTFragment] = None
    parsed_type: Optional[str] = None
    body_contains_parameters: Optional[bool] = None
    body_contains_free_variables: Optional[bool] = None
    body_contains_nested_macros: Optional[bool] = None
    parameter_identifiers_to_types: DefaultDict[str, Set] = field(
        default_factory=lambda: defaultdict(set))
    free_variable_identifiers_to_types: DefaultDict[str, Set] = field(
        default_factory=lambda: defaultdict(set))
    macro_identifiers_to_types: DefaultDict[str, Set] = field(
        default_factory=lambda: defaultdict(set))
    body_has_side_effects: Optional[bool] = None
    used_in_case_label: Optional[bool] = None
    used_to_declare_array_size: Optional[bool] = None
    multiply_defined_under_single_compilation_branch: Optional[bool] = None
    appears_in_static_conditional: Optional[bool] = None
    body_contains_stringization: Optional[bool] = None
    body_contains_token_pasting: Optional[bool] = None
    variadic: Optional[bool] = None
    classification: Optional[MacroClassification] = None
