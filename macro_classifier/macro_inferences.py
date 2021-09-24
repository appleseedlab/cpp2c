'''
macro_inferences.py

Dataclasses for storing macro inferences.
Macro inferences include information that cannot reliably be determined
from the macro's definition alone, and must be determined by examining
macro's instantiation(s) in the AST, trying to parse its definition as an
AST fragment, and more.
'''

from dataclasses import dataclass
from macro_fact_collector.macro_facts import MacroFacts
from macro_classifier.macro_classification import MacroClassification
from typing import Optional


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
    ast_fragment: Optional[ASTFragment]
    parsed_type: Optional[str]
    body_contains_parameters: bool
    body_contains_free_variables: bool
    body_contains_nested_macros: bool
    body_has_side_effects: bool
    used_in_case_label: bool
    used_to_declare_array_size: bool
    multiply_defined_under_single_compilation_branch: bool
    appears_in_static_conditional: bool
    body_contains_stringization: bool
    body_contains_token_pasting: bool
    variadic: bool
    classification: Optional[MacroClassification]
