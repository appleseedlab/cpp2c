'''
macro_classification.py

Enum for different macro classifications.
Refer to macro classification spreadsheet for the "truth table"
from which these classifications were determined
'''


from dataclasses import dataclass


@dataclass
class MacroClassification:
    MultiplyDefinedMacro = 'multiply-defined-macro'
    ConfigurationMacro = 'configuration-macro'
    TokenPastingMacro = 'token-pasting-macro'
    StringificationMacro = 'stringification-macro'
    VariadicMacro = 'variadic-macro'
    ConstantTypedefObjectMacro = 'constant-typedef-object-macro'
    ExternalVariableTypedefObjectMacro = 'external-variable-typedef-object-macro'
    InconvertibleTypeExpressionObjectMacro = 'inconvertible-type-expression-object-macro'
    ConstantExpressionObjectMacro = 'constant-expression-object-macro'
    ConstantExpressionArraySizeObjectMacro = 'constant-expression-array-size-object-macro'
    ConstantExpressionCaseLabelObjectMacro = 'constant-expression-case-label-object-macro'
    ConstantExpressionArraySizeCaseLabelObjectMacro = 'constant-expression-array-size-case-label-object-macro'
    ExternalVariablesExpressionObjectMacro = 'external-variables-expression-object-macro'
    ExternalVariablesSideEffectsExpressionObjectMacro = 'external-variables-side-effects-expression-object-macro'
    ConstantIterationStatementObjectMacro = 'constant-iteration-statement-object-macro'
    ExternalVariablesIterationStatementObjectMacro = 'external-variables-iteration-statement-object-macro'
    ExternalVariablesSideEffectsIterationStatementObjectMacro = 'external-variables-side-effects-iteration-statement-object-macro'
    ConstantCompoundStatementObjectMacro = 'constant-compound-statement-object-macro'
    ExternalVariablesCompoundStatementObjectMacro = 'external-variables-compound-statement-object-macro'
    ExternalVariablesSideEffectsCompoundStatementObjectMacro = 'external-variables-side-effects-compound-statement-object-macro'
    ConstantBlockItemListObjectMacro = 'constant-block-item-list-object-macro'
    ExternalVariablesBlockItemListObjectMacro = 'external-variables-block-item-list-object-macro'
    ExternalVariablesSideEffectsBlockItemListObjectMacro = 'external-variables-side-effects-block-item-list-object-macro'
    ConstantTypedefFunctionMacro = 'constant-typedef-function-macro'
    ExternalVariablesTypedefFunctionMacro = 'external-variables-typedef-function-macro'
    PotentiallyInconvertibleFunctionMacro = 'potentially-inconvertible-function-macro'
    ConstantExpressionFunctionMacro = 'constant-expression-function-macro'
    ConstantExpressionArraySizeFunctionMacro = 'constant-expression-array-size-function-macro'
    ConstantExpressionCaseLabelFunctionMacro = 'constant-expression-case-label-function-macro'
    ConstantExpressionCaseLabelArraySizeFunctionMacro = 'constant-expression-case-label-array-size-function-macro'
    ExternalVariablesExpressionFunctionMacro = 'external-variables-expression-function-macro'
    ExternalVariablesSideEffectsExpressionFunctionMacro = 'external-variables-side-effects-expression-function-macro'
    ConstantIterationStatementFunctionMacro = 'constant-iteration-statement-function-macro'
    ExternalVariablesIterationStatementFunctionMacro = 'external-variables-iteration-statement-function-macro'
    ExternalVariablesSideEffectsIterationStatementFunctionMacro = 'external-variables-side-effects-iteration-statement-function-macro'
    ConstantCompoundStatementFunctionMacro = 'constant-compound-statement-function-macro'
    ExternalVariablesCompoundStatementFunctionMacro = 'external-variables-compound-statement-function-macro'
    ExternalVariablesSideEffectsCompoundStatementFunctionMacro = 'external-variables-side-effects-compound-statement-function-macro'
    ConstantBlockItemListFunctionMacro = 'constant-block-item-list-function-macro'
    ExternalVariablesBlockItemListFunctionMacro = 'external-variables-block-item-list-function-macro'
    ExternalVariablesSideEffectsBlockItemListFunctionMacro = 'external-variables-side-effects-block-item-list-function-macro'
