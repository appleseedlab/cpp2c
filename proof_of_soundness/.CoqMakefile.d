ConfigVars.vo ConfigVars.glob ConfigVars.v.beautified ConfigVars.required_vo: ConfigVars.v Syntax.vo
ConfigVars.vio: ConfigVars.v Syntax.vio
ConfigVars.vos ConfigVars.vok ConfigVars.required_vos: ConfigVars.v Syntax.vos
EvalRules.vo EvalRules.glob EvalRules.v.beautified EvalRules.required_vo: EvalRules.v ConfigVars.vo MapTheorems.vo Syntax.vo
EvalRules.vio: EvalRules.v ConfigVars.vio MapTheorems.vio Syntax.vio
EvalRules.vos EvalRules.vok EvalRules.required_vos: EvalRules.v ConfigVars.vos MapTheorems.vos Syntax.vos
MapTheorems.vo MapTheorems.glob MapTheorems.v.beautified MapTheorems.required_vo: MapTheorems.v ConfigVars.vo
MapTheorems.vio: MapTheorems.v ConfigVars.vio
MapTheorems.vos MapTheorems.vok MapTheorems.required_vos: MapTheorems.v ConfigVars.vos
NoCallsFromFunctionTable.vo NoCallsFromFunctionTable.glob NoCallsFromFunctionTable.v.beautified NoCallsFromFunctionTable.required_vo: NoCallsFromFunctionTable.v ConfigVars.vo EvalRules.vo Syntax.vo MapTheorems.vo
NoCallsFromFunctionTable.vio: NoCallsFromFunctionTable.v ConfigVars.vio EvalRules.vio Syntax.vio MapTheorems.vio
NoCallsFromFunctionTable.vos NoCallsFromFunctionTable.vok NoCallsFromFunctionTable.required_vos: NoCallsFromFunctionTable.v ConfigVars.vos EvalRules.vos Syntax.vos MapTheorems.vos
NoMacroInvocations.vo NoMacroInvocations.glob NoMacroInvocations.v.beautified NoMacroInvocations.required_vo: NoMacroInvocations.v ConfigVars.vo EvalRules.vo MapTheorems.vo NoCallsFromFunctionTable.vo Syntax.vo
NoMacroInvocations.vio: NoMacroInvocations.v ConfigVars.vio EvalRules.vio MapTheorems.vio NoCallsFromFunctionTable.vio Syntax.vio
NoMacroInvocations.vos NoMacroInvocations.vok NoMacroInvocations.required_vos: NoMacroInvocations.v ConfigVars.vos EvalRules.vos MapTheorems.vos NoCallsFromFunctionTable.vos Syntax.vos
NoVarsInEnvironment.vo NoVarsInEnvironment.glob NoVarsInEnvironment.v.beautified NoVarsInEnvironment.required_vo: NoVarsInEnvironment.v ConfigVars.vo EvalRules.vo Syntax.vo
NoVarsInEnvironment.vio: NoVarsInEnvironment.v ConfigVars.vio EvalRules.vio Syntax.vio
NoVarsInEnvironment.vos NoVarsInEnvironment.vok NoVarsInEnvironment.required_vos: NoVarsInEnvironment.v ConfigVars.vos EvalRules.vos Syntax.vos
SideEffects.vo SideEffects.glob SideEffects.v.beautified SideEffects.required_vo: SideEffects.v ConfigVars.vo EvalRules.vo Syntax.vo
SideEffects.vio: SideEffects.v ConfigVars.vio EvalRules.vio Syntax.vio
SideEffects.vos SideEffects.vok SideEffects.required_vos: SideEffects.v ConfigVars.vos EvalRules.vos Syntax.vos
Syntax.vo Syntax.glob Syntax.v.beautified Syntax.required_vo: Syntax.v 
Syntax.vio: Syntax.v 
Syntax.vos Syntax.vok Syntax.required_vos: Syntax.v 
Theorems.vo Theorems.glob Theorems.v.beautified Theorems.required_vo: Theorems.v Syntax.vo ConfigVars.vo MapTheorems.vo EvalRules.vo SideEffects.vo NoCallsFromFunctionTable.vo NoMacroInvocations.vo NoVarsInEnvironment.vo Transformations.vo
Theorems.vio: Theorems.v Syntax.vio ConfigVars.vio MapTheorems.vio EvalRules.vio SideEffects.vio NoCallsFromFunctionTable.vio NoMacroInvocations.vio NoVarsInEnvironment.vio Transformations.vio
Theorems.vos Theorems.vok Theorems.required_vos: Theorems.v Syntax.vos ConfigVars.vos MapTheorems.vos EvalRules.vos SideEffects.vos NoCallsFromFunctionTable.vos NoMacroInvocations.vos NoVarsInEnvironment.vos Transformations.vos
Transformations.vo Transformations.glob Transformations.v.beautified Transformations.required_vo: Transformations.v Syntax.vo ConfigVars.vo EvalRules.vo SideEffects.vo MapTheorems.vo NoCallsFromFunctionTable.vo NoMacroInvocations.vo NoVarsInEnvironment.vo
Transformations.vio: Transformations.v Syntax.vio ConfigVars.vio EvalRules.vio SideEffects.vio MapTheorems.vio NoCallsFromFunctionTable.vio NoMacroInvocations.vio NoVarsInEnvironment.vio
Transformations.vos Transformations.vok Transformations.required_vos: Transformations.v Syntax.vos ConfigVars.vos EvalRules.vos SideEffects.vos MapTheorems.vos NoCallsFromFunctionTable.vos NoMacroInvocations.vos NoVarsInEnvironment.vos
