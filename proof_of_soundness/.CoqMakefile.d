ConfigVars.vo ConfigVars.glob ConfigVars.v.beautified ConfigVars.required_vo: ConfigVars.v Syntax.vo
ConfigVars.vio: ConfigVars.v Syntax.vio
ConfigVars.vos ConfigVars.vok ConfigVars.required_vos: ConfigVars.v Syntax.vos
EvalRules.vo EvalRules.glob EvalRules.v.beautified EvalRules.required_vo: EvalRules.v ConfigVars.vo Syntax.vo
EvalRules.vio: EvalRules.v ConfigVars.vio Syntax.vio
EvalRules.vos EvalRules.vok EvalRules.required_vos: EvalRules.v ConfigVars.vos Syntax.vos
MapTheorems.vo MapTheorems.glob MapTheorems.v.beautified MapTheorems.required_vo: MapTheorems.v ConfigVars.vo
MapTheorems.vio: MapTheorems.v ConfigVars.vio
MapTheorems.vos MapTheorems.vok MapTheorems.required_vos: MapTheorems.v ConfigVars.vos
Syntax.vo Syntax.glob Syntax.v.beautified Syntax.required_vo: Syntax.v 
Syntax.vio: Syntax.v 
Syntax.vos Syntax.vok Syntax.required_vos: Syntax.v 
Theorems.vo Theorems.glob Theorems.v.beautified Theorems.required_vo: Theorems.v Syntax.vo ConfigVars.vo MapTheorems.vo EvalRules.vo Transformations.vo
Theorems.vio: Theorems.v Syntax.vio ConfigVars.vio MapTheorems.vio EvalRules.vio Transformations.vio
Theorems.vos Theorems.vok Theorems.required_vos: Theorems.v Syntax.vos ConfigVars.vos MapTheorems.vos EvalRules.vos Transformations.vos
Transformations.vo Transformations.glob Transformations.v.beautified Transformations.required_vo: Transformations.v Syntax.vo ConfigVars.vo EvalRules.vo
Transformations.vio: Transformations.v Syntax.vio ConfigVars.vio EvalRules.vio
Transformations.vos Transformations.vok Transformations.required_vos: Transformations.v Syntax.vos ConfigVars.vos EvalRules.vos
