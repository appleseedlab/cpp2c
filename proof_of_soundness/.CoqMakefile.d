ConfigVars.vo ConfigVars.glob ConfigVars.v.beautified ConfigVars.required_vo: ConfigVars.v Syntax.vo
ConfigVars.vio: ConfigVars.v Syntax.vio
ConfigVars.vos ConfigVars.vok ConfigVars.required_vos: ConfigVars.v Syntax.vos
EvalRules.vo EvalRules.glob EvalRules.v.beautified EvalRules.required_vo: EvalRules.v Syntax.vo ConfigVars.vo
EvalRules.vio: EvalRules.v Syntax.vio ConfigVars.vio
EvalRules.vos EvalRules.vok EvalRules.required_vos: EvalRules.v Syntax.vos ConfigVars.vos
Syntax.vo Syntax.glob Syntax.v.beautified Syntax.required_vo: Syntax.v 
Syntax.vio: Syntax.v 
Syntax.vos Syntax.vok Syntax.required_vos: Syntax.v 
Theorems.vo Theorems.glob Theorems.v.beautified Theorems.required_vo: Theorems.v Syntax.vo ConfigVars.vo EvalRules.vo Transformations.vo
Theorems.vio: Theorems.v Syntax.vio ConfigVars.vio EvalRules.vio Transformations.vio
Theorems.vos Theorems.vok Theorems.required_vos: Theorems.v Syntax.vos ConfigVars.vos EvalRules.vos Transformations.vos
Transformations.vo Transformations.glob Transformations.v.beautified Transformations.required_vo: Transformations.v Syntax.vo ConfigVars.vo EvalRules.vo
Transformations.vio: Transformations.v Syntax.vio ConfigVars.vio EvalRules.vio
Transformations.vos Transformations.vok Transformations.required_vos: Transformations.v Syntax.vos ConfigVars.vos EvalRules.vos
