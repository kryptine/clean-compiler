definition module explicitimports

import syntax, checksupport

temporary_import_solution_XXX yes no :== yes
// to switch between importing modes.
// iff this is yes, then explicit imports happen in the old Clean 1.3 fashion.
// This feature will be removed, when all programs are ported to Clean 2.0. The last Constructors of AtomType
// and StructureType should then be removed also

// MW2 everything changed in this dcl
::	FunctionConsequence

possibly_filter_decls :: .[ImportDeclaration] u:[w:(.Index,y:Declarations)] (.FileName,.LineNr) *{#.DclModule} *CheckState -> (v:[x:(Index,z:Declarations)],.{#DclModule},.CheckState), [y <= z, w <= x, u <= v];
check_completeness_of_module :: .Index [(.Declaration,.Int)] .String *(*{!.FunctionConsequence},*{#.DclModule},*{#FunDef},*ExpressionHeap,*CheckState) -> (.{!FunctionConsequence},.{#DclModule},.{#FunDef},.ExpressionHeap,.CheckState);
check_completeness_of_all_dcl_modules	:: !*{#DclModule} !*{#FunDef} !*ExpressionHeap !*CheckState
									-> (!Int, !(!*{!FunctionConsequence}, !*{#DclModule}, !*{#FunDef}, !*ExpressionHeap, !*CheckState))
