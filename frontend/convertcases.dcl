definition module convertcases

import syntax, transform, trans

::	ImportedFunctions 	:== [Global Index]

convertCasesOfFunctionsIntoPatterns :: !*{! Group} !{# {# FunType} } !{# CommonDefs} !*{#FunDef} !*{#{# CheckedTypeDef}}
		!ImportedConstructors !*VarHeap !*TypeHeaps !*ExpressionHeap
			-> (!ImportedFunctions, !*{! Group}, !*{#FunDef}, !*{#{# CheckedTypeDef}}, !ImportedConstructors, !*VarHeap, !*TypeHeaps, !*ExpressionHeap)

convertImportedTypeSpecifications :: !{# DclModule}  !{# {# FunType} } !{# CommonDefs} !ImportedConstructors !ImportedFunctions
	!*{# {#CheckedTypeDef}} !*TypeHeaps !*VarHeap -> (!*{#{#CheckedTypeDef}}, !*TypeHeaps, !*VarHeap)

convertDclModule :: !{# DclModule} !{# CommonDefs} !*{#{# CheckedTypeDef}} !ImportedConstructors !*VarHeap !*TypeHeaps
	-> (!*{#{# CheckedTypeDef}}, !ImportedConstructors, !*VarHeap, !*TypeHeaps)

convertIclModule :: !{# CommonDefs} !*{#{# CheckedTypeDef}} !ImportedConstructors !*VarHeap !*TypeHeaps
	-> (!*{#{# CheckedTypeDef}}, !ImportedConstructors, !*VarHeap, !*TypeHeaps)


newFunction :: !(Optional Ident) !FunctionBody ![FreeVar] ![AType] !AType !Int !(!Int, ![FunctionInfoPtr],!*FunctionHeap)
	-> (! SymbIdent, !(!Int, ![FunctionInfoPtr],!*FunctionHeap))


::	TypedVariable =
	{	tv_free_var	:: !FreeVar
	,	tv_type		:: !AType
	}

copyExpression :: ![TypedVariable] !Expression !*VarHeap -> (![Expression], ![TypedVariable], ![FreeVar], !Expression, !*VarHeap)

addNewFunctionsToGroups :: !{#.CommonDefs} FunctionHeap ![FunctionInfoPtr] !*{! Group} !*{#{# CheckedTypeDef}} !ImportedFunctions !*TypeHeaps !*VarHeap
	-> (!*{! Group}, ![FunDef],  !*{#{# CheckedTypeDef}}, !ImportedConstructors, !*TypeHeaps, !*VarHeap)

