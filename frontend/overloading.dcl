definition module overloading

import StdEnv
import syntax, check, typesupport

::	InstanceTree = IT_Node !(Global Index) !InstanceTree !InstanceTree | IT_Empty 

::	ClassInstanceInfo :== {# {! .InstanceTree}}

::	ArrayInstance =
	{	ai_record		:: !TypeSymbIdent
	,	ai_members		:: !{# DefinedSymbol}
	}

::	GlobalTCInstance =
	{	gtci_type		:: !GlobalTCType
	,	gtci_index		:: !Index
	}

::	SpecialInstances =
	{	si_next_array_member_index			:: !Index
	,	si_array_instances					:: ![ArrayInstance]
	,	si_next_TC_member_index				:: !Index
	,	si_TC_instances						:: ![GlobalTCInstance]
	}
	
::	OverloadingState =
	{	os_type_heaps			:: !.TypeHeaps
	,	os_var_heap				:: !.VarHeap
	,	os_symbol_heap			:: !.ExpressionHeap
	,	os_predef_symbols		:: !.PredefinedSymbols
	,	os_special_instances	:: !.SpecialInstances
	,	os_error				:: !.ErrorAdmin				
	}

::	LocalTypePatternVariable
::	DictionaryTypes :== [(Index, [ExprInfoPtr])]

tryToSolveOverloading :: ![(Optional [TypeContext], [ExprInfoPtr], IdentPos, Index)] !Int !{# CommonDefs } !ClassInstanceInfo !*Coercions !*OverloadingState
	-> (![TypeContext], !*Coercions, ![LocalTypePatternVariable], DictionaryTypes, !*OverloadingState)

::	TypeCodeInfo =
	{	tci_next_index			:: !Index
	,	tci_instances			:: ![GlobalTCInstance]
	,	tci_type_var_heap		:: !.TypeVarHeap
	}

removeOverloadedFunctions :: ![Index] ![LocalTypePatternVariable] !Int !*{#FunDef} !*{! FunctionType} !*ExpressionHeap
	!*TypeCodeInfo !*VarHeap !*ErrorAdmin !*{#PredefinedSymbol} //!*{#PredefinedSymbol}
		-> (!*{#FunDef}, !*{! FunctionType}, !*ExpressionHeap, !*TypeCodeInfo, !*VarHeap, !*ErrorAdmin, !*{#PredefinedSymbol})

updateDynamics :: ![Index] ![LocalTypePatternVariable] !Int !*{#FunDef} !*{! FunctionType} !*ExpressionHeap !*TypeCodeInfo !*VarHeap !*ErrorAdmin !*{#PredefinedSymbol}
	-> (!*{#FunDef}, !*{! FunctionType}, !*ExpressionHeap, !*TypeCodeInfo, !*VarHeap, !*ErrorAdmin, !*{#PredefinedSymbol})
