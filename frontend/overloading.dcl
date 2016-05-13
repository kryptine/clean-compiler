definition module overloading

import StdEnv
import syntax, typesupport
from unitype import ::BOOLVECT

::	InstanceTree = IT_Node !(Global Index) !InstanceTree !InstanceTree | IT_Empty 

::	ClassInstanceInfo :== {# {! .InstanceTree}}

::	ArrayInstance =
	{	ai_record		:: !TypeSymbIdent
	,	ai_members		:: !{#ClassInstanceMember}
	}

::	GlobalTCInstance =
	{	gtci_type		:: !GlobalTCType
	,	gtci_index		:: !Index
	}

::	SpecialInstances =
	{	si_next_array_member_index			:: !Index
	,	si_array_instances					:: ![ArrayInstance]
	,	si_list_instances					:: ![ArrayInstance]
	,	si_tail_strict_list_instances		:: ![ArrayInstance]
	}
	
::	OverloadingState =
	{	os_type_heaps			:: !.TypeHeaps
	,	os_var_heap				:: !.VarHeap
	,	os_symbol_heap			:: !.ExpressionHeap
	,	os_generic_heap			:: !.GenericHeap
	,	os_predef_symbols		:: !.PredefinedSymbols
	,	os_special_instances	:: !.SpecialInstances
	,	os_error				:: !.ErrorAdmin				
	}

::	LocalTypePatternVariable
::	DictionaryTypes :== [(Index, [ExprInfoPtr])]

:: ReducedOverloadedApplication
:: ReducedOverloadedContext

finishContextReduction :: ![ReducedOverloadedContext] ![ExprInfoPtr] !Int !{# CommonDefs } 
	!*VarHeap !*TypeHeaps !*ExpressionHeap  !*PredefinedSymbols !*SpecialInstances !*Coercions !*{!Type} !*ErrorAdmin
	-> (![ReducedOverloadedApplication], ![TypeContext], ![LocalTypePatternVariable], !*VarHeap, !*TypeHeaps, !*ExpressionHeap, !*PredefinedSymbols,
		!*SpecialInstances , !*Coercions, !*{!Type}, !*ErrorAdmin)

startContextReduction :: ![OverloadedExpressions] ![[TypeContext]] !{# CommonDefs } !ClassInstanceInfo 
	!*VarHeap !*TypeHeaps !*ExpressionHeap  !*PredefinedSymbols !*{!Type} !*ErrorAdmin
	-> (![ReducedOverloadedContext], ![ExprInfoPtr], !*VarHeap, !*TypeHeaps, !*ExpressionHeap, !*PredefinedSymbols, !*{!Type}, !*ErrorAdmin)

addDictionaries :: ![[TypeContext]] ![TypeContext] ![ReducedOverloadedApplication] !{# CommonDefs } 
	!*Heaps !*{!Type} !*ErrorAdmin -> (![TypeContext], !DictionaryTypes, !*Heaps, !*{!Type}, !*ErrorAdmin)

uniqueError :: a b *ErrorAdmin -> *ErrorAdmin | writeType b & <<< a

::	OverloadedExpressions = 
	{	oe_expr_ptrs	:: ![ExprInfoPtr]
	,	oe_fun_index	:: !Index
	}

::	TypeCodeInfo =
	{	tci_type_var_heap					:: !.TypeVarHeap
	,	tci_attr_var_heap					:: !.AttrVarHeap
	,	tci_dcl_modules						:: !{# DclModule}
	,	tci_common_defs						:: !{# CommonDefs }
	}

liftNewVarSubstitutions :: ![ReducedOverloadedContext] !Int !*{!Type} -> (!*{#BOOLVECT},!*{!Type})

removeOverloadedFunctions :: ![Index] ![LocalTypePatternVariable] !Int !*{#FunDef} !*{! FunctionType} !*ExpressionHeap
	!*TypeCodeInfo !*VarHeap !*ErrorAdmin !*{#PredefinedSymbol} //!*{#PredefinedSymbol}
		-> (!*{#FunDef}, !*{! FunctionType}, !*ExpressionHeap, !*TypeCodeInfo, !*VarHeap, !*ErrorAdmin, !*{#PredefinedSymbol})

removeOverloadedFunctionsWithoutUpdatingFunctions :: ![Index] ![LocalTypePatternVariable] !Int !*{#FunDef} !*{! FunctionType} !*ExpressionHeap
	!*TypeCodeInfo !*VarHeap !*ErrorAdmin !*{#PredefinedSymbol} //!*{#PredefinedSymbol}
		-> (!*{#FunDef}, !*{! FunctionType}, !*ExpressionHeap, !*TypeCodeInfo, !*VarHeap, !*ErrorAdmin, !*{#PredefinedSymbol})

::	Subst =
	{	subst_changed	:: !Bool
	,	subst_array		:: !.{!Type}
	,	subst_next_var_n :: !Int
	,	subst_previous_context_n :: !Int
	,	subst_context_n_at_last_update :: !Int
	}

find_instance :: [Type] !InstanceTree {#CommonDefs} *TypeHeaps !*Subst -> *(!Global Int, ![TypeContext], !*TypeHeaps, !*Subst)
