definition module type

import StdArray
import syntax, check

typeProgram ::!{! Group} !Int !*{# FunDef} !IndexRange !(Optional Bool) !CommonDefs ![Declaration] !{# DclModule} !NumberSet !*Heaps !*PredefinedSymbols !*File !*File
	-> (!Bool, !*{# FunDef}, !IndexRange, {! GlobalTCType}, !{# CommonDefs}, !{# {# FunType} }, !.TypeDefInfos, !*Heaps, !*PredefinedSymbols, !*File, !*File)

addPropagationAttributesToAType :: {#CommonDefs} !AType !*PropState -> *(!AType,Int,!*PropState);

::	PropState =
	{	prop_type_heaps	:: !.TypeHeaps
	,	prop_td_infos	:: !.TypeDefInfos
	,	prop_attr_vars	:: ![AttributeVar]
	,	prop_attr_env	:: ![AttrInequality]
	,	prop_error		:: !.Optional .ErrorAdmin
	}

class unify a :: !a !a !TypeInput !*{! Type} !*TypeHeaps -> (!Bool, !*{! Type}, !*TypeHeaps)

instance unify AType

::	TypeInput =
	{	ti_common_defs	:: !{# CommonDefs }
	,	ti_functions	:: !{# {# FunType }}
	,	ti_main_dcl_module_n :: !Int
	}

class arraySubst type :: !type !u:{!Type} -> (!type, !u:{! Type})

instance arraySubst AType
