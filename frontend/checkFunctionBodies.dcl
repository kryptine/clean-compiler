definition module checkFunctionBodies

import syntax, checksupport

::	ExpressionState =
	{	es_expr_heap	:: !.ExpressionHeap
	,	es_var_heap			:: !.VarHeap
	,	es_type_heaps		:: !.TypeHeaps
	,	es_calls			:: ![FunCall]
	,	es_dynamics			:: ![ExprInfoPtr]
	,	es_fun_defs			:: !.{# FunDef}
	}
	
::	ExpressionInput =
	{	ei_expr_level	:: !Level
	,	ei_fun_index	:: !Index
	,	ei_fun_level	:: !Level
	,	ei_mod_index	:: !Index
	}

checkFunctionBodies :: !FunctionBody !.ExpressionInput !*ExpressionState !*ExpressionInfo !*CheckState
					-> (FunctionBody,[FreeVar],!.ExpressionState,.ExpressionInfo,!.CheckState);
