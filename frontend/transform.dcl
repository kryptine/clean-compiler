definition module transform

import syntax, checksupport

::	Group =
	{	group_members	:: ![Int]
	}

partitionateAndLiftFunctions :: ![IndexRange] !Index !PredefinedSymbol !*{# FunDef} !u:{# DclModule} !*VarHeap !*ExpressionHeap !*SymbolTable !*ErrorAdmin
	-> (!*{! Group}, !*{# FunDef}, !u:{# DclModule}, !*VarHeap, !*ExpressionHeap,  !*SymbolTable, !*ErrorAdmin )

partitionateMacros :: !IndexRange !Index !PredefinedSymbol !*{# FunDef} !u:{# DclModule} !*VarHeap !*ExpressionHeap !*SymbolTable !*ErrorAdmin
	-> (!*{# FunDef}, !u:{# DclModule}, !*VarHeap, !*ExpressionHeap, !*SymbolTable, !*ErrorAdmin )

::	UnfoldState =
	{	us_var_heap				:: !.VarHeap
	,	us_symbol_heap			:: !.ExpressionHeap
	,	us_opt_type_heaps		:: !.Optional .TypeHeaps
	,	us_cleanup_info			:: ![ExprInfoPtr]
	,	us_handle_aci_free_vars	:: !AciFreeVarHandleMode
	}
	
:: AciFreeVarHandleMode = LeaveThem | RemoveThem | SubstituteThem

class unfold a :: !a !*UnfoldState -> (!a, !*UnfoldState)

instance unfold Expression, CasePatterns





















































