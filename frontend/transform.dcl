definition module transform

import syntax, checksupport

::	Group =
	{	group_members	:: ![Int]
	}

partitionateAndLiftFunctions :: ![IndexRange] !Index !PredefinedSymbol !*{# FunDef} !*{# DclModule} !*VarHeap !*ExpressionHeap !*SymbolTable !*ErrorAdmin
	-> (!*{! Group}, !*{# FunDef}, !.{# DclModule}, !*VarHeap, !*ExpressionHeap,  !*SymbolTable, !*ErrorAdmin )

partitionateMacros :: !IndexRange !Index !PredefinedSymbol !*{# FunDef} !*{# DclModule} !*VarHeap !*ExpressionHeap !*SymbolTable !*ErrorAdmin
	-> (!*{# FunDef}, !.{# DclModule}, !*VarHeap, !*ExpressionHeap, !*SymbolTable, !*ErrorAdmin )

::	CopiedLocalFunctions

::	UnfoldState =
	{	us_var_heap				:: !.VarHeap
	,	us_symbol_heap			:: !.ExpressionHeap
	,	us_opt_type_heaps		:: !.Optional .TypeHeaps,
		us_cleanup_info			:: ![ExprInfoPtr],
		us_local_macro_functions :: !Optional CopiedLocalFunctions
	}

::	UnfoldInfo =
	{	ui_handle_aci_free_vars	:: !AciFreeVarHandleMode,
		ui_convert_module_n :: !Int, // -1 if no conversion
		ui_conversion_table :: !Optional ConversionTable
	}

:: AciFreeVarHandleMode = LeaveThem | RemoveThem | SubstituteThem

class unfold a :: !a !UnfoldInfo !*UnfoldState -> (!a, !*UnfoldState)

instance unfold Expression, CasePatterns
