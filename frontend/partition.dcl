definition module partition

import syntax, transform

partitionateFunctions :: !*{# FunDef} ![IndexRange] -> (!*{! Group}, !*{# FunDef})

//partitionateFunctions` :: !*{# FunDef} ![IndexRange] !Index !Int !Int -> (!*{! Group}, !*{# FunDef})
partitionateFunctions` :: !*{# FunDef} ![IndexRange] !Index !Int !Int !*PredefinedSymbols !*VarHeap !*ExpressionHeap !*ErrorAdmin -> (!*{! Group}, !*{# FunDef}, !*PredefinedSymbols, !*VarHeap, !*ExpressionHeap, !*ErrorAdmin)

stripStrictLets :: !*{# FunDef} !*PredefinedSymbols !*VarHeap !*ExpressionHeap !*ErrorAdmin -> (!*{# FunDef}, !*PredefinedSymbols, !*VarHeap, !*ExpressionHeap, !*ErrorAdmin)

partitionateFunctions`` :: !Int !Int ![FunctionInfoPtr] !*{# FunDef} ![Int] !Index !Int !Int !*FunctionHeap
	-> (!Int, ![Group], !*{# FunDef}, !*FunctionHeap)