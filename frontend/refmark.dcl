definition module refmark

import syntax, checksupport, unitype

makeSharedReferencesNonUnique :: ![Int] !u:{# FunDef} !*Coercions !w:{! Type} !{# CommonDefs } !*VarHeap !*ExpressionHeap !*ErrorAdmin
	-> (!u:{# FunDef}, !*Coercions, !w:{! Type}, !*VarHeap, !*ExpressionHeap, !*ErrorAdmin)
