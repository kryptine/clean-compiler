definition module convertDynamics

import syntax, transform, convertcases


convertDynamicPatternsIntoUnifyAppls :: {! GlobalTCType} !{# CommonDefs} !Int !*{! Group} !*{#FunDef} !*PredefinedSymbols !*VarHeap !*TypeHeaps !*ExpressionHeap
			-> (!*{! Group}, !*{#FunDef}, !*PredefinedSymbols, !*{#{# CheckedTypeDef}}, !ImportedConstructors, !*VarHeap, !*TypeHeaps, !*ExpressionHeap)

/*
convertDynamicPatternsIntoUnifyAppls :: {! GlobalTCType} !{# CommonDefs} !*{! Group} !*{#FunDef} !*PredefinedSymbols
		!*{#{# CheckedTypeDef}} !ImportedConstructors !*VarHeap !*TypeHeaps !*ExpressionHeap
			-> (!*{! Group}, !*{#FunDef}, !*PredefinedSymbols, !*{#{# CheckedTypeDef}}, !ImportedConstructors, !*VarHeap, !*TypeHeaps, !*ExpressionHeap)
*/

instance toString GlobalTCType
instance toString BasicType