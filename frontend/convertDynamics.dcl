definition module convertDynamics

import syntax, transform, convertcases

convertDynamicPatternsIntoUnifyAppls :: {! GlobalTCType} !{# CommonDefs} !*{! Group} !*{#FunDef} !*PredefinedSymbols
		!*{#{# CheckedTypeDef}} !ImportedFunctions !*VarHeap !*TypeHeaps !*ExpressionHeap
			-> (!*{! Group}, !*{#FunDef}, !*PredefinedSymbols, !*{#{# CheckedTypeDef}}, !ImportedConstructors, !*VarHeap, !*TypeHeaps, !*ExpressionHeap)
