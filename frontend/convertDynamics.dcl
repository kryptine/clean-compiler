/*
	module owner: Martijn Vervoort
*/
definition module convertDynamics

import syntax, transform

:: TypeCodeVariableInfo
:: DynamicValueAliasInfo

convertDynamicPatternsIntoUnifyAppls :: {! GlobalTCType} !{# CommonDefs} !Int !*{! Group} !*{#FunDef} !*PredefinedSymbols !*VarHeap !*TypeHeaps !*ExpressionHeap (Optional *File) {# DclModule} !IclModule /* TD */ [String]
			-> (!*{! Group}, !*{#FunDef}, !*PredefinedSymbols, !*{#{# CheckedTypeDef}}, !ImportedConstructors, !*VarHeap, !*TypeHeaps, !*ExpressionHeap, Optional *File)
