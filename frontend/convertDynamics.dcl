/*
	module owner: Martijn Vervoort
*/
definition module convertDynamics

import syntax , checksupport
from transform import ::Group
:: TypeCodeVariableInfo
:: DynamicValueAliasInfo

convertDynamicPatternsIntoUnifyAppls :: !{# CommonDefs} !Int !*{! Group} !*{#FunDef} !*PredefinedSymbols !*VarHeap !*TypeHeaps !*ExpressionHeap (Optional *File) {# DclModule} !IclModule /* TD */ [String]
			-> (!*{! Group}, !*{#FunDef}, !*PredefinedSymbols, !*{#{# CheckedTypeDef}}, !ImportedConstructors, !*VarHeap, !*TypeHeaps, !*ExpressionHeap, Optional *File)
