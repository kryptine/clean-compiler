/*
	module owner: Ronny Wichers Schreur
*/
definition module convertDynamics

import syntax , checksupport
from transform import ::Group

:: TypeCodeVariableInfo
:: DynamicValueAliasInfo

convertDynamicPatternsIntoUnifyAppls :: !{# CommonDefs} !Int !*{! Group} !*{#FunDef} !*PredefinedSymbols !*VarHeap !*TypeHeaps !*ExpressionHeap (Optional *File) {# DclModule} !IclModule /* TD */ [String]
			-> (!*{!Group}, !*{#FunDef}, !*PredefinedSymbols, !*{#{#CheckedTypeDef}}, !*VarHeap, !*TypeHeaps, !*ExpressionHeap, !Optional *File)
