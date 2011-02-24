/*
	module owner: Ronny Wichers Schreur
*/
definition module convertDynamics

import syntax , checksupport
from transform import ::Group

:: TypeCodeVariableInfo
:: DynamicValueAliasInfo

convertDynamicPatternsIntoUnifyAppls :: !{# CommonDefs} !Int  {#DclModule} !IclModule [String] !Int !Int
		!*{!Group} !*{#FunDef} !*PredefinedSymbols !*VarHeap !*TypeHeaps !*ExpressionHeap !(Optional *File)
	-> (!*{#{#CheckedTypeDef}},
		!*{!Group},!*{#FunDef},!*PredefinedSymbols,!*VarHeap,!*TypeHeaps,!*ExpressionHeap,!(Optional *File))
