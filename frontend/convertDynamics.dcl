definition module convertDynamics

import syntax, checksupport

:: TypeCodeVariableInfo
:: DynamicValueAliasInfo

convertDynamicPatternsIntoUnifyAppls :: !{# CommonDefs} !Int  {#DclModule} !IclModule [String] !Int !Int
		!*{!Component} !*{#FunDef} !*PredefinedSymbols !*VarHeap !*TypeHeaps !*ExpressionHeap !(Optional *File)
	-> (!*{#{#CheckedTypeDef}},
		!*{!Component},!*{#FunDef},!*PredefinedSymbols,!*VarHeap,!*TypeHeaps,!*ExpressionHeap,!(Optional *File))
