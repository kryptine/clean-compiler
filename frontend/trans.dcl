definition module trans

import StdEnv

import syntax, transform

cPassive   		:== -1
cActive			:== -2
cAccumulating   :== -3

analyseGroups :: !*{! Group} !*{#FunDef} !*VarHeap -> (!*{! ConsClasses}, !*{! Group}, !*{#FunDef}, !*VarHeap)

transformGroups :: !*{! Group} !*{#FunDef} !{!.ConsClasses} !{# CommonDefs}  !{# {# FunType} } !*VarHeap !*TypeHeaps !*ExpressionHeap
	-> (!*{! Group}, !*{#FunDef}, !*{#{# CheckedTypeDef}}, !ImportedConstructors, !*VarHeap, !*TypeHeaps, !*ExpressionHeap)

partitionateFunctions :: !*{# FunDef} ![IndexRange] -> (!*{! Group}, !*{# FunDef})

::	ImportedConstructors	:== [Global Index]

convertSymbolType :: !{# CommonDefs} !SymbolType !*{#{# CheckedTypeDef}} !ImportedConstructors !*TypeHeaps !*VarHeap
	-> (!SymbolType, !*{#{# CheckedTypeDef}}, !ImportedConstructors, !*TypeHeaps, !*VarHeap)
