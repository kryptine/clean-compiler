definition module trans

import StdEnv

import syntax, transform

cPassive   		:== -1
cActive			:== -2
cAccumulating   :== -3

::	CleanupInfo

analyseGroups	:: !{# CommonDefs} !IndexRange !*{! Group} !*{#FunDef} !*VarHeap !*ExpressionHeap 
				-> (!CleanupInfo, !*{! ConsClasses}, !*{! Group}, !*{#FunDef}, !*VarHeap, !*ExpressionHeap)

transformGroups :: !CleanupInfo !*{! Group} !*{#FunDef} !{!.ConsClasses} !{# CommonDefs}  !{# {# FunType} }
		!*{#{# CheckedTypeDef}} !ImportedConstructors !*VarHeap !*TypeHeaps !*ExpressionHeap
			-> (!*{! Group}, !*{#FunDef}, !*{#{# CheckedTypeDef}}, !ImportedConstructors, !*VarHeap, !*TypeHeaps, !*ExpressionHeap)

partitionateFunctions :: !*{# FunDef} ![IndexRange] -> (!*{! Group}, !*{# FunDef})

::	ImportedConstructors	:== [Global Index]

convertSymbolType :: !{# CommonDefs} !SymbolType !*{#{# CheckedTypeDef}} !ImportedConstructors !*TypeHeaps !*VarHeap
	-> (!SymbolType, !*{#{# CheckedTypeDef}}, !ImportedConstructors, !*TypeHeaps, !*VarHeap)

// MV ..
addTypesOfDictionaries :: w:(a x:CommonDefs) .[TypeContext] u:[AType] -> v:[AType] | Array .a, [u <= v, w <= x];
// .. MV