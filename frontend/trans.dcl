definition module trans

import StdEnv

import syntax, transform

cPassive   				:== -1
cActive					:== -2
cAccumulating   		:== -3
cVarOfMultimatchCase	:== -4

::	CleanupInfo

analyseGroups	:: !{# CommonDefs} !{#{#FunType}} !IndexRange !Int !Int !*{! Group} !*{#FunDef} !*VarHeap !*ExpressionHeap 
				-> (!CleanupInfo, !*{! ConsClasses}, !*{! Group}, !*{#FunDef}, !*VarHeap, !*ExpressionHeap)

transformGroups :: !CleanupInfo !Int !Int !*{! Group} !*{#FunDef} !*{!.ConsClasses} !{# CommonDefs}  !{# {# FunType} }
					!*ImportedTypes !ImportedConstructors !*TypeDefInfos !*VarHeap !*TypeHeaps !*ExpressionHeap !Bool
				-> (!*{! Group}, !*{#FunDef}, !*ImportedTypes, !ImportedConstructors, !*VarHeap, !*TypeHeaps, !*ExpressionHeap, !*{!ConsClasses})

partitionateFunctions :: !*{# FunDef} ![IndexRange] -> (!*{! Group}, !*{# FunDef})

::	ImportedConstructors	:== [Global Index]
::	ImportedFunctions		:== [Global Index]
::	ImportedTypes			:== {#{# CheckedTypeDef}}

convertSymbolType :: !Bool !{# CommonDefs} !SymbolType !Int !*ImportedTypes !ImportedConstructors !*TypeHeaps !*VarHeap 
	-> (!SymbolType, !*ImportedTypes, !ImportedConstructors, !*TypeHeaps, !*VarHeap)

addTypesOfDictionaries :: !{#CommonDefs} ![TypeContext] ![AType] -> [AType]
