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
					!*{#{# CheckedTypeDef}} !ImportedConstructors !*TypeDefInfos !*VarHeap !*TypeHeaps !*ExpressionHeap !Bool
				-> (!*{! Group}, !*{#FunDef}, !*{#{# CheckedTypeDef}}, !ImportedConstructors, !*VarHeap, !*TypeHeaps, !*ExpressionHeap)

partitionateFunctions :: !*{# FunDef} ![IndexRange] -> (!*{! Group}, !*{# FunDef})

::	ImportedConstructors	:== [Global Index]
::	ImportedFunctions	:== [Global Index]

convertSymbolType :: !Bool !{# CommonDefs} !SymbolType !Int !*{#{# CheckedTypeDef}} !ImportedConstructors !*TypeHeaps !*VarHeap 
	-> (!SymbolType, !*{#{# CheckedTypeDef}}, !ImportedConstructors, !*TypeHeaps, !*VarHeap)

addTypesOfDictionaries :: !{#CommonDefs} ![TypeContext] ![AType] -> [AType]
