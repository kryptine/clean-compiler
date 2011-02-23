definition module trans

import StdEnv

import syntax, transform
import classify, partition

transformGroups :: !CleanupInfo !Int !Int !Int !Int !*{!Group} !*{#FunDef} !*{!.ConsClasses} !{# CommonDefs}  !{# {# FunType} }
		!*ImportedTypes !*TypeDefInfos !*VarHeap !*TypeHeaps !*ExpressionHeap !Bool !*File !*PredefinedSymbols
			-> (!*{!Group}, !*{#FunDef}, !*ImportedTypes, !ImportedConstructors, !*VarHeap, !*TypeHeaps, !*ExpressionHeap, !*{!ConsClasses}, !*File, !*PredefinedSymbols)

convertSymbolType :: !Bool !{# CommonDefs} !SymbolType !Int !*ImportedTypes !ImportedConstructors !*TypeHeaps !*VarHeap 
	-> (!SymbolType, !*ImportedTypes, !ImportedConstructors, !*TypeHeaps, !*VarHeap)

convertSymbolTypeWithoutCollectingImportedConstructors :: !Bool !{# CommonDefs} !SymbolType !Int !*ImportedTypes !*TypeHeaps !*VarHeap 
	-> (!SymbolType, !*ImportedTypes, !*TypeHeaps, !*VarHeap)

addTypesOfDictionaries :: !{#CommonDefs} ![TypeContext] ![AType] -> [AType]
