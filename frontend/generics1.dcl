definition module generics1

import checksupport
from transform import ::Group

convertGenerics :: 
		!Int 
		!NumberSet
		!{#CommonDefs} 
		!{!Group} 
		!*{# FunDef} 
		!*TypeDefInfos 
		!*Heaps 
		!*HashTable 
		!*PredefinedSymbols 
		!u:{# DclModule}
		!*ErrorAdmin 
	-> (  !{#CommonDefs}
		, !{!Group}
		, !*{# FunDef}
		, ![IndexRange]
		, !*TypeDefInfos
		, !*Heaps
		, !*HashTable
		, !*PredefinedSymbols
		, !u:{# DclModule}
		, !*ErrorAdmin
		)
