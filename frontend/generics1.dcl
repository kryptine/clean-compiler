definition module generics1

import checksupport
/*2.0
from transform import ::Group
0.2*/
//1.3
from transform import Group
//3.1

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
