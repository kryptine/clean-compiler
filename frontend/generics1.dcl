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
		!*{#*{#FunDef}}
		!*ErrorAdmin
	-> (  !{#CommonDefs}
		, !{!Group}
		, !*{# FunDef}
		, !*TypeDefInfos
		, !*Heaps
		, !*HashTable
		, !*PredefinedSymbols
		, !u:{# DclModule}
		, !*{#*{#FunDef}}
		, !*ErrorAdmin
		)

collectVars :: 
		!Expression 	// expression to collect variables in
		![FreeVar] 		// function argument variables
	-> (  ![FreeVar]	// argument variables (with updated ref count)
		, ![FreeVar]	// local variables
		, ![FreeVar]	// free_variables
		)

collectCalls :: !Index !Expression -> 	[FunCall]
