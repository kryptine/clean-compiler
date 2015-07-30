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

foldExpr :: 
		(Expression -> .st -> .st)  	// function to apply at each node
		Expression 						// expression to run throuh
		.st 							// state
	-> 
		.st								// updated state 

collectCalls :: !Index !Expression -> [FunCall]
