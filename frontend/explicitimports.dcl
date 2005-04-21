definition module explicitimports

import syntax, checksupport

:: ImportNrAndIdents =
	{	ini_symbol_nr	:: !Index
	,	ini_imp_decl	:: !ImportDeclaration
	}

:: SolvedImports =
	{	si_explicit	:: ![([Declaration], Position)]
	,	si_implicit	:: ![(Index, Position)]	// module indices
	}


markExplImpSymbols :: !Int !*(!*{!*{!u:ExplImpInfo}}, !*SymbolTable)
			-> (!.[Ident],!(!{!{!u:ExplImpInfo}},!.SymbolTable))

updateExplImpForMarkedSymbol :: !Index !Declaration !SymbolTableEntry !u:{#DclModule} !{!{!*ExplImpInfo}} !*SymbolTable
			-> (!u:{#DclModule}, !{!{!.ExplImpInfo}}, !.SymbolTable)

solveExplicitImports :: !(IntKeyHashtable [(Int,Position,[ImportNrAndIdents])]) !{#Int} !Index 
								!*(!v:{#DclModule},!*{#Int},!{!*ExplImpInfo},!*CheckState)
			-> (!.SolvedImports,! (!v:{#DclModule},!.{#Int},!{!.ExplImpInfo},!.CheckState))

checkExplicitImportCompleteness :: ![([Declaration], Position)] !*{#DclModule} !*{#FunDef} !*{#*{#FunDef}} !*ExpressionHeap !*CheckState
															-> (!.{#DclModule},!.{#FunDef},!*{#*{#FunDef}},!.ExpressionHeap,!.CheckState)

