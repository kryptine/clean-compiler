definition module explicitimports

import syntax, checksupport

:: ImportNrAndIdents =
	{	ini_symbol_nr	:: !Index
	,	ini_belonging	:: !Optional [ImportedIdent]
	}

:: SolvedImports =
	{	si_explicit	:: ![([Declaration], Position)]
	,	si_implicit	:: ![(Index, Position)]	// module indices
	}


solveExplicitImports :: !(IntKeyHashtable [(Int,Position,[ImportNrAndIdents])]) !{#Int} !Index 
				!*(!{#x:DclModule},!*{#Int},!{!*ExplImpInfo},!*CheckState)
			-> (!.SolvedImports,!(!{#x:DclModule},!.{#Int},!{!.ExplImpInfo},!.CheckState))
checkExplicitImportCompleteness :: ![(Declaration, Position)] !*{#DclModule} !*{#FunDef} !*ExpressionHeap !*CheckState
				-> (!.{#DclModule},!.{#FunDef},!.ExpressionHeap,!.CheckState)

