definition module explicitimports

import syntax, checksupport

temporary_import_solution_XXX yes no :== yes
// to switch between importing modes.
// iff this is yes, then explicit imports happen in the old Clean 1.3 fashion.
// This feature will be removed, when all programs are ported to Clean 2.0. The last Constructors of AtomType
// and StructureType should then be removed also

possibly_filter_decls :: ![ImportDeclaration] ![(!Index,!Declarations)] !(!FileName,!LineNr) !*{#DclModule} !*CheckState 
						-> (![(!Index,!Declarations)],!.{#DclModule},!.CheckState)
checkExplicitImportCompleteness :: !String ![(!Declaration,!Int)]
									!*{#DclModule} !*{#FunDef} !*ExpressionHeap !*CheckState 
								-> (!.{#DclModule},!.{#FunDef},!.ExpressionHeap,!.CheckState)
