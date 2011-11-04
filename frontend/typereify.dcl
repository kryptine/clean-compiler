/*
	module owner: Ronny Wichers Schreur
*/
definition module typereify

from syntax import
	::Ident, ::FunDef, ::IndexRange, ::TypeHeaps,
	::SymbolTable, ::SymbolTableEntry, ::Heap,
	::DclModule, ::CommonDefs, ::VarHeap, ::VarInfo
from predef import
	::PredefinedSymbols, ::PredefinedSymbol

addTypeFunctions :: Ident Int *{#DclModule} *{#FunDef} *CommonDefs *PredefinedSymbols *VarHeap *SymbolTable
			  -> (IndexRange, *{#DclModule},*{#FunDef},*CommonDefs,*PredefinedSymbols,*VarHeap,*SymbolTable)

buildTypeFunctions :: !Int !*{#FunDef} !{#CommonDefs} *PredefinedSymbols *VarHeap *TypeHeaps
									  -> (*{#FunDef}, *PredefinedSymbols,*VarHeap,*TypeHeaps)

sanityCheckTypeFunctions :: !Int !CommonDefs !{#DclModule} !{#FunDef}
	->	Bool
