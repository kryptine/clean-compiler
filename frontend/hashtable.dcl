definition module hashtable

import syntax

::	.HashTableEntry 

::	HashTable =
	{	hte_symbol_heap	:: !.SymbolTable
	,	hte_entries		:: !.{! .HashTableEntry}
	,	hte_mark	:: !Int // 1 for .icl modules, otherwise 0
	}

newHashTable :: !*SymbolTable -> *HashTable

set_hte_mark :: !Int !*HashTable -> *HashTable

::	IdentClass	= IC_Expression
				| IC_Type
				| IC_TypeAttr
				| IC_Class
				| IC_Module
				| IC_Field !Ident
				| IC_Selector
				| IC_Instance ![Type]
				| IC_Generic
				| IC_GenericCase !Type
				| IC_GenericDeriveClass !Type
				| IC_Unknown

:: BoxedIdent = {boxed_ident::!Ident}

putIdentInHashTable :: !String !IdentClass !*HashTable -> (!BoxedIdent, !*HashTable)
putPredefinedIdentInHashTable :: !Ident !IdentClass !*HashTable -> *HashTable

remove_icl_symbols_from_hash_table :: !*HashTable -> *HashTable
