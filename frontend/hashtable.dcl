definition module hashtable

import syntax

::	HashTableEntry 

::	HashTable =
	{	hte_symbol_heap	:: !.SymbolTable
	,	hte_entries		:: !.{! .HashTableEntry}
	}

newHashTable :: *HashTable

::	IdentClass	= IC_Expression
				| IC_Type
				| IC_TypeAttr
				| IC_Class
				| IC_Module
				| IC_Field !Ident
				| IC_Selector
				| IC_Instance ![Type]
				| IC_Unknown


putIdentInHashTable :: !String !IdentClass !*HashTable -> (!Ident, !*HashTable)

