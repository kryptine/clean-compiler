implementation module hashtable

import predef, syntax, StdCompare, compare_constructor


::	HashTableEntry	= HTE_Ident !String !SymbolPtr !IdentClass !HashTableEntry !HashTableEntry
					| HTE_Empty 

::	HashTable =
	{	hte_symbol_heap	:: !.SymbolTable
	,	hte_entries		:: !.{! .HashTableEntry}
	}

::	IdentClass	= IC_Expression
				| IC_Type
				| IC_TypeAttr
				| IC_Class
				| IC_Module
				| IC_Field !Ident
				| IC_Selector
				| IC_Instance ![Type]
				| IC_Unknown

newHashTable :: *HashTable
newHashTable = { hte_symbol_heap = newHeap, hte_entries = {  HTE_Empty \\ i <- [0 .. dec cHashTableSize] }}

instance =< IdentClass
where
	(=<) (IC_Instance types1) (IC_Instance types2)
		= compare_types types1 types2
	where
		compare_types [t1 : t1s] [t2 : t2s]
			# cmp = t1 =< t2
			| cmp == Equal
				= t1s =< t2s
				= cmp
		compare_types [] []
			= Equal
		compare_types [] _
			= Smaller
		compare_types _ []
			= Greater
	(=<) (IC_Field typ_id1) (IC_Field typ_id2)
		= typ_id1 =< typ_id2
	(=<) ic1 ic2
		| equal_constructor ic1 ic2
			= Equal
		| less_constructor ic1 ic2
			= Smaller
			= Greater

instance =< (!a,!b) |  =< a &  =< b
where
	(=<) (x1,y1) (x2,y2)
		# cmp = x1 =< x2
		| cmp == Equal
			= y1 =< y2
			= cmp

cHashTableSize	:==	1023

hashValue :: !String -> Int
hashValue name
	# hash_val = hash_value name (size name) 0 mod cHashTableSize
	| hash_val < 0
		= hash_val + cHashTableSize
		= hash_val
where
	hash_value :: !String !Int !Int -> Int
	hash_value name index val
		| index == 0
			= val
		# index = dec index
		  char = name.[index]
		= hash_value name index (val << 2 + toInt char)

putIdentInHashTable :: !String !IdentClass !*HashTable -> (!Ident, !*HashTable)
putIdentInHashTable name indent_class {hte_symbol_heap,hte_entries}
	# hash_val = hashValue name
	  (entries,hte_entries) = replace hte_entries hash_val HTE_Empty
	  (ident, hte_symbol_heap, entries) = insert name indent_class hte_symbol_heap entries
	  (_,hte_entries) = replace hte_entries hash_val entries
	= (ident, { hte_symbol_heap = hte_symbol_heap, hte_entries = hte_entries })

where
	insert ::  !String !IdentClass !*SymbolTable *HashTableEntry -> (!Ident, !*SymbolTable, !*HashTableEntry)
	insert name indent_class hte_symbol_heap HTE_Empty
		# (hte_symbol_ptr, hte_symbol_heap) = newPtr EmptySymbolTableEntry hte_symbol_heap
		= ({ id_name = name, id_info = hte_symbol_ptr}, hte_symbol_heap, HTE_Ident name hte_symbol_ptr indent_class HTE_Empty HTE_Empty)
	insert name indent_class hte_symbol_heap (HTE_Ident hte_name hte_symbol_ptr hte_class hte_left hte_right)
		# cmp = (name,indent_class) =< (hte_name,hte_class)
		| cmp == Equal
			= ({ id_name = hte_name, id_info = hte_symbol_ptr}, hte_symbol_heap, HTE_Ident hte_name hte_symbol_ptr hte_class hte_left hte_right)
		| cmp == Smaller
			#! (ident, hte_symbol_heap, hte_left) = insert name indent_class hte_symbol_heap hte_left
			= (ident, hte_symbol_heap, HTE_Ident hte_name hte_symbol_ptr hte_class hte_left hte_right)
			#! (ident, hte_symbol_heap, hte_right) = insert name indent_class hte_symbol_heap hte_right
			= (ident, hte_symbol_heap, HTE_Ident hte_name hte_symbol_ptr hte_class hte_left hte_right)

