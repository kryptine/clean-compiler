implementation module hashtable

import predef, syntax, StdCompare, compare_constructor

::	HashTableEntry
		= HTE_Ident !BoxedIdent !IdentClass !Int !HashTableEntry !HashTableEntry
		| HTE_Empty 

::	HashTable =
	{	hte_symbol_heap	:: !.SymbolTable
	,	hte_entries		:: !.{! .HashTableEntry}
	,	hte_mark	:: !Int // 1 for .icl modules, otherwise 0
	}

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

newHashTable :: !*SymbolTable -> *HashTable
newHashTable symbol_heap = { hte_symbol_heap = symbol_heap, hte_entries = {  HTE_Empty \\ i <- [0 .. dec cHashTableSize] },hte_mark=0}

set_hte_mark :: !Int !*HashTable -> *HashTable
set_hte_mark hte_mark ht = {ht & hte_mark=hte_mark}

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
	(=<) (IC_GenericCase type1) (IC_GenericCase type2)
		= type1 =< type2
	(=<) (IC_GenericDeriveClass type1) (IC_GenericDeriveClass type2)
		= type1 =< type2
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
	# hash_val = hash_value name (size name) 0 rem cHashTableSize
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

putIdentInHashTable :: !String !IdentClass !*HashTable -> (!BoxedIdent, !*HashTable)
putIdentInHashTable name ident_class {hte_symbol_heap,hte_entries,hte_mark}
	# hash_val = hashValue name
	  (entries,hte_entries) = replace hte_entries hash_val HTE_Empty
	  (ident, hte_symbol_heap, entries) = insert name ident_class hte_mark hte_symbol_heap entries
	  hte_entries = update hte_entries hash_val entries
	= (ident, { hte_symbol_heap = hte_symbol_heap, hte_entries = hte_entries,hte_mark=hte_mark })
where
	insert ::  !String !IdentClass !Int !*SymbolTable *HashTableEntry -> (!BoxedIdent, !*SymbolTable, !*HashTableEntry)
	insert name ident_class hte_mark0 hte_symbol_heap HTE_Empty
		# (hte_symbol_ptr, hte_symbol_heap) = newPtr EmptySymbolTableEntry hte_symbol_heap
		# ident = { id_name = name, id_info = hte_symbol_ptr}
		# boxed_ident={boxed_ident=ident}
		= (boxed_ident, hte_symbol_heap, HTE_Ident boxed_ident ident_class hte_mark0 HTE_Empty HTE_Empty)
	insert name ident_class hte_mark0 hte_symbol_heap (HTE_Ident hte_ident=:{boxed_ident={id_name,id_info}} hte_class hte_mark hte_left hte_right)
		# cmp = (name,ident_class) =< (id_name,hte_class)
		| cmp == Equal
			= (hte_ident, hte_symbol_heap, HTE_Ident hte_ident hte_class (hte_mark bitand hte_mark0) hte_left hte_right)
		| cmp == Smaller
			#! (boxed_ident, hte_symbol_heap, hte_left) = insert name ident_class hte_mark0 hte_symbol_heap hte_left
			= (boxed_ident, hte_symbol_heap, HTE_Ident hte_ident hte_class hte_mark hte_left hte_right)
			#! (boxed_ident, hte_symbol_heap, hte_right) = insert name ident_class hte_mark0 hte_symbol_heap hte_right
			= (boxed_ident, hte_symbol_heap, HTE_Ident hte_ident hte_class hte_mark hte_left hte_right)

putPredefinedIdentInHashTable :: !Ident !IdentClass !*HashTable -> *HashTable
putPredefinedIdentInHashTable predefined_ident=:{id_name} ident_class {hte_symbol_heap,hte_entries,hte_mark}
	# hash_val = hashValue id_name
	  (entries,hte_entries) = replace hte_entries hash_val HTE_Empty
	  (hte_symbol_heap, entries) = insert id_name ident_class hte_mark hte_symbol_heap entries
	  hte_entries = update hte_entries hash_val entries
	= { hte_symbol_heap = hte_symbol_heap, hte_entries = hte_entries,hte_mark=hte_mark }
where
	insert ::  !String !IdentClass !Int !*SymbolTable *HashTableEntry -> (!*SymbolTable, !*HashTableEntry)
	insert name ident_class hte_mark0 hte_symbol_heap HTE_Empty
		# hte_symbol_heap = writePtr predefined_ident.id_info EmptySymbolTableEntry hte_symbol_heap
		# boxed_ident={boxed_ident=predefined_ident}
		= (hte_symbol_heap, HTE_Ident boxed_ident ident_class hte_mark0 HTE_Empty HTE_Empty)
	insert name ident_class hte_mark0 hte_symbol_heap (HTE_Ident hte_ident=:{boxed_ident={id_name,id_info}} hte_class hte_mark hte_left hte_right)
		# cmp = (name,ident_class) =< (id_name,hte_class)
		| cmp == Equal
			= (hte_symbol_heap, HTE_Ident hte_ident hte_class (hte_mark bitand hte_mark0) hte_left hte_right)
		| cmp == Smaller
			#! (hte_symbol_heap, hte_left) = insert name ident_class hte_mark0 hte_symbol_heap hte_left
			= (hte_symbol_heap, HTE_Ident hte_ident hte_class hte_mark hte_left hte_right)
			#! (hte_symbol_heap, hte_right) = insert name ident_class hte_mark0 hte_symbol_heap hte_right
			= (hte_symbol_heap, HTE_Ident hte_ident hte_class hte_mark hte_left hte_right)

remove_icl_symbols_from_hash_table :: !*HashTable -> *HashTable
remove_icl_symbols_from_hash_table hash_table=:{hte_entries}
	# hte_entries=remove_icl_symbols_from_array 0 hte_entries
	= {hash_table & hte_entries=hte_entries}
	where
		remove_icl_symbols_from_array i hte_entries
			 | i<size hte_entries
			 	# (entries,hte_entries) = replace hte_entries i HTE_Empty
				# (_,entries) = remove_icl_entries_from_tree entries
				# hte_entries = update hte_entries i entries
				= remove_icl_symbols_from_array (i+1) hte_entries
				= hte_entries

		// a tuple with a dummy value is used to change the calling convention to improve reuse of nodes
		remove_icl_entries_from_tree :: !*HashTableEntry -> (!Int,!.HashTableEntry);
		remove_icl_entries_from_tree HTE_Empty
			= (0,HTE_Empty)
		remove_icl_entries_from_tree (HTE_Ident hte_ident hte_class 0 hte_left hte_right)
			# (_,hte_left) = remove_icl_entries_from_tree hte_left
			# (_,hte_right) = remove_icl_entries_from_tree hte_right
			= (0,HTE_Ident hte_ident hte_class 0 hte_left hte_right)
		remove_icl_entries_from_tree (HTE_Ident hte_ident hte_class _ hte_left hte_right)
			# (depth_left,hte_left) = remove_icl_entries_from_tree_and_compute_depth hte_left
			# (depth_right,hte_right) = remove_icl_entries_from_tree_and_compute_depth hte_right
			= merge_trees hte_left hte_right depth_left depth_right

		remove_icl_entries_from_tree_and_compute_depth :: !*HashTableEntry -> (!Int,!.HashTableEntry);
		remove_icl_entries_from_tree_and_compute_depth HTE_Empty
			= (0,HTE_Empty)
		remove_icl_entries_from_tree_and_compute_depth (HTE_Ident hte_ident hte_class 0 hte_left hte_right)
			# (depth_left,hte_left) = remove_icl_entries_from_tree_and_compute_depth hte_left
			# (depth_right,hte_right) = remove_icl_entries_from_tree_and_compute_depth hte_right
			= (if (depth_left>=depth_right) depth_left depth_right,HTE_Ident hte_ident hte_class 0 hte_left hte_right)
		remove_icl_entries_from_tree_and_compute_depth (HTE_Ident hte_ident hte_class _ hte_left hte_right)
			# (depth_left,hte_left) = remove_icl_entries_from_tree_and_compute_depth hte_left
			# (depth_right,hte_right) = remove_icl_entries_from_tree_and_compute_depth hte_right
			= merge_trees hte_left hte_right depth_left depth_right
		
		// the returned depth is an estimate
		merge_trees :: !*HashTableEntry !*HashTableEntry !Int !Int -> (!Int,!.HashTableEntry)
		merge_trees HTE_Empty hte_right depth_left depth_right
			= (depth_right,hte_right)
		merge_trees hte_left HTE_Empty depth_left depth_right
			= (depth_left,hte_left)
		merge_trees hte_left hte_right depth_left depth_right
			| depth_left>=depth_right
				= merge_trees_left hte_left hte_right depth_left depth_right
				= merge_trees_right hte_left hte_right depth_left depth_right
		where
				merge_trees_left :: !*HashTableEntry !*HashTableEntry !Int !Int -> (!Int,!.HashTableEntry)
				merge_trees_left (HTE_Ident hte_ident hte_class hte_mark hte_left_left hte_left_right) hte_right depth_left depth_right
					# (depth_right,hte_right)=merge_trees hte_left_right hte_right (depth_left-1) depth_right
					# depth_right=depth_right+1
					= (if (depth_left>=depth_right) depth_left depth_right,HTE_Ident hte_ident hte_class hte_mark hte_left_left hte_right)

				merge_trees_right :: !*HashTableEntry !*HashTableEntry !Int !Int -> (!Int,!.HashTableEntry)
				merge_trees_right hte_left (HTE_Ident hte_ident hte_class hte_mark hte_right_left hte_right_right) depth_left depth_right
					# (depth_left,hte_left)=merge_trees hte_left hte_right_left depth_left (depth_right-1)
					# depth_left=depth_left+1
					= (if (depth_left>=depth_right) depth_left depth_right,HTE_Ident hte_ident hte_class hte_mark hte_left hte_right_right)
