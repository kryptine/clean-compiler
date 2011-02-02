/*
	module owner: Martijn Vervoort
*/
definition module type_io

// WARNING: It is essential to report changes in this module to martijnv@cs.kun.nl
//			because the binary format for type-files is used by the dynamic run-time
//			system.

import scanner, general, Heap, typeproperties, utilities, checksupport
import StdEnv
import trans

:: WriteTypeInfoState
	= { 
		wtis_n_type_vars						:: !Int
	,	wtis_common_defs						:: !{#CommonDefs}	
	,	wtis_type_defs							:: !.{#{#CheckedTypeDef}}
	,	wtis_collected_conses					:: !ImportedConstructors
	,	wtis_type_heaps							:: !.TypeHeaps
	,	wtis_var_heap							:: !.VarHeap
	,	wtis_main_dcl_module_n 					:: !Int
	};

class WriteTypeInfo a 
where
	write_type_info :: a !*File !*WriteTypeInfoState -> (!*File,!*WriteTypeInfoState)
	
instance WriteTypeInfo CommonDefs, Char, [a] | WriteTypeInfo a

instance WriteTypeInfo StrictnessList

instance WriteTypeInfo {#b} | Array {#} b & WriteTypeInfo b 

instance WriteTypeInfo (a,b) | WriteTypeInfo a & WriteTypeInfo b

instance WriteTypeInfo TypeSymbIdent

instance WriteTypeInfo Int 