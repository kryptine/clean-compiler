definition module type_io

// WARNING: It is essential to report changes in this module to martijnv@cs.kun.nl
//			because the binary format for type-files is used by the dynamic run-time
//			system.

import scanner, general, Heap, typeproperties, utilities, checksupport

import StdEnv

:: WriteTypeInfoState
	= { 
		wtis_type_heaps			:: !.TypeHeaps
	,	wtis_n_type_vars		:: !Int
	};

class WriteTypeInfo a 
where
	write_type_info :: a !*File !*WriteTypeInfoState -> (!*File,!*WriteTypeInfoState)
	
instance WriteTypeInfo CommonDefs, Char, [a] | WriteTypeInfo a

/*2.0
instance WriteTypeInfo String
0.2*/

//1.3
instance WriteTypeInfo {#b} | select_u, size_u, WriteTypeInfo b 
//3.1

