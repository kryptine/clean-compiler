/*
	module owner: Martijn Vervoort
*/
definition module type_io

openTclFile :: !Bool !String !*Files -> (Optional !.File, !*Files)
closeTclFile :: !*(Optional *File) *Files -> *(!Bool,*Files)

baseName :: {#Char} -> {#Char}

directoryName :: {#Char} -> {#Char}

splitBy :: Char {#Char} -> [{#Char}]

// WARNING: It is essential to report changes in this module to martijnv@cs.kun.nl
//			because the binary format for type-files is used by the dynamic run-time
//			system.

import scanner, general, Heap, typeproperties, utilities, checksupport

import StdEnv

:: WriteTypeInfoState
	= { 
		wtis_type_heaps			:: !.TypeHeaps
	,	wtis_n_type_vars		:: !Int
	,	wtis_predefined_module_def	:: !Index
	};

class WriteTypeInfo a 
where
	write_type_info :: a !*File !*WriteTypeInfoState -> (!*File,!*WriteTypeInfoState)
	
instance WriteTypeInfo CommonDefs, Char, [a] | WriteTypeInfo a

instance WriteTypeInfo StrictnessList
/*2.0
instance WriteTypeInfo {#b} | Array {#} b & WriteTypeInfo b 
0.2*/

//1.3
instance WriteTypeInfo {#b} | select_u, size_u, WriteTypeInfo b 
//3.1