definition module type_io

import scanner, general, Heap, typeproperties, utilities, checksupport

import StdEnv

class WriteTypeInfo a 
where
	write_type_info :: a !*File -> !*File
	
instance WriteTypeInfo CommonDefs, Char, [a] | WriteTypeInfo a

//1.3
instance WriteTypeInfo {#b} | select_u, size_u, WriteTypeInfo b 
//3.1

// read
// read
class ReadTypeInfo a
where
	read_type_info :: !*File -> (!Bool,a,!*File)
	
instance ReadTypeInfo CommonDefs //,TypeDef TypeRhs, ConsDef
