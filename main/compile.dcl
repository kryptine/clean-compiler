/*
	module owner: Ronny Wichers Schreur
*/
definition module compile

/*2.0
from StdFile import ::Files
0.2*/
//1.3
from StdFile import Files
//3.1
import checksupport

compile :: ![{#Char}] !*DclCache !*Files -> (!Bool,!*DclCache,!*Files)

:: DclCache = {
	dcl_modules::!{#DclModule},
	functions_and_macros::!.{#.{#FunDef}},
	predef_symbols::!.PredefinedSymbols,
	hash_table::!.HashTable,
	heaps::!.Heaps
 };

empty_cache :: !*SymbolTable -> *DclCache
