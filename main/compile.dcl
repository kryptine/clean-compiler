/*
	module owner: Ronny Wichers Schreur
*/
definition module compile

from StdFile import ::Files
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

open_file_in_clean_system_files_folder :: !String !String !String !Int !*File !*Files -> (!Bool, !Optional .File, !*File, !*Files)
