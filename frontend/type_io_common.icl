/*
	module owner: Martijn Vervoort
*/
implementation module type_io_common

// common between compiler and static linker
import StdEnv
import syntax
import StdOverloaded

APPEND_DEFINING_TYPE_MODULE_NAMES_TO_TYPE_NAMES yes no :== yes

/*
// Priority
PrioCode				:== toChar 0
NoPrioCode				:== toChar 1

// Assoc
LeftAssocCode			:== toChar 2
RightAssocCode			:== toChar 3
NoAssocCode				:== toChar 4
*/

// TypeRhs
AlgTypeCode				:== (toChar 5)
SynTypeCode 			:== (toChar 6)
RecordTypeCode			:== (toChar 7)
AbstractTypeCode		:== (toChar 8)

// Type
TypeTACode				:== (toChar 9)		// TA
TypeArrowCode 			:== (toChar 10)		// -->
TypeConsApplyCode		:== (toChar 11)		// :@:
TypeTBCode				:== (toChar 12)		// TB
TypeGTVCode				:== (toChar 13)		// GTV
TypeTVCode				:== (toChar 14)		// TV
TypeTQVCode				:== (toChar 15)		// TempTQV
TypeTECode				:== (toChar 16)		// TE

// Type; TB
BT_IntCode				:== (toChar 17)	
BT_CharCode				:== (toChar 18)
BT_RealCode				:== (toChar 19)
BT_BoolCode				:== (toChar 20)
BT_DynamicCode			:== (toChar 21)
BT_FileCode				:== (toChar 22)
BT_WorldCode			:== (toChar 23)
BT_StringCode			:== (toChar 24)

// ConsVariable	
ConsVariableCVCode		:== (toChar 25)	
ConsVariableTempCVCode	:== (toChar 26)
ConsVariableTempQCVCode	:== (toChar 27)

// TypeSymbIdent
TypeSymbIdentWithoutDefinition	:== (toChar 28)		// valid only for predefined in PD_PredefinedModule e.g. _String, _List
TypeSymbIdentWithDefinition		:== (toChar 29)		// for all types which have definitions in some .icl-module

// Maybe
MaybeNothingCode				:== (toChar 30)
MaybeJustCode					:== (toChar 31)

// used by {compiler,dynamic rts} to make String representation of types
PredefinedModuleName			:== "_predefined"

isPredefinedModuleName name		:== name == PredefinedModuleName

UnderscoreSystemModule			:== "_system"		// implements the predefined module

LowLevelInterfaceModule			:== "StdDynamicLowLevelInterface"

instance toString GlobalTCType
where
	toString (GTT_Basic basic_type)							= create_type_string (toString basic_type) PredefinedModuleName
	toString GTT_Function									= " -> "
	toString (GTT_Constructor type_symb_indent mod_name)	= create_type_string type_symb_indent.type_name.id_name mod_name
//	 +++ (APPEND_DEFINING_TYPE_MODULE_NAMES_TO_TYPE_NAMES ("'" +++ mod_name) "")

instance toString BasicType
where
	toString BT_Int 		= "Int"
	toString BT_Char		= "Char"
	toString BT_Real		= "Real"
	toString BT_Bool		= "Bool"
	toString BT_Dynamic		= "Dynamic"
	toString BT_File		= "File"
	toString BT_World		= "World"
	toString (BT_String _)	= "String"

create_type_string type_name module_name
	:== type_name +++ (APPEND_DEFINING_TYPE_MODULE_NAMES_TO_TYPE_NAMES ("'" +++ module_name ) "")

get_type_name_and_module_name_from_type_string :: !String -> (!String,!String)
get_type_name_and_module_name_from_type_string type_string
	#! (found_sep,sep_pos)
		= CharIndex type_string 0 '\'' 
	| found_sep
		#! type_name
			= type_string % (0,dec sep_pos)
		#! module_name
			= type_string % (inc sep_pos,dec (size type_string))
		= (type_name,module_name)
where 
	CharIndex  :: !String !Int !Char -> (!Bool,!Int)
	CharIndex s i char
		| i == (size s)
			= (False,size s)
			
			| i < (size s)
				| s.[i] == char
					= (True,i)
					= CharIndex s (inc i) char;
				= abort "CharIndex: index out of range"
	