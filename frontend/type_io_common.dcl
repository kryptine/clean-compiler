/*
	module owner: Martijn Vervoort
*/
definition module type_io_common

// common between compiler and static linker
import StdEnv
import syntax
import StdOverloaded

/*
// Priority
PrioCode						:== toChar 0
NoPrioCode						:== toChar 1

// Assoc
LeftAssocCode					:== toChar 2
RightAssocCode					:== toChar 3
NoAssocCode						:== toChar 4
*/

// TypeRhs
AlgTypeCode						:== (toChar 5)
SynTypeCode 					:== (toChar 6)
RecordTypeCode					:== (toChar 7)
AbstractTypeCode				:== (toChar 8)

// Type
TypeTACode						:== (toChar 9)		// TA
TypeArrowCode 					:== (toChar 10)		// -->
TypeConsApplyCode				:== (toChar 11)		// :@:
TypeTBCode						:== (toChar 12)		// TB
TypeGTVCode						:== (toChar 13)		// GTV
TypeTVCode						:== (toChar 14)		// TV
TypeTQVCode						:== (toChar 15)		// TempTQV
TypeTECode						:== (toChar 16)		// TE

// Type; TB
BT_IntCode						:== (toChar 17)	
BT_CharCode						:== (toChar 18)
BT_RealCode						:== (toChar 19)
BT_BoolCode						:== (toChar 20)
BT_DynamicCode					:== (toChar 21)
BT_FileCode						:== (toChar 22)
BT_WorldCode					:== (toChar 23)
BT_StringCode					:== (toChar 24)

// ConsVariable	
ConsVariableCVCode				:== (toChar 25)	
ConsVariableTempCVCode			:== (toChar 26)
ConsVariableTempQCVCode			:== (toChar 27)

// TypeSymbIdent
TypeSymbIdentWithoutDefinition	:== (toChar 28)		// valid only for predefined in PD_PredefinedModule e.g. _String, _List
TypeSymbIdentWithDefinition		:== (toChar 29)		// for all types which have definitions in some .icl-module

// Maybe
MaybeNothingCode				:== (toChar 30)
MaybeJustCode					:== (toChar 31)

// used by {compiler,dynamic rts} to make String representation of types
PredefinedModuleName			:== "_predefined"

UnderscoreSystemModule			:== "_system"		// implements the predefined module

instance toString GlobalTCType

instance toString BasicType
