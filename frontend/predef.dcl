definition module predef

	
import syntax, hashtable

::	PredefinedSymbols	:== {# PredefinedSymbol}

::	PredefinedSymbol =
	{	pds_ident	:: !Ident
	,	pds_module	:: !Index
	,	pds_def		:: !Index
	}

/* identifiers not present the hastable */



PD_PredefinedModule			:== 0

PD_StringType				:== 1
PD_ListType					:== 2
PD_Arity2TupleType			:== 3
PD_Arity32TupleType			:== 33

PD_LazyArrayType			:== 34
PD_StrictArrayType			:== 35
PD_UnboxedArrayType			:== 36

PD_ConsSymbol				:== 37
PD_NilSymbol				:== 38
PD_Arity2TupleSymbol		:== 39
PD_Arity32TupleSymbol		:== 69

PD_TypeVar_a0				:== 70
PD_TypeVar_a31				:== 101

PD_TypeCodeMember			:== 123

/* identifiers present in the hastable */

PD_StdArray					:== 102
PD_StdEnum					:== 103
PD_StdBool					:== 104

PD_AndOp					:== 105
PD_OrOp						:== 106


/* Array functions */

PD_ArrayClass				:== 107

PD_CreateArrayFun			:== 108
PD__CreateArrayFun			:== 109
PD_ArraySelectFun			:== 110
PD_UnqArraySelectFun		:== 111
PD_ArrayUpdateFun			:== 112
PD_ArrayReplaceFun			:== 113
PD_ArraySizeFun				:== 114
PD_UnqArraySizeFun			:== 115

/* Enum/Comprehension functions */

PD_SmallerFun				:== 116
PD_IncFun					:== 117
PD_From						:== 118
PD_FromThen					:== 119
PD_FromTo					:== 120
PD_FromThenTo				:== 121

/* Dynamics */

PD_TypeCodeClass			:== 122

PD_TypeObjectType			:== 124
PD_TypeConsSymbol			:== 125
PD_unify					:== 126
PD_coerce					:== 127
PD_variablePlaceholder		:== 128
PD_StdDynamics				:== 129
PD_undo_indirections		:== 130

PD_Start					:== 131

// MW..
PD_DummyForStrictAliasFun	:== 132

PD_NrOfPredefSymbols		:== 133
// ..MW

GetTupleConsIndex tup_arity :== PD_Arity2TupleSymbol + tup_arity - 2
GetTupleTypeIndex tup_arity :== PD_Arity2TupleType + tup_arity - 2

buildPredefinedSymbols :: !*HashTable -> (!.PredefinedSymbols,!*HashTable)

buildPredefinedModule :: !*PredefinedSymbols -> (!ScannedModule, !.PredefinedSymbols)
