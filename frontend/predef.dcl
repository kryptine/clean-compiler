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

/* Dynamics */

PD_TypeCodeMember			:== 102
// MV ...
PD_DynamicTemp				:== 103
PD_DynamicValue				:== 104
PD_DynamicType				:== 105
// ... MV

/* identifiers present in the hastable */

PD_StdArray					:== 106
PD_StdEnum					:== 107
PD_StdBool					:== 108

PD_AndOp					:== 109
PD_OrOp						:== 110


/* Array functions */

PD_ArrayClass				:== 111

PD_CreateArrayFun			:== 112
PD__CreateArrayFun			:== 113
PD_ArraySelectFun			:== 114
PD_UnqArraySelectFun		:== 115
PD_ArrayUpdateFun			:== 116
PD_ArrayReplaceFun			:== 117
PD_ArraySizeFun				:== 118
PD_UnqArraySizeFun			:== 119

/* Enum/Comprehension functions */

PD_SmallerFun				:== 120
PD_IncFun					:== 121
PD_From						:== 122
PD_FromThen					:== 123
PD_FromTo					:== 124
PD_FromThenTo				:== 125

/* Dynamics */

PD_TypeCodeClass			:== 126

PD_TypeObjectType			:== 127
PD_TypeConsSymbol			:== 128
PD_unify					:== 129
// MV ..
PD_coerce					:== 130
PD_variablePlaceholder		:== 131
PD_StdDynamics				:== 132
PD_undo_indirections		:== 133

/* Generics */
PD_StdGeneric				:== 134
PD_TypeISO					:== 135
PD_ConsISO					:== 136
PD_iso_to					:== 137
PD_iso_from					:== 138

PD_TypeUNIT					:== 139
PD_ConsUNIT					:== 140
PD_TypeEITHER				:== 141
PD_ConsLEFT					:== 142
PD_ConsRIGHT				:== 143
PD_TypePAIR					:== 144
PD_ConsPAIR					:== 145
PD_TypeARROW				:== 146
PD_ConsARROW				:== 147

PD_TypeConsDefInfo			:== 148 
PD_ConsConsDefInfo			:== 149
PD_TypeTypeDefInfo			:== 150 
PD_ConsTypeDefInfo			:== 151
PD_cons_info				:== 152
PD_TypeCONS					:== 153
PD_ConsCONS					:== 154

PD_isomap_ARROW_			:== 155
PD_isomap_ID				:== 156

/* StdMisc */
PD_StdMisc					:== 157
PD_abort					:== 158
PD_undef					:== 159

PD_Start					:== 160

// MW..
PD_DummyForStrictAliasFun	:== 161

PD_NrOfPredefSymbols		:== 162
// ..MW

GetTupleConsIndex tup_arity :== PD_Arity2TupleSymbol + tup_arity - 2
GetTupleTypeIndex tup_arity :== PD_Arity2TupleType + tup_arity - 2

buildPredefinedSymbols :: !*HashTable -> (!.PredefinedSymbols,!*HashTable)

buildPredefinedModule :: !*PredefinedSymbols -> (!ScannedModule, !.PredefinedSymbols)
