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
PD_LessOrEqualFun:==121
PD_SubFun:==122
PD_IncFun					:== 123
PD_From						:== 124
PD_FromThen					:== 125
PD_FromTo					:== 126
PD_FromThenTo				:== 127

/* Dynamics */

PD_TypeCodeClass			:== 128

PD_TypeObjectType			:== 129
PD_TypeConsSymbol			:== 130
PD_unify					:== 131
// MV ..
PD_coerce					:== 132
PD_variablePlaceholder		:== 133
PD_StdDynamics				:== 134
PD_undo_indirections		:== 135

/* Generics */
PD_StdGeneric				:== 136
PD_TypeISO					:== 137
PD_ConsISO					:== 138
PD_iso_to					:== 139
PD_iso_from					:== 140

PD_TypeUNIT					:== 141
PD_ConsUNIT					:== 142
PD_TypeEITHER				:== 143
PD_ConsLEFT					:== 144
PD_ConsRIGHT				:== 145
PD_TypePAIR					:== 146
PD_ConsPAIR					:== 147
PD_TypeARROW				:== 148
PD_ConsARROW				:== 149

PD_TypeConsDefInfo			:== 150 
PD_ConsConsDefInfo			:== 151
PD_TypeTypeDefInfo			:== 152 
PD_ConsTypeDefInfo			:== 153
PD_cons_info				:== 154
PD_TypeCONS					:== 155
PD_ConsCONS					:== 156

PD_isomap_ARROW_			:== 157
PD_isomap_ID				:== 158

/* StdMisc */
PD_StdMisc					:== 159
PD_abort					:== 160
PD_undef					:== 161

PD_Start					:== 162

PD_DummyForStrictAliasFun	:== 163

PD_NrOfPredefSymbols		:== 164

GetTupleConsIndex tup_arity :== PD_Arity2TupleSymbol + tup_arity - 2
GetTupleTypeIndex tup_arity :== PD_Arity2TupleType + tup_arity - 2

buildPredefinedSymbols :: !*HashTable -> (!.PredefinedSymbols,!*HashTable)

buildPredefinedModule :: !*PredefinedSymbols -> (!ScannedModule, !.PredefinedSymbols)
