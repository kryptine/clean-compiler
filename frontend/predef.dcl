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
PD_LessOrEqualFun:== 121
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
PD_StdDynamic				:== 134
PD_undo_indirections		:== 135

// MV ...
PD_TypeID					:== 136
PD_ModuleID					:== 137
PD_ModuleConsSymbol			:== 138
// ... MV

/* Generics */
PD_StdGeneric				:== 139
PD_TypeISO					:== 140
PD_ConsISO					:== 141
PD_iso_to					:== 142
PD_iso_from					:== 143

PD_TypeUNIT					:== 144
PD_ConsUNIT					:== 145
PD_TypeEITHER				:== 146
PD_ConsLEFT					:== 147
PD_ConsRIGHT				:== 148
PD_TypePAIR					:== 149
PD_ConsPAIR					:== 150
PD_TypeARROW				:== 151
PD_ConsARROW				:== 152

PD_TypeConsDefInfo			:== 153 
PD_ConsConsDefInfo			:== 154
PD_TypeTypeDefInfo			:== 155 
PD_ConsTypeDefInfo			:== 156
PD_cons_info				:== 157
PD_TypeCONS					:== 158
PD_ConsCONS					:== 159

PD_isomap_ARROW_			:== 160
PD_isomap_ID				:== 161

/* StdMisc */
PD_StdMisc					:== 162
PD_abort					:== 163
PD_undef					:== 164

PD_Start					:== 165

PD_DummyForStrictAliasFun	:== 166

PD_NrOfPredefSymbols		:== 167


GetTupleConsIndex tup_arity :== PD_Arity2TupleSymbol + tup_arity - 2
GetTupleTypeIndex tup_arity :== PD_Arity2TupleType + tup_arity - 2

buildPredefinedSymbols :: !*HashTable -> (!.PredefinedSymbols,!*HashTable)

buildPredefinedModule :: !*PredefinedSymbols -> (!ScannedModule, !.PredefinedSymbols)
