definition module predef

import syntax, hashtable

::	PredefinedSymbols	:== {# PredefinedSymbol}

::	PredefinedSymbol = {
		pds_module	:: !Index,
		pds_def		:: !Index
	}

cPredefinedModuleIndex :== 1

PD_StringTypeIndex :== 0
PD_Arity2TupleTypeIndex :== 8
PD_Arity32TupleTypeIndex :== 38

/* identifiers not present the hastable */

PD_PredefinedModule			:== 0

FirstTypePredefinedSymbolIndex:==PD_StringType; // to compute index in com_type_defs

PD_StringType				:== 1

PD_ListType :== 2
PD_StrictListType :== 3
PD_UnboxedListType :== 4
PD_TailStrictListType :== 5
PD_StrictTailStrictListType :== 6
PD_UnboxedTailStrictListType :== 7
PD_OverloadedListType :== 8

PD_Arity2TupleType			:== 9
PD_Arity32TupleType			:== 39

PD_LazyArrayType			:== 40
PD_StrictArrayType			:== 41
PD_UnboxedArrayType			:== 42

// constructors:

FirstConstructorPredefinedSymbolIndex :== PD_ConsSymbol; // to compute index in com_cons_defs

PD_ConsSymbol :== 43
PD_StrictConsSymbol :== 44
PD_UnboxedConsSymbol :== 45
PD_TailStrictConsSymbol :== 46
PD_StrictTailStrictConsSymbol :== 47
PD_UnboxedTailStrictConsSymbol :== 48
PD_OverloadedConsSymbol :== 49

PD_NilSymbol :== 50
PD_StrictNilSymbol :== 51
PD_UnboxedNilSymbol :== 52
PD_TailStrictNilSymbol :== 53
PD_StrictTailStrictNilSymbol :== 54
PD_UnboxedTailStrictNilSymbol :== 55
PD_OverloadedNilSymbol :== 56

PD_Arity2TupleSymbol		:== 57
PD_Arity32TupleSymbol		:== 87

// end constructors

PD_TypeVar_a0				:== 88
PD_TypeVar_a31				:== 119

/* Dynamics */

PD_TypeCodeMember			:== 120
PD_TypeCodeClass			:== 121
PD_Dyn_bind_global_type_pattern_var
							:== 122
PD_Dyn_ModuleID				:== 123

/* identifiers present in the hashtable */

PD_StdArray					:== 124
PD_StdEnum					:== 125
PD_StdBool					:== 126

PD_AndOp					:== 127
PD_OrOp						:== 128

/* Array functions */

PD_ArrayClass				:== 129

PD_CreateArrayFun			:== 130
PD__CreateArrayFun			:== 131
PD_ArraySelectFun			:== 132
PD_UnqArraySelectFun		:== 133
PD_ArrayUpdateFun			:== 134
PD_ArrayReplaceFun			:== 135
PD_ArraySizeFun				:== 136
PD_UnqArraySizeFun			:== 137

/* Enum/Comprehension functions */

PD_SmallerFun				:== 138
PD_LessOrEqualFun			:== 139
PD_IncFun					:== 140
PD_SubFun:== 141
PD_From						:== 142
PD_FromThen					:== 143
PD_FromTo					:== 144
PD_FromThenTo				:== 145

/* StdMisc */
PD_StdMisc					:== 146
PD_abort					:== 147
PD_undef					:== 148

PD_Start					:== 149

PD_DummyForStrictAliasFun	:== 150

PD_StdStrictLists:==151

PD_cons:==152
PD_decons:==153

PD_cons_u:==154
PD_decons_u:==155

PD_cons_uts:==156
PD_decons_uts:==157

PD_nil:==158
PD_nil_u:==159
PD_nil_uts:==160

PD_ListClass :== 161
PD_UListClass :== 162
PD_UTSListClass :== 163

/* Dynamics */

PD_StdDynamic				:== 164

PD_Dyn_DynamicTemp			:== 165
PD_Dyn_Type					:== 166
PD_Dyn_TypeScheme			:== 167
PD_Dyn_TypeApp				:== 168
PD_Dyn_TypeVar				:== 169
PD_Dyn_TypePatternVar		:== 170
PD_Dyn_TypeCons				:== 171
PD_Dyn_tc_name				:== 172
PD_Dyn_Unifier				:== 173
PD_Dyn_unify				:== 174
PD_Dyn_initial_unifier		:== 175
PD_Dyn_normalise			:== 176

/* Generics */
PD_StdGeneric				:== 177

PD_TypeBimap				:== 178
PD_ConsBimap				:== 179
PD_map_to					:== 180
PD_map_from					:== 181

PD_TypeUNIT					:== 182
PD_ConsUNIT					:== 183
PD_TypeEITHER				:== 184
PD_ConsLEFT					:== 185
PD_ConsRIGHT				:== 186
PD_TypePAIR					:== 187
PD_ConsPAIR					:== 188

// for constructor info
PD_TypeCONS					:== 189
PD_ConsCONS					:== 190
PD_TypeFIELD				:== 191
PD_ConsFIELD				:== 192
PD_TypeREC					:== 193
PD_ConsREC					:== 194
PD_GenericInfo				:== 195
PD_NoGenericInfo			:== 196
PD_GenericConsInfo			:== 197
PD_GenericFieldInfo			:== 198
PD_TGenericConsDescriptor 	:== 199
PD_CGenericConsDescriptor 	:== 200
PD_TGenericFieldDescriptor 	:== 201
PD_CGenericFieldDescriptor 	:== 202
PD_TGenericTypeDefDescriptor :== 203
PD_CGenericTypeDefDescriptor :== 204
PD_TGenConsPrio				:== 205 
PD_CGenConsNoPrio			:== 206
PD_CGenConsPrio				:== 207
PD_TGenConsAssoc			:== 208
PD_CGenConsAssocNone		:== 209
PD_CGenConsAssocLeft		:== 210
PD_CGenConsAssocRight		:== 211
PD_TGenType					:== 212
PD_CGenTypeCons				:== 213
PD_CGenTypeVar				:== 214
PD_CGenTypeArrow			:== 215
PD_CGenTypeApp				:== 216


PD_GenericBimap				:== 217
PD_bimapId					:== 218

PD_TypeGenericDict 			:== 219

PD_ModuleConsSymbol			:== 220
PD_NrOfPredefSymbols		:== 221

GetTupleConsIndex tup_arity :== PD_Arity2TupleSymbol + tup_arity - 2
GetTupleTypeIndex tup_arity :== PD_Arity2TupleType + tup_arity - 2

init_identifiers :: !*SymbolTable !*World -> (!*SymbolTable,!*World)

predefined_idents :: {!Ident}

buildPredefinedSymbols :: !*HashTable -> (!.PredefinedSymbols,!*HashTable)

buildPredefinedModule :: !*PredefinedSymbols -> (!ScannedModule, !.PredefinedSymbols)

// MV ...
// changes requires recompile of {static,dynamic}-linker plus all dynamics ever made
UnderscoreSystemDynamicModule_String	:== "_SystemDynamic"	

// List-type
PD_ListType_String				:== "_List"
PD_ConsSymbol_String			:== "_Cons"
PD_NilSymbol_String				:== "_Nil"

// Array-type
PD_UnboxedArray_String			:== "_#Array"
// ... MV
