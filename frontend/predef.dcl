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

/* identifiers present in the hashtable */

PD_StdArray					:== 120
PD_StdEnum					:== 121
PD_StdBool					:== 122

PD_AndOp					:== 123
PD_OrOp						:== 124

/* Array functions */

PD_ArrayClass				:== 125

PD_CreateArrayFun			:== 126
PD__CreateArrayFun			:== 127
PD_ArraySelectFun			:== 128
PD_UnqArraySelectFun		:== 129
PD_ArrayUpdateFun			:== 130
PD_ArrayReplaceFun			:== 131
PD_ArraySizeFun				:== 132
PD_UnqArraySizeFun			:== 133

/* Enum/Comprehension functions */

PD_SmallerFun				:== 134
PD_LessOrEqualFun			:== 135
PD_IncFun					:== 136
PD_SubFun					:== 137
PD_From						:== 138
PD_FromThen					:== 139
PD_FromTo					:== 140
PD_FromThenTo				:== 141

/* StdMisc */
PD_StdMisc					:== 142
PD_abort					:== 143
PD_undef					:== 144

PD_Start					:== 145

PD_DummyForStrictAliasFun	:== 146

PD_StdStrictLists:==147

PD_cons:==148
PD_decons:==149

PD_cons_u:==150
PD_decons_u:==151

PD_cons_uts:==152
PD_decons_uts:==153

PD_nil:==154
PD_nil_u:==155
PD_nil_uts:==156

PD_ListClass :== 157
PD_UListClass :== 158
PD_UTSListClass :== 159

/* Dynamics */

// TC class
PD_TypeCodeMember			:== 160
PD_TypeCodeClass			:== 161
// dynamic module
PD_StdDynamic				:== 162
// dynamic type
PD_Dyn_DynamicTemp			:== 163
// type code
PD_Dyn_Type					:== 164
PD_Dyn_TypeScheme			:== 165
PD_Dyn_TypeApp				:== 166
PD_Dyn_TypeVar				:== 167
PD_Dyn_TypePatternVar		:== 168
PD_Dyn_TypeCons				:== 169
// unification
PD_Dyn_UnificationEnvironment			:== 170
PD_Dyn_initial_unification_environment	:== 171
PD_Dyn_bind_global_type_pattern_var		:== 172
PD_Dyn_unify							:== 173
PD_Dyn_normalise						:== 174
// predefined type code constructor
PD_Dyn_TypeCodeConstructorInt						:==	175
PD_Dyn_TypeCodeConstructorChar						:== 176
PD_Dyn_TypeCodeConstructorReal						:== 177
PD_Dyn_TypeCodeConstructorBool						:== 178
PD_Dyn_TypeCodeConstructorDynamic					:== 179
PD_Dyn_TypeCodeConstructorFile						:== 180
PD_Dyn_TypeCodeConstructorWorld						:== 181
PD_Dyn_TypeCodeConstructor_Arrow					:== 182
PD_Dyn_TypeCodeConstructor_List						:== 183
PD_Dyn_TypeCodeConstructor_StrictList				:== 184
PD_Dyn_TypeCodeConstructor_UnboxedList				:== 185
PD_Dyn_TypeCodeConstructor_TailStrictList			:== 186
PD_Dyn_TypeCodeConstructor_StrictTailStrictList		:== 187		
PD_Dyn_TypeCodeConstructor_UnboxedTailStrictList	:== 188
PD_Dyn_TypeCodeConstructor_Tuple					:== 189
PD_Dyn_TypeCodeConstructor_LazyArray				:== 190
PD_Dyn_TypeCodeConstructor_StrictArray				:== 191
PD_Dyn_TypeCodeConstructor_UnboxedArray				:== 192

/* Generics */
PD_StdGeneric				:== 193

PD_TypeBimap				:== 194
PD_ConsBimap				:== 195
PD_map_to					:== 196
PD_map_from					:== 197

PD_TypeUNIT					:== 198
PD_ConsUNIT					:== 199
PD_TypeEITHER				:== 200
PD_ConsLEFT					:== 201
PD_ConsRIGHT				:== 202
PD_TypePAIR					:== 203
PD_ConsPAIR					:== 204
// for constructor info
PD_TypeCONS					:== 205
PD_ConsCONS					:== 206
PD_TypeFIELD				:== 207
PD_ConsFIELD				:== 208
PD_TypeREC					:== 209
PD_ConsREC					:== 210
PD_GenericInfo				:== 211
PD_NoGenericInfo			:== 212
PD_GenericConsInfo			:== 213
PD_GenericFieldInfo			:== 214
PD_TGenericConsDescriptor 	:== 215
PD_CGenericConsDescriptor 	:== 216
PD_TGenericFieldDescriptor 	:== 217
PD_CGenericFieldDescriptor 	:== 218
PD_TGenericTypeDefDescriptor :== 219
PD_CGenericTypeDefDescriptor :== 220
PD_TGenConsPrio				:== 221
PD_CGenConsNoPrio			:== 222
PD_CGenConsPrio				:== 223
PD_TGenConsAssoc			:== 224
PD_CGenConsAssocNone		:== 225
PD_CGenConsAssocLeft		:== 226
PD_CGenConsAssocRight		:== 227
PD_TGenType					:== 228
PD_CGenTypeCons				:== 229
PD_CGenTypeVar				:== 230
PD_CGenTypeArrow			:== 231
PD_CGenTypeApp				:== 232


PD_GenericBimap				:== 233
PD_bimapId					:== 234

PD_TypeGenericDict 			:== 235

PD_NrOfPredefSymbols		:== 236

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
