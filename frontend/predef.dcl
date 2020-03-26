definition module predef

import syntax, hashtable

::	PredefinedSymbols	:== {# PredefinedSymbol}

::	PredefinedSymbol = {
		pds_module	:: !Index,
		pds_def		:: !Index
	}

init_identifiers :: !*SymbolTable !*World -> (!*SymbolTable,!*World)

predefined_idents :: {!Ident}

buildPredefinedSymbols :: !*HashTable -> (!.PredefinedSymbols,!*HashTable)

buildPredefinedModule :: !Bool !*PredefinedSymbols -> (!ScannedModule, !.PredefinedSymbols)

cPredefinedModuleIndex :== 1

PD_StringTypeIndex :== 0
PD_Arity2TupleTypeIndex :== 8
PD_Arity32TupleTypeIndex :== 38

/* identifiers not present the hashtable */

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
PD_ClippedArrayType			:== 43

PD_UnitType :== 44

// constructors:

FirstConstructorPredefinedSymbolIndex :== PD_ConsSymbol; // to compute index in com_cons_defs

PD_ConsSymbol :== 45
PD_StrictConsSymbol :== 46
PD_UnboxedConsSymbol :== 47
PD_TailStrictConsSymbol :== 48
PD_StrictTailStrictConsSymbol :== 49
PD_UnboxedTailStrictConsSymbol :== 50
PD_OverloadedConsSymbol :== 51

PD_NilSymbol :== 52
PD_StrictNilSymbol :== 53
PD_UnboxedNilSymbol :== 54
PD_TailStrictNilSymbol :== 55
PD_StrictTailStrictNilSymbol :== 56
PD_UnboxedTailStrictNilSymbol :== 57
PD_OverloadedNilSymbol :== 58

PD_Arity2TupleSymbol		:== 59
PD_Arity32TupleSymbol		:== 89

PD_UnitConsSymbol :== 90

// end constructors

PD_TypeVar_a0				:== 91
PD_TypeVar_a31				:== 122

/* identifiers present in the hashtable */

PD_StdArray					:== 123
PD_StdEnum					:== 124
PD_StdBool					:== 125

PD_AndOp					:== 126
PD_OrOp						:== 127

/* Array functions */

PD_ArrayClass				:== 128

PD_CreateArrayFun			:== 129
PD__CreateArrayFun			:== 130
PD_ArraySelectFun			:== 131
PD_UnqArraySelectFun		:== 132
PD_ArrayUpdateFun			:== 133
PD_ArrayReplaceFun			:== 134
PD_ArraySizeFun				:== 135
PD_UnqArraySizeFun			:== 136

/* Enum/Comprehension functions */

PD_SmallerFun				:== 137
PD_LessOrEqualFun			:== 138
PD_IncFun					:== 139
PD_SubFun					:== 140
PD_From						:== 141
PD_FromThen					:== 142
PD_FromTo					:== 143
PD_FromThenTo				:== 144

/* StdMisc */
PD_StdMisc					:== 145
PD_abort					:== 146
PD_undef					:== 147

PD_Start					:== 148

PD_DummyForStrictAliasFun	:== 149

PD_StdStrictLists:==150

PD_cons:==151
PD_decons:==152

PD_cons_u:==153
PD_decons_u:==154

PD_cons_uts:==155
PD_decons_uts:==156

PD_nil:==157
PD_nil_u:==158
PD_nil_uts:==159

PD_ListClass :== 160
PD_UListClass :== 161
PD_UTSListClass :== 162

/* Dynamics */

// TC class
PD_TypeCodeMember			:== 163
PD_TypeCodeClass			:== 164
// dynamic module
PD_StdDynamic				:== 165
// dynamic type
PD_Dyn_DynamicTemp				:== 166
// type code (type)
PD_Dyn_TypeCode					:== 167
// unification (type)
PD_Dyn_UnificationEnvironment	:== 168
// type code (expressions)
PD_Dyn_TypeScheme			:== 169
PD_Dyn_TypeApp				:== 170
PD_Dyn_TypeVar				:== 171
PD_Dyn_TypeCons				:== 172
PD_Dyn_TypeUnique			:== 173
PD_Dyn__TypeFixedVar		:== 174
// unification (expressions)
PD_Dyn_initial_unification_environment	:== 175
PD_Dyn_bind_global_type_pattern_var		:== 176
PD_Dyn_unify							:== 177
PD_Dyn_normalise						:== 178

/* Generics */
PD_StdGeneric				:== 179
// Generics types
PD_TypeUNIT					:== 180
PD_TypeEITHER				:== 181
PD_TypePAIR					:== 182
// for constructor info
PD_TypeCONS					:== 183
PD_TypeRECORD				:== 184
PD_TypeFIELD				:== 185
PD_TypeOBJECT				:== 186
PD_TGenericConsDescriptor	:== 187
PD_TGenericRecordDescriptor	:== 188
PD_TGenericFieldDescriptor 	:== 189
PD_TGenericTypeDefDescriptor :== 190
PD_TGenConsPrio				:== 191
PD_TGenConsAssoc			:== 192
PD_TGenType					:== 193

PD_TypeGenericDict 			:== 194
PD_TypeGenericDict0			:== 195
// Generics expression
PD_ConsUNIT					:== 196
PD_ConsLEFT					:== 197
PD_ConsRIGHT				:== 198
PD_ConsPAIR					:== 199
// for constructor info
PD_ConsCONS					:== 200
PD_ConsRECORD				:== 201
PD_ConsFIELD				:== 202
PD_ConsOBJECT				:== 203
PD_CGenericConsDescriptor 	:== 204
PD_CGenericRecordDescriptor	:== 205
PD_CGenericFieldDescriptor 	:== 206
PD_CGenericTypeDefDescriptor :== 207
PD_CGenConsNoPrio			:== 208
PD_CGenConsPrio				:== 209
PD_CGenConsAssocNone		:== 210
PD_CGenConsAssocLeft		:== 211
PD_CGenConsAssocRight		:== 212
PD_CGenTypeCons				:== 213
PD_CGenTypeVar				:== 214
PD_CGenTypeArrow			:== 215
PD_CGenTypeApp				:== 216

PD_GenericBimap				:== 217
PD_GenericBinumap			:== 218

PD_FromS					:== 219
PD_FromTS					:== 220
PD_FromSTS					:== 221
PD_FromU					:== 222
PD_FromUTS					:== 223
PD_FromO					:== 224

PD_FromThenS				:== 225
PD_FromThenTS				:== 226
PD_FromThenSTS				:== 227
PD_FromThenU				:== 228
PD_FromThenUTS				:== 229
PD_FromThenO				:== 230

PD_FromToS					:== 231
PD_FromToTS					:== 232
PD_FromToSTS				:== 233
PD_FromToU					:== 234
PD_FromToUTS				:== 235
PD_FromToO					:== 236

PD_FromThenToS				:== 237
PD_FromThenToTS				:== 238
PD_FromThenToSTS			:== 239
PD_FromThenToU				:== 240
PD_FromThenToUTS			:== 241
PD_FromThenToO				:== 242

PD_Dyn__to_TypeCodeConstructor	:== 243
PD_TypeCodeConstructor :== 244

PD_TC_Int			:== 245
PD_TC_Char			:== 246
PD_TC_Real			:== 247
PD_TC_Bool			:== 248
PD_TC_Dynamic		:== 249
PD_TC_File			:== 250
PD_TC_World			:== 251

PD_TC__Arrow		:== 252

PD_TC__List			:== 253
PD_TC__StrictList	:== 254
PD_TC__UnboxedList	:== 255
PD_TC__TailStrictList	:== 256
PD_TC__StrictTailStrictList	:== 257
PD_TC__UnboxedTailStrictList	:== 258

PD_TC__Tuple2		:== 259
PD_TC__Tuple32		:== 289

PD_TC__LazyArray	:== 290
PD_TC__StrictArray	:== 291
PD_TC__UnboxedArray	:== 292
PD_TC__ClippedArray	:== 293

PD_TC__Unit			:== 294

PD_NrOfPredefSymbols		:== 295

GetTupleConsIndex tup_arity :== PD_Arity2TupleSymbol + tup_arity - 2
GetTupleTypeIndex tup_arity :== PD_Arity2TupleType + tup_arity - 2

// changes requires recompile of {static,dynamic}-linker plus all dynamics ever made
UnderscoreSystemDynamicModule_String	:== "_SystemDynamic"	

// List-type
PD_ListType_String				:== "_List"
PD_ConsSymbol_String			:== "_Cons"
PD_NilSymbol_String				:== "_Nil"

// Array-type
PD_UnboxedArray_String			:== "_#Array"

DynamicRepresentation_String			:== "DynamicTemp" // "_DynamicTemp"		
