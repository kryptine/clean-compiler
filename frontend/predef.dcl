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

PD_UnitType :== 43

// constructors:

FirstConstructorPredefinedSymbolIndex :== PD_ConsSymbol; // to compute index in com_cons_defs

PD_ConsSymbol :== 44
PD_StrictConsSymbol :== 45
PD_UnboxedConsSymbol :== 46
PD_TailStrictConsSymbol :== 47
PD_StrictTailStrictConsSymbol :== 48
PD_UnboxedTailStrictConsSymbol :== 49
PD_OverloadedConsSymbol :== 50

PD_NilSymbol :== 51
PD_StrictNilSymbol :== 52
PD_UnboxedNilSymbol :== 53
PD_TailStrictNilSymbol :== 54
PD_StrictTailStrictNilSymbol :== 55
PD_UnboxedTailStrictNilSymbol :== 56
PD_OverloadedNilSymbol :== 57

PD_Arity2TupleSymbol		:== 58
PD_Arity32TupleSymbol		:== 88

PD_UnitConsSymbol :== 89

// end constructors

PD_TypeVar_a0				:== 90
PD_TypeVar_a31				:== 121

/* identifiers present in the hashtable */

PD_StdArray					:== 122
PD_StdEnum					:== 123
PD_StdBool					:== 124

PD_AndOp					:== 125
PD_OrOp						:== 126

/* Array functions */

PD_ArrayClass				:== 127

PD_CreateArrayFun			:== 128
PD__CreateArrayFun			:== 129
PD_ArraySelectFun			:== 130
PD_UnqArraySelectFun		:== 131
PD_ArrayUpdateFun			:== 132
PD_ArrayReplaceFun			:== 133
PD_ArraySizeFun				:== 134
PD_UnqArraySizeFun			:== 135

/* Enum/Comprehension functions */

PD_SmallerFun				:== 136
PD_LessOrEqualFun			:== 137
PD_IncFun					:== 138
PD_SubFun					:== 139
PD_From						:== 140
PD_FromThen					:== 141
PD_FromTo					:== 142
PD_FromThenTo				:== 143

/* StdMisc */
PD_StdMisc					:== 144
PD_abort					:== 145
PD_undef					:== 146

PD_Start					:== 147

PD_DummyForStrictAliasFun	:== 148

PD_StdStrictLists:==149

PD_cons:==150
PD_decons:==151

PD_cons_u:==152
PD_decons_u:==153

PD_cons_uts:==154
PD_decons_uts:==155

PD_nil:==156
PD_nil_u:==157
PD_nil_uts:==158

PD_ListClass :== 159
PD_UListClass :== 160
PD_UTSListClass :== 161

/* Dynamics */

// TC class
PD_TypeCodeMember			:== 162
PD_TypeCodeClass			:== 163
// dynamic module
PD_StdDynamic				:== 164
// dynamic type
PD_Dyn_DynamicTemp				:== 165
// type code (type)
PD_Dyn_TypeCode					:== 166
// unification (type)
PD_Dyn_UnificationEnvironment	:== 167
// type code (expressions)
PD_Dyn_TypeScheme			:== 168
PD_Dyn_TypeApp				:== 169
PD_Dyn_TypeVar				:== 170
PD_Dyn_TypeCons				:== 171
PD_Dyn_TypeUnique			:== 172
PD_Dyn__TypeFixedVar		:== 173
// unification (expressions)
PD_Dyn_initial_unification_environment	:== 174
PD_Dyn_bind_global_type_pattern_var		:== 175
PD_Dyn_unify							:== 176
PD_Dyn_normalise						:== 177

/* Generics */
PD_StdGeneric				:== 178
// Generics types
PD_TypeUNIT					:== 179
PD_TypeEITHER				:== 180
PD_TypePAIR					:== 181
// for constructor info
PD_TypeCONS					:== 182
PD_TypeRECORD				:== 183
PD_TypeFIELD				:== 184
PD_TypeOBJECT				:== 185
PD_TGenericConsDescriptor	:== 186
PD_TGenericRecordDescriptor	:== 187
PD_TGenericFieldDescriptor 	:== 188
PD_TGenericTypeDefDescriptor :== 189
PD_TGenConsPrio				:== 190
PD_TGenConsAssoc			:== 191
PD_TGenType					:== 192

PD_TypeGenericDict 			:== 193
// Generics expression
PD_ConsUNIT					:== 194
PD_ConsLEFT					:== 195
PD_ConsRIGHT				:== 196
PD_ConsPAIR					:== 197
// for constructor info
PD_ConsCONS					:== 198
PD_ConsRECORD				:== 199
PD_ConsFIELD				:== 200
PD_ConsOBJECT				:== 201
PD_CGenericConsDescriptor 	:== 202
PD_CGenericRecordDescriptor	:== 203
PD_CGenericFieldDescriptor 	:== 204
PD_CGenericTypeDefDescriptor :== 205
PD_CGenConsNoPrio			:== 206
PD_CGenConsPrio				:== 207
PD_CGenConsAssocNone		:== 208
PD_CGenConsAssocLeft		:== 209
PD_CGenConsAssocRight		:== 210
PD_CGenTypeCons				:== 211
PD_CGenTypeVar				:== 212
PD_CGenTypeArrow			:== 213
PD_CGenTypeApp				:== 214

PD_GenericBimap				:== 215

PD_FromS					:== 216
PD_FromTS					:== 217
PD_FromSTS					:== 218
PD_FromU					:== 219
PD_FromUTS					:== 220
PD_FromO					:== 221

PD_FromThenS				:== 222
PD_FromThenTS				:== 223
PD_FromThenSTS				:== 224
PD_FromThenU				:== 225
PD_FromThenUTS				:== 226
PD_FromThenO				:== 227

PD_FromToS					:== 228
PD_FromToTS					:== 229
PD_FromToSTS				:== 230
PD_FromToU					:== 231
PD_FromToUTS				:== 232
PD_FromToO					:== 233

PD_FromThenToS				:== 234
PD_FromThenToTS				:== 235
PD_FromThenToSTS			:== 236
PD_FromThenToU				:== 237
PD_FromThenToUTS			:== 238
PD_FromThenToO				:== 239

PD_Dyn__to_TypeCodeConstructor	:== 240
PD_TypeCodeConstructor :== 241

PD_TC_Int			:== 242
PD_TC_Char			:== 243
PD_TC_Real			:== 244
PD_TC_Bool			:== 245
PD_TC_Dynamic		:== 246
PD_TC_File			:== 247
PD_TC_World			:== 248

PD_TC__Arrow		:== 249

PD_TC__List			:== 250
PD_TC__StrictList	:== 251
PD_TC__UnboxedList	:== 252
PD_TC__TailStrictList	:== 253
PD_TC__StrictTailStrictList	:== 254
PD_TC__UnboxedTailStrictList	:== 255

PD_TC__Tuple2		:== 256
PD_TC__Tuple3		:== 257
PD_TC__Tuple4		:== 258
PD_TC__Tuple5		:== 259
PD_TC__Tuple6		:== 260
PD_TC__Tuple7		:== 261
PD_TC__Tuple8		:== 262
PD_TC__Tuple9		:== 263
PD_TC__Tuple10		:== 264
PD_TC__Tuple11		:== 265
PD_TC__Tuple12		:== 266
PD_TC__Tuple13		:== 267
PD_TC__Tuple14		:== 268
PD_TC__Tuple15		:== 269
PD_TC__Tuple16		:== 270
PD_TC__Tuple17		:== 271
PD_TC__Tuple18		:== 272
PD_TC__Tuple19		:== 273
PD_TC__Tuple20		:== 274
PD_TC__Tuple21		:== 275
PD_TC__Tuple22		:== 276
PD_TC__Tuple23		:== 277
PD_TC__Tuple24		:== 278
PD_TC__Tuple25		:== 279
PD_TC__Tuple26		:== 280
PD_TC__Tuple27		:== 281
PD_TC__Tuple28		:== 282
PD_TC__Tuple29		:== 283
PD_TC__Tuple30		:== 284
PD_TC__Tuple31		:== 285
PD_TC__Tuple32		:== 286

PD_TC__LazyArray	:== 287
PD_TC__StrictArray	:== 288
PD_TC__UnboxedArray	:== 289

PD_TC__Unit			:== 290

PD_NrOfPredefSymbols		:== 291

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
