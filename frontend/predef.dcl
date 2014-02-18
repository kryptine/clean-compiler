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
PD_Dyn_DynamicTemp				:== 163
// type code (type)
PD_Dyn_TypeCode					:== 164
// unification (type)
PD_Dyn_UnificationEnvironment	:== 165
// type code (expressions)
PD_Dyn_TypeScheme			:== 166
PD_Dyn_TypeApp				:== 167
PD_Dyn_TypeVar				:== 168
PD_Dyn_TypeCons				:== 169
PD_Dyn_TypeUnique			:== 170
PD_Dyn__TypeFixedVar		:== 171
// unification (expressions)
PD_Dyn_initial_unification_environment	:== 172
PD_Dyn_bind_global_type_pattern_var		:== 173
PD_Dyn_unify							:== 174
PD_Dyn_normalise						:== 175

/* Generics */
PD_StdGeneric				:== 176
// Generics types
PD_TypeBimap				:== 177
PD_TypeUNIT					:== 178
PD_TypeEITHER				:== 179
PD_TypePAIR					:== 180
// for constructor info
PD_TypeCONS					:== 181
PD_TypeRECORD				:== 182
PD_TypeFIELD				:== 183
PD_TypeOBJECT				:== 184
PD_TGenericConsDescriptor 	:== 185
PD_TGenericRecordDescriptor :== 186
PD_TGenericFieldDescriptor 	:== 187
PD_TGenericTypeDefDescriptor :== 188
PD_TGenConsPrio				:== 189
PD_TGenConsAssoc			:== 190
PD_TGenType					:== 191

PD_TypeGenericDict 			:== 192
// Generics fields
PD_map_to					:== 193
PD_map_from					:== 194
// Generics expression
PD_ConsBimap				:== 195
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

PD_bimapId					:== 217
PD_GenericBimap				:== 218

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
PD_TC__Tuple3		:== 260
PD_TC__Tuple4		:== 261
PD_TC__Tuple5		:== 262
PD_TC__Tuple6		:== 263
PD_TC__Tuple7		:== 264
PD_TC__Tuple8		:== 265
PD_TC__Tuple9		:== 266
PD_TC__Tuple10		:== 267
PD_TC__Tuple11		:== 268
PD_TC__Tuple12		:== 269
PD_TC__Tuple13		:== 270
PD_TC__Tuple14		:== 271
PD_TC__Tuple15		:== 272
PD_TC__Tuple16		:== 273
PD_TC__Tuple17		:== 274
PD_TC__Tuple18		:== 275
PD_TC__Tuple19		:== 276
PD_TC__Tuple20		:== 277
PD_TC__Tuple21		:== 278
PD_TC__Tuple22		:== 279
PD_TC__Tuple23		:== 280
PD_TC__Tuple24		:== 281
PD_TC__Tuple25		:== 282
PD_TC__Tuple26		:== 283
PD_TC__Tuple27		:== 284
PD_TC__Tuple28		:== 285
PD_TC__Tuple29		:== 286
PD_TC__Tuple30		:== 287
PD_TC__Tuple31		:== 288
PD_TC__Tuple32		:== 289

PD_TC__LazyArray	:== 290
PD_TC__StrictArray	:== 291
PD_TC__UnboxedArray	:== 292

PD_iTasks_Framework_Tonic		:== 293
PD_tonicTune					:== 294
PD_tonicBind					:== 295
PD_tonicReflection				:== 296
PD_tonicReplaceSingleTaskVar    :== 297
PD_tonicAnyTask                 :== 298

PD_NrOfPredefSymbols		:== 299

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
