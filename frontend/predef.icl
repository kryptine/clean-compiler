implementation module predef

import syntax, hashtable, type_io_common

::	PredefinedSymbols	:== {# PredefinedSymbol}

::	PredefinedSymbol = {
		pds_module	:: !Index,
		pds_def		:: !Index
	}

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
PD_DynamicTemp				:== 121
PD_DynamicValue				:== 122
PD_DynamicType				:== 123

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

PD_TypeCodeClass			:== 165
PD_TypeObjectType			:== 166
PD_TypeConsSymbol			:== 167
PD_unify					:== 168
PD_coerce					:== 169
PD_PV_Placeholder			:== 170		// Pattern variable (occurs only in pattern)
PD_UPV_Placeholder			:== 171		// Universal Pattern Variable (occurs only in pattern; universally quantified variable)
PD_UV_Placeholder			:== 172		// Universal Variable (occurs only in dynamic; universally quantified variable)					
PD_undo_indirections		:== 173

PD_TypeID					:== 174
PD_ModuleID					:== 175
PD_ModuleConsSymbol			:== 176

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

PD_GenericBimap				:== 189
PD_bimapId					:== 190

PD_TypeGenericDict 			:== 191

PD_NrOfPredefSymbols		:== 192

(<<=) infixl
(<<=) symbol_table val
	:==	let (predefined_idents, index) = val
	  	in writePtr predefined_idents.[index].id_info EmptySymbolTableEntry symbol_table

(<<-) infixl
(<<-) hash_table val
	:== let (predefined_idents, table_kind, index) = val
		in putPredefinedIdentInHashTable predefined_idents.[index] table_kind hash_table

GetTupleConsIndex tup_arity :== PD_Arity2TupleSymbol + tup_arity - 2
GetTupleTypeIndex tup_arity :== PD_Arity2TupleType + tup_arity - 2

predefined_idents :: {!Ident}
predefined_idents
	# idents = createArray PD_NrOfPredefSymbols {id_name="",id_info=nilPtr}
	# idents = { idents &
					[PD_ConsSymbol] = i PD_ConsSymbol_String,
					[PD_StrictConsSymbol] = i "_!Cons",
					[PD_UnboxedConsSymbol] = i "_#Cons",
					[PD_TailStrictConsSymbol] = i "_Cons!",
					[PD_StrictTailStrictConsSymbol] = i "_!Cons!",
					[PD_UnboxedTailStrictConsSymbol] = i "_#Cons!",
					[PD_OverloadedConsSymbol] = i "_|Cons",
					[PD_NilSymbol] = i PD_NilSymbol_String,
					[PD_StrictNilSymbol] = i "_!Nil",
					[PD_UnboxedNilSymbol] = i "_#Nil",
					[PD_TailStrictNilSymbol] = 	i "_Nil!",
					[PD_StrictTailStrictNilSymbol] = i "_!Nil!",
					[PD_UnboxedTailStrictNilSymbol] = i "_#Nil!",
					[PD_OverloadedNilSymbol] = i "_|Nil",
			
					[PD_PredefinedModule] = i "_predefined",
					[PD_StringType] = i "_String",
					[PD_ListType] = i PD_ListType_String,
					[PD_StrictListType] = i "_!List",
					[PD_UnboxedListType] = i "_#List",
					[PD_TailStrictListType] = i "_List!",
					[PD_StrictTailStrictListType] = i "_!List!",
					[PD_UnboxedTailStrictListType] = i "_#List!",
					[PD_OverloadedListType] = i "_|List",
					[PD_LazyArrayType] = i "_Array",
					[PD_StrictArrayType] = i "_!Array",
					[PD_UnboxedArrayType] = i PD_UnboxedArray_String,
					[PD_TypeCodeMember] = i "_type_code",
					[PD_DummyForStrictAliasFun] = i "_dummyForStrictAlias"
				}
	# idents = build_tuples 2 32 idents
	# idents = build_variables 0 32 idents
	
	# idents = { idents &
					[PD_StdArray] = i "_SystemArray",
					[PD_StdEnum] = i "StdEnum",
					[PD_StdBool] = i "StdBool",
					[PD_AndOp] = i "&&",
					[PD_OrOp] = i "||",
					[PD_ArrayClass] = i "Array",
					[PD_CreateArrayFun] = i "createArray",
					[PD__CreateArrayFun] = i "_createArray",
					[PD_ArraySelectFun] = i "select",
					[PD_UnqArraySelectFun] = i "uselect",
					[PD_ArrayUpdateFun] = i "update",
					[PD_ArrayReplaceFun] = i "replace",
					[PD_ArraySizeFun] = i "size",
					[PD_UnqArraySizeFun] = i "usize",
				
					[PD_StdStrictLists] = i "StdStrictLists",
					[PD_cons] = i "cons",
					[PD_decons] = i "decons",
					[PD_nil] = i "nil",
				
					[PD_cons_u] = i "cons_u",
					[PD_decons_u] = i "decons_u",
					[PD_nil_u] = i "nil_u",
				
					[PD_cons_uts] = i "cons_uts",
					[PD_decons_uts] = i "decons_uts",
					[PD_nil_uts] = i "nil_uts",
		
					[PD_ListClass] = i "List",
					[PD_UListClass] = i "UList",
					[PD_UTSListClass] = i "UTSList",
					
					[PD_SmallerFun] = i "<",
					[PD_LessOrEqualFun] = i "<=",
					[PD_IncFun] = i "inc",
					[PD_SubFun] = i "-",
				
					[PD_From] = i "_from",
					[PD_FromThen] = i "_from_then",
					[PD_FromTo] = i "_from_to",
					[PD_FromThenTo] = i "_from_then_to",
					
					[PD_TypeCodeClass] = i "TC",
					[PD_TypeObjectType] = i T_ypeObjectTypeRepresentation_String,
					[PD_TypeConsSymbol] = i "T_ypeConsSymbol",
					[PD_PV_Placeholder] = i "PV_Placeholder",
					[PD_UPV_Placeholder] = i "UPV_Placeholder",
					[PD_UV_Placeholder] = i "UV_Placeholder",
					[PD_unify] = i "_unify",
					[PD_coerce] = i "_coerce",
					[PD_StdDynamic] = i UnderscoreSystemDynamicModule_String,
					[PD_undo_indirections] = i "_undo_indirections",
				
					[PD_DynamicTemp] = i DynamicRepresentation_String,
					[PD_ModuleConsSymbol] = i "__Module",
					[PD_TypeID] = i "T_ypeID",
					[PD_ModuleID] = i "ModuleID",
				
					[PD_StdGeneric] = i "StdGeneric2",
					[PD_TypeBimap] = i "Bimap",
					[PD_ConsBimap] = i "_Bimap",
					[PD_map_to] = i "map_to",
					[PD_map_from] = i "map_from",
					[PD_TypeUNIT] = i "UNIT",
					[PD_ConsUNIT] = i "UNIT",
					[PD_TypeEITHER] = i "EITHER",
					[PD_ConsLEFT] = i "LEFT",
					[PD_ConsRIGHT] = i "RIGHT",
					[PD_TypePAIR] = i "PAIR",
					[PD_ConsPAIR] = i "PAIR",
					[PD_GenericBimap] = i "bimap",
					[PD_bimapId] = i "bimapId",
				
					[PD_TypeGenericDict] = i "GenericDict",
									
					[PD_StdMisc] = i "StdMisc",
					[PD_abort] = i "abort",
					[PD_undef] = i "undef",
					
					[PD_Start] = i "Start",
								
					[PD_DynamicType] = i "type",
					[PD_DynamicValue] = i "value"
		}
	=: idents
	where
		i s = { id_name = s, id_info = allocPtr };

		build_tuples tup_arity max_arity idents
			| tup_arity > max_arity
				= idents
				# tup_name = "_Tuple" +++ toString tup_arity
				# idents = {idents & [GetTupleTypeIndex tup_arity]=i tup_name, [GetTupleConsIndex tup_arity]=i tup_name}
				= build_tuples (inc tup_arity) max_arity idents

		build_variables var_number max_arity idents
			| var_number == max_arity
				= idents
				# var_name = "a" +++ toString var_number
				# idents = {idents & [PD_TypeVar_a0 + var_number] = i var_name}
				= build_variables (inc var_number) max_arity idents

init_identifiers :: !*SymbolTable !*World -> (!*SymbolTable,!*World)
init_identifiers heap world
	# local_predefined_idents = predefined_idents
	# (heap,world) = init_predefined_idents 0 heap world
		with
			init_predefined_idents i heap world
				| i<size local_predefined_idents
					| size local_predefined_idents.[i].id_name>0
						# (heap,world) = initPtr local_predefined_idents.[i].id_info EmptySymbolTableEntry heap world
						= init_predefined_idents (i+1) heap world
						= init_predefined_idents (i+1) heap world
					= (heap,world)
	= (heap,world)

buildPredefinedSymbols :: !*HashTable -> (!.PredefinedSymbols,!*HashTable)
buildPredefinedSymbols hash_table=:{hte_symbol_heap}
	# predef_symbol_table = createArray PD_NrOfPredefSymbols { pds_module = NoIndex, pds_def = NoIndex }
	  hte_symbol_heap = fill_table_without_hashing hte_symbol_heap
	= (predef_symbol_table,fill_table_with_hashing { hash_table & hte_symbol_heap = hte_symbol_heap })
where
	local_predefined_idents = predefined_idents
	
	fill_table_without_hashing hash_table
		= build_variables 0 32 (build_tuples 2 32 hash_table)
			<<= (local_predefined_idents, PD_PredefinedModule)
			<<= (local_predefined_idents, PD_StringType)
			<<= (local_predefined_idents, PD_ListType) <<= (local_predefined_idents, PD_ConsSymbol)<<= (local_predefined_idents, PD_NilSymbol)
			<<= (local_predefined_idents, PD_StrictListType) <<= (local_predefined_idents, PD_StrictConsSymbol) <<= (local_predefined_idents, PD_StrictNilSymbol)
			<<= (local_predefined_idents, PD_UnboxedListType) <<= (local_predefined_idents, PD_UnboxedConsSymbol) <<= (local_predefined_idents, PD_UnboxedNilSymbol)
			<<= (local_predefined_idents, PD_TailStrictListType) <<= (local_predefined_idents, PD_TailStrictConsSymbol) <<= (local_predefined_idents, PD_TailStrictNilSymbol)
			<<= (local_predefined_idents, PD_StrictTailStrictListType) <<= (local_predefined_idents, PD_StrictTailStrictConsSymbol) <<= (local_predefined_idents, PD_StrictTailStrictNilSymbol)
			<<= (local_predefined_idents, PD_UnboxedTailStrictListType) <<= (local_predefined_idents, PD_UnboxedTailStrictConsSymbol) <<= (local_predefined_idents, PD_UnboxedTailStrictNilSymbol)
			<<= (local_predefined_idents, PD_OverloadedListType) <<= (local_predefined_idents, PD_OverloadedConsSymbol) <<= (local_predefined_idents, PD_OverloadedNilSymbol)
			<<= (local_predefined_idents, PD_LazyArrayType)
			<<= (local_predefined_idents, PD_StrictArrayType)
			<<= (local_predefined_idents, PD_UnboxedArrayType)
			<<= (local_predefined_idents, PD_TypeCodeMember)
			<<= (local_predefined_idents, PD_DummyForStrictAliasFun) // MW++
	where
		build_tuples tup_arity max_arity hash_table
			| tup_arity > max_arity
				= hash_table
				= build_tuples (inc tup_arity) max_arity (hash_table <<= (local_predefined_idents, GetTupleTypeIndex tup_arity)
						<<= (local_predefined_idents, GetTupleConsIndex tup_arity))

		build_variables var_number max_arity hash_table
			| var_number == max_arity
				= hash_table
				= build_variables (inc var_number) max_arity (hash_table <<= (local_predefined_idents, PD_TypeVar_a0 + var_number))

	fill_table_with_hashing hash_table
		# hash_table = hash_table
					<<- (local_predefined_idents, IC_Module, PD_StdArray)
					<<- (local_predefined_idents, IC_Module, PD_StdEnum)
					<<- (local_predefined_idents, IC_Module, PD_StdBool)
					<<- (local_predefined_idents, IC_Expression, PD_AndOp)
					<<- (local_predefined_idents, IC_Expression, PD_OrOp)
					<<- (local_predefined_idents, IC_Class, PD_ArrayClass)
					<<- (local_predefined_idents, IC_Expression, PD_CreateArrayFun)
					<<- (local_predefined_idents, IC_Expression, PD__CreateArrayFun)
					<<- (local_predefined_idents, IC_Expression, PD_ArraySelectFun)
					<<- (local_predefined_idents, IC_Expression, PD_UnqArraySelectFun)
					<<- (local_predefined_idents, IC_Expression, PD_ArrayUpdateFun)
					<<- (local_predefined_idents, IC_Expression, PD_ArrayReplaceFun)
					<<- (local_predefined_idents, IC_Expression, PD_ArraySizeFun)
					<<- (local_predefined_idents, IC_Expression, PD_UnqArraySizeFun)

					<<- (local_predefined_idents, IC_Module, PD_StdStrictLists)
					<<- (local_predefined_idents, IC_Expression, PD_cons)
					<<- (local_predefined_idents, IC_Expression, PD_decons)
					<<- (local_predefined_idents, IC_Expression, PD_nil)

					<<- (local_predefined_idents, IC_Expression, PD_cons_u)
					<<- (local_predefined_idents, IC_Expression, PD_decons_u)
					<<- (local_predefined_idents, IC_Expression, PD_nil_u)

					<<- (local_predefined_idents, IC_Expression, PD_cons_uts)
					<<- (local_predefined_idents, IC_Expression, PD_decons_uts)
					<<- (local_predefined_idents, IC_Expression, PD_nil_uts)

					<<- (local_predefined_idents, IC_Class, PD_ListClass)
					<<- (local_predefined_idents, IC_Class, PD_UListClass)
					<<- (local_predefined_idents, IC_Class, PD_UTSListClass)
					
					<<- (local_predefined_idents, IC_Expression, PD_SmallerFun)
					<<- (local_predefined_idents, IC_Expression, PD_LessOrEqualFun)
					<<- (local_predefined_idents, IC_Expression, PD_IncFun)
					<<- (local_predefined_idents, IC_Expression, PD_SubFun)

					<<- (local_predefined_idents, IC_Expression, PD_From)
					<<- (local_predefined_idents, IC_Expression, PD_FromThen)
					<<- (local_predefined_idents, IC_Expression, PD_FromTo)
					<<- (local_predefined_idents, IC_Expression, PD_FromThenTo)
					
					<<- (local_predefined_idents,					 IC_Class, PD_TypeCodeClass)
					<<- (local_predefined_idents,		IC_Type, PD_TypeObjectType)
					<<- (local_predefined_idents,		IC_Expression, PD_TypeConsSymbol)
					<<- (local_predefined_idents,		IC_Expression, PD_PV_Placeholder)
					<<- (local_predefined_idents,		IC_Expression, PD_UPV_Placeholder)
					<<- (local_predefined_idents,		IC_Expression, PD_UV_Placeholder)
					<<- (local_predefined_idents,				IC_Expression, PD_unify)
					<<-	(local_predefined_idents,				IC_Expression, PD_coerce) /* MV */
					<<- (local_predefined_idents,		IC_Module, PD_StdDynamic)
					<<- (local_predefined_idents,	IC_Expression, PD_undo_indirections)

					<<- (local_predefined_idents,			IC_Type, PD_DynamicTemp)
					<<- (local_predefined_idents,			IC_Expression, PD_ModuleConsSymbol)
					<<- (local_predefined_idents,				IC_Type, PD_TypeID)
					<<- (local_predefined_idents,			IC_Expression, PD_ModuleID)

					<<- (local_predefined_idents,			IC_Module, 		PD_StdGeneric)
					<<- (local_predefined_idents,				IC_Type, 		PD_TypeBimap)
					<<- (local_predefined_idents,				IC_Expression, 	PD_ConsBimap)	
					<<- (local_predefined_idents,				IC_Type, 		PD_TypeUNIT)
					<<- (local_predefined_idents,				IC_Expression,	PD_ConsUNIT)
					<<- (local_predefined_idents,				IC_Type, 		PD_TypeEITHER)
					<<- (local_predefined_idents,				IC_Expression,	PD_ConsLEFT)
					<<- (local_predefined_idents,				IC_Expression,	PD_ConsRIGHT)
					<<- (local_predefined_idents,				IC_Type, 		PD_TypePAIR)					
					<<- (local_predefined_idents,				IC_Expression,	PD_ConsPAIR)	
					<<- (local_predefined_idents,				IC_Generic,		PD_GenericBimap)	
					<<- (local_predefined_idents,				IC_Expression,	PD_bimapId)
					<<- (local_predefined_idents,				IC_Type,		PD_TypeGenericDict)
									
					<<- (local_predefined_idents,				IC_Module, 		PD_StdMisc)
					<<- (local_predefined_idents,				IC_Expression, 	PD_abort)
					<<- (local_predefined_idents,				IC_Expression, 	PD_undef)					
					
					<<- (local_predefined_idents,				IC_Expression, PD_Start)

		# bimap_type = local_predefined_idents.[PD_TypeBimap]
		# hash_table = hash_table 
					<<- (local_predefined_idents, IC_Field bimap_type, PD_map_to)
					<<- (local_predefined_idents, IC_Field bimap_type, PD_map_from)
					
		# dynamic_temp_ident = local_predefined_idents.[PD_DynamicTemp]
		# hash_table = hash_table 
					<<- (local_predefined_idents, IC_Field dynamic_temp_ident, PD_DynamicType)
					<<- (local_predefined_idents, IC_Field dynamic_temp_ident, PD_DynamicValue)

		= hash_table

MakeTupleConsSymbIndex arity 	:== arity - 2 + (PD_Arity2TupleSymbol-FirstConstructorPredefinedSymbolIndex)

MaxTupleArity				:== 32

cTCClassSymbIndex			:== 0

cTCMemberSymbIndex			:== 0

cTCInstanceSymbIndex		:== 0

make_type_def :: !Int ![TypeVar] !a !*{#PredefinedSymbol} -> (!TypeDef a,!.{#PredefinedSymbol})
make_type_def type_cons_index type_vars type_rhs pre_def_symbols
	# type_cons_ident = predefined_idents.[type_cons_index]
	= (MakeTypeDef type_cons_ident (map (\tv -> MakeAttributedTypeVar tv) type_vars) type_rhs TA_None [] NoPos, pre_def_symbols)

make_list_definition :: Int Int Int Ident TypeVar AType StrictnessList *{#PredefinedSymbol} -> (!TypeDef TypeRhs,!ConsDef,!ConsDef,!.{#PredefinedSymbol})
make_list_definition list_type_pre_def_symbol_index cons_pre_def_symbol_index nil_pre_def_symbol_index pre_mod_id type_var type_var_with_attr cons_strictness pre_def_symbols
	# cons_ident = predefined_idents.[cons_pre_def_symbol_index]
	  nil_ident = predefined_idents.[nil_pre_def_symbol_index]
	  list_ident = predefined_idents.[list_type_pre_def_symbol_index] 
	  
	  cons_symb = { ds_ident = cons_ident, ds_arity = 2, ds_index = cons_pre_def_symbol_index-FirstConstructorPredefinedSymbolIndex }
	  nil_symb = { ds_ident = nil_ident, ds_arity=0 ,ds_index = nil_pre_def_symbol_index-FirstConstructorPredefinedSymbolIndex }
	  (list_def, pre_def_symbols) = make_type_def list_type_pre_def_symbol_index [type_var] (AlgType [cons_symb,nil_symb]) pre_def_symbols	
	  list_type = MakeAttributedType (TA (MakeNewTypeSymbIdent list_ident 1) [type_var_with_attr])
	  cons_def = {	pc_cons_name = cons_ident, pc_cons_arity = 2, pc_arg_types = [type_var_with_attr, list_type],
				 	pc_args_strictness=cons_strictness,	pc_cons_prio =  NoPrio, pc_exi_vars = [], pc_cons_pos = PreDefPos pre_mod_id}
	  nil_def = {	pc_cons_name = nil_ident, pc_cons_arity = 0, pc_arg_types = [], pc_args_strictness=NotStrict,
	  				pc_cons_prio =  NoPrio, pc_exi_vars = [], pc_cons_pos = PreDefPos pre_mod_id}
	= (list_def,ParsedConstructorToConsDef cons_def,ParsedConstructorToConsDef nil_def,pre_def_symbols);

buildPredefinedModule :: !*PredefinedSymbols -> (!ScannedModule, !.PredefinedSymbols)
buildPredefinedModule pre_def_symbols 
	# type_var_ident = predefined_idents.[PD_TypeVar_a0]
	  string_ident = predefined_idents.[PD_StringType]
	  unb_array_ident = predefined_idents.[PD_UnboxedArrayType]
	  pre_mod_ident = predefined_idents.[PD_PredefinedModule]
	  alias_dummy_ident = predefined_idents.[PD_DummyForStrictAliasFun]

	  type_var						= MakeTypeVar type_var_ident
	  type_var_with_attr			= MakeAttributedType (TV type_var)
	  unb_arr_of_char_type			= MakeAttributedType (TA (MakeNewTypeSymbIdent unb_array_ident 1) [MakeAttributedType (TB BT_Char)])

	  (string_def, pre_def_symbols)	= make_type_def PD_StringType [] (SynType unb_arr_of_char_type) pre_def_symbols
	
	  (list_def,cons_def,nil_def,pre_def_symbols)
		= make_list_definition PD_ListType PD_ConsSymbol PD_NilSymbol pre_mod_ident type_var type_var_with_attr NotStrict pre_def_symbols
	  (strict_list_def,strict_cons_def,strict_nil_def,pre_def_symbols)
		= make_list_definition PD_StrictListType PD_StrictConsSymbol PD_StrictNilSymbol pre_mod_ident type_var type_var_with_attr (Strict 1) pre_def_symbols
	  (unboxed_list_def,unboxed_cons_def,unboxed_nil_def,pre_def_symbols)
		= make_list_definition PD_UnboxedListType PD_UnboxedConsSymbol PD_UnboxedNilSymbol pre_mod_ident type_var type_var_with_attr (Strict 1) pre_def_symbols
	  (tail_strict_list_def,tail_strict_cons_def,tail_strict_nil_def,pre_def_symbols)
		= make_list_definition PD_TailStrictListType PD_TailStrictConsSymbol PD_TailStrictNilSymbol pre_mod_ident type_var type_var_with_attr (Strict 2) pre_def_symbols
	  (strict_tail_strict_list_def,strict_tail_strict_cons_def,strict_tail_strict_nil_def,pre_def_symbols)
		= make_list_definition PD_StrictTailStrictListType PD_StrictTailStrictConsSymbol PD_StrictTailStrictNilSymbol pre_mod_ident type_var type_var_with_attr (Strict 3) pre_def_symbols
	  (unboxed_tail_strict_list_def,unboxed_tail_strict_cons_def,unboxed_tail_strict_nil_def,pre_def_symbols)
		= make_list_definition PD_UnboxedTailStrictListType PD_UnboxedTailStrictConsSymbol PD_UnboxedTailStrictNilSymbol pre_mod_ident type_var type_var_with_attr (Strict 3) pre_def_symbols
	  (overloaded_list_def,overloaded_cons_def,overloaded_nil_def,pre_def_symbols)
		= make_list_definition PD_OverloadedListType PD_OverloadedConsSymbol PD_OverloadedNilSymbol pre_mod_ident type_var type_var_with_attr NotStrict pre_def_symbols

	  (array_def, pre_def_symbols)		= make_type_def PD_LazyArrayType [type_var] (AbstractType cAllBitsClear) pre_def_symbols
	  (strict_def, pre_def_symbols)		= make_type_def PD_StrictArrayType [type_var] (AbstractType cIsHyperStrict) pre_def_symbols
	  (unboxed_def, pre_def_symbols)	= make_type_def PD_UnboxedArrayType [type_var] (AbstractType cIsHyperStrict) pre_def_symbols

	  (type_defs, cons_defs, pre_def_symbols)	= add_tuple_defs pre_mod_ident MaxTupleArity [array_def,strict_def,unboxed_def] [] pre_def_symbols
	  alias_dummy_type = make_identity_fun_type alias_dummy_ident type_var
	  (class_def, member_def, pre_def_symbols) = make_TC_class_def pre_def_symbols
	= ({ mod_name = pre_mod_ident, mod_modification_time = "", mod_type = MK_System, mod_imports = [],  mod_imported_objects = [],
		 mod_defs = {
			def_types = [string_def, list_def,strict_list_def,unboxed_list_def,tail_strict_list_def,strict_tail_strict_list_def,unboxed_tail_strict_list_def,overloaded_list_def : type_defs],
						def_constructors = [cons_def,strict_cons_def,unboxed_cons_def,tail_strict_cons_def,strict_tail_strict_cons_def,unboxed_tail_strict_cons_def,overloaded_cons_def,
											nil_def,strict_nil_def,unboxed_nil_def,tail_strict_nil_def,strict_tail_strict_nil_def,unboxed_tail_strict_nil_def,overloaded_nil_def : cons_defs],
						def_selectors = [], def_classes = [class_def],
			def_macro_indices= { ir_from = 0, ir_to = 0 },def_macros=[],def_members = [member_def], def_funtypes = [alias_dummy_type], def_instances = [], 
			def_generics = [], def_generic_cases = []}}, pre_def_symbols)
where

	add_tuple_defs pre_mod_id tup_arity type_defs cons_defs pre_def_symbols
		| tup_arity >= 2
			# (type_vars, pre_def_symbols)		= make_type_vars tup_arity [] pre_def_symbols
			  tuple_ident = predefined_idents.[GetTupleConsIndex tup_arity]
			  tuple_cons_symb					= { ds_ident = tuple_ident, ds_index = MakeTupleConsSymbIndex tup_arity, ds_arity = tup_arity }
			  
			  (tuple_type_def, pre_def_symbols)	= make_type_def (GetTupleTypeIndex tup_arity) type_vars (AlgType [tuple_cons_symb]) pre_def_symbols
			  tuple_cons_def	= { pc_cons_name = tuple_ident, pc_cons_arity = tup_arity, pc_cons_pos = PreDefPos pre_mod_id,
			  						pc_arg_types = [ MakeAttributedType (TV tv) \\ tv <- type_vars],
			  						pc_args_strictness = NotStrict,
			  						pc_cons_prio =  NoPrio, pc_exi_vars = []}
			= add_tuple_defs pre_mod_id (dec tup_arity) [tuple_type_def : type_defs] [ParsedConstructorToConsDef tuple_cons_def : cons_defs] pre_def_symbols
			= (type_defs, cons_defs, pre_def_symbols)
	where
		make_type_vars nr_of_vars type_vars pre_def_symbols
			| nr_of_vars == 0
				= (type_vars, pre_def_symbols)
				# nr_of_vars = dec nr_of_vars
				# var_ident = predefined_idents.[PD_TypeVar_a0 + nr_of_vars]
				= make_type_vars nr_of_vars [MakeTypeVar var_ident : type_vars] pre_def_symbols
		
	make_TC_class_def pre_def_symbols
		# tc_class_name = predefined_idents.[PD_TypeCodeClass]
		  type_var_ident = predefined_idents.[PD_TypeVar_a0]
		  tc_member_name = predefined_idents.[PD_TypeCodeMember]
		
		  class_var = MakeTypeVar type_var_ident

		  me_type = { st_vars = [], st_args = [], st_args_strictness=NotStrict, st_arity = 0,
					  st_result = { at_attribute = TA_None, at_type = TV class_var },
					  st_context = [ {tc_class = TCClass {glob_module = NoIndex, glob_object = {ds_ident = tc_class_name, ds_arity = 1, ds_index = NoIndex }},
					   				tc_types = [ TV class_var ], tc_var = nilPtr}],
					  st_attr_vars = [], st_attr_env = [] }

		  member_def = { me_symb = tc_member_name, me_type = me_type, me_pos = NoPos, me_priority = NoPrio,
						 me_offset = NoIndex, me_class_vars = [], me_class = { glob_module = NoIndex, glob_object = NoIndex}, me_type_ptr = nilPtr }
		
		  class_def = { class_name = tc_class_name, class_arity = 1, class_args = [class_var], class_context = [],
		  				class_members = {{ds_ident = tc_member_name, ds_index = cTCMemberSymbIndex, ds_arity = 0 }}, class_cons_vars = 0,
						class_dictionary = { ds_ident = { tc_class_name & id_info = nilPtr }, ds_arity = 0, ds_index = NoIndex }, class_pos = NoPos,
						class_arg_kinds = [] }

		= (class_def, member_def, pre_def_symbols)

// MW..
	make_identity_fun_type alias_dummy_id type_var
		# a = { at_attribute = TA_Anonymous, at_type = TV type_var }
		  id_symbol_type = { st_vars = [], st_args = [a], st_args_strictness = Strict 1, st_arity = 1, st_result = a, st_context = [], 
							st_attr_vars = [], st_attr_env = [] } // !.a -> .a
		= { ft_symb = alias_dummy_id, ft_arity = 1, ft_priority = NoPrio, ft_type = id_symbol_type, ft_pos = NoPos,
			ft_specials = SP_None, ft_type_ptr = nilPtr }

// changes requires recompile of {static,dynamic}-linker plus all dynamics ever made
UnderscoreSystemDynamicModule_String	:== "_SystemDynamic"	

DynamicRepresentation_String			:== "DynamicTemp"		

T_ypeObjectTypeRepresentation_String	:== "T_ypeObjectType"

// List-type
PD_ListType_String				:== "_List"
PD_ConsSymbol_String			:== "_Cons"
PD_NilSymbol_String				:== "_Nil"

// Array-type
PD_UnboxedArray_String			:== "_#Array"
// ... MV

