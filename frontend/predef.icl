implementation module predef

import syntax, hashtable

cPredefinedModuleIndex :== 1

::	PredefinedSymbols	:== {# PredefinedSymbol}

::	PredefinedSymbol =
	{	pds_ident	:: !Ident
	,	pds_module	:: !Index
	,	pds_def		:: !Index
	}

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
PD_LessOrEqualFun:== 139
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
PD_variablePlaceholder		:== 170
PD_undo_indirections		:== 171

PD_TypeID					:== 172
PD_ModuleID					:== 173
PD_ModuleConsSymbol			:== 174

/* Generics */

PD_StdGeneric				:== 175

PD_TypeISO					:== 176
PD_ConsISO					:== 177
PD_iso_to					:== 178
PD_iso_from					:== 179

PD_TypeUNIT					:== 180
PD_ConsUNIT					:== 181
PD_TypeEITHER				:== 182
PD_ConsLEFT					:== 183
PD_ConsRIGHT				:== 184
PD_TypePAIR					:== 185
PD_ConsPAIR					:== 186
PD_TypeARROW				:== 187
PD_ConsARROW				:== 188

PD_TypeConsDefInfo			:== 189 
PD_ConsConsDefInfo			:== 190
PD_TypeTypeDefInfo			:== 191 
PD_ConsTypeDefInfo			:== 192
PD_cons_info				:== 193
PD_TypeCONS					:== 194
PD_ConsCONS					:== 195

PD_isomap_ARROW_			:== 196
PD_isomap_ID				:== 197

PD_NrOfPredefSymbols		:== 198

(<<=) infixl
(<<=) state val
	:==	let (array, symbol_table) = state
			(name, index) = val
			(id_info, new_symbol_table) = newPtr EmptySymbolTableEntry symbol_table
	  	in 	({ array & [index] = { pds_ident = { id_name = name, id_info = id_info }, pds_module = NoIndex, pds_def = NoIndex } }, new_symbol_table)

(<<+) infixl
(<<+) state val
	:==	let (array, symbol_table) = state
			(cons_and_nil_idents, index) = val
	  	in 	({ array & [index] = { pds_ident = cons_and_nil_idents.[index-FirstConstructorPredefinedSymbolIndex], pds_module = NoIndex, pds_def = NoIndex } }, symbol_table)

(<<-) infixl
(<<-) (array, hash_table) (name, table_kind, index)
//	# (id, hash_table) = putIdentInHashTable name table_kind hash_table
	# ({boxed_ident=id}, hash_table) = putIdentInHashTable name table_kind hash_table
	= ({ array & [index] = { pds_ident = id, pds_module = NoIndex, pds_def = NoIndex } }, hash_table)
	
GetTupleConsIndex tup_arity :== PD_Arity2TupleSymbol + tup_arity - 2
GetTupleTypeIndex tup_arity :== PD_Arity2TupleType + tup_arity - 2

cons_and_nil_idents :: {!Ident}
cons_and_nil_idents =: {
	{ id_name = "_Cons", id_info = allocPtr },
	{ id_name = "_!Cons", id_info = allocPtr },
	{ id_name = "_#Cons", id_info = allocPtr },
	{ id_name = "_Cons!", id_info = allocPtr },
	{ id_name = "_!Cons!", id_info = allocPtr },
	{ id_name = "_#Cons!", id_info = allocPtr },
	{ id_name = "_|Cons", id_info = allocPtr },
	{ id_name = "_Nil", id_info = allocPtr },
	{ id_name = "_!Nil", id_info = allocPtr },
	{ id_name = "_#Nil", id_info = allocPtr },
	{ id_name = "_Nil!", id_info = allocPtr },
	{ id_name = "_!Nil!", id_info = allocPtr },
	{ id_name = "_#Nil!", id_info = allocPtr },
	{ id_name = "_|Nil", id_info = allocPtr }
  }

init_identifiers :: *SymbolTable -> *SymbolTable
init_identifiers heap
	# local_cons_and_nil_idents = cons_and_nil_idents
	# heap = init_cons_and_nil_idents 0 heap
		with
			init_cons_and_nil_idents i heap
				| i<size local_cons_and_nil_idents
					# heap=initPtr local_cons_and_nil_idents.[i].id_info EmptySymbolTableEntry heap
					= init_cons_and_nil_idents (i+1) heap
					= heap
	= heap

buildPredefinedSymbols :: !*HashTable -> (!.PredefinedSymbols,!*HashTable)
buildPredefinedSymbols hash_table=:{hte_symbol_heap}
	# predef_symbol_table = createArray PD_NrOfPredefSymbols { pds_ident = { id_name = "", id_info = nilPtr }, pds_module = NoIndex, pds_def = NoIndex }
	  (predef_symbol_table, hte_symbol_heap) = fill_table_without_hashing (predef_symbol_table, hte_symbol_heap)
	= fill_table_with_hashing (predef_symbol_table, { hash_table & hte_symbol_heap = hte_symbol_heap })
where
	local_cons_and_nil_idents = cons_and_nil_idents
	
	fill_table_without_hashing tables
		= build_variables 0 32 (build_tuples 2 32 tables)
			<<= ("_predefined", PD_PredefinedModule)
			<<= ("_String", PD_StringType)
			<<= ("_List", PD_ListType) <<+ (local_cons_and_nil_idents, PD_ConsSymbol)<<+ (local_cons_and_nil_idents, PD_NilSymbol)
			<<= ("_!List", PD_StrictListType) <<+ (local_cons_and_nil_idents, PD_StrictConsSymbol) <<+ (local_cons_and_nil_idents, PD_StrictNilSymbol)
			<<= ("_#List", PD_UnboxedListType) <<+ (local_cons_and_nil_idents, PD_UnboxedConsSymbol) <<+ (local_cons_and_nil_idents, PD_UnboxedNilSymbol)
			<<= ("_List!", PD_TailStrictListType) <<+ (local_cons_and_nil_idents, PD_TailStrictConsSymbol) <<+ (local_cons_and_nil_idents, PD_TailStrictNilSymbol)
			<<= ("_!List!", PD_StrictTailStrictListType) <<+ (local_cons_and_nil_idents, PD_StrictTailStrictConsSymbol) <<+ (local_cons_and_nil_idents, PD_StrictTailStrictNilSymbol)
			<<= ("_#List!", PD_UnboxedTailStrictListType) <<+ (local_cons_and_nil_idents, PD_UnboxedTailStrictConsSymbol) <<+ (local_cons_and_nil_idents, PD_UnboxedTailStrictNilSymbol)
			<<= ("_|List", PD_OverloadedListType) <<+ (local_cons_and_nil_idents, PD_OverloadedConsSymbol) <<+ (local_cons_and_nil_idents, PD_OverloadedNilSymbol)
			<<= ("_Array", PD_LazyArrayType) <<= ("_!Array", PD_StrictArrayType) <<= ("_#Array", PD_UnboxedArrayType)
			<<= ("_type_code", PD_TypeCodeMember)
			<<= ("_dummyForStrictAlias", PD_DummyForStrictAliasFun) // MW++
	where

		build_tuples tup_arity max_arity tables
			| tup_arity > max_arity
				= tables
				# tup_name = "_Tuple" +++ toString tup_arity
				= build_tuples (inc tup_arity) max_arity (tables <<= (tup_name, GetTupleTypeIndex tup_arity)
						<<= (tup_name, GetTupleConsIndex tup_arity))

		build_variables var_number max_arity tables
			| var_number == max_arity
				= tables
				# var_name = "a" +++ toString var_number
				= build_variables (inc var_number) max_arity (tables <<= (var_name, PD_TypeVar_a0 + var_number))

	fill_table_with_hashing tables
		# (predefs, hash_table) = tables	
					<<- ("_SystemArray", IC_Module, PD_StdArray) <<- ("StdEnum", IC_Module, PD_StdEnum) <<- ("StdBool", IC_Module, PD_StdBool)
					<<- ("&&", IC_Expression, PD_AndOp) <<- ("||", IC_Expression, PD_OrOp)
					<<- ("Array", IC_Class, PD_ArrayClass)
					<<- ("createArray", IC_Expression, PD_CreateArrayFun)
					<<- ("_createArray", IC_Expression, PD__CreateArrayFun)
					<<- ("select", IC_Expression, PD_ArraySelectFun)
					<<- ("uselect", IC_Expression, PD_UnqArraySelectFun)
					<<- ("update", IC_Expression, PD_ArrayUpdateFun)
					<<- ("replace", IC_Expression, PD_ArrayReplaceFun)
					<<- ("size", IC_Expression, PD_ArraySizeFun)
					<<- ("usize", IC_Expression, PD_UnqArraySizeFun)

					<<- ("StdStrictLists", IC_Module, PD_StdStrictLists)
					<<- ("cons", IC_Expression, PD_cons)
					<<- ("decons", IC_Expression, PD_decons)
					<<- ("nil", IC_Expression, PD_nil)

					<<- ("cons_u", IC_Expression, PD_cons_u)
					<<- ("decons_u", IC_Expression, PD_decons_u)
					<<- ("nil_u", IC_Expression, PD_nil_u)

					<<- ("cons_uts", IC_Expression, PD_cons_uts)
					<<- ("decons_uts", IC_Expression, PD_decons_uts)
					<<- ("nil_uts", IC_Expression, PD_nil_uts)

					<<- ("List", IC_Class, PD_ListClass)
					<<- ("UList", IC_Class, PD_UListClass)
					<<- ("UTSList", IC_Class, PD_UTSListClass)
					
// RWS ...					<<- ("_smaller", IC_Expression, PD_SmallerFun) <<- ("_inc", IC_Expression, PD_IncFun)
					<<- ("<", IC_Expression, PD_SmallerFun)
					<<- ("<=", IC_Expression, PD_LessOrEqualFun)
					<<- ("inc", IC_Expression, PD_IncFun)
					<<- ("-", IC_Expression, PD_SubFun)
// ... RWS
					<<- ("_from", IC_Expression, PD_From) <<- ("_from_then", IC_Expression, PD_FromThen)
					<<- ("_from_to", IC_Expression, PD_FromTo) <<- ("_from_then_to", IC_Expression, PD_FromThenTo)
					
					<<- ("TC", 					IC_Class, PD_TypeCodeClass)
					<<- ("T_ypeObjectType",		IC_Type, PD_TypeObjectType)
					<<- ("T_ypeConsSymbol",		IC_Expression, PD_TypeConsSymbol)
					<<- ("P_laceholder",		IC_Expression, PD_variablePlaceholder)
					<<- ("_unify",				IC_Expression, PD_unify)
					<<-	("_coerce",				IC_Expression, PD_coerce) /* MV */
					<<- ("_SystemDynamic",		IC_Module, PD_StdDynamic)
					<<- ("_undo_indirections",	IC_Expression, PD_undo_indirections)
// MV..
					<<- ("DynamicTemp",			IC_Type, PD_DynamicTemp)
					<<- ("__Module",			IC_Expression, PD_ModuleConsSymbol)
					<<- ("T_ypeID",				IC_Type, PD_TypeID)
					<<- ("ModuleID",			IC_Expression, PD_ModuleID)
// ..MV
					
// AA..
					<<- ("StdGeneric",			IC_Module, 		PD_StdGeneric)
					<<- ("ISO",					IC_Type, 		PD_TypeISO)
					<<- ("_ISO",				IC_Expression, 	PD_ConsISO)					
					//<<- ("iso_from",			IC_Field {id_name="", id_info=nilPtr}, PD_iso_from)
					//<<- ("iso_to",			IC_Field {id_name="", id_info=nilPtr}, PD_iso_to)					
					<<- ("UNIT",				IC_Type, 		PD_TypeUNIT)
					<<- ("UNIT",				IC_Expression,	PD_ConsUNIT)
					<<- ("EITHER",				IC_Type, 		PD_TypeEITHER)
					<<- ("LEFT",				IC_Expression,	PD_ConsLEFT)
					<<- ("RIGHT",				IC_Expression,	PD_ConsRIGHT)
					<<- ("PAIR",				IC_Type, 		PD_TypePAIR)					
					<<- ("PAIR",				IC_Expression,	PD_ConsPAIR)					
					<<- ("ARROW",				IC_Type, 		PD_TypeARROW)
					<<- ("ARROW",				IC_Expression, 	PD_ConsARROW)										
					<<- ("isomap_ARROW_",		IC_Expression, 	PD_isomap_ARROW_)										
					<<- ("isomap_ID",			IC_Expression, 	PD_isomap_ID)										
					<<- ("ConsDefInfo",			IC_Type, 		PD_TypeConsDefInfo)					
					<<- ("_ConsDefInfo",		IC_Expression,	PD_ConsConsDefInfo)					
					<<- ("TypeDefInfo",			IC_Type, 		PD_TypeTypeDefInfo)					
					<<- ("_TypeDefInfo",		IC_Expression,	PD_ConsTypeDefInfo)					
					<<- ("CONS",				IC_Type, 		PD_TypeCONS)					
					<<- ("CONS",				IC_Expression,	PD_ConsCONS)					
					<<- ("_cons_info",			IC_Expression, 	PD_cons_info)										

					<<- ("StdMisc",				IC_Module, 		PD_StdMisc)
					<<- ("abort",				IC_Expression, 	PD_abort)
					<<- ("undef",				IC_Expression, 	PD_undef)					
// ..AA					
					
					<<- ("Start",				IC_Expression, PD_Start)

		# ({pds_ident}, predefs) = predefs![PD_TypeISO]
		# (predefs, hash_table)= (predefs, hash_table) 
			<<- ("iso_from", 			IC_Field pds_ident, PD_iso_from)
			<<- ("iso_to", 				IC_Field pds_ident, PD_iso_to)

		# ({pds_ident}, predefs) = predefs![PD_DynamicTemp]
		# (predefs, hash_table)= (predefs, hash_table) 
			<<- ("type",				IC_Field pds_ident, PD_DynamicType)
			<<- ("value",				IC_Field pds_ident, PD_DynamicValue)
			<<- ("Start",				IC_Expression, PD_Start)
		= (predefs, hash_table)

MakeTupleConsSymbIndex arity 	:== arity - 2 + (PD_Arity2TupleSymbol-FirstConstructorPredefinedSymbolIndex)

MaxTupleArity				:== 32

cTCClassSymbIndex			:== 0

cTCMemberSymbIndex			:== 0

cTCInstanceSymbIndex		:== 0

make_type_def :: !Int ![TypeVar] !a !*{#PredefinedSymbol} -> (!TypeDef a,!.{#PredefinedSymbol})
make_type_def type_cons_index type_vars type_rhs pre_def_symbols
	# (type_ident, pre_def_symbols) = pre_def_symbols![type_cons_index]
	= (MakeTypeDef type_ident.pds_ident (map (\tv -> MakeAttributedTypeVar tv) type_vars) type_rhs TA_None [] NoPos, pre_def_symbols)

make_list_definition :: Int Int Int Ident TypeVar AType *{#PredefinedSymbol} -> (!TypeDef TypeRhs,!ConsDef,!ConsDef,!.{#PredefinedSymbol})
make_list_definition list_type_pre_def_symbol_index cons_pre_def_symbol_index nil_pre_def_symbol_index pre_mod_id type_var type_var_with_attr pre_def_symbols
	# (cons_id, pre_def_symbols) = pre_def_symbols![cons_pre_def_symbol_index]
	  (nil_id, pre_def_symbols)	= pre_def_symbols![nil_pre_def_symbol_index]
	  (list_id, pre_def_symbols) = pre_def_symbols![list_type_pre_def_symbol_index]
	  cons_symb = { ds_ident = cons_id.pds_ident, ds_arity = 2, ds_index = cons_pre_def_symbol_index-FirstConstructorPredefinedSymbolIndex }
	  nil_symb = { ds_ident = nil_id.pds_ident, ds_arity=0 ,ds_index = nil_pre_def_symbol_index-FirstConstructorPredefinedSymbolIndex }
	  (list_def, pre_def_symbols) = make_type_def list_type_pre_def_symbol_index [type_var] (AlgType [cons_symb,nil_symb]) pre_def_symbols	
	  list_type = MakeAttributedType (TA (MakeNewTypeSymbIdent list_id.pds_ident 1) [type_var_with_attr])
	  cons_def = {	pc_cons_name = cons_id.pds_ident, pc_cons_arity = 2, pc_arg_types = [type_var_with_attr, list_type],
	  				pc_cons_prio =  NoPrio, pc_exi_vars = [], pc_cons_pos = PreDefPos pre_mod_id}
	  nil_def = {	pc_cons_name = nil_id.pds_ident, pc_cons_arity = 0, pc_arg_types = [],
	  				pc_cons_prio =  NoPrio, pc_exi_vars = [], pc_cons_pos = PreDefPos pre_mod_id}
	= (list_def,ParsedConstructorToConsDef cons_def,ParsedConstructorToConsDef nil_def,pre_def_symbols);

buildPredefinedModule :: !*PredefinedSymbols -> (!ScannedModule, !.PredefinedSymbols)
buildPredefinedModule pre_def_symbols 
	# (type_var_id, pre_def_symbols)	= pre_def_symbols![PD_TypeVar_a0]
	  (string_id, pre_def_symbols)		= pre_def_symbols![PD_StringType]
	  (unb_array_id, pre_def_symbols)	= pre_def_symbols![PD_UnboxedArrayType]
	  (pre_mod_symb, pre_def_symbols)	= pre_def_symbols![PD_PredefinedModule]
	  (alias_dummy_symb,pre_def_symbols)= pre_def_symbols![PD_DummyForStrictAliasFun]
	  pre_mod_id						= pre_mod_symb.pds_ident

	  type_var						= MakeTypeVar type_var_id.pds_ident
	  type_var_with_attr			= MakeAttributedType (TV type_var)
	  unb_arr_of_char_type			= MakeAttributedType (TA (MakeNewTypeSymbIdent unb_array_id.pds_ident 1) [MakeAttributedType (TB BT_Char)])

	  (string_def, pre_def_symbols)	= make_type_def PD_StringType [] (SynType unb_arr_of_char_type) pre_def_symbols
	
	  (list_def,cons_def,nil_def,pre_def_symbols)
		= make_list_definition PD_ListType PD_ConsSymbol PD_NilSymbol pre_mod_id type_var type_var_with_attr pre_def_symbols
	  (strict_list_def,strict_cons_def,strict_nil_def,pre_def_symbols)
		= make_list_definition PD_StrictListType PD_StrictConsSymbol PD_StrictNilSymbol pre_mod_id type_var type_var_with_attr pre_def_symbols
	  (unboxed_list_def,unboxed_cons_def,unboxed_nil_def,pre_def_symbols)
		= make_list_definition PD_UnboxedListType PD_UnboxedConsSymbol PD_UnboxedNilSymbol pre_mod_id type_var type_var_with_attr pre_def_symbols
	  (tail_strict_list_def,tail_strict_cons_def,tail_strict_nil_def,pre_def_symbols)
		= make_list_definition PD_TailStrictListType PD_TailStrictConsSymbol PD_TailStrictNilSymbol pre_mod_id type_var type_var_with_attr pre_def_symbols
	  (strict_tail_strict_list_def,strict_tail_strict_cons_def,strict_tail_strict_nil_def,pre_def_symbols)
		= make_list_definition PD_StrictTailStrictListType PD_StrictTailStrictConsSymbol PD_StrictTailStrictNilSymbol pre_mod_id type_var type_var_with_attr pre_def_symbols
	  (unboxed_tail_strict_list_def,unboxed_tail_strict_cons_def,unboxed_tail_strict_nil_def,pre_def_symbols)
		= make_list_definition PD_UnboxedTailStrictListType PD_UnboxedTailStrictConsSymbol PD_UnboxedTailStrictNilSymbol pre_mod_id type_var type_var_with_attr pre_def_symbols
	  (overloaded_list_def,overloaded_cons_def,overloaded_nil_def,pre_def_symbols)
		= make_list_definition PD_OverloadedListType PD_OverloadedConsSymbol PD_OverloadedNilSymbol pre_mod_id type_var type_var_with_attr pre_def_symbols

	  (array_def, pre_def_symbols)		= make_type_def PD_LazyArrayType [type_var] (AbstractType cAllBitsClear) pre_def_symbols
	  (strict_def, pre_def_symbols)		= make_type_def PD_StrictArrayType [type_var] (AbstractType cIsHyperStrict) pre_def_symbols
	  (unboxed_def, pre_def_symbols)	= make_type_def PD_UnboxedArrayType [type_var] (AbstractType cIsHyperStrict) pre_def_symbols

	  (type_defs, cons_defs, pre_def_symbols)	= add_tuple_defs pre_mod_id MaxTupleArity [array_def,strict_def,unboxed_def] [] pre_def_symbols
	  alias_dummy_type = make_identity_fun_type alias_dummy_symb.pds_ident type_var // MW++
	  (class_def, member_def, pre_def_symbols) = make_TC_class_def pre_def_symbols
	= ({ mod_name = pre_mod_id, mod_type = MK_System, mod_imports = [],  mod_imported_objects = [],
		 mod_defs = {
			def_types = [string_def, list_def,strict_list_def,unboxed_list_def,tail_strict_list_def,strict_tail_strict_list_def,unboxed_tail_strict_list_def,overloaded_list_def : type_defs],
						def_constructors = [cons_def,strict_cons_def,unboxed_cons_def,tail_strict_cons_def,strict_tail_strict_cons_def,unboxed_tail_strict_cons_def,overloaded_cons_def,
											nil_def,strict_nil_def,unboxed_nil_def,tail_strict_nil_def,strict_tail_strict_nil_def,unboxed_tail_strict_nil_def,overloaded_nil_def : cons_defs],
						def_selectors = [], def_classes = [class_def],
			def_macros = { ir_from = 0, ir_to = 0 }, def_members = [member_def], def_funtypes = [alias_dummy_type], def_instances = [], /* AA */ def_generics = [] }}, pre_def_symbols)
where
	add_tuple_defs pre_mod_id tup_arity type_defs cons_defs pre_def_symbols
		| tup_arity >= 2
			# (type_vars, pre_def_symbols)		= make_type_vars tup_arity [] pre_def_symbols
			  (tuple_id, pre_def_symbols)		= pre_def_symbols![GetTupleConsIndex tup_arity]
			  tuple_cons_symb					= { ds_ident = tuple_id.pds_ident, ds_index = MakeTupleConsSymbIndex tup_arity, ds_arity = tup_arity }
			  
			  (tuple_type_def, pre_def_symbols)	= make_type_def (GetTupleTypeIndex tup_arity) type_vars (AlgType [tuple_cons_symb]) pre_def_symbols
			  tuple_cons_def	= { pc_cons_name = tuple_id.pds_ident, pc_cons_arity = tup_arity, pc_cons_pos = PreDefPos pre_mod_id,
			  						pc_arg_types = [ MakeAttributedType (TV tv) \\ tv <- type_vars], pc_cons_prio =  NoPrio, pc_exi_vars = []}
			= add_tuple_defs pre_mod_id (dec tup_arity) [tuple_type_def : type_defs] [ParsedConstructorToConsDef tuple_cons_def : cons_defs] pre_def_symbols
			= (type_defs, cons_defs, pre_def_symbols)
	where
		make_type_vars nr_of_vars type_vars pre_def_symbols
			| nr_of_vars == 0
				= (type_vars, pre_def_symbols)
				# nr_of_vars = dec nr_of_vars
				# (var_id, pre_def_symbols) = pre_def_symbols![PD_TypeVar_a0 + nr_of_vars]
				= make_type_vars nr_of_vars [MakeTypeVar var_id.pds_ident : type_vars] pre_def_symbols
		
	make_TC_class_def pre_def_symbols
		# (tc_class_name, pre_def_symbols)		= pre_def_symbols![PD_TypeCodeClass]
		  (type_var_id, pre_def_symbols)		= pre_def_symbols![PD_TypeVar_a0]
		  (tc_member_name, pre_def_symbols)		= pre_def_symbols![PD_TypeCodeMember]
		
		  class_var = MakeTypeVar type_var_id.pds_ident

		  me_type = { st_vars = [], st_args = [], st_arity = 0,
					  st_result = { at_attribute = TA_None, at_annotation = AN_None, at_type = TV class_var },
					  st_context = [ {tc_class = {glob_module = NoIndex, glob_object = {ds_ident = tc_class_name.pds_ident, ds_arity = 1, ds_index = NoIndex }},
					   				tc_types = [ TV class_var ], tc_var = nilPtr}],
					  st_attr_vars = [], st_attr_env = [] }

		  member_def = { me_symb = tc_member_name.pds_ident, me_type = me_type, me_pos = NoPos, me_priority = NoPrio,
						 me_offset = NoIndex, me_class_vars = [], me_class = { glob_module = NoIndex, glob_object = NoIndex}, me_type_ptr = nilPtr }
		
		  class_def = { class_name = tc_class_name.pds_ident, class_arity = 1, class_args = [class_var], class_context = [],
		  				class_members = {{ds_ident = tc_member_name.pds_ident, ds_index = cTCMemberSymbIndex, ds_arity = 0 }}, class_cons_vars = 0,
						class_dictionary = { ds_ident = { tc_class_name.pds_ident & id_info = nilPtr }, ds_arity = 0, ds_index = NoIndex }, class_pos = NoPos,
						class_arg_kinds = [] }

		= (class_def, member_def, pre_def_symbols)

// MW..
	make_identity_fun_type alias_dummy_id type_var
		# a = { at_attribute = TA_Anonymous, at_annotation = AN_Strict, at_type = TV type_var }
		  id_symbol_type = { st_vars = [], st_args = [a], st_arity = 1, st_result = a, st_context = [], 
							st_attr_vars = [], st_attr_env = [] } // !.a -> .a
		= { ft_symb = alias_dummy_id, ft_arity = 1, ft_priority = NoPrio, ft_type = id_symbol_type, ft_pos = NoPos,
			ft_specials = SP_None, ft_type_ptr = nilPtr }
// ..MW
