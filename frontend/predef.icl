implementation module predef

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
PD_StdDynamics				:== 134
PD_undo_indirections		:== 135

// MV ...
//PD_ModuleType				:== 136
PD_ModuleConsSymbol			:== 137
// ... MV

/* Generics */
PD_StdGeneric				:== 138
PD_TypeISO					:== 139
PD_ConsISO					:== 140
PD_iso_to					:== 141
PD_iso_from					:== 142

PD_TypeUNIT					:== 143
PD_ConsUNIT					:== 144
PD_TypeEITHER				:== 145
PD_ConsLEFT					:== 146
PD_ConsRIGHT				:== 147
PD_TypePAIR					:== 148
PD_ConsPAIR					:== 149
PD_TypeARROW				:== 150
PD_ConsARROW				:== 151

PD_TypeConsDefInfo			:== 152 
PD_ConsConsDefInfo			:== 153
PD_TypeTypeDefInfo			:== 154 
PD_ConsTypeDefInfo			:== 155
PD_cons_info				:== 156
PD_TypeCONS					:== 157
PD_ConsCONS					:== 158

PD_isomap_ARROW_			:== 159
PD_isomap_ID				:== 160

/* StdMisc */
PD_StdMisc					:== 161
PD_abort					:== 162
PD_undef					:== 163

PD_Start					:== 164

PD_DummyForStrictAliasFun	:== 165

PD_NrOfPredefSymbols		:== 166

(<<=) infixl
(<<=) state val
	:==	let (array, symbol_table) = state
			(name, index) = val
			(id_info, new_symbol_table) = newPtr EmptySymbolTableEntry symbol_table
	  	in 	({ array & [index] = { pds_ident = { id_name = name, id_info = id_info }, pds_module = NoIndex, pds_def = NoIndex } }, new_symbol_table)

(<<-) infixl
(<<-) (array, hash_table) (name, table_kind, index)
//	# (id, hash_table) = putIdentInHashTable name table_kind hash_table
	# ({boxed_ident=id}, hash_table) = putIdentInHashTable name table_kind hash_table
	= ({ array & [index] = { pds_ident = id, pds_module = NoIndex, pds_def = NoIndex } }, hash_table)
	
GetTupleConsIndex tup_arity :== PD_Arity2TupleSymbol + tup_arity - 2
GetTupleTypeIndex tup_arity :== PD_Arity2TupleType + tup_arity - 2

buildPredefinedSymbols :: !*HashTable -> (!.PredefinedSymbols,!*HashTable)
buildPredefinedSymbols hash_table=:{hte_symbol_heap}
	# predef_symbol_table = createArray PD_NrOfPredefSymbols { pds_ident = { id_name = "", id_info = nilPtr }, pds_module = NoIndex, pds_def = NoIndex }
	  (predef_symbol_table, hte_symbol_heap) = fill_table_without_hashing (predef_symbol_table, hte_symbol_heap)
	= fill_table_with_hashing (predef_symbol_table, { hash_table & hte_symbol_heap = hte_symbol_heap })
where	
	fill_table_without_hashing tables
		= build_variables 0 32 (build_tuples 2 32 tables)
			<<= ("_predefined", PD_PredefinedModule)
			<<= ("_string", PD_StringType)
			<<= ("_list", PD_ListType) <<= ("_cons", PD_ConsSymbol) <<= ("_nil", PD_NilSymbol)
			<<= ("_array", PD_LazyArrayType) <<= ("_!array", PD_StrictArrayType) <<= ("_#array", PD_UnboxedArrayType)
			<<= ("_type_code", PD_TypeCodeMember)
			<<= ("_dummyForStrictAlias", PD_DummyForStrictAliasFun) // MW++
	where

		build_tuples tup_arity max_arity tables
			| tup_arity > max_arity
				= tables
				# tup_name = "_tuple" +++ toString tup_arity
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
					<<- ("uselect", IC_Expression, PD_UnqArraySelectFun) <<- ("update", IC_Expression, PD_ArrayUpdateFun)
					<<- ("replace", IC_Expression, PD_ArrayReplaceFun) <<- ("size", IC_Expression, PD_ArraySizeFun)
					<<- ("usize", IC_Expression, PD_UnqArraySizeFun)
// RWS ...		<<- ("_smaller", IC_Expression, PD_SmallerFun) <<- ("_inc", IC_Expression, PD_IncFun)
					<<- ("<", IC_Expression, PD_SmallerFun) <<- ("<=", IC_Expression, PD_LessOrEqualFun)
					<<- ("-", IC_Expression, PD_SubFun) <<- ("inc", IC_Expression, PD_IncFun)
// ... RWS
					<<- ("_from", IC_Expression, PD_From) <<- ("_from_then", IC_Expression, PD_FromThen)
					<<- ("_from_to", IC_Expression, PD_FromTo) <<- ("_from_then_to", IC_Expression, PD_FromThenTo)
					
					<<- ("TC", 					IC_Class, PD_TypeCodeClass)
					<<- ("T_ypeObjectType",		IC_Type, PD_TypeObjectType)
					<<- ("T_ypeConsSymbol",		IC_Expression, PD_TypeConsSymbol)
					<<- ("P_laceholder",		IC_Expression, PD_variablePlaceholder)
					<<- ("_unify",				IC_Expression, PD_unify)
					<<-	("_coerce",				IC_Expression, PD_coerce) /* MV */
					<<- ("StdDynamic",			IC_Module, PD_StdDynamics)
					<<- ("_undo_indirections",	IC_Expression, PD_undo_indirections)
// MV..
					<<- ("DynamicTemp",			IC_Type, PD_DynamicTemp)
//					<<- ("Module",				IC_Type, PD_ModuleType)
					<<- ("__Module",			IC_Expression, PD_ModuleConsSymbol)
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

MakeTupleConsSymbIndex arity 	:== arity - 2 + cArity2TupleConsSymbIndex
MakeTupleTypeSymbIndex arity 	:== arity - 2 + cArity2TupleTypeSymbIndex

MakeNilExpression pre_def_symbols			:== PE_List [PE_Ident pre_def_symbols.[PD_NilSymbol]]
MakeConsExpression a1 a2 pre_def_symbols	:== PE_List [PE_Ident pre_def_symbols.[PD_ConsSymbol], a1, a2]

MaxTupleArity				:== 32

cLazyArray			:== 0
cStrictArray		:== 1
cUnboxedArray		:== 2

cConsSymbIndex				:== 0
cNilSymbIndex				:== 1
cArity2TupleConsSymbIndex	:== 2
//Arity32TupleConsSymbIndex	:== 32

cListTypeSymbIndex			:== 0
cArity2TupleTypeSymbIndex	:== 1
//Arity32TupleTypeSymbIndex	:== 31
cLazyArraySymbIndex			:== 32
cStrictArraySymbIndex		:== 33
cUnboxedArraySymbIndex		:== 34

cLastPredefinedConstructor	:== 32
cLastPredefinedType			:== 34

cTCClassSymbIndex			:== 0

cTCMemberSymbIndex			:== 0

cTCInstanceSymbIndex		:== 0

buildPredefinedModule :: !*PredefinedSymbols -> (!ScannedModule, !.PredefinedSymbols)
buildPredefinedModule pre_def_symbols 
	# (type_var_id, pre_def_symbols)	= pre_def_symbols![PD_TypeVar_a0]
	  (cons_id, pre_def_symbols)		= pre_def_symbols![PD_ConsSymbol]
	  (nil_id, pre_def_symbols)			= pre_def_symbols![PD_NilSymbol]
	  (string_id, pre_def_symbols)		= pre_def_symbols![PD_StringType]
	  (list_id, pre_def_symbols)		= pre_def_symbols![PD_ListType]
	  (unb_array_id, pre_def_symbols)	= pre_def_symbols![PD_UnboxedArrayType]
	  (pre_mod_symb, pre_def_symbols)	= pre_def_symbols![PD_PredefinedModule]
	  (alias_dummy_symb, pre_def_symbols)	= pre_def_symbols![PD_DummyForStrictAliasFun] // MW++
	  (cons_symb, pre_def_symbols)		= new_defined_symbol PD_ConsSymbol 2 cConsSymbIndex pre_def_symbols
	  (nil_symb, pre_def_symbols)		= new_defined_symbol PD_NilSymbol 0 cNilSymbIndex pre_def_symbols
	  pre_mod_id						= pre_mod_symb.pds_ident

	  type_var						= MakeTypeVar type_var_id.pds_ident
	  type_var_with_attr			= MakeAttributedType (TV type_var)
	  list_type						= MakeAttributedType (TA (MakeNewTypeSymbIdent list_id.pds_ident 1) [type_var_with_attr])
	  unb_arr_of_char_type			= MakeAttributedType (TA (MakeNewTypeSymbIdent unb_array_id.pds_ident 1) [MakeAttributedType (TB BT_Char)])

	  (string_def, pre_def_symbols)	= make_type_def PD_StringType [] (SynType unb_arr_of_char_type) pre_def_symbols
	  (list_def, pre_def_symbols)	= make_type_def PD_ListType [type_var] (AlgType [cons_symb,nil_symb]) pre_def_symbols
	
	  cons_def			= { pc_cons_name = cons_id.pds_ident, pc_cons_arity = 2, pc_arg_types = [type_var_with_attr, list_type],
	  						pc_cons_prio =  NoPrio, pc_exi_vars = [], pc_cons_pos = PreDefPos pre_mod_id}
	  nil_def			= { pc_cons_name = nil_id.pds_ident, pc_cons_arity = 0, pc_arg_types = [],
	  						pc_cons_prio =  NoPrio, pc_exi_vars = [], pc_cons_pos = PreDefPos pre_mod_id}

	  (array_def, pre_def_symbols)		= make_type_def PD_LazyArrayType [type_var] (AbstractType cAllBitsClear) pre_def_symbols
	  (strict_def, pre_def_symbols)		= make_type_def PD_StrictArrayType [type_var] (AbstractType cIsHyperStrict) pre_def_symbols
	  (unboxed_def, pre_def_symbols)	= make_type_def PD_UnboxedArrayType [type_var] (AbstractType cIsHyperStrict) pre_def_symbols

	  (type_defs, cons_defs, pre_def_symbols)	= add_tuple_defs pre_mod_id MaxTupleArity [array_def,strict_def,unboxed_def] [] pre_def_symbols
	  alias_dummy_type = make_identity_fun_type alias_dummy_symb.pds_ident type_var // MW++
	  (class_def, member_def, pre_def_symbols) = make_TC_class_def pre_def_symbols
	= ({ mod_name = pre_mod_id, mod_type = MK_System, mod_imports = [],  mod_imported_objects = [],
		 mod_defs = {
			def_types = [string_def, list_def : type_defs], def_constructors
						= [ParsedConstructorToConsDef cons_def, ParsedConstructorToConsDef nil_def : cons_defs], def_selectors = [], def_classes = [class_def],
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

	new_defined_symbol symbol_index arity ds_index pre_def_symbols
		# (ds_ident, pre_def_symbols) = pre_def_symbols![symbol_index]
		= ({ ds_ident = ds_ident.pds_ident, ds_arity = arity/*AA: was 2*/, ds_index = ds_index }, pre_def_symbols)
	
	make_type_def type_cons_index type_vars type_rhs pre_def_symbols
		# (type_ident, pre_def_symbols) = pre_def_symbols![type_cons_index]
		= (MakeTypeDef type_ident.pds_ident (map (\tv -> MakeAttributedTypeVar tv) type_vars) type_rhs TA_None [] NoPos, pre_def_symbols)
	
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
