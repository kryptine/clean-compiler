implementation module checktypes

import StdEnv
import syntax, checksupport, check, typesupport, utilities,
		compilerSwitches //, RWSDebug


::	TypeSymbols =
	{	ts_type_defs		:: !.{# CheckedTypeDef}
	,	ts_cons_defs 		:: !.{# ConsDef}
	,	ts_selector_defs	:: !.{# SelectorDef}
	,	ts_modules			:: !.{# DclModule}
	}

::	TypeInfo =
	{	ti_var_heap			:: !.VarHeap
	,	ti_type_heaps		:: !.TypeHeaps
	,	ti_used_types		:: ![SymbolPtr]
	}

::	CurrentTypeInfo =
	{	cti_module_index	:: !Index
	,	cti_type_index		:: !Index
	,	cti_lhs_attribute	:: !TypeAttribute
	}

class bindTypes type :: !CurrentTypeInfo !type !(!*TypeSymbols, !*TypeInfo, !*CheckState)
	-> (!type, !TypeAttribute, !(!*TypeSymbols, !*TypeInfo, !*CheckState))

instance bindTypes AType
where
	bindTypes cti atype=:{at_attribute,at_type} ts_ti_cs
		# (at_type, type_attr, (ts, ti, cs)) = bindTypes cti at_type ts_ti_cs
		  cs_error = check_attr_of_type_var at_attribute at_type cs.cs_error
		  (combined_attribute, cs_error) = check_type_attribute at_attribute type_attr cti.cti_lhs_attribute cs_error
		= ({ atype & at_attribute = combined_attribute, at_type = at_type }, combined_attribute, (ts, ti, { cs & cs_error = cs_error }))
	where
		check_type_attribute :: !TypeAttribute !TypeAttribute !TypeAttribute !*ErrorAdmin -> (!TypeAttribute,!*ErrorAdmin)
		check_type_attribute TA_Anonymous type_attr root_attr error
			| try_to_combine_attributes type_attr root_attr
				= (root_attr, error)
				= (TA_Multi, checkError "conflicting attribution of type definition" "" error)
		check_type_attribute TA_Unique type_attr root_attr error
			| try_to_combine_attributes TA_Unique type_attr || try_to_combine_attributes TA_Unique root_attr
				= (TA_Unique, error)
				= (TA_Multi, checkError "conflicting attribution of type definition" "" error)
		check_type_attribute (TA_Var var) _ _ error
			= (TA_Multi, checkError var "attribute variable not allowed" error)
		check_type_attribute (TA_RootVar var) _ _ error
			= (TA_Multi, checkError var "attribute variable not allowed" error)
		check_type_attribute _ type_attr root_attr error
			= (type_attr, error)

		try_to_combine_attributes :: !TypeAttribute !TypeAttribute -> Bool
		try_to_combine_attributes TA_Multi _
			= True
		try_to_combine_attributes (TA_Var attr_var1) (TA_Var attr_var2)
			= attr_var1.av_name == attr_var2.av_name
		try_to_combine_attributes TA_Unique TA_Unique
			= True
		try_to_combine_attributes TA_Unique TA_Multi
			= True
		try_to_combine_attributes _ _
			= False

		check_attr_of_type_var :: !TypeAttribute !Type !*ErrorAdmin -> .ErrorAdmin
		check_attr_of_type_var TA_Unique (TV var) error
			// the case "TA_Var" is catched by check_type_attribute
			= checkError var "uniqueness attribute not allowed" error
		check_attr_of_type_var attr _ error
			= error

instance bindTypes TypeVar
where
	bindTypes cti tv=:{tv_name=var_id=:{id_info}} (ts, ti, cs=:{cs_symbol_table})
		# (var_def, cs_symbol_table) = readPtr id_info cs_symbol_table
		  cs = { cs & cs_symbol_table = cs_symbol_table }
		= case var_def.ste_kind of
			STE_BoundTypeVariable bv=:{stv_attribute, stv_info_ptr, stv_count}
				# cs = { cs & cs_symbol_table = cs.cs_symbol_table <:= (id_info, { var_def & ste_kind = STE_BoundTypeVariable { bv & stv_count = inc stv_count }})}
				-> ({ tv & tv_info_ptr = stv_info_ptr}, stv_attribute, (ts, ti, cs))
			_
				-> (tv, TA_Multi, (ts, ti, { cs & cs_error = checkError var_id "undefined" cs.cs_error }))

instance bindTypes [a] | bindTypes a
where
	bindTypes cti [] ts_ti_cs
		= ([], TA_Multi, ts_ti_cs)
	bindTypes cti [x : xs] ts_ti_cs
		# (x, _, ts_ti_cs) = bindTypes cti x ts_ti_cs
		  (xs, attr, ts_ti_cs) = bindTypes cti xs ts_ti_cs
		= ([x : xs], attr, ts_ti_cs)


retrieveTypeDefinition :: SymbolPtr !Index !*SymbolTable ![SymbolPtr] -> ((!Index, !Index), !*SymbolTable, ![SymbolPtr])
retrieveTypeDefinition type_ptr mod_index symbol_table used_types
	# (entry, symbol_table)	= readPtr type_ptr symbol_table
	= case entry of
		({ste_kind = this_kind =: STE_Imported STE_Type decl_index, ste_def_level, ste_index})
			-> ((ste_index, decl_index), symbol_table <:= (type_ptr, { entry & ste_kind = STE_UsedType decl_index this_kind }), [type_ptr : used_types])
		({ste_kind = this_kind =: STE_Type, ste_def_level, ste_index})
			| ste_def_level == cGlobalScope
				-> ((ste_index, mod_index), symbol_table <:= (type_ptr, { entry & ste_kind = STE_UsedType mod_index this_kind }), [type_ptr : used_types])
				-> ((NotFound, mod_index), symbol_table, used_types)
		({ste_kind = STE_UsedType mod_index _, ste_def_level, ste_index})
			-> ((ste_index, mod_index), symbol_table, used_types)
		_
			-> ((NotFound, mod_index), symbol_table, used_types)

instance bindTypes Type
where
	bindTypes cti (TV tv) ts_ti_cs
		# (tv, attr, ts_ti_cs) = bindTypes cti tv ts_ti_cs
		= (TV tv, attr, ts_ti_cs)
	bindTypes cti=:{cti_module_index,cti_type_index,cti_lhs_attribute} type=:(TA type_cons=:{type_name=type_name=:{id_info}} types)
					(ts=:{ts_type_defs,ts_modules}, ti, cs=:{cs_symbol_table})
		# ((type_index, type_module), cs_symbol_table, ti_used_types) = retrieveTypeDefinition id_info cti_module_index cs_symbol_table ti.ti_used_types
		  ti = { ti & ti_used_types = ti_used_types }
		# cs = { cs & cs_symbol_table = cs_symbol_table }
		| type_index <> NotFound
			# ({td_arity,td_attribute,td_rhs},type_index,ts_type_defs,ts_modules) = getTypeDef type_index type_module cti_module_index ts_type_defs ts_modules
			  ts = { ts & ts_type_defs = ts_type_defs, ts_modules = ts_modules }
			| checkArityOfType type_cons.type_arity td_arity td_rhs
				# (types, _, ts_ti_cs) = bindTypes cti types (ts, ti, cs)
				| type_module == cti_module_index && cti_type_index == type_index
					= (TA { type_cons & type_index = { glob_object = type_index, glob_module = type_module}} types, cti_lhs_attribute, ts_ti_cs)
					= (TA { type_cons & type_index = { glob_object = type_index, glob_module = type_module}} types,
								determine_type_attribute td_attribute, ts_ti_cs)
				= (TE, TA_Multi, (ts, ti, { cs & cs_error = checkError type_cons.type_name "used with wrong arity" cs.cs_error }))
			= (TE, TA_Multi, (ts, ti, { cs & cs_error = checkError type_cons.type_name "undefined" cs.cs_error}))
	where
		determine_type_attribute TA_Unique		= TA_Unique
		determine_type_attribute _				= TA_Multi

	bindTypes cti (arg_type --> res_type) ts_ti_cs
		# (arg_type, _, ts_ti_cs) = bindTypes cti arg_type ts_ti_cs
		  (res_type, _, ts_ti_cs) = bindTypes cti res_type ts_ti_cs
		= (arg_type --> res_type, TA_Multi, ts_ti_cs)
//AA..
	bindTypes cti (TArrow1 type) ts_ti_cs
		# (type, _, ts_ti_cs) = bindTypes cti type ts_ti_cs
		= (TArrow1 type, TA_Multi, ts_ti_cs)
//..AA
	bindTypes cti (CV tv :@: types) ts_ti_cs
		# (tv, type_attr, ts_ti_cs) = bindTypes cti tv ts_ti_cs
		  (types, _, ts_ti_cs) = bindTypes cti types ts_ti_cs
		= (CV tv :@: types, type_attr, ts_ti_cs)
// Sjaak 16-08-01
	bindTypes cti (TFA vars type) (ts, ti=:{ti_type_heaps}, cs)
		# (type_vars, (_, ti_type_heaps, cs)) = addTypeVariablesToSymbolTable cRankTwoScope vars [] ti_type_heaps cs
		  (type, _, (ts, ti, cs)) = bindTypes cti type (ts, {ti & ti_type_heaps = ti_type_heaps}, cs)
		  cs_symbol_table = removeAttributedTypeVarsFromSymbolTable cRankTwoScope type_vars cs.cs_symbol_table
		= (TFA type_vars type, TA_Multi, (ts, ti, { cs & cs_symbol_table = cs_symbol_table }))
// ... Sjaak
	bindTypes cti type ts_ti_cs
		= (type, TA_Multi, ts_ti_cs)


addToAttributeEnviron :: !TypeAttribute !TypeAttribute ![AttrInequality] !*ErrorAdmin -> (![AttrInequality],!*ErrorAdmin)
addToAttributeEnviron TA_Multi _ attr_env error
	= (attr_env, error)
addToAttributeEnviron _ TA_Unique attr_env error
	= (attr_env, error)
addToAttributeEnviron (TA_Var attr_var) (TA_Var root_var) attr_env error
	| attr_var.av_info_ptr == root_var.av_info_ptr
		= (attr_env, error)
		= ([ { ai_demanded = attr_var, ai_offered = root_var } :  attr_env], error)
addToAttributeEnviron (TA_RootVar attr_var) root_attr attr_env error
	= (attr_env, error)
addToAttributeEnviron _ _ attr_env error
	= (attr_env, checkError "inconsistent attribution of type definition" "" error)



checkTypeDef :: !Index !Index !*TypeSymbols !*TypeInfo !*CheckState -> (!*TypeSymbols, !*TypeInfo, !*CheckState)
checkTypeDef type_index module_index ts=:{ts_type_defs} ti=:{ti_type_heaps} cs=:{cs_error}
	# (type_def, ts_type_defs) = ts_type_defs![type_index]
	# {td_name,td_pos,td_args,td_attribute,td_index} = type_def
	| td_index == NoIndex
		# position = newPosition td_name td_pos
		  cs_error = pushErrorAdmin position cs_error
		  (td_attribute, attr_vars, th_attrs) = determine_root_attribute td_attribute td_name.id_name ti_type_heaps.th_attrs
		  (type_vars, (attr_vars, ti_type_heaps, cs))
		  		= addTypeVariablesToSymbolTable cGlobalScope td_args attr_vars { ti_type_heaps & th_attrs = th_attrs } { cs & cs_error = cs_error }
		  type_def = {	type_def & td_args = type_vars, td_index = type_index, td_attrs = attr_vars, td_attribute = td_attribute }
		  (td_rhs, (ts, ti, cs)) = check_rhs_of_TypeDef type_def attr_vars
				{ cti_module_index = module_index, cti_type_index = type_index, cti_lhs_attribute = td_attribute }
					({ ts & ts_type_defs = ts_type_defs },{ ti & ti_type_heaps = ti_type_heaps}, cs)
		  (td_used_types, cs_symbol_table) = retrieve_used_types ti.ti_used_types cs.cs_symbol_table
		= ({ ts & ts_type_defs = { ts.ts_type_defs & [type_index] = { type_def & td_rhs = td_rhs, td_used_types = td_used_types }}}, { ti & ti_used_types = [] },
					{ cs &	cs_error = popErrorAdmin cs.cs_error,
							cs_symbol_table = removeAttributedTypeVarsFromSymbolTable cGlobalScope type_vars cs_symbol_table})
		= ({ ts & ts_type_defs = ts_type_defs }, ti, cs)
where
	determine_root_attribute TA_None name attr_var_heap
		# (attr_info_ptr, attr_var_heap) = newPtr AVI_Empty attr_var_heap
		  new_var = { av_name = emptyIdent name, av_info_ptr = attr_info_ptr}
		= (TA_Var new_var, [new_var], attr_var_heap)
	determine_root_attribute TA_Unique name attr_var_heap
		= (TA_Unique, [], attr_var_heap)

	//
	check_rhs_of_TypeDef :: !CheckedTypeDef ![AttributeVar] !CurrentTypeInfo !(!*TypeSymbols, !*TypeInfo, !*CheckState)
		-> (!TypeRhs, !(!*TypeSymbols, !*TypeInfo, !*CheckState))
	//
	check_rhs_of_TypeDef {td_name,td_arity,td_args,td_rhs = td_rhs=:AlgType conses} attr_vars cti=:{cti_module_index,cti_type_index,cti_lhs_attribute} ts_ti_cs
		# type_lhs = { at_annotation = AN_None, at_attribute = cti_lhs_attribute,
				  	   at_type = TA (MakeTypeSymbIdent { glob_object = cti_type_index, glob_module = cti_module_index } td_name td_arity)
									[{at_annotation = AN_None, at_attribute = atv_attribute,at_type = TV atv_variable} \\ {atv_variable, atv_attribute} <- td_args]}
		  ts_ti_cs = bind_types_of_constructors cti 0 [ atv_variable \\ {atv_variable} <- td_args] attr_vars type_lhs conses ts_ti_cs
		= (td_rhs, ts_ti_cs)
	check_rhs_of_TypeDef {td_name,td_arity,td_args,td_rhs = td_rhs=:RecordType {rt_constructor=rec_cons=:{ds_index}, rt_fields}}
			attr_vars cti=:{cti_module_index,cti_type_index,cti_lhs_attribute} ts_ti_cs
		# type_lhs = {	at_annotation = AN_None, at_attribute = cti_lhs_attribute,
						at_type = TA (MakeTypeSymbIdent { glob_object = cti_type_index, glob_module = cti_module_index } td_name td_arity)
				[{at_annotation = AN_None, at_attribute = atv_attribute,at_type = TV atv_variable} \\ {atv_variable, atv_attribute} <- td_args]}
		  (ts, ti, cs) = bind_types_of_constructors cti 0  [ atv_variable \\ {atv_variable} <- td_args]
		  						attr_vars type_lhs [rec_cons] ts_ti_cs
		# (rec_cons_def, ts) = ts!ts_cons_defs.[ds_index]
		# {cons_type = { st_vars,st_args,st_result,st_attr_vars }, cons_exi_vars} = rec_cons_def
		# (ts_selector_defs, ti_var_heap, cs_error) = check_selectors 0 rt_fields cti_type_index st_args st_result st_vars st_attr_vars cons_exi_vars
					ts.ts_selector_defs ti.ti_var_heap cs.cs_error
		= (td_rhs, ({ ts & ts_selector_defs = ts_selector_defs }, { ti & ti_var_heap = ti_var_heap }, { cs & cs_error = cs_error}))
	where
		check_selectors :: !Index !{# FieldSymbol} !Index ![AType] !AType ![TypeVar] ![AttributeVar] ![ATypeVar] !*{#SelectorDef} !*VarHeap !*ErrorAdmin
			-> (!*{#SelectorDef}, !*VarHeap, !*ErrorAdmin)
		check_selectors field_nr fields rec_type_index sel_types rec_type st_vars st_attr_vars exi_vars selector_defs var_heap error
			| field_nr < size fields
				# {fs_index} = fields.[field_nr]
				# (sel_def, selector_defs) = selector_defs![fs_index]
				  [sel_type : sel_types] = sel_types
				# (sel_type, (st_vars, st_attr_vars)) = lift_quantifier sel_type (st_vars, st_attr_vars)
				# (st_attr_env, error) = addToAttributeEnviron sel_type.at_attribute rec_type.at_attribute [] error
				# (new_type_ptr, var_heap) = newPtr VI_Empty var_heap
				  sd_type = { sel_def.sd_type &  st_arity = 1, st_args = [rec_type], st_result = sel_type, st_vars = st_vars,
				  				st_attr_vars = st_attr_vars, st_attr_env = st_attr_env }
				  selector_defs = { selector_defs & [fs_index] = { sel_def & sd_type = sd_type, sd_field_nr = field_nr, sd_type_index = rec_type_index,
				  									sd_type_ptr = new_type_ptr, sd_exi_vars = exi_vars  } }
				= check_selectors (inc field_nr) fields rec_type_index sel_types  rec_type st_vars st_attr_vars exi_vars selector_defs var_heap error
				= (selector_defs, var_heap, error)
		where
			lift_quantifier at=:{at_type = TFA vars type} (type_vars, attr_vars)
				= ({ at & at_type = type}, foldSt add_var_and_attr vars (type_vars, attr_vars))
			lift_quantifier at (type_vars, attr_vars)
				= (at, (type_vars, attr_vars))

			add_var_and_attr {atv_variable, atv_attribute} (type_vars, attr_vars)
				= ([atv_variable : type_vars], add_attr_var atv_attribute attr_vars)

			add_attr_var (TA_Var av) attr_vars
				= [av : attr_vars]
			add_attr_var attr attr_vars
				= attr_vars

	check_rhs_of_TypeDef {td_rhs = SynType type} _ cti ts_ti_cs
		# (type, type_attr, ts_ti_cs) = bindTypes cti type ts_ti_cs
		= (SynType type, ts_ti_cs)
	check_rhs_of_TypeDef {td_rhs} _ _ ts_ti_cs
		= (td_rhs, ts_ti_cs)

	bind_types_of_constructors :: !CurrentTypeInfo !Index ![TypeVar] ![AttributeVar] !AType ![DefinedSymbol] !(!*TypeSymbols,!*TypeInfo,!*CheckState)
		-> (!*TypeSymbols, !*TypeInfo, !*CheckState)
	bind_types_of_constructors _ _ _ _ _ [] ts_ti_cs
		= ts_ti_cs
	bind_types_of_constructors cti=:{cti_lhs_attribute} cons_index free_vars free_attrs type_lhs [{ds_index}:conses] (ts=:{ts_cons_defs}, ti=:{ti_type_heaps}, cs)
		# (cons_def, ts_cons_defs) = ts_cons_defs![ds_index]
		# (exi_vars, (ti_type_heaps, cs))
		  		= addExistentionalTypeVariablesToSymbolTable cti_lhs_attribute cons_def.cons_exi_vars ti_type_heaps cs
		  (st_args, cons_arg_vars, st_attr_env, (ts, ti, cs))
		  		= bind_types_of_cons cons_def.cons_type.st_args cti free_vars []
		  				({ ts & ts_cons_defs = ts_cons_defs }, { ti  & ti_type_heaps = ti_type_heaps }, cs)
		  cs_symbol_table = removeAttributedTypeVarsFromSymbolTable cGlobalScope /* cOuterMostLevel */ exi_vars cs.cs_symbol_table
		  (ts, ti, cs) = bind_types_of_constructors cti (inc cons_index) free_vars free_attrs type_lhs conses
								(ts, ti, { cs & cs_symbol_table = cs_symbol_table })
		  cons_type = { cons_def.cons_type & st_vars = free_vars, st_args = st_args, st_result = type_lhs, st_attr_vars = free_attrs, st_attr_env = st_attr_env }
		  (new_type_ptr, ti_var_heap) = newPtr VI_Empty ti.ti_var_heap
		= ({ ts & ts_cons_defs = { ts.ts_cons_defs & [ds_index] =
				{ cons_def & cons_type = cons_type, cons_index = cons_index, cons_type_index = cti.cti_type_index, cons_exi_vars = exi_vars,
						cons_type_ptr = new_type_ptr, cons_arg_vars = cons_arg_vars }}}, { ti & ti_var_heap = ti_var_heap }, cs)
//				---> ("bind_types_of_constructors", cons_def.cons_symb, exi_vars, cons_type)
	where
		bind_types_of_cons :: ![AType] !CurrentTypeInfo ![TypeVar] ![AttrInequality] !(!*TypeSymbols, !*TypeInfo, !*CheckState)
			-> !(![AType], ![[ATypeVar]], ![AttrInequality], !(!*TypeSymbols, !*TypeInfo, !*CheckState))
		bind_types_of_cons [] cti free_vars attr_env ts_ti_cs
			= ([], [], attr_env, ts_ti_cs)
		bind_types_of_cons [type : types] cti free_vars attr_env ts_ti_cs
			# (types, local_vars_list, attr_env, ts_ti_cs)
					= bind_types_of_cons types cti free_vars attr_env ts_ti_cs
			  (type, type_attr, (ts, ti, cs)) = bindTypes cti type ts_ti_cs
			  (local_vars, cs_symbol_table) = foldSt retrieve_local_vars free_vars ([], cs.cs_symbol_table)
			  (attr_env, cs_error) = addToAttributeEnviron type_attr cti.cti_lhs_attribute attr_env cs.cs_error
			= ([type : types], [local_vars : local_vars_list], attr_env, (ts, ti , { cs & cs_symbol_table = cs_symbol_table, cs_error = cs_error }))
		where
			retrieve_local_vars tv=:{tv_name={id_info}} (local_vars, symbol_table)
				# (ste=:{ste_kind = STE_BoundTypeVariable bv=:{stv_attribute, stv_info_ptr, stv_count }}, symbol_table) = readPtr id_info symbol_table
				| stv_count == 0
					= (local_vars, symbol_table)

					= ([{ atv_variable = { tv & tv_info_ptr = stv_info_ptr}, atv_attribute = stv_attribute, atv_annotation = AN_None } : local_vars],
							symbol_table <:= (id_info, { ste & ste_kind = STE_BoundTypeVariable { bv & stv_count = 0}}))

	retrieve_used_types symb_ptrs symbol_table
		= foldSt retrieve_used_type symb_ptrs ([], symbol_table)
	where
		retrieve_used_type symb_ptr (used_types, symbol_table)
			# (ste=:{ste_kind=STE_UsedType decl_index orig_kind,ste_index}, symbol_table) = readPtr symb_ptr symbol_table
			= ([{gi_module = decl_index, gi_index = ste_index} : used_types], symbol_table <:= (symb_ptr, { ste & ste_kind = orig_kind }))

CS_Checked	:== 1
CS_Checking	:== 0

checkTypeDefs :: !Index !(Optional (CopiedDefinitions, Int)) !*{# CheckedTypeDef} !*{# ConsDef} !*{# SelectorDef} !*{# DclModule} !*VarHeap !*TypeHeaps !*CheckState
	-> (!*{# CheckedTypeDef}, !*{# ConsDef}, !*{# SelectorDef}, !*{# DclModule}, !*VarHeap, !*TypeHeaps, !*CheckState)
checkTypeDefs module_index opt_icl_info type_defs cons_defs selector_defs modules var_heap type_heaps cs
	#! nr_of_types = size type_defs
	#  ts = { ts_type_defs = type_defs, ts_cons_defs = cons_defs, ts_selector_defs = selector_defs, ts_modules = modules }
	   ti = { ti_type_heaps = type_heaps, ti_var_heap = var_heap, ti_used_types = [] }
	   ({ts_type_defs,ts_cons_defs, ts_selector_defs, ts_modules}, {ti_var_heap,ti_type_heaps}, cs)
	  		= iFoldSt (check_type_def module_index opt_icl_info) 0 nr_of_types (ts, ti, cs)
	= (ts_type_defs, ts_cons_defs, ts_selector_defs, ts_modules, ti_var_heap, ti_type_heaps, cs)
where
	check_type_def module_index opt_icl_info type_index (ts, ti, cs)
		| has_to_be_checked module_index opt_icl_info type_index
			= checkTypeDef  type_index module_index ts ti cs
			= (ts, ti, cs)

	has_to_be_checked module_index No type_index
		= True
	has_to_be_checked module_index (Yes ({copied_type_defs}, n_cached_dcl_mods)) type_index
		= not (module_index < n_cached_dcl_mods && type_index < size copied_type_defs && copied_type_defs.[type_index])


::	OpenTypeInfo =
	{	oti_heaps		:: !.TypeHeaps
	,	oti_all_vars	:: ![TypeVar]
	,	oti_all_attrs	:: ![AttributeVar]
	,	oti_global_vars	:: ![TypeVar]
	}

::	OpenTypeSymbols =
	{	ots_type_defs	:: .{# CheckedTypeDef}
	,	ots_modules		:: .{# DclModule}
	}

determineAttributeVariable attr_var=:{av_name=attr_name=:{id_info}} oti=:{oti_heaps,oti_all_attrs} symbol_table
	# (entry=:{ste_kind,ste_def_level}, symbol_table) = readPtr id_info symbol_table
	| ste_kind == STE_Empty || ste_def_level == cModuleScope
		#! (new_attr_ptr, th_attrs) = newPtr AVI_Empty oti_heaps.th_attrs
		# symbol_table = symbol_table <:= (id_info,{	ste_index = NoIndex, ste_kind = STE_TypeAttribute new_attr_ptr,
														ste_def_level = cGlobalScope, ste_previous = entry })
		  new_attr = { attr_var & av_info_ptr = new_attr_ptr}
		= (new_attr, { oti & oti_heaps = { oti_heaps & th_attrs = th_attrs }, oti_all_attrs = [new_attr : oti_all_attrs] }, symbol_table)
		# (STE_TypeAttribute attr_ptr) = ste_kind
		= ({ attr_var & av_info_ptr = attr_ptr}, oti, symbol_table)

::	DemandedAttributeKind = DAK_Ignore | DAK_Unique | DAK_None

newAttribute :: !DemandedAttributeKind {#Char} TypeAttribute !*OpenTypeInfo !*CheckState -> (!TypeAttribute, !*OpenTypeInfo, !*CheckState)
newAttribute DAK_Ignore var_name _ oti cs
	= (TA_Multi, oti, cs)
newAttribute DAK_Unique var_name new_attr  oti cs
	= case new_attr of
		TA_Unique
			-> (TA_Unique, oti, cs)
		TA_Multi
			-> (TA_Unique, oti, cs)
		TA_None
			-> (TA_Unique, oti, cs)
		_
			-> (TA_Unique, oti, { cs & cs_error = checkError var_name "inconsistently attributed (2)" cs.cs_error })
newAttribute DAK_None var_name (TA_Var attr_var) oti cs=:{cs_symbol_table}
	# (attr_var, oti, cs_symbol_table) = determineAttributeVariable attr_var oti cs_symbol_table
	= (TA_Var attr_var, oti, { cs & cs_symbol_table = cs_symbol_table })
newAttribute DAK_None var_name TA_Anonymous oti=:{oti_heaps, oti_all_attrs} cs
	# (new_attr_ptr, th_attrs) = newPtr AVI_Empty oti_heaps.th_attrs
	  new_attr = { av_info_ptr = new_attr_ptr, av_name = emptyIdent var_name }
	= (TA_Var new_attr, { oti & oti_heaps = { oti_heaps & th_attrs = th_attrs }, oti_all_attrs = [new_attr : oti_all_attrs] }, cs)
newAttribute DAK_None var_name TA_Unique oti cs
	= (TA_Unique, oti, cs)
newAttribute DAK_None var_name attr oti cs
	= (TA_Multi, oti, cs)


getTypeDef :: !Index !Index !Index !u:{# CheckedTypeDef} !v:{# DclModule} -> (!CheckedTypeDef, !Index , !u:{# CheckedTypeDef}, !v:{# DclModule})
getTypeDef type_index type_module module_index type_defs modules
	| type_module == module_index
		# (type_def, type_defs) = type_defs![type_index]
		= (type_def, type_index, type_defs, modules)
		# ({dcl_common={com_type_defs},dcl_conversions}, modules) = modules![type_module]
		  type_def = com_type_defs.[type_index]
		  type_index = convertIndex type_index (toInt STE_Type) dcl_conversions
		= (type_def, type_index, type_defs, modules)

checkArityOfType act_arity form_arity (SynType _)
	= form_arity == act_arity
checkArityOfType act_arity form_arity _
	= form_arity >= act_arity

getClassDef :: !Index !Index !Index !u:{# ClassDef} !v:{# DclModule} -> (!ClassDef, !Index , !u:{# ClassDef}, !v:{# DclModule})
getClassDef class_index type_module module_index class_defs modules
	| type_module == module_index
		#! si = size class_defs
		# (class_def, class_defs) = class_defs![class_index]
		= (class_def, class_index, class_defs, modules)
		# ({dcl_common={com_class_defs},dcl_conversions}, modules) = modules![type_module]
		  class_def = com_class_defs.[class_index]
		  class_index = convertIndex class_index (toInt STE_Class) dcl_conversions
		= (class_def, class_index, class_defs, modules)

getGenericDef :: !Index !Index !Index !u:{# GenericDef} !v:{# DclModule} -> (!GenericDef, !Index , !u:{# GenericDef}, !v:{# DclModule})
getGenericDef generic_index type_module module_index generic_defs modules
	| type_module == module_index
		#! si = size generic_defs
		# (generic_def, generic_defs) = generic_defs![generic_index]
		= (generic_def, generic_index, generic_defs, modules)
		# ({dcl_common={com_generic_defs},dcl_conversions}, modules) = modules![type_module]
		  generic_def = com_generic_defs.[generic_index]
		  generic_index = convertIndex generic_index (toInt STE_Generic) dcl_conversions
		= (generic_def, generic_index, generic_defs, modules)

checkTypeVar :: !Level !DemandedAttributeKind !TypeVar !TypeAttribute !(!*OpenTypeInfo, !*CheckState)
					-> (! TypeVar, !TypeAttribute, !(!*OpenTypeInfo, !*CheckState))
checkTypeVar scope dem_attr tv=:{tv_name=var_name=:{id_name,id_info}} tv_attr (oti, cs=:{cs_symbol_table})
	# (entry=:{ste_kind,ste_def_level},cs_symbol_table) = readPtr id_info cs_symbol_table
	| ste_kind == STE_Empty || ste_def_level == cModuleScope
		# (new_attr, oti=:{oti_heaps,oti_all_vars}, cs) = newAttribute dem_attr id_name tv_attr oti { cs & cs_symbol_table = cs_symbol_table }
		  (new_var_ptr, th_vars) = newPtr (TVI_Attribute new_attr) oti_heaps.th_vars
		  new_var = { tv & tv_info_ptr = new_var_ptr }
		= (new_var, new_attr, ({ oti & oti_heaps = { oti_heaps & th_vars = th_vars }, oti_all_vars = [new_var : oti_all_vars]},
				{ cs & cs_symbol_table = cs.cs_symbol_table <:= (id_info, {ste_index = NoIndex, ste_kind = STE_TypeVariable new_var_ptr,
								ste_def_level = scope, ste_previous = entry })}))
		# (STE_TypeVariable tv_info_ptr) = ste_kind
		  {oti_heaps} = oti
		  (var_info, th_vars) = readPtr tv_info_ptr oti_heaps.th_vars
		  (var_attr, oti, cs) = check_attribute id_name dem_attr var_info tv_attr { oti & oti_heaps = { oti_heaps & th_vars = th_vars }}
		  								{ cs & cs_symbol_table = cs_symbol_table }
		= ({ tv & tv_info_ptr = tv_info_ptr }, var_attr, (oti, cs))
where
	check_attribute var_name DAK_Ignore (TVI_Attribute prev_attr) this_attr oti cs=:{cs_error}
		= (TA_Multi, oti, cs)
	check_attribute var_name dem_attr (TVI_Attribute prev_attr) this_attr oti cs=:{cs_error}
		# (new_attr, cs_error) = determine_attribute var_name dem_attr this_attr cs_error
		= check_var_attribute prev_attr new_attr oti { cs & cs_error = cs_error }
	where
		check_var_attribute (TA_Var old_var) (TA_Var new_var) oti cs=:{cs_symbol_table,cs_error}
			# (new_var, oti, cs_symbol_table) = determineAttributeVariable new_var oti cs_symbol_table
			| old_var.av_info_ptr == new_var.av_info_ptr
				= (TA_Var old_var, oti, { cs &  cs_symbol_table = cs_symbol_table })
				= (TA_Var old_var, oti, { cs &  cs_symbol_table = cs_symbol_table,
						cs_error = checkError new_var.av_name "inconsistently attributed (3)" cs_error })
		check_var_attribute var_attr=:(TA_Var old_var) TA_Anonymous oti cs
			= (var_attr, oti, cs)
		check_var_attribute TA_Unique new_attr oti cs
			= case new_attr of
				TA_Unique
					-> (TA_Unique, oti, cs)
				_
					-> (TA_Unique, oti, { cs & cs_error = checkError var_name "inconsistently attributed (4)" cs.cs_error })
		check_var_attribute TA_Multi new_attr oti cs
			= case new_attr of
				TA_Multi
					-> (TA_Multi, oti, cs)
				TA_None
					-> (TA_Multi, oti, cs)
				_
					-> (TA_Multi, oti, { cs & cs_error = checkError var_name "inconsistently attributed (5)" cs.cs_error })
		check_var_attribute var_attr new_attr oti cs
			= (var_attr, oti, { cs & cs_error = checkError var_name "inconsistently attributed (6)" cs.cs_error })// ---> (var_attr, new_attr)


		determine_attribute var_name DAK_Unique new_attr error
			= case new_attr of
				 TA_Multi
				 	-> (TA_Unique, error)
				 TA_None
				 	-> (TA_Unique, error)
				 TA_Unique
				 	-> (TA_Unique, error)
				 _
				 	-> (TA_Unique, checkError var_name "inconsistently attributed (1)" error)
		determine_attribute var_name dem_attr TA_None error
			= (TA_Multi, error)
		determine_attribute var_name dem_attr new_attr error
			= (new_attr, error)

	check_attribute var_name dem_attr _ this_attr oti cs
		= (TA_Multi, oti, cs)

checkOpenAType :: !Index !Int !DemandedAttributeKind !AType !(!u:OpenTypeSymbols, !*OpenTypeInfo, !*CheckState)
	-> (!AType, !(!u:OpenTypeSymbols, !*OpenTypeInfo, !*CheckState))
checkOpenAType mod_index scope dem_attr type=:{at_type = TV tv, at_attribute} (ots, oti, cs)
	# (tv, at_attribute, (oti, cs)) = checkTypeVar scope dem_attr tv at_attribute (oti, cs)
	= ({ type & at_type = TV tv, at_attribute = at_attribute }, (ots, oti, cs))
checkOpenAType mod_index scope dem_attr type=:{at_type = GTV var_id=:{tv_name={id_info}}} (ots, oti=:{oti_heaps,oti_global_vars}, cs=:{cs_symbol_table})
	# (entry, cs_symbol_table) = readPtr id_info cs_symbol_table
	  (type_var, oti_global_vars, th_vars, entry) = retrieve_global_variable var_id entry oti_global_vars oti_heaps.th_vars
	= ({type & at_type = TV type_var, at_attribute = TA_Multi }, (ots, { oti & oti_heaps = { oti_heaps & th_vars = th_vars }, oti_global_vars = oti_global_vars },
								{ cs & cs_symbol_table = cs_symbol_table <:= (id_info, entry) }))
where
	retrieve_global_variable var entry=:{ste_kind = STE_Empty} global_vars var_heap
		# (new_var_ptr, var_heap) = newPtr TVI_Used var_heap
		  var = { var & tv_info_ptr = new_var_ptr }
		= (var, [var : global_vars], var_heap,
				{ entry  & ste_kind = STE_TypeVariable new_var_ptr, ste_def_level = cModuleScope, ste_previous = entry })
	retrieve_global_variable var entry=:{ste_kind,ste_def_level, ste_previous} global_vars var_heap
		| ste_def_level == cModuleScope
			= case ste_kind of
				STE_TypeVariable glob_info_ptr
					# var = { var & tv_info_ptr = glob_info_ptr }
					  (var_info, var_heap) = readPtr glob_info_ptr var_heap
					-> case var_info of
						TVI_Empty
							-> (var, [var : global_vars], var_heap <:= (glob_info_ptr, TVI_Used), entry)
						TVI_Used
							-> (var, global_vars, var_heap, entry)
			# (var, global_vars, var_heap, ste_previous) = retrieve_global_variable var ste_previous global_vars var_heap
			= (var, global_vars, var_heap, { entry & ste_previous = ste_previous })
//
checkOpenAType mod_index scope dem_attr type=:{ at_type=TA type_cons=:{type_name=type_name=:{id_name,id_info}} types, at_attribute}
		(ots=:{ots_type_defs,ots_modules}, oti, cs=:{cs_symbol_table})
	# (entry, cs_symbol_table) = readPtr id_info cs_symbol_table
	  cs = { cs & cs_symbol_table = cs_symbol_table }
	  (type_index, type_module) = retrieveGlobalDefinition entry STE_Type mod_index
	| type_index <> NotFound
		# ({td_arity,td_args,td_attribute,td_rhs},type_index,ots_type_defs,ots_modules) = getTypeDef type_index type_module mod_index ots_type_defs ots_modules
		  ots = { ots & ots_type_defs = ots_type_defs, ots_modules = ots_modules }
		| checkArityOfType type_cons.type_arity td_arity td_rhs
			# type_cons = { type_cons & type_index = { glob_object = type_index, glob_module = type_module }}
			  (types, (ots, oti, cs)) = check_args_of_type_cons mod_index scope /* dem_attr */ types td_args (ots, oti, cs)
			  (new_attr, oti, cs) = newAttribute (new_demanded_attribute dem_attr td_attribute) id_name at_attribute oti cs
			= ({ type & at_type = TA type_cons types, at_attribute = new_attr } , (ots, oti, cs))
			= (type, (ots, oti, {cs & cs_error = checkError type_name "used with wrong arity" cs.cs_error}))
		= (type, (ots, oti, {cs & cs_error = checkError type_name "undefined" cs.cs_error}))
where
	check_args_of_type_cons :: !Index !Int ![AType] ![ATypeVar] !(!u:OpenTypeSymbols, !*OpenTypeInfo, !*CheckState)
		-> (![AType], !(!u:OpenTypeSymbols, !*OpenTypeInfo, !*CheckState))
	check_args_of_type_cons mod_index scope [] _ cot_state
		= ([], cot_state)
	check_args_of_type_cons mod_index scope [arg_type : arg_types] [ {atv_attribute} : td_args ] cot_state
		# (arg_type, cot_state) = checkOpenAType mod_index scope (new_demanded_attribute DAK_None atv_attribute) arg_type cot_state
		  (arg_types, cot_state) = check_args_of_type_cons mod_index scope arg_types td_args cot_state
		= ([arg_type : arg_types], cot_state)

	new_demanded_attribute DAK_Ignore _
		= DAK_Ignore
	new_demanded_attribute _ TA_Unique
		= DAK_Unique
	new_demanded_attribute dem_attr _
		= dem_attr

checkOpenAType mod_index scope dem_attr type=:{at_type = arg_type --> result_type, at_attribute} cot_state
	# (arg_type, cot_state) = checkOpenAType mod_index scope DAK_None arg_type cot_state
	  (result_type, (ots, oti, cs)) = checkOpenAType mod_index scope DAK_None result_type cot_state
	  (new_attr, oti, cs) = newAttribute dem_attr "-->" at_attribute oti cs
	= ({ type & at_type = arg_type --> result_type, at_attribute = new_attr }, (ots, oti, cs))
//AA..
checkOpenAType mod_index scope dem_attr type=:{at_type = TArrow1 arg_type, at_attribute} cot_state
	# (arg_type, (ots, oti, cs)) = checkOpenAType mod_index scope DAK_None arg_type cot_state
	  (new_attr, oti, cs) = newAttribute dem_attr "TArrow1" at_attribute oti cs
	= ({ type & at_type = TArrow1 arg_type, at_attribute = new_attr }, (ots, oti, cs))
//..AA
/*
checkOpenAType mod_index scope dem_attr type=:{at_type = CV tv :@: types, at_attribute} (ots, oti, cs)
	# (cons_var, _, (oti, cs)) = checkTypeVar scope DAK_None tv TA_Multi (oti, cs)
	  (types, (ots, oti, cs)) = mapSt (checkOpenAType mod_index scope DAK_None) types (ots, oti, cs)
	  (new_attr, oti, cs) = newAttribute dem_attr ":@:" at_attribute oti cs
	= ({ type & at_type = CV cons_var :@: types, at_attribute = new_attr }, (ots, oti, cs))
*/
checkOpenAType mod_index scope dem_attr type=:{at_type = CV tv :@: types, at_attribute} (ots, oti, cs)
	# (cons_var, var_attr, (oti, cs)) = checkTypeVar scope dem_attr tv at_attribute (oti, cs)
	  (types, (ots, oti, cs)) = mapSt (checkOpenAType mod_index scope DAK_None) types (ots, oti, cs)
	= ({ type & at_type = CV cons_var :@: types, at_attribute = var_attr }, (ots, oti, cs))
checkOpenAType mod_index scope dem_attr atype=:{at_type = TFA vars type, at_attribute} (ots, oti, cs)
	# (vars, (oti, cs)) = mapSt add_universal_var vars  (oti, cs)
	  (checked_type, (ots, oti, cs)) = checkOpenAType mod_index cRankTwoScope dem_attr { atype & at_type = type } (ots, oti, cs)
	  cs = { cs & cs_symbol_table = foldSt remove_universal_var vars cs.cs_symbol_table }
	= ( { checked_type & at_type = TFA vars checked_type.at_type }, (ots, oti, cs))
where
	add_universal_var atv=:{atv_variable = tv=:{tv_name={id_name,id_info}}, atv_attribute} (oti, cs=:{cs_symbol_table,cs_error})
		# (entry=:{ste_kind,ste_def_level},cs_symbol_table) = readPtr id_info cs_symbol_table
		| ste_kind == STE_Empty || ste_def_level < cRankTwoScope
			# (new_attr, oti=:{oti_heaps}, cs) = newAttribute DAK_None id_name atv_attribute oti { cs & cs_symbol_table = cs_symbol_table }
			  (new_var_ptr, th_vars) = newPtr (TVI_Attribute new_attr) oti_heaps.th_vars
			= ({atv & atv_variable = { tv & tv_info_ptr = new_var_ptr}, atv_attribute = new_attr },
					({ oti & oti_heaps = { oti_heaps & th_vars = th_vars }}, { cs & cs_symbol_table =
							cs.cs_symbol_table <:= (id_info, {ste_index = NoIndex, ste_kind = STE_TypeVariable new_var_ptr,
									ste_def_level = cRankTwoScope, ste_previous = entry })}))
			= (atv, (oti, { cs & cs_error = checkError id_name "type variable already undefined" cs_error, cs_symbol_table = cs_symbol_table }))

	remove_universal_var {atv_variable = {tv_name}, atv_attribute = TA_Var {av_name}} cs_symbol_table
		= removeDefinitionFromSymbolTable cGlobalScope av_name (removeDefinitionFromSymbolTable cRankTwoScope tv_name cs_symbol_table)
	remove_universal_var {atv_variable = {tv_name}} cs_symbol_table
		= removeDefinitionFromSymbolTable cRankTwoScope tv_name cs_symbol_table

checkOpenAType mod_index scope dem_attr type=:{at_attribute} (ots, oti, cs)
	# (new_attr, oti, cs) = newAttribute dem_attr "." at_attribute oti cs
	= ({ type & at_attribute = new_attr}, (ots, oti, cs))

checkOpenTypes mod_index scope dem_attr types cot_state
	= mapSt (checkOpenType mod_index scope dem_attr) types cot_state

checkOpenType mod_index scope dem_attr type cot_state
	# ({at_type}, cot_state) = checkOpenAType mod_index scope dem_attr { at_type = type, at_attribute = TA_Multi, at_annotation = AN_None } cot_state
	= (at_type, cot_state)

checkOpenATypes mod_index scope types cot_state
	= mapSt (checkOpenAType mod_index scope DAK_None) types cot_state

checkInstanceType :: !Index !(Global DefinedSymbol) !InstanceType !Specials !u:{# CheckedTypeDef} !v:{# ClassDef} !u:{# DclModule} !*TypeHeaps !*CheckState
	-> (!InstanceType, !Specials, !u:{# CheckedTypeDef}, !v:{# ClassDef}, !u:{# DclModule}, !*TypeHeaps, !*CheckState)
checkInstanceType mod_index ins_class it=:{it_types,it_context} specials type_defs class_defs modules heaps cs
	# cs_error
			= check_fully_polymorphity it_types it_context cs.cs_error
	  ots = { ots_type_defs = type_defs, ots_modules = modules }
	  oti = { oti_heaps = heaps, oti_all_vars = [], oti_all_attrs = [], oti_global_vars= [] }
	  (it_types, (ots, oti=:{oti_all_vars = it_vars, oti_all_attrs = it_attr_vars}, cs))
	  	= checkOpenTypes mod_index cGlobalScope DAK_None it_types (ots, oti, { cs & cs_error = cs_error })
	  oti = { oti &  oti_all_vars = [], oti_all_attrs = [] }
	  (it_context, type_defs, class_defs, modules, heaps, cs) = checkTypeContexts it_context mod_index class_defs ots oti cs
	  cs_error = foldSt (compare_context_and_instance_types ins_class it_types) it_context cs.cs_error
	  (specials, cs) = checkSpecialTypeVars specials { cs & cs_error = cs_error }
	  cs_symbol_table = removeVariablesFromSymbolTable cGlobalScope it_vars cs.cs_symbol_table
	  cs_symbol_table = removeAttributesFromSymbolTable it_attr_vars cs_symbol_table
	  (specials, type_defs, modules, heaps, cs) = checkSpecialTypes mod_index specials type_defs modules heaps { cs & cs_symbol_table = cs_symbol_table }
	= ({it & it_vars = it_vars, it_types = it_types, it_attr_vars = it_attr_vars, it_context = it_context },
	    	specials, type_defs, class_defs, modules, heaps, cs)
  where
	check_fully_polymorphity it_types it_context cs_error
		| all is_type_var it_types && not (isEmpty it_context)
			= checkError "context restriction not allowed for fully polymorph instance" "" cs_error
		= cs_error
	  where
		is_type_var (TV _) = True
		is_type_var _ = False

	compare_context_and_instance_types ins_class it_types {tc_class, tc_types} cs_error
		| ins_class<>tc_class
			= cs_error
		# are_equal
				= fold2St compare_context_and_instance_type it_types tc_types True
		| are_equal
			= checkError ins_class.glob_object.ds_ident "context restriction equals instance type" cs_error
		= cs_error
	  where
		compare_context_and_instance_type (TA {type_index=ti1} _) (TA {type_index=ti2} _) are_equal_accu
			= ti1==ti2 && are_equal_accu
		compare_context_and_instance_type (_ --> _) (_ --> _) are_equal_accu
			= are_equal_accu
//AA..
		compare_context_and_instance_type TArrow TArrow are_equal_accu
			= are_equal_accu
		compare_context_and_instance_type (TArrow1 _) (TArrow1 _) are_equal_accu
			= are_equal_accu
//..AA
		compare_context_and_instance_type (CV tv1 :@: _) (CV tv2 :@: _) are_equal_accu
			= tv1==tv2 && are_equal_accu
		compare_context_and_instance_type (TB bt1) (TB bt2) are_equal_accu
			= bt1==bt2 && are_equal_accu
		compare_context_and_instance_type (TV tv1) (TV tv2) are_equal_accu
			= tv1==tv2 && are_equal_accu
		compare_context_and_instance_type _ _ are_equal_accu
			= False

checkFunctionType :: !Index !SymbolType !Specials !u:{# CheckedTypeDef} !v:{# ClassDef} !u:{# DclModule} !*TypeHeaps !*CheckState
	-> (!SymbolType, !Specials, !u:{# CheckedTypeDef}, !v:{# ClassDef}, !u:{# DclModule}, !*TypeHeaps, !*CheckState)
checkFunctionType mod_index st specials type_defs class_defs modules heaps cs
	= checkSymbolType True mod_index st specials type_defs class_defs modules heaps cs

checkMemberType :: !Index !SymbolType !u:{# CheckedTypeDef} !v:{# ClassDef} !u:{# DclModule} !*TypeHeaps !*CheckState
	-> (!SymbolType, !u:{# CheckedTypeDef}, !v:{# ClassDef}, !u:{# DclModule}, !*TypeHeaps, !*CheckState)
checkMemberType mod_index st type_defs class_defs modules heaps cs
	# (checked_st, specials, type_defs, class_defs, modules, heaps, cs)
			= checkSymbolType False mod_index st SP_None type_defs class_defs modules heaps cs
	= (checked_st, type_defs, class_defs, modules, heaps, cs)

checkSymbolType :: !Bool !Index !SymbolType !Specials !u:{# CheckedTypeDef} !v:{# ClassDef} !u:{# DclModule} !*TypeHeaps !*CheckState
	-> (!SymbolType, !Specials, !u:{# CheckedTypeDef}, !v:{# ClassDef}, !u:{# DclModule}, !*TypeHeaps, !*CheckState)
checkSymbolType is_function mod_index st=:{st_args,st_result,st_context,st_attr_env} specials type_defs class_defs modules heaps cs
	# ots = { ots_type_defs = type_defs, ots_modules = modules }
	  oti = { oti_heaps = heaps, oti_all_vars = [], oti_all_attrs = [], oti_global_vars= [] }
	  (st_args, cot_state) = checkOpenATypes mod_index cGlobalScope st_args (ots, oti, cs)
//	   ---> ("checkSymbolType", st_args))
	  (st_result, (ots, oti=:{oti_all_vars = st_vars,oti_all_attrs = st_attr_vars}, cs))
	  	= checkOpenAType mod_index cGlobalScope DAK_None st_result cot_state
	  oti = { oti &  oti_all_vars = [], oti_all_attrs = [] }
	  (st_context, type_defs, class_defs, modules, heaps, cs) = check_type_contexts is_function st_context mod_index class_defs ots oti cs
	  (st_attr_env, cs) = mapSt check_attr_inequality st_attr_env cs
	  (specials, cs) = checkSpecialTypeVars specials cs
	  cs_symbol_table = removeVariablesFromSymbolTable cGlobalScope st_vars cs.cs_symbol_table
	  cs_symbol_table = removeAttributesFromSymbolTable st_attr_vars cs_symbol_table
	  (specials, type_defs, modules, heaps, cs) = checkSpecialTypes mod_index specials type_defs modules heaps { cs & cs_symbol_table = cs_symbol_table }
	  checked_st = {st & st_vars = st_vars, st_args = st_args, st_result = st_result, st_context = st_context,
	    					st_attr_vars = st_attr_vars, st_attr_env = st_attr_env }
	= (checked_st, specials, type_defs, class_defs, modules, heaps, cs)
//			---> ("checkSymbolType", checked_st)
where
	check_attr_inequality ineq=:{ai_demanded=ai_demanded=:{av_name=dem_name},ai_offered=ai_offered=:{av_name=off_name}} cs=:{cs_symbol_table,cs_error}
		# (dem_entry, cs_symbol_table) = readPtr dem_name.id_info cs_symbol_table
		# (found_dem_attr, dem_attr_ptr) = retrieve_attribute dem_entry
		| found_dem_attr
		   	# (off_entry, cs_symbol_table) = readPtr off_name.id_info cs_symbol_table
			# (found_off_attr, off_attr_ptr) = retrieve_attribute off_entry
			| found_off_attr
				= ({ai_demanded = { ai_demanded & av_info_ptr = dem_attr_ptr }, ai_offered = { ai_offered & av_info_ptr = off_attr_ptr }},
						{ cs & cs_symbol_table = cs_symbol_table })
				= (ineq, { cs & cs_error = checkError off_name "attribute variable undefined" cs_error, cs_symbol_table = cs_symbol_table })
			= (ineq, { cs & cs_error = checkError dem_name "attribute variable undefined" cs_error, cs_symbol_table = cs_symbol_table })
	where
		retrieve_attribute {ste_kind = STE_TypeAttribute attr_ptr, ste_def_level, ste_index}
			| ste_def_level == cGlobalScope
				= (True, attr_ptr)
		retrieve_attribute entry
			= (False, abort "no attribute")

	check_type_contexts is_function st_context mod_index class_defs ots oti cs
		| is_function
		 	= checkTypeContexts st_context mod_index class_defs ots oti cs
			= check_member_contexts st_context mod_index class_defs ots oti cs

// AA.. generic members do not have a context at the moment of checking
	check_member_contexts [] mod_index class_defs ots oti cs
		= checkTypeContexts [] mod_index class_defs ots oti cs
// ..AA
	check_member_contexts [tc : tcs] mod_index class_defs ots oti cs
		# (tc, (class_defs, ots, oti, cs)) = checkTypeContext mod_index tc  (class_defs, ots, oti, cs)
		  cs_symbol_table = removeVariablesFromSymbolTable cGlobalScope [ tv \\ (TV tv) <- tc.tc_types] cs.cs_symbol_table
		  (tcs, type_defs, class_defs, modules, heaps, cs) =  checkTypeContexts tcs mod_index class_defs ots oti { cs & cs_symbol_table = cs_symbol_table }
		= ([tc : tcs], type_defs, class_defs, modules, heaps, cs)

NewEntry symbol_table symb_ptr def_kind def_index level previous :==
	 symbol_table <:= (symb_ptr,{  ste_kind = def_kind, ste_index = def_index, ste_def_level = level, ste_previous = previous })

checkSuperClasses :: ![TypeVar] ![TypeContext] !Index !u:{# CheckedTypeDef} !v:{# ClassDef} !u:{# DclModule} !*TypeHeaps !*CheckState
	-> (![TypeVar], ![TypeContext], !u:{#CheckedTypeDef}, !v:{# ClassDef}, !u:{# DclModule}, !*TypeHeaps, !*CheckState)
checkSuperClasses class_args class_contexts mod_index type_defs class_defs modules heaps=:{th_vars} cs=:{cs_symbol_table,cs_error}
	# (rev_class_args, cs_symbol_table, th_vars, cs_error)
			= foldSt add_variable_to_symbol_table class_args ([], cs_symbol_table, th_vars, cs_error)
	  cs = {cs & cs_symbol_table = cs_symbol_table, cs_error = cs_error }
	  ots = { ots_modules = modules, ots_type_defs = type_defs }
	  oti = { oti_heaps = { heaps & th_vars = th_vars }, oti_all_vars = [], oti_all_attrs = [], oti_global_vars = [] }
	  (class_contexts, type_defs, class_defs, modules, type_heaps, cs)
		  		= checkTypeContexts class_contexts mod_index class_defs ots oti cs
	  (class_args, cs_symbol_table) = retrieve_variables_from_symbol_table rev_class_args [] cs.cs_symbol_table
	= (class_args, class_contexts, type_defs, class_defs, modules, type_heaps, {cs & cs_symbol_table = cs_symbol_table})
where
	add_variable_to_symbol_table :: !TypeVar !(![TypeVar], !*SymbolTable, !*TypeVarHeap, !*ErrorAdmin)
		-> (![TypeVar],!*SymbolTable,!*TypeVarHeap,!*ErrorAdmin)
	add_variable_to_symbol_table tv=:{tv_name={id_name,id_info}} (rev_class_args, symbol_table, th_vars, error)
	  	# (entry, symbol_table) = readPtr id_info symbol_table
		| entry.ste_kind == STE_Empty || entry.ste_def_level < cGlobalScope
			# (new_var_ptr, th_vars) = newPtr TVI_Empty th_vars
			# symbol_table = NewEntry symbol_table id_info (STE_TypeVariable new_var_ptr) NoIndex cGlobalScope entry
			= ([{ tv & tv_info_ptr = new_var_ptr} : rev_class_args], symbol_table, th_vars, error)
			= (rev_class_args, symbol_table, th_vars, checkError id_name "(variable) already defined" error)

	retrieve_variables_from_symbol_table :: ![TypeVar] ![TypeVar] !*SymbolTable -> (![TypeVar],!*SymbolTable)
	retrieve_variables_from_symbol_table [var=:{tv_name={id_name,id_info}} : vars] class_args symbol_table
		# (entry, symbol_table) = readPtr id_info symbol_table
		= retrieve_variables_from_symbol_table vars [var : class_args] (symbol_table <:= (id_info,entry.ste_previous))
	retrieve_variables_from_symbol_table [] class_args symbol_table
		= (class_args, symbol_table)

checkTypeContext ::  !Index !TypeContext !(!v:{# ClassDef}, !u:OpenTypeSymbols, !*OpenTypeInfo, !*CheckState)
	-> (!TypeContext,!(!v:{# ClassDef}, !u:OpenTypeSymbols, !*OpenTypeInfo, !*CheckState))
checkTypeContext mod_index tc=:{tc_class=tc_class=:{glob_object=class_name=:{ds_ident=ds_ident=:{id_name,id_info},ds_arity}},tc_types}
	  	(class_defs, ots, oti, cs=:{cs_symbol_table, cs_predef_symbols})
	# (entry, cs_symbol_table) = readPtr id_info cs_symbol_table
	  cs = { cs & cs_symbol_table = cs_symbol_table }
	# (class_index, class_module) = retrieveGlobalDefinition entry STE_Class mod_index
	| class_index <> NotFound
		# (class_def, class_index, class_defs, ots_modules) = getClassDef class_index class_module mod_index class_defs ots.ots_modules
		  ots = { ots & ots_modules = ots_modules }
		  (tc_types, (ots, oti, cs)) = checkOpenTypes mod_index cGlobalScope DAK_Ignore tc_types (ots, oti, cs)
		  cs = check_context_types 	class_def.class_name tc_types cs
		  tc = { tc & tc_class = { tc_class & glob_object = { class_name & ds_index = class_index }, glob_module = class_module }, tc_types = tc_types}
		| class_def.class_arity == ds_arity
			= (tc, (class_defs, ots, oti, cs))
			= (tc, (class_defs, ots, oti, { cs & cs_error = checkError id_name "used with wrong arity" cs.cs_error }))
		= ({tc & tc_types = []}, (class_defs, ots, oti, { cs & cs_error = checkError id_name "undefined" cs.cs_error }))
where

	check_context_types tc_class [] cs=:{cs_error}
		= { cs & cs_error = checkError tc_class "type context should contain one or more type variables" cs_error}
	check_context_types tc_class [((CV {tv_name}) :@: _):_] cs=:{cs_error}
		= cs
//		= { cs & cs_error = checkError tv_name "not allowed as higher order type variable in context" cs_error}
	check_context_types tc_class [TV _ : types] cs
		= cs
	check_context_types tc_class [type : types] cs
		= check_context_types tc_class types cs

checkTypeContext1 ::  !Index !TypeContext !(!v:{# ClassDef}, !x:{# GenericDef}, !u:OpenTypeSymbols, !*OpenTypeInfo, !*CheckState)
	-> (!TypeContext,!(!v:{# ClassDef}, !x:{# GenericDef}, !u:OpenTypeSymbols, !*OpenTypeInfo, !*CheckState))
checkTypeContext1 mod_index tc (class_defs, generic_defs, ots, oti, cs)
	# (entry, cs) = get_entry tc cs
	= check_context mod_index entry tc (class_defs, generic_defs, ots, oti, cs)
where
	get_entry tc cs=:{cs_symbol_table}
		# (entry, cs_symbol_table) = readPtr tc.tc_class.glob_object.ds_ident.id_info cs_symbol_table
		= (entry, {cs & cs_symbol_table = cs_symbol_table})

	check_context
			mod_index
			entry
			tc=:{tc_class=tc_class=:{glob_object=class_name=:{ds_ident=ds_ident=:{id_name,id_info},ds_arity}},tc_types}
	  		(class_defs, generic_defs, ots, oti, cs)
		# (class_index, class_module) = retrieveGlobalDefinition entry STE_Class mod_index
		| class_index <> NotFound
			# (class_def, class_index, class_defs, ots_modules) = getClassDef class_index class_module mod_index class_defs ots.ots_modules
			  ots = { ots & ots_modules = ots_modules }
			  (tc_types, (ots, oti, cs)) = checkOpenTypes mod_index cGlobalScope DAK_Ignore tc_types (ots, oti, cs)
			  cs = check_context_types 	class_def.class_name tc_types cs
			  tc = { tc & tc_class = { tc_class & glob_object = { class_name & ds_index = class_index }, glob_module = class_module }, tc_types = tc_types}
			| class_def.class_arity == ds_arity
				= (tc, (class_defs, generic_defs, ots, oti, cs))
				= (tc, (class_defs, generic_defs, ots, oti, { cs & cs_error = checkError id_name "used with wrong arity" cs.cs_error }))
			= ({tc & tc_types = []}, (class_defs, generic_defs, ots, oti, { cs & cs_error = checkError id_name "class undefined" cs.cs_error }))
	check_context
			mod_index
			entry
			tc=:{tc_class=tc_class=:{glob_object=class_name=:{ds_ident=ds_ident=:{id_name,id_info},ds_arity}},tc_types}
			(class_defs, generic_defs, ots, oti, cs)
		# 	(generic_index, generic_module) = retrieveGlobalDefinition entry STE_Generic mod_index
		| generic_index <> NotFound
			# (generic_def, generic_index, generic_defs, ots_modules) = getGenericDef generic_index generic_module mod_index generic_defs ots.ots_modules
			  ots = { ots & ots_modules = ots_modules }
			  (tc_types, (ots, oti, cs)) = checkOpenTypes mod_index cGlobalScope DAK_Ignore tc_types (ots, oti, cs)
			  //cs = check_context_types 	generic_def.gen_name tc_types cs
			  tc = { tc & tc_class = { tc_class & glob_object = { class_name & ds_index = generic_index }, glob_module = generic_module }, tc_types = tc_types}
			| ds_arity == 1
				= (tc, (class_defs, generic_defs, ots, oti, cs))
				= (tc, (class_defs, generic_defs, ots, oti, { cs & cs_error = checkError id_name "used with wrong arity" cs.cs_error }))
			= ({tc & tc_types = []}, (class_defs, generic_defs, ots, oti, { cs & cs_error = checkError id_name "generic undefined" cs.cs_error }))

	check_context_types tc_class [] cs=:{cs_error}
		= { cs & cs_error = checkError tc_class "type context should contain one or more type variables" cs_error}
	check_context_types tc_class [((CV {tv_name}) :@: _):_] cs=:{cs_error}
		= cs
//		= { cs & cs_error = checkError tv_name "not allowed as higher order type variable in context" cs_error}
	check_context_types tc_class [TV _ : types] cs
		= cs
	check_context_types tc_class [type : types] cs
		= check_context_types tc_class types cs

checkTypeContexts :: ![TypeContext] !Index !v:{# ClassDef} !u:OpenTypeSymbols !*OpenTypeInfo !*CheckState
	-> (![TypeContext], !u:{# CheckedTypeDef}, !v:{# ClassDef}, u:{# DclModule}, !*TypeHeaps, !*CheckState)
checkTypeContexts tcs mod_index class_defs ots oti cs
	# (tcs, (class_defs, { ots_modules, ots_type_defs}, oti, cs)) = mapSt (checkTypeContext mod_index) tcs (class_defs, ots, oti, cs)
	  cs = check_class_variables oti.oti_all_vars cs
	  cs = check_class_attributes oti.oti_all_attrs cs
	= (tcs, ots_type_defs, class_defs, ots_modules, oti.oti_heaps, cs)
where
	check_class_variables class_variables cs
		= foldSt check_class_variable class_variables cs
	where
		check_class_variable {tv_name} cs=:{cs_symbol_table,cs_error}
			= { cs & cs_symbol_table	= removeDefinitionFromSymbolTable cGlobalScope tv_name cs_symbol_table,
					 cs_error			= checkError tv_name "wrongly used or not used at all" cs_error}

	check_class_attributes class_attributes cs
		= foldSt check_class_attribute class_attributes cs
	where
		check_class_attribute {av_name} cs=:{cs_symbol_table,cs_error}
			= { cs & cs_symbol_table	= removeDefinitionFromSymbolTable cGlobalScope av_name cs_symbol_table,
					 cs_error			= checkError av_name "undefined" cs_error}


checkDynamicTypes :: !Index ![ExprInfoPtr] !(Optional SymbolType) !u:{# CheckedTypeDef} !u:{# DclModule} !*TypeHeaps !*ExpressionHeap !*CheckState
	-> (!u:{# CheckedTypeDef}, !u:{# DclModule}, !*TypeHeaps, !*ExpressionHeap, !*CheckState)
checkDynamicTypes mod_index dyn_type_ptrs No type_defs modules type_heaps expr_heap cs
	# (type_defs, modules, heaps, expr_heap, cs) = checkDynamics mod_index (inc cModuleScope) dyn_type_ptrs type_defs modules type_heaps expr_heap cs
	  (expr_heap, cs_symbol_table) = remove_global_type_variables_in_dynamics dyn_type_ptrs (expr_heap, cs.cs_symbol_table)
	= (type_defs, modules, heaps, expr_heap, { cs & cs_symbol_table = cs_symbol_table })
where
	remove_global_type_variables_in_dynamics dyn_info_ptrs expr_heap_and_symbol_table
		= foldSt remove_global_type_variables_in_dynamic dyn_info_ptrs expr_heap_and_symbol_table
	where
		remove_global_type_variables_in_dynamic dyn_info_ptr (expr_heap, symbol_table)
			# (dyn_info, expr_heap) = readPtr dyn_info_ptr expr_heap
			= case dyn_info of
				EI_Dynamic (Yes {dt_global_vars}) _
					-> (expr_heap, remove_global_type_variables dt_global_vars symbol_table)
				EI_Dynamic No _
					-> (expr_heap, symbol_table)
				EI_DynamicTypeWithVars loc_type_vars {dt_global_vars} loc_dynamics
					-> remove_global_type_variables_in_dynamics loc_dynamics (expr_heap, remove_global_type_variables dt_global_vars symbol_table)


		remove_global_type_variables global_vars symbol_table
			= foldSt remove_global_type_variable global_vars symbol_table
		where
			remove_global_type_variable {tv_name=tv_name=:{id_info}} symbol_table
				# (entry, symbol_table) = readPtr id_info symbol_table
				| entry.ste_kind == STE_Empty
					= symbol_table
					= symbol_table <:= (id_info, entry.ste_previous)



checkDynamicTypes mod_index dyn_type_ptrs (Yes {st_vars}) type_defs modules type_heaps expr_heap cs=:{cs_symbol_table}
	# (th_vars, cs_symbol_table) = foldSt add_type_variable_to_symbol_table st_vars (type_heaps.th_vars, cs_symbol_table)
	  (type_defs, modules, heaps, expr_heap, cs) = checkDynamics mod_index (inc cModuleScope) dyn_type_ptrs type_defs modules
	  		{ type_heaps & th_vars = th_vars } expr_heap { cs & cs_symbol_table = cs_symbol_table }
	  cs_symbol_table =	removeVariablesFromSymbolTable cModuleScope st_vars cs.cs_symbol_table
	  (expr_heap, cs) = check_global_type_variables_in_dynamics dyn_type_ptrs (expr_heap, { cs & cs_symbol_table = cs_symbol_table })
	= (type_defs, modules, heaps, expr_heap, cs)
where
	add_type_variable_to_symbol_table {tv_name={id_info},tv_info_ptr} (var_heap,symbol_table)
		# (entry, symbol_table) = readPtr id_info symbol_table
		= (	var_heap <:= (tv_info_ptr, TVI_Empty),
			symbol_table <:= (id_info, {ste_index = NoIndex, ste_kind = STE_TypeVariable tv_info_ptr,
									ste_def_level = cModuleScope, ste_previous = entry }))

	check_global_type_variables_in_dynamics dyn_info_ptrs expr_heap_and_cs
		= foldSt check_global_type_variables_in_dynamic dyn_info_ptrs expr_heap_and_cs
	where
		check_global_type_variables_in_dynamic dyn_info_ptr (expr_heap, cs)
			# (dyn_info, expr_heap) = readPtr dyn_info_ptr expr_heap
			= case dyn_info of
				EI_Dynamic (Yes {dt_global_vars}) _
					-> (expr_heap, check_global_type_variables dt_global_vars cs)
				EI_Dynamic No _
					-> (expr_heap, cs)
				EI_DynamicTypeWithVars loc_type_vars {dt_global_vars} loc_dynamics
					-> check_global_type_variables_in_dynamics loc_dynamics (expr_heap, check_global_type_variables dt_global_vars cs)


		check_global_type_variables global_vars cs
			= foldSt check_global_type_variable global_vars cs
		where
			check_global_type_variable {tv_name=tv_name=:{id_info}} cs=:{cs_symbol_table, cs_error}
				# (entry, cs_symbol_table) = readPtr id_info cs_symbol_table
				| entry.ste_kind == STE_Empty
					= { cs & cs_symbol_table = cs_symbol_table }
					= { cs & cs_symbol_table = cs_symbol_table <:= (id_info, entry.ste_previous),
							 cs_error = checkError tv_name.id_name "global type variable not used in type of the function" cs_error }

checkDynamics mod_index scope dyn_type_ptrs type_defs modules type_heaps expr_heap cs
	= foldSt (check_dynamic mod_index scope) dyn_type_ptrs (type_defs, modules, type_heaps, expr_heap, cs)
where
	check_dynamic mod_index scope dyn_info_ptr (type_defs, modules, type_heaps, expr_heap, cs)
		# (dyn_info, expr_heap) = readPtr dyn_info_ptr expr_heap
		= case dyn_info of
			EI_Dynamic opt_type ei_dynamic_id
				-> case opt_type of
					Yes dyn_type
						# (dyn_type, loc_type_vars, type_defs, modules, type_heaps, cs) = check_dynamic_type mod_index scope dyn_type type_defs modules type_heaps cs
						| isEmpty loc_type_vars
							-> (type_defs, modules, type_heaps, expr_heap <:= (dyn_info_ptr, EI_Dynamic (Yes dyn_type) ei_dynamic_id), cs)
				  			# cs_symbol_table = removeVariablesFromSymbolTable scope loc_type_vars cs.cs_symbol_table
							  cs_error = checkError loc_type_vars "type variable(s) not defined" cs.cs_error
							-> (type_defs, modules, type_heaps, expr_heap <:= (dyn_info_ptr, EI_Dynamic (Yes dyn_type) ei_dynamic_id),
									{ cs & cs_error = cs_error, cs_symbol_table = cs_symbol_table })
					No
						-> (type_defs, modules, type_heaps, expr_heap, cs)
			EI_DynamicType dyn_type loc_dynamics
				# (dyn_type, loc_type_vars, type_defs, modules, type_heaps, cs) = check_dynamic_type mod_index scope dyn_type type_defs modules type_heaps cs
				  (type_defs, modules, type_heaps, expr_heap, cs) = check_local_dynamics mod_index scope loc_dynamics type_defs modules type_heaps expr_heap cs
				  cs_symbol_table = removeVariablesFromSymbolTable scope loc_type_vars cs.cs_symbol_table
				-> (type_defs, modules, type_heaps, expr_heap <:= (dyn_info_ptr, EI_DynamicTypeWithVars loc_type_vars dyn_type loc_dynamics),
							{ cs & cs_symbol_table = cs_symbol_table })
						// ---> ("check_dynamic ", scope, dyn_type, loc_type_vars)

	check_local_dynamics mod_index scope local_dynamics type_defs modules type_heaps expr_heap cs
		= foldSt (check_dynamic mod_index (inc scope)) local_dynamics (type_defs, modules, type_heaps, expr_heap, cs)

	check_dynamic_type mod_index scope dt=:{dt_uni_vars,dt_type} type_defs modules type_heaps=:{th_vars} cs
		# (dt_uni_vars, (th_vars, cs)) = mapSt (add_type_variable_to_symbol_table scope) dt_uni_vars (th_vars, cs)
		  ots = { ots_type_defs = type_defs, ots_modules = modules }
		  oti = { oti_heaps = { type_heaps & th_vars = th_vars }, oti_all_vars = [], oti_all_attrs = [], oti_global_vars = [] }
		  (dt_type, ( {ots_type_defs, ots_modules}, {oti_heaps,oti_all_vars,oti_all_attrs, oti_global_vars}, cs))
		  		= checkOpenAType mod_index scope DAK_Ignore dt_type (ots, oti, cs)
		  th_vars = foldSt (\{tv_info_ptr} -> writePtr tv_info_ptr TVI_Empty) oti_global_vars oti_heaps.th_vars
	  	  cs_symbol_table = removeAttributedTypeVarsFromSymbolTable scope dt_uni_vars cs.cs_symbol_table
		| isEmpty oti_all_attrs
			= ({ dt & dt_uni_vars = dt_uni_vars, dt_global_vars = oti_global_vars, dt_type = dt_type },
					oti_all_vars, ots_type_defs, ots_modules, { oti_heaps & th_vars = th_vars }, { cs & cs_symbol_table = cs_symbol_table })
			# cs_symbol_table = removeAttributesFromSymbolTable oti_all_attrs cs_symbol_table
			= ({ dt & dt_uni_vars = dt_uni_vars, dt_global_vars = oti_global_vars, dt_type = dt_type },
					oti_all_vars, ots_type_defs, ots_modules, { oti_heaps & th_vars = th_vars },
					{ cs & cs_symbol_table = cs_symbol_table, cs_error = checkError (hd oti_all_attrs).av_name "type attribute variable not allowed" cs.cs_error})

	add_type_variable_to_symbol_table :: !Level !ATypeVar !*(!*TypeVarHeap,!*CheckState) -> (!ATypeVar,!(!*TypeVarHeap, !*CheckState))
	add_type_variable_to_symbol_table scope atv=:{atv_variable=atv_variable=:{tv_name}, atv_attribute} (type_var_heap, cs=:{cs_symbol_table,cs_error})
		#  var_info = tv_name.id_info
		   (var_entry, cs_symbol_table) = readPtr var_info cs_symbol_table
		| var_entry.ste_kind == STE_Empty || scope < var_entry.ste_def_level
			#! (new_var_ptr, type_var_heap) = newPtr TVI_Empty type_var_heap
			# cs_symbol_table = cs_symbol_table <:=
				(var_info, {ste_index = NoIndex, ste_kind = STE_TypeVariable new_var_ptr, ste_def_level = scope, ste_previous = var_entry })
			= ({atv & atv_attribute = TA_Multi, atv_variable = { atv_variable & tv_info_ptr = new_var_ptr }}, (type_var_heap,
					{ cs & cs_symbol_table = cs_symbol_table, cs_error = check_attribute atv_attribute cs_error}))
			= (atv, (type_var_heap, { cs & cs_symbol_table = cs_symbol_table, cs_error = checkError tv_name.id_name "type variable already defined" cs_error }))

	check_attribute TA_Unique error
		= error
	check_attribute TA_Multi error
		= error
	check_attribute TA_None error
		= error
	check_attribute attr error
		= checkError attr "attribute not allowed in type of dynamic" error


checkSpecialTypeVars :: !Specials !*CheckState -> (!Specials, !*CheckState)
checkSpecialTypeVars (SP_ParsedSubstitutions env) cs
	# (env, cs) = mapSt (mapSt check_type_var) env cs
	= (SP_ParsedSubstitutions env, cs)
where
	check_type_var bind=:{bind_dst=type_var=:{tv_name={id_name,id_info}}} cs=:{cs_symbol_table,cs_error}
		# ({ste_kind,ste_def_level}, cs_symbol_table) = readPtr id_info cs_symbol_table
		| ste_kind <> STE_Empty && ste_def_level == cGlobalScope
			# (STE_TypeVariable tv_info_ptr) = ste_kind
			= ({ bind & bind_dst = { type_var & tv_info_ptr = tv_info_ptr}}, { cs & cs_symbol_table = cs_symbol_table })
			= (bind, { cs & cs_symbol_table= cs_symbol_table, cs_error = checkError id_name "type variable not defined" cs_error })
checkSpecialTypeVars SP_None cs
	= (SP_None, cs)

checkSpecialTypes :: !Index !Specials !v:{#CheckedTypeDef} !u:{#.DclModule} !*TypeHeaps !*CheckState
	-> (!Specials,!x:{#CheckedTypeDef},!w:{#DclModule},!.TypeHeaps,!.CheckState), [u v <= w, v u <= x]
checkSpecialTypes mod_index (SP_ParsedSubstitutions envs) type_defs modules heaps cs
	# ots = { ots_type_defs = type_defs, ots_modules = modules }
	  (specials, (heaps, ots, cs)) = mapSt (check_environment mod_index) envs (heaps, ots, cs)
	= (SP_Substitutions specials, ots.ots_type_defs, ots.ots_modules, heaps, cs)
where
	check_environment mod_index env (heaps, ots, cs)
	 	# oti = { oti_heaps = heaps, oti_all_vars = [], oti_all_attrs = [], oti_global_vars = [] }
	 	  (env, (ots, {oti_heaps,oti_all_vars,oti_all_attrs}, cs)) = mapSt (check_substituted_type mod_index) env (ots, oti, cs)
	  	  cs_symbol_table = removeVariablesFromSymbolTable cGlobalScope oti_all_vars cs.cs_symbol_table
		  cs_symbol_table = removeAttributesFromSymbolTable oti_all_attrs cs_symbol_table
		= ({ ss_environ = env, ss_context = [], ss_vars = oti_all_vars, ss_attrs = oti_all_attrs}, (oti_heaps, ots, { cs & cs_symbol_table = cs_symbol_table }))

	check_substituted_type mod_index bind=:{bind_src} cot_state
		 # (bind_src, cot_state) = checkOpenType mod_index cGlobalScope DAK_Ignore bind_src cot_state
		 = ({ bind & bind_src = bind_src }, cot_state)
checkSpecialTypes mod_index SP_None type_defs modules heaps cs
	= (SP_None, type_defs, modules, heaps, cs)

/* cOuterMostLevel :== 0 */

addTypeVariablesToSymbolTable :: !Level ![ATypeVar] ![AttributeVar] !*TypeHeaps !*CheckState
	-> (![ATypeVar], !(![AttributeVar], !*TypeHeaps, !*CheckState))
addTypeVariablesToSymbolTable scope type_vars attr_vars heaps cs
	= mapSt (add_type_variable_to_symbol_table scope) type_vars (attr_vars, heaps, cs)
where
	add_type_variable_to_symbol_table :: !Level !ATypeVar !(![AttributeVar], !*TypeHeaps, !*CheckState)
		-> (!ATypeVar, !(![AttributeVar], !*TypeHeaps, !*CheckState))
	add_type_variable_to_symbol_table scope atv=:{atv_variable=atv_variable=:{tv_name}, atv_attribute}
		(attr_vars, heaps=:{th_vars,th_attrs}, cs=:{ cs_symbol_table, cs_error })
		# tv_info = tv_name.id_info
		  (entry, cs_symbol_table) = readPtr tv_info cs_symbol_table
		| entry.ste_def_level < scope // cOuterMostLevel
			# (tv_info_ptr, th_vars) = newPtr TVI_Empty th_vars
		      atv_variable = { atv_variable & tv_info_ptr = tv_info_ptr }
		      (atv_attribute, attr_vars, th_attrs, cs_error) = check_attribute (scope == cRankTwoScope) atv_attribute tv_name.id_name attr_vars th_attrs cs_error
			  cs_symbol_table = cs_symbol_table <:= (tv_info, {ste_index = NoIndex, ste_kind = STE_BoundTypeVariable {stv_attribute = atv_attribute,
			  						stv_info_ptr = tv_info_ptr, stv_count = 0}, ste_def_level = scope /* cOuterMostLevel */, ste_previous = entry })
			  heaps = { heaps & th_vars = th_vars, th_attrs = th_attrs }
			= ({atv & atv_variable = atv_variable, atv_attribute = atv_attribute},
					(attr_vars, heaps, { cs & cs_symbol_table = cs_symbol_table, cs_error = cs_error }))
			= (atv, (attr_vars, { heaps & th_vars = th_vars },
					 { cs & cs_symbol_table = cs_symbol_table, cs_error = checkError tv_name.id_name "type variable already defined" cs_error }))

	check_attribute :: !Bool !TypeAttribute !String ![AttributeVar] !*AttrVarHeap !*ErrorAdmin
		-> (!TypeAttribute, ![AttributeVar], !*AttrVarHeap, !*ErrorAdmin)
	check_attribute _ TA_Unique name attr_vars attr_var_heap cs
		= (TA_Unique, attr_vars, attr_var_heap, cs)
	check_attribute is_rank_two attr name attr_vars attr_var_heap cs
		| is_rank_two
			= check_rank_two_attribute attr attr_vars attr_var_heap cs
			= check_global_attribute attr name attr_vars attr_var_heap cs
	where
		check_global_attribute TA_Multi name attr_vars attr_var_heap cs
			# (attr_info_ptr, attr_var_heap) = newPtr AVI_Empty attr_var_heap
			  new_var = { av_name = emptyIdent name, av_info_ptr = attr_info_ptr}
			= (TA_Var new_var, [new_var : attr_vars], attr_var_heap, cs)
		check_global_attribute TA_None name attr_vars attr_var_heap cs
			# (attr_info_ptr, attr_var_heap) = newPtr AVI_Empty attr_var_heap
			  new_var = { av_name = emptyIdent name, av_info_ptr = attr_info_ptr}
			= (TA_Var new_var, [new_var : attr_vars], attr_var_heap, cs)
		check_global_attribute _ name attr_vars attr_var_heap cs
			= (TA_Multi, attr_vars, attr_var_heap, checkError name "specified attribute variable not allowed" cs)

		check_rank_two_attribute (TA_Var var) attr_vars attr_var_heap cs
			# (attr_info_ptr, attr_var_heap) = newPtr AVI_Empty attr_var_heap
			  new_var = { var & av_info_ptr = attr_info_ptr}
			= (TA_Var new_var, [new_var : attr_vars], attr_var_heap, cs)
		check_rank_two_attribute TA_Anonymous attr_vars attr_var_heap cs
			= abort "check_rank_two_attribute (TA_Anonymous, check_types.icl)"
/*			# (attr_info_ptr, attr_var_heap) = newPtr AVI_Empty attr_var_heap
			  new_var = { av_name = emptyIdent name, av_info_ptr = attr_info_ptr}
			= (TA_Var new_var, [new_var : attr_vars], attr_var_heap, cs)
*/		check_rank_two_attribute attr attr_vars attr_var_heap cs
			= (attr, attr_vars, attr_var_heap, cs)

addExistentionalTypeVariablesToSymbolTable :: !TypeAttribute ![ATypeVar] !*TypeHeaps !*CheckState
	-> (![ATypeVar], !(!*TypeHeaps, !*CheckState))
addExistentionalTypeVariablesToSymbolTable root_attr type_vars heaps cs
	= mapSt (add_exi_variable_to_symbol_table root_attr) type_vars (heaps, cs)
where
	add_exi_variable_to_symbol_table :: !TypeAttribute !ATypeVar !(!*TypeHeaps, !*CheckState)
		-> (!ATypeVar, !(!*TypeHeaps, !*CheckState))
	add_exi_variable_to_symbol_table root_attr atv=:{atv_variable=atv_variable=:{tv_name}, atv_attribute}
		(heaps=:{th_vars,th_attrs}, cs=:{ cs_symbol_table, cs_error})
		# tv_info = tv_name.id_info
		  (entry, cs_symbol_table) = readPtr tv_info cs_symbol_table
		| entry.ste_def_level < cGlobalScope // cOuterMostLevel
			# (tv_info_ptr, th_vars) = newPtr TVI_Empty th_vars
		      atv_variable = { atv_variable & tv_info_ptr = tv_info_ptr }
		      (atv_attribute, th_attrs, cs_error) = check_attribute atv_attribute root_attr tv_name.id_name th_attrs cs_error
			  cs_symbol_table = cs_symbol_table <:= (tv_info, {ste_index = NoIndex, ste_kind = STE_BoundTypeVariable {stv_attribute = atv_attribute,
			  						stv_info_ptr = tv_info_ptr, stv_count = 0  }, ste_def_level = cGlobalScope /* cOuterMostLevel */, ste_previous = entry })
			  heaps = { heaps & th_vars = th_vars, th_attrs = th_attrs }
			= ({atv & atv_variable = atv_variable, atv_attribute = atv_attribute},
					(heaps, { cs & cs_symbol_table = cs_symbol_table, cs_error = cs_error}))
			= (atv, ({ heaps & th_vars = th_vars },
					 { cs & cs_symbol_table = cs_symbol_table, cs_error = checkError tv_name.id_name "type variable already defined" cs_error}))
/*
	check_attribute :: !TypeAttribute !TypeAttribute !String !*ErrorAdmin
		-> (!TypeAttribute, !*ErrorAdmin)
	check_attribute TA_Multi root_attr name error
		= (TA_Multi, error)
	check_attribute TA_None root_attr name error
		= (TA_Multi, error)
	check_attribute TA_Unique root_attr name error
		= (TA_Unique, error)
	check_attribute TA_Anonymous root_attr name error
		= case root_attr of
			TA_Var var
				-> (TA_RootVar var, error)
			_
				-> (PA_BUG (TA_RootVar (abort "SwitchUniquenessBug is on")) root_attr, error)
	check_attribute attr root_attr name error
		= (TA_Multi, checkError name "specified attribute not allowed" error)
*/


	check_attribute :: !TypeAttribute !TypeAttribute !String !*AttrVarHeap !*ErrorAdmin
		-> (!TypeAttribute, !*AttrVarHeap, !*ErrorAdmin)
	check_attribute TA_Multi root_attr name attr_var_heap error
		= (TA_Multi, attr_var_heap, error)
	check_attribute TA_None root_attr name attr_var_heap error
		= (TA_Multi, attr_var_heap, error)
	check_attribute TA_Unique root_attr name attr_var_heap error
		= (TA_Unique, attr_var_heap, error)
	check_attribute (TA_Var var) root_attr name attr_var_heap error
		= case root_attr of
			TA_Var root_var
				-> (TA_RootVar root_var, attr_var_heap, error)
			TA_Unique
				# (attr_info_ptr, attr_var_heap) = newPtr AVI_Empty attr_var_heap
				-> (TA_Var { var & av_info_ptr = attr_info_ptr}, attr_var_heap, error)
//				-> (PA_BUG (TA_RootVar (abort "SwitchUniquenessBug is on")) root_attr, error)
	check_attribute attr root_attr name attr_var_heap error
		= (TA_Multi, attr_var_heap, checkError name "specified attribute not allowed" error)


retrieveKinds :: ![ATypeVar] *TypeVarHeap -> (![TypeKind], !*TypeVarHeap)
retrieveKinds type_vars var_heap = mapSt retrieve_kind type_vars var_heap
where
	retrieve_kind {atv_variable = {tv_info_ptr}} var_heap
		# (TVI_TypeKind kind_info_ptr, var_heap) = readPtr tv_info_ptr var_heap
		= (KindVar kind_info_ptr, var_heap)

removeAttributedTypeVarsFromSymbolTable :: !Level ![ATypeVar] !*SymbolTable -> *SymbolTable
removeAttributedTypeVarsFromSymbolTable level vars symbol_table
	= foldr (\{atv_variable={tv_name}} -> removeDefinitionFromSymbolTable level tv_name) symbol_table vars


cExistentialVariable	:== True
cUniversalVariable 		:== False

removeDefinitionFromSymbolTable level {id_info} symbol_table
	| isNilPtr id_info
		= symbol_table
		# ({ste_def_level, ste_previous}, symbol_table) = readPtr id_info symbol_table
		| ste_def_level >= level
			= symbol_table <:= (id_info, ste_previous)
			= symbol_table

removeAttributesFromSymbolTable :: ![AttributeVar] !*SymbolTable -> *SymbolTable
removeAttributesFromSymbolTable attrs symbol_table
	= foldr (\{av_name} -> removeDefinitionFromSymbolTable cGlobalScope av_name) symbol_table attrs

removeVariablesFromSymbolTable :: !Int ![TypeVar] !*SymbolTable -> *SymbolTable
removeVariablesFromSymbolTable scope vars symbol_table
	= foldr (\{tv_name} -> removeDefinitionFromSymbolTable scope tv_name) symbol_table vars

::	Indexes =
	{	index_type		:: !Index
	,	index_cons		:: !Index
	,	index_selector	:: !Index
	}

makeAttributedType attr annot type :== { at_attribute = attr, at_annotation = annot, at_type = type }

class toVariable var :: !STE_Kind !Ident -> var

instance toVariable TypeVar
where
	toVariable (STE_TypeVariable info_ptr) ident = { tv_name = ident, tv_info_ptr = info_ptr }

instance toVariable AttributeVar
where
	toVariable (STE_TypeAttribute info_ptr) ident = { av_name = ident, av_info_ptr = info_ptr }

instance <<< DynamicType
where
	(<<<) file {dt_global_vars,dt_type} = file <<< dt_global_vars <<< dt_type


/****************************
* BUILDING DICTIONARY TYPES *
****************************/

/* This function converts a single class to a dictionary, with:
    - dictionary type (in the symbol table, prepended to the accumulator, stored in the classdef)
	- dictionary constructor (in the symbol table)
	- dictionary field selectors (in the symbol table)
   A later function puts these in their relevant arrays if necessary
*/

createClassDictionaries2 ::
	Index                   // Module index of dictionary being converted
	*{#ClassDef}            // Array of classes to convert
	u1:{#MemberDef}         // Array of class members of classes to convert
	u2:{#.DclModule}        // DCL modules for looking up context classes
	u3:{#CheckedTypeDef}    // Typedef array to update with dictionary type
	u4:{#SelectorDef}       // Selectordef array to update with dictionary field selectors
	u5:{#ConsDef}           // Consdef array to update with dictionary constructor
	*TypeHeaps              // Heaps to allocate fresh type and attribute variables from
	*VarHeap                // Heap to allocate fresh variable from
	*SymbolTable            // Symbol table to store dictionary types, constructors, and field selectors
 ->	( .{#ClassDef}          // Updated array of classes (class_dictionary)
	, v1:{#MemberDef}       // Used array of class members
	, v2:{#DclModule}       // Used DCL modules
	, v3:{#CheckedTypeDef}  // Typedef array updated with dictionary types
	, v4:{#SelectorDef}     // Selectordef array updated with dictionary field selectors
	, v5:{#ConsDef}         // Consdef array updated with dictionary constructors
	, .TypeHeaps            // Extended type heaps
	, .VarHeap              // Extended heap
	, .SymbolTable          // Updated symbol table
	)
 ,	[u1<=v1, u2<=v2, u3<=v3, u4<=v4, u5<=v5]

createClassDictionaries2 modindex classdefs0 memberdefs0 dcls0 typedefs0 seldefs0 consdefs0 typeheaps0 vheap0 symboltable0
= (classdefs1, memberdefs1, dcls1, typedefs1, seldefs1, consdefs1, typeheaps1, vheap1, symboltable1)
  where (classdefs1, memberdefs1, typedefs1, consdefs1, seldefs1, symboltable1, vheap1, typeheaps1, dcls1)
        = convert_classdefs get_classdef modindex (classdefs0, memberdefs0, typedefs0, consdefs0, seldefs0, symboltable0, vheap0, typeheaps0, dcls0)
		get_classdef {glob_module,glob_object} (dcls_a, classdefs_a)
		= (classdef, (dcls_b, classdefs_b))
		  where (classdef, _, classdefs_b, dcls_b) = getClassDef glob_object glob_module modindex classdefs_a dcls_a

convert_classdefs ::
	((Global Index) (.env, .{#ClassDef}) -> (ClassDef, (.env, *{#ClassDef}))) // Getting the definition of a context class
	.Int                                     // Module index of dictionary being converted
	( *{#ClassDef}                           // Array of classes to convert
	, u1:{#MemberDef}                         // Array of class members of classes to convert
	, u2:{#CheckedTypeDef}                     // Typedef array to update with dictionary type
	, u3:{#ConsDef}                            // Consdef array to update with dictionary constructor
	, u4:{#SelectorDef}                        // Selectordef array to update with dictionary field selectors
	, *SymbolTable                           // Symbol table to store dictionary types, constructors, and field selectors
	, *VarHeap                               // Heap to allocate fresh variable from
	, *TypeHeaps                             // Heaps to allocate fresh type and attribute variables from
	, .env                                   // Environment for looking up context classes
	)
 ->	( .{#ClassDef}                           // Updated array of classes (class_dictionary)
	, v1:{#MemberDef}                         // Used array of class members
	, v2:{#CheckedTypeDef}                     // Typedef array updated with dictionary type
	, v3:{#ConsDef}                            // Consdef array updated with dictionary constructor
	, v4:{#SelectorDef}                        // Selectordef array updated with dictionary field selectors
	, .SymbolTable                           // Updated symbol table
	, .VarHeap                               // Extended heap
	, .TypeHeaps                             // Extended heaps
	, .env                                   // Used environment
	)
 ,	[u1<=v1, u2<=v2, u3<=v3, u4<=v4]

convert_classdefs get_classdef modindex (classdefs0, memberdefs0, typedefs0, consdefs0, seldefs0, symboltable0, varheap0, typeheaps0, env0)
= (classdefs2, memberdefs1, typedefs5, consdefs5, seldefs5, symboltable1, varheap1, typeheaps1, env1)
  where (classdefs2, memberdefs1, typedefs4, consdefs4, seldefs4, indexes1, symboltable1, varheap1, typeheaps1, env1)
        = iFoldSt (convert_classdef get_classdef modindex) 0 nclass (classdefs1, memberdefs0, typedefs3, consdefs3, seldefs3, indexes0, symboltable0, varheap0, typeheaps0, env0)
        (nclass, classdefs1) = usize classdefs0
		// Some wizardry to prevent copying the array if nothing is to be appended
		// ... and still make use of input uniqueness and produce output uniqueness
		typedefs5 = if (ntypedef0==ntypedef1) typedefs2 typedefs4
		(typedefs3,typedefs2) = resizeArray emptyCheckedTypeDef ntypedef1 typedefs1
		consdefs5 = if (nconsdef0==nconsdef1) consdefs2 consdefs4
		(consdefs3,consdefs2) = resizeArray emptyConsDef nconsdef1 consdefs1
		seldefs5 = if (nseldef0==nseldef1) seldefs2 seldefs4
		(seldefs3,seldefs2) = resizeArray emptySelectorDef nseldef1 seldefs1
		{index_type = ntypedef1, index_cons = nconsdef1, index_selector = nseldef1} = indexes1
		indexes0 = {index_type = ntypedef0, index_cons = nconsdef0, index_selector = nseldef0}
		(ntypedef0, typedefs1) = usize typedefs0
		(nconsdef0, consdefs1) = usize consdefs0
		(nseldef0, seldefs1) = usize seldefs0

convert_classdef ::
	((Global Index) (.env, .{#ClassDef}) -> (ClassDef, (.env, *{#ClassDef}))) // Getting the definition of a context class
	.Index                                   // Module index of dictionary being converted
	.Index                                   // Class to convert
	( *{#ClassDef}                           // Array of classes to convert
	, u1:{#MemberDef}                        // Array of class members of classes to convert
	, *{#CheckedTypeDef}                     // Typedef array to update with dictionary type
	, *{#ConsDef}                            // Consdef array to update with dictionary constructor
	, *{#SelectorDef}                        // Selectordef array to update with dictionary field selectors
	, Indexes                                // Where to store the next type, constructor, and selector
	, *SymbolTable                           // Symbol table to store dictionary types, constructors, and field selectors
	, *VarHeap                               // Heap to allocate fresh variable from
	, *TypeHeaps                             // Heaps to allocate fresh type and attribute variables from
	, .env                                   // Environment for looking up context classes
	)
 ->	( .{#ClassDef}                           // Updated array of classes (class_dictionary)
	, v1:{#MemberDef}                        // Used array of class members
	, .{#CheckedTypeDef}                     // Typedef array updated with dictionary type
	, .{#ConsDef}                            // Consdef array updated with dictionary constructor
	, .{#SelectorDef}                        // Selectordef array updated with dictionary field selectors
	, Indexes                                // Where to store the next type, constructor, and selector after these
	, .SymbolTable                           // Updated symbol table
	, .VarHeap                               // Extended heap
	, .TypeHeaps                             // Extended heaps
	, .env                                   // Used environment
	)
 ,  [u1<=v1]

convert_classdef get_classdef0 modindex classindex (classdefs0, memberdefs0, typedefs0, consdefs0, seldefs0, indexes0, symboltable0, varheap0, typeheaps0, env0)
= (classdefs3, memberdefs1, typedefs1, consdefs1, seldefs1, indexes1, symboltable1, varheap1, typeheaps1, env1)
  where classdefs3 = {classdefs2 & [classindex] = classdef1}
		classdef1 = {classdef0 & class_dictionary = dicttypedef}
        (dicttypedef, memberdefs1, typedefs1, consdefs1, seldefs1, indexes1, symboltable1, varheap1, typeheaps1, (env1,classdefs2))
        = build_dicttypedef get_classdef0 modindex classindex classdef0 memberdefs0 typedefs0 consdefs0 seldefs0 indexes0 symboltable0 varheap0 typeheaps0 (env0,classdefs1)
		(classdef0, classdefs1) = classdefs0![classindex]

build_dicttypedef ::
	((Global Index) .env -> (ClassDef,.env)) // Getting the definition of a context class
	.Index               // Module index of dictionary being converted
	.Index               // Index of class definition
	ClassDef             // Class to convert
	u1:{#MemberDef}      // Array of member definitions
	*{#CheckedTypeDef}   // Typedef array to update with dictionary type
	*{#ConsDef}          // Consdef array to update with dictionary constructor
	*{#SelectorDef}      // Selectordef array to update with dictionary field selectors
	Indexes              // Where to store the next type, constructor, and selectors
	*SymbolTable         // Symbol table to store defined symbols in
	*VarHeap             // Heap for allocating fresh variables
	*TypeHeaps           // Heap for allocating fresh type and attribute variables
	.env                 // Environment for looking up contexts and members
 ->	( DefinedSymbol      // Defined dictionary type symbol
	, v1:{#MemberDef}    // Used array of member definitions
	, .{#CheckedTypeDef} // Typedef array updated with dictionary type
	, .{#ConsDef}        // Consdef array updated with dictionary constructor
	, .{#SelectorDef}    // Selectordef array updated with dictionary field selectors
	, Indexes            // Where to store the next type, constructor, and selectors after these
    , .SymbolTable       // Extended symbol table
	, .VarHeap           // Used variable heap
	, .TypeHeaps         // Used type heaps
	, .env               // Used environment
	)
 ,  [u1<=v1]

build_dicttypedef get_classdef0 modindex classindex classdef memberdefs0 typedefs0 consdefs0 seldefs0 indexes0 symboltable0 varheap0 typeheaps0 env0
| not ok
  = abort "build_dicttypedef (checktypes.icl): substitute failed?"
= (dict_defsymb, memberdefs1, typedefs1, consdefs1, seldefs1, indexes1, symboltable3, varheap2, typeheaps3, env1)
  where dict_defsymb = { ds_ident = dict_ident
                       , ds_arity = dict_arity
					   , ds_index = dictindex
					   }
        dict_ident = { id_name = classdef.class_name.id_name
		             , id_info = dict_symbolptr
					 }
		(dict_symbolptr, symboltable3) = newSymbolPtr (STE_DictType dict_typedef) dictindex symboltable2
		typedefs1 = {typedefs0 & [dictindex] = dict_typedef}
		dict_typedef
 		= { td_name       = dict_ident
		  , td_index      = dictindex
		  , td_arity      = dict_arity
		  , td_args       = dict_typeargs
		  , td_attrs      = [] // FIXME: Should this be filled in?
		  , td_context    = []
		  , td_rhs        = RecordType {rt_constructor = constr_defsym, rt_fields = fields}
		  , td_attribute  = TA_None
		  , td_pos        = classdef.class_pos
		  , td_used_types = [] // FIXME: What's this supposed to be?
	      }
		dict_arity = length dict_typeargs
		(ok, class_typeargs, typeheaps3) = substitute dict_type_vars typeheaps2
		(constr_defsym, consdefs1, symboltable2, varheap2, typeheaps2)
		= build_constructor classdef dictindex dicttype dict_type_vars constr_index fieldinfos consdefs0 symboltable1 varheap1 typeheaps1
		(fields, fieldinfos, seldefs1, varheap1, typeheaps1, symboltable1, (memberdefs1, env1))
		= build_selectors get_classdef1 get_memberdef dict_type_vars dicttype classdef selindex (seldefs0, varheap0, typeheaps0, symboltable0, (memberdefs0, env0))
		dict_typeargs = map build_atypevar class_typeargs
		dicttype = build_dicttype modindex classdef
		nfield = nmember+ncontext
		nmember = size classdef.class_members
		ncontext = length classdef.class_context
		dict_type_vars = classdef.class_args
		indexes1 = {index_type = inc dictindex, index_cons = inc constr_index, index_selector = selindex+nmember+ncontext}
		{index_type = dictindex, index_cons = constr_index, index_selector = selindex} = indexes0
		get_memberdef memberindex (memberdefs0,env0)
		= (memberdef, (memberdefs1, env0))
		  where (memberdef,memberdefs1) = memberdefs0![memberindex]
		get_classdef1 classindex (memberdefs0, env0)
		= (classdef, (memberdefs0, env1))
		  where (classdef, env1) = get_classdef0 classindex env0

:: FieldInfo :== (AType, [TypeVar], [AttributeVar], [AttrInequality])


/***********************************
* BUILDING DICTIONARY CONSTRUCTORS *
***********************************/

build_constructor ::
	ClassDef               // Class being converted
	Index                  // Index of dictionary type
	AType                  // Dictionary type
	[TypeVar]              // Polymorphic type variables bound by dictionary (class' type arguments)
	Index                  // Where to store the constructor symbol
	[FieldInfo]            // Dictionary fields
	*{#ConsDef}            // Consdef array to update with created dictionary constructor
	*SymbolTable           // Symbol table to store the constructor symbol
	*VarHeap               // Heap for allocating fresh constructor variable pointer
	*TypeHeaps             // For allocating fresh type variables
 ->	( DefinedSymbol        // Resulting constructor symbol
	, .{#ConsDef}          // Consdef array updated with created dictionary constructor
	, .SymbolTable         // Updated symbol table
	, .VarHeap             // Used variable heap
	, .TypeHeaps           // Used type heaps
	)

build_constructor classdef dictindex dicttype dicttypevars constr_index typeinfos consdefs0 symboltable0 varheap0 typeheaps0
| not ok1
  = abort "build_constructor (checktypes.icl): copy_symboltype failed?"
| not ok2
  = abort "build_constructor (checktypes.icl): substitute failed?"
= (constr_defsymbol, consdefs1, symboltable1, varheap1, typeheaps2)
  where constr_defsymbol = {ds_ident = constr_ident, ds_arity = constr_arity, ds_index = constr_index}
        constr_ident = {id_name = classdef.class_name.id_name, id_info = constr_symbol_ptr}
		(constr_symbol_ptr, symboltable1) = newSymbolPtr (STE_DictCons constr_cons) constr_index symboltable0
		consdefs1 = {consdefs0 & [constr_index] = constr_cons}
		constr_cons
		= { cons_symb       = constr_ident
		  , cons_type       = constr_type_copy
		  , cons_arg_vars   = constr_atvs_copy
		  , cons_priority   = NoPrio
		  , cons_index      = constr_index
		  , cons_type_index = dictindex
		  , cons_exi_vars   = []
		  , cons_type_ptr   = constr_vip
		  , cons_pos        = classdef.class_pos
		  }
		(constr_vip, varheap1) = newPtr VI_Empty varheap0
		(ok1, constr_type_copy, typeheaps1) = copy_symboltype dicttypevars constr_type typeheaps0
		(ok2, constr_atvs_copy, typeheaps2) = substitute argvarss typeheaps1
		constr_type
		= { st_vars      = removeDup (flatten typevarss)
		  , st_args      = fieldtypes
		  , st_arity     = constr_arity
		  , st_result    = dicttype
		  , st_context   = []
		  , st_attr_vars = removeDup (flatten attrvarss)
		  , st_attr_env  = removeDup (flatten attr_ineqs)
		  }
		constr_arity = length fieldtypes
		argvarss = map (map build_atypevar) typevarss
		(fieldtypes, typevarss, attrvarss, attr_ineqs) = unzip4 typeinfos

build_constructor_type (typevars, fieldtype) (argvarss, constr_type_args)
= ([argvars:argvarss], [fieldtype:constr_type_args])
  where argvars = map build_atypevar typevars
build_atypevar typevar = {atv_attribute = TA_Multi, atv_annotation = AN_None, atv_variable = typevar}

/********************************
* BUILDING DICTIONARY SELECTORS *
********************************/
// Built selectors are put into the symbol table


build_selectors ::
	((Global Index) .env -> (ClassDef,.env)) // Getting the definition of a context class
	(Index .env -> (MemberDef,.env))         // Getting the member definition of a class member
	[TypeVar]                                // Polymorphic type variables of dictionary (class arguments)
	AType                                    // Application of current dictionary type
	ClassDef                                 // Class being converted
	Index                                    // Index where first selector is stored
	(*{#SelectorDef}, *VarHeap, *TypeHeaps, *SymbolTable, .env)
 -> (.{#FieldSymbol}, .[FieldInfo], .{#SelectorDef}, .VarHeap, .TypeHeaps, .SymbolTable, .env)
build_selectors get_classdef get_memberdef dict_type_vars dicttype classdef selindex (seldefs0, varheap0, typeheaps0, symboltable0, env0)
= (fields2, fieldinfos2, seldefs2, verheap2, typeheaps2, symboltable2, env2)
  where (fields2, fieldinfos2, seldefs2, verheap2, typeheaps2, symboltable2, env2)
		= foldrarray (build_member_selector dict_type_vars dicttype classdef get_memberdef selindex 0) ftvhthst1 class_members
        ftvhthst1 = foldrwithindex (build_context_selector get_contexttype classdef dicttype (selindex+nmember) nmember)
								   (fields0, [], seldefs0, varheap0, typeheaps0, symboltable0, env0)
								   class_context
		{class_members,class_context} = classdef
		get_contexttype typecontext env0
		= (atype, env1)
		  where atype = convert_typecontext typecontext classdef
		        (classdef, env1) = get_classdef (get_global_ds_index typecontext.tc_class) env0
		fields0 = createArray (nmember+ncontext) emptyFieldSymbol
		nmember = size classdef.class_members
		ncontext = length classdef.class_context

get_global_ds_index = mapglobal get_ds_index
mapglobal f gl = {glob_module = gl.glob_module, glob_object = f gl.glob_object}
get_ds_index = \ds->ds.ds_index

// Convert a typecontext pointing to a classdef that's being converted to a typedef into a dictionary application
convert_typecontext :: TypeContext ClassDef -> AType
convert_typecontext typecontext classdef
# typesymbindex = classdef.class_dictionary.ds_index
# globaltypesymbindex = {glob_module=typecontext.tc_class.glob_module, glob_object=typesymbindex}
# dictsymbident = MakeTypeSymbIdent globaltypesymbindex classdef.class_dictionary.ds_ident classdef.class_arity
= makeAttributedType TA_Multi AN_Strict (TA dictsymbident (map (makeAttributedType TA_Multi AN_None) typecontext.tc_types))

// Convert a class to its dictionary type
build_dicttype :: Index ClassDef -> AType
build_dicttype modindex classdef
# typesymbindex = classdef.class_dictionary.ds_index
# globaltypesymbindex = {glob_module = modindex, glob_object = typesymbindex}
# dictsymbident = MakeTypeSymbIdent globaltypesymbindex classdef.class_dictionary.ds_ident classdef.class_arity
= makeAttributedType TA_Multi AN_Strict (TA dictsymbident (map (makeAttributedType TA_Multi AN_None o TV) classdef.class_args))

build_member_selector ::
	.[TypeVar]                             // Polymorphic type variables of dictionary type (arguments of class)
	AType                                  // Application of dictionary type
	.ClassDef                              // Class being converted to dictionary
	(Index .envin -> (MemberDef,.envout))  // Getting the definition of the class member
	.Index                                 // Offset where first member selector is stored in selectordef array
	.Index                                 // Offset where first member field is stored in record
	.Int                                   // Index of member in class
	.DefinedSymbol                         // Member to create dictionary selector for
	( *{#FieldSymbol}                      // Storage for defined record field
	, [u1:FieldInfo]                       // Types of remaining fields (accumulator)
	, *{#SelectorDef}                      // Storage for defined selector
	, *VarHeap                             // Heap for allocating fresh (value) variables
	, *TypeHeaps                           // Heaps for creating fresh type and attribute variables
	, *SymbolTable                         // Destination for generated member selector symbol
	, .envin
	)
 -> ( .{#FieldSymbol}                      // Updated storage
	, [v1:FieldInfo]                       // Extended field types
	, .{#SelectorDef}                      // Updated storage
    , .VarHeap                             // Used heap
	, .TypeHeaps                           // Used heaps
	, .SymbolTable                         // Extended symbol table
	, .envout
	)
 ,  [u1<=v1]

build_member_selector dict_type_vars dict_type classdef get_memberdef selectoroffset fieldoffset memberindex membersymbol state
	// Unpack state.  Has to be done lazily, so here.  I hate strict tuple matching.
    # (fields, fieldinfos, seldefs, varheap, typeheaps, symbol_table, env) = state
	// Determine where the selector and field goes
	# selectorindex = selectoroffset+memberindex
	  fieldindex = fieldoffset+memberindex
	// Fetch the member's definition
	# (memberdef,env) = get_memberdef membersymbol.ds_index env
	// Create fresh instance of member's type
	# (fieldinfo, selectortype, typeheaps)
	  = build_member_selector_type dict_type_vars dict_type memberdef.me_type typeheaps
	# (fields, seldefs, varheap, symbol_table)
	  = build_selector selectorindex selectortype fieldindex membersymbol.ds_ident.id_name classdef.class_dictionary.ds_index memberdef.me_pos (fields, seldefs, varheap, symbol_table)
	= (fields, [fieldinfo:fieldinfos], seldefs, varheap, typeheaps, symbol_table, env)

/* Build the type of a dictory member field selector
 * Strategy: First build what we want without refreshing type variables
 *           Then copy the whole thing in one go
 */
build_member_selector_type ::
	.[TypeVar]   // Polymorphic type variables of dictionary (arguments of class)
	AType        // Application of dictionary type
	SymbolType   // Type of member
    *TypeHeaps   // Heaps for allocating fresh type and attribute variables
 -> ( .FieldInfo // fieldinfo
    , SymbolType // Resulting dictionary field selector type
	, .TypeHeaps // Used heaps
	)

build_member_selector_type dict_type_vars dict_type st=:{st_vars,st_args,st_result,st_attr_vars,st_attr_env} heaps
	# curried_member_type = foldr buildarrowtype st_result st_args
	# fieldinfo = (curried_member_type, st_vars, st_attr_vars, st_attr_env)
	# st = { st
		   & st_vars = removeDup (dict_type_vars++st_vars)
		   , st_args = [dict_type]
		   , st_arity = 1
		   , st_result = curried_member_type
		   }
    # (ok, symboltype, heaps) = copy_symboltype [] st heaps
	# symboltype = if ok symboltype (abort "build_member_selector_type (checktypes.icl): copy_symboltype failed?")
	= (fieldinfo, symboltype, heaps)

// FIXME: find out what to do with uniqueness
buildarrowtype :: AType AType -> AType
buildarrowtype argtype restype = makeAttributedType TA_Multi AN_None (argtype-->restype)

build_context_selector ::
	( TypeContext     // Context to find dictionary for
	  .envin          // Unique environment for lookup
	-> ( AType        // Resulting dictionary type
	   , .envout      // Used environment
	   )
	)                 // Get the dictionary type for a class' context
	ClassDef          // Class for which dictionary is being created
	AType             // Dictionary type corresponding to class
	.Index            // Offset where first selector of this dictionary is stored in selectordef array
	.Int              // Offset where first context is stored in dictionary
	.Int              // Index of context in list of contexts
    TypeContext       // Type context for which to generate selector
    ( *{#FieldSymbol} // Storage for defined field symbol
	, [u1:FieldInfo]  // Types of remaining fields (accumulator)
    , *{#SelectorDef} // Storage for defined selector symbol
	, *VarHeap        // Heap for allocating fresh (value) variables
	, *TypeHeaps      // Heaps for allocating fresh type and attribute variables
	, *SymbolTable    // Destination for generated context selector symbol
	, .envin          // Other unique environment parts
	)
 -> ( .{#FieldSymbol} // Updated storage
	, [v1:FieldInfo]  // Extended types
    , .{#SelectorDef} // Updated storage
    , .VarHeap        // Used heap
	, .TypeHeaps      // Used heaps
	, .SymbolTable    // Extended symbol table
	, .envout         // Consulted unique environment parts
	)
 ,  [u1<=v1]

build_context_selector get_contexttype classdef dicttype selectoroffset fieldoffset contextindex typecontext state
	// Lazily unpack state
    # (fields, fieldinfos, seldefs, varheap, typeheaps,symbol_table,env) = state
	// Determine where the selector goes
	# selectorindex = selectoroffset+contextindex  // FIXME: Use precomputed offset for context?
	// Find context dictionary of used context
	# (contexttype,env) = get_contexttype typecontext env
	# fieldinfo = (contexttype, [], noattrvars, noattrenv) // Dictionary field doesn't introduce new type variables
	  with // FIXME: What attribute variables/inequalities do we need?
	       noattrvars = [] // abort "build_context_selector (checktypes.icl): dictionary context field selector's attribute variables not implemented"
	       noattrenv = [] // abort "build_context_selector (checktypes.icl): dictionary context field selector's attribute inequalities not implemented"
	// Create fresh instance of context's type
	# (selectortype, typeheaps) = build_context_selector_type classdef dicttype contexttype typeheaps
	// Build the selector
	# (fields, seldefs, varheap, symbol_table) = build_selector selectorindex selectortype (fieldoffset+contextindex) typecontext.tc_class.glob_object.ds_ident.id_name classdef.class_dictionary.ds_index classdef.class_pos (fields, seldefs, varheap, symbol_table)
	= (fields, [fieldinfo:fieldinfos], seldefs, varheap, typeheaps, symbol_table, env)

/* Build the type of a dictory context field selector
 * Strategy: First build what we want without refreshing type variables
 *           Then copy the whole thing in one go
 */
build_context_selector_type ::
	ClassDef     // Class being converted to dictionary
	AType        // Dictionary type of class being converted
	AType        // Context's dictionary type
    *TypeHeaps   // Heaps for allocating fresh type and attribute variables
 -> ( SymbolType // Resulting dictionary field selector type
	, .TypeHeaps // Used heaps
	)

build_context_selector_type {class_args} dict_type contexttype heaps
	# st = { st_vars = class_args // Context doesn't introduce additional type variables like a member
	       , st_args = [dict_type]
	       , st_arity = 1
	       , st_result = contexttype
	       , st_context = []
	       , st_attr_vars = []
	       , st_attr_env = []
	       }
	# (ok, symboltype, heaps) = copy_symboltype [] st heaps
	# symboltype = if ok symboltype (abort "build_context_selector_type (checktypes.icl): copy_symboltype failed?")
	= (symboltype, heaps)

buildcontexttype ctxt_index=:{glob_module} ctxt_def=:{class_arity,class_dictionary={ds_ident,ds_index}} args
= makeAttributedType TA_Multi AN_Strict (TA classdictident (map (makeAttributedType TA_Multi AN_None) args))
  where classdictident = MakeTypeSymbIdent {glob_module=glob_module, glob_object=ds_index} ds_ident class_arity

build_selector ::
	Index             // Index of selector symbol in selectordef array
	SymbolType        // Type of selector
	Index             // Index of field in dictionary that this selector selects
	String            // Name of the field selector
	Index             // Index of dictionary this selector selects from
	Position          // Position in input where this selector is defined (member or context)
	( *{#FieldSymbol} // Storage for defined field
	, *{#SelectorDef} // Storage for defined selector
	, *VarHeap        // Heap for allocation of fresh (value) variables
	, *SymbolTable    // Symbol table to add selector symbol to
	)
 -> ( .{#FieldSymbol} // Updated storage
	, .{#SelectorDef} // Updated storage
	, .VarHeap        // Used variable heap
	, .SymbolTable    // Extended symbol table
	)
build_selector selectorindex selector_type fieldindex field_name dict_type_index selector_position (fields0, seldefs0, varheap0, symbol_table0)
= (fields1, seldefs1, varheap1, symbol_table1)
  where
		// Allocate type variable for selector
		(selector_var, varheap1) = newPtr VI_Empty varheap0
		// Define selector
		selectordef
		  = { sd_symb       = selector_ident    // Name with respect to a specific record (yes, a forward reference, see below)
			, sd_field      = selector_ident    // Name irrespective of record (hopefully the cycle isn't all strict...)
			, sd_type       = selector_type
			, sd_exi_vars   = []
			, sd_field_nr   = fieldindex
			, sd_type_index = dict_type_index   // Index of record type
			, sd_type_ptr   = selector_var
			, sd_pos        = selector_position // Position in input refers to member definition
			}
		// Allocate and store selector symbol
		(selectorsymbolptr, symbol_table1) = newSymbolPtr (STE_DictField selectordef) selectorindex symbol_table0
		// Create identifier for selector symbol
		selector_ident = {id_name = field_name, id_info = selectorsymbolptr}
		field = {fs_name = selector_ident, fs_var = selector_ident, fs_index = selectorindex}
		fields1 = {fields0 & [fieldindex] = field}
		seldefs1 = {seldefs0 & [selectorindex] = selectordef}

// Allocating a new symbol pointer
// This has to be done in two steps, because STE_DictField/STE_DictCons/STE_DictType strictly require their own pointer
//  ... solution: first write a dummy value into the heap, use that for the pointer, then overwrite the pointer
//  ... sometimes you have just too much strictness :-(
newSymbolPtr :: STE_Kind Index *SymbolTable -> (SymbolPtr, .SymbolTable)
newSymbolPtr kind index symboltable
# (symbolptr, symboltable) = newPtr EmptySymbolTableEntry symboltable
# symboltable = writePtr symbolptr {EmptySymbolTableEntry & ste_kind = kind, ste_index = index} symboltable
= (symbolptr, symboltable)

/* Copy a symbol type, creating fresh type variables and attribute variables,
 * There is an exception for type variables that were already bound in the environment
 * (the environment is the class context that we're building a dictionary record for)
 */
copy_symboltype ::
    .[TypeVar]   // Type variables bound in context
    SymbolType   // Symbol type to make fresh copy of
    *TypeHeaps   // Type heaps for doing the substitution
 -> ( Bool       // Result indicating success (?)
    , SymbolType // Fresh symbol type
	, .TypeHeaps // Used type heaps
	)

copy_symboltype boundtypevars st {th_vars,th_attrs}
# th_vars = foldr refresh_typevar th_vars (removeMembers st.st_vars boundtypevars)
# th_attrs = foldr refresh_attrvar th_attrs st.st_attr_vars
= substitute st {th_vars=th_vars,th_attrs=th_attrs}

refresh_typevar :: TypeVar *TypeVarHeap -> .TypeVarHeap
refresh_typevar tv tv_heap
# (new_tv_ptr,tv_heap) = newPtr TVI_Empty tv_heap
= writePtr tv.tv_info_ptr (TVI_Type (TV {tv & tv_info_ptr=new_tv_ptr})) tv_heap

refresh_attrvar :: AttributeVar *AttrVarHeap -> .AttrVarHeap
refresh_attrvar av av_heap
# (new_av_ptr,av_heap) = newPtr AVI_Empty av_heap
= writePtr av.av_info_ptr (AVI_Attr (TA_Var {av & av_info_ptr=new_av_ptr})) av_heap

instance substitute SymbolType
where
	substitute st=:{st_vars,st_args,st_result,st_context,st_attr_vars,st_attr_env} heaps
	# (ok_vars,st_vars,heaps) = substitute st_vars heaps
	  (ok_args,st_args,heaps) = substitute st_args heaps
	  (ok_result,st_result,heaps) = substitute st_result heaps
	  (ok_context,st_context,heaps) = substitute st_context heaps
	  (ok_attr_vars,st_attr_vars,heaps) = substitute st_attr_vars heaps
	  (ok_attr_env,st_attr_env,heaps) = substitute st_attr_env heaps
	# ok = ok_vars && ok_args && ok_result && ok_context && ok_attr_vars && ok_attr_env
	# st = { st
	       & st_vars      = st_vars
		   , st_args      = st_args
		   , st_result    = st_result
		   , st_context   = st_context
		   , st_attr_vars = st_attr_vars
		   , st_attr_env  = st_attr_env
		   }
	= (ok, st, heaps)

instance substitute ATypeVar
where
	substitute atv=:{atv_variable} heaps
	# (ok, atv_variable, heaps) = substitute atv_variable heaps
	= (ok, {atv & atv_variable = atv_variable}, heaps)

instance substitute TypeVar
where
	substitute tv=:{tv_info_ptr} heaps=:{th_vars}
		#! tv_info = sreadPtr tv_info_ptr th_vars
		= case tv_info of
			TVI_Type (TV new_tv)
				-> (True, new_tv, heaps)
			_
				-> (True, tv, heaps)

//foldrarray :: (Int a .b -> .b) .b .{#a} -> .b | uselect,usize a
foldrarray f i xs
= fold 0
  where fold j
        | j<sizexs
          = f j xs.[j] (fold (j+1))
        = i
		sizexs = size xs

foldrwithindex :: (Int a .b -> .b) .b .[a] -> .b
foldrwithindex f i xs = foldr (uncurry f) i (zip2 [0..] xs)


/*****************
*  OFFSET TABLE  *
*****************/

/* Temporary tables for efficiently determining the indices of dictionary field selectors

Dictionaries for classes are stored contiguously in the CheckedTypeDef array of
the corresponding DCL (ICL) in the same order as their classes, with the first
just after the last CheckedTypeDef already present.

	DICTTYPE (CLASS[i]) = TYPEDEF[#typedefs+i]
	#typedefs = number of CheckedTypeDefs before conversion

Dictionary constructors are stored analogously, but in the relevant ConsDef
array.

    DICTCONS (CLASS[i]) = CONSDEF[#consdefs+i]
	#consdefs = number of ConsDefs before conversion

Dictionary field selectors are stored contiguously, in the order of their
classes, and within each class first the member field selectors, then the
context field selectors. For efficiently finding the index of a field selector,
we use a temporary array to hold the offsets for each class.

    DICTSEL (CLASS[i].MEMBER[j]) = SELDEF[OFFSET[i].mem+j]
    DICTSEL (CLASS[i].CONTEXT[j]) = SELDEF[OFFSET[i].ctxt+j]
	OFFSET[0].mem = #seldefs
	OFFSET[i].ctxt = OFFSET[i].mem+#CLASS[i].MEMBER
	OFFSET[i+1].mem = OFFSET[i].ctxt+#CLASS[i].CONTEXT
	#seldefs = number of SelectorDefs before conversion

These numbers (including #typedefs and #consdefs) are kept for each module, be
they DCL or ICL.  Thus:

*/

unzip4
 :== foldr distrib4 ([], [], [], [])
	 where distrib4 x1234 xs1234
		   = ([x1:xs1], [x2:xs2], [x3:xs3], [x4:xs4])
	         where (x1, x2, x3, x4) = x1234
			       (xs1, xs2, xs3, xs4) = xs1234

// Resize an array by truncating it or appending elements
resizeArray :: e Int u:{#e} -> (.{#e}, v:{#e}) | createArray_u,uselect_u,update_u,usize_u e, [u<=v]
resizeArray defaultelement newsize oldarray0
= iFoldSt copy_elem 0 (min oldsize newsize) (createArray newsize defaultelement, oldarray1)
  where (oldsize, oldarray1) = usize oldarray0
        copy_elem i (dst, src0)
		= ({dst & [i] = elem}, src1)
		  where (elem, src1) = src0![i]

/*
 * Empty records for initially filling arrays
 */

emptyIdent name :== {reallyEmptyIdent&id_name=name}
emptyTypeDef rhs :== {td_name=reallyEmptyIdent,td_index=NoIndex,td_arity=emptyArity,td_args=[],td_attrs=[],td_context=[],td_rhs=rhs,td_attribute=TA_None,td_pos=NoPos,td_used_types=[]}

emptySelectorDef =: {sd_symb=reallyEmptyIdent,sd_field=reallyEmptyIdent,sd_type=emptySymbolType,sd_exi_vars=[],sd_field_nr=NoIndex,sd_type_index=NoIndex,sd_type_ptr=nilPtr,sd_pos=NoPos}
reallyEmptyIdent =: {id_name="",id_info=nilPtr}
emptySymbolType  =: {st_vars=[],st_args=[],st_arity=0,st_result=emptyAType,st_context=[],st_attr_vars=[],st_attr_env=[]}
emptyAType       =: {at_attribute=TA_None,at_annotation=AN_None,at_type=TE}
emptyFieldSymbol =: {fs_name=reallyEmptyIdent,fs_var=reallyEmptyIdent,fs_index=NoIndex}
emptyArity       =: -1
emptyTypeRhs     =: UnknownType
emptyConsDef     =: {cons_symb=reallyEmptyIdent,cons_type=emptySymbolType,cons_arg_vars=[],cons_priority=NoPrio,cons_index=NoIndex,cons_type_index=NoIndex,cons_exi_vars=[],cons_type_ptr=nilPtr,cons_pos=NoPos}
emptyCheckedTypeDef =: emptyTypeDef emptyTypeRhs
