implementation module analtypes

import StdEnv
import syntax, checksupport, checktypes, check, typesupport, utilities, analunitypes //, RWSDebug

/*
::	TypeGroup =
	{	tg_number	:: !Int
	,	tg_members	:: ![GlobalIndex]
	}
*/	

::	TypeGroups :== [[GlobalIndex]]

::	PartitioningInfo = 
	{	pi_marks			:: !.{# .{# Int}}
	,	pi_type_defs		:: !.{# .{# CheckedTypeDef}}
	,	pi_type_def_infos	:: !.TypeDefInfos
	,	pi_next_num 		:: !Int
	,	pi_next_group_num	:: !Int
	,	pi_groups			:: !TypeGroups
	,	pi_deps 			:: ![GlobalIndex]
	,	pi_error			:: !.ErrorAdmin
	}

cNotPartitionated	:== -1
cChecking 			:== -1

partionateAndExpandTypes :: !NumberSet !Index !*CommonDefs !*{#DclModule} !*TypeHeaps !*ErrorAdmin
	-> (!TypeGroups, !*{# CommonDefs}, !*TypeDefInfos, !*CommonDefs, !*{#DclModule}, !*TypeHeaps, !*ErrorAdmin)
partionateAndExpandTypes used_module_numbers main_dcl_module_index icl_common=:{com_type_defs,com_class_defs} dcl_modules type_heaps error
	#! nr_of_modules = size dcl_modules
//	#! nr_of_types_in_icl_mod = size com_type_defs - size com_class_defs
	#! n_exported_dictionaries = size dcl_modules.[main_dcl_module_index].dcl_common.com_class_defs
	#! index_of_first_not_exported_type_or_dictionary = size dcl_modules.[main_dcl_module_index].dcl_common.com_type_defs
	#! n_exported_icl_types = index_of_first_not_exported_type_or_dictionary - n_exported_dictionaries
	#! n_types_without_not_exported_dictionaries = size com_type_defs - (size com_class_defs - n_exported_dictionaries)
	# (dcl_type_defs, dcl_modules, new_type_defs, new_marks, type_def_infos)
		= copy_type_defs_and_create_marks_and_infos used_module_numbers main_dcl_module_index n_types_without_not_exported_dictionaries nr_of_modules (com_type_defs, dcl_modules)

	  pi = {pi_marks = new_marks, pi_type_defs = new_type_defs, pi_type_def_infos = type_def_infos, 
			pi_next_num = 0, pi_deps = [], pi_next_group_num = 0, pi_groups = [], pi_error = error }

	  {pi_error,pi_groups,pi_type_defs,pi_type_def_infos} = iFoldSt partionate_type_defs 0 nr_of_modules pi
		with
			partionate_type_defs mod_index pi=:{pi_marks}
				#! nr_of_typedefs_to_be_examined = size pi_marks.[mod_index]
				| mod_index == main_dcl_module_index
					# pi = iFoldSt (partitionate_type_def mod_index) 0 n_exported_icl_types pi
					= iFoldSt (partitionate_type_def mod_index) index_of_first_not_exported_type_or_dictionary nr_of_typedefs_to_be_examined pi
					= iFoldSt (partitionate_type_def mod_index) 0 nr_of_typedefs_to_be_examined pi
			where
				partitionate_type_def module_index type_index pi=:{pi_marks}
					# mark = pi_marks.[module_index, type_index]
					| mark == cNotPartitionated
						# (_, pi) = partitionateTypeDef {gi_module = module_index, gi_index = type_index} pi
						= pi
						= pi
	| not pi_error.ea_ok
		# (icl_type_defs, type_defs) = replace pi_type_defs main_dcl_module_index dcl_type_defs
		  (dcl_modules, common_defs) = update_modules_and_create_commondefs used_module_numbers type_defs nr_of_modules dcl_modules
		= (reverse pi_groups, common_defs, pi_type_def_infos, {icl_common & com_type_defs = icl_type_defs }, dcl_modules, type_heaps, pi_error)

		# (type_defs, dcl_type_defs, type_heaps, error)
				= foldSt (expand_synonym_types_of_group main_dcl_module_index) pi_groups (pi_type_defs, dcl_type_defs, type_heaps, pi_error)
		  (icl_type_defs, type_defs) = replace type_defs main_dcl_module_index dcl_type_defs
		  (dcl_modules, common_defs) = update_modules_and_create_commondefs used_module_numbers type_defs nr_of_modules dcl_modules
		= (reverse pi_groups, common_defs, pi_type_def_infos, {icl_common & com_type_defs = icl_type_defs}, dcl_modules, type_heaps, error)
where
	copy_type_defs_and_create_marks_and_infos used_module_numbers main_dcl_module_index n_types_without_not_exported_dictionaries nr_of_modules  (icl_type_defs, dcl_modules)
		# type_defs 		= { {}	\\ module_nr <- [1..nr_of_modules] }
		  marks				= { {}	\\ module_nr <- [1..nr_of_modules] }
	  	  type_def_infos	= { {}	\\ module_nr <- [1..nr_of_modules] }
		= iFoldSt (copy_type_def_and_create_marks_and_infos used_module_numbers main_dcl_module_index n_types_without_not_exported_dictionaries) 0 nr_of_modules
				(icl_type_defs, dcl_modules, type_defs, marks, type_def_infos)
	where
		copy_type_def_and_create_marks_and_infos used_module_numbers main_dcl_module_index n_types_without_not_exported_dictionaries module_index 
						(icl_type_defs, dcl_modules, type_defs, marks, type_def_infos)
			| inNumberSet module_index used_module_numbers
				# ({com_type_defs,com_class_defs}, dcl_modules) = dcl_modules![module_index].dcl_common
				| module_index == main_dcl_module_index
					= ( { type_def \\ type_def <-: com_type_defs }, dcl_modules, { type_defs & [module_index] = icl_type_defs },
							{ marks				& [module_index] = createArray n_types_without_not_exported_dictionaries cNotPartitionated },
							{ type_def_infos	& [module_index] = createArray n_types_without_not_exported_dictionaries EmptyTypeDefInfo })
					# nr_of_types = size com_type_defs - size com_class_defs
					= (	icl_type_defs, dcl_modules,  { type_defs & [module_index] = { type_def \\ type_def <-: com_type_defs }},
							{ marks				& [module_index] = createArray nr_of_types cNotPartitionated },
							{ type_def_infos	& [module_index] = createArray nr_of_types EmptyTypeDefInfo })
				= (icl_type_defs, dcl_modules, type_defs, marks,type_def_infos)

	expand_synonym_types_of_group main_dcl_module_index group_members (type_defs, main_dcl_type_defs, type_heaps, error)
		= foldSt (expand_synonym_type main_dcl_module_index) group_members (type_defs, main_dcl_type_defs, type_heaps, error)
	where		
		expand_synonym_type main_dcl_module_index gi=:{gi_module,gi_index} (type_defs, main_dcl_type_defs, type_heaps, error)
			# (td=:{td_rhs,td_attribute}, type_defs) = type_defs![gi_module, gi_index]
			= case td_rhs of
				SynType type
					# (opt_type, type_defs, type_heaps, error)
						= try_to_expand_synonym_type (newPosition td.td_name td.td_pos) type td_attribute (type_defs, type_heaps, error)
					-> case opt_type of
						Yes type
							# type_defs = { type_defs & [gi_module, gi_index] = { td & td_rhs = SynType type}}
							-> try_to_expand_synonym_type_in_main_dcl main_dcl_module_index gi (type_defs, main_dcl_type_defs, type_heaps, error)
						No
							-> (type_defs, main_dcl_type_defs, type_heaps, error)
				_
					-> (type_defs, main_dcl_type_defs, type_heaps, error)

		try_to_expand_synonym_type pos type=:{at_type = TA {type_index={glob_object,glob_module}} types} attribute (type_defs, type_heaps, error)
			= try_to_expand_synonym_type_for_TA glob_object glob_module types pos type attribute type_defs type_heaps error
		try_to_expand_synonym_type pos type=:{at_type = TAS {type_index={glob_object,glob_module}} types _} attribute (type_defs, type_heaps, error)
			= try_to_expand_synonym_type_for_TA glob_object glob_module types pos type attribute type_defs type_heaps error
		try_to_expand_synonym_type pos type attribute (type_defs, type_heaps, error)
			= (No, type_defs, type_heaps, error)

		try_to_expand_synonym_type_for_TA glob_object glob_module types pos type attribute type_defs type_heaps error
			# (used_td=:{td_rhs}, type_defs) = type_defs![glob_module, glob_object]
			= case td_rhs of
				SynType {at_type}
					# (ok, subst_rhs, type_heaps) = substituteType used_td.td_attribute attribute used_td.td_args types at_type type_heaps
					| ok
						-> (Yes {type & at_type = subst_rhs }, type_defs, type_heaps, error)
					  	# error = popErrorAdmin (typeSynonymError used_td.td_name "kind conflict in argument of type synonym" (pushErrorAdmin pos error))
						-> (No, type_defs, type_heaps, error)
				_
					-> (No, type_defs, type_heaps, error)

		try_to_expand_synonym_type_in_main_dcl main_dcl_module_index {gi_module,gi_index} (type_defs, main_dcl_type_defs, type_heaps, error)
			| main_dcl_module_index == main_dcl_module_index && gi_index < size main_dcl_type_defs
				# (td=:{td_rhs,td_attribute,td_name,td_pos}, main_dcl_type_defs) = main_dcl_type_defs![gi_index]
				= case td_rhs of
					SynType type
						# (opt_type, type_defs, type_heaps, error)
							= try_to_expand_synonym_type (newPosition td_name td_pos) type td_attribute (type_defs, type_heaps, error)
						-> case opt_type of
							Yes type
								-> (type_defs, { main_dcl_type_defs & [gi_index] = { td & td_rhs = SynType type}}, type_heaps, error)
							No
								-> (type_defs, main_dcl_type_defs, type_heaps, error)
					_
						-> (type_defs, main_dcl_type_defs, type_heaps, error)
				=  (type_defs, main_dcl_type_defs, type_heaps, error)

	update_modules_and_create_commondefs used_module_numbers type_defs nr_of_modules dcl_modules
		# (arbitrary_value_for_initializing, dcl_modules) = dcl_modules![0].dcl_common
		  initial_common_defs = createArray nr_of_modules arbitrary_value_for_initializing 
		= iFoldSt (copy_commondefs_and_adjust_type_defs used_module_numbers type_defs) 0 nr_of_modules (dcl_modules, initial_common_defs)
	where		  
		copy_commondefs_and_adjust_type_defs used_module_numbers type_defs module_index (dcl_modules, common_defs)
			| inNumberSet module_index used_module_numbers
				# (dcl_module=:{dcl_common}, dcl_modules) = dcl_modules![module_index]
				  dcl_common = { dcl_common & com_type_defs = type_defs.[module_index]}
				= ({ dcl_modules & [module_index] = { dcl_module & dcl_common = dcl_common }}, { common_defs & [module_index] = dcl_common })
				= (dcl_modules, common_defs)
//				# (dcl_common, dcl_modules) = dcl_modules![module_index].dcl_common
//				= (dcl_modules, { common_defs & [module_index] = dcl_common })
//					---> ("update_modules_and_create_commondefs", module_index)

		
partitionateTypeDef gi=:{gi_module,gi_index} pi=:{pi_type_defs}
	# ({td_name,td_pos,td_used_types}, pi) = pi!pi_type_defs.[gi_module].[gi_index]
	  pi = push_on_dep_stack gi pi
	  (min_dep, pi) = foldSt visit_type td_used_types (cMAXINT, pi)
	= try_to_close_group gi min_dep pi
where
	visit_type gi=:{gi_module,gi_index} (min_dep, pi=:{pi_marks})
		#! mark = pi_marks.[gi_module].[gi_index]
		| mark == cNotPartitionated
			# (ldep, pi) = partitionateTypeDef gi pi
			= (min min_dep ldep, pi)
			= (min min_dep mark, pi)

	push_on_dep_stack type_index=:{gi_module,gi_index} pi=:{pi_deps,pi_marks,pi_next_num}
		= { pi & pi_deps = [type_index : pi_deps], pi_marks = { pi_marks & [gi_module].[gi_index] = pi_next_num }, pi_next_num = inc pi_next_num }

	try_to_close_group this_type=:{gi_module,gi_index} ldep pi=:{pi_deps,pi_marks,pi_next_group_num,pi_groups,pi_type_defs,pi_error,pi_type_def_infos}
		#! my_mark = pi_marks.[gi_module].[gi_index]
		| (ldep == cMAXINT || ldep == my_mark)
			# (pi_deps, group_members)	= close_group this_type pi_deps []
			  (reorganised_group_members, pi_marks, pi_type_defs, pi_error)	= check_cyclic_type_defs group_members [] pi_marks pi_type_defs pi_error
			  pi_type_def_infos = update_type_def_infos pi_next_group_num reorganised_group_members group_members pi_type_def_infos
			= (cMAXINT, { pi &	pi_marks = pi_marks, pi_deps = pi_deps, pi_next_group_num = inc pi_next_group_num, pi_error = pi_error,
								pi_type_defs = pi_type_defs, pi_type_def_infos = pi_type_def_infos,
								pi_groups =  [reorganised_group_members : pi_groups ]})
//								---> ("try_to_close_group", reorganised_group_members, group_members)
			= (min my_mark ldep, pi)
	where
		close_group first_type [td : tds] group
			| first_type == td
				= (tds, [td : group])
				= close_group first_type tds [td : group]

	check_cyclic_type_defs tds group marks type_defs error
		= foldSt check_cyclic_type_def tds (group, marks, type_defs, error)
	where
		check_cyclic_type_def td=:{gi_module,gi_index} (group, marks, typedefs, error)
			# (mark, marks) = marks![gi_module,gi_index]
			# ({td_name,td_pos,td_used_types,td_rhs}, typedefs) = typedefs![gi_module].[gi_index]
			| mark == cChecking
				= (group, marks, typedefs, typeSynonymError td_name "cyclic dependency between type synonyms" error)
			| mark < cMAXINT
				| is_synonym_type td_rhs
					# marks = { marks & [gi_module,gi_index] = cChecking }
					  error = pushErrorAdmin (newPosition td_name td_pos) error
					  (group, marks, typedefs, error) = check_cyclic_type_defs td_used_types [td : group] marks typedefs error
					  error = popErrorAdmin error
					= (group, { marks & [gi_module,gi_index] = cMAXINT }, typedefs, error)
					= ([td : group], { marks & [gi_module,gi_index] = cMAXINT }, typedefs, error)
				= (group, marks, typedefs, error)

		is_synonym_type (SynType _)	= True
		is_synonym_type td_rhs		= False

	update_type_def_infos group_nr group_members tds type_def_infos
		# (_, type_def_infos) = foldSt (update_type_def_info group_nr group_members) tds (0, type_def_infos)
		= type_def_infos
	where
		update_type_def_info group_nr group_members {gi_module,gi_index} (index_in_group, type_def_infos)
			# (info, type_def_infos) = type_def_infos![gi_module,gi_index]
			= (inc index_in_group,
				{ type_def_infos & [gi_module,gi_index] = { info & tdi_group_nr = group_nr, tdi_index_in_group = index_in_group, tdi_group = group_members}})
		

typeSynonymError type_symb msg error
	= checkError type_symb msg error
	
::	UnifyKindsInfo = 
	{	uki_kind_heap	::!.KindHeap
	,	uki_error		::!.ErrorAdmin
	}
	
AS_NotChecked :== -1

kindError kind1 kind2 error
	= checkError "conflicting kinds: " (toString kind1 +++ " and " +++ toString kind2) error

skipIndirections (KI_Var kind_info_ptr) kind_heap
	# (kind, kind_heap) = readPtr kind_info_ptr kind_heap
	= skip_indirections kind_info_ptr kind kind_heap
where
	skip_indirections this_info_ptr kind=:(KI_Var kind_info_ptr) kind_heap
		| this_info_ptr == kind_info_ptr
			= (kind, kind_heap)
			# (kind, kind_heap) = readPtr kind_info_ptr kind_heap
			= skip_indirections kind_info_ptr kind kind_heap
	skip_indirections this_info_ptr kind kind_heap
		= (kind, kind_heap)
skipIndirections kind kind_heap
	= (kind, kind_heap)

unifyKinds  :: !KindInfo !KindInfo !*UnifyKindsInfo -> *UnifyKindsInfo
unifyKinds kind1 kind2 uni_info=:{uki_kind_heap}
	# (kind1, uki_kind_heap) = skipIndirections kind1 uki_kind_heap
	# (kind2, uki_kind_heap) = skipIndirections kind2 uki_kind_heap
	= unify_kinds kind1 kind2 { uni_info & uki_kind_heap = uki_kind_heap }
where	
	unify_kinds kind1=:(KI_Var info_ptr1) kind2 uni_info
		= case kind2 of
			KI_Var info_ptr2
				| info_ptr1 == info_ptr2
					-> uni_info
					-> { uni_info & uki_kind_heap = uni_info.uki_kind_heap <:= (info_ptr1, kind2) }
			_
				# (found, uki_kind_heap) = contains_kind_ptr info_ptr1 kind2 uni_info.uki_kind_heap
				| found
					-> { uni_info & uki_kind_heap = uki_kind_heap, uki_error = kindError kind1 kind2 uni_info.uki_error }
					-> { uni_info & uki_kind_heap = uki_kind_heap <:= (info_ptr1, kind2)  }
		where
			contains_kind_ptr info_ptr (KI_Arrow kind1 kind2) kind_heap				
				# (kind1, kind_heap) = skipIndirections kind1 kind_heap
				# (found, kind_heap) = contains_kind_ptr info_ptr kind1 kind_heap 		
				| found
					= (True, kind_heap)
					# (kind2, kind_heap) = skipIndirections kind2 kind_heap
					= contains_kind_ptr info_ptr kind2 kind_heap						
			contains_kind_ptr info_ptr (KI_Var kind_info_ptr) kind_heap
				= (info_ptr == kind_info_ptr, kind_heap)
			contains_kind_ptr info_ptr (KI_Const) kind_heap
				= (False, kind_heap)

	unify_kinds kind k1=:(KI_Var info_ptr1) uni_info
		= unify_kinds k1 kind  uni_info
	unify_kinds kind1=:(KI_Arrow x1 y1) kind2=:(KI_Arrow x2 y2) uni_info
		= unifyKinds x1 x2 (unifyKinds y1 y2 uni_info)
	unify_kinds KI_Const KI_Const uni_info
		= uni_info
	unify_kinds kind1 kind2 uni_info=:{uki_error}
		= { uni_info & uki_error = kindError kind1 kind2 uki_error }


kindToKindInfo (KindVar info_ptr)
	= KI_Var info_ptr
kindToKindInfo KindConst
	= KI_Const
kindToKindInfo (KindArrow ks)
	= kindArrowToKindInfo ks

kindArrowToKindInfo []
	= KI_Const
kindArrowToKindInfo [k : ks]
	= KI_Arrow (kindToKindInfo k) (kindArrowToKindInfo ks)

kindInfoToKind kind_info kind_heap
	# (kind_info, kind_heap) = skipIndirections kind_info kind_heap
	= case kind_info of
		KI_Arrow x y
			# (x, kind_heap) = kindInfoToKind x kind_heap
			# (y, kind_heap) = kindInfoToKind y kind_heap						
			-> case y of
				KindArrow ks
					-> (KindArrow [x:ks], kind_heap)
				_ 
					-> (KindArrow [x], kind_heap)							
		_
			-> (KindConst, kind_heap)

::	VarBind =
	{	vb_var 	::	!KindInfoPtr
	,	vb_vars	::	![KindInfoPtr]
	}

::	Conditions =
	{	con_top_var_binds	:: ![KindInfoPtr]
	,	con_var_binds		:: ![VarBind]
	}
	
::	AnalyseState =
	{	as_td_infos			:: !.TypeDefInfos
	,	as_type_var_heap	:: !.TypeVarHeap
	,	as_kind_heap		:: !.KindHeap
	,	as_error			:: !.ErrorAdmin
	}

::	TypeProperties	:== BITVECT

combineTypeProperties prop1 prop2 :== (combineHyperstrictness prop1 prop2) bitor (combineCoercionProperties prop1 prop2)

condCombineTypeProperties has_root_attr prop1 prop2
	| has_root_attr
		= combineTypeProperties prop1 prop2
		= combineTypeProperties prop1 (prop2 bitand (bitnot cIsNonCoercible))

combineCoercionProperties prop1 prop2	:== (prop1 bitor prop2) bitand cIsNonCoercible
combineHyperstrictness prop1 prop2		:== (prop1 bitand prop2) bitand cIsHyperStrict

class analTypes type :: !Bool !{#CommonDefs} ![KindInfoPtr] !type !(!Conditions, !*AnalyseState)
	-> (!KindInfo, !TypeProperties, !(!Conditions, !*AnalyseState))

freshKindVar kind_heap
	# (kind_info_ptr, kind_heap) = newPtr KI_Const kind_heap
	# kind_var = KI_Var kind_info_ptr
	= (kind_var, kind_heap <:= (kind_info_ptr, kind_var))

instance analTypes AType
where
	analTypes _ modules form_tvs atype=:{at_attribute,at_type} conds_as
		= analTypes (has_root_attr at_attribute) modules form_tvs at_type conds_as
	where
		has_root_attr (TA_RootVar _)	= True
		has_root_attr _ 				= False
		
instance analTypes TypeVar
where
	analTypes has_root_attr modules form_tvs {tv_info_ptr}  (conds=:{con_var_binds}, as=:{as_type_var_heap, as_kind_heap})
		# (TVI_TypeKind kind_info_ptr, as_type_var_heap) = readPtr tv_info_ptr as_type_var_heap
		  (kind_info, as_kind_heap) = readPtr kind_info_ptr as_kind_heap
		  (kind_info, as_kind_heap) = skipIndirections kind_info as_kind_heap
		| isEmpty form_tvs
			= (kind_info, cIsHyperStrict, (conds, { as & as_type_var_heap = as_type_var_heap, as_kind_heap = as_kind_heap }))
			= (kind_info, cIsHyperStrict, ({ conds & con_var_binds = [{vb_var = kind_info_ptr, vb_vars = form_tvs } : con_var_binds] },
						 { as & as_type_var_heap = as_type_var_heap, as_kind_heap = as_kind_heap }))

analTypes_for_TA :: Ident Int Int Int [AType] !Bool !{#CommonDefs} ![KindInfoPtr] !Conditions !*AnalyseState
	-> (!KindInfo, !TypeProperties, !(!Conditions, !*AnalyseState))
analTypes_for_TA type_name glob_module glob_object type_arity types has_root_attr modules form_tvs conds as
	# form_type_arity = modules.[glob_module].com_type_defs.[glob_object].td_arity
	  ({tdi_kinds, tdi_properties}, as) = as!as_td_infos.[glob_module].[glob_object]
	| type_arity <= form_type_arity
		# kind = kindArrowToKindInfo (drop type_arity tdi_kinds)
		| tdi_properties bitand cIsAnalysed == 0
			# (type_properties, conds_as) = anal_types_of_rec_type_cons modules form_tvs types tdi_kinds (conds, as)
			= (kind, type_properties, conds_as)
			# (type_properties, conds_as) = anal_types_of_type_cons modules form_tvs types tdi_kinds (conds, as)
			= (kind, type_properties, conds_as)
		= (KI_Const, tdi_properties, (conds, { as & as_error = checkError type_name type_appl_error as.as_error }))
where
	anal_types_of_rec_type_cons modules form_tvs [] _ conds_as
		= (cIsHyperStrict, conds_as)
	anal_types_of_rec_type_cons modules form_tvs [type : types] [(KindVar kind_info_ptr) : tvs] conds_as
		# (type_kind, type_props, (conds, as=:{as_kind_heap,as_error})) = analTypes has_root_attr modules [ kind_info_ptr : form_tvs ] type conds_as
		  (kind, as_kind_heap) = readPtr kind_info_ptr as_kind_heap
		  {uki_kind_heap, uki_error} = unifyKinds type_kind kind {uki_kind_heap = as_kind_heap, uki_error = as_error}
		| is_type_var type
			# (other_type_props, conds_as) = anal_types_of_rec_type_cons modules form_tvs types tvs
					(conds, { as & as_kind_heap = uki_kind_heap, as_error = uki_error })
			= (combineTypeProperties type_props other_type_props, conds_as)
			# (other_type_props, conds_as) =  anal_types_of_rec_type_cons modules form_tvs types tvs
					({ conds & con_top_var_binds = [kind_info_ptr : conds.con_top_var_binds]}, { as & as_kind_heap = uki_kind_heap, as_error = uki_error })
			= (combineTypeProperties type_props other_type_props, conds_as)
	where
		is_type_var {at_type = TV _}
			= True
		is_type_var _
			= False
		
	anal_types_of_type_cons modules form_tvs [] _ conds_as
		= (cIsHyperStrict, conds_as)
	anal_types_of_type_cons modules form_tvs [type : types] [tk : tks] conds_as
		# (type_kind, type_props, (conds, as=:{as_kind_heap,as_error})) = analTypes has_root_attr modules form_tvs type conds_as
		  {uki_kind_heap, uki_error} = unifyKinds type_kind (kindToKindInfo tk) {uki_kind_heap = as_kind_heap, uki_error = as_error}
		  as = { as & as_kind_heap = uki_kind_heap, as_error = uki_error }
		  (other_type_props, conds_as) =  anal_types_of_type_cons modules form_tvs types tks (conds, as)
		= (combineTypeProperties type_props other_type_props, conds_as)
	anal_types_of_type_cons modules form_tvs types tks conds_as
		= abort ("anal_types_of_type_cons (analtypes.icl)" ---> (types, tks))

instance analTypes Type
where
	analTypes has_root_attr modules form_tvs (TV tv) conds_as
		= analTypes has_root_attr modules form_tvs tv conds_as
	analTypes has_root_attr modules form_tvs type=:(TA {type_name,type_index={glob_module,glob_object},type_arity} types) (conds, as)
		= analTypes_for_TA type_name glob_module glob_object type_arity types has_root_attr modules form_tvs conds as
	analTypes has_root_attr modules form_tvs type=:(TAS {type_name,type_index={glob_module,glob_object},type_arity} types _) (conds, as)
		= analTypes_for_TA type_name glob_module glob_object type_arity types has_root_attr modules form_tvs conds as
	analTypes has_root_attr modules form_tvs (arg_type --> res_type) conds_as
		# (arg_kind, arg_type_props, conds_as) = analTypes has_root_attr modules form_tvs arg_type conds_as
		  (res_kind, res_type_props, (conds, as=:{as_kind_heap,as_error})) = analTypes has_root_attr modules form_tvs res_type conds_as
		  {uki_kind_heap, uki_error} = unifyKinds res_kind KI_Const (unifyKinds arg_kind KI_Const {uki_kind_heap = as_kind_heap, uki_error = as_error})
		  type_props = if	has_root_attr
							(combineCoercionProperties arg_type_props res_type_props bitor cIsNonCoercible)
							(combineCoercionProperties arg_type_props res_type_props)
		= (KI_Const, type_props, (conds, {as & as_kind_heap = uki_kind_heap, as_error = uki_error }))

// AA..
	analTypes has_root_attr modules form_tvs TArrow conds_as
		# type_props = if has_root_attr
			(cIsHyperStrict bitor cIsNonCoercible) 
			cIsHyperStrict
		= (KI_Arrow KI_Const (KI_Arrow KI_Const KI_Const), type_props, conds_as) 
		
	analTypes has_root_attr modules form_tvs (TArrow1 arg_type) conds_as
		# (arg_kind, arg_type_props, conds_as) = analTypes has_root_attr modules form_tvs arg_type conds_as
		# (conds, as=:{as_kind_heap,as_error}) = conds_as
		# type_props = if has_root_attr 
			(arg_type_props bitor cIsNonCoercible) 
			arg_type_props
		# {uki_kind_heap, uki_error} = unifyKinds arg_kind KI_Const {uki_kind_heap = as_kind_heap, uki_error = as_error}	
		= (KI_Arrow KI_Const KI_Const, type_props, (conds, {as & as_kind_heap = uki_kind_heap, as_error = uki_error}))
// ..AA

	analTypes has_root_attr modules form_tvs (CV tv :@: types) conds_as
		# (type_kind, cv_props, (conds, as)) = analTypes has_root_attr modules form_tvs tv conds_as
		  (kind_var, as_kind_heap) = freshKindVar as.as_kind_heap	 
		  (type_kinds, is_non_coercible, (conds, as=:{as_kind_heap,as_error}))
		  		= check_type_list kind_var modules form_tvs types (conds, { as & as_kind_heap = as_kind_heap })
		  {uki_kind_heap, uki_error} = unifyKinds type_kind type_kinds {uki_kind_heap = as_kind_heap, uki_error = as_error}
		  type_props = if (is_non_coercible || has_root_attr) cIsNonCoercible (cv_props bitand cIsNonCoercible)
		= (kind_var, type_props, (conds, {as & as_kind_heap = uki_kind_heap, as_error = uki_error }))

	where
		check_type_list kind_var modules form_tvs [] conds_as
			= (kind_var, False, conds_as)
		check_type_list kind_var modules form_tvs [type : types] conds_as
			# (tk, type_props, conds_as) = analTypes has_root_attr modules form_tvs type conds_as
//			  {uki_kind_heap, uki_error} = unifyKinds tk KI_Const {uki_kind_heap = as_kind_heap, uki_error = as_error}
			  (tks, is_non_coercible, conds_as) = check_type_list kind_var modules form_tvs types conds_as
			= (KI_Arrow tk tks, is_non_coercible || (type_props bitand cIsNonCoercible <> 0), conds_as)
	analTypes has_root_attr modules form_tvs (TFA vars type) (conds, as=:{as_type_var_heap,as_kind_heap})
		# (as_type_var_heap, as_kind_heap) = new_local_kind_variables vars as_type_var_heap as_kind_heap
		= analTypes has_root_attr modules form_tvs type (conds, { as & as_type_var_heap = as_type_var_heap, as_kind_heap = as_kind_heap})
	where
		new_local_kind_variables :: [ATypeVar] !*TypeVarHeap !*KindHeap -> (!*TypeVarHeap,!*KindHeap)
		new_local_kind_variables type_vars type_var_heap as_kind_heap
			= foldSt new_kind type_vars (type_var_heap, as_kind_heap)
		where
			new_kind :: !ATypeVar !(!*TypeVarHeap,!*KindHeap) -> (!*TypeVarHeap,!*KindHeap)
			new_kind {atv_variable={tv_info_ptr}} (type_var_heap, kind_heap)
				# (kind_info_ptr, kind_heap) = newPtr KI_Const kind_heap
				= (	type_var_heap <:= (tv_info_ptr, TVI_TypeKind kind_info_ptr), kind_heap <:= (kind_info_ptr, KI_Var kind_info_ptr))
	analTypes has_root_attr modules form_tvs type conds_as
		= (KI_Const, cIsHyperStrict, conds_as)


cDummyBool :== False

analTypesOfConstructor modules cons_defs [{ds_index}:conses] (conds, as=:{as_type_var_heap,as_kind_heap})
	# {cons_exi_vars,cons_type} = cons_defs.[ds_index ]
	  (coercible, as_type_var_heap, as_kind_heap) = new_local_kind_variables cons_exi_vars (as_type_var_heap, as_kind_heap)
	  (cons_properties, conds_as) = anal_types_of_cons modules cons_type.st_args cons_type.st_args_strictness 0
			(conds, { as & as_type_var_heap = as_type_var_heap, as_kind_heap = as_kind_heap })
	  (other_properties, conds_as) = analTypesOfConstructor modules cons_defs conses conds_as
	  properties = combineTypeProperties cons_properties other_properties
	= (if coercible properties (properties bitor cIsNonCoercible), conds_as)
where
	new_local_kind_variables :: [ATypeVar] !(!*TypeVarHeap,!*KindHeap) -> (!Bool,!*TypeVarHeap,!*KindHeap)
	new_local_kind_variables td_args (type_var_heap, as_kind_heap)
		= foldSt new_kind td_args (True, type_var_heap, as_kind_heap)
	where
		new_kind :: !ATypeVar !(!Bool,!*TypeVarHeap,!*KindHeap) -> (!Bool,!*TypeVarHeap,!*KindHeap)
		new_kind {atv_variable={tv_info_ptr},atv_attribute} (coercible, type_var_heap, kind_heap)
			# (kind_info_ptr, kind_heap) = newPtr KI_Const kind_heap
			= (coercible && is_not_a_variable atv_attribute, type_var_heap <:= (tv_info_ptr, TVI_TypeKind kind_info_ptr),
				kind_heap <:= (kind_info_ptr, KI_Var kind_info_ptr))

		is_not_a_variable (TA_RootVar var)	= False
		is_not_a_variable attr				= True
			
	anal_types_of_cons modules [] args_strictness strictness_index conds_as
		= (cIsHyperStrict, conds_as)
	anal_types_of_cons modules [type : types] args_strictness strictness_index conds_as
		# (other_type_props, conds_as) = anal_types_of_cons modules types args_strictness (strictness_index+1) conds_as
		  (type_kind, cv_props, (conds, as=:{as_kind_heap, as_error})) = analTypes cDummyBool modules [] type conds_as
		  {uki_kind_heap, uki_error} = unifyKinds type_kind KI_Const {uki_kind_heap = as_kind_heap, uki_error = as_error}
		  cons_props = if (arg_is_strict strictness_index args_strictness)
							(combineTypeProperties cv_props other_type_props)
							(combineCoercionProperties cv_props other_type_props)
		= (cons_props, (conds, { as & as_kind_heap = uki_kind_heap, as_error = uki_error }))

analTypesOfConstructor _ _ [] conds_as
	= (cIsHyperStrict, conds_as)

isATopConsVar cv		:== cv < 0
encodeTopConsVar cv		:== dec (~cv)
decodeTopConsVar cv		:== ~(inc cv)

emptyIdent name :== { id_name = name, id_info = nilPtr }

newKindVariables td_args (type_var_heap, as_kind_heap)
	= mapSt new_kind td_args (type_var_heap, as_kind_heap)
where
	new_kind :: ATypeVar *(*Heap TypeVarInfo,*Heap KindInfo) -> (!.TypeKind,!(!.Heap TypeVarInfo,!.Heap KindInfo));
	new_kind {atv_variable={tv_info_ptr}} (type_var_heap, kind_heap)
		# (kind_info_ptr, kind_heap) = newPtr KI_Const kind_heap
		= (KindVar kind_info_ptr, (type_var_heap <:= (tv_info_ptr, TVI_TypeKind kind_info_ptr), kind_heap <:= (kind_info_ptr, KI_Var kind_info_ptr)))

analyseTypeDefs :: !{#CommonDefs} !TypeGroups !*TypeDefInfos !*TypeVarHeap !*ErrorAdmin -> (!*TypeDefInfos, !*TypeVarHeap, !*ErrorAdmin)
analyseTypeDefs modules groups type_def_infos type_var_heap error
	# as = { as_kind_heap = newHeap, as_type_var_heap = type_var_heap, as_td_infos = type_def_infos, as_error = error }
	  {as_td_infos,as_type_var_heap,as_error} = foldSt (anal_type_defs_in_group modules) groups as
	= check_left_root_attribution_of_typedefs modules groups as_td_infos as_type_var_heap as_error
where
	anal_type_defs_in_group modules group as=:{as_td_infos,as_type_var_heap,as_kind_heap}
		# (is_abstract_type, as_td_infos, as_type_var_heap, as_kind_heap)
			= foldSt (init_type_def_infos modules) group (False, as_td_infos, as_type_var_heap, as_kind_heap)
		  as = { as & as_td_infos = as_td_infos, as_type_var_heap = as_type_var_heap, as_kind_heap = as_kind_heap }
		| is_abstract_type
			= as
			# (type_properties, conds, as) = foldSt (anal_type_def modules) group (cIsHyperStrict, { con_top_var_binds = [], con_var_binds = [] }, as)
			  (kinds_in_group, (as_kind_heap, as_td_infos))	= mapSt determine_kinds group (as.as_kind_heap, as.as_td_infos)
			  as_kind_heap									= unify_var_binds conds.con_var_binds as_kind_heap
			  (normalized_top_vars, (kind_var_store, as_kind_heap)) = normalize_top_vars conds.con_top_var_binds 0 as_kind_heap
			  (as_kind_heap, as_td_infos) = update_type_def_infos type_properties normalized_top_vars group kinds_in_group  kind_var_store as_kind_heap as_td_infos
			= { as & as_kind_heap = as_kind_heap, as_td_infos = as_td_infos }

	init_type_def_infos modules gi=:{gi_module,gi_index} (is_abstract_type, type_def_infos, as_type_var_heap, kind_heap)
		# {td_args,td_rhs} = modules.[gi_module].com_type_defs.[gi_index]
		= case td_rhs of
			AbstractType properties
				# (tdi, type_def_infos) = type_def_infos![gi_module,gi_index]
				  new_tdi = { tdi &	tdi_kinds = [ KindConst \\ _ <- td_args ],
				  					tdi_group_vars = [ i \\ _ <- td_args & i <- [0..]],
				  					tdi_properties = properties bitor cIsAnalysed  }
				-> (True, { type_def_infos & [gi_module].[gi_index] = new_tdi}, as_type_var_heap, kind_heap)
			AbstractSynType properties _
				# (tdi, type_def_infos) = type_def_infos![gi_module,gi_index]
				  new_tdi = { tdi &	tdi_kinds = [ KindConst \\ _ <- td_args ],
				  					tdi_group_vars = [ i \\ _ <- td_args & i <- [0..]],
				  					tdi_properties = properties bitor cIsAnalysed  }
				-> (True, { type_def_infos & [gi_module].[gi_index] = new_tdi}, as_type_var_heap, kind_heap)
			_
				# (tdi_kinds, (as_type_var_heap, kind_heap)) = newKindVariables td_args (as_type_var_heap, kind_heap)
				-> (is_abstract_type, { type_def_infos & [gi_module].[gi_index].tdi_kinds = tdi_kinds }, as_type_var_heap, kind_heap)

	anal_type_def modules gi=:{gi_module,gi_index} (group_properties, conds, as=:{as_error})
		# {com_type_defs,com_cons_defs} = modules.[gi_module]
		  {td_name,td_pos,td_args,td_rhs} = com_type_defs.[gi_index]
		  as_error = pushErrorAdmin (newPosition td_name td_pos) as_error
		  (type_properties, (conds, as)) = anal_rhs_of_type_def modules com_cons_defs td_rhs (conds, { as & as_error = as_error })
		= (combineTypeProperties group_properties type_properties, conds, {as & as_error = popErrorAdmin as.as_error })
	where
		anal_rhs_of_type_def modules com_cons_defs (AlgType conses) conds_as
			= analTypesOfConstructor modules com_cons_defs conses conds_as
		anal_rhs_of_type_def modules com_cons_defs (RecordType {rt_constructor}) conds_as
			= analTypesOfConstructor modules com_cons_defs [rt_constructor] conds_as
		anal_rhs_of_type_def modules _ (SynType type) conds_as
			# (type_kind, cv_props, (conds, as=:{as_kind_heap, as_error})) = analTypes cDummyBool modules [] type conds_as
			  {uki_kind_heap, uki_error} = unifyKinds type_kind KI_Const {uki_kind_heap = as_kind_heap, uki_error = as_error}
			= (cv_props, (conds, { as & as_kind_heap = as_kind_heap, as_error = as_error }))

	determine_kinds {gi_module,gi_index} (kind_heap, td_infos)
		# (td_info=:{tdi_kinds}, td_infos) = td_infos![gi_module,gi_index]
		  (new_kinds, kind_heap) = mapSt retrieve_kind tdi_kinds kind_heap
		= (new_kinds, (kind_heap, td_infos))
	where
		retrieve_kind (KindVar kind_info_ptr) kind_heap
			# (kind_info, kind_heap) = readPtr kind_info_ptr kind_heap
			= kindInfoToKind kind_info kind_heap

	unify_var_binds :: ![VarBind] !*KindHeap -> *KindHeap
	unify_var_binds binds kind_heap
		= foldr unify_var_bind kind_heap binds

	unify_var_bind :: !VarBind !*KindHeap -> *KindHeap
	unify_var_bind {vb_var, vb_vars} kind_heap
		# (kind_info, kind_heap) = readPtr vb_var kind_heap
		# (vb_var, kind_heap) = determine_var_bind vb_var kind_info kind_heap
		= redirect_vars vb_var vb_vars kind_heap
	where	
		redirect_vars kind_info_ptr [var_info_ptr : var_info_ptrs] kind_heap
			# (kind_info, kind_heap) = readPtr var_info_ptr kind_heap
			# (var_info_ptr, kind_heap) = determine_var_bind var_info_ptr kind_info kind_heap
			| kind_info_ptr == var_info_ptr
				= redirect_vars kind_info_ptr var_info_ptrs kind_heap
				= redirect_vars kind_info_ptr var_info_ptrs (writePtr kind_info_ptr (KI_VarBind var_info_ptr) kind_heap)
		redirect_vars kind_info_ptr [] kind_heap
			= kind_heap
			
		determine_var_bind _ (KI_VarBind kind_info_ptr) kind_heap
			# (kind_info, kind_heap) = readPtr kind_info_ptr kind_heap
			= determine_var_bind kind_info_ptr  kind_info kind_heap
		determine_var_bind kind_info_ptr kind_info kind_heap
			= (kind_info_ptr, kind_heap)

	nomalize_var :: !KindInfoPtr !KindInfo !(!Int,!*KindHeap) -> (!Int,!(!Int,!*KindHeap))
	nomalize_var orig_kind_info (KI_VarBind kind_info_ptr) (kind_store, kind_heap)
		# (kind_info, kind_heap) = readPtr kind_info_ptr kind_heap
		= nomalize_var kind_info_ptr kind_info (kind_store, kind_heap)
	nomalize_var kind_info_ptr (KI_NormVar var_number) (kind_store, kind_heap)
		= (var_number, (kind_store, kind_heap))
	nomalize_var kind_info_ptr kind (kind_store, kind_heap)
		= (kind_store, (inc kind_store, writePtr kind_info_ptr (KI_NormVar kind_store) kind_heap))
	
	normalize_top_vars top_vars kind_store kind_heap
		= mapSt normalize_top_var top_vars (kind_store, kind_heap)
	where
		normalize_top_var :: !KindInfoPtr !(!Int,!*KindHeap) -> (!Int,!(!Int,!*KindHeap))
		normalize_top_var kind_info_ptr (kind_store, kind_heap)
			# (kind_info, kind_heap) = readPtr kind_info_ptr kind_heap
			= nomalize_var kind_info_ptr kind_info (kind_store, kind_heap)
			
	update_type_def_infos type_properties top_vars group updated_kinds_of_group kind_store kind_heap td_infos
		# (_, as_kind_heap, as_td_infos) = fold2St (update_type_def_info (type_properties bitor cIsAnalysed) top_vars) group updated_kinds_of_group
				(kind_store, kind_heap, td_infos)
		= (as_kind_heap, as_td_infos)
	where
		update_type_def_info type_properties top_vars {gi_module,gi_index} updated_kinds (kind_store, kind_heap, td_infos)
			# (td_info=:{tdi_kinds}, td_infos) = td_infos![gi_module].[gi_index]
			# (group_vars, cons_vars, kind_store, kind_heap) = determine_type_def_info tdi_kinds updated_kinds top_vars kind_store kind_heap
			= (kind_store, kind_heap, { td_infos & [gi_module,gi_index] =
					{td_info & tdi_properties = type_properties, tdi_kinds = updated_kinds, tdi_group_vars = group_vars, tdi_cons_vars = cons_vars }})

		determine_type_def_info [ KindVar kind_info_ptr : kind_vars ] [ kind : kinds ] top_vars kind_store kind_heap
			#! kind_info = sreadPtr kind_info_ptr kind_heap
			# (var_number, (kind_store, kind_heap)) = nomalize_var kind_info_ptr kind_info (kind_store, kind_heap)
			  (group_vars, cons_vars, kind_store, kind_heap) = determine_type_def_info kind_vars kinds top_vars kind_store kind_heap
			= case kind of
				KindArrow _
					| is_a_top_var var_number top_vars
						-> ([ var_number : group_vars ], [ encodeTopConsVar var_number : cons_vars ], kind_store, kind_heap)
						-> ([ var_number : group_vars ], [ var_number : cons_vars ], kind_store, kind_heap)
				_
					-> ([ var_number : group_vars ], cons_vars, kind_store, kind_heap)
		determine_type_def_info [] [] top_vars kind_store kind_heap
			= ([], [], kind_store, kind_heap)
				
		is_a_top_var var_number [ top_var_number : top_var_numbers]
			= var_number == top_var_number || is_a_top_var var_number top_var_numbers
		is_a_top_var var_number []
			= False

	check_left_root_attribution_of_typedefs modules groups type_def_infos type_var_heap error
		# (type_def_infos, type_var_heap, error) = foldSt (foldSt (checkLeftRootAttributionOfTypeDef modules)) groups (type_def_infos, type_var_heap, error)
		= (type_def_infos, type_var_heap, error)

cDummyConditions		=: { con_top_var_binds = [], con_var_binds = []}

determineKind modules type as
	# (type_kind, _, (_,as)) = analTypes cDummyBool modules [] type (cDummyConditions, as)
	= (type_kind, as)

determine_kinds_of_type_contexts :: !{#CommonDefs} ![TypeContext] !*ClassDefInfos !*AnalyseState -> (!*ClassDefInfos, !*AnalyseState)
determine_kinds_of_type_contexts modules type_contexts class_infos as
	= foldSt (determine_kinds_of_type_context modules) type_contexts (class_infos, as)
where
	determine_kinds_of_type_context :: !{#CommonDefs} !TypeContext !(!*ClassDefInfos, !*AnalyseState) -> (!*ClassDefInfos, !*AnalyseState)
	determine_kinds_of_type_context modules {tc_class=TCClass {glob_module,glob_object={ds_ident,ds_index}},tc_types} (class_infos, as)
		# (class_kinds, class_infos) = class_infos![glob_module,ds_index]
		| length class_kinds == length tc_types
			# as = fold2St (verify_kind_of_type modules) class_kinds tc_types as
			= (class_infos, as)
			= abort ("determine_kinds_of_type_context" ---> (ds_ident, class_kinds, tc_types))
	determine_kinds_of_type_context modules {tc_class=TCGeneric {gtc_generic,gtc_kind},tc_types} (class_infos, as)
		| length tc_types == 1
			# as = verify_kind_of_type modules gtc_kind (hd tc_types) as 
			= (class_infos, as)
			= abort ("determine_kinds_of_type_context" ---> (gtc_generic.glob_object.ds_ident, gtc_kind, tc_types))
			
	verify_kind_of_type modules req_kind type as
		# (kind_of_type, as=:{as_kind_heap,as_error}) = determineKind modules type as
		  {uki_kind_heap, uki_error} = unifyKinds kind_of_type (kindToKindInfo req_kind) {uki_kind_heap = as_kind_heap, uki_error = as_error}
		= { as & as_kind_heap = uki_kind_heap, as_error = uki_error }

determine_kinds_type_list :: !{#CommonDefs} [AType] !*AnalyseState -> *AnalyseState
determine_kinds_type_list modules types as
	= foldSt (force_star_kind modules) types as
where
	force_star_kind modules type as
		# (off_kind, as=:{as_kind_heap,as_error}) = determineKind modules type as
		  {uki_kind_heap, uki_error} = unifyKinds off_kind KI_Const {uki_kind_heap = as_kind_heap, uki_error = as_error}
		= { as & as_kind_heap = uki_kind_heap, as_error = uki_error }

class_def_error = "cyclic dependencies between type classes"
type_appl_error = "type constructor has too many arguments"

cyclicClassInfoMark =: [KindCycle]

determineKindsOfClasses :: !NumberSet !{#CommonDefs} !*TypeDefInfos !*TypeVarHeap !*ErrorAdmin
	-> (!*ClassDefInfos, !*TypeDefInfos, !*TypeVarHeap, !*ErrorAdmin)
determineKindsOfClasses used_module_numbers modules type_def_infos type_var_heap error
	#! prev_error_ok = error.ea_ok	
	# nr_of_modules = size modules
	  class_infos = {{} \\ module_nr <- [0..nr_of_modules] }
	  class_infos = iFoldSt (initialyse_info_for_module used_module_numbers modules) 0 nr_of_modules class_infos
	  as =
	  	{	as_td_infos			= type_def_infos
		,	as_type_var_heap	= type_var_heap
		,	as_kind_heap		= newHeap
		,	as_error			= { error & ea_ok = True }
		}

	  (class_infos, {as_td_infos,as_type_var_heap,as_error}) = iFoldSt (determine_kinds_of_class_in_module modules) 0 nr_of_modules (class_infos, as)
	#! ok = as_error.ea_ok
	= (class_infos, as_td_infos, as_type_var_heap, { as_error & ea_ok = prev_error_ok && ok })
where
	initialyse_info_for_module used_module_numbers modules module_index class_infos
		| inNumberSet module_index used_module_numbers
			# nr_of_classes = size modules.[module_index].com_class_defs
			= { class_infos	& [module_index] = createArray nr_of_classes [] }
			= class_infos

	determine_kinds_of_class_in_module modules module_index (class_infos, as)
		#! nr_of_classes = size class_infos.[module_index]
		= iFoldSt (determine_kinds_of_class modules module_index) 0 nr_of_classes (class_infos, as)

	determine_kinds_of_class :: !{#CommonDefs} !Index !Index !(!*ClassDefInfos, !*AnalyseState) -> (!*ClassDefInfos, !*AnalyseState)
	determine_kinds_of_class modules class_module class_index (class_infos, as)
		| isEmpty class_infos.[class_module,class_index]
			# {com_class_defs,com_member_defs} = modules.[class_module]
			  {class_args,class_context,class_members,class_arity,class_pos,class_name} = com_class_defs.[class_index]
			  (class_kind_vars, as_kind_heap) = fresh_kind_vars class_arity [] as.as_kind_heap
			  as_type_var_heap = bind_kind_vars class_args class_kind_vars as.as_type_var_heap
			  as_error = pushErrorAdmin (newPosition class_name class_pos) as.as_error
			  class_infos = { class_infos & [class_module,class_index] = cyclicClassInfoMark }
			  (class_infos, as) = determine_kinds_of_context_classes class_context (class_infos,
			  								{ as & as_kind_heap = as_kind_heap, as_type_var_heap = as_type_var_heap, as_error = as_error })
			| as.as_error.ea_ok
				# (class_infos, as) = determine_kinds_of_type_contexts modules class_context class_infos as
				  (class_infos, as) = determine_kinds_of_members modules class_members com_member_defs class_kind_vars (class_infos, as)
				  (class_kinds, as_kind_heap) = retrieve_class_kinds class_kind_vars as.as_kind_heap
				= ({class_infos & [class_module,class_index] = class_kinds }, { as & as_kind_heap = as_kind_heap, as_error = popErrorAdmin as.as_error})
//						---> ("determine_kinds_of_class", class_name, class_kinds)
				= ({class_infos & [class_module,class_index] = [ KindConst \\ _ <- [1..class_arity]] }, { as & as_error = popErrorAdmin as.as_error })
		| isCyclicClass class_infos.[class_module,class_index]
			# {class_name,class_arity} = modules.[class_module].com_class_defs.[class_index]
			= ({ class_infos & [class_module,class_index] = [ KindConst \\ _ <- [1..class_arity]]},
				{ as & as_error = checkError class_name class_def_error as.as_error })
			= (class_infos, as)
	where
		fresh_kind_vars nr_of_vars fresh_vars kind_heap
			| nr_of_vars > 0
				# (kind_info_ptr, kind_heap) = newPtr KI_Const kind_heap
				= fresh_kind_vars (dec nr_of_vars) [ kind_info_ptr : fresh_vars] (kind_heap <:= (kind_info_ptr, KI_Var kind_info_ptr))
				= (fresh_vars, kind_heap)
	
		
		isCyclicClass [ KindCycle : _ ] = True 
		isCyclicClass _					= False 

	determine_kinds_of_context_classes contexts class_infos_and_as
		= foldSt (determine_kinds_of_context_class modules) contexts class_infos_and_as
	where
		determine_kinds_of_context_class modules {tc_class=TCClass {glob_module,glob_object={ds_index}}} infos_and_as
			= determine_kinds_of_class modules glob_module ds_index infos_and_as
		determine_kinds_of_context_class modules {tc_class=TCGeneric {gtc_kind}} infos_and_as
			= infos_and_as 

	bind_kind_vars type_vars kind_ptrs type_var_heap
		= fold2St bind_kind_var type_vars kind_ptrs type_var_heap
	where
		bind_kind_var {tv_info_ptr} kind_info_ptr type_var_heap
			= type_var_heap <:= (tv_info_ptr, TVI_TypeKind kind_info_ptr)
			
	clear_variables type_vars type_var_heap
		= foldSt clear_variable type_vars type_var_heap
	where
		clear_variable {tv_info_ptr} type_var_heap
			= type_var_heap <:= (tv_info_ptr, TVI_Empty)

	determine_kinds_of_members modules members member_defs class_kind_vars (class_infos, as)
		= iFoldSt (determine_kind_of_member modules members member_defs class_kind_vars) 0 (size members) (class_infos, as)
		
	determine_kind_of_member modules members member_defs class_kind_vars loc_member_index class_infos_and_as
		# glob_member_index = members.[loc_member_index].ds_index
		  {me_class_vars,me_type={st_vars,st_args,st_result,st_context}} = member_defs.[glob_member_index]
		  other_contexts = (tl st_context)
		  (class_infos, as) = determine_kinds_of_context_classes other_contexts class_infos_and_as
		  as_type_var_heap = clear_variables st_vars as.as_type_var_heap
		  as_type_var_heap = bind_kind_vars me_class_vars class_kind_vars as_type_var_heap
		  (as_type_var_heap, as_kind_heap) = fresh_kind_vars_for_unbound_vars st_vars as_type_var_heap as.as_kind_heap
		  as = determine_kinds_type_list modules [st_result:st_args] { as & as_type_var_heap = as_type_var_heap, as_kind_heap = as_kind_heap}
		  (class_infos, as)	= determine_kinds_of_type_contexts modules other_contexts class_infos as
		= (class_infos, as)
	where
		fresh_kind_vars_for_unbound_vars type_vars type_var_heap kind_heap
			= foldSt fresh_kind_vars_for_unbound_var type_vars (type_var_heap, kind_heap)

		fresh_kind_vars_for_unbound_var {tv_info_ptr} (type_var_heap, kind_heap)
			# (tv_info, type_var_heap) = readPtr tv_info_ptr type_var_heap
			= case tv_info of
				TVI_Empty
					# (kind_info_ptr, kind_heap) = newPtr KI_Const kind_heap
					-> (type_var_heap <:= (tv_info_ptr, TVI_TypeKind kind_info_ptr), kind_heap <:= (kind_info_ptr, KI_Var kind_info_ptr))
				_
					-> (type_var_heap, kind_heap)
					
	retrieve_class_kinds class_kind_vars kind_heap
		= mapSt retrieve_kind class_kind_vars kind_heap
	where
		retrieve_kind kind_info_ptr kind_heap
			# (kind_info, kind_heap) = readPtr kind_info_ptr kind_heap
			= kindInfoToKind kind_info kind_heap

bindFreshKindVariablesToTypeVars :: [TypeVar] !*TypeVarHeap !*KindHeap -> (!*TypeVarHeap,!*KindHeap)
bindFreshKindVariablesToTypeVars type_vars type_var_heap as_kind_heap
	= foldSt new_kind type_vars (type_var_heap, as_kind_heap)
where
	new_kind :: !TypeVar !(!*TypeVarHeap,!*KindHeap) -> (!*TypeVarHeap,!*KindHeap)
	new_kind {tv_info_ptr} (type_var_heap, kind_heap)
		# (kind_info_ptr, kind_heap) = newPtr KI_Const kind_heap
		= (	type_var_heap <:= (tv_info_ptr, TVI_TypeKind kind_info_ptr), kind_heap <:= (kind_info_ptr, KI_Var kind_info_ptr))

checkKindsOfCommonDefsAndFunctions :: !Index !Index !NumberSet ![IndexRange] !{#CommonDefs} !u:{# FunDef} !v:{#DclModule} !*TypeDefInfos !*ClassDefInfos
	!*TypeVarHeap !*GenericHeap !*ErrorAdmin -> (!u:{# FunDef}, !v:{#DclModule}, !*TypeDefInfos, !*TypeVarHeap, !*GenericHeap, !*ErrorAdmin)
checkKindsOfCommonDefsAndFunctions first_uncached_module main_module_index used_module_numbers icl_fun_def_ranges common_defs icl_fun_defs dcl_modules
			type_def_infos class_infos type_var_heap gen_heap error
	# as =
	  	{	as_td_infos			= type_def_infos
		,	as_type_var_heap	= type_var_heap
		,	as_kind_heap		= newHeap
		,	as_error			= error
		}

	# (icl_fun_defs, dcl_modules, class_infos, gen_heap, as)
		= iFoldSt (check_kinds_of_module first_uncached_module main_module_index used_module_numbers icl_fun_def_ranges common_defs)
						0 (size common_defs) (icl_fun_defs, dcl_modules, class_infos, gen_heap, as)
	= (icl_fun_defs, dcl_modules, as.as_td_infos, as.as_type_var_heap, gen_heap, as.as_error)
where
	check_kinds_of_module first_uncached_module main_module_index used_module_numbers icl_fun_def_ranges common_defs module_index
					(icl_fun_defs, dcl_modules, class_infos, gen_heap, as) 
		| inNumberSet module_index used_module_numbers
			| module_index == main_module_index
				# (class_infos, as) = check_kinds_of_class_instances common_defs 0 common_defs.[module_index].com_instance_defs class_infos as
				# (class_infos, gen_heap, as) = check_kinds_of_generics common_defs 0 common_defs.[module_index].com_generic_defs class_infos gen_heap as
				# as = check_kinds_of_gencases 0 common_defs.[module_index].com_gencase_defs as
				# (icl_fun_defs, class_infos, as) = foldSt (check_kinds_of_icl_fuctions common_defs) icl_fun_def_ranges (icl_fun_defs, class_infos, as)
					with
						check_kinds_of_icl_fuctions common_defs {ir_from,ir_to} (icl_fun_defs, class_infos, as)
							= iFoldSt (check_kinds_of_icl_fuction common_defs) ir_from ir_to (icl_fun_defs, class_infos, as)
				= (icl_fun_defs, dcl_modules, class_infos, gen_heap, as)
			| module_index >= first_uncached_module
				# (class_infos, as) = check_kinds_of_class_instances common_defs 0 common_defs.[module_index].com_instance_defs class_infos as
				# (class_infos, gen_heap, as) = check_kinds_of_generics common_defs 0 common_defs.[module_index].com_generic_defs class_infos gen_heap as
				# as = check_kinds_of_gencases 0 common_defs.[module_index].com_gencase_defs as
				# (dcl_modules, class_infos, as) = check_kinds_of_dcl_fuctions common_defs module_index dcl_modules class_infos as
				= (icl_fun_defs, dcl_modules, class_infos, gen_heap, as)
				= (icl_fun_defs, dcl_modules, class_infos, gen_heap, as)
			= (icl_fun_defs, dcl_modules, class_infos, gen_heap, as)				

	check_kinds_of_class_instances common_defs instance_index instance_defs class_infos as
		| instance_index == size instance_defs
			= (class_infos, as)
			# (class_infos, as) = check_kinds_of_class_instance common_defs instance_defs.[instance_index] class_infos as
			= check_kinds_of_class_instances common_defs (inc instance_index) instance_defs class_infos as
	where	
		check_kinds_of_class_instance :: !{#CommonDefs} !ClassInstance  !*ClassDefInfos !*AnalyseState -> (!*ClassDefInfos, !*AnalyseState)
		check_kinds_of_class_instance common_defs {ins_class,ins_ident,ins_pos,ins_type={it_vars,it_types,it_context}} class_infos
					as=:{as_type_var_heap,as_kind_heap,as_error}
			# as_error = pushErrorAdmin (newPosition ins_ident ins_pos) as_error
			  (as_type_var_heap, as_kind_heap) = bindFreshKindVariablesToTypeVars it_vars as_type_var_heap as_kind_heap
			  as = { as & as_type_var_heap = as_type_var_heap, as_kind_heap = as_kind_heap, as_error = as_error }
			  (class_infos, as) = determine_kinds_of_type_contexts common_defs
			  		[{tc_class = TCClass ins_class, tc_types = it_types, tc_var = nilPtr} : it_context] class_infos as
			= (class_infos, { as & as_error = popErrorAdmin as.as_error})

	check_kinds_of_generics common_defs index generic_defs class_infos gen_heap as
		| index == size generic_defs
			= (class_infos, gen_heap, as)
			# (class_infos, gen_heap, as) = check_kinds_of_generic common_defs generic_defs.[index] class_infos gen_heap as
			= check_kinds_of_generics common_defs (inc index) generic_defs class_infos gen_heap as
	where
		check_kinds_of_generic :: !{#CommonDefs} !GenericDef  !*ClassDefInfos !*GenericHeap !*AnalyseState -> (!*ClassDefInfos, !*GenericHeap, !*AnalyseState)
		check_kinds_of_generic common_defs {gen_type, gen_name, gen_pos, gen_vars, gen_info_ptr} class_infos gen_heap as					
			# as = {as & as_error = pushErrorAdmin (newPosition gen_name gen_pos) as.as_error}
			# (class_infos, as) = check_kinds_of_symbol_type common_defs gen_type class_infos as			
			# (kinds, as) = mapSt retrieve_tv_kind gen_type.st_vars as
			# as = check_kinds_of_generic_vars (take (length gen_vars) kinds) as
			# (gen_info, gen_heap) = readPtr gen_info_ptr gen_heap
			# gen_heap = writePtr gen_info_ptr {gen_info & gen_var_kinds = kinds} gen_heap
			# as = {as & as_error = popErrorAdmin as.as_error}	
			= (class_infos, gen_heap, as)
			
		retrieve_tv_kind :: !TypeVar !*AnalyseState -> (!TypeKind, !*AnalyseState)		
		retrieve_tv_kind tv=:{tv_info_ptr} as=:{as_type_var_heap, as_kind_heap}
			#! (TVI_TypeKind kind_info_ptr, as_type_var_heap) = readPtr tv_info_ptr as_type_var_heap
			#! (kind_info, as_kind_heap) = readPtr kind_info_ptr as_kind_heap
			#! (kind, as_kind_heap) = kindInfoToKind kind_info as_kind_heap 	
			= (kind, {as & as_kind_heap = as_kind_heap, as_type_var_heap = as_type_var_heap})

		check_kinds_of_generic_vars :: ![TypeKind] !*AnalyseState -> *AnalyseState
		check_kinds_of_generic_vars [gen_kind:gen_kinds] as
			//| all (\k -> k == gen_kind) gen_kinds
			  | all ((==) KindConst) [gen_kind:gen_kinds]  // forcing all kind variables be of kind star
				 = as 
				 # as_error = checkError 
				 	"conflicting kinds: "
				 	"generic variables must have the same kind" 
				 	as.as_error
				 = {as & as_error = as_error}  

	check_kinds_of_gencases :: !Index !{#GenericCaseDef} !*AnalyseState -> *AnalyseState
	check_kinds_of_gencases index gencases as
		| index == size gencases
			= as
			# as = check_kinds_of_gencase gencases.[index] as	
			= check_kinds_of_gencases (inc index) gencases as 
	where
		check_kinds_of_gencase gencase=:{gc_type_cons=TypeConsSymb {type_index}} as=:{as_error, as_td_infos}
			# ({tdi_kinds}, as_td_infos) = as_td_infos ! [type_index.glob_module, type_index.glob_object] 
			# kind = if (isEmpty tdi_kinds) KindConst (KindArrow tdi_kinds)
			# as_error = case rank_of_kind kind > 2 of 
				True -> checkError kind "only kinds up to rank-2 supported by generics" as_error
				False -> as_error
			= {as & as_error = as_error, as_td_infos = as_td_infos}
		where
			rank_of_kind KindConst = 0
			rank_of_kind (KindArrow kinds) = 1 + foldr max 0 (map rank_of_kind kinds)	
			
		check_kinds_of_gencase gencase as 
			= as

	check_kinds_of_icl_fuction common_defs fun_index (icl_fun_defs, class_infos, as)
		# ({fun_type,fun_symb,fun_pos}, icl_fun_defs) = icl_fun_defs![fun_index]
		= case fun_type of
			Yes symbol_type
				# as_error = pushErrorAdmin (newPosition fun_symb fun_pos) as.as_error
				  (class_infos, as) = check_kinds_of_symbol_type common_defs symbol_type class_infos { as & as_error = as_error }
				-> (icl_fun_defs, class_infos, { as & as_error = popErrorAdmin as.as_error })
			No
				-> (icl_fun_defs, class_infos, as)

	check_kinds_of_dcl_fuctions common_defs module_index dcl_modules class_infos as
		# ({dcl_functions,dcl_instances}, dcl_modules) = dcl_modules![module_index]
		# nr_of_dcl_funs = dcl_instances.ir_from
		# (class_infos, as) = iFoldSt (check_kinds_of_dcl_fuction common_defs dcl_functions) 0 nr_of_dcl_funs (class_infos, as)
		= (dcl_modules, class_infos, as)
	where
		check_kinds_of_dcl_fuction common_defs dcl_functions fun_index (class_infos, as)
			# {ft_type,ft_symb,ft_pos} = dcl_functions.[fun_index]
			  as_error = pushErrorAdmin (newPosition ft_symb ft_pos) as.as_error
			  (class_infos, as) = check_kinds_of_symbol_type common_defs ft_type class_infos
			  							{ as & as_error = as_error }			  								
			= (class_infos, { as & as_error = popErrorAdmin as.as_error})
			
	check_kinds_of_symbol_type :: !{#CommonDefs} !SymbolType !*ClassDefInfos !*AnalyseState -> (!*ClassDefInfos, !*AnalyseState)
	check_kinds_of_symbol_type common_defs {st_vars,st_result,st_args,st_context} class_infos as=:{as_type_var_heap,as_kind_heap}
		# (as_type_var_heap, as_kind_heap) = bindFreshKindVariablesToTypeVars st_vars as_type_var_heap as_kind_heap
		  as = determine_kinds_type_list common_defs [st_result:st_args] { as & as_type_var_heap = as_type_var_heap, as_kind_heap = as_kind_heap}
		= determine_kinds_of_type_contexts common_defs st_context class_infos as

instance <<< DynamicType
where
	(<<<) file {dt_global_vars,dt_type} = file <<< dt_global_vars <<< dt_type

instance <<< GlobalIndex
where
	(<<<) file {gi_module,gi_index} = file <<< '[' <<< gi_module <<< ',' <<< gi_index <<< ']'

checkLeftRootAttributionOfTypeDef :: !{# CommonDefs} GlobalIndex !(!*TypeDefInfos, !*TypeVarHeap, !*ErrorAdmin)
		-> (!*TypeDefInfos, !*TypeVarHeap, !*ErrorAdmin)
checkLeftRootAttributionOfTypeDef common_defs {gi_module,gi_index} (td_infos, th_vars, error)
	# {td_rhs, td_attribute, td_name, td_pos} = common_defs.[gi_module].com_type_defs.[gi_index]
	| isUniqueAttr td_attribute
		= (td_infos, th_vars, error)
	# (is_unique, (td_infos, th_vars))
			= isUniqueTypeRhs common_defs gi_module td_rhs (td_infos, th_vars)
	| is_unique
		= (td_infos, th_vars, checkErrorWithIdentPos (newPosition td_name td_pos) 
								" left root * attribute expected" error)
		= (td_infos, th_vars, error)
		
isUniqueTypeRhs common_defs mod_index (AlgType constructors) state
	= one_constructor_is_unique common_defs mod_index constructors state
isUniqueTypeRhs common_defs mod_index (SynType rhs) state
	= isUnique common_defs rhs state
isUniqueTypeRhs common_defs mod_index (RecordType {rt_constructor}) state
	= one_constructor_is_unique common_defs mod_index [rt_constructor] state
isUniqueTypeRhs common_defs mod_index _ state
	= (False, state)

one_constructor_is_unique common_defs mod_index [] state
	= (False, state)
one_constructor_is_unique common_defs mod_index [{ds_index}:constructors] state
	# {cons_type}
			= common_defs.[mod_index].com_cons_defs.[ds_index]
	  (uniqueness_of_args, state)
	  		= mapSt (isUnique common_defs) cons_type.st_args state
	= (or uniqueness_of_args, state)

class isUnique a :: !{# CommonDefs} !a !(!*TypeDefInfos, !*TypeVarHeap) -> (!Bool, !(!*TypeDefInfos, !*TypeVarHeap))

instance isUnique AType
  where
	isUnique common_defs {at_attribute=TA_Unique} state
		= (True, state)
	isUnique common_defs {at_type} state
		= isUnique common_defs at_type state
		
instance isUnique Type
  where
	isUnique common_defs (TA {type_index={glob_module, glob_object}} type_args) (td_infos, th_vars)
		= isUnique_for_TA glob_module glob_object type_args common_defs td_infos th_vars
	isUnique common_defs (TAS {type_index={glob_module, glob_object}} type_args _) (td_infos, th_vars)
		= isUnique_for_TA glob_module glob_object type_args common_defs td_infos th_vars
	isUnique common_defs _ state
		= (False, state)

isUnique_for_TA :: Int Int [AType] !{# CommonDefs} !*TypeDefInfos !*TypeVarHeap -> (!Bool, !(!*TypeDefInfos, !*TypeVarHeap))
isUnique_for_TA glob_module glob_object type_args common_defs td_infos th_vars
	# type_def
			= common_defs.[glob_module].com_type_defs.[glob_object]
	| isUniqueAttr type_def.td_attribute
		= (True, (td_infos, th_vars))
	# (prop_classification, th_vars, td_infos)
			= propClassification glob_object glob_module (repeatn type_def.td_arity 0)
					common_defs th_vars td_infos
	  (uniqueness_of_args, (td_infos, th_vars))
	  		= mapSt (isUnique common_defs) type_args (td_infos, th_vars)
	= (unique_if_arg_is_unique_and_propagating uniqueness_of_args prop_classification, (td_infos, th_vars))
  where
	unique_if_arg_is_unique_and_propagating [] _
		= False
	unique_if_arg_is_unique_and_propagating [is_unique_argument:rest] prop_classification
		| isOdd prop_classification && is_unique_argument
			= True
		= unique_if_arg_is_unique_and_propagating rest (prop_classification>>1)

isUniqueAttr TA_Unique = True
isUniqueAttr _ = False
