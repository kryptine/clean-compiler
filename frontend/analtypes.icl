implementation module analtypes

import StdEnv
import syntax, checksupport, checktypes, check, typesupport, utilities, RWSDebug

::	UnifyKindsInfo = 
	{	uki_kind_heap	::!.KindHeap
	,	uki_error		::!.ErrorAdmin
	}
	
AS_NotChecked :== -1

instance <<< TypeKind
where
	(<<<) file tk = file <<< toString (toKindInfo tk)

instance toString KindInfo
where
	toString (KI_Var ptr) 		= "*" +++ toString (ptrToInt ptr)
	toString (KI_Const) 		= "*"
	toString (KI_Arrow kinds)	= kind_list_to_string kinds
	where
		kind_list_to_string [] = " ?????? "
		kind_list_to_string [k] = "* -> *"
		kind_list_to_string [k:ks] = "* -> " +++ kind_list_to_string ks


kindError kind1 kind2 error
	= checkError "conflicting kinds: " (toString kind1 +++ " and " +++ toString kind2) error

unifyKinds  :: !KindInfo !KindInfo !*UnifyKindsInfo -> *UnifyKindsInfo
unifyKinds (KI_Indirection kind1) kind2 uni_info=:{uki_kind_heap}
	= unifyKinds kind1 kind2 uni_info
unifyKinds kind1 (KI_Indirection kind2) uni_info=:{uki_kind_heap}
	= unifyKinds kind1 kind2 uni_info
unifyKinds (KI_Var info_ptr1) kind=:(KI_Var info_ptr2) uni_info=:{uki_kind_heap}
	| info_ptr1 == info_ptr2
		= uni_info
		= { uni_info & uki_kind_heap = writePtr info_ptr1 (KI_Indirection kind) uki_kind_heap }
unifyKinds k1=:(KI_Var info_ptr1) kind uni_info=:{uki_kind_heap,uki_error}
	| contains_kind_ptr info_ptr1 uki_kind_heap kind
		= { uni_info & uki_error = kindError k1 kind uki_error }
		= { uni_info & uki_kind_heap = writePtr info_ptr1 (KI_Indirection kind) uki_kind_heap }
where
	contains_kind_ptr info_ptr uki_kind_heap (KI_Arrow kinds) 
		= any (contains_kind_ptr info_ptr uki_kind_heap) kinds
	contains_kind_ptr info_ptr uki_kind_heap (KI_Indirection kind_info)
		= contains_kind_ptr info_ptr uki_kind_heap kind_info
	contains_kind_ptr info_ptr uki_kind_heap (KI_Var kind_info_ptr)
		= info_ptr1 == kind_info_ptr
	contains_kind_ptr info_ptr uki_kind_heap (KI_Const)
		= False

unifyKinds kind k1=:(KI_Var info_ptr1) uni_info
	= unifyKinds k1 kind  uni_info
unifyKinds kind1=:(KI_Arrow kinds1) kind2=:(KI_Arrow kinds2) uni_info=:{uki_error}
	| length kinds1 == length kinds2
		= foldr2 unifyKinds uni_info kinds1 kinds2
		= { uni_info & uki_error = kindError kind1 kind2 uki_error }
unifyKinds KI_Const KI_Const uni_info
	= uni_info
unifyKinds kind1 kind2 uni_info=:{uki_error}
	= { uni_info & uki_error = kindError kind1 kind2 uki_error }

class toKindInfo a :: !a -> KindInfo

instance toKindInfo TypeKind
where
	toKindInfo (KindVar info_ptr)
		= KI_Var info_ptr
	toKindInfo KindConst
		= KI_Const
	toKindInfo (KindArrow arity)
		= KI_Arrow [ KI_Const \\ i <- [1 .. arity]]
//			---> ("toKindInfo", arity)


::	VarBind =
	{	vb_var 	::	!KindInfoPtr
	,	vb_vars	::	![KindInfoPtr]
	}

::	Conditions =
	{	con_top_var_binds	:: ![KindInfoPtr]
	,	con_var_binds		:: ![VarBind]
	}


	
::	AnalState =
	{	as_td_infos			:: !.TypeDefInfos
	,	as_heaps			:: !.TypeHeaps
	,	as_kind_heap		:: !.KindHeap
	,	as_check_marks		:: !.{# .{# Int}}
	,	as_next_num			:: !Int
	,	as_deps				:: ![Global Index]
//	,	as_groups			:: ![[Global Index]]
	,	as_next_group_num	:: !Int
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

class analTypes type :: !Bool !{#CommonDefs} ![KindInfoPtr] !type !(!Conditions, !*AnalState)
	-> (!Int, !KindInfo, TypeProperties, !(!Conditions, !*AnalState))

cDummyBool :== False

instance analTypes AType
where
	analTypes _ modules form_tvs atype=:{at_attribute,at_type} conds_as
		= analTypes (has_root_attr at_attribute) modules form_tvs at_type conds_as
	where
		has_root_attr (TA_RootVar _)	= True
		has_root_attr _ 				= False
		
instance analTypes TypeVar
where
	analTypes has_root_attr modules form_tvs {tv_info_ptr}  (conds=:{con_var_binds}, as=:{as_heaps, as_kind_heap})
		# (TVI_TypeKind kind_info_ptr, th_vars) = readPtr tv_info_ptr as_heaps.th_vars
		  (kind_info, as_kind_heap) = readPtr kind_info_ptr as_kind_heap
		  kind_info = skip_indirections kind_info
		| isEmpty form_tvs
			= (cMAXINT, kind_info, cIsHyperStrict, (conds, { as & as_heaps = { as_heaps & th_vars = th_vars }, as_kind_heap = as_kind_heap }))
			= (cMAXINT, kind_info, cIsHyperStrict, ({ conds & con_var_binds = [{vb_var = kind_info_ptr, vb_vars = form_tvs } : con_var_binds] },
						 { as & as_heaps = { as_heaps & th_vars = th_vars }, as_kind_heap = as_kind_heap }))
	where
		skip_indirections (KI_Indirection kind)
			= skip_indirections kind
		skip_indirections kind
			= kind

instance analTypes Type
where
	analTypes has_root_attr modules form_tvs (TV tv) conds_as
		= analTypes has_root_attr modules form_tvs tv conds_as
	analTypes has_root_attr modules form_tvs type=:(TA {type_index={glob_module,glob_object},type_arity} types) conds_as
		# (ldep, (conds, as)) = anal_type_def modules glob_module glob_object conds_as
		  {td_arity} = modules.[glob_module].com_type_defs.[glob_object]
		  ({tdi_kinds, tdi_properties}, as) = as!as_td_infos.[glob_module].[glob_object]
		  kind = if (td_arity == type_arity) KI_Const (KI_Arrow [ toKindInfo tk \\ tk <- drop type_arity tdi_kinds ])
		| ldep < cMAXINT /* hence we have a recursive type application */ // ---> ("analTypes", toString kind)
			# (ldep2, type_props, conds_as)
					= anal_types_of_rec_type_cons modules form_tvs types tdi_kinds (conds, as)
			= (min ldep ldep2, kind, type_props, conds_as)
			# (ldep2, type_props, conds_as)
					= anal_types_of_type_cons modules form_tvs types tdi_kinds (conds, as)
//							 ---> (types, tdi_kinds)
			= (min ldep ldep2, kind, condCombineTypeProperties has_root_attr type_props tdi_properties, conds_as)
	where
		anal_types_of_rec_type_cons modules form_tvs [] _ conds_as
			= (cMAXINT, cIsHyperStrict, conds_as)
		anal_types_of_rec_type_cons modules form_tvs [type : types] [(KindVar kind_info_ptr) : tvs] conds_as
			# (ldep, type_kind, type_props, (conds, as=:{as_kind_heap,as_error})) = analTypes has_root_attr modules [ kind_info_ptr : form_tvs ] type conds_as
			  (kind, as_kind_heap) = readPtr kind_info_ptr as_kind_heap
			  {uki_kind_heap, uki_error} = unifyKinds type_kind kind {uki_kind_heap = as_kind_heap, uki_error = as_error}
			| is_type_var type
				# (min_dep, other_type_props, conds_as) = 
						anal_types_of_rec_type_cons modules form_tvs types tvs (conds, { as & as_kind_heap = uki_kind_heap, as_error = uki_error })
				= (min ldep min_dep, combineTypeProperties type_props other_type_props, conds_as)
				# (min_dep, other_type_props, conds_as) = 
						anal_types_of_rec_type_cons modules form_tvs types tvs
							({ conds & con_top_var_binds = [kind_info_ptr : conds.con_top_var_binds]}, { as & as_kind_heap = uki_kind_heap, as_error = uki_error })

				# (min_dep, other_type_props, conds_as) = 
						anal_types_of_rec_type_cons modules form_tvs types tvs 
							({ conds & con_top_var_binds = [kind_info_ptr : conds.con_top_var_binds]}, { as & as_kind_heap = uki_kind_heap, as_error = uki_error })
				= (min ldep min_dep, combineTypeProperties type_props other_type_props, conds_as)
		where
			is_type_var {at_type = TV _}
				= True
			is_type_var _
				= False
			
		anal_types_of_type_cons modules form_tvs [] _ conds_as
			= (cMAXINT, cIsHyperStrict, conds_as)
		anal_types_of_type_cons modules form_tvs [type : types] [tk : tks] conds_as
			# (ldep, type_kind, type_props, (conds, as=:{as_kind_heap,as_error})) = analTypes has_root_attr modules form_tvs type conds_as
			  {uki_kind_heap, uki_error} = unifyKinds type_kind (toKindInfo tk) {uki_kind_heap = as_kind_heap, uki_error = as_error}
			  (min_dep, other_type_props, conds_as)
					=  anal_types_of_type_cons modules form_tvs types tks (conds, { as & as_kind_heap = uki_kind_heap, as_error = uki_error })
			= (min ldep min_dep, combineTypeProperties type_props other_type_props, conds_as)
		anal_types_of_type_cons modules form_tvs types tks conds_as
			= abort ("anal_types_of_type_cons (analtypes.icl)" ---> (types, tks))
		
		anal_type_def modules module_index type_index (conds, as=:{as_check_marks})
			#! mark = as_check_marks.[module_index].[type_index]
			| mark == AS_NotChecked
				# (mark, ({con_var_binds,con_top_var_binds}, as)) = analTypeDef modules module_index type_index as
				= (mark, ({con_top_var_binds = con_top_var_binds ++ conds.con_top_var_binds, con_var_binds = con_var_binds ++ conds.con_var_binds}, as))
				= (mark, (conds, as))
	
	analTypes has_root_attr modules form_tvs (arg_type --> res_type) conds_as
		# (arg_ldep, arg_kind, arg_type_props, conds_as) = analTypes has_root_attr modules form_tvs arg_type conds_as
		  (res_ldep, res_kind, res_type_props, (conds, as=:{as_kind_heap,as_error})) = analTypes has_root_attr modules form_tvs res_type conds_as
		  {uki_kind_heap, uki_error} = unifyKinds res_kind KI_Const (unifyKinds arg_kind KI_Const {uki_kind_heap = as_kind_heap, uki_error = as_error})
		  type_props = if	has_root_attr
							(combineCoercionProperties arg_type_props res_type_props bitor cIsNonCoercible)
							(combineCoercionProperties arg_type_props res_type_props)
		= (min arg_ldep res_ldep, KI_Const, type_props, (conds, {as & as_kind_heap = uki_kind_heap, as_error = uki_error }))
	analTypes has_root_attr modules form_tvs (CV tv :@: types) conds_as
		# (ldep1, type_kind, cv_props, conds_as) = analTypes has_root_attr modules form_tvs tv conds_as
		  (ldep2, type_kinds, is_non_coercible, (conds, as=:{as_kind_heap,as_error})) = check_type_list modules form_tvs types conds_as
		  {uki_kind_heap, uki_error} = unifyKinds type_kind (KI_Arrow type_kinds) {uki_kind_heap = as_kind_heap, uki_error = as_error}
		  type_props = if (is_non_coercible || has_root_attr) cIsNonCoercible (cv_props bitand cIsNonCoercible)
		= (min ldep1 ldep2, KI_Const, type_props, (conds, {as & as_kind_heap = uki_kind_heap, as_error = uki_error }))

	where
		check_type_list modules form_tvs [] conds_as
			= (cMAXINT, [], False, conds_as)
		check_type_list modules form_tvs [type : types] conds_as
			# (ldep1, tk, type_props, (conds, as=:{as_kind_heap,as_error})) = analTypes has_root_attr modules form_tvs type conds_as
			  {uki_kind_heap, uki_error} = unifyKinds tk KI_Const {uki_kind_heap = as_kind_heap, uki_error = as_error}
			  (ldep2, tks, is_non_coercible, conds_as) = check_type_list modules form_tvs types (conds, {as & as_kind_heap = uki_kind_heap, as_error = uki_error })
			= (min ldep1 ldep2, [tk : tks], is_non_coercible || (type_props bitand cIsNonCoercible <> 0), conds_as)
	analTypes has_root_attr modules form_tvs type conds_as
		= (cMAXINT, KI_Const, cIsHyperStrict, conds_as)
	
/*
analTypesOfConstructor :: !Index !Index ![TypeVar] ![AttributeVar] !AType ![DefinedSymbol] !Bool !Index !Level !TypeAttribute !Conditions !*TypeSymbols !*TypeInfo !*CheckState
	-> *(!TypeProperties, !Conditions, !Int, !*TypeSymbols, !*TypeInfo, !*CheckState)
*/
analTypesOfConstructor modules cons_defs [{ds_index}:conses] (conds, as=:{as_heaps,as_kind_heap})
	# {cons_exi_vars,cons_type} = cons_defs.[ds_index]
	  (coercible, th_vars, as_kind_heap) = new_local_kind_variables cons_exi_vars (as_heaps.th_vars, as_kind_heap)
	  (cons_ldep, cons_properties, conds_as) = anal_types_of_cons modules cons_type.st_args
			(conds, { as & as_heaps = { as_heaps & th_vars = th_vars }, as_kind_heap = as_kind_heap })
	  (conses_ldep, other_properties, conds_as) = analTypesOfConstructor modules cons_defs conses conds_as
	  properties = combineTypeProperties cons_properties other_properties
	= (min cons_ldep conses_ldep, if coercible properties (properties bitor cIsNonCoercible), conds_as)
where
/*
	check_types_of_cons :: ![AType] !Bool !Index  !Level ![TypeVar] !TypeAttribute ![AttrInequality] !Conditions !*TypeSymbols !*TypeInfo !*CheckState
		-> *(![AType], ![[ATypeVar]], ![AttrInequality], !TypeProperties, !Conditions, !Int, !*TypeSymbols, !*TypeInfo, !*CheckState)
*/
	new_local_kind_variables td_args (type_var_heap, as_kind_heap)
		= foldSt new_kind td_args (True, type_var_heap, as_kind_heap)
	where
		new_kind {atv_variable={tv_info_ptr},atv_attribute} (coercible, type_var_heap, kind_heap)
			# (kind_info_ptr, kind_heap) = newPtr KI_Const kind_heap
			= (coercible && is_not_a_variable atv_attribute, type_var_heap <:= (tv_info_ptr, TVI_TypeKind kind_info_ptr),
				kind_heap <:= (kind_info_ptr, KI_Var kind_info_ptr))

		is_not_a_variable (TA_RootVar var)	= False
		is_not_a_variable attr				= True
			
	anal_types_of_cons modules [] conds_as
		= (cMAXINT, cIsHyperStrict, conds_as)
	anal_types_of_cons modules [type : types] conds_as
		# (ldep1, other_type_props, conds_as) = anal_types_of_cons modules types conds_as
		  (ldep2, type_kind, cv_props, (conds, as=:{as_kind_heap, as_error})) = analTypes cDummyBool modules [] type conds_as
		  {uki_kind_heap, uki_error} = unifyKinds type_kind KI_Const {uki_kind_heap = as_kind_heap, uki_error = as_error}
		  cons_props = if	(type_is_strict type.at_annotation)
							(combineTypeProperties cv_props other_type_props)
							(combineCoercionProperties cv_props other_type_props)
		= (min ldep1 ldep2, cons_props, (conds, { as & as_kind_heap = uki_kind_heap, as_error = uki_error }))

	where 
		type_is_strict AN_Strict
			= True
		type_is_strict annot
			= False

analTypesOfConstructor _ _ [] conds_as
	= (cMAXINT, cIsHyperStrict, conds_as)

/*
analRhsOfTypeDef :: !CheckedTypeDef ![AttributeVar] !Bool !Index !Level !TypeAttribute !Index !Conditions !*TypeSymbols !*TypeInfo !*CheckState
	-> (!TypeRhs, !TypeProperties, !Conditions, !Int, !*TypeSymbols, !*TypeInfo, !*CheckState)
*/

analRhsOfTypeDef modules com_cons_defs (AlgType conses) conds_as
	= analTypesOfConstructor modules com_cons_defs conses conds_as
analRhsOfTypeDef modules com_cons_defs (RecordType {rt_constructor}) conds_as
	= analTypesOfConstructor modules com_cons_defs [rt_constructor] conds_as
analRhsOfTypeDef modules _ (SynType type) conds_as
	# (ldep, type_kind, cv_props, (conds, as=:{as_kind_heap, as_error})) = analTypes cDummyBool modules [] type conds_as
	  {uki_kind_heap, uki_error} = unifyKinds type_kind KI_Const {uki_kind_heap = as_kind_heap, uki_error = as_error}
	= (ldep, cv_props, (conds, { as & as_kind_heap = as_kind_heap, as_error = as_error }))

emptyIdent name :== { id_name = name, id_info = nilPtr }

newKindVariables td_args (type_var_heap, as_kind_heap)
	= mapSt new_kind td_args (type_var_heap, as_kind_heap)
where
	new_kind {atv_variable={tv_info_ptr}} (type_var_heap, kind_heap)
		# (kind_info_ptr, kind_heap) = newPtr KI_Const kind_heap
		= (KindVar kind_info_ptr, (type_var_heap <:= (tv_info_ptr, TVI_TypeKind kind_info_ptr), kind_heap <:= (kind_info_ptr, KI_Var kind_info_ptr)))


/*
checkTypeDef :: !Bool !Index !Index  !Level !*TypeSymbols !*TypeInfo !*CheckState -> (!Int, !Conditions, !*TypeSymbols, !*TypeInfo, !*CheckState);
checkTypeDef is_main_dcl type_index module_index level ts=:{ts_type_defs} ti=:{ti_kind_heap,ti_heaps} cs=:{cs_error}
*/
analTypeDef modules type_module type_index as=:{as_error,as_heaps,as_kind_heap,as_td_infos}
	# {com_type_defs,com_cons_defs} = modules.[type_module]
	  {td_name,td_pos,td_args,td_rhs} = com_type_defs.[type_index]
	  (is_abs_type, abs_type_properties) = is_abstract_type td_rhs
	| is_abs_type
		# (tdi, as_td_infos) = as_td_infos![type_module].[type_index]
		  tdi = {	tdi & tdi_kinds = [ KindConst \\ _ <- td_args ], tdi_group = [{glob_module = type_module, glob_object = type_index}], 
		  			tdi_group_vars = [ i \\ _ <- td_args & i <- [0..]], tdi_properties = abs_type_properties }
		= (cMAXINT, ({con_top_var_binds = [], con_var_binds = [] }, { as & as_td_infos = { as_td_infos & [type_module].[type_index] = tdi}}))
		# position = newPosition td_name td_pos
		  as_error = pushErrorAdmin position as_error
		  (tdi_kinds, (th_vars, as_kind_heap)) = newKindVariables td_args (as_heaps.th_vars, as_kind_heap)
		  (ldep, type_properties, (conds, as)) = analRhsOfTypeDef modules com_cons_defs td_rhs ({ con_top_var_binds = [], con_var_binds = [] },
				push_on_dep_stack type_module type_index
					{ as &	as_heaps = { as_heaps & th_vars = th_vars }, as_kind_heap = as_kind_heap, as_error = as_error,
							as_td_infos = { as_td_infos & [type_module].[type_index].tdi_kinds = tdi_kinds }})
//								---> (td_name, td_args, tdi_kinds)
		= try_to_close_group modules type_module type_index ldep (conds,
				{ as & as_error = popErrorAdmin as.as_error,  as_td_infos = { as.as_td_infos & [type_module].[type_index].tdi_properties = type_properties }})
//					---> ("analTypeDef", td_name, type_module, type_index)
where
	is_abstract_type (AbstractType properties)
		= (True, properties)
	is_abstract_type _
		= (False, cAllBitsClear)

	push_on_dep_stack module_index type_index as=:{as_deps,as_check_marks,as_next_num}
		= { as &
				as_deps = [{glob_module = module_index, glob_object = type_index } : as_deps],
				as_check_marks = { as_check_marks & [module_index].[type_index] = as_next_num },
				as_next_num = inc as_next_num }

	try_to_close_group modules type_module type_index ldep (conds=:{con_top_var_binds,con_var_binds},
		as=:{as_check_marks,as_deps,as_next_group_num,as_kind_heap,as_heaps,as_td_infos})
		#! my_mark = as_check_marks.[type_module].[type_index]
		| (ldep == cMAXINT || ldep == my_mark)
			# (as_deps, as_check_marks, group) = close_group type_module type_index as_deps as_check_marks [] 
			  (kinds, (type_properties, as_kind_heap, as_td_infos)) = determine_kinds_and_properties_of_group group as_kind_heap as_td_infos
			  kind_heap = unify_var_binds con_var_binds as_kind_heap
			  (normalized_top_vars, (kind_var_store, as_kind_heap)) = normalize_top_vars con_top_var_binds 0 as_kind_heap
			  (as_kind_heap, as_td_infos) = update_type_group_info group kinds type_properties normalized_top_vars group as_next_group_num kind_var_store as_kind_heap as_td_infos
			= (cMAXINT, ({con_top_var_binds = [], con_var_binds = [] },
				 { as & as_check_marks = as_check_marks, as_deps = as_deps, as_kind_heap = as_kind_heap,
						as_td_infos = as_td_infos, as_next_group_num = inc as_next_group_num }))
			= (min my_mark ldep, (conds, as))

	close_group first_module first_index [d:ds] marks group
		# marks = { marks & [d.glob_module].[d.glob_object] = cMAXINT }
		| d.glob_module == first_module && d.glob_object == first_index
			= (ds, marks, [d : group])
			= close_group first_module first_index ds marks [d : group]

	determine_kinds_and_properties_of_group group kind_heap as_td_infos
		= mapSt determine_kinds group (cIsHyperStrict, kind_heap, as_td_infos)
	where
		determine_kinds {glob_module,glob_object} (type_properties, kind_heap, as_td_infos)
			# ({tdi_properties,tdi_kinds}, as_td_infos) = as_td_infos![glob_module].[glob_object]
			  (kinds, kind_heap) = mapSt retrieve_kind tdi_kinds kind_heap
			= (kinds, (combineTypeProperties type_properties tdi_properties, kind_heap, as_td_infos))
				
		retrieve_kind (KindVar kind_info_ptr) kind_heap
			#! kind_info = sreadPtr kind_info_ptr kind_heap
			= (determine_kind kind_info, kind_heap)
		where
			determine_kind (KI_Indirection kind) 
				= determine_kind kind
			determine_kind (KI_Arrow kinds)
				= KindArrow (length kinds)
			determine_kind kind
				= KindConst
			   
	unify_var_binds :: ![VarBind] !*KindHeap -> *KindHeap
	unify_var_binds binds kind_heap
		= foldr unify_var_bind kind_heap binds

	unify_var_bind :: !VarBind !*KindHeap -> *KindHeap
	unify_var_bind {vb_var, vb_vars} kind_heap
		#! kind_info = sreadPtr vb_var kind_heap
		# (vb_var, kind_heap) = determine_var_bind vb_var kind_info kind_heap
		= redirect_vars vb_var vb_vars kind_heap
	where	
		redirect_vars kind_info_ptr [var_info_ptr : var_info_ptrs] kind_heap
			#! kind_info = sreadPtr var_info_ptr kind_heap
			# (var_info_ptr, kind_heap) = determine_var_bind var_info_ptr kind_info kind_heap
			| kind_info_ptr == var_info_ptr
				= redirect_vars kind_info_ptr var_info_ptrs kind_heap
				= redirect_vars kind_info_ptr var_info_ptrs (writePtr kind_info_ptr (KI_VarBind var_info_ptr) kind_heap)
		redirect_vars kind_info_ptr [] kind_heap
			= kind_heap
			
		determine_var_bind _ (KI_VarBind kind_info_ptr) kind_heap
			#! kind_info = sreadPtr kind_info_ptr kind_heap
			= determine_var_bind kind_info_ptr  kind_info kind_heap
		determine_var_bind kind_info_ptr kind_info kind_heap
			= (kind_info_ptr, kind_heap)

	nomalize_var :: !KindInfoPtr !KindInfo !(!Int,!*KindHeap) -> (!Int,!(!Int,!*KindHeap))
	nomalize_var orig_kind_info (KI_VarBind kind_info_ptr) (kind_store, kind_heap)
		#! kind_info = sreadPtr kind_info_ptr kind_heap
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
			#! kind_info = sreadPtr kind_info_ptr kind_heap
			= nomalize_var kind_info_ptr kind_info (kind_store, kind_heap)
			
//	update_type_group_info :: ![Index] ![[TypeKind]] !TypeProperties ![Int] ![Int] !Int !*KindHeap !*{# CheckedTypeDef} -> (!*KindHeap,!*{# CheckedTypeDef})
	update_type_group_info [td:tds] [td_kinds : tds_kinds] type_properties top_vars group group_nr kind_store kind_heap td_infos
		# (kind_store, kind_heap, td_infos) = update_type_def_info td td_kinds type_properties top_vars group group_nr kind_store kind_heap td_infos
		= update_type_group_info tds tds_kinds type_properties top_vars group group_nr kind_store kind_heap td_infos
	update_type_group_info [] [] type_properties top_vars group group_nr kind_store kind_heap td_infos
		= (kind_heap, td_infos)

//	update_type_def_info :: !Int ![TypeKind] !TypeProperties ![Int] ![Int] !Int !*KindHeap !*{# CheckedTypeDef} -> (!Int,!*KindHeap,!*{# CheckedTypeDef}) 
	update_type_def_info {glob_module,glob_object} td_kinds type_properties top_vars group group_nr kind_store kind_heap td_infos
		# (td_info=:{tdi_kinds}, td_infos) = td_infos![glob_module].[glob_object]
		# (group_vars, cons_vars, kind_store, kind_heap) = determine_type_def_info tdi_kinds td_kinds top_vars kind_store kind_heap
		= (kind_store, kind_heap, { td_infos & [glob_module].[glob_object] =
				{td_info & tdi_properties = type_properties, tdi_kinds = td_kinds, tdi_group = group,
				 tdi_group_vars = group_vars, tdi_cons_vars = cons_vars, tdi_group_nr = group_nr } })
//					---> ("update_type_def_info", glob_module, glob_object, group_nr)
	where
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


analTypeDefs :: !{#CommonDefs} !*TypeHeaps !*ErrorAdmin -> (!*TypeDefInfos, !*TypeHeaps, !*ErrorAdmin)
analTypeDefs modules heaps error
//	#! modules = modules ---> "analTypeDefs"
	# sizes = [ size mod.com_type_defs - size mod.com_class_defs \\ mod <-: modules ]

	  check_marks		= { createArray nr_of_types AS_NotChecked \\ nr_of_types <- sizes }
	  type_def_infos	= { createArray nr_of_types EmptyTypeDefInfo \\ nr_of_types <- sizes }

	  as = {	as_check_marks = check_marks, as_kind_heap = newHeap, as_heaps = heaps, as_td_infos = type_def_infos,
				as_next_num = 0, as_deps = [], as_next_group_num = 0, as_error = error }

	  {as_td_infos,as_heaps,as_error} = anal_type_defs modules 0 sizes as
	= (as_td_infos, as_heaps, as_error)
where
	anal_type_defs modules mod_index [ size : sizes ] as
		# as = iFoldSt (anal_type_def modules mod_index) 0 size as
		= anal_type_defs modules (inc mod_index) sizes as
	anal_type_defs _ _ [] as
		= as


	anal_type_def modules mod_index type_index as=:{as_check_marks}
		| as_check_marks.[mod_index].[type_index] == AS_NotChecked
			# (_, (_, as)) = analTypeDef modules mod_index type_index as
			= as
			= as

instance == AttributeVar
where
	(==) av1 av2 = av1.av_info_ptr == av2.av_info_ptr

instance <<< DynamicType
where
	(<<<) file {dt_global_vars,dt_type} = file <<< dt_global_vars <<< dt_type
