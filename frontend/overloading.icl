implementation module overloading

import StdEnv

import syntax, check, type, typesupport, utilities, unitype, predef, RWSDebug


::	InstanceTree = IT_Node !(Global Index) !InstanceTree !InstanceTree | IT_Empty 

::	ClassInstanceInfo :== {# {! .InstanceTree}}

::	ReducedContext = 
	{	rc_class			:: !Global DefinedSymbol
	,	rc_types			:: ![Type]
	,	rc_inst_module		:: !Index
	,	rc_inst_members		:: !{# DefinedSymbol}
	,	rc_red_contexts		:: ![ClassApplication]
	}

::	ReducedContexts = 
	{	rcs_class_context			:: !ReducedContext
	,	rcs_constraints_contexts	:: ![ReducedContexts]
	}

::	TypeCodeInstance =
	{	tci_index			:: !Index
	,	tci_contexts		:: ![ClassApplication]
	}


::	ClassApplication	= CA_Instance !ReducedContexts
						| CA_Context !TypeContext
						| CA_LocalTypeCode !VarInfoPtr			/* for (local) type pattern variables */
						| CA_GlobalTypeCode !TypeCodeInstance	/* for (global) type constructors */


::	ArrayInstance =
	{	ai_record		:: !TypeSymbIdent
	,	ai_members		:: !{# DefinedSymbol}
	}

::	GlobalTCInstance =
	{	gtci_type		:: !GlobalTCType
	,	gtci_index		:: !Index
	}

::	SpecialInstances =
	{	si_next_array_member_index			:: !Index
	,	si_array_instances					:: ![ArrayInstance]
	,	si_next_TC_member_index				:: !Index
	,	si_TC_instances						:: ![GlobalTCInstance]
	}
	
::	LocalTypePatternVariable =
	{	ltpv_var			:: !Int
	,	ltpv_new_var		:: !VarInfoPtr
	}

::	LocalTypePatternVariables =
	{	ltp_var_heap			:: !.VarHeap
	,	ltp_variables			:: ![LocalTypePatternVariable]
	}

::	OverloadingState =
	{	os_type_heaps			:: !.TypeHeaps
	,	os_var_heap				:: !.VarHeap
	,	os_symbol_heap			:: !.ExpressionHeap
	,	os_predef_symbols		:: !.PredefinedSymbols
	,	os_special_instances	:: !.SpecialInstances
	,	os_error				:: !.ErrorAdmin				
	}

instance =< TypeSymbIdent
where	
	(=<) {type_index={glob_module=mod1,glob_object=index1}} {type_index={glob_module=mod2,glob_object=index2}}
		# cmp = mod1 =< mod2
		| cmp == Equal
			= index1 =< index2
			= cmp

instance =< GlobalTCType
where	
	(=<) globtype1 globtype2
		| equal_constructor globtype1 globtype2
			= compare_types  globtype1 globtype2
		| less_constructor globtype1 globtype2
			= Smaller
			= Greater
	where
		compare_types (GTT_Basic bt1) (GTT_Basic bt2)
			= bt1 =< bt2
		compare_types (GTT_Constructor cons1) (GTT_Constructor cons2) 
			= cons1 =< cons2
		compare_types _ _
			= Equal
		
		
instanceError symbol types err=:{ea_file,ea_loc}
	# ea_file = ea_file <<< "Overloading error " <<< hd ea_loc <<< ": \"" <<< symbol <<< "\" no instance available of type " <<< types <<< '\n'
	= { err & ea_file = ea_file, ea_ok = False}

contextError err=:{ea_file,ea_loc}
	# ea_file = ea_file <<< "Overloading Error " <<< hd ea_loc <<< ": specified context is too general\n"
	= { err & ea_file = ea_file, ea_ok = False}

uniqueError symbol types err=:{ea_file, ea_loc}
	# ea_file = ea_file <<< "Overloading/Uniqueness Error " <<< hd ea_loc <<< ": \"" <<< symbol <<< "\" uniqueness specification of instance conflicts with current application " <<< types <<< '\n'
	= { err & ea_file = ea_file, ea_ok = False}

unboxError type err=:{ea_file,ea_loc}
	# ea_file = ea_file <<< "Overloading error "  <<< hd ea_loc <<< ": instance cannot be unboxed" <<< type <<< '\n'
	= { err & ea_file = ea_file, ea_ok = False}

get :: !a !(Env a b) -> b | == a 
get elem_id [] 
		= abort "illegal access"
get elem_id [b : bs]
	| elem_id == b.bind_src
		= b.bind_dst
		= get elem_id bs

/*
	As soon as all overloaded variables in an type context are instantiated, context reduction is carried out.
	This reduction yields a type class instance (here represented by a an index) and a list of
	ClassApplications.
*/

simpleSubstitution type type_heaps
	= substitute type type_heaps

FoundObject object :== object.glob_module <> NotFound
ObjectNotFound 	:== { glob_module = NotFound, glob_object = NotFound }


reduceContexts :: ![TypeContext] !{# CommonDefs} !ClassInstanceInfo !*SpecialInstances !*LocalTypePatternVariables
	!*TypeHeaps !*Coercions !*PredefinedSymbols !*ErrorAdmin
		-> *(![ClassApplication], !*SpecialInstances, !*LocalTypePatternVariables, !*TypeHeaps, !*Coercions, !*PredefinedSymbols, !*ErrorAdmin)
reduceContexts [] defs instance_info special_instances type_pattern_vars type_heaps coercion_env predef_symbols error
	= ([], special_instances, type_pattern_vars, type_heaps, coercion_env, predef_symbols, error)
reduceContexts [tc : tcs] defs instance_info special_instances type_pattern_vars type_heaps coercion_env predef_symbols error
	# (appl, special_instances, type_pattern_vars, type_heaps, coercion_env, predef_symbols, error)
			= try_to_reduce_context tc defs instance_info special_instances type_pattern_vars type_heaps coercion_env predef_symbols error
	  (appls, special_instances, type_pattern_vars, type_heaps, coercion_env, predef_symbols, error)
	  		= reduceContexts tcs defs instance_info special_instances type_pattern_vars type_heaps coercion_env predef_symbols error
	= ([appl : appls], special_instances, type_pattern_vars, type_heaps, coercion_env, predef_symbols, error)

where		
	try_to_reduce_context :: !TypeContext !{# CommonDefs} !ClassInstanceInfo  !*SpecialInstances !*LocalTypePatternVariables
		!*TypeHeaps !*Coercions !*PredefinedSymbols !*ErrorAdmin
			-> *(!ClassApplication, !*SpecialInstances, !*LocalTypePatternVariables, !*TypeHeaps, !*Coercions, !*PredefinedSymbols, !*ErrorAdmin)
	try_to_reduce_context tc=:{tc_class=class_symb=:{glob_object={ds_index},glob_module},tc_types} defs instance_info
			special_instances type_pattern_vars type_heaps coercion_env predef_symbols error
		| is_reducible tc_types
			| is_predefined_symbol glob_module ds_index PD_TypeCodeClass predef_symbols
				# (red_context, (special_instances, type_pattern_vars)) = reduce_TC_context class_symb (hd tc_types) special_instances type_pattern_vars
				= (red_context, special_instances, type_pattern_vars, type_heaps, coercion_env, predef_symbols, error)
				# (class_appls, special_instances, type_pattern_vars, type_heaps, coercion_env, predef_symbols, error)
						= reduceContext tc defs instance_info special_instances type_pattern_vars
								type_heaps coercion_env predef_symbols error
				= (CA_Instance class_appls, special_instances, type_pattern_vars, type_heaps, coercion_env, predef_symbols, error)
			= (CA_Context tc, special_instances, type_pattern_vars, type_heaps, coercion_env, predef_symbols, error)

/*	reduceContext :: !ClassDef !InstanceTree ![Type] !{# CommonDefs} !ClassInstanceInfo !*SpecialInstances !*LocalTypePatternVariables
			!*TypeHeaps !*Coercions !*PredefinedSymbols !*ErrorAdmin
				-> *(![ReducedContext], !*SpecialInstances, !*LocalTypePatternVariables, !*TypeHeaps, !*Coercions, !*PredefinedSymbols, !*ErrorAdmin)
*/
	reduceContext {tc_class=class_symb=:{glob_object={ds_index},glob_module},tc_types} defs
						instance_info special_instances type_pattern_vars type_heaps coercion_env predef_symbols error
		# {class_members,class_context,class_args,class_name} = defs.[glob_module].com_class_defs.[ds_index]
		| size class_members > 0
			# class_instances = instance_info.[glob_module].[ds_index]
			# ({glob_module,glob_object}, contexts, uni_ok, type_heaps, coercion_env) = find_instance tc_types class_instances defs type_heaps coercion_env
			| (glob_module <> NotFound) && uni_ok
				# {ins_members, ins_class} = defs.[glob_module].com_instance_defs.[glob_object]
				| is_predefined_symbol ins_class.glob_module ins_class.glob_object.ds_index PD_ArrayClass predef_symbols &&
				  is_unboxed_array tc_types predef_symbols
					# (rcs_class_context, special_instances, predef_symbols, error)
							= check_unboxed_type glob_module ins_class ins_members tc_types class_members defs special_instances predef_symbols error
					= ({ rcs_class_context = rcs_class_context, rcs_constraints_contexts = []},
									special_instances, type_pattern_vars, type_heaps, coercion_env, predef_symbols, error)
					# (appls, special_instances, type_pattern_vars, type_heaps, coercion_env, predef_symbols, error)
							= reduceContexts contexts defs instance_info special_instances type_pattern_vars type_heaps coercion_env predef_symbols error
					  (constraints, special_instances, type_pattern_vars, type_heaps, coercion_env, predef_symbols, error)
					  		= reduceContextsInConstraints tc_types class_args class_context defs instance_info special_instances type_pattern_vars
					  				type_heaps coercion_env predef_symbols error

					= ({ rcs_class_context = { rc_class = ins_class, rc_inst_module = glob_module, rc_inst_members = ins_members,
								rc_types = tc_types, rc_red_contexts = appls }, rcs_constraints_contexts = constraints },
							special_instances, type_pattern_vars, type_heaps, coercion_env, predef_symbols, error)
				# rcs_class_context = { rc_class = class_symb, rc_inst_module = NoIndex, rc_inst_members = {}, rc_types = tc_types, rc_red_contexts = [] }
				| glob_module <> NotFound
					= ({ rcs_class_context = rcs_class_context, rcs_constraints_contexts = []},
							special_instances, type_pattern_vars, type_heaps, coercion_env, predef_symbols, uniqueError class_name tc_types error)
					= ({ rcs_class_context = rcs_class_context, rcs_constraints_contexts = []},
							special_instances, type_pattern_vars, type_heaps, coercion_env, predef_symbols, instanceError class_name tc_types error)
			# (constraints, special_instances, type_pattern_vars, type_heaps, coercion_env, predef_symbols, error)
				= reduceContextsInConstraints tc_types class_args class_context defs instance_info special_instances type_pattern_vars
					type_heaps coercion_env predef_symbols error
			= ({ rcs_class_context = { rc_class = class_symb, rc_inst_module = NoIndex, rc_inst_members = {}, rc_types = tc_types, rc_red_contexts = [] },
				rcs_constraints_contexts = constraints },  special_instances, type_pattern_vars, type_heaps, coercion_env, predef_symbols, error)

	reduceContextsInConstraints types class_args [] defs instance_info special_instances type_pattern_vars type_heaps coercion_env predef_symbols error
		= ([], special_instances, type_pattern_vars, type_heaps, coercion_env, predef_symbols, error)
	reduceContextsInConstraints types class_args class_context defs instance_info special_instances type_pattern_vars
			type_heaps=:{th_vars} coercion_env predef_symbols error
		# th_vars = fold2St (\ type {tv_info_ptr} -> writePtr tv_info_ptr (TVI_Type type)) types class_args th_vars
		  (instantiated_context, type_heaps) = substitute class_context { type_heaps & th_vars = th_vars }
		# (cappls, (special_instances, type_pattern_vars, type_var_heap, coercion_env, predef_symbols, error))
		  		= mapSt (reduce_context_in_constraint defs instance_info) instantiated_context
		  				(special_instances, type_pattern_vars, type_heaps, coercion_env, predef_symbols, error)
		= (cappls, special_instances, type_pattern_vars, type_var_heap, coercion_env, predef_symbols, error)

	where
		reduce_context_in_constraint defs instance_info tc (special_instances, type_pattern_vars, type_heaps, coercion_env, predef_symbols, error)
		  	# (cappls, special_instances, type_pattern_vars, type_var_heap, coercion_env, predef_symbols, error)
				= reduceContext tc defs instance_info special_instances
			  			type_pattern_vars type_heaps coercion_env predef_symbols error
			= (cappls, (special_instances, type_pattern_vars, type_var_heap, coercion_env, predef_symbols, error))

	find_instance co_types (IT_Node this_inst_index=:{glob_object,glob_module} left right) defs type_heaps coercion_env
		# (left_index, types, uni_ok, type_heaps, coercion_env) = find_instance co_types left defs type_heaps coercion_env
		| FoundObject left_index
			= (left_index, types, uni_ok, type_heaps, coercion_env)
			# {ins_type={it_types,it_context}, ins_specials} = defs.[glob_module].com_instance_defs.[glob_object]
			  (matched, type_heaps) = match defs it_types co_types type_heaps
			| matched
				# (subst_context, type_heaps) = simpleSubstitution it_context type_heaps
				  (uni_ok, coercion_env, type_heaps) = adjust_type_attributes defs co_types it_types coercion_env type_heaps
				  (spec_inst, type_heaps) = trySpecializedInstances subst_context (get_specials ins_specials) type_heaps
				| FoundObject spec_inst
					= (spec_inst, [], uni_ok, type_heaps, coercion_env)
					= (this_inst_index, subst_context, uni_ok, type_heaps, coercion_env)
				= find_instance co_types right defs type_heaps coercion_env
	find_instance co_types IT_Empty defs type_heaps coercion_env
		= (ObjectNotFound, [], True, type_heaps, coercion_env)
	
	get_specials (SP_ContextTypes specials) = specials
	get_specials SP_None 					= []

	adjust_type_attributes defs act_types form_types coercion_env type_heaps
		= fold2St (adjust_type_attribute defs) act_types form_types (True, coercion_env, type_heaps)

	adjust_type_attribute defs (TA type_cons1 cons_args1) (TA type_cons2 cons_args2) (ok, coercion_env, type_heaps)
		| type_cons1 == type_cons2
			# (ok, coercion_env) = fold2St adjust_attribute cons_args1 cons_args2 (ok, coercion_env)
			= (ok, coercion_env, type_heaps)
			# (_, type1, type_heaps) = tryToExpandTypeSyn defs type_cons1 cons_args1 type_heaps
			  (_, type2, type_heaps) = tryToExpandTypeSyn defs type_cons2 cons_args2 type_heaps
			= adjust_type_attribute defs type1 type2 (ok, coercion_env, type_heaps)
	adjust_type_attribute _ _ _  state
		= state
	
	adjust_attribute {at_attribute} {at_attribute = TA_Var _} state
		= state
	adjust_attribute {at_attribute} {at_attribute = TA_Unique} (ok, coercion_env)
		= case at_attribute of
			TA_Unique
				-> (ok, coercion_env)
			TA_TempVar av_number
				# (succ, coercion_env) = tryToMakeUnique av_number coercion_env
				-> (ok && succ, coercion_env)
			_
				-> (False, coercion_env)
	adjust_attribute {at_attribute} attr (ok, coercion_env)
		= case at_attribute of
			TA_Multi
				-> (ok, coercion_env)
			TA_TempVar av_number
				# (succ, coercion_env) = tryToMakeNonUnique av_number coercion_env
				-> (ok && succ, coercion_env)
			_
				-> (False, coercion_env)
	
	is_reducible []
		= True
	is_reducible [TempV _ : types]
		= False
	is_reducible [ _ :@: _ : types]
		= False
	is_reducible [ _ : types]
		= is_reducible types

	is_predefined_symbol mod_index symb_index predef_index predef_symbols
		# {pds_def,pds_module,pds_ident} = predef_symbols.[predef_index]
		= (mod_index == pds_module && symb_index == pds_def)
		
	is_unboxed_array [TA {type_index={glob_module,glob_object},type_arity} _ : _] predef_symbols
		= is_predefined_symbol glob_module glob_object PD_UnboxedArrayType predef_symbols
	is_unboxed_array _ predef_symbols
		= False


	check_unboxed_type ins_module ins_class ins_members types=:[ _, elem_type :_] class_members defs special_instances predef_symbols error
		# (unboxable, opt_record, predef_symbols) = try_to_unbox elem_type defs predef_symbols
		| unboxable
			= case opt_record of
				Yes record
					# (ins_members, special_instances) = add_record_to_array_instances record class_members special_instances
					-> ({ rc_class = ins_class, rc_inst_module = cIclModIndex, rc_inst_members = ins_members, rc_red_contexts = [], rc_types = types },
							special_instances, predef_symbols, error)
				No
					-> ({ rc_class = ins_class, rc_inst_module = ins_module, rc_inst_members = ins_members, rc_red_contexts = [], rc_types = types },
							special_instances, predef_symbols, error)
			= ({ rc_class = ins_class, rc_inst_module = ins_module, rc_inst_members = ins_members, rc_red_contexts = [], rc_types = types },
					special_instances, predef_symbols, unboxError elem_type error)
	where
		try_to_unbox (TB _) _ predef_symbols
			= (True, No, predef_symbols)
		try_to_unbox (TA type_symb=:{type_index={glob_module,glob_object},type_arity} _) defs predef_symbols
			# {td_arity,td_rhs} = defs.[glob_module].com_type_defs.[glob_object]
			= case td_rhs of
				RecordType _
					-> (True, (Yes type_symb), predef_symbols)
				AbstractType _
					#! unboxable =
						   is_predefined_symbol glob_module glob_object PD_LazyArrayType predef_symbols ||
						   is_predefined_symbol glob_module glob_object PD_StrictArrayType predef_symbols ||
						   is_predefined_symbol glob_module glob_object PD_UnboxedArrayType predef_symbols
					-> (unboxable, No, predef_symbols)
				_
					-> (False, No, predef_symbols)
				
		try_to_unbox type _ predef_symbols
			= (True, No, predef_symbols)

		add_record_to_array_instances :: !TypeSymbIdent !{# DefinedSymbol} !*SpecialInstances -> (!{#DefinedSymbol},!*SpecialInstances)
		add_record_to_array_instances record members special_instances=:{si_next_array_member_index,si_array_instances}
			# (inst_members, si_array_instances, si_next_array_member_index) = add_array_instance record members si_next_array_member_index si_array_instances
			= (inst_members, { special_instances & si_array_instances = si_array_instances, si_next_array_member_index = si_next_array_member_index })
		where
			add_array_instance :: !TypeSymbIdent !{# DefinedSymbol} !Index !u:[ArrayInstance]
				-> (!{#DefinedSymbol}, !u:[ArrayInstance], !Index)
			add_array_instance record members next_member_index instances=:[inst : insts]
				# cmp = record =< inst.ai_record
				| cmp == Equal
					= (inst.ai_members, instances, next_member_index)
				| cmp == Smaller
					# ai_members = { { class_member & ds_index = next_inst_index } \\
								class_member <-: members & next_inst_index <- [next_member_index .. ]}
					= (ai_members, [{ ai_members = ai_members, ai_record = record } : instances ], next_member_index + size members)
					# (found_inst, insts, next_member_index) = add_array_instance record members next_member_index insts
					= (found_inst, [inst : insts], next_member_index)
			add_array_instance record members next_member_index []
				# ai_members = { { class_member & ds_index = next_inst_index } \\
							class_member <-: members & next_inst_index <- [next_member_index .. ]}
				= (ai_members, [{ ai_members = ai_members, ai_record = record }], next_member_index + size members)


	reduce_TC_context type_code_class tc_type special_instances type_pattern_vars
		= reduce_tc_context type_code_class tc_type (special_instances, type_pattern_vars)
	where							
		reduce_tc_context type_code_class (TA cons_id cons_args) (special_instances=:{si_next_TC_member_index, si_TC_instances}, type_pattern_vars)
			# (inst_index, (si_next_TC_member_index, si_TC_instances))
			  		= addGlobalTCInstance (GTT_Constructor cons_id) (si_next_TC_member_index, si_TC_instances)
			  (rc_red_contexts, instances) = reduce_TC_contexts type_code_class cons_args
			  		 ({ special_instances & si_next_TC_member_index = si_next_TC_member_index, si_TC_instances = si_TC_instances }, type_pattern_vars)
			= (CA_GlobalTypeCode { tci_index = inst_index, tci_contexts = rc_red_contexts }, instances)

		reduce_tc_context type_code_class (TB basic_type) (special_instances=:{si_next_TC_member_index, si_TC_instances}, type_pattern_vars)
			# (inst_index, (si_next_TC_member_index, si_TC_instances))
			  		= addGlobalTCInstance (GTT_Basic basic_type) (si_next_TC_member_index, si_TC_instances)
			= (CA_GlobalTypeCode { tci_index = inst_index, tci_contexts = [] },
					({ special_instances & si_next_TC_member_index = si_next_TC_member_index, si_TC_instances = si_TC_instances }, type_pattern_vars))

		reduce_tc_context type_code_class (arg_type --> result_type) (special_instances=:{si_next_TC_member_index, si_TC_instances}, type_pattern_vars)
			# (inst_index, (si_next_TC_member_index, si_TC_instances))
			  		= addGlobalTCInstance GTT_Function (si_next_TC_member_index, si_TC_instances)
			  (rc_red_contexts, instances) = reduce_TC_contexts type_code_class [arg_type, result_type]
			  		 ({ special_instances & si_next_TC_member_index = si_next_TC_member_index, si_TC_instances = si_TC_instances }, type_pattern_vars)
			= (CA_GlobalTypeCode { tci_index = inst_index, tci_contexts = rc_red_contexts }, instances)


		reduce_tc_context type_code_class (TempQV var_number) (special_instances, type_pattern_vars)
			# (inst_var, type_pattern_vars) = addLocalTCInstance var_number type_pattern_vars
			= (CA_LocalTypeCode inst_var, (special_instances, type_pattern_vars))

		reduce_tc_context type_code_class (TempV var_number) instances
			= (CA_Context { tc_class = type_code_class, tc_types = [TempV var_number], tc_var = nilPtr }, instances)
		

		reduce_TC_contexts type_code_class cons_args instances
			= mapSt (\{at_type} -> reduce_tc_context type_code_class at_type) cons_args instances
		
addLocalTCInstance var_number ltp=:{ltp_variables=instances=:[inst : insts], ltp_var_heap}
	# cmp = var_number =< inst.ltpv_var
	| cmp == Equal
		= (inst.ltpv_new_var, ltp)
	| cmp == Smaller
		# (ltpv_new_var, ltp_var_heap) = newPtr VI_Empty ltp_var_heap
		= (ltpv_new_var, { ltp_variables = [{ ltpv_new_var = ltpv_new_var, ltpv_var = var_number } : instances ], ltp_var_heap = ltp_var_heap })
		# (found_var, ltp) = addLocalTCInstance var_number { ltp & ltp_variables = insts }
		= (found_var, { ltp & ltp_variables = [inst :ltp.ltp_variables ] })
addLocalTCInstance var_number {ltp_variables = [], ltp_var_heap}
	# (ltpv_new_var, ltp_var_heap) = newPtr VI_Empty ltp_var_heap
	= (ltpv_new_var, { ltp_variables = [{ ltpv_new_var = ltpv_new_var, ltpv_var = var_number }], ltp_var_heap = ltp_var_heap })

addGlobalTCInstance type_of_TC (next_member_index, instances=:[inst : insts])
	# cmp = type_of_TC =< inst.gtci_type
	| cmp == Equal
		= (inst.gtci_index, (next_member_index, instances))
	| cmp == Smaller
		= (next_member_index, (inc next_member_index, [{ gtci_index = next_member_index, gtci_type = type_of_TC } : instances ]))
		# (found_inst, (next_member_index, insts)) = addGlobalTCInstance type_of_TC (next_member_index, insts)
		= (found_inst, (next_member_index, [inst : insts]))
addGlobalTCInstance type_of_TC (next_member_index, [])
	= (next_member_index, (inc next_member_index, [{ gtci_index = next_member_index, gtci_type = type_of_TC }]))

tryToExpandTypeSyn defs cons_id=:{type_name,type_index={glob_object,glob_module}} type_args type_heaps
	# {td_name,td_rhs,td_args} = defs.[glob_module].com_type_defs.[glob_object]
	| is_synonym_type td_rhs
		# (SynType {at_type}) = td_rhs
		  type_heaps = fold2St bind_var td_args type_args type_heaps
		  (expanded_type, type_heaps) = substitute at_type type_heaps
		= (True, expanded_type, type_heaps)
		= (False, TA cons_id type_args, type_heaps)
where
	is_synonym_type (SynType _)
		= True
	is_synonym_type type_rhs
		= False

	bind_var {atv_attribute = TA_Var {av_info_ptr}, atv_variable={tv_info_ptr}} {at_attribute, at_type} type_heaps=:{th_vars,th_attrs}
		= { type_heaps & th_vars = th_vars <:= (tv_info_ptr, TVI_Type at_type), th_attrs = th_attrs <:= (av_info_ptr, AVI_Attr at_attribute) }
	bind_var {atv_variable={tv_info_ptr}} {at_type} type_heaps=:{th_vars}
		= { type_heaps & th_vars = th_vars <:= (tv_info_ptr, TVI_Type at_type) }
		
class match type ::  !{# CommonDefs} !type !type !*TypeHeaps -> (!Bool, !*TypeHeaps)

instance match AType
where
	match defs atype1 atype2 type_heaps = match defs atype1.at_type atype2.at_type type_heaps

instance match Type
where 
	match defs (TV {tv_info_ptr}) type type_heaps=:{th_vars}
		= (True, { type_heaps & th_vars = th_vars <:= (tv_info_ptr,TVI_Type type)})
	match defs (TA cons_id1 cons_args1) (TA cons_id2 cons_args2) type_heaps
		| cons_id1 == cons_id2
			= match defs cons_args1 cons_args2 type_heaps
//			# (succ1, type1, type_heaps) = tryToExpandTypeSyn defs cons_id1 cons_args1 type_heaps
			# (succ2, type2, type_heaps) = tryToExpandTypeSyn defs cons_id2 cons_args2 type_heaps
			| succ2
				= case type2 of
					TA cons_id2 cons_args2
						| cons_id1 == cons_id2
							-> match defs cons_args1 cons_args2 type_heaps
							-> (False, type_heaps)
					_
							-> (False, type_heaps)
				= (False, type_heaps)
	match defs (arg_type1 --> res_type1) (arg_type2 --> res_type2) type_heaps
		= match defs (arg_type1,res_type1) (arg_type2,res_type2) type_heaps
	match defs (type1 :@: types1) (type2 :@: types2) type_heaps
		= match defs (type1,types1) (type2,types2) type_heaps
	match defs (CV tv :@: types) (TA type_cons cons_args) type_heaps
		# diff = type_cons.type_arity - length types
		| diff >= 0
			= match defs (TV tv, types) (TA { type_cons & type_arity = diff } (take diff cons_args), drop diff cons_args) type_heaps
			= (False, type_heaps)
	match defs (TB tb1) (TB tb2) type_heaps
		= (tb1 == tb2, type_heaps)
/*	match defs type (TB (BT_String array_type)) type_heaps
		= match defs type array_type type_heaps
*/	match defs (TA cons_id cons_args) type2 type_heaps
		# (succ, type1, type_heaps) = tryToExpandTypeSyn defs cons_id cons_args type_heaps
		| succ
			= match defs type1 type2 type_heaps
			= (False, type_heaps)
	match defs type1 (TA cons_id cons_args) type_heaps
		# (succ, type2, type_heaps) = tryToExpandTypeSyn defs cons_id cons_args type_heaps
		| succ
			= match defs type1 type2 type_heaps
			= (False, type_heaps)
	match defs type1 type2 type_heaps
		= (False, type_heaps)

instance match (!a,!b) | match a & match b
where
	match defs (x1,y1) (x2,y2) type_heaps
		# (matched, type_heaps) = match defs x1 x2 type_heaps
		| matched
			= match defs y1 y2 type_heaps
			= (False, type_heaps)
			
instance match [a] | match a
where
	match defs [t1 : ts1] [t2 : ts2] type_heaps
		= match defs (t1,ts1) (t2,ts2) type_heaps
	match defs [] [] type_heaps
		= (True, type_heaps)

instance match ConsVariable
where
	match defs (CV {tv_info_ptr}) cons_var type_heaps=:{th_vars}
		= (True, { type_heaps & th_vars = th_vars <:= (tv_info_ptr,TVI_Type (consVariableToType cons_var))})

consVariableToType (TempCV temp_var_id)
	= TempV temp_var_id
consVariableToType (TempQCV temp_var_id)
	= TempQV temp_var_id

trySpecializedInstances type_contexts [] type_heaps
	= (ObjectNotFound, type_heaps)
trySpecializedInstances type_contexts specials type_heaps=:{th_vars}
	# (spec_index, th_vars) = try_specialized_instances (map (\{tc_types} -> tc_types) type_contexts) specials th_vars
	= (spec_index, { type_heaps & th_vars = th_vars })
where

	try_specialized_instances type_contexts_types [{spec_index,spec_vars,spec_types} : specials] type_var_heap
		# type_var_heap = foldSt (\tv -> writePtr tv.tv_info_ptr TVI_Empty) spec_vars type_var_heap
		  (equ, type_var_heap) = equalTypes spec_types type_contexts_types type_var_heap
		| equ
			= (spec_index, type_var_heap)
			= try_specialized_instances type_contexts_types specials type_var_heap
	try_specialized_instances type_contexts_types [] type_var_heap
		= (ObjectNotFound, type_var_heap)

tryToSolveOverloading :: ![(Optional [TypeContext], [ExprInfoPtr], IdentPos)] !{# CommonDefs } !ClassInstanceInfo !*Coercions !*OverloadingState
	-> (![TypeContext], !*Coercions, ![LocalTypePatternVariable], !*OverloadingState)
tryToSolveOverloading ocs defs instance_info coercion_env os
	= foldSt (try_to_solve_overloading defs instance_info) ocs ([], coercion_env, [], os)
where

	try_to_solve_overloading  defs instance_info (fun_context, call_ptrs, location) (contexts, coercion_env, type_pattern_vars, os=:{os_error})
		| isEmpty call_ptrs
			= (contexts, coercion_env, type_pattern_vars, os)
			# os = { os & os_error = setErrorAdmin location os_error }
			= case fun_context of
				Yes specified_context
					# (_, coercion_env, type_pattern_vars, os)
						= reduce_and_simplify_contexts call_ptrs defs instance_info True specified_context coercion_env type_pattern_vars os
					-> (contexts, coercion_env, type_pattern_vars, os)
//							---> ("try_to_solve_overloading (Yes ...)", specified_context)
				No
					-> reduce_and_simplify_contexts call_ptrs defs instance_info False contexts coercion_env type_pattern_vars os
//							---> ("try_to_solve_overloading (No)", contexts)
		
	reduce_and_simplify_contexts :: ![ExprInfoPtr] !{# CommonDefs } !ClassInstanceInfo !Bool ![TypeContext] !*Coercions ![LocalTypePatternVariable]
			!*OverloadingState -> (![TypeContext], !*Coercions, ![LocalTypePatternVariable], !*OverloadingState)
	reduce_and_simplify_contexts [over_info_ptr : ocs] defs instance_info has_context contexts coercion_env type_pattern_vars os=:{os_symbol_heap, os_type_heaps}
		# (EI_Overloaded {oc_symbol, oc_context, oc_specials}, os_symbol_heap) = readPtr over_info_ptr os_symbol_heap
		  (glob_fun, os_type_heaps) = trySpecializedInstances oc_context oc_specials os_type_heaps
		| FoundObject glob_fun
			# os_symbol_heap = os_symbol_heap <:= (over_info_ptr, EI_Instance {glob_module = glob_fun.glob_module, glob_object =
									{ ds_ident =  oc_symbol.symb_name, ds_arity = 0, ds_index = glob_fun.glob_object }} [])
			= reduce_and_simplify_contexts ocs defs instance_info has_context contexts coercion_env type_pattern_vars
					{ os & os_type_heaps = os_type_heaps, os_symbol_heap = os_symbol_heap }
			# (appls, os_special_instances, {ltp_var_heap, ltp_variables}, os_type_heaps, coercion_env, os_predef_symbols, os_error)
					= reduceContexts oc_context defs instance_info os.os_special_instances {ltp_var_heap = os.os_var_heap, ltp_variables = type_pattern_vars}
							os_type_heaps coercion_env os.os_predef_symbols os.os_error
			| os_error.ea_ok
				# (contexts, os_type_heaps, os_var_heap, os_symbol_heap, os_error)
					= simplifyOverloadedCall oc_symbol over_info_ptr appls defs has_context contexts os_type_heaps ltp_var_heap os_symbol_heap os_error
				= reduce_and_simplify_contexts ocs defs instance_info has_context contexts coercion_env ltp_variables { os &
						os_type_heaps = os_type_heaps, os_var_heap = os_var_heap, os_symbol_heap = os_symbol_heap,
						os_predef_symbols = os_predef_symbols, os_special_instances = os_special_instances, os_error = os_error }

				= reduce_and_simplify_contexts ocs defs instance_info has_context contexts coercion_env ltp_variables
						{ os & os_type_heaps = os_type_heaps, os_predef_symbols = os_predef_symbols, os_symbol_heap = os_symbol_heap,
							os_special_instances = os_special_instances, os_error = os_error, os_var_heap = ltp_var_heap}
	reduce_and_simplify_contexts [] defs instance_info has_context contexts coercion_env type_pattern_vars os
		= (contexts, coercion_env, type_pattern_vars, os)

/*	
RecordName = { id_name = "_Record", id_info = nilPtr }

InternalSelectSymbol = { symb_name = {id_name = "_Select", id_info = nilPtr },
						 symb_kind = SK_InternalFunction (-1), symb_arity = 2 }
*/

selectFromDictionary  dict_mod dict_index member_index defs
	# (RecordType {rt_fields}) = defs.[dict_mod].com_type_defs.[dict_index].td_rhs
	  { fs_name, fs_index } = rt_fields.[member_index]
	= { glob_module = dict_mod, glob_object = { ds_ident = fs_name, ds_index = fs_index, ds_arity = 1 }}

getDictionaryConstructor {glob_module, glob_object = {ds_ident,ds_index}} defs	  
	# {class_dictionary} = defs.[glob_module].com_class_defs.[ds_index]
	  (RecordType {rt_constructor}) = defs.[glob_module].com_type_defs.[class_dictionary.ds_index].td_rhs
	= rt_constructor

simplifyOverloadedCall {symb_kind = SK_OverloadedFunction {glob_module,glob_object}, symb_arity} expr_info_ptr [class_appl:class_appls]
		defs has_context contexts type_heaps var_heap symbol_heap error
	# mem_def = defs.[glob_module].com_member_defs.[glob_object]
	# (class_exprs, (contexts, heaps, error)) = convertClassApplsToExpressions defs has_context class_appls (contexts, (type_heaps, var_heap, symbol_heap), error)
	  (inst_expr, contexts, (type_heaps, var_heap, symbol_heap), error)
	  		= adjust_member_application mem_def symb_arity class_appl class_exprs defs has_context contexts heaps error
	= (contexts, type_heaps, var_heap, symbol_heap <:= (expr_info_ptr, inst_expr), error)

where
	adjust_member_application {me_symb,me_offset,me_class} symb_arity (CA_Instance red_contexts) class_exprs defs has_context contexts heaps error
		# ({glob_module,glob_object}, red_contexts) = find_instance_of_member me_class me_offset red_contexts
		  (exprs, (contexts, heaps, error)) = convertClassApplsToExpressions defs has_context red_contexts (contexts, heaps, error)
		  class_exprs = exprs ++ class_exprs
		= (EI_Instance { glob_module = glob_module, glob_object = { ds_ident = me_symb, ds_arity = length class_exprs, ds_index = glob_object }}
				 class_exprs, contexts, heaps, error)
	adjust_member_application {me_symb,me_offset,me_class={glob_module,glob_object}} symb_arity (CA_Context tc)
			class_exprs defs has_context contexts (type_heaps, var_heap, symbol_heap) error
		# (class_context, address, contexts, type_heaps, var_heap, error)
				= determineContextAddress tc has_context contexts defs type_heaps var_heap error
		  {class_dictionary={ds_index}} = defs.[glob_module].com_class_defs.[glob_object]
		  selector = selectFromDictionary glob_module ds_index me_offset defs
		= (EI_Selection (generateClassSelection address [RecordSelection selector me_offset]) (createBoundVar class_context) class_exprs,
				contexts, (type_heaps, var_heap, symbol_heap), error)

	adjust_member_application _ _ (CA_GlobalTypeCode {tci_index,tci_contexts}) _ defs has_context contexts heaps error
		# (exprs, (contexts, heaps, error)) = convertClassApplsToExpressions defs has_context tci_contexts (contexts, heaps, error)
		= (EI_TypeCode (TCE_Constructor tci_index (map expressionToTypeCodeExpression exprs)), contexts, heaps, error)
	adjust_member_application _ _ (CA_LocalTypeCode new_var_ptr) _ defs has_context contexts heaps error
		= (EI_TypeCode (TCE_Var new_var_ptr), contexts, heaps, error)
	
	find_instance_of_member me_class me_offset { rcs_class_context = {rc_class, rc_inst_module, rc_inst_members, rc_red_contexts}, rcs_constraints_contexts}
		| rc_class.glob_module == me_class.glob_module && rc_class.glob_object.ds_index == me_class.glob_object
			= ({ glob_module = rc_inst_module, glob_object = rc_inst_members.[me_offset].ds_index }, rc_red_contexts)
			= find_instance_of_member_in_constraints me_class me_offset rcs_constraints_contexts
	where
		find_instance_of_member_in_constraints me_class me_offset [ rcs=:{rcs_constraints_contexts} : rcss ]
			= find_instance_of_member me_class me_offset {rcs & rcs_constraints_contexts = rcs_constraints_contexts ++ rcss}
		find_instance_of_member_in_constraints me_class me_offset []
			= abort "Error in module overloading: find_instance_of_member_in_constraints\n"

simplifyOverloadedCall {symb_kind = SK_TypeCode} expr_info_ptr class_appls defs has_context contexts type_heaps var_heap symbol_heap error
	# (class_expressions, (contexts, (type_heaps, var_heap, symbol_heap), error))
			= convertClassApplsToExpressions defs has_context class_appls (contexts, (type_heaps, var_heap, symbol_heap), error)
	= (contexts, type_heaps, var_heap, symbol_heap <:= (expr_info_ptr, EI_TypeCodes (map expressionToTypeCodeExpression class_expressions)), error)	
simplifyOverloadedCall _ expr_info_ptr appls defs has_context contexts type_heaps var_heap symbol_heap error
	# (class_expressions, (contexts, (type_heaps, var_heap, symbol_heap), error))
			= convertClassApplsToExpressions defs has_context appls (contexts, (type_heaps, var_heap, symbol_heap), error)
	= (contexts, type_heaps, var_heap, symbol_heap <:= (expr_info_ptr, EI_Context class_expressions), error)


expressionToTypeCodeExpression (TypeCodeExpression texpr) 			= texpr
expressionToTypeCodeExpression (Var {var_info_ptr})					= TCE_Var var_info_ptr

generateClassSelection address last_selectors
	= mapAppend (\(off_set,selector) -> RecordSelection selector off_set) address last_selectors
	
convertClassApplsToExpressions defs has_context cl_appls contexts_heaps_error
	= mapSt (convert_class_appl_to_expression defs has_context) cl_appls contexts_heaps_error
where
	convert_class_appl_to_expression defs has_context (CA_Instance {rcs_class_context,rcs_constraints_contexts}) contexts_heaps_error
		# (class_symb, class_members, instance_types, contexts_heaps_error)
				= convert_reduced_context_to_expression defs has_context rcs_class_context contexts_heaps_error
		  (members_of_constraints, (contexts, (type_heaps, var_heap, expr_heap), error))
		  		= convert_list_of_reduced_contexts_to_expressions defs has_context rcs_constraints_contexts contexts_heaps_error
		  {ds_ident,ds_index,ds_arity} = getDictionaryConstructor class_symb defs
		  record_symbol = { symb_name = ds_ident, symb_kind = SK_Constructor {glob_module = class_symb.glob_module, glob_object = ds_index}, symb_arity = ds_arity }
		  (app_info_ptr, expr_heap) = newPtr (EI_ClassTypes instance_types) expr_heap
		= (App { app_symb = record_symbol, app_args = class_members ++ members_of_constraints, app_info_ptr = app_info_ptr },
				(contexts, (type_heaps, var_heap, expr_heap), error))
	convert_class_appl_to_expression defs has_context (CA_Context tc) (contexts, (type_heaps, var_heap, expr_heap), error)
		# (class_context, context_address, contexts, type_heaps, var_heap, error)
				= determineContextAddress tc has_context contexts defs type_heaps var_heap error
		| isEmpty context_address
			= (Var (createBoundVar class_context), (contexts, (type_heaps, var_heap, expr_heap), error))
			= (Selection No (Var (createBoundVar class_context)) (generateClassSelection context_address []), (contexts, (type_heaps, var_heap, expr_heap), error))
	convert_class_appl_to_expression defs has_context (CA_LocalTypeCode new_var_ptr) contexts_heaps_error
		= (TypeCodeExpression (TCE_Var new_var_ptr), contexts_heaps_error)
	convert_class_appl_to_expression defs has_context (CA_GlobalTypeCode {tci_index,tci_contexts}) contexts_heaps_error
		# (exprs, contexts_heaps_error) = convertClassApplsToExpressions defs has_context tci_contexts contexts_heaps_error
		= (TypeCodeExpression (TCE_Constructor tci_index (map expressionToTypeCodeExpression exprs)), contexts_heaps_error)

	convert_reduced_context_to_expression defs has_context {rc_class, rc_inst_module, rc_inst_members, rc_red_contexts, rc_types} contexts_heaps_error
		# (expressions, contexts_heaps_error) = convertClassApplsToExpressions defs has_context rc_red_contexts contexts_heaps_error
		  members = build_class_members 0 rc_inst_members rc_inst_module expressions (length expressions)
		= (rc_class, members, rc_types, contexts_heaps_error)
	where
		build_class_members mem_offset ins_members mod_index class_arguments arity
			| mem_offset == size ins_members
				= []
				# expressions = build_class_members (inc mem_offset) ins_members mod_index class_arguments arity
				  {ds_ident,ds_index} = ins_members.[mem_offset]
				= [ App { app_symb = { symb_name = ds_ident, symb_kind = SK_Function { glob_object = ds_index, glob_module = mod_index },
						symb_arity = arity }, app_args = class_arguments, app_info_ptr = nilPtr } : expressions ]

	convert_list_of_reduced_contexts_to_expressions defs has_context list_of_rcs contexts_heaps_error
		= mapSt (convert_reduced_contexts_to_expressions defs has_context) list_of_rcs contexts_heaps_error

	convert_reduced_contexts_to_expressions defs has_context {rcs_class_context,rcs_constraints_contexts} contexts_heaps_error
		# (class_symb, rc_exprs, instance_types, contexts_heaps_error)
				= convert_reduced_context_to_expression defs has_context rcs_class_context contexts_heaps_error
		  (rcs_exprs, (contexts, (type_heaps, var_heap, expr_heap), error))
				= convert_list_of_reduced_contexts_to_expressions defs has_context rcs_constraints_contexts contexts_heaps_error
		  {ds_ident,ds_index,ds_arity} = getDictionaryConstructor class_symb defs
		  record_symbol = { symb_name = ds_ident, symb_kind = SK_Constructor {glob_module = class_symb.glob_module, glob_object = ds_index}, symb_arity = ds_arity }
		  (app_info_ptr, expr_heap) = newPtr (EI_ClassTypes instance_types) expr_heap
		  rc_record = App { app_symb = record_symbol, app_args = rc_exprs ++ rcs_exprs, app_info_ptr = app_info_ptr }
		= (rc_record, (contexts, (type_heaps, var_heap, expr_heap), error))
	
createBoundVar :: !TypeContext -> BoundVar
createBoundVar {tc_class={glob_object={ds_ident}}, tc_var}
	| isNilPtr tc_var
		= abort ("createBoundVar : NIL ptr" ---> ds_ident)
		= { var_name = { id_name = "_v" +++ ds_ident.id_name, id_info = nilPtr }, var_info_ptr = tc_var, var_expr_ptr = nilPtr }

createFreeVar :: !TypeContext -> FreeVar
createFreeVar {tc_class={glob_object={ds_ident}}, tc_var}
	| isNilPtr tc_var
		= abort ("createFreeVar : NIL ptr" ---> ds_ident)
		= { fv_name = { id_name = "_v" +++ ds_ident.id_name, id_info = nilPtr }, fv_info_ptr = tc_var, fv_def_level = NotALevel, fv_count = -1 }


determineContextAddress :: !TypeContext !Bool ![TypeContext] !{#CommonDefs} !*TypeHeaps !*VarHeap !*ErrorAdmin
	-> (!TypeContext, ![(Int, Global DefinedSymbol)], ![TypeContext], !*TypeHeaps, !*VarHeap, !*ErrorAdmin)
determineContextAddress tc has_context contexts defs type_heaps var_heap error
	= determine_context_and_address tc contexts has_context contexts defs type_heaps var_heap error
where
	determine_context_and_address :: !TypeContext ![TypeContext] !Bool ![TypeContext] !{#CommonDefs} !*TypeHeaps !*VarHeap !*ErrorAdmin
			-> (!TypeContext, ![(Int, Global DefinedSymbol)], ![TypeContext], !*TypeHeaps, !*VarHeap, !*ErrorAdmin)
	determine_context_and_address context [] has_context contexts defs type_heaps var_heap error
		| has_context
			= (context, [], contexts, type_heaps, var_heap, contextError error)
			#! (new_info_ptr, var_heap) = newPtr VI_Empty var_heap
			# new_context = { context & tc_var = new_info_ptr}
			= (new_context, [], [new_context : contexts], type_heaps, var_heap, error)
	determine_context_and_address context [tc : tcs] has_context contexts defs type_heaps var_heap error
		#! (may_be_addres, type_heaps) = determine_address context tc [] defs type_heaps
		= case may_be_addres of
			Yes address
				| isNilPtr tc.tc_var
					-> abort ("determine_context_and_address" ---> tc.tc_class.glob_object.ds_ident)
					-> (tc, address, contexts, type_heaps, var_heap, error)
			No
				-> determine_context_and_address context tcs has_context contexts defs type_heaps var_heap error

	determine_address :: !TypeContext !TypeContext ![(Int, Global DefinedSymbol)] !{#CommonDefs} !*TypeHeaps
		-> (!Optional [(Int, Global DefinedSymbol)],!*TypeHeaps)
	determine_address tc1 tc2 address defs type_heaps=:{th_vars}
		| tc1 == tc2
			= (Yes address, type_heaps)
			# {tc_class={glob_object={ds_index},glob_module}} = tc2
			  {class_args,class_members,class_context,class_dictionary} = defs.[glob_module].com_class_defs.[ds_index]
			  th_vars = foldr2 (\{tv_info_ptr} type -> writePtr tv_info_ptr (TVI_Type type)) th_vars class_args tc2.tc_types
			  (super_instances, type_heaps) = substitute class_context { type_heaps & th_vars = th_vars } 
			= find_super_instance tc1 super_instances (size class_members) address glob_module class_dictionary.ds_index defs type_heaps

	find_super_instance :: !TypeContext ![TypeContext] !Index ![(Int, Global DefinedSymbol)] !Index !Index !{#CommonDefs} !*TypeHeaps
		-> (!Optional [(Int, Global DefinedSymbol)],!*TypeHeaps)
	find_super_instance context [] tc_index address dict_mod dict_index defs type_heaps
		= (No, type_heaps)
	find_super_instance context [tc : tcs] tc_index address dict_mod dict_index defs type_heaps
		#! (may_be_addres, type_heaps) = determine_address context tc address defs type_heaps
		= case may_be_addres of
			Yes address
				# selector = selectFromDictionary dict_mod dict_index tc_index defs
				-> (Yes [ (tc_index, selector) : address ], type_heaps)
			No
				-> find_super_instance context tcs (inc tc_index) address  dict_mod dict_index defs type_heaps

updateDynamics :: ![Int] ![TypeContext] ![LocalTypePatternVariable] !*{#FunDef} !*ExpressionHeap !*TypeCodeInfo !*VarHeap !*ErrorAdmin
	-> (!*{#FunDef}, !*ExpressionHeap, !*TypeCodeInfo, !*VarHeap, !*ErrorAdmin)
updateDynamics funs type_contexts type_pattern_vars fun_defs symbol_heap type_code_info var_heap error
	| error.ea_ok
		= update_dynamics funs type_contexts fun_defs symbol_heap type_code_info { ltp_var_heap = var_heap, ltp_variables = type_pattern_vars} error
		= (fun_defs, symbol_heap, type_code_info, var_heap, error)	
where
	update_dynamics [] type_contexts fun_defs symbol_heap type_code_info ltp error
		= (fun_defs, symbol_heap, type_code_info, ltp.ltp_var_heap,  error)
	update_dynamics [fun:funs] type_contexts fun_defs symbol_heap type_code_info ltp error
		#! fun_def = fun_defs.[fun]
		# {fun_body,fun_info={fi_group_index, fi_dynamics}} = fun_def
		| isEmpty fi_dynamics
			= update_dynamics funs type_contexts fun_defs symbol_heap type_code_info ltp error
		  	# (type_code_info, symbol_heap, ltp) = convertDynamicTypes fi_dynamics (type_code_info, symbol_heap, ltp)
		  	  (TransformedBody tb) = fun_body
		  	  (tb_rhs, {ui_instance_calls, ui_symbol_heap, ui_fun_defs})
		  	  		= updateExpression fi_group_index [] tb.tb_rhs {  ui_instance_calls = [], ui_symbol_heap = symbol_heap, ui_fun_defs = fun_defs }
		 	  fun_def = { fun_def & fun_body = TransformedBody {tb & tb_rhs = tb_rhs}}
			= update_dynamics funs type_contexts { ui_fun_defs & [fun] = fun_def } ui_symbol_heap type_code_info ltp error

removeOverloadedFunctions :: ![Int] ![(Optional [TypeContext], IdentPos)] ![TypeContext] ![LocalTypePatternVariable] !*{#FunDef} !*ExpressionHeap
	!*TypeCodeInfo !*VarHeap !*ErrorAdmin
		-> (!*{#FunDef}, !*ExpressionHeap, !*TypeCodeInfo, !*VarHeap, !*ErrorAdmin)
removeOverloadedFunctions funs opt_spec_contexts type_contexts type_pattern_vars fun_defs symbol_heap type_code_info var_heap error
	| error.ea_ok
		= remove_overloaded_functions funs opt_spec_contexts type_contexts fun_defs symbol_heap type_code_info
				{ ltp_var_heap = var_heap, ltp_variables = type_pattern_vars} error
		= (fun_defs, symbol_heap, type_code_info, var_heap, error)	
where	
	remove_overloaded_functions :: ![Int] ![(Optional [TypeContext], IdentPos)] ![TypeContext] !*{#FunDef} !*ExpressionHeap !*TypeCodeInfo
		!*LocalTypePatternVariables !*ErrorAdmin
			-> (!*{#FunDef}, !*ExpressionHeap, !*TypeCodeInfo, !*VarHeap, !*ErrorAdmin)
	remove_overloaded_functions [] opt_contexts type_contexts fun_defs symbol_heap type_code_info ltp error
		= (fun_defs, symbol_heap, type_code_info, ltp.ltp_var_heap,  error)
	remove_overloaded_functions [fun:funs] [(opt_context, location):opt_contexts] type_contexts fun_defs symbol_heap type_code_info ltp error
		#! fun_def = fun_defs.[fun]
		# {fun_body = TransformedBody {tb_args,tb_rhs},fun_info,fun_arity,fun_symb} = fun_def
		  error = setErrorAdmin location error
		  (type_code_info, symbol_heap, ltp) = convertDynamicTypes fun_info.fi_dynamics (type_code_info, symbol_heap, ltp)
		  tb_args = determine_class_arguments opt_context type_contexts tb_args
		  (tb_rhs, {ui_instance_calls, ui_symbol_heap, ui_fun_defs}) = updateExpression fun_info.fi_group_index type_contexts tb_rhs
		  							{  ui_instance_calls = [], ui_symbol_heap = symbol_heap, ui_fun_defs = fun_defs }
		  fun_def = { fun_def & fun_body = TransformedBody {tb_args = tb_args, tb_rhs = tb_rhs},
		  								  fun_arity = length tb_args, fun_info = { fun_info & fi_calls = fun_info.fi_calls ++ ui_instance_calls } }
		= remove_overloaded_functions funs opt_contexts type_contexts { ui_fun_defs & [fun] = fun_def } ui_symbol_heap type_code_info ltp error

	determine_class_arguments (Yes spec_context) _ tb_args
		= mapAppend (\tc -> createFreeVar tc) spec_context tb_args
	determine_class_arguments No type_contexts tb_args
		= mapAppend (\tc -> createFreeVar tc) type_contexts tb_args

/*	
	type_contexts fun_symb fun_info_ptr tb_args symbol_heap error
		#! fun_info = sreadPtr fun_info_ptr symbol_heap
		= case fun_info of
			EI_Empty
				-> (mapAppend (\tc -> createFreeVar tc) type_contexts tb_args, symbol_heap, error)
			EI_Context class_expressions
				# (tb_args, error) = convert_class_expressions fun_symb class_expressions tb_args error
				-> (tb_args, symbol_heap, error)
			_
//				-> (tb_args, symbol_heap, contextError fun_symb error)
				-> (tb_args, symbol_heap, contextError error)
				
	convert_class_expressions fun_symb [] tb_args error
		= (tb_args, error)
	convert_class_expressions fun_symb [Var {var_name,var_info_ptr} : class_exprs] tb_args error
		# (tb_args, error) = convert_class_expressions fun_symb class_exprs tb_args error
		= ([ { fv_name = var_name, fv_info_ptr = var_info_ptr, fv_def_level = NotALevel, fv_count = -1 } : tb_args], error)
	convert_class_expressions fun_symb [class_expr : class_exprs] tb_args error
//		= (tb_args, contextError fun_symb error)
		= (tb_args, contextError error)
*/
convertDynamicTypes dyn_ptrs update_info
	= foldSt update_dynamic dyn_ptrs update_info
where		
	update_dynamic dyn_ptr (type_code_info, expr_heap, local_type_pattern_vars)
		# (dyn_info, expr_heap) = readPtr dyn_ptr expr_heap
		= case dyn_info of
			EI_TempDynamicType (Yes {dt_global_vars, dt_uni_vars, dt_type}) _ _ expr_ptr _
				# (expr_info, expr_heap) = readPtr expr_ptr expr_heap
				-> case expr_info of
					EI_TypeCodes type_codes
						# type_var_heap = fold2St (\{tv_info_ptr} type_code -> writePtr tv_info_ptr (TVI_TypeCode type_code))
														dt_global_vars type_codes type_code_info.tci_type_var_heap
						  (uni_vars, (type_var_heap, ltp_var_heap)) = new_type_variables dt_uni_vars (type_var_heap, local_type_pattern_vars.ltp_var_heap)
						  (type_code_expr, type_code_info) = toTypeCodeExpression dt_type { type_code_info & tci_type_var_heap = type_var_heap }
						-> (type_code_info, expr_heap <:= (dyn_ptr, EI_TypeOfDynamic uni_vars type_code_expr), {local_type_pattern_vars & ltp_var_heap = ltp_var_heap})
					EI_Empty
						# (uni_vars, (type_var_heap, ltp_var_heap)) = new_type_variables dt_uni_vars (type_code_info.tci_type_var_heap, local_type_pattern_vars.ltp_var_heap)
						  (type_code_expr, type_code_info) = toTypeCodeExpression dt_type { type_code_info & tci_type_var_heap = type_var_heap }
						-> (type_code_info, expr_heap <:= (dyn_ptr, EI_TypeOfDynamic uni_vars type_code_expr), {local_type_pattern_vars & ltp_var_heap = ltp_var_heap})
			EI_TempDynamicType No _ _ expr_ptr _
				# (expr_info, expr_heap) = readPtr expr_ptr expr_heap
				-> case expr_info of
					EI_TypeCode type_expr
						-> (type_code_info, expr_heap <:= (dyn_ptr, EI_TypeOfDynamic [] type_expr), local_type_pattern_vars)
					EI_Selection selectors record_var _
						-> (type_code_info, expr_heap <:= (dyn_ptr, EI_TypeOfDynamic [] (convert_selectors selectors record_var)), local_type_pattern_vars)
			EI_TempDynamicPattern type_vars {dt_global_vars, dt_type} loc_dynamics temp_local_vars _ _ expr_ptr _
				# (expr_info, expr_heap) = readPtr expr_ptr expr_heap
				-> case expr_info of
					EI_TypeCodes type_codes
						# type_var_heap = fold2St (\{tv_info_ptr} type_code -> writePtr tv_info_ptr (TVI_TypeCode type_code)) dt_global_vars type_codes type_code_info.tci_type_var_heap
						  (var_ptrs, local_type_pattern_vars) = mapSt addLocalTCInstance temp_local_vars local_type_pattern_vars
						  type_var_heap = fold2St (\{tv_info_ptr} var_ptr -> writePtr tv_info_ptr (TVI_TypeCode (TCE_Var var_ptr))) type_vars var_ptrs type_var_heap
						  (type_code_expr, type_code_info) = toTypeCodeExpression dt_type { type_code_info & tci_type_var_heap = type_var_heap }
						-> convert_local_dynamics loc_dynamics (type_code_info, expr_heap <:= (dyn_ptr, EI_TypeOfDynamicPattern var_ptrs type_code_expr), local_type_pattern_vars)
					EI_Empty
						# (var_ptrs, local_type_pattern_vars) = mapSt addLocalTCInstance temp_local_vars local_type_pattern_vars
						  type_var_heap = fold2St (\{tv_info_ptr} var_ptr -> writePtr tv_info_ptr (TVI_TypeCode (TCE_Var var_ptr))) type_vars var_ptrs type_code_info.tci_type_var_heap
						  (type_code_expr, type_code_info) = toTypeCodeExpression dt_type { type_code_info & tci_type_var_heap = type_var_heap }
						-> convert_local_dynamics loc_dynamics (type_code_info, expr_heap <:= (dyn_ptr, EI_TypeOfDynamicPattern var_ptrs type_code_expr), local_type_pattern_vars)
					
	where
		convert_local_dynamics loc_dynamics state
			= foldSt update_dynamic loc_dynamics state
/*
		convert_local_dynamics (Yes loc_dynamics) state
			= update_dynamic loc_dynamics state
		convert_local_dynamics No state
			= state
*/
		convert_selectors [type_code_selector] {var_info_ptr}
			= TCE_Var var_info_ptr
		convert_selectors selectors {var_info_ptr}
			= TCE_Selector (init selectors) var_info_ptr
		
		new_type_variables uni_vars heaps
			= mapSt new_type_variable uni_vars heaps
			
		new_type_variable {atv_variable = {tv_info_ptr}} (type_var_heap, var_heap)
			# (new_var_ptr, var_heap) = newPtr VI_Empty var_heap
			= (new_var_ptr, (type_var_heap <:= (tv_info_ptr, TVI_TypeCode (TCE_Var new_var_ptr)), var_heap))
		
::	TypeCodeInfo =
	{	tci_next_index			:: !Index
	,	tci_instances			:: ![GlobalTCInstance]
	,	tci_type_var_heap		:: !.TypeVarHeap
	}
		
class toTypeCodeExpression type :: type !*TypeCodeInfo -> (!TypeCodeExpression, !*TypeCodeInfo)

instance toTypeCodeExpression Type
where
	toTypeCodeExpression (TA cons_id type_args) tci=:{tci_next_index,tci_instances}
		# (inst_index, (tci_next_index, tci_instances))
		  		= addGlobalTCInstance (GTT_Constructor cons_id) (tci_next_index, tci_instances)
		  (type_code_args, tci) = mapSt toTypeCodeExpression type_args { tci & tci_next_index = tci_next_index, tci_instances = tci_instances }
		= (TCE_Constructor inst_index type_code_args, tci)
	toTypeCodeExpression (TB basic_type) tci=:{tci_next_index,tci_instances}
		# (inst_index, (tci_next_index, tci_instances))
		  		= addGlobalTCInstance (GTT_Basic basic_type) (tci_next_index, tci_instances)
		= (TCE_Constructor inst_index [], { tci & tci_next_index = tci_next_index, tci_instances = tci_instances })
	toTypeCodeExpression  (arg_type --> result_type) tci=:{tci_next_index,tci_instances}
		# (inst_index, (tci_next_index, tci_instances))
				= addGlobalTCInstance GTT_Function (tci_next_index, tci_instances)
		  (type_code_args, tci) = mapSt toTypeCodeExpression [arg_type, result_type] { tci & tci_next_index = tci_next_index, tci_instances = tci_instances }
		= (TCE_Constructor inst_index type_code_args, tci)
	toTypeCodeExpression  (TV {tv_info_ptr}) tci=:{tci_type_var_heap}
		# (TVI_TypeCode type_code, tci_type_var_heap) = readPtr tv_info_ptr tci_type_var_heap
		= (type_code, { tci & tci_type_var_heap = tci_type_var_heap })

instance toTypeCodeExpression AType
where
	toTypeCodeExpression {at_type} tci = toTypeCodeExpression at_type tci
	

::	UpdateInfo =
	{	ui_instance_calls	:: ![FunCall]
	,	ui_symbol_heap		:: !.ExpressionHeap
	,	ui_fun_defs			:: !.{# FunDef}
	}

class updateExpression e :: !Index ![TypeContext] !e !*UpdateInfo -> (!e, !*UpdateInfo)

instance updateExpression Expression
where
	updateExpression group_index type_contexts (App app=:{app_symb=symb=:{symb_kind,symb_arity,symb_name},app_args,app_info_ptr}) ui
		# (app_args, ui) = updateExpression group_index type_contexts app_args ui
		| isNilPtr app_info_ptr
			= (App { app & app_args = app_args }, ui)
			#! symb_info = sreadPtr app_info_ptr ui.ui_symbol_heap
			= case symb_info of
				EI_Empty
					| is_recursive_call group_index symb_kind ui.ui_fun_defs
						# app_args = strictMapAppend (\tc -> Var (createBoundVar tc)) type_contexts app_args
						-> (App { app & app_symb = { symb & symb_arity = length type_contexts + symb_arity }, app_args = app_args }, ui)
						-> (App { app & app_args = app_args }, ui)
				EI_Instance inst_symbol context_args
					-> (build_application inst_symbol context_args app_args symb_arity app_info_ptr,
							examine_calls context_args (new_call inst_symbol.glob_module inst_symbol.glob_object.ds_index ui))
				EI_Selection selectors record_var context_args
					# all_args = context_args ++ app_args
					  select_expr = Selection No (Var record_var) selectors
					| isEmpty all_args
						-> (select_expr, ui)
						-> (select_expr @ all_args, examine_calls context_args ui)
				EI_Context context_args
					# app = { app & app_symb = { symb & symb_arity = length context_args + symb_arity }, app_args = context_args ++  app_args}
					-> (App app, examine_calls context_args ui)


	where
		is_recursive_call group_index (SK_Function {glob_module,glob_object}) fun_defs
			| glob_module == cIclModIndex
				#! fun_def = fun_defs.[glob_object]
				= fun_def.fun_info.fi_group_index == group_index
				= False
		is_recursive_call group_index _ fun_defs
			= False

		build_application def_symbol=:{glob_object} context_args orig_args nr_of_orig_args app_info_ptr
			= App {app_symb = { symb_name = glob_object.ds_ident,
									symb_kind = SK_Function { def_symbol & glob_object = glob_object.ds_index },
										symb_arity = glob_object.ds_arity + nr_of_orig_args },
				   app_args = context_args ++ orig_args, app_info_ptr = app_info_ptr }

		examine_application (SK_Function {glob_module,glob_object}) ui
			= new_call glob_module glob_object ui
		examine_application symb_kind ui
			= ui
			
		new_call mod_index symb_index ui=:{ui_instance_calls,ui_fun_defs}
			| mod_index == cIclModIndex && symb_index < size ui_fun_defs
				# ui_instance_calls = add_call symb_index ui_instance_calls
				= { ui & ui_instance_calls = ui_instance_calls }
				= ui
		where
			add_call fun_num []
				= [{ fc_level = 0, fc_index = fun_num }]
			add_call fun_num funs=:[call=:{fc_index} : ui]
				| fun_num == fc_index
					= funs
				| fun_num < fc_index
					= [{ fc_level = 0, fc_index = fun_num } : funs]
					= [call : add_call fun_num ui]
	
		examine_calls [expr : exprs] ui
			= examine_calls exprs (examine_calls_in_expr expr ui)
		where
			examine_calls_in_expr (App {app_symb = {symb_name,symb_kind}, app_args}) ui
				= examine_calls app_args (examine_application symb_kind ui)
			examine_calls_in_expr _ ui
				= ui
		examine_calls [] ui
			= ui
		
			
	updateExpression group_index type_contexts (expr @ exprs) ui
		# ((expr, exprs), ui) = updateExpression group_index type_contexts (expr, exprs) ui
		= (expr @ exprs, ui)
	updateExpression group_index type_contexts (Let lad=:{let_binds, let_expr}) ui
		# ((let_binds, let_expr), ui) = updateExpression group_index type_contexts (let_binds, let_expr) ui
		= (Let {lad & let_binds = let_binds, let_expr = let_expr}, ui)
	updateExpression group_index type_contexts (Case kees=:{case_expr,case_guards,case_default}) ui
		# ((case_expr,(case_guards,case_default)), ui) = updateExpression group_index type_contexts (case_expr,(case_guards,case_default)) ui
		= (Case { kees & case_expr = case_expr, case_guards = case_guards, case_default = case_default }, ui)
	updateExpression group_index type_contexts (Selection is_unique expr selectors) ui
		# (expr, ui) = updateExpression group_index type_contexts expr ui
		  (selectors, ui) = updateExpression group_index type_contexts selectors ui
		= (Selection is_unique expr selectors, ui)
/*
		where
			update_selections group_index type_contexts is_unique selectors ui
				= foldl (update_selection group_index type_contexts is_unique) state selectors
		  
		  	update_selection group_index type_contexts is_unique (expr, ui) (ArraySelection selector expr_ptr index_expr)
				# (index_expr, ui) = updateExpression group_index type_contexts index_expr ui
				#! symb_info = sreadPtr expr_ptr ui.ui_symbol_heap
				= case symb_info of
					EI_Instance array_select []
						-> (App {app_symb = { symb_name = glob_object.ds_ident,
									symb_kind = SK_Function { glob_module = glob_module, glob_object = glob_object.ds_index },
										symb_arity = glob_object.ds_arity + 2 },
								 app_args = context_args ++ [expr,index_expr], app_info_ptr = expr_ptr }, ui)
					EI_Selection selectors record context_args
						-> (Selection is_unique record selectors @ [expr,index_expr], ui)
		  	update_selection group_index type_contexts is_unique (expr, ui) (RecordSelection selector field_nr)
		  		= (Selection is_unique expr [RecordSelection selector field_nr], ui)
*/
	updateExpression group_index type_contexts (Update expr1 selectors expr2) ui
		# (expr1, ui) = updateExpression group_index type_contexts expr1 ui
		  (selectors, ui) = updateExpression group_index type_contexts selectors ui
		  (expr2, ui) = updateExpression group_index type_contexts expr2 ui
		= (Update expr1 selectors expr2, ui)
	updateExpression group_index type_contexts (RecordUpdate cons_symbol expression expressions) ui
		# (expression, ui) = updateExpression group_index type_contexts expression ui
		  (expressions, ui) = updateExpression group_index type_contexts expressions ui
		= (RecordUpdate cons_symbol expression expressions, ui)
	updateExpression group_index type_contexts (DynamicExpr dyn=:{dyn_expr,dyn_info_ptr}) ui
		# (dyn_expr, ui) = updateExpression group_index type_contexts dyn_expr ui
		  (EI_TypeOfDynamic uni_vars type_code, ui_symbol_heap) = readPtr dyn_info_ptr ui.ui_symbol_heap
		= (DynamicExpr { dyn & dyn_expr = dyn_expr, dyn_type_code = type_code, dyn_uni_vars = uni_vars }, { ui & ui_symbol_heap = ui_symbol_heap })
	updateExpression group_index type_contexts (MatchExpr opt_tuple cons_symbol expr) ui
		# (expr, ui) = updateExpression group_index type_contexts expr ui
		= (MatchExpr opt_tuple cons_symbol expr, ui)
	updateExpression group_index type_contexts (TupleSelect symbol argn_nr expr) ui
		# (expr, ui) = updateExpression group_index type_contexts expr ui
		= (TupleSelect symbol argn_nr expr, ui)
	updateExpression group_index type_contexts expr ui
		= (expr, ui)

instance updateExpression Bind a b | updateExpression a
where
	updateExpression group_index type_contexts bind=:{bind_src} ui
		# (bind_src, ui) = updateExpression group_index type_contexts bind_src ui
		= ({bind & bind_src = bind_src }, ui)

instance updateExpression Optional a | updateExpression a
where
	updateExpression group_index type_contexts (Yes x) ui
		# (x, ui) = updateExpression group_index type_contexts x ui
		= (Yes x, ui)
	updateExpression group_index type_contexts No ui
		= (No, ui)

instance updateExpression CasePatterns
where
	updateExpression group_index type_contexts (AlgebraicPatterns type patterns) ui
		# (patterns, ui) =  updateExpression group_index type_contexts patterns ui
		= (AlgebraicPatterns type patterns, ui)
	updateExpression group_index type_contexts (BasicPatterns type patterns) ui
		# (patterns, ui) =  updateExpression group_index type_contexts patterns ui
		= (BasicPatterns type patterns, ui)
	updateExpression group_index type_contexts (DynamicPatterns patterns) ui
		# (patterns, ui) =  updateExpression group_index type_contexts patterns ui
		= (DynamicPatterns patterns, ui)
	
instance updateExpression AlgebraicPattern
where
	updateExpression group_index type_contexts pattern=:{ap_vars,ap_expr} ui
		# (ap_expr, ui) =  updateExpression group_index type_contexts ap_expr ui
		= ({ pattern & ap_expr = ap_expr }, ui)

instance updateExpression BasicPattern
where
	updateExpression group_index type_contexts pattern=:{bp_expr} ui
		# (bp_expr, ui) = updateExpression group_index type_contexts bp_expr ui
		= ({ pattern & bp_expr = bp_expr }, ui)

instance updateExpression Selection
where
  	updateExpression group_index type_contexts (ArraySelection selector expr_ptr index_expr) ui
		# (index_expr, ui) = updateExpression group_index type_contexts index_expr ui
		#! symb_info = sreadPtr expr_ptr ui.ui_symbol_heap
		= case symb_info of
			EI_Instance array_select []
				-> (ArraySelection array_select expr_ptr index_expr, ui)
			EI_Selection selectors record context_args
				-> (DictionarySelection record selectors expr_ptr index_expr, ui)
  	updateExpression group_index type_contexts selection ui
		= (selection, ui)

instance updateExpression TypeCase
where
	updateExpression group_index type_contexts type_case=:{type_case_dynamic,type_case_patterns,type_case_default} ui
		# ((type_case_dynamic,(type_case_patterns,type_case_default)), ui) = updateExpression group_index type_contexts
				(type_case_dynamic,(type_case_patterns,type_case_default)) ui
		= ({ type_case & type_case_dynamic = type_case_dynamic, type_case_patterns = type_case_patterns, type_case_default = type_case_default }, ui)
	
instance updateExpression DynamicPattern
where
	updateExpression group_index type_contexts dp=:{dp_type,dp_rhs} ui
		# (dp_rhs, ui) =  updateExpression group_index type_contexts dp_rhs ui
		  (EI_TypeOfDynamicPattern type_pattern_vars type_code, ui_symbol_heap) = readPtr dp_type ui.ui_symbol_heap
		= ({ dp & dp_rhs = dp_rhs, dp_type_patterns_vars = type_pattern_vars, dp_type_code = type_code }, { ui & ui_symbol_heap = ui_symbol_heap })

instance updateExpression (a,b) | updateExpression a & updateExpression b
where
	updateExpression group_index type_contexts t ui
		= app2St (updateExpression group_index type_contexts,updateExpression group_index type_contexts) t ui

instance updateExpression [e] | updateExpression e
where
	updateExpression group_index type_contexts l ui
		= mapSt (updateExpression group_index type_contexts) l ui
		

class equalTypes a :: !a !a !*TypeVarHeap -> (!Bool, !*TypeVarHeap)

instance equalTypes AType
where
	equalTypes atype1 atype2 type_var_heap
		= equalTypes atype1.at_type atype2.at_type type_var_heap

equalTypeVars {tv_info_ptr}	temp_var_id type_var_heap
	#! tv_info = sreadPtr tv_info_ptr type_var_heap
	= case tv_info of
		TVI_Forward forw_var_number
			-> (forw_var_number == temp_var_id, type_var_heap)
		_
			-> (True, type_var_heap <:= (tv_info_ptr, TVI_Forward temp_var_id))

instance equalTypes Type
where
	equalTypes (TV tv) (TempV var_number) type_var_heap
		= equalTypeVars tv var_number type_var_heap
	equalTypes (arg_type1 --> restype1) (arg_type2 --> restype2) type_var_heap
		= equalTypes (arg_type1,restype1) (arg_type2,restype2) type_var_heap
	equalTypes (TA tc1 types1) (TA tc2 types2) type_var_heap
		| tc1 == tc2
			= equalTypes types1 types2 type_var_heap
			= (False, type_var_heap)
	equalTypes (TB basic1) (TB basic2) type_var_heap
		= (basic1 == basic2, type_var_heap)
	equalTypes (CV tv :@: types1) (TempCV var_number :@: types2) type_var_heap
		# (eq, type_var_heap) = equalTypeVars tv var_number type_var_heap
		| eq
			= equalTypes types1 types2 type_var_heap
			= (False, type_var_heap)
	equalTypes type1 type2 type_var_heap
		= (False, type_var_heap)

instance equalTypes (a,b) | equalTypes a & equalTypes b
where
	equalTypes (x1,y1) (x2,y2) type_var_heap
		# (eq, type_var_heap) = equalTypes x1 x2 type_var_heap
		| eq
			= equalTypes y1 y2 type_var_heap
			= (False, type_var_heap)

instance equalTypes [a] | equalTypes a
where
	equalTypes [x:xs] [y:ys] type_var_heap
		= equalTypes (x,xs) (y,ys) type_var_heap
	equalTypes [] [] type_var_heap
		= (True, type_var_heap)
	equalTypes _ _ type_var_heap
		= (False, type_var_heap)

instance <<< TypeContext
where
	(<<<) file tc = file <<< tc.tc_class.glob_object.ds_ident <<< ' ' <<< tc.tc_types

instance <<< FunCall
where
	(<<<) file {fc_index} = file <<< fc_index
	

instance <<< Special
where
	(<<<) file {spec_types} = file <<< spec_types

instance <<< (Ptr x)
where
	(<<<) file _ = file
	
instance <<< TypeCodeExpression
where
	(<<<) file _ = file

