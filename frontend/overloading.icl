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
		
		
instanceError symbol types err
	# err = errorHeading "Overloading error" err
	  format = { form_properties = cNoProperties, form_attr_position = No }
	= { err & ea_file = err.ea_file <<< " \"" <<< symbol <<< "\" no instance available of type " <:: (format, types) <<< '\n' }


uniqueError symbol types err
	# err = errorHeading "Overloading/Uniqueness error" err
	  format = { form_properties = cAnnotated, form_attr_position = No }
	= { err & ea_file = err.ea_file <<< " \"" <<< symbol
			<<< "\" uniqueness specification of instance conflicts with current application " <:: (format, types) <<< '\n'}

unboxError type err
	# err = errorHeading "Overloading error of Array class" err
	  format = { form_properties = cNoProperties, form_attr_position = No }
	= { err & ea_file = err.ea_file <<< ' ' <:: (format, type) <<< " instance cannot be unboxed\n"}

overloadingError op_symb err
	# err = errorHeading "Overloading error" err
	= { err & ea_file = err.ea_file <<< " internal overloading of \"" <<< op_symb <<< "\" could not be solved\n" }

/*
	As soon as all overloaded variables in an type context are instantiated, context reduction is carried out.
	This reduction yields a type class instance (here represented by a an index) and a list of
	ClassApplications.
*/

containsContext :: !TypeContext ![TypeContext] -> Bool
containsContext new_tc []
	= False
containsContext new_tc [tc : tcs]
	= new_tc == tc || containsContext new_tc tcs


FoundObject object :== object.glob_module <> NotFound
ObjectNotFound 	:== { glob_module = NotFound, glob_object = NotFound }

reduceContexts :: ![TypeContext] !{# CommonDefs} !ClassInstanceInfo ![TypeContext] !*SpecialInstances ![LocalTypePatternVariable]
	!(!*VarHeap, !*TypeHeaps) !*Coercions !*PredefinedSymbols !*ErrorAdmin
		-> *(![ClassApplication],  ![TypeContext], !*SpecialInstances, ![LocalTypePatternVariable],
				!(!*VarHeap, !*TypeHeaps), !*Coercions, !*PredefinedSymbols, !*ErrorAdmin)
reduceContexts [] defs instance_info new_contexts special_instances type_pattern_vars heaps coercion_env predef_symbols error
	= ([], new_contexts, special_instances, type_pattern_vars, heaps, coercion_env, predef_symbols, error)
reduceContexts [tc : tcs] defs instance_info new_contexts special_instances type_pattern_vars heaps coercion_env predef_symbols error
	# (appl, new_contexts, special_instances, type_pattern_vars, heaps, coercion_env, predef_symbols, error)
			= try_to_reduce_context tc defs instance_info new_contexts special_instances type_pattern_vars heaps coercion_env predef_symbols error
	  (appls, new_contexts, special_instances, type_pattern_vars, heaps, coercion_env, predef_symbols, error)
	  		= reduceContexts tcs defs instance_info new_contexts special_instances type_pattern_vars heaps coercion_env predef_symbols error
	= ([appl : appls], new_contexts, special_instances, type_pattern_vars, heaps, coercion_env, predef_symbols, error)

where		
	try_to_reduce_context :: !TypeContext !{# CommonDefs} !ClassInstanceInfo ![TypeContext] !*SpecialInstances ![LocalTypePatternVariable]
		!(!*VarHeap, !*TypeHeaps) !*Coercions !*PredefinedSymbols !*ErrorAdmin
			-> *(!ClassApplication, ![TypeContext], !*SpecialInstances, ![LocalTypePatternVariable], !(!*VarHeap, !*TypeHeaps), !*Coercions, !*PredefinedSymbols, !*ErrorAdmin)
	try_to_reduce_context tc=:{tc_class=class_symb=:{glob_object={ds_index},glob_module},tc_types} defs instance_info new_contexts
			special_instances type_pattern_vars (var_heap, type_heaps) coercion_env predef_symbols error
		| is_reducible tc_types
			| is_predefined_symbol glob_module ds_index PD_TypeCodeClass predef_symbols
				# (red_context, (special_instances, type_pattern_vars, var_heap))
							= reduce_TC_context class_symb (hd tc_types) special_instances type_pattern_vars var_heap
				= (red_context, new_contexts, special_instances, type_pattern_vars, (var_heap, type_heaps), coercion_env, predef_symbols, error)
				# (class_appls, new_contexts, special_instances, type_pattern_vars, heaps, coercion_env, predef_symbols, error)
						= reduce_context tc defs instance_info new_contexts special_instances type_pattern_vars
								(var_heap, type_heaps) coercion_env predef_symbols error
				= (CA_Instance class_appls, new_contexts, special_instances, type_pattern_vars, heaps, coercion_env, predef_symbols, error)
			| containsContext tc new_contexts
				= (CA_Context tc, new_contexts, special_instances, type_pattern_vars, (var_heap, type_heaps), coercion_env, predef_symbols, error)
				# (tc_var, var_heap) = newPtr VI_Empty var_heap
				= (CA_Context tc, [{ tc & tc_var = tc_var } : new_contexts], special_instances,
						type_pattern_vars, (var_heap, type_heaps), coercion_env, predef_symbols, error)

/*	reduceContext :: !ClassDef !InstanceTree ![Type] !{# CommonDefs} !ClassInstanceInfo !*SpecialInstances ![LocalTypePatternVariable]
			!*TypeHeaps !*Coercions !*PredefinedSymbols !*ErrorAdmin
				-> *(![ReducedContext], !*SpecialInstances, ![LocalTypePatternVariable], !*TypeHeaps, !*Coercions, !*PredefinedSymbols, !*ErrorAdmin)
*/

	reduce_context {tc_class=class_symb=:{glob_object={ds_index},glob_module},tc_types} defs
						instance_info new_contexts special_instances type_pattern_vars heaps coercion_env predef_symbols error
		# {class_members,class_context,class_args,class_name} = defs.[glob_module].com_class_defs.[ds_index]
		| size class_members > 0
			# class_instances = instance_info.[glob_module].[ds_index]
			# ({glob_module,glob_object}, contexts, uni_ok, (var_heap, type_heaps), coercion_env) = find_instance tc_types class_instances defs heaps coercion_env
			| (glob_module <> NotFound) && uni_ok
				# {ins_members, ins_class} = defs.[glob_module].com_instance_defs.[glob_object]
				| is_predefined_symbol ins_class.glob_module ins_class.glob_object.ds_index PD_ArrayClass predef_symbols &&
				  is_unboxed_array tc_types predef_symbols
					# (rcs_class_context, special_instances, (predef_symbols, type_heaps), error)
							= check_unboxed_type glob_module ins_class ins_members tc_types class_members defs special_instances (predef_symbols, type_heaps) error
					= ({ rcs_class_context = rcs_class_context, rcs_constraints_contexts = []}, new_contexts,
									special_instances, type_pattern_vars, (var_heap, type_heaps), coercion_env, predef_symbols, error)
					# (appls, new_contexts, special_instances, type_pattern_vars, heaps, coercion_env, predef_symbols, error)
							= reduceContexts contexts defs instance_info new_contexts special_instances type_pattern_vars (var_heap, type_heaps) coercion_env predef_symbols error
					  (constraints, new_contexts, special_instances, type_pattern_vars, heaps, coercion_env, predef_symbols, error)
					  		= reduce_contexts_in_constraints tc_types class_args class_context defs instance_info new_contexts special_instances type_pattern_vars
					  				heaps coercion_env predef_symbols error
					= ({ rcs_class_context = { rc_class = ins_class, rc_inst_module = glob_module, rc_inst_members = ins_members,
								rc_types = tc_types, rc_red_contexts = appls }, rcs_constraints_contexts = constraints }, new_contexts,
							special_instances, type_pattern_vars, heaps, coercion_env, predef_symbols, error)
				# rcs_class_context = { rc_class = class_symb, rc_inst_module = NoIndex, rc_inst_members = {}, rc_types = tc_types, rc_red_contexts = [] }
				| glob_module <> NotFound
					= ({ rcs_class_context = rcs_class_context, rcs_constraints_contexts = []}, new_contexts,
							special_instances, type_pattern_vars, (var_heap, type_heaps), coercion_env, predef_symbols, uniqueError class_name tc_types error)
					= ({ rcs_class_context = rcs_class_context, rcs_constraints_contexts = []}, new_contexts,
							special_instances, type_pattern_vars, (var_heap, type_heaps), coercion_env, predef_symbols, instanceError class_name tc_types error)
			# (constraints, new_contexts, special_instances, type_pattern_vars, heaps, coercion_env, predef_symbols, error)
				= reduce_contexts_in_constraints tc_types class_args class_context defs instance_info new_contexts special_instances type_pattern_vars
								heaps coercion_env predef_symbols error
			= ({ rcs_class_context = { rc_class = class_symb, rc_inst_module = NoIndex, rc_inst_members = {}, rc_types = tc_types, rc_red_contexts = [] },
				rcs_constraints_contexts = constraints },  new_contexts, special_instances, type_pattern_vars, heaps, coercion_env, predef_symbols, error)

	reduce_contexts_in_constraints types class_args [] defs instance_info new_contexts special_instances type_pattern_vars heaps coercion_env predef_symbols error
		= ([], new_contexts, special_instances, type_pattern_vars, heaps, coercion_env, predef_symbols, error)
	reduce_contexts_in_constraints types class_args class_context defs instance_info new_contexts special_instances type_pattern_vars
			(var_heap, type_heaps=:{th_vars}) coercion_env predef_symbols error
		# th_vars = fold2St (\ type {tv_info_ptr} -> writePtr tv_info_ptr (TVI_Type type)) types class_args th_vars
		  (instantiated_context, heaps) = fresh_contexts class_context (var_heap, { type_heaps & th_vars = th_vars })
		# (cappls, (new_contexts, special_instances, type_pattern_vars, heaps, coercion_env, predef_symbols, error))
		  		= mapSt (reduce_context_in_constraint defs instance_info) instantiated_context
		  				(new_contexts, special_instances, type_pattern_vars, heaps, coercion_env, predef_symbols, error)
		= (cappls, new_contexts, special_instances, type_pattern_vars, heaps, coercion_env, predef_symbols, error)

	where
		reduce_context_in_constraint defs instance_info tc (new_contexts, special_instances, type_pattern_vars, heaps, coercion_env, predef_symbols, error)
		  	# (cappls, new_contexts, special_instances, type_pattern_vars, heaps, coercion_env, predef_symbols, error)
				= reduce_context tc defs instance_info new_contexts special_instances type_pattern_vars heaps coercion_env predef_symbols error
			= (cappls, (new_contexts, special_instances, type_pattern_vars, heaps, coercion_env, predef_symbols, error))

	find_instance co_types (IT_Node this_inst_index=:{glob_object,glob_module} left right) defs heaps coercion_env
		# (left_index, types, uni_ok, (var_heap, type_heaps), coercion_env) = find_instance co_types left defs heaps coercion_env
		| FoundObject left_index
			= (left_index, types, uni_ok, (var_heap, type_heaps), coercion_env)
			# {ins_type={it_types,it_context}, ins_specials} = defs.[glob_module].com_instance_defs.[glob_object]
			  (matched, type_heaps) = match defs it_types co_types type_heaps
			| matched
				# (subst_context, (var_heap, type_heaps)) = fresh_contexts it_context (var_heap, type_heaps)
				  (uni_ok, coercion_env, type_heaps) = adjust_type_attributes defs co_types it_types coercion_env type_heaps
				  (spec_inst, type_heaps) = trySpecializedInstances subst_context (get_specials ins_specials) type_heaps
				| FoundObject spec_inst
					= (spec_inst, [], uni_ok, (var_heap, type_heaps), coercion_env)
					= (this_inst_index, subst_context, uni_ok, (var_heap, type_heaps), coercion_env)
				= find_instance co_types right defs (var_heap, type_heaps) coercion_env
	find_instance co_types IT_Empty defs heaps coercion_env
		= (ObjectNotFound, [], True, heaps, coercion_env)
	
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

	fresh_contexts contexts heaps
		= mapSt fresh_context contexts heaps
	where
		fresh_context tc=:{tc_types} (var_heap, type_heaps)
			# (tc_types, type_heaps) = substitute tc_types type_heaps
//			  (tc_var, var_heap) = newPtr VI_Empty var_heap
//			= ({ tc & tc_types = tc_types, tc_var = tc_var }, (var_heap, type_heaps))
			= ({ tc & tc_types = tc_types }, (var_heap, type_heaps))

	is_predefined_symbol mod_index symb_index predef_index predef_symbols
		# {pds_def,pds_module,pds_ident} = predef_symbols.[predef_index]
		= (mod_index == pds_module && symb_index == pds_def)
		
	is_unboxed_array [TA {type_index={glob_module,glob_object},type_arity} _ : _] predef_symbols
		= is_predefined_symbol glob_module glob_object PD_UnboxedArrayType predef_symbols
	is_unboxed_array _ predef_symbols
		= False

	check_unboxed_type ins_module ins_class ins_members types=:[ _, elem_type :_] class_members defs special_instances predef_symbols_type_heaps error
		# (unboxable, opt_record, predef_symbols_type_heaps) = try_to_unbox elem_type defs predef_symbols_type_heaps
		| unboxable
			= case opt_record of
				Yes record
					# (ins_members, special_instances) = add_record_to_array_instances record class_members special_instances
					-> ({ rc_class = ins_class, rc_inst_module = cIclModIndex, rc_inst_members = ins_members, rc_red_contexts = [], rc_types = types },
							special_instances, predef_symbols_type_heaps, error)
				No
					-> ({ rc_class = ins_class, rc_inst_module = ins_module, rc_inst_members = ins_members, rc_red_contexts = [], rc_types = types },
							special_instances, predef_symbols_type_heaps, error)
			= ({ rc_class = ins_class, rc_inst_module = ins_module, rc_inst_members = ins_members, rc_red_contexts = [], rc_types = types },
					special_instances, predef_symbols_type_heaps, unboxError elem_type error)
	where
		try_to_unbox (TB _) _ predef_symbols_type_heaps
			= (True, No, predef_symbols_type_heaps)
		try_to_unbox (TA type_symb=:{type_index={glob_module,glob_object},type_arity} type_args) defs (predef_symbols, type_heaps)
			# {td_arity,td_rhs, td_args} = defs.[glob_module].com_type_defs.[glob_object]
			= case td_rhs of
				RecordType _
					-> (True, (Yes type_symb), (predef_symbols, type_heaps))
				AbstractType _
					#! unboxable =
						   is_predefined_symbol glob_module glob_object PD_LazyArrayType predef_symbols ||
						   is_predefined_symbol glob_module glob_object PD_StrictArrayType predef_symbols ||
						   is_predefined_symbol glob_module glob_object PD_UnboxedArrayType predef_symbols
					-> (unboxable, No, (predef_symbols, type_heaps))
				SynType {at_type}
					# (expanded_type, type_heaps) = expandTypeSyn td_args type_args at_type type_heaps
					-> try_to_unbox expanded_type defs (predef_symbols, type_heaps)
				_
					-> (False, No, (predef_symbols, type_heaps))				
		try_to_unbox type _ predef_symbols_type_heaps
			= (True, No, predef_symbols_type_heaps)

		add_record_to_array_instances :: !TypeSymbIdent !{# DefinedSymbol} !*SpecialInstances -> (!{#DefinedSymbol},!*SpecialInstances)
		add_record_to_array_instances record members special_instances=:{si_next_array_member_index,si_array_instances}
			# may_be_there = look_up_array_instance record si_array_instances
			= case may_be_there of
				Yes inst
					-> (inst.ai_members, special_instances)
				No
					# inst = new_array_instance record members si_next_array_member_index
					-> (inst.ai_members, { special_instances &  si_next_array_member_index = si_next_array_member_index + size members,
																si_array_instances = [ inst : si_array_instances ] })
		where
			look_up_array_instance :: !TypeSymbIdent ![ArrayInstance] -> Optional ArrayInstance
			look_up_array_instance record []
				= No
			look_up_array_instance record [inst : insts]
				| record == inst.ai_record
					= Yes inst
					= look_up_array_instance record insts
			
			new_array_instance :: !TypeSymbIdent !{# DefinedSymbol} !Index -> ArrayInstance
			new_array_instance record members next_member_index
				= {	ai_members = { { class_member & ds_index = next_inst_index } \\ class_member <-: members & next_inst_index <- [next_member_index .. ]},
					ai_record = record }
				
				
/*
			# (inst_members, si_array_instances, si_next_array_member_index) = add_array_instance record members si_next_array_member_index si_array_instances
			= (inst_members, { special_instances & si_array_instances = si_array_instances, si_next_array_member_index = si_next_array_member_index })

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
*/			
	reduce_TC_context type_code_class tc_type special_instances type_pattern_vars var_heap
		= reduce_tc_context type_code_class tc_type (special_instances, type_pattern_vars, var_heap)
	where							
		reduce_tc_context type_code_class (TA cons_id cons_args) (special_instances=:{si_next_TC_member_index, si_TC_instances}, type_pattern_vars, var_heap)
			# (inst_index, (si_next_TC_member_index, si_TC_instances))
			  		= addGlobalTCInstance (GTT_Constructor cons_id) (si_next_TC_member_index, si_TC_instances)
			  (rc_red_contexts, instances) = reduce_TC_contexts type_code_class cons_args
			  		 ({ special_instances & si_next_TC_member_index = si_next_TC_member_index, si_TC_instances = si_TC_instances }, type_pattern_vars, var_heap)
			= (CA_GlobalTypeCode { tci_index = inst_index, tci_contexts = rc_red_contexts }, instances)

		reduce_tc_context type_code_class (TB basic_type) (special_instances=:{si_next_TC_member_index, si_TC_instances}, type_pattern_vars, var_heap)
			# (inst_index, (si_next_TC_member_index, si_TC_instances))
			  		= addGlobalTCInstance (GTT_Basic basic_type) (si_next_TC_member_index, si_TC_instances)
			= (CA_GlobalTypeCode { tci_index = inst_index, tci_contexts = [] },
					({ special_instances & si_next_TC_member_index = si_next_TC_member_index, si_TC_instances = si_TC_instances }, type_pattern_vars, var_heap))

		reduce_tc_context type_code_class (arg_type --> result_type) (special_instances=:{si_next_TC_member_index, si_TC_instances}, type_pattern_vars, var_heap)
			# (inst_index, (si_next_TC_member_index, si_TC_instances))
			  		= addGlobalTCInstance GTT_Function (si_next_TC_member_index, si_TC_instances)
			  (rc_red_contexts, instances) = reduce_TC_contexts type_code_class [arg_type, result_type]
			  		 ({ special_instances & si_next_TC_member_index = si_next_TC_member_index, si_TC_instances = si_TC_instances }, type_pattern_vars, var_heap)
			= (CA_GlobalTypeCode { tci_index = inst_index, tci_contexts = rc_red_contexts }, instances)


		reduce_tc_context type_code_class (TempQV var_number) (special_instances, type_pattern_vars, var_heap)
			# (inst_var, (type_pattern_vars, var_heap)) = addLocalTCInstance var_number (type_pattern_vars, var_heap)
			= (CA_LocalTypeCode inst_var, (special_instances, type_pattern_vars, var_heap))

		reduce_tc_context type_code_class (TempV var_number) (special_instances, type_pattern_vars, var_heap)
//			# (tc_var, var_heap) = newPtr VI_Empty var_heap
			= (CA_Context { tc_class = type_code_class, tc_types = [TempV var_number], tc_var = nilPtr }, (special_instances, type_pattern_vars, var_heap))
		

		reduce_TC_contexts type_code_class cons_args instances
			= mapSt (\{at_type} -> reduce_tc_context type_code_class at_type) cons_args instances
		
addLocalTCInstance var_number (instances=:[inst : insts], ltp_var_heap)
	# cmp = var_number =< inst.ltpv_var
	| cmp == Equal
		= (inst.ltpv_new_var, (instances, ltp_var_heap))
	| cmp == Smaller
		# (ltpv_new_var, ltp_var_heap) = newPtr VI_Empty ltp_var_heap
		= (ltpv_new_var, ( [{ ltpv_new_var = ltpv_new_var, ltpv_var = var_number } : instances ], ltp_var_heap ))
		# (found_var, (insts, ltp_var_heap)) = addLocalTCInstance var_number (insts, ltp_var_heap)
		= (found_var, ([inst : insts ], ltp_var_heap))
addLocalTCInstance var_number ([], ltp_var_heap)
	# (ltpv_new_var, ltp_var_heap) = newPtr VI_Empty ltp_var_heap
	= (ltpv_new_var, ([{ ltpv_new_var = ltpv_new_var, ltpv_var = var_number }], ltp_var_heap))

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
	= case td_rhs of
		SynType {at_type}
			# (expanded_type, type_heaps) = expandTypeSyn td_args type_args at_type type_heaps
			-> (True, expanded_type, type_heaps) 
		_
			-> (False, TA cons_id type_args, type_heaps)
where
	is_synonym_type (SynType _)
		= True
	is_synonym_type type_rhs
		= False

expandTypeSyn td_args type_args td_rhs type_heaps
	# type_heaps = fold2St bind_var td_args type_args type_heaps
	  (expanded_type, type_heaps) = substitute td_rhs type_heaps
	= (expanded_type, type_heaps)
where
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

tryToSolveOverloading :: ![(Optional [TypeContext], [ExprInfoPtr], IdentPos, Index)] !{# CommonDefs } !ClassInstanceInfo !*Coercions !*OverloadingState
	-> (![TypeContext], !*Coercions, ![LocalTypePatternVariable], !*OverloadingState)
tryToSolveOverloading ocs defs instance_info coercion_env os
	# (reduced_contexts, contexts, coercion_env, type_pattern_vars, os) = foldSt (reduce_contexts defs instance_info) ocs
			([], [], coercion_env, [], os)
	  (contexts, os_var_heap) = foldSt add_spec_contexts ocs (contexts, os.os_var_heap)
	  (contexts, os_type_heaps) = remove_sub_classes contexts os.os_type_heaps
	  (os_type_heaps, os_symbol_heap) = foldSt (convert_dictionaries defs contexts) reduced_contexts (os_type_heaps, os.os_symbol_heap)
	= (contexts, coercion_env, type_pattern_vars, { os & os_type_heaps = os_type_heaps, os_symbol_heap = os_symbol_heap, os_var_heap = os_var_heap })

where
	reduce_contexts defs instance_info (opt_spec_contexts, expr_ptrs, pos, index) rc_state
		= foldSt (reduce_contexts_of_application defs instance_info) expr_ptrs rc_state

	add_spec_contexts (Yes spec_context, expr_ptrs, pos, index) contexts_and_var_heap
		= foldSt add_spec_context spec_context contexts_and_var_heap
	where
		add_spec_context tc (contexts, var_heap)
			| containsContext tc contexts
				= (contexts, var_heap)
			  	# (tc_var, var_heap) = newPtr VI_Empty var_heap
				= ([{ tc & tc_var = tc_var } : contexts], var_heap)
	add_spec_contexts (No, expr_ptrs, pos, index) contexts_and_var_heap
		= contexts_and_var_heap

	reduce_contexts_of_application :: !{# CommonDefs } !ClassInstanceInfo  !ExprInfoPtr
				([(SymbIdent, ExprInfoPtr,[ClassApplication])], ![TypeContext], !*Coercions, ![LocalTypePatternVariable], !*OverloadingState)
					 -> ([(SymbIdent, ExprInfoPtr,[ClassApplication])], ![TypeContext], !*Coercions, ![LocalTypePatternVariable], !*OverloadingState)
	reduce_contexts_of_application  defs instance_info over_info_ptr (reduced_calls, new_contexts, coercion_env, type_pattern_vars,
			os=:{os_symbol_heap,os_type_heaps,os_var_heap,os_special_instances,os_error,os_predef_symbols})
		# (EI_Overloaded {oc_symbol, oc_context, oc_specials}, os_symbol_heap) = readPtr over_info_ptr os_symbol_heap
		  (glob_fun, os_type_heaps) = trySpecializedInstances oc_context oc_specials os_type_heaps
		| FoundObject glob_fun
			# os_symbol_heap = os_symbol_heap <:= (over_info_ptr, EI_Instance {glob_module = glob_fun.glob_module, glob_object =
									{ ds_ident =  oc_symbol.symb_name, ds_arity = 0, ds_index = glob_fun.glob_object }} [])
			= (reduced_calls, new_contexts, coercion_env, type_pattern_vars, { os & os_type_heaps = os_type_heaps, os_symbol_heap = os_symbol_heap })
		| otherwise
			# (class_applications, new_contexts, os_special_instances, type_pattern_vars,
								(os_var_heap, os_type_heaps), coercion_env, os_predef_symbols, os_error)
					= reduceContexts oc_context defs instance_info new_contexts os_special_instances type_pattern_vars
							(os_var_heap, os_type_heaps) coercion_env os_predef_symbols os_error
			= ([ (oc_symbol, over_info_ptr, class_applications) : reduced_calls ], new_contexts, coercion_env, type_pattern_vars, 
					{ os & os_type_heaps = os_type_heaps, os_symbol_heap = os_symbol_heap, os_var_heap = os_var_heap,
						   os_special_instances = os_special_instances, os_error = os_error, os_predef_symbols = os_predef_symbols })

	remove_sub_classes contexts type_heaps
		# (sub_classes, type_heaps) = foldSt generate_subclasses contexts ([], type_heaps)
		= (foldSt (remove_doubles sub_classes) contexts [], type_heaps)
		
	generate_subclasses {tc_class={glob_object={ds_index},glob_module},tc_types} (sub_classes, type_heaps)
		# {class_args,class_members,class_context,class_dictionary} = defs.[glob_module].com_class_defs.[ds_index]
		  th_vars = fold2St set_type class_args tc_types type_heaps.th_vars
		= foldSt subst_context class_context (sub_classes, { type_heaps & th_vars = th_vars })
	where
		set_type {tv_info_ptr} type type_var_heap
			= type_var_heap <:= (tv_info_ptr, TVI_Type type)
		  
		subst_context class_context (sub_classes, type_heaps)
			# (sub_class, type_heaps) = substitute class_context type_heaps
			= ([sub_class : sub_classes], type_heaps) 
		 
	remove_doubles sub_classes tc context
		| containsContext tc sub_classes
			= context
			= [tc : context]

	convert_dictionaries :: !{# CommonDefs } ![TypeContext] !(!SymbIdent,!ExprInfoPtr,![ClassApplication]) !(!*TypeHeaps, !*ExpressionHeap)
		-> !(!*TypeHeaps, !*ExpressionHeap)
	convert_dictionaries defs contexts (oc_symbol, over_info_ptr, class_applications) heaps
		= convertOverloadedCall defs contexts oc_symbol over_info_ptr class_applications heaps
	
selectFromDictionary  dict_mod dict_index member_index defs
	# (RecordType {rt_fields}) = defs.[dict_mod].com_type_defs.[dict_index].td_rhs
	  { fs_name, fs_index } = rt_fields.[member_index]
	= { glob_module = dict_mod, glob_object = { ds_ident = fs_name, ds_index = fs_index, ds_arity = 1 }}

getDictionaryConstructor {glob_module, glob_object = {ds_ident,ds_index}} defs	  
	# {class_dictionary} = defs.[glob_module].com_class_defs.[ds_index]
	  (RecordType {rt_constructor}) = defs.[glob_module].com_type_defs.[class_dictionary.ds_index].td_rhs
	= rt_constructor 

convertOverloadedCall :: !{#CommonDefs} ![TypeContext] !SymbIdent !ExprInfoPtr ![ClassApplication] !(!*TypeHeaps, !*ExpressionHeap)
		-> (!*TypeHeaps, !*ExpressionHeap)
convertOverloadedCall defs contexts {symb_name,symb_kind = SK_OverloadedFunction {glob_module,glob_object}, symb_arity} expr_ptr [class_appl:class_appls] heaps
	# mem_def = defs.[glob_module].com_member_defs.[glob_object]
	  (class_exprs, heaps) = convertClassApplsToExpressions defs contexts class_appls heaps
	  (inst_expr, (type_heaps, expr_heap)) = adjust_member_application defs contexts  mem_def symb_arity class_appl class_exprs heaps
	= (type_heaps, expr_heap <:= (expr_ptr, inst_expr))
where
	adjust_member_application defs contexts {me_symb,me_offset,me_class} symb_arity (CA_Instance red_contexts) class_exprs heaps
		# ({glob_module,glob_object}, red_contexts) = find_instance_of_member me_class me_offset red_contexts
		  (exprs, heaps) = convertClassApplsToExpressions defs contexts red_contexts heaps
		  class_exprs = exprs ++ class_exprs
		= (EI_Instance { glob_module = glob_module, glob_object = { ds_ident = me_symb, ds_arity = length class_exprs, ds_index = glob_object }} class_exprs,
			 heaps)
	adjust_member_application  defs contexts  {me_symb,me_offset,me_class={glob_module,glob_object}} symb_arity (CA_Context tc) class_exprs (type_heaps, expr_heap)
		# (class_context, address, type_heaps) = determineContextAddress contexts defs tc type_heaps
		  {class_dictionary={ds_index}} = defs.[glob_module].com_class_defs.[glob_object]
		  selector = selectFromDictionary glob_module ds_index me_offset defs
		= (EI_Selection (generateClassSelection address [RecordSelection selector me_offset]) class_context.tc_var class_exprs, (type_heaps, expr_heap))
	
	adjust_member_application defs contexts  _ _ (CA_GlobalTypeCode {tci_index,tci_contexts}) _ heaps
		# (exprs, heaps) = convertClassApplsToExpressions defs contexts tci_contexts heaps
		= (EI_TypeCode (TCE_Constructor tci_index (map expressionToTypeCodeExpression exprs)), heaps)
	adjust_member_application defs contexts _ _ (CA_LocalTypeCode new_var_ptr) _  heaps
		= (EI_TypeCode (TCE_Var new_var_ptr), heaps)
	
	find_instance_of_member me_class me_offset { rcs_class_context = {rc_class, rc_inst_module, rc_inst_members, rc_red_contexts}, rcs_constraints_contexts}
		| rc_class.glob_module == me_class.glob_module && rc_class.glob_object.ds_index == me_class.glob_object
			= ({ glob_module = rc_inst_module, glob_object = rc_inst_members.[me_offset].ds_index }, rc_red_contexts)
			= find_instance_of_member_in_constraints me_class me_offset rcs_constraints_contexts
	where
		find_instance_of_member_in_constraints me_class me_offset [ rcs=:{rcs_constraints_contexts} : rcss ]
			= find_instance_of_member me_class me_offset {rcs & rcs_constraints_contexts = rcs_constraints_contexts ++ rcss}
		find_instance_of_member_in_constraints me_class me_offset []
			= abort "Error in module overloading: find_instance_of_member_in_constraints\n"
convertOverloadedCall defs contexts {symb_kind = SK_TypeCode} expr_info_ptr class_appls heaps
	# (class_expressions, (type_heaps, expr_heap)) = convertClassApplsToExpressions defs contexts class_appls heaps
	= (type_heaps, expr_heap <:= (expr_info_ptr, EI_TypeCodes (map expressionToTypeCodeExpression class_expressions)))	
convertOverloadedCall defs contexts {symb_name} expr_info_ptr appls heaps
	# (class_expressions, (type_heaps, expr_heap)) = convertClassApplsToExpressions defs contexts appls heaps
	= (type_heaps, expr_heap <:= (expr_info_ptr, EI_Context class_expressions))


expressionToTypeCodeExpression (TypeCodeExpression texpr) 			= texpr
expressionToTypeCodeExpression (Var {var_info_ptr})					= TCE_Var var_info_ptr

generateClassSelection address last_selectors
	= mapAppend (\(off_set,selector) -> RecordSelection selector off_set) address last_selectors
	
convertClassApplsToExpressions defs contexts cl_appls  heaps
	= mapSt (convert_class_appl_to_expression defs contexts) cl_appls heaps
where
	convert_class_appl_to_expression defs contexts (CA_Instance {rcs_class_context,rcs_constraints_contexts}) heaps
		# (class_symb, class_members, instance_types, heaps)
				= convert_reduced_context_to_expression defs contexts rcs_class_context heaps
		  (members_of_constraints, (type_heaps, expr_heap))
		  		= convert_list_of_reduced_contexts_to_expressions defs contexts rcs_constraints_contexts heaps
		  {ds_ident,ds_index,ds_arity} = getDictionaryConstructor class_symb defs
		  record_symbol = { symb_name = ds_ident, symb_kind = SK_Constructor {glob_module = class_symb.glob_module, glob_object = ds_index}, symb_arity = ds_arity }
		  (app_info_ptr, expr_heap) = newPtr (EI_ClassTypes instance_types) expr_heap
		= (App { app_symb = record_symbol, app_args = class_members ++ members_of_constraints, app_info_ptr = app_info_ptr }, (type_heaps, expr_heap))
	convert_class_appl_to_expression defs contexts (CA_Context tc) (type_heaps, expr_heap)
		# (class_context, context_address, type_heaps) = determineContextAddress contexts defs tc type_heaps
		| isEmpty context_address
			= (ClassVariable class_context.tc_var, (type_heaps, expr_heap))
			= (Selection No (ClassVariable class_context.tc_var) (generateClassSelection context_address []), (type_heaps, expr_heap))
	convert_class_appl_to_expression defs contexts (CA_LocalTypeCode new_var_ptr) heaps
		= (TypeCodeExpression (TCE_Var new_var_ptr), heaps)
	convert_class_appl_to_expression defs contexts (CA_GlobalTypeCode {tci_index,tci_contexts}) heaps
		# (exprs, heaps) = convertClassApplsToExpressions defs contexts tci_contexts heaps
		= (TypeCodeExpression (TCE_Constructor tci_index (map expressionToTypeCodeExpression exprs)), heaps)
	
	convert_reduced_context_to_expression defs contexts {rc_class, rc_inst_module, rc_inst_members, rc_red_contexts, rc_types} heaps
		# (expressions, heaps) = convertClassApplsToExpressions defs contexts rc_red_contexts heaps
		  members = build_class_members 0 rc_inst_members rc_inst_module expressions (length expressions)
		= (rc_class, members, rc_types, heaps)
	where
		build_class_members mem_offset ins_members mod_index class_arguments arity
			| mem_offset == size ins_members
				= []
				# expressions = build_class_members (inc mem_offset) ins_members mod_index class_arguments arity
				  {ds_ident,ds_index} = ins_members.[mem_offset]
				= [ App { app_symb = { symb_name = ds_ident, symb_kind = SK_Function { glob_object = ds_index, glob_module = mod_index },
						symb_arity = arity }, app_args = class_arguments, app_info_ptr = nilPtr } : expressions ]

	convert_list_of_reduced_contexts_to_expressions defs contexts list_of_rcs heaps
		= mapSt (convert_reduced_contexts_to_expressions defs contexts) list_of_rcs heaps
	
	convert_reduced_contexts_to_expressions defs contexts {rcs_class_context,rcs_constraints_contexts} heaps
		# (class_symb, rc_exprs, instance_types, heaps)
				= convert_reduced_context_to_expression defs contexts rcs_class_context heaps
		  (rcs_exprs, (type_heaps, expr_heap))
				= convert_list_of_reduced_contexts_to_expressions defs contexts rcs_constraints_contexts heaps
		  {ds_ident,ds_index,ds_arity} = getDictionaryConstructor class_symb defs
		  record_symbol = { symb_name = ds_ident, symb_kind = SK_Constructor {glob_module = class_symb.glob_module, glob_object = ds_index}, symb_arity = ds_arity }
		  (app_info_ptr, expr_heap) = newPtr (EI_ClassTypes instance_types) expr_heap
		  rc_record = App { app_symb = record_symbol, app_args = rc_exprs ++ rcs_exprs, app_info_ptr = app_info_ptr }
		= (rc_record, (type_heaps, expr_heap))
	

determineContextAddress :: ![TypeContext] !{#CommonDefs} !TypeContext !*TypeHeaps
	-> (!TypeContext, ![(Int, Global DefinedSymbol)], !*TypeHeaps)
determineContextAddress contexts defs this_context type_heaps
	= look_up_context_and_address this_context contexts defs type_heaps
where
	look_up_context_and_address :: !TypeContext ![TypeContext] !{#CommonDefs} !*TypeHeaps -> (TypeContext, [(Int, Global DefinedSymbol)], !*TypeHeaps)
	look_up_context_and_address context []  defs type_heaps
		= abort "look_up_context_and_address (overloading.icl)"
	look_up_context_and_address this_context [tc : tcs] defs type_heaps 
		#! (may_be_addres, type_heaps) = determine_address this_context tc [] defs type_heaps
		= case may_be_addres of
			Yes address
				-> (tc, address, type_heaps)
			No
				-> look_up_context_and_address this_context tcs defs type_heaps

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
	where
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
		

getClassVariable :: !Ident !VarInfoPtr !*VarHeap !*ErrorAdmin -> (!Ident, !VarInfoPtr, !*VarHeap, !*ErrorAdmin)
getClassVariable symb var_info_ptr var_heap error
	= case (readPtr var_info_ptr var_heap) of
		(VI_ClassVar var_name new_info_ptr count, var_heap)
			-> (var_name, new_info_ptr, var_heap <:= (var_info_ptr, VI_ClassVar var_name new_info_ptr (inc count)), error)
		(_, var_heap)
			-> (symb, var_info_ptr, var_heap, overloadingError symb error)


updateDynamics :: ![Index] ![LocalTypePatternVariable] !*{#FunDef} !*{! FunctionType} !*ExpressionHeap !*TypeCodeInfo !*VarHeap !*ErrorAdmin
	-> (!*{#FunDef},  !*{! FunctionType}, !*ExpressionHeap, !*TypeCodeInfo, !*VarHeap, !*ErrorAdmin)
updateDynamics funs type_pattern_vars fun_defs fun_env symbol_heap type_code_info var_heap error
	| error.ea_ok
		= update_dynamics funs type_pattern_vars fun_defs fun_env symbol_heap type_code_info var_heap error
		= (fun_defs, fun_env, symbol_heap, type_code_info, var_heap, error)	
where
	update_dynamics [] type_pattern_vars fun_defs fun_env symbol_heap type_code_info var_heap error
		= (fun_defs, fun_env, symbol_heap, type_code_info, var_heap,  error)
	update_dynamics [fun:funs] type_pattern_vars fun_defs fun_env symbol_heap type_code_info var_heap error
		#! fun_def = fun_defs.[fun]
		# {fun_body,fun_info={fi_group_index, fi_dynamics}} = fun_def
		| isEmpty fi_dynamics
			= update_dynamics funs type_pattern_vars fun_defs fun_env symbol_heap type_code_info var_heap error
		  	# (type_code_info, symbol_heap, type_pattern_vars, var_heap)
		  			= convertDynamicTypes fi_dynamics (type_code_info, symbol_heap, type_pattern_vars, var_heap)
		  	  (TransformedBody tb) = fun_body
		  	  (tb_rhs, {ui_instance_calls, ui_symbol_heap, ui_var_heap, ui_fun_defs, ui_fun_env, ui_error}) = updateExpression fi_group_index tb.tb_rhs
					{ ui_instance_calls = [], ui_symbol_heap = symbol_heap, ui_fun_defs = fun_defs,
					  ui_fun_env = fun_env, ui_var_heap = var_heap, ui_error = error }
		 	  fun_def = { fun_def & fun_body = TransformedBody {tb & tb_rhs = tb_rhs}}
			= update_dynamics funs type_pattern_vars { ui_fun_defs & [fun] = fun_def } ui_fun_env  ui_symbol_heap type_code_info ui_var_heap ui_error

removeOverloadedFunctions :: ![Index] ![LocalTypePatternVariable] !*{#FunDef} !*{! FunctionType} !*ExpressionHeap
	!*TypeCodeInfo !*VarHeap !*ErrorAdmin
		-> (!*{#FunDef}, !*{! FunctionType}, !*ExpressionHeap, !*TypeCodeInfo, !*VarHeap, !*ErrorAdmin)
removeOverloadedFunctions group type_pattern_vars fun_defs fun_env symbol_heap type_code_info var_heap error
	| error.ea_ok
		# (fun_defs, fun_env, symbol_heap, type_code_info, var_heap, error)
			= foldSt (remove_overloaded_function type_pattern_vars) group (fun_defs, fun_env, symbol_heap, type_code_info, var_heap, error)
		= (fun_defs, fun_env, symbol_heap, type_code_info, var_heap, error)
where
	remove_overloaded_function type_pattern_vars fun_index (fun_defs, fun_env, symbol_heap, type_code_info, var_heap, error)
		# (fun_def, fun_defs) = fun_defs![fun_index]
		  (CheckedType {st_context}, fun_env) = fun_env![fun_index]
		  {fun_body = TransformedBody {tb_args,tb_rhs},fun_info,fun_arity,fun_symb,fun_pos} = fun_def
		  (rev_variables, var_heap) = foldSt determine_class_argument st_context ([], var_heap)
//		  		 ---> ("remove_overloaded_function", fun_symb, st_context))
		  error = setErrorAdmin (newPosition fun_symb fun_pos) error
		  (type_code_info, symbol_heap, type_pattern_vars, var_heap) = convertDynamicTypes fun_info.fi_dynamics (type_code_info, symbol_heap, type_pattern_vars, var_heap)
		  (tb_rhs, {ui_instance_calls, ui_symbol_heap, ui_var_heap, ui_fun_defs, ui_fun_env, ui_error})
		  		= updateExpression fun_info.fi_group_index tb_rhs {  ui_instance_calls = [], ui_symbol_heap = symbol_heap,
		  				ui_var_heap = var_heap, ui_fun_defs = fun_defs, ui_fun_env = fun_env, ui_error = error }
		  (tb_args, var_heap) = foldSt retrieve_class_argument rev_variables (tb_args, ui_var_heap)
		  fun_def = { fun_def & fun_body = TransformedBody {tb_args = tb_args, tb_rhs = tb_rhs},
		  								  fun_arity = length tb_args, fun_info = { fun_info & fi_calls = fun_info.fi_calls ++ ui_instance_calls } }
		= ({ ui_fun_defs & [fun_index] = fun_def }, ui_fun_env, ui_symbol_heap, type_code_info, var_heap, ui_error)
//			---> ("remove_overloaded_function", fun_symb, tb_args, tb_rhs)

	determine_class_argument {tc_class={glob_object={ds_ident={id_name}}}, tc_var} (variables, var_heap)
		# (var_info, var_heap) = readPtr tc_var var_heap
		= case var_info of 
			VI_ForwardClassVar var_info_ptr
				# (var_info, var_heap) = readPtr var_info_ptr var_heap
//				  (new_info_ptr, var_heap) = newPtr VI_Empty var_heap
//				-> ([var_info_ptr : variables], var_heap <:= (var_info_ptr, VI_ClassVar (build_var_name id_name) new_info_ptr 0 var_info))

				-> case var_info of
					VI_Empty
						# (new_info_ptr, var_heap) = newPtr VI_Empty var_heap
						-> ([var_info_ptr : variables], var_heap <:= (var_info_ptr, VI_ClassVar (build_var_name id_name) new_info_ptr 0))
					_
						-> abort "determine_class_argument (overloading.icl)"

			VI_Empty
				# (new_info_ptr, var_heap) = newPtr VI_Empty var_heap
				-> ([tc_var : variables], var_heap <:= (tc_var, VI_ClassVar (build_var_name id_name) new_info_ptr 0))
			_
				-> abort "determine_class_argument (overloading.icl)"

	build_var_name id_name
		= { id_name = "_v" +++ id_name, id_info = nilPtr }

	retrieve_class_argument var_info_ptr (args, var_heap)
		# (VI_ClassVar var_name new_info_ptr count, var_heap) = readPtr var_info_ptr var_heap
		= ([{fv_name = var_name, fv_info_ptr = new_info_ptr, fv_def_level = NotALevel, fv_count = count } : args], var_heap <:= (var_info_ptr, VI_Empty))

convertDynamicTypes dyn_ptrs update_info
	= foldSt update_dynamic dyn_ptrs update_info
where		
	update_dynamic dyn_ptr (type_code_info, expr_heap, type_pattern_vars, var_heap)
		# (dyn_info, expr_heap) = readPtr dyn_ptr expr_heap
		= case dyn_info of
			EI_TempDynamicType (Yes {dt_global_vars, dt_uni_vars, dt_type}) _ _ expr_ptr _
				# (expr_info, expr_heap) = readPtr expr_ptr expr_heap
				-> case expr_info of
					EI_TypeCodes type_codes
						# type_var_heap = fold2St (\{tv_info_ptr} type_code -> writePtr tv_info_ptr (TVI_TypeCode type_code))
														dt_global_vars type_codes type_code_info.tci_type_var_heap
						  (uni_vars, (type_var_heap, var_heap)) = new_type_variables dt_uni_vars (type_var_heap, var_heap)
						  (type_code_expr, type_code_info) = toTypeCodeExpression dt_type { type_code_info & tci_type_var_heap = type_var_heap }
						-> (type_code_info, expr_heap <:= (dyn_ptr, EI_TypeOfDynamic uni_vars type_code_expr), type_pattern_vars, var_heap)
					EI_Empty
						# (uni_vars, (type_var_heap, var_heap)) = new_type_variables dt_uni_vars (type_code_info.tci_type_var_heap, var_heap)
						  (type_code_expr, type_code_info) = toTypeCodeExpression dt_type { type_code_info & tci_type_var_heap = type_var_heap }
						-> (type_code_info, expr_heap <:= (dyn_ptr, EI_TypeOfDynamic uni_vars type_code_expr), type_pattern_vars, var_heap)
			EI_TempDynamicType No _ _ expr_ptr _
				# (expr_info, expr_heap) = readPtr expr_ptr expr_heap
				-> case expr_info of
					EI_TypeCode type_expr
						-> (type_code_info, expr_heap <:= (dyn_ptr, EI_TypeOfDynamic [] type_expr), type_pattern_vars, var_heap)
					EI_Selection selectors record_var _
						# (_, var_info_ptr, var_heap) = abort "getClassVariable record_var var_heap (overloading.icl)"
						-> (type_code_info, expr_heap <:= (dyn_ptr, EI_TypeOfDynamic [] (convert_selectors selectors var_info_ptr)), type_pattern_vars, var_heap)
			EI_TempDynamicPattern type_vars {dt_global_vars, dt_type} loc_dynamics temp_local_vars _ _ expr_ptr _
				# (expr_info, expr_heap) = readPtr expr_ptr expr_heap
				-> case expr_info of
					EI_TypeCodes type_codes
						# type_var_heap = fold2St (\{tv_info_ptr} type_code -> writePtr tv_info_ptr (TVI_TypeCode type_code)) dt_global_vars type_codes type_code_info.tci_type_var_heap
						  (var_ptrs, (type_pattern_vars, var_heap)) = mapSt addLocalTCInstance temp_local_vars (type_pattern_vars, var_heap)
						  type_var_heap = fold2St (\{tv_info_ptr} var_ptr -> writePtr tv_info_ptr (TVI_TypeCode (TCE_Var var_ptr))) type_vars var_ptrs type_var_heap
						  (type_code_expr, type_code_info) = toTypeCodeExpression dt_type { type_code_info & tci_type_var_heap = type_var_heap }
						-> convert_local_dynamics loc_dynamics (type_code_info, expr_heap <:= (dyn_ptr, EI_TypeOfDynamicPattern var_ptrs type_code_expr), type_pattern_vars, var_heap)
					EI_Empty
						# (var_ptrs, (type_pattern_vars, var_heap)) = mapSt addLocalTCInstance temp_local_vars (type_pattern_vars, var_heap)
						  type_var_heap = fold2St (\{tv_info_ptr} var_ptr -> writePtr tv_info_ptr (TVI_TypeCode (TCE_Var var_ptr))) type_vars var_ptrs type_code_info.tci_type_var_heap
						  (type_code_expr, type_code_info) = toTypeCodeExpression dt_type { type_code_info & tci_type_var_heap = type_var_heap }
						-> convert_local_dynamics loc_dynamics (type_code_info, expr_heap <:= (dyn_ptr, EI_TypeOfDynamicPattern var_ptrs type_code_expr), type_pattern_vars, var_heap)
					
	where
		convert_local_dynamics loc_dynamics state
			= foldSt update_dynamic loc_dynamics state

		convert_selectors [type_code_selector] var_info_ptr
			= TCE_Var var_info_ptr
		convert_selectors selectors var_info_ptr
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
	,	ui_var_heap			:: !.VarHeap
	,	ui_fun_defs			:: !.{# FunDef}
	,	ui_fun_env			:: !.{! FunctionType}
	,	ui_error			:: !.ErrorAdmin
	}

class updateExpression e :: !Index !e !*UpdateInfo -> (!e, !*UpdateInfo)


instance updateExpression Expression
where
	updateExpression group_index (App app=:{app_symb=symb=:{symb_kind,symb_arity,symb_name},app_args,app_info_ptr}) ui
		# (app_args, ui) = updateExpression group_index app_args ui
		| isNilPtr app_info_ptr
			= (App { app & app_args = app_args }, ui)
			#! symb_info = sreadPtr app_info_ptr ui.ui_symbol_heap
			= case symb_info of
				EI_Empty
					#! fun_index = get_recursive_fun_index group_index symb_kind ui.ui_fun_defs
					| fun_index == NoIndex
						-> (App { app & app_args = app_args }, ui)
						# (CheckedType {st_context}, ui) = ui!ui_fun_env.[fun_index]
						  (app_args, (ui_var_heap, ui_error)) = mapAppendSt (build_context_arg symb_name) st_context app_args (ui.ui_var_heap, ui.ui_error)
						-> (App { app & app_symb = { symb & symb_arity = symb_arity + length st_context}, app_args = app_args },
									{ ui & ui_var_heap = ui_var_heap, ui_error = ui_error })
				EI_Context context_args
					# (app_args, (ui_var_heap, ui_error)) = adjustClassExpressions symb_name context_args app_args (ui.ui_var_heap, ui.ui_error)
					#! fun_index = get_recursive_fun_index group_index symb_kind ui.ui_fun_defs
					| fun_index == NoIndex
						# app = { app & app_symb = { symb & symb_arity = length context_args + symb_arity }, app_args = app_args}
						-> (App app, examine_calls context_args { ui & ui_var_heap = ui_var_heap, ui_error = ui_error })
						# (CheckedType {st_context}, ui) = ui!ui_fun_env.[fun_index]
						  nr_of_context_args = length context_args
						  nr_of_lifted_contexts = length st_context - nr_of_context_args
						  (app_args, (ui_var_heap, ui_error)) = mapAppendSt (build_context_arg symb_name) (take nr_of_lifted_contexts st_context) app_args (ui_var_heap, ui_error)
						-> (App { app & app_symb = { symb & symb_arity = nr_of_lifted_contexts + nr_of_context_args + symb_arity }, app_args = app_args },
									examine_calls context_args { ui & ui_var_heap = ui_var_heap, ui_error = ui_error })
				EI_Instance inst_symbol context_args
					# (context_args, (ui_var_heap, ui_error)) = adjustClassExpressions symb_name context_args [] (ui.ui_var_heap, ui.ui_error)
					-> (build_application inst_symbol context_args app_args symb_arity app_info_ptr,
							examine_calls context_args (new_call inst_symbol.glob_module inst_symbol.glob_object.ds_index
								{ ui & ui_var_heap = ui_var_heap, ui_error = ui_error }))
				EI_Selection selectors record_var context_args
					# (all_args, (ui_var_heap, ui_error)) = adjustClassExpressions symb_name context_args app_args (ui.ui_var_heap, ui.ui_error)
					  (var_name, var_info_ptr, ui_var_heap, ui_error) = getClassVariable symb_name record_var ui_var_heap ui_error
					  select_expr = Selection No (Var { var_name = var_name, var_info_ptr = var_info_ptr, var_expr_ptr = nilPtr }) selectors
					| isEmpty all_args
						-> (select_expr, { ui & ui_var_heap = ui_var_heap, ui_error = ui_error })
						-> (select_expr @ all_args, examine_calls context_args { ui & ui_var_heap = ui_var_heap, ui_error = ui_error })


	where
		build_context_arg symb {tc_var} (var_heap, error)
			# (var_info, var_heap) = readPtr tc_var var_heap
			= case var_info of
				VI_ForwardClassVar var_info_ptr
					# (var_name, var_info_ptr, var_heap, error) = getClassVariable symb var_info_ptr var_heap error
					-> (Var { var_name = var_name, var_info_ptr = var_info_ptr, var_expr_ptr = nilPtr }, (var_heap, error))
				VI_ClassVar var_name new_info_ptr count
					-> (Var { var_name = var_name, var_info_ptr = new_info_ptr, var_expr_ptr = nilPtr },
								(var_heap <:= (tc_var, VI_ClassVar var_name new_info_ptr (inc count)), error))
				_
					-> abort "build_context_arg (overloading.icl)"

		get_recursive_fun_index group_index (SK_Function {glob_module,glob_object}) fun_defs
			| glob_module == cIclModIndex
				# ({fun_info={fi_group_index}, fun_index}, fun_defs) = fun_defs![glob_object]
				| fi_group_index == group_index
					= fun_index 
					= NoIndex
				= NoIndex
		get_recursive_fun_index group_index _ fun_defs
			= NoIndex

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
		
			
	updateExpression group_index (expr @ exprs) ui
		# ((expr, exprs), ui) = updateExpression group_index (expr, exprs) ui
		= (expr @ exprs, ui)
	updateExpression group_index (Let lad=:{let_lazy_binds, let_strict_binds, let_expr}) ui
		# (let_lazy_binds, ui)		= updateExpression group_index let_lazy_binds ui
		# (let_strict_binds, ui)	= updateExpression group_index let_strict_binds ui
		# (let_expr, ui)			= updateExpression group_index let_expr ui
		= (Let {lad & let_lazy_binds = let_lazy_binds, let_strict_binds = let_strict_binds, let_expr = let_expr}, ui)
	updateExpression group_index (Case kees=:{case_expr,case_guards,case_default}) ui
		# ((case_expr,(case_guards,case_default)), ui) = updateExpression group_index (case_expr,(case_guards,case_default)) ui
		= (Case { kees & case_expr = case_expr, case_guards = case_guards, case_default = case_default }, ui)
	updateExpression group_index (Selection is_unique expr selectors) ui
		# (expr, ui) = updateExpression group_index expr ui
		  (selectors, ui) = updateExpression group_index selectors ui
		= (Selection is_unique expr selectors, ui)
	updateExpression group_index (Update expr1 selectors expr2) ui
		# (expr1, ui) = updateExpression group_index expr1 ui
		  (selectors, ui) = updateExpression group_index selectors ui
		  (expr2, ui) = updateExpression group_index expr2 ui
		= (Update expr1 selectors expr2, ui)
	updateExpression group_index (RecordUpdate cons_symbol expression expressions) ui
		# (expression, ui) = updateExpression group_index expression ui
		  (expressions, ui) = updateExpression group_index expressions ui
		= (RecordUpdate cons_symbol expression expressions, ui)
	updateExpression group_index (DynamicExpr dyn=:{dyn_expr,dyn_info_ptr}) ui
		# (dyn_expr, ui) = updateExpression group_index dyn_expr ui
		  (EI_TypeOfDynamic uni_vars type_code, ui_symbol_heap) = readPtr dyn_info_ptr ui.ui_symbol_heap
		= (DynamicExpr { dyn & dyn_expr = dyn_expr, dyn_type_code = type_code, dyn_uni_vars = uni_vars }, { ui & ui_symbol_heap = ui_symbol_heap })
	updateExpression group_index (MatchExpr opt_tuple cons_symbol expr) ui
		# (expr, ui) = updateExpression group_index expr ui
		= (MatchExpr opt_tuple cons_symbol expr, ui)
	updateExpression group_index (TupleSelect symbol argn_nr expr) ui
		# (expr, ui) = updateExpression group_index expr ui
		= (TupleSelect symbol argn_nr expr, ui)
	updateExpression group_index expr ui
		= (expr, ui)

instance updateExpression Bind a b | updateExpression a
where
	updateExpression group_index bind=:{bind_src} ui
		# (bind_src, ui) = updateExpression group_index bind_src ui
		= ({bind & bind_src = bind_src }, ui)

instance updateExpression Optional a | updateExpression a
where
	updateExpression group_index (Yes x) ui
		# (x, ui) = updateExpression group_index x ui
		= (Yes x, ui)
	updateExpression group_index No ui
		= (No, ui)

instance updateExpression CasePatterns
where
	updateExpression group_index (AlgebraicPatterns type patterns) ui
		# (patterns, ui) =  updateExpression group_index patterns ui
		= (AlgebraicPatterns type patterns, ui)
	updateExpression group_index (BasicPatterns type patterns) ui
		# (patterns, ui) =  updateExpression group_index patterns ui
		= (BasicPatterns type patterns, ui)
	updateExpression group_index (DynamicPatterns patterns) ui
		# (patterns, ui) =  updateExpression group_index patterns ui
		= (DynamicPatterns patterns, ui)
	
instance updateExpression AlgebraicPattern
where
	updateExpression group_index pattern=:{ap_vars,ap_expr} ui
		# (ap_expr, ui) =  updateExpression group_index ap_expr ui
		= ({ pattern & ap_expr = ap_expr }, ui)

instance updateExpression BasicPattern
where
	updateExpression group_index pattern=:{bp_expr} ui
		# (bp_expr, ui) = updateExpression group_index bp_expr ui
		= ({ pattern & bp_expr = bp_expr }, ui)

instance updateExpression Selection
where
  	updateExpression group_index (ArraySelection selector=:{glob_object={ds_ident}} expr_ptr index_expr) ui
		# (index_expr, ui) = updateExpression group_index index_expr ui
		#! symb_info = sreadPtr expr_ptr ui.ui_symbol_heap
		= case symb_info of
			EI_Instance array_select []
				-> (ArraySelection array_select expr_ptr index_expr, ui)
			EI_Selection selectors record_var context_args
				# (var_name, var_info_ptr, ui_var_heap, ui_error) = getClassVariable ds_ident record_var ui.ui_var_heap ui.ui_error
				-> (DictionarySelection { var_name = var_name, var_info_ptr = var_info_ptr, var_expr_ptr = nilPtr } selectors expr_ptr index_expr,
							{ ui & ui_var_heap = ui_var_heap, ui_error = ui_error })
  	updateExpression group_index selection ui
		= (selection, ui)

instance updateExpression TypeCase
where
	updateExpression group_index type_case=:{type_case_dynamic,type_case_patterns,type_case_default} ui
		# ((type_case_dynamic,(type_case_patterns,type_case_default)), ui) = updateExpression group_index
				(type_case_dynamic,(type_case_patterns,type_case_default)) ui
		= ({ type_case & type_case_dynamic = type_case_dynamic, type_case_patterns = type_case_patterns, type_case_default = type_case_default }, ui)
	
instance updateExpression DynamicPattern
where
	updateExpression group_index dp=:{dp_type,dp_rhs} ui
		# (dp_rhs, ui) =  updateExpression group_index dp_rhs ui
		  (EI_TypeOfDynamicPattern type_pattern_vars type_code, ui_symbol_heap) = readPtr dp_type ui.ui_symbol_heap
		= ({ dp & dp_rhs = dp_rhs, dp_type_patterns_vars = type_pattern_vars, dp_type_code = type_code }, { ui & ui_symbol_heap = ui_symbol_heap })

instance updateExpression (a,b) | updateExpression a & updateExpression b
where
	updateExpression group_index t ui
		= app2St (updateExpression group_index,updateExpression group_index) t ui

instance updateExpression [e] | updateExpression e
where
	updateExpression group_index l ui
		= mapSt (updateExpression group_index) l ui

adjustClassExpressions symb_name exprs tail_exprs var_heap_error 
	= mapAppendSt (adjustClassExpression symb_name) exprs tail_exprs var_heap_error
where
	adjustClassExpression symb_name (App app=:{app_args}) var_heap_error
		# (app_args, var_heap_error) = adjustClassExpressions symb_name  app_args [] var_heap_error
		= (App { app & app_args = app_args }, var_heap_error)
	adjustClassExpression symb_name (ClassVariable var_info_ptr) (var_heap, error)
		# (var_name, var_info_ptr, var_heap, error) = getClassVariable symb_name var_info_ptr var_heap error
		= (Var { var_name = var_name, var_info_ptr = var_info_ptr, var_expr_ptr = nilPtr }, (var_heap, error))
	adjustClassExpression symb_name (Selection opt_type expr selectors) var_heap_error
		# (expr, var_heap_error) = adjustClassExpression symb_name expr var_heap_error
		= (Selection opt_type expr selectors, var_heap_error)
	adjustClassExpression symb_name  expr var_heap_error
		= (expr, var_heap_error)

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
	(<<<) file tc = file <<< tc.tc_class.glob_object.ds_ident <<< ' ' <<< tc.tc_types <<< " <" <<< tc.tc_var <<< '>'

instance <<< FunCall
where
	(<<<) file {fc_index} = file <<< fc_index
	

instance <<< Special
where
	(<<<) file {spec_types} = file <<< spec_types

instance <<< (Ptr x)
where
	(<<<) file ptr = file <<< '<' <<< ptrToInt ptr <<< '>'
	
instance <<< TypeCodeExpression
where
	(<<<) file _ = file


instance <<< DefinedSymbol
where
	(<<<) file ds = file <<< ds.ds_ident

instance <<< ExprInfo
where
	(<<<) file (EI_Instance symb exprs) = file <<< symb <<< exprs
	(<<<) file (EI_Selection sels var_ptr exprs) = file <<< sels <<< var_ptr <<< exprs
	(<<<) file (EI_Context exprs) = file <<< exprs
	(<<<) file _ = file
