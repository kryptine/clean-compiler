implementation module checkFunctionBodies

import syntax, typesupport, parse, checksupport, utilities, checktypes, transform, predef //, RWSDebug
import explicitimports, comparedefimp

cIsInExpressionList		:== True
cIsNotInExpressionList	:== False

cEndWithUpdate			:== True
cEndWithSelection		:== False

::	ExpressionState =
	{	es_expr_heap	:: !.ExpressionHeap
	,	es_var_heap			:: !.VarHeap
	,	es_type_heaps		:: !.TypeHeaps
	,	es_calls			:: ![FunCall]
	,	es_dynamics			:: ![ExprInfoPtr]
	,	es_fun_defs			:: !.{# FunDef}
	}
	
::	ExpressionInput =
	{	ei_expr_level	:: !Level
	,	ei_fun_index	:: !Index
	,	ei_fun_level	:: !Level
	,	ei_mod_index	:: !Index
//	,	ei_fun_kind		:: !FunKind
	}

::	PatternState =
	{	ps_var_heap :: !.VarHeap
	,	ps_fun_defs :: !.{# FunDef}
	}

::	PatternInput =
	{	pi_def_level		:: !Int
	,	pi_mod_index		:: !Index
	,	pi_is_node_pattern	:: !Bool
	}
	
::	ArrayPattern =
	{	ap_opt_var		:: !Optional (Bind Ident VarInfoPtr)
	,	ap_array_var	:: !FreeVar
	,	ap_selections	:: ![Bind FreeVar [ParsedExpr]]
	}

::	UnfoldMacroState =
	{	ums_var_heap	:: !.VarHeap
	,	ums_modules		:: !.{# DclModule}
	,	ums_cons_defs	:: !.{# ConsDef}
	,	ums_error		:: !.ErrorAdmin
	}

::	RecordKind = RK_Constructor | RK_Update | RK_UpdateToConstructor ![AuxiliaryPattern]

checkFunctionBodies :: !FunctionBody !.ExpressionInput !*ExpressionState !*ExpressionInfo !*CheckState -> (FunctionBody,[FreeVar],!.ExpressionState,.ExpressionInfo,!.CheckState);
checkFunctionBodies (ParsedBody [{pb_args,pb_rhs={rhs_alts,rhs_locals}, pb_position} : bodies]) e_input=:{ei_expr_level,ei_mod_index}
		e_state=:{es_var_heap, es_fun_defs} e_info cs
	# (aux_patterns, (var_env, array_patterns), {ps_var_heap, ps_fun_defs}, e_info, cs)
			= check_patterns pb_args {pi_def_level = ei_expr_level, pi_mod_index = ei_mod_index, pi_is_node_pattern = False} ([], [])
							{ps_var_heap = es_var_heap, ps_fun_defs = es_fun_defs} e_info cs 
	  (rhs_expr, free_vars, e_state, e_info, cs)
	  		= checkRhs [] rhs_alts rhs_locals e_input { e_state & es_var_heap = ps_var_heap, es_fun_defs = ps_fun_defs } e_info cs
	  (dynamics_in_rhs, e_state)
	  		= e_state!es_dynamics
	  (expr_with_array_selections, free_vars, e_state=:{es_var_heap}, e_info, cs)
			= addArraySelections array_patterns rhs_expr free_vars e_input e_state e_info cs
	  cs_symbol_table = removeLocalIdentsFromSymbolTable ei_expr_level var_env cs.cs_symbol_table
	  (cb_args, es_var_heap) = mapSt determine_function_arg aux_patterns es_var_heap
	  (rhss, free_vars, e_state=:{es_dynamics,es_expr_heap,es_var_heap}, e_info, cs)
	  		= check_function_bodies free_vars cb_args bodies e_input { e_state & es_dynamics = [], es_var_heap = es_var_heap } e_info
	  								{ cs & cs_symbol_table = cs_symbol_table }
	  (rhs, position, es_var_heap, es_expr_heap, dynamics_in_patterns, cs)
	  		= transform_patterns_into_cases aux_patterns cb_args expr_with_array_selections pb_position es_var_heap es_expr_heap
	  										dynamics_in_rhs cs
	= (CheckedBody { cb_args = cb_args, cb_rhs = [{ ca_rhs = rhs, ca_position = position } : rhss] }, free_vars,
		{ e_state & es_var_heap = es_var_heap, es_expr_heap = es_expr_heap, es_dynamics = dynamics_in_patterns ++ es_dynamics }, e_info, cs)
where
	check_patterns [pattern : patterns] p_input accus var_store e_info cs
		# (aux_pat, accus, var_store, e_info, cs) = checkPattern pattern No p_input accus var_store e_info cs
		  (aux_pats, accus, var_store, e_info, cs) = check_patterns patterns p_input accus var_store e_info cs
		= ([aux_pat : aux_pats], accus, var_store, e_info, cs)
	check_patterns [] p_input accus var_store e_info cs
		= ([], accus, var_store, e_info, cs)

	determine_function_arg (AP_Variable name var_info (Yes {bind_src, bind_dst})) var_store
		= ({ fv_name = bind_src, fv_info_ptr = bind_dst, fv_def_level = NotALevel, fv_count = 0 }, var_store)
	determine_function_arg (AP_Variable name var_info No) var_store
		= ({ fv_name = name, fv_info_ptr = var_info, fv_def_level = NotALevel, fv_count = 0 }, var_store)
	determine_function_arg (AP_Algebraic _ _ _ opt_var) var_store
		# ({bind_src,bind_dst}, var_store) = determinePatternVariable opt_var var_store
		= ({ fv_name = bind_src, fv_info_ptr = bind_dst, fv_def_level = NotALevel, fv_count = 0 }, var_store)
	determine_function_arg (AP_Basic _ opt_var) var_store
		# ({bind_src,bind_dst}, var_store) = determinePatternVariable opt_var var_store
		= ({ fv_name = bind_src, fv_info_ptr = bind_dst, fv_def_level = NotALevel, fv_count = 0 }, var_store)
	determine_function_arg (AP_Dynamic _ _ opt_var) var_store
		# ({bind_src,bind_dst}, var_store) = determinePatternVariable opt_var var_store
		= ({ fv_name = bind_src, fv_info_ptr = bind_dst, fv_def_level = NotALevel, fv_count = 0 }, var_store)
	determine_function_arg _ var_store
		# ({bind_src,bind_dst}, var_store) = determinePatternVariable No var_store
		= ({ fv_name = bind_src, fv_info_ptr = bind_dst, fv_def_level = NotALevel, fv_count = 0 }, var_store)
	
	check_function_bodies free_vars fun_args [{pb_args,pb_rhs={rhs_alts,rhs_locals},pb_position} : bodies]
							e_input=:{ei_expr_level,ei_mod_index} e_state=:{es_var_heap,es_fun_defs} e_info cs
		# (aux_patterns, (var_env, array_patterns), {ps_var_heap, ps_fun_defs}, e_info, cs)
				= check_patterns pb_args { pi_def_level = ei_expr_level, pi_mod_index = ei_mod_index, pi_is_node_pattern = False } ([], [])
					{ps_var_heap = es_var_heap, ps_fun_defs = es_fun_defs} e_info cs
		  e_state = { e_state & es_var_heap = ps_var_heap, es_fun_defs = ps_fun_defs}
		  (rhs_expr, free_vars, e_state, e_info, cs) = checkRhs free_vars rhs_alts rhs_locals e_input e_state e_info cs
		  (rhs_expr, free_vars, e_state=:{es_dynamics=dynamics_in_rhs}, e_info, cs)
				= addArraySelections array_patterns rhs_expr free_vars e_input e_state e_info cs
	 	  cs_symbol_table = removeLocalIdentsFromSymbolTable ei_expr_level var_env cs.cs_symbol_table
		  (rhs_exprs, free_vars, e_state=:{es_dynamics,es_expr_heap,es_var_heap}, e_info, cs)
		  		= check_function_bodies free_vars fun_args bodies e_input { e_state & es_dynamics = [] } e_info { cs & cs_symbol_table = cs_symbol_table }
		  (rhs_expr, position, es_var_heap, es_expr_heap, dynamics_in_patterns, cs)
		  		= transform_patterns_into_cases aux_patterns fun_args rhs_expr pb_position
		  										 es_var_heap es_expr_heap dynamics_in_rhs cs
		= ([{ ca_rhs = rhs_expr, ca_position = position } : rhs_exprs], free_vars,
			{ e_state & es_var_heap = es_var_heap, es_expr_heap = es_expr_heap,
			es_dynamics = dynamics_in_patterns ++ es_dynamics }, e_info, cs)
	check_function_bodies free_vars fun_args [] e_input e_state e_info cs
		= ([], free_vars, e_state, e_info, cs) 
		
	transform_patterns_into_cases [pattern : patterns] [fun_arg : fun_args] result_expr pattern_position
									var_store expr_heap opt_dynamics cs
		# (patterns_expr, pattern_position, var_store, expr_heap, opt_dynamics, cs)
				= transform_succeeding_patterns_into_cases patterns fun_args result_expr pattern_position
															var_store expr_heap opt_dynamics cs
		= transform_pattern_into_cases pattern fun_arg patterns_expr pattern_position var_store expr_heap opt_dynamics cs
	where
		transform_succeeding_patterns_into_cases [] _ result_expr pattern_position var_store expr_heap opt_dynamics cs
			= (result_expr, pattern_position, var_store, expr_heap, opt_dynamics, cs)
		transform_succeeding_patterns_into_cases [pattern : patterns] [fun_arg : fun_args] result_expr pattern_position
												var_store expr_heap opt_dynamics cs
			# (patterns_expr, pattern_position, var_store, expr_heap, opt_dynamics, cs)
				= transform_succeeding_patterns_into_cases patterns fun_args result_expr pattern_position
															var_store expr_heap opt_dynamics cs
			= transform_pattern_into_cases pattern fun_arg patterns_expr pattern_position var_store expr_heap opt_dynamics cs

	transform_patterns_into_cases [] _ result_expr pattern_position var_store expr_heap opt_dynamics cs
		= (result_expr, pattern_position, var_store, expr_heap, opt_dynamics, cs)

	transform_pattern_into_cases :: !AuxiliaryPattern !FreeVar !Expression !Position !*VarHeap !*ExpressionHeap ![DynamicPtr] !*CheckState
		-> (!Expression, !Position, !*VarHeap, !*ExpressionHeap, ![DynamicPtr], !*CheckState)
	transform_pattern_into_cases (AP_Variable name var_info opt_var) fun_arg=:{fv_info_ptr,fv_name} result_expr pattern_position
									var_store expr_heap opt_dynamics cs
		= case opt_var of
			Yes {bind_src, bind_dst}
				| bind_dst == fv_info_ptr
					# (var_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
					  (let_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
					-> (Let { let_strict_binds = [], let_lazy_binds= [
								{ lb_src = Var { var_name = fv_name, var_info_ptr = fv_info_ptr, var_expr_ptr = var_expr_ptr },
									lb_dst = { fv_name = name, fv_info_ptr = var_info, fv_def_level = NotALevel, fv_count = 0 },
									lb_position = NoPos }],
							  let_expr = result_expr, let_info_ptr = let_expr_ptr, let_expr_position = NoPos }, 
						pattern_position, var_store, expr_heap, opt_dynamics, cs)
					# (var_expr_ptr1, expr_heap) = newPtr EI_Empty expr_heap
					  (var_expr_ptr2, expr_heap) = newPtr EI_Empty expr_heap
					  (let_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
					-> (Let { let_strict_binds = [], let_lazy_binds= [
								{ lb_src = Var { var_name = fv_name, var_info_ptr = fv_info_ptr, var_expr_ptr = var_expr_ptr1 },
									lb_dst = { fv_name = name, fv_info_ptr = var_info, fv_def_level = NotALevel, fv_count = 0 },
									lb_position = NoPos },
								{ lb_src = Var { var_name = fv_name, var_info_ptr = fv_info_ptr, var_expr_ptr = var_expr_ptr2 },
									lb_dst = { fv_name = bind_src, fv_info_ptr = bind_dst, fv_def_level = NotALevel, fv_count = 0 },
									lb_position = NoPos }],
							  let_expr = result_expr, let_info_ptr = let_expr_ptr, let_expr_position = NoPos }, 
						pattern_position, var_store, expr_heap, opt_dynamics, cs)
			No
				| var_info == fv_info_ptr
					-> (result_expr, pattern_position, var_store, expr_heap, opt_dynamics, cs)
					# (var_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
					  (let_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
					-> (Let { let_strict_binds = [], let_lazy_binds=
									[{ lb_src = Var { var_name = fv_name, var_info_ptr = fv_info_ptr, var_expr_ptr = var_expr_ptr },
										 lb_dst = { fv_name = name, fv_info_ptr = var_info, fv_def_level = NotALevel, fv_count = 0 },
										 lb_position = NoPos }],
							  let_expr = result_expr, let_info_ptr = let_expr_ptr, let_expr_position = NoPos },
						pattern_position, var_store, expr_heap, opt_dynamics, cs)

	transform_pattern_into_cases (AP_Algebraic cons_symbol type_index args opt_var) fun_arg result_expr pattern_position
									var_store expr_heap opt_dynamics cs
		# (var_args, result_expr, pattern_position, var_store, expr_heap, opt_dynamics, cs)
				= convertSubPatterns args result_expr pattern_position var_store expr_heap opt_dynamics cs
		  type_symbol = {glob_module = cons_symbol.glob_module, glob_object = type_index}
	  	  (act_var, result_expr, expr_heap) = transform_pattern_variable fun_arg opt_var result_expr expr_heap
		  alg_pattern = { ap_symbol = cons_symbol, ap_vars = var_args, ap_expr = result_expr, ap_position = pattern_position }
	  	  case_guards = AlgebraicPatterns type_symbol [alg_pattern]
		  (case_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
		= (Case { case_expr = act_var, case_guards = case_guards, case_default = No, case_ident = No,
				case_info_ptr = case_expr_ptr, case_default_pos = NoPos },
				NoPos, var_store, expr_heap, opt_dynamics, cs)	
	transform_pattern_into_cases (AP_Basic basic_val opt_var) fun_arg result_expr pattern_position var_store expr_heap opt_dynamics cs
		# (basic_type, cs) = typeOfBasicValue basic_val cs
	  	  (act_var, result_expr, expr_heap) = transform_pattern_variable fun_arg opt_var result_expr expr_heap
		  case_guards = BasicPatterns basic_type [{ bp_value = basic_val, bp_expr = result_expr, bp_position = pattern_position }]
		  (case_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
		= (Case { case_expr = act_var, case_guards = case_guards, case_default = No, case_ident = No,
					case_info_ptr = case_expr_ptr, case_default_pos = NoPos },
			NoPos, var_store, expr_heap, opt_dynamics, cs)	
	transform_pattern_into_cases (AP_Dynamic pattern type opt_var) fun_arg result_expr pattern_position var_store expr_heap opt_dynamics cs
		# (var_arg, result_expr, pattern_position, var_store, expr_heap, opt_dynamics, cs)
				= convertSubPattern pattern result_expr pattern_position var_store expr_heap opt_dynamics cs
		  (type_case_info_ptr, expr_heap) = newPtr EI_Empty expr_heap
		  (dynamic_info_ptr, expr_heap) = newPtr (EI_DynamicType type opt_dynamics) expr_heap
	  	  (act_var, result_expr, expr_heap) = transform_pattern_variable fun_arg opt_var result_expr expr_heap
	  	  type_case_patterns = [{ dp_var = var_arg, dp_type	= dynamic_info_ptr,	dp_rhs = result_expr, dp_type_patterns_vars = [],
	  	  							dp_type_code = TCE_Empty, dp_position = pattern_position }]
		= (buildTypeCase act_var type_case_patterns No type_case_info_ptr, NoPos, var_store, expr_heap, [dynamic_info_ptr], cs)	
	transform_pattern_into_cases (AP_WildCard _) fun_arg result_expr pattern_position var_store expr_heap opt_dynamics cs
		= (result_expr, pattern_position, var_store, expr_heap, opt_dynamics, cs)	
	transform_pattern_into_cases (AP_Empty name) fun_arg result_expr pattern_position var_store expr_heap opt_dynamics cs
		= (result_expr, pattern_position, var_store, expr_heap, opt_dynamics, cs)

	transform_pattern_variable :: !FreeVar !(Optional !(Bind Ident VarInfoPtr)) !Expression !*ExpressionHeap
		-> (!Expression, !Expression, !*ExpressionHeap)
	transform_pattern_variable {fv_info_ptr,fv_name} (Yes {bind_src,bind_dst}) result_expr expr_heap
		| bind_dst == fv_info_ptr
			# (var_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
			= (Var { var_name = fv_name, var_info_ptr = fv_info_ptr, var_expr_ptr = var_expr_ptr }, result_expr, expr_heap)
			# (var_expr_ptr1, expr_heap) = newPtr EI_Empty expr_heap
			  (var_expr_ptr2, expr_heap) = newPtr EI_Empty expr_heap
			  (let_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
			= (Var { var_name = fv_name, var_info_ptr = fv_info_ptr, var_expr_ptr = var_expr_ptr1 },
						Let { let_strict_binds = [], let_lazy_binds =
						 		[{ lb_src = Var { var_name = fv_name, var_info_ptr = fv_info_ptr, var_expr_ptr = var_expr_ptr2 },
									lb_dst = { fv_name = bind_src, fv_info_ptr = bind_dst, fv_def_level = NotALevel, fv_count = 0 },
									lb_position = NoPos }],
							  let_expr = result_expr, let_info_ptr = let_expr_ptr, let_expr_position = NoPos }, expr_heap)
	transform_pattern_variable {fv_info_ptr,fv_name} No result_expr expr_heap
		# (var_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
		= (Var { var_name = fv_name, var_info_ptr = fv_info_ptr, var_expr_ptr = var_expr_ptr }, result_expr, expr_heap)

checkRhs :: [FreeVar] OptGuardedAlts LocalDefs ExpressionInput *ExpressionState *ExpressionInfo *CheckState -> *(!Expression,![FreeVar],!*ExpressionState,!*ExpressionInfo,!*CheckState);
checkRhs free_vars rhs_alts rhs_locals e_input=:{ei_expr_level,ei_mod_index} e_state e_info cs
	# ei_expr_level = inc ei_expr_level
	  (loc_defs, (var_env, array_patterns), e_state, e_info, cs) = checkLhssOfLocalDefs ei_expr_level ei_mod_index rhs_locals e_state e_info cs
	  (es_fun_defs, e_info, heaps, cs)
	  		= checkLocalFunctions ei_mod_index ei_expr_level rhs_locals e_state.es_fun_defs e_info
	  			{ hp_var_heap = e_state.es_var_heap, hp_expression_heap = e_state.es_expr_heap, hp_type_heaps = e_state.es_type_heaps } cs
	  (rhs_expr, free_vars, e_state, e_info, cs) 
	  		= check_opt_guarded_alts free_vars rhs_alts { e_input & ei_expr_level = ei_expr_level }
	  			{ e_state & es_fun_defs = es_fun_defs, es_var_heap = heaps.hp_var_heap, es_expr_heap = heaps.hp_expression_heap,
					es_type_heaps = heaps.hp_type_heaps } e_info cs
	  (expr, free_vars, e_state, e_info, cs)
			= addArraySelections array_patterns rhs_expr free_vars e_input e_state e_info cs
	  (expr, free_vars, e_state, e_info, cs) = checkRhssAndTransformLocalDefs free_vars loc_defs expr e_input e_state e_info cs
	  (es_fun_defs, cs_symbol_table) = removeLocalsFromSymbolTable ei_expr_level var_env rhs_locals e_state.es_fun_defs cs.cs_symbol_table
	= (expr, free_vars, { e_state & es_fun_defs = es_fun_defs}, e_info, { cs & cs_symbol_table = cs_symbol_table })
where
	check_opt_guarded_alts free_vars (GuardedAlts guarded_alts default_expr) e_input e_state e_info cs
		# (let_vars_list, rev_guarded_exprs, last_expr_level, free_vars, e_state, e_info, cs)
				= check_guarded_expressions free_vars guarded_alts [] [] e_input e_state e_info cs
		  (default_expr, free_vars, e_state, e_info, cs)
		  		= check_default_expr free_vars default_expr { e_input & ei_expr_level = last_expr_level } e_state e_info cs
		  cs = { cs & cs_symbol_table = remove_seq_let_vars e_input.ei_expr_level let_vars_list cs.cs_symbol_table }
	  	  (_, result_expr, es_expr_heap) = convert_guards_to_cases rev_guarded_exprs default_expr e_state.es_expr_heap
	  	= (result_expr, free_vars, { e_state & es_expr_heap = es_expr_heap }, e_info, cs)
	check_opt_guarded_alts free_vars (UnGuardedExpr unguarded_expr) e_input e_state e_info cs
		= check_unguarded_expression free_vars unguarded_expr e_input e_state e_info cs

	check_default_expr free_vars (Yes default_expr) e_input e_state e_info cs
		# (expr, free_vars, e_state, e_info, cs) = check_unguarded_expression free_vars default_expr e_input e_state e_info cs
		= (Yes expr, free_vars, e_state, e_info, cs)
	check_default_expr free_vars No e_input e_state e_info cs
		= (No, free_vars, e_state, e_info, cs)
		
	convert_guards_to_cases [(let_binds, guard, expr, guard_ident)] result_expr es_expr_heap
		# (case_expr_ptr, es_expr_heap) = newPtr EI_Empty es_expr_heap
		  basic_pattern = {bp_value = (BVB True), bp_expr = expr, bp_position = NoPos }
		  case_expr = Case { case_expr = guard, case_guards = BasicPatterns BT_Bool [basic_pattern],
		  		case_default = result_expr, case_ident = Yes guard_ident,
		  		case_info_ptr = case_expr_ptr, case_default_pos = NoPos }
		= build_sequential_lets let_binds case_expr NoPos es_expr_heap
	convert_guards_to_cases [(let_binds, guard, expr, guard_ident) : rev_guarded_exprs] result_expr es_expr_heap
		# (case_expr_ptr, es_expr_heap) = newPtr EI_Empty es_expr_heap
		  basic_pattern = {bp_value = (BVB True), bp_expr = expr, bp_position = NoPos }
		  case_expr = Case { case_expr = guard, case_guards = BasicPatterns BT_Bool [basic_pattern],
		  		case_default = result_expr, case_ident = Yes guard_ident,
		  		case_info_ptr = case_expr_ptr, case_default_pos = NoPos }
		  (_, result_expr, es_expr_heap) = build_sequential_lets let_binds case_expr NoPos es_expr_heap
		= convert_guards_to_cases rev_guarded_exprs (Yes result_expr) es_expr_heap
	
	check_guarded_expressions free_vars [gexpr : gexprs] let_vars_list rev_guarded_exprs e_input e_state e_info cs
		# (let_vars_list, rev_guarded_exprs, ei_expr_level, free_vars, e_state, e_info, cs)
				= check_guarded_expression free_vars gexpr let_vars_list rev_guarded_exprs e_input e_state e_info cs
		= check_guarded_expressions free_vars gexprs let_vars_list rev_guarded_exprs { e_input & ei_expr_level = ei_expr_level } e_state e_info cs
	check_guarded_expressions free_vars [] let_vars_list rev_guarded_exprs {ei_expr_level} e_state e_info cs
		= (let_vars_list, rev_guarded_exprs, ei_expr_level, free_vars, e_state, e_info, cs)

	check_guarded_expression free_vars {alt_nodes,alt_guard,alt_expr,alt_ident,alt_position}
			let_vars_list rev_guarded_exprs e_input=:{ei_expr_level,ei_mod_index} e_state e_info cs
		# (let_binds, let_vars_list, ei_expr_level, free_vars, e_state, e_info, cs) = check_sequential_lets free_vars alt_nodes let_vars_list
		  		{ e_input & ei_expr_level = inc ei_expr_level } e_state e_info cs
		  e_input = { e_input & ei_expr_level = ei_expr_level }
		  cs = pushErrorAdmin2 "guard" alt_position cs
	  	  (guard, free_vars, e_state, e_info, cs) = checkExpression free_vars alt_guard e_input e_state e_info cs
		  cs = popErrorAdmin cs
		  (expr, free_vars, e_state, e_info, cs) = check_opt_guarded_alts free_vars alt_expr e_input e_state e_info cs
	  	= (let_vars_list, [(let_binds, guard, expr, alt_ident) : rev_guarded_exprs], ei_expr_level, free_vars, e_state, e_info,  cs )

	check_unguarded_expression :: [FreeVar] ExprWithLocalDefs ExpressionInput *ExpressionState *ExpressionInfo *CheckState -> *(!Expression,![FreeVar],!*ExpressionState,!*ExpressionInfo,!*CheckState);
	check_unguarded_expression free_vars {ewl_nodes,ewl_expr,ewl_locals,ewl_position} e_input=:{ei_expr_level,ei_mod_index} e_state e_info cs
		# this_expr_level = inc ei_expr_level
		  (loc_defs, (var_env, array_patterns), e_state, e_info, cs)
		 		= checkLhssOfLocalDefs this_expr_level ei_mod_index ewl_locals e_state e_info cs
		  (binds, let_vars_list, rhs_expr_level, free_vars, e_state, e_info, cs) = check_sequential_lets free_vars ewl_nodes [] { e_input & ei_expr_level = this_expr_level } e_state e_info cs
		  cs = pushErrorAdmin2 "" ewl_position cs
	  	  (expr, free_vars, e_state, e_info, cs) = checkExpression free_vars ewl_expr { e_input & ei_expr_level = rhs_expr_level } e_state e_info cs
		  cs = popErrorAdmin cs
		  (expr, free_vars, e_state, e_info, cs)
				= addArraySelections array_patterns expr free_vars e_input e_state e_info cs
		  cs = { cs & cs_symbol_table = remove_seq_let_vars rhs_expr_level let_vars_list cs.cs_symbol_table }
		  (_, seq_let_expr, es_expr_heap) = build_sequential_lets binds expr ewl_position e_state.es_expr_heap
	  	  (expr, free_vars, e_state, e_info, cs)
				= checkRhssAndTransformLocalDefs free_vars loc_defs seq_let_expr e_input { e_state & es_expr_heap = es_expr_heap} e_info cs
	  	  (es_fun_defs, e_info, heaps, cs)
	  	  		= checkLocalFunctions ei_mod_index rhs_expr_level ewl_locals e_state.es_fun_defs e_info 
	  	  		{ hp_var_heap = e_state.es_var_heap, hp_expression_heap = e_state.es_expr_heap, hp_type_heaps = e_state.es_type_heaps } cs
		  (es_fun_defs, cs_symbol_table) = removeLocalsFromSymbolTable this_expr_level var_env ewl_locals es_fun_defs cs.cs_symbol_table
	  	= (expr, free_vars, {e_state & es_fun_defs = es_fun_defs, es_var_heap = heaps.hp_var_heap,
	  			es_expr_heap = heaps.hp_expression_heap, es_type_heaps = heaps.hp_type_heaps }, e_info, { cs & cs_symbol_table = cs_symbol_table} )
	
	remove_seq_let_vars level [] symbol_table
		= symbol_table
	remove_seq_let_vars level [let_vars : let_vars_list] symbol_table
		= remove_seq_let_vars (dec level) let_vars_list (removeLocalIdentsFromSymbolTable level let_vars symbol_table)
	
	check_sequential_lets :: [FreeVar] [NodeDefWithLocals] u:[[Ident]] !ExpressionInput *ExpressionState *ExpressionInfo *CheckState 
						-> *(![.([LetBind],![LetBind])],!u:[[Ident]],!Int,![FreeVar],!*ExpressionState,!*ExpressionInfo,!*CheckState);
	check_sequential_lets free_vars [seq_let:seq_lets] let_vars_list e_input=:{ei_expr_level,ei_mod_index} e_state e_info cs
		# ei_expr_level
				= inc ei_expr_level
		  e_input
		  		= { e_input & ei_expr_level = ei_expr_level }
		  (src_expr, pattern_expr, (let_vars, array_patterns), free_vars, e_state, e_info, cs)
		  		= check_sequential_let free_vars seq_let e_input e_state e_info cs
	      (binds, loc_envs, max_expr_level, free_vars, e_state, e_info, cs)
	      		= check_sequential_lets free_vars seq_lets [let_vars : let_vars_list] e_input e_state e_info cs
		  (let_binds, es_var_heap, es_expr_heap, e_info, cs)
				= transfromPatternIntoBind ei_mod_index ei_expr_level pattern_expr src_expr seq_let.ndwl_position
						e_state.es_var_heap e_state.es_expr_heap e_info cs
		  e_state
		  		= { e_state & es_var_heap = es_var_heap, es_expr_heap = es_expr_heap }
		  (strict_array_pattern_binds, lazy_array_pattern_binds, free_vars, e_state, e_info, cs)
				= foldSt (buildSelections e_input) array_patterns ([], [], free_vars, e_state, e_info, cs)
		  all_binds
		  		= [if seq_let.ndwl_strict (s, l) ([],let_binds), (strict_array_pattern_binds, lazy_array_pattern_binds) : binds]
		    with (l,s) = splitAt ((length let_binds)-1) let_binds
	    = (all_binds, loc_envs, max_expr_level, free_vars, e_state, e_info, cs)
	check_sequential_lets free_vars [] let_vars_list e_input=:{ei_expr_level} e_state e_info cs
		= ([], let_vars_list, ei_expr_level, free_vars, e_state, e_info, cs)

	check_sequential_let :: [FreeVar] NodeDefWithLocals ExpressionInput *ExpressionState *ExpressionInfo *CheckState -> *(!Expression,!AuxiliaryPattern,!(![Ident],![ArrayPattern]),![FreeVar],!*ExpressionState,!*ExpressionInfo,!*CheckState);
	check_sequential_let free_vars {ndwl_def={bind_src,bind_dst},ndwl_locals, ndwl_position} e_input=:{ei_expr_level,ei_mod_index} e_state e_info cs
		# cs = pushErrorAdmin (newPosition {id_name="node definition", id_info=nilPtr} ndwl_position) cs
		  (loc_defs, (loc_env, loc_array_patterns), e_state, e_info, cs) = checkLhssOfLocalDefs ei_expr_level ei_mod_index ndwl_locals e_state e_info cs
		  (src_expr, free_vars, e_state, e_info, cs) = checkExpression free_vars bind_src e_input e_state e_info cs
		  (src_expr, free_vars, e_state, e_info, cs)
				= addArraySelections loc_array_patterns src_expr free_vars e_input e_state e_info cs
		  (src_expr, free_vars, e_state, e_info, cs) = checkRhssAndTransformLocalDefs free_vars loc_defs src_expr e_input e_state e_info cs
		  (es_fun_defs, e_info, {hp_var_heap,hp_expression_heap,hp_type_heaps}, cs)
				= checkLocalFunctions ei_mod_index ei_expr_level ndwl_locals e_state.es_fun_defs e_info
	  				{ hp_var_heap = e_state.es_var_heap, hp_expression_heap = e_state.es_expr_heap, hp_type_heaps = e_state.es_type_heaps } cs
	  	  (es_fun_defs, cs_symbol_table) = removeLocalsFromSymbolTable ei_expr_level loc_env ndwl_locals es_fun_defs cs.cs_symbol_table
		  (pattern, accus, {ps_fun_defs,ps_var_heap}, e_info, cs)
				= checkPattern bind_dst No { pi_def_level = ei_expr_level, pi_mod_index = ei_mod_index, pi_is_node_pattern = True } ([], []) 
					{ps_var_heap = hp_var_heap, ps_fun_defs = es_fun_defs } e_info { cs & cs_symbol_table = cs_symbol_table }
		  e_state = { e_state & es_var_heap = ps_var_heap, es_expr_heap = hp_expression_heap, es_type_heaps = hp_type_heaps, es_fun_defs = ps_fun_defs }
		= (src_expr, pattern, accus, free_vars, e_state, e_info, popErrorAdmin cs)
	
	build_sequential_lets :: ![(![LetBind],![LetBind])] !Expression !Position !*ExpressionHeap -> (!Position, !Expression, !*ExpressionHeap)
	build_sequential_lets [] expr let_expr_position expr_heap
		= (let_expr_position, expr, expr_heap)
	build_sequential_lets [(strict_binds, lazy_binds) : seq_lets] expr let_expr_position expr_heap
		# (let_expr_position, let_expr, expr_heap) = build_sequential_lets seq_lets expr let_expr_position expr_heap
	  	  (let_expr, expr_heap) = buildLetExpression strict_binds lazy_binds let_expr let_expr_position expr_heap
		= (if (isEmpty strict_binds && isEmpty lazy_binds) let_expr_position NoPos, let_expr, expr_heap)

checkExpression :: ![FreeVar] !ParsedExpr !ExpressionInput !*ExpressionState !*ExpressionInfo !*CheckState
	-> *(!Expression, ![FreeVar], !*ExpressionState, !*ExpressionInfo, !*CheckState);
checkExpression free_vars (PE_List exprs) e_input e_state e_info cs	
	# (exprs, free_vars, e_state, e_info, cs) = check_expressions free_vars exprs e_input e_state e_info cs
	  (expr, e_state, cs_error) = build_expression exprs e_state cs.cs_error
	= (expr, free_vars, e_state, e_info, { cs & cs_error = cs_error })

where
	check_expressions free_vars [expr : exprs] e_input e_state e_info cs
		# (exprs, free_vars, e_state, e_info, cs) = check_expressions free_vars exprs e_input e_state e_info cs
		= case expr of
			PE_Ident id
				# (expr, free_vars, e_state, e_info, cs) = checkIdentExpression cIsInExpressionList free_vars id e_input e_state e_info cs
 				-> ([expr : exprs], free_vars, e_state, e_info, cs)
 			_
				# (expr, free_vars, e_state, e_info, cs) = checkExpression free_vars expr e_input e_state e_info cs
 				-> ([expr : exprs], free_vars, e_state, e_info, cs)
 	check_expressions free_vars [] e_input e_state e_info cs
		= ([], free_vars, e_state, e_info, cs)

	first_argument_of_infix_operator_missing
		= "first argument of infix operator missing"

	build_expression [Constant symb _ (Prio _ _) _ , _: _] e_state cs_error
		= (EE, e_state, checkError symb.symb_name first_argument_of_infix_operator_missing cs_error)
	build_expression [Constant symb arity _ is_fun] e_state cs_error
		= buildApplication symb arity 0 is_fun [] e_state cs_error
	build_expression [expr] e_state cs_error
		= (expr, e_state, cs_error)
	build_expression [expr : exprs] e_state cs_error
		# (opt_opr, left, e_state, cs_error) = split_at_operator [expr] exprs e_state cs_error
		  (left_expr, e_state, cs_error) = combine_expressions left [] 0 e_state cs_error
		= case opt_opr of
			Yes (symb, prio, is_fun, right)
				-> case right of
					[Constant symb _ (Prio _ _) _:_]
						-> (EE, e_state, checkError symb.symb_name first_argument_of_infix_operator_missing cs_error)
					_
						-> build_operator_expression [] left_expr (symb, prio, is_fun) right e_state cs_error
			No
				-> (left_expr, e_state, cs_error)
	where
		split_at_operator left [Constant symb arity NoPrio is_fun : exprs] e_state cs_error
			# (appl_exp, e_state, cs_error) = buildApplication symb arity 0 is_fun [] e_state cs_error
			= split_at_operator [appl_exp : left] exprs e_state cs_error
		split_at_operator left [Constant symb arity (Prio _ _) is_fun] e_state cs_error
			= (No, left, e_state, checkError symb.symb_name "second argument of infix operator missing" cs_error)
		split_at_operator left [Constant symb arity prio is_fun] e_state cs_error
			# (appl_exp, e_state, cs_error) = buildApplication symb arity 0 is_fun [] e_state cs_error
			= (No, [appl_exp : left], e_state, cs_error)
		split_at_operator left [expr=:(Constant symb _ prio is_fun) : exprs] e_state cs_error
			= (Yes (symb, prio, is_fun, exprs), left, e_state, cs_error)
		split_at_operator left [expr : exprs] e_state cs_error
			= split_at_operator [expr : left] exprs e_state cs_error
		split_at_operator exp [] e_state cs_error
			= (No, exp, e_state, cs_error)

		combine_expressions [first_expr] args arity e_state cs_error
			= case first_expr of
				Constant symb form_arity _ is_fun
					# (app_exp, e_state, cs_error) = buildApplication symb form_arity arity is_fun args e_state cs_error
					-> (app_exp, e_state, cs_error)
				_
					| arity == 0
						-> (first_expr, e_state, cs_error)
						-> (first_expr @ args, e_state, cs_error)
		combine_expressions [rev_arg : rev_args] args arity e_state cs_error
			= combine_expressions rev_args [rev_arg : args] (inc arity) e_state cs_error
		

 		build_operator_expression left_appls left1 (symb1, prio1, is_fun1) [re : res] e_state cs_error
			# (opt_opr, left2, e_state, cs_error) = split_at_operator [re] res e_state cs_error
			= case opt_opr of
				Yes (symb2, prio2, is_fun2, right)
					# optional_prio = determinePriority prio1 prio2
					-> case optional_prio of
						Yes priority
							| priority
						  		# (middle_exp, e_state, cs_error) = combine_expressions left2 [] 0 e_state cs_error
								  (new_left, e_state, cs_error) = buildApplication symb1 2 2 is_fun1 [left1,middle_exp] e_state cs_error
								  (left_appls, new_left, e_state, cs_error) = build_left_operand left_appls prio2 new_left e_state cs_error
								-> build_operator_expression left_appls new_left (symb2, prio2, is_fun2) right e_state cs_error
						  		# (middle_exp, e_state, cs_error) = combine_expressions left2 [] 0 e_state cs_error
								-> build_operator_expression [(symb1, prio1, is_fun1, left1) : left_appls]
										middle_exp (symb2, prio2, is_fun2) right e_state cs_error
						No
							-> (EE, e_state, checkError symb1.symb_name "conflicting priorities" cs_error)
				No
					# (right, e_state, cs_error) = combine_expressions left2 [] 0 e_state cs_error
					  (result_expr, e_state, cs_error) = buildApplication symb1 2 2 is_fun1 [left1,right] e_state cs_error
					-> build_final_expression left_appls result_expr e_state cs_error

		build_left_operand [] _ result_expr e_state cs_error
			= ([], result_expr, e_state, cs_error)		
		build_left_operand la=:[(symb, priol, is_fun, left) : left_appls] prior result_expr e_state cs_error
			# optional_prio = determinePriority priol prior
			= case optional_prio of
				Yes priority
					| priority
						# (result_expr, e_state, cs_error) = buildApplication symb 2 2 is_fun [left,result_expr] e_state cs_error
						-> build_left_operand left_appls prior result_expr e_state cs_error
						-> (la, result_expr, e_state, cs_error)
				No
					-> (la, EE, e_state, checkError symb.symb_name "conflicting priorities" cs_error)
		
		build_final_expression [] result_expr e_state cs_error
			= (result_expr, e_state, cs_error)		
		build_final_expression [(symb, _, is_fun, left) : left_appls] result_expr e_state cs_error
			# (result_expr, e_state, cs_error) = buildApplication symb 2 2 is_fun [left,result_expr] e_state cs_error
			= build_final_expression left_appls result_expr e_state cs_error
					
checkExpression free_vars (PE_Let strict let_locals expr) e_input=:{ei_expr_level,ei_mod_index} e_state e_info cs
	# ei_expr_level = inc ei_expr_level
	  (loc_defs, (var_env, array_patterns), e_state, e_info, cs)
	  		= checkLhssOfLocalDefs ei_expr_level ei_mod_index let_locals e_state e_info cs
	  e_input = { e_input & ei_expr_level = ei_expr_level }
	  (let_expr, free_vars, e_state, e_info, cs) = checkExpression free_vars expr e_input e_state e_info cs
	  (expr, free_vars, e_state=:{es_dynamics,es_expr_heap,es_var_heap}, e_info, cs)
			= addArraySelections array_patterns let_expr free_vars e_input e_state e_info cs
	  (expr, free_vars, e_state, e_info, cs) = checkRhssAndTransformLocalDefs free_vars loc_defs expr e_input e_state e_info cs
	  (es_fun_defs, e_info, heaps, cs)
			= checkLocalFunctions ei_mod_index ei_expr_level let_locals e_state.es_fun_defs e_info
	  			{ hp_var_heap = e_state.es_var_heap, hp_expression_heap = e_state.es_expr_heap, hp_type_heaps = e_state.es_type_heaps } cs
	  (es_fun_defs, cs_symbol_table) = removeLocalsFromSymbolTable ei_expr_level var_env let_locals es_fun_defs cs.cs_symbol_table
	= (expr, free_vars,
		{ e_state & es_fun_defs = es_fun_defs, es_var_heap = heaps.hp_var_heap, es_expr_heap = heaps.hp_expression_heap,
			es_type_heaps = heaps.hp_type_heaps }, e_info, { cs & cs_symbol_table = cs_symbol_table })

checkExpression free_vars (PE_Case case_ident expr alts) e_input e_state e_info cs
	# (pattern_expr, free_vars, e_state, e_info, cs) = checkExpression free_vars expr e_input e_state e_info cs
	  (guards, _, pattern_variables, defaul, free_vars, e_state, e_info, cs) = check_guarded_expressions free_vars alts [] case_ident.id_name e_input e_state e_info cs
	  (pattern_expr, binds, es_expr_heap) = bind_pattern_variables pattern_variables pattern_expr e_state.es_expr_heap
	  (case_expr, es_expr_heap) = build_case guards defaul pattern_expr case_ident es_expr_heap
	  (result_expr, es_expr_heap) = buildLetExpression [] binds case_expr NoPos es_expr_heap
	= (result_expr, free_vars, { e_state & es_expr_heap = es_expr_heap }, e_info, cs)
	
where
	check_guarded_expressions free_vars [g] pattern_variables case_name e_input=:{ei_expr_level} e_state e_info cs
		# e_input = { e_input & ei_expr_level = inc ei_expr_level }
		= check_guarded_expression free_vars g NoPattern NoPattern pattern_variables No case_name e_input e_state e_info cs 
	check_guarded_expressions free_vars [g : gs] pattern_variables case_name e_input=:{ei_expr_level} e_state e_info cs
		# e_input = { e_input & ei_expr_level = inc ei_expr_level }
		  (gs, pattern_scheme, pattern_variables, defaul, free_vars, e_state, e_info, cs)
		  	= check_guarded_expressions free_vars gs pattern_variables case_name e_input e_state e_info cs
		= check_guarded_expression free_vars g gs pattern_scheme pattern_variables defaul case_name e_input e_state e_info cs 
	check_guarded_expression free_vars {calt_pattern,calt_rhs={rhs_alts,rhs_locals}} patterns pattern_scheme pattern_variables defaul case_name 
				e_input=:{ei_expr_level,ei_mod_index} e_state=:{es_fun_defs,es_var_heap} e_info cs
		# (pattern, (var_env, array_patterns), {ps_fun_defs,ps_var_heap}, e_info, cs)
				= checkPattern calt_pattern No { pi_def_level = ei_expr_level, pi_mod_index = ei_mod_index, pi_is_node_pattern = False } ([], [])
					{ps_var_heap = es_var_heap, ps_fun_defs = es_fun_defs} e_info cs
		  e_state = { e_state & es_var_heap = ps_var_heap, es_fun_defs = ps_fun_defs }
		  (rhs_expr, free_vars, e_state, e_info, cs)
		  		= checkRhs free_vars rhs_alts rhs_locals e_input e_state e_info cs
		  (expr_with_array_selections, free_vars, e_state=:{es_dynamics,es_expr_heap,es_var_heap}, e_info, cs)
				= addArraySelections array_patterns rhs_expr free_vars e_input e_state e_info cs
		  cs_symbol_table = removeLocalIdentsFromSymbolTable ei_expr_level var_env cs.cs_symbol_table
		  (guarded_expr, pattern_scheme, pattern_variables, defaul, es_var_heap, es_expr_heap, dynamics_in_patterns, cs)
		  		= transform_pattern pattern patterns pattern_scheme pattern_variables defaul expr_with_array_selections case_name
		  									es_var_heap es_expr_heap es_dynamics { cs & cs_symbol_table = cs_symbol_table }
		= (guarded_expr, pattern_scheme, pattern_variables, defaul, free_vars,
			{ e_state & es_var_heap = es_var_heap, es_expr_heap = es_expr_heap, es_dynamics = dynamics_in_patterns },
				e_info, cs)

	transform_pattern :: !AuxiliaryPattern !CasePatterns !CasePatterns !(Env Ident VarInfoPtr) !(Optional (!Optional FreeVar, !Expression)) !Expression
			!String !*VarHeap !*ExpressionHeap ![DynamicPtr] !*CheckState
				-> (!CasePatterns, !CasePatterns, !Env Ident VarInfoPtr, !Optional (!Optional FreeVar,!Expression), !*VarHeap, !*ExpressionHeap, ![DynamicPtr], !*CheckState)
	transform_pattern (AP_Algebraic cons_symbol type_index args opt_var) patterns pattern_scheme pattern_variables defaul result_expr _ var_store expr_heap opt_dynamics cs
		# (var_args, result_expr, _, var_store, expr_heap, opt_dynamics, cs) = convertSubPatterns args result_expr NoPos var_store expr_heap opt_dynamics cs
		  type_symbol = { glob_module = cons_symbol.glob_module, glob_object = type_index}
		  pattern = { ap_symbol = cons_symbol, ap_vars = var_args, ap_expr = result_expr, ap_position = NoPos}
		  pattern_variables = cons_optional opt_var pattern_variables
		= case pattern_scheme of
			AlgebraicPatterns alg_type _
				| type_symbol == alg_type
					# alg_patterns = case patterns of
							AlgebraicPatterns _ alg_patterns -> alg_patterns
							NoPattern -> []
					-> (AlgebraicPatterns type_symbol [pattern : alg_patterns], pattern_scheme, pattern_variables, defaul, var_store, expr_heap, opt_dynamics, cs)
					-> (patterns, pattern_scheme, pattern_variables, defaul, var_store, expr_heap, opt_dynamics,
								{ cs & cs_error = checkError cons_symbol.glob_object.ds_ident "incompatible types of patterns" cs.cs_error })
			NoPattern
				-> (AlgebraicPatterns type_symbol [pattern], AlgebraicPatterns type_symbol [], pattern_variables, defaul, var_store, expr_heap, opt_dynamics, cs)
			_
				-> (patterns, pattern_scheme, pattern_variables, defaul, var_store, expr_heap, opt_dynamics,
						{ cs & cs_error = checkError cons_symbol.glob_object.ds_ident "illegal combination of patterns" cs.cs_error })
	transform_pattern (AP_Basic basic_val opt_var) patterns pattern_scheme pattern_variables defaul result_expr _ var_store expr_heap opt_dynamics cs
		# pattern = { bp_value = basic_val, bp_expr = result_expr, bp_position = NoPos}
		  pattern_variables = cons_optional opt_var pattern_variables
		  (type_symbol, cs) = typeOfBasicValue basic_val cs
		= case pattern_scheme of
			BasicPatterns basic_type _
				| type_symbol == basic_type
					# basic_patterns = case patterns of
							BasicPatterns _ basic_patterns
								-> basic_patterns
							NoPattern
								-> [] 
					-> (BasicPatterns basic_type [pattern : basic_patterns], pattern_scheme, pattern_variables, defaul, var_store, expr_heap, opt_dynamics, cs)
					-> (patterns, pattern_scheme, pattern_variables, defaul, var_store, expr_heap, opt_dynamics,
							{ cs & cs_error = checkError basic_val "incompatible types of patterns" cs.cs_error })
			NoPattern
				-> (BasicPatterns type_symbol [pattern], BasicPatterns type_symbol [], pattern_variables, defaul, var_store, expr_heap, opt_dynamics, cs)
			_
				-> (patterns, pattern_scheme, pattern_variables, defaul, var_store, expr_heap, opt_dynamics,
						{ cs & cs_error = checkError basic_val "illegal combination of patterns" cs.cs_error})
	transform_pattern (AP_Dynamic pattern type opt_var) patterns pattern_scheme pattern_variables defaul result_expr _ var_store expr_heap opt_dynamics cs
		# (var_arg, result_expr, _, var_store, expr_heap, opt_dynamics, cs) = convertSubPattern pattern result_expr NoPos var_store expr_heap opt_dynamics cs
		  (dynamic_info_ptr, expr_heap) = newPtr (EI_DynamicType type opt_dynamics) expr_heap
		  pattern = { dp_var = var_arg, dp_type	= dynamic_info_ptr,	dp_rhs = result_expr, dp_type_patterns_vars = [],
		  				dp_type_code = TCE_Empty, dp_position = NoPos }
		  pattern_variables = cons_optional opt_var pattern_variables
		= case pattern_scheme of
			DynamicPatterns _
				# dyn_patterns = case patterns of 
										DynamicPatterns dyn_patterns
											-> dyn_patterns
										NoPattern
											-> []
				-> (DynamicPatterns [pattern : dyn_patterns], pattern_scheme, pattern_variables, defaul, var_store, expr_heap, [dynamic_info_ptr], cs)
			NoPattern
				-> (DynamicPatterns [pattern], DynamicPatterns [], pattern_variables, defaul, var_store, expr_heap, [dynamic_info_ptr], cs)
			_
				-> (patterns, pattern_scheme, pattern_variables, defaul, var_store, expr_heap, opt_dynamics,
						{ cs & cs_error = checkError "<dynamic pattern>" "illegal combination of patterns" cs.cs_error })
	transform_pattern (AP_Variable name var_info opt_var) NoPattern pattern_scheme pattern_variables No result_expr _ var_store expr_heap opt_dynamics cs
		= ( NoPattern, pattern_scheme, cons_optional opt_var pattern_variables, 
		  	Yes (Yes { fv_name = name, fv_info_ptr = var_info, fv_def_level = NotALevel, fv_count = 0 }, result_expr),
			var_store, expr_heap, opt_dynamics, cs)		
	transform_pattern (AP_Variable name var_info opt_var) patterns pattern_scheme pattern_variables defaul result_expr case_name var_store expr_heap opt_dynamics cs
		# free_var = { fv_name = name, fv_info_ptr = var_info, fv_def_level = NotALevel, fv_count = 0 }
		  (new_bound_var, expr_heap) = allocate_bound_var free_var expr_heap
		  case_ident = { id_name = case_name, id_info = nilPtr }
		  (new_case, expr_heap) = build_case patterns defaul (Var new_bound_var) case_ident expr_heap
		  new_defaul = insert_as_default new_case result_expr
		= (NoPattern, pattern_scheme, (cons_optional opt_var pattern_variables), Yes (Yes free_var, new_defaul),
			var_store, expr_heap, opt_dynamics, cs)
	transform_pattern (AP_WildCard (Yes opt_var)) patterns pattern_scheme pattern_variables defaul result_expr case_name var_store expr_heap opt_dynamics cs
		= transform_pattern (AP_Variable opt_var.bind_src opt_var.bind_dst No) patterns pattern_scheme pattern_variables defaul
							result_expr case_name var_store expr_heap opt_dynamics cs
	transform_pattern (AP_WildCard no) NoPattern pattern_scheme pattern_variables No result_expr _ var_store expr_heap opt_dynamics cs
		= (NoPattern, pattern_scheme, pattern_variables, Yes (No, result_expr), var_store, expr_heap, opt_dynamics, cs)
	transform_pattern (AP_WildCard _) patterns pattern_scheme pattern_variables defaul result_expr case_name var_store expr_heap opt_dynamics cs
		# (new_info_ptr, var_store) = newPtr VI_Empty var_store
		= transform_pattern (AP_Variable (newVarId "wc") new_info_ptr No) patterns pattern_scheme pattern_variables defaul
							result_expr case_name var_store expr_heap opt_dynamics cs
	transform_pattern (AP_Empty name) patterns pattern_scheme pattern_variables defaul result_expr _ var_store expr_heap opt_dynamics cs
		= (patterns, pattern_scheme, pattern_variables, defaul, var_store, expr_heap, opt_dynamics, cs)


	insert_as_default :: !Expression !Expression -> Expression
	insert_as_default to_insert (Let lad=:{let_expr})
		= Let { lad & let_expr = insert_as_default to_insert let_expr }
	insert_as_default to_insert (Case kees=:{case_default})
		= case case_default of
			No			-> Case { kees & case_default = Yes to_insert }
			Yes defaul	-> Case { kees & case_default = Yes (insert_as_default to_insert defaul)}
	insert_as_default _ expr = expr // checkWarning "pattern won't match"

	build_case NoPattern defaul expr case_ident expr_heap
		= case defaul of
			Yes (opt_var, result)
				-> case opt_var of
					Yes var
						# (let_expression, expr_heap) = bind_default_variable expr var result expr_heap
						-> (let_expression, expr_heap)
					No
						-> (result, expr_heap)
			No
				-> (EE, expr_heap)
	build_case (DynamicPatterns patterns) defaul expr case_ident expr_heap
		= case defaul of
			Yes (opt_var, result)
				-> case opt_var of
					Yes var
						# (type_case_info_ptr, expr_heap) = newPtr EI_Empty expr_heap
						  (bound_var, expr_heap) = allocate_bound_var var expr_heap
						  result = buildTypeCase (Var bound_var) patterns (Yes result) type_case_info_ptr
						  (case_expression, expr_heap) = bind_default_variable expr var result expr_heap
					 	-> (case_expression, expr_heap)
					No
						# (type_case_info_ptr, expr_heap) = newPtr EI_Empty expr_heap
						-> (buildTypeCase expr patterns (Yes result) type_case_info_ptr, expr_heap)
			No
				# (type_case_info_ptr, expr_heap) = newPtr EI_Empty expr_heap
				-> (buildTypeCase expr patterns No type_case_info_ptr, expr_heap)
	build_case patterns (Yes (opt_var,result)) expr case_ident expr_heap
		= case opt_var of
			Yes var
				# (case_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
				  (bound_var, expr_heap) = allocate_bound_var var expr_heap
				  result = Case {case_expr = Var bound_var, case_guards = patterns, case_default = Yes result,
								 case_ident = Yes case_ident, case_info_ptr = case_expr_ptr,
								 case_default_pos = NoPos }
				  (case_expression, expr_heap) = bind_default_variable expr var result expr_heap
				-> (case_expression, expr_heap)
			No
				#  (case_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
				-> (Case {case_expr = expr, case_guards = patterns, case_default = Yes result,
						case_ident = Yes case_ident, case_info_ptr = case_expr_ptr, case_default_pos = NoPos }, expr_heap)
	build_case patterns No expr case_ident expr_heap
		# (case_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
		= (Case {case_expr = expr, case_guards = patterns, case_default = No, case_ident = Yes case_ident,
			case_info_ptr = case_expr_ptr, case_default_pos = NoPos }, expr_heap)

	bind_default_variable lb_src lb_dst result_expr expr_heap
		#  (let_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
		= (Let {let_strict_binds = [], let_lazy_binds = [{ lb_src = lb_src, lb_dst = lb_dst, lb_position = NoPos }],
				let_expr = result_expr, let_info_ptr = let_expr_ptr, let_expr_position = NoPos }, expr_heap)

	bind_pattern_variables [] pattern_expr expr_heap
		= (pattern_expr, [], expr_heap)
	bind_pattern_variables [{bind_src,bind_dst} : variables] this_pattern_expr expr_heap
		# free_var = { fv_name = bind_src, fv_info_ptr = bind_dst, fv_def_level = NotALevel, fv_count = 0 }
		  (bound_var, expr_heap) = allocate_bound_var free_var expr_heap
		  (pattern_expr, binds, expr_heap) = bind_pattern_variables variables (Var bound_var) expr_heap
		= (pattern_expr, [{lb_src = this_pattern_expr, lb_dst = free_var, lb_position = NoPos } : binds], expr_heap)

	cons_optional (Yes var) variables
		= [ var : variables ]
	cons_optional No variables
		= variables

checkExpression free_vars (PE_Selection is_unique expr [PS_Array index_expr]) e_input e_state e_info cs	
	# (expr, free_vars, e_state, e_info, cs) = checkExpression free_vars expr e_input e_state e_info cs
	| is_unique
		# (glob_select_symb, cs) = getPredefinedGlobalSymbol PD_UnqArraySelectFun PD_StdArray STE_Member 2 cs
		  (selector, free_vars, e_state, e_info, cs) = checkArraySelection glob_select_symb free_vars index_expr e_input e_state e_info cs
		= (Selection No expr [selector], free_vars, e_state, e_info, cs)
		# (glob_select_symb, cs) = getPredefinedGlobalSymbol PD_ArraySelectFun PD_StdArray STE_Member 2 cs
		  (selector, free_vars, e_state, e_info, cs) = checkArraySelection glob_select_symb free_vars index_expr e_input e_state e_info cs
		= (Selection No expr [selector], free_vars, e_state, e_info, cs)
checkExpression free_vars (PE_Selection is_unique expr selectors) e_input e_state e_info cs	
	# (selectors, free_vars, e_state, e_info, cs) = checkSelectors cEndWithSelection free_vars selectors e_input e_state e_info cs
	  (expr, free_vars, e_state, e_info, cs) = checkExpression free_vars expr e_input e_state e_info cs
	| is_unique
		# (tuple_type, cs) = getPredefinedGlobalSymbol (GetTupleTypeIndex 2) PD_PredefinedModule STE_Type 2 cs
		= (Selection (Yes tuple_type) expr selectors, free_vars, e_state, e_info, cs)
		= (Selection No expr selectors, free_vars, e_state, e_info, cs)
checkExpression free_vars (PE_Update expr1 selectors expr2) e_input e_state e_info cs	
	# (expr1, free_vars, e_state, e_info, cs) = checkExpression free_vars expr1 e_input e_state e_info cs
	  (selectors, free_vars, e_state, e_info, cs) = checkSelectors cEndWithUpdate free_vars selectors e_input e_state e_info cs
	  (expr2, free_vars, e_state, e_info, cs) = checkExpression free_vars expr2 e_input e_state e_info cs
	= (Update expr1 selectors expr2, free_vars, e_state, e_info, cs)
checkExpression free_vars (PE_Tuple exprs) e_input e_state e_info cs
	# (exprs, arity, free_vars, e_state, e_info, cs) = check_expression_list free_vars exprs e_input e_state e_info cs
	  ({glob_object={ds_ident,ds_index, ds_arity},glob_module}, cs)
	  		= getPredefinedGlobalSymbol (GetTupleConsIndex arity) PD_PredefinedModule STE_Constructor arity cs
	= (App { app_symb = { symb_name = ds_ident, symb_arity = ds_arity,
						  symb_kind = SK_Constructor { glob_object = ds_index, glob_module = glob_module }},
			 app_args = exprs, app_info_ptr = nilPtr }, free_vars, e_state, e_info, cs)
where
	check_expression_list free_vars [] e_input e_state e_info cs
		= ([], 0, free_vars, e_state, e_info, cs)
	check_expression_list free_vars [expr : exprs] e_input e_state e_info cs
		# (expr, free_vars, e_state, e_info, cs) = checkExpression free_vars expr e_input e_state e_info cs
		  (exprs, length, free_vars, e_state, e_info, cs) = check_expression_list free_vars exprs e_input e_state e_info cs
		= ([expr : exprs], inc length, free_vars, e_state, e_info, cs)

checkExpression free_vars rec=:(PE_Record record opt_type fields) e_input=:{ei_expr_level,ei_mod_index} e_state e_info cs
	# (opt_record_and_fields, e_info, cs) = checkFields ei_mod_index fields opt_type e_info cs
	= case opt_record_and_fields of
		Yes (cons=:{glob_module, glob_object}, _, new_fields)
			# {ds_ident,ds_index,ds_arity} = glob_object
			  rec_cons = { symb_name = ds_ident, symb_kind = SK_Constructor { glob_object = ds_index, glob_module = glob_module }, symb_arity = ds_arity }
			-> case record of
				PE_Empty
					# (exprs, free_vars, e_state, e_info, cs) = check_field_exprs free_vars new_fields 0 RK_Constructor e_input e_state e_info cs
					-> (App { app_symb = rec_cons, app_args = remove_fields exprs, app_info_ptr = nilPtr }, free_vars, e_state, e_info, cs)
				_
					# (rec_expr, free_vars, e_state, e_info, cs) = checkExpression free_vars record e_input e_state e_info cs
					-> case rec_expr of
						Var {var_info_ptr,var_name}
							# (var_info, es_var_heap) = readPtr var_info_ptr e_state.es_var_heap
							  e_state = { e_state & es_var_heap = es_var_heap }
							-> case var_info of
								VI_Record fields
									# (exprs, free_vars, e_state, e_info, cs) 
											= check_field_exprs free_vars new_fields 0 (RK_UpdateToConstructor fields) e_input e_state e_info cs
									-> (App { app_symb = rec_cons, app_args = remove_fields exprs, app_info_ptr = nilPtr }, free_vars, e_state, e_info, cs)
								_ 
									# (exprs, free_vars, e_state, e_info, cs)
											= check_field_exprs free_vars new_fields 0 RK_Update e_input e_state e_info cs
									-> (RecordUpdate cons rec_expr exprs, free_vars, e_state, e_info, cs)
						_ 
							# (exprs, free_vars, e_state, e_info, cs)
									= check_field_exprs free_vars new_fields 0 RK_Update e_input e_state e_info cs
							-> (RecordUpdate cons rec_expr exprs, free_vars, e_state, e_info, cs)
		No
			-> (EE, free_vars, e_state, e_info, cs)
where
	remove_fields binds = [ bind_src \\ {bind_src} <- binds ]

	check_field_exprs :: [FreeVar] [Bind ParsedExpr (Global FieldSymbol)] Int RecordKind ExpressionInput !*ExpressionState !*ExpressionInfo !*CheckState -> *(![.Bind Expression (Global FieldSymbol)],![FreeVar],!*ExpressionState,!*ExpressionInfo,!*CheckState);
	check_field_exprs free_vars [] field_nr record_kind e_input e_state e_info cs
		= ([], free_vars, e_state, e_info, cs)
	check_field_exprs free_vars [field_expr : field_exprs] field_nr record_kind e_input e_state e_info cs
		# (expr, free_vars, e_state, e_info, cs)
			= check_field_expr free_vars field_expr field_nr record_kind e_input e_state e_info cs
		  (exprs, free_vars, e_state, e_info, cs) = check_field_exprs free_vars field_exprs (inc field_nr) record_kind e_input e_state e_info cs
		= ([expr : exprs], free_vars, e_state, e_info, cs)

	check_field_expr :: [FreeVar] (Bind ParsedExpr (Global FieldSymbol)) Int RecordKind ExpressionInput *ExpressionState *ExpressionInfo *CheckState -> *(!.Bind Expression (Global FieldSymbol),![FreeVar],!*ExpressionState,!*ExpressionInfo,!*CheckState);
	check_field_expr free_vars field=:{bind_src = PE_Empty, bind_dst={glob_object={fs_var,fs_name,fs_index},glob_module}} field_nr record_kind e_input e_state e_info cs
		# (expr, free_vars, e_state, e_info, cs)
			= checkIdentExpression cIsNotInExpressionList free_vars fs_var e_input e_state e_info cs
		= ({ field & bind_src = expr }, free_vars, e_state, e_info, cs)
	check_field_expr free_vars field=:{bind_src = PE_WildCard, bind_dst={glob_object=fs_name}} field_nr RK_Constructor e_input e_state e_info cs
		= ({ field & bind_src = NoBind nilPtr }, free_vars, e_state, e_info, { cs & cs_error = checkError fs_name "field not specified" cs.cs_error })
	check_field_expr free_vars field=:{bind_src = PE_WildCard} field_nr RK_Update e_input e_state=:{es_expr_heap} e_info cs
		# (bind_expr_ptr, es_expr_heap) = newPtr EI_Empty es_expr_heap
		= ({ field & bind_src = NoBind bind_expr_ptr }, free_vars, { e_state & es_expr_heap = es_expr_heap }, e_info, cs)
	check_field_expr free_vars field=:{bind_src = PE_WildCard} field_nr (RK_UpdateToConstructor fields) e_input e_state=:{es_expr_heap} e_info cs
		# (var_name, var_info_ptr) = get_field_var (fields !! field_nr)
		  (var_expr_ptr, es_expr_heap) = newPtr EI_Empty es_expr_heap
		= ({ field & bind_src = Var { var_name = var_name, var_info_ptr = var_info_ptr, var_expr_ptr = var_expr_ptr }}, free_vars,
				{ e_state & es_expr_heap = es_expr_heap }, e_info, cs)
	check_field_expr free_vars field=:{bind_src} field_nr upd_record e_input e_state e_info cs
		# (expr, free_vars, e_state, e_info, cs)
			= checkExpression free_vars bind_src e_input e_state e_info cs
		= ({ field & bind_src = expr }, free_vars, e_state, e_info, cs)
	
	get_field_var (AP_Algebraic _ _ _ (Yes {bind_src,bind_dst}))
		= (bind_src, bind_dst)
	get_field_var (AP_Basic _ (Yes {bind_src,bind_dst}))
		= (bind_src, bind_dst)
	get_field_var (AP_Dynamic _ _ (Yes {bind_src,bind_dst}))
		= (bind_src, bind_dst)
	get_field_var (AP_Variable id var_ptr _)
		= (id, var_ptr)
	get_field_var (AP_WildCard (Yes {bind_src,bind_dst}))
		= (bind_src, bind_dst)
	get_field_var _
		= ({ id_name = "** ERRONEOUS **", id_info = nilPtr }, nilPtr)

checkExpression free_vars (PE_Dynamic expr opt_type) e_input e_state=:{es_expr_heap,es_dynamics} e_info cs=:{cs_x}
	# (dyn_info_ptr, es_expr_heap) = newPtr (EI_Dynamic opt_type) es_expr_heap
	  (dyn_expr, free_vars, e_state, e_info, cs) = checkExpression free_vars expr e_input
	  		{e_state & es_dynamics = [dyn_info_ptr : es_dynamics], es_expr_heap = es_expr_heap } e_info cs
	= (DynamicExpr { dyn_expr = dyn_expr, dyn_opt_type = opt_type, dyn_info_ptr = dyn_info_ptr, dyn_type_code = TCE_Empty, dyn_uni_vars = [] },
			free_vars, e_state, e_info, { cs & cs_x.x_needed_modules = cs_x.x_needed_modules bitor cNeedStdDynamics }) 

checkExpression free_vars (PE_Basic basic_value) e_input e_state e_info cs
	# (basic_type, cs) = typeOfBasicValue basic_value cs
	= (BasicExpr basic_value basic_type, free_vars, e_state, e_info, cs)

checkExpression free_vars (PE_ABC_Code code_sequence do_inline) e_input e_state e_info cs
	= (ABCCodeExpr code_sequence do_inline, free_vars, e_state, e_info, cs)
checkExpression free_vars (PE_Any_Code ins outs code_sequence) e_input e_state e_info cs
	# (ins, (free_vars, e_state, e_info, cs)) = check_in_parameters e_input ins (free_vars, e_state, e_info, cs)
	  (new_outs, (e_state, cs)) = check_out_parameters e_input.ei_expr_level outs (e_state, cs)
	  cs_symbol_table = remove_out_parameters_from_symbol_table e_input.ei_expr_level outs cs.cs_symbol_table
	= (AnyCodeExpr ins new_outs code_sequence, free_vars, e_state, e_info, { cs & cs_symbol_table = cs_symbol_table })
where
	check_in_parameters e_input params fv_es_ei_cs
		= mapSt (check_in_parameter e_input) params fv_es_ei_cs

	check_in_parameter e_input { bind_src, bind_dst } (free_vars, e_state, e_info, cs)
		# (id_expr, free_vars, e_state, e_info, cs) = checkIdentExpression cIsNotInExpressionList free_vars bind_dst e_input e_state e_info cs
		= case id_expr of
			Var var
				-> ({ bind_dst = var, bind_src = bind_src }, (free_vars, e_state, e_info, cs))
			_
				-> ({ bind_dst = { var_name = bind_dst, var_info_ptr = nilPtr, var_expr_ptr = nilPtr }, bind_src = bind_src }, (free_vars, e_state, e_info,
						{ cs & cs_error = checkError bind_src "bound variable expected" cs.cs_error }))

	check_out_parameters expr_level params es_cs
		= mapSt (check_out_parameter expr_level) params es_cs

	check_out_parameter expr_level bind=:{ bind_src, bind_dst } (e_state, cs)
		| isLowerCaseName bind_dst.id_name
			# (entry, cs_symbol_table) = readPtr bind_dst.id_info cs.cs_symbol_table
			# (new_info_ptr, es_var_heap) = newPtr VI_Empty e_state.es_var_heap
			  cs = checkPatternVariable expr_level entry bind_dst new_info_ptr { cs & cs_symbol_table = cs_symbol_table }
			= (	{ bind & bind_dst = { fv_def_level = expr_level, fv_name = bind_dst, fv_info_ptr = new_info_ptr, fv_count = 0 }},
					( { e_state & es_var_heap = es_var_heap }, cs))
			= ( { bind & bind_dst = { fv_def_level = expr_level, fv_name = bind_dst, fv_info_ptr = nilPtr, fv_count = 0 }},
					( e_state, { cs & cs_error = checkError bind_src "variable expected" cs.cs_error }))

	remove_out_parameters_from_symbol_table expr_level idents symbol_table
		= foldSt (\{bind_dst} -> removeIdentFromSymbolTable expr_level bind_dst) idents symbol_table

checkExpression free_vars (PE_Ident id) e_input e_state e_info cs
	= checkIdentExpression cIsNotInExpressionList free_vars id e_input e_state e_info cs
// AA..
checkExpression free_vars (PE_Generic id=:{id_name,id_info} kind) e_input e_state e_info cs=:{cs_symbol_table, cs_x}
	//= checkIdentExpression cIsNotInExpressionList free_vars id e_input e_state e_info cs
	# (entry, cs_symbol_table) = readPtr id_info cs_symbol_table
	= check_generic_expr free_vars entry id kind e_input e_state e_info {cs & cs_symbol_table = cs_symbol_table}
	where 
		check_generic_expr :: ![FreeVar] !SymbolTableEntry !Ident !TypeKind !ExpressionInput !*ExpressionState !*ExpressionInfo !*CheckState
			-> (!Expression, ![FreeVar], !*ExpressionState, !*ExpressionInfo, !*CheckState)
		check_generic_expr 
				free_vars entry=:{ste_kind=STE_Generic,ste_index} id  kind  
				e_input=:{ei_mod_index}  e_state 
				e_info=:{ef_generic_defs} cs
			//#! e_info = {e_info & ef_generic_defs = add_kind ef_generic_defs ste_index kind}	
			= check_it free_vars ei_mod_index ste_index id kind e_input e_state e_info cs	
		check_generic_expr 
				free_vars entry=:{ste_kind=STE_Imported STE_Generic mod_index, ste_index} id kind  
				e_input e_state 
				e_info=:{ef_modules} cs
			
			//#! (dcl_module, ef_modules) = ef_modules ! [mod_index]
			//#! (dcl_common, dcl_module) = dcl_module ! dcl_common 
			//#! (com_generic_defs, dcl_common) = dcl_common ! com_generic_defs
			//#! dcl_common = {dcl_common & com_generic_defs = add_kind com_generic_defs ste_index kind}
			//#! dcl_module = {dcl_module & dcl_common = dcl_common}
			//#! ef_modules = {ef_modules & [mod_index] = dcl_module} 
			//#! e_info = { e_info & ef_modules = ef_modules }

			= check_it free_vars mod_index ste_index id kind e_input e_state e_info cs	
		check_generic_expr free_vars  entry=:{ste_kind=STE_Empty} id kind  e_input e_state e_info cs=:{cs_error}
			= (EE, free_vars, e_state, e_info, { cs & cs_error = checkError id "undefined generic" cs_error })
		check_generic_expr free_vars entry id kind  e_input e_state e_info cs=:{cs_error}
			= (EE, free_vars, e_state, e_info, { cs & cs_error = checkError id "not a generic" cs_error })						

		check_it free_vars mod_index gen_index id kind e_input e_state=:{es_expr_heap} e_info cs
			#! symb_kind = SK_Generic { glob_object = gen_index, glob_module = mod_index} kind
		  	#! symbol = { symb_name = id, symb_kind = symb_kind, symb_arity = 0 }			
			#! (new_info_ptr, es_expr_heap) = newPtr EI_Empty es_expr_heap
			#! app = { app_symb = symbol, app_args = [], app_info_ptr = new_info_ptr }
			#! e_state = { e_state & es_expr_heap = es_expr_heap }
			#! cs = { cs & cs_x.x_needed_modules = cs_x.x_needed_modules bitor cNeedStdGeneric }
			= (App app, free_vars, e_state, e_info, cs)

		add_kind :: !*{#GenericDef} !Index !TypeKind -> !*{#GenericDef}			
		add_kind generic_defs generic_index kind
			# (generic_def, generic_defs) = generic_defs ! [generic_index]		
			= {generic_defs & [generic_index] = addGenericKind generic_def kind}
			 									 
// ..AA
checkExpression free_vars expr e_input e_state e_info cs
	= abort "checkExpression (checkFunctionBodies.icl, line 868)" // <<- expr


checkIdentExpression :: !Bool ![FreeVar] !Ident !ExpressionInput !*ExpressionState !u:ExpressionInfo !*CheckState
	-> (!Expression, ![FreeVar], !*ExpressionState, !u:ExpressionInfo, !*CheckState)
checkIdentExpression is_expr_list free_vars id=:{id_info} e_input e_state e_info cs=:{cs_symbol_table}
	# (entry, cs_symbol_table) = readPtr id_info cs_symbol_table
	= check_id_expression entry is_expr_list free_vars id e_input e_state e_info { cs & cs_symbol_table = cs_symbol_table }
where
	check_id_expression :: !SymbolTableEntry !Bool ![FreeVar] !Ident !ExpressionInput !*ExpressionState !u:ExpressionInfo !*CheckState
		-> (!Expression, ![FreeVar], !*ExpressionState, !u:ExpressionInfo, !*CheckState)

	check_id_expression {ste_kind = STE_Empty} is_expr_list free_vars id e_input e_state e_info cs=:{cs_error,cs_predef_symbols,cs_x}
		# ({pds_ident=from_ident}) = cs_predef_symbols.[PD_From]
		  ({pds_ident=from_then_ident}) = cs_predef_symbols.[PD_FromThen]
		  ({pds_ident=from_to_ident}) = cs_predef_symbols.[PD_FromTo]
		  ({pds_ident=from_then_to_ident}) = cs_predef_symbols.[PD_FromThenTo]
		| id==from_ident || id==from_then_ident || id==from_to_ident || id==from_then_to_ident
			= (EE, free_vars, e_state, e_info, { cs & cs_x.x_needed_modules = cs_x.x_needed_modules bitor cNeedStdEnum})
				// instead of giving an error message remember that StdEnum should have been imported.
				// Error will be given in function check_needed_modules_are_imported
		# ({pds_ident=createArray_ident}) = cs_predef_symbols.[PD__CreateArrayFun]
		  ({pds_ident=uselect_ident}) = cs_predef_symbols.[PD_UnqArraySelectFun]
		  ({pds_ident=update_ident}) = cs_predef_symbols.[PD_ArrayUpdateFun]
		  ({pds_ident=usize_ident}) = cs_predef_symbols.[PD_UnqArraySizeFun]
		| id==createArray_ident || id==uselect_ident || id==update_ident || id==usize_ident
			= (EE, free_vars, e_state, e_info, { cs & cs_x.x_needed_modules = cs_x.x_needed_modules bitor cNeedStdArray})
				// instead of giving an error message remember that StdArray should have been be imported.
				//  Error will be given in function check_needed_modules_are_imported
		= (EE, free_vars, e_state, e_info, { cs & cs_error = checkError id "undefined" cs_error })
	check_id_expression {ste_kind = STE_Variable info_ptr,ste_def_level} is_expr_list free_vars id e_input=:{ei_fun_level} e_state=:{es_expr_heap} e_info cs
		| ste_def_level < ei_fun_level
			# free_var = { fv_def_level = ste_def_level, fv_name = id, fv_info_ptr = info_ptr, fv_count = 0 }
			  (free_var_added, free_vars) = newFreeVariable free_var free_vars
			= (FreeVar free_var, free_vars, e_state, e_info, cs)
			#! (var_expr_ptr, es_expr_heap) = newPtr EI_Empty es_expr_heap
			= (Var {var_name = id, var_info_ptr = info_ptr, var_expr_ptr = var_expr_ptr}, free_vars,
					{e_state & es_expr_heap = es_expr_heap}, e_info, cs)
	check_id_expression entry is_expr_list free_vars id=:{id_info} e_input e_state e_info cs
		# (symb_kind, arity, priority, is_a_function, e_state, e_info, cs) = determine_info_of_symbol entry id_info e_input e_state e_info cs
		  symbol = { symb_name = id, symb_kind = symb_kind, symb_arity = 0 }
  		| is_expr_list
			= (Constant symbol arity priority is_a_function, free_vars, e_state, e_info, cs)
			# (app_expr, e_state, cs_error) = buildApplication symbol arity 0 is_a_function [] e_state cs.cs_error
			= (app_expr, free_vars, e_state, e_info, { cs & cs_error = cs_error })

	determine_info_of_symbol :: !SymbolTableEntry !SymbolPtr !ExpressionInput !*ExpressionState !u:ExpressionInfo !*CheckState
		-> (!SymbKind, !Int, !Priority, !Bool, !*ExpressionState, !u:ExpressionInfo,!*CheckState)
	determine_info_of_symbol entry=:{ste_kind=STE_FunctionOrMacro calls,ste_index,ste_def_level} symb_info
				e_input=:{ei_fun_index, ei_mod_index} e_state=:{es_fun_defs,es_calls} e_info cs=:{cs_symbol_table,cs_x}
		# ({fun_symb,fun_arity,fun_kind,fun_priority,fun_info={fi_properties}}, es_fun_defs) = es_fun_defs![ste_index]
		# index = { glob_object = ste_index, glob_module = cs_x.x_main_dcl_module_n }
		| is_called_before ei_fun_index calls
			| case fun_kind of FK_DefMacro->True ; FK_ImpMacro->True; _ -> False
				= (SK_Macro index, fun_arity, fun_priority, cIsAFunction, { e_state & es_fun_defs = es_fun_defs }, e_info, cs)
				# symbol_kind = if (fi_properties bitand FI_IsMacroFun <> 0) (SK_LocalMacroFunction ste_index) (SK_Function index)
				= (symbol_kind, fun_arity, fun_priority, cIsAFunction, { e_state & es_fun_defs = es_fun_defs }, e_info, cs)
			# cs = { cs & cs_symbol_table = cs_symbol_table <:= (symb_info, { entry & ste_kind = STE_FunctionOrMacro [ ei_fun_index : calls ]})}
			  e_state = { e_state & es_fun_defs = es_fun_defs, es_calls = [{ fc_index = ste_index, fc_level = ste_def_level} : es_calls ]}
			# symbol_kind = case fun_kind of
				FK_DefMacro
					-> SK_Macro index;
				FK_ImpMacro
					-> SK_Macro index;
				_
					| fi_properties bitand FI_IsMacroFun <> 0
						-> SK_LocalMacroFunction ste_index
						-> SK_Function index
			= (symbol_kind, fun_arity, fun_priority, cIsAFunction, e_state, e_info, cs)
	where
		is_called_before caller_index []
			= False
		is_called_before caller_index [called_index : calls]
			= caller_index == called_index || is_called_before caller_index calls

	determine_info_of_symbol entry=:{ste_kind=STE_Imported kind mod_index,ste_index} symb_index e_input e_state e_info=:{ef_modules} cs
		# (mod_def, ef_modules) = ef_modules![mod_index]
		# (kind, arity, priotity, is_fun) = ste_kind_to_symbol_kind kind ste_index mod_index mod_def
		= (kind, arity, priotity, is_fun, e_state, { e_info & ef_modules = ef_modules }, cs)
	where
		ste_kind_to_symbol_kind :: !STE_Kind !Index !Index !DclModule -> (!SymbKind, !Int, !Priority, !Bool);
		ste_kind_to_symbol_kind STE_DclFunction def_index mod_index {dcl_functions,dcl_conversions}
			# {ft_type={st_arity},ft_priority} = dcl_functions.[def_index]
			# def_index = convertIndex def_index (toInt STE_DclFunction) dcl_conversions
			= (SK_Function { glob_object = def_index, glob_module = mod_index }, st_arity, ft_priority, cIsAFunction)
		ste_kind_to_symbol_kind STE_Member def_index mod_index {dcl_common={com_member_defs},dcl_conversions}
			# {me_type={st_arity},me_priority} = com_member_defs.[def_index]
			# def_index = convertIndex def_index (toInt STE_Member) dcl_conversions
			= (SK_OverloadedFunction { glob_object = def_index, glob_module = mod_index }, st_arity, me_priority, cIsAFunction)
		ste_kind_to_symbol_kind STE_Constructor def_index mod_index {dcl_common={com_cons_defs},dcl_conversions}
			# {cons_type={st_arity},cons_priority} = com_cons_defs.[def_index]
			# def_index = convertIndex def_index (toInt STE_Constructor) dcl_conversions
			= (SK_Constructor { glob_object = def_index, glob_module = mod_index }, st_arity, cons_priority, cIsNotAFunction)

	determine_info_of_symbol {ste_kind=STE_Member, ste_index} _ e_input=:{ei_mod_index} e_state e_info=:{ef_member_defs} cs
		# ({me_type={st_arity},me_priority}, ef_member_defs) = ef_member_defs![ste_index]
		= (SK_OverloadedFunction { glob_object = ste_index, glob_module = ei_mod_index}, st_arity, me_priority, cIsAFunction,
				e_state, { e_info & ef_member_defs = ef_member_defs }, cs)
	determine_info_of_symbol {ste_kind=STE_Constructor, ste_index} _ e_input=:{ei_mod_index} e_state e_info=:{ef_cons_defs} cs
		# ({cons_type={st_arity},cons_priority}, ef_cons_defs) = ef_cons_defs![ste_index]
		= (SK_Constructor { glob_object = ste_index, glob_module =  ei_mod_index}, st_arity, cons_priority, cIsNotAFunction,
				e_state, { e_info & ef_cons_defs = ef_cons_defs }, cs)
	determine_info_of_symbol {ste_kind=STE_DclFunction, ste_index} _ e_input=:{ei_mod_index} e_state e_info=:{ef_modules} cs
		# (mod_def, ef_modules) = ef_modules![ei_mod_index]
		# {ft_type={st_arity},ft_priority} = mod_def.dcl_functions.[ste_index]
		  def_index = convertIndex ste_index (toInt STE_DclFunction) mod_def.dcl_conversions
		= (SK_Function { glob_object = def_index, glob_module =  ei_mod_index}, st_arity, ft_priority, cIsAFunction,
				e_state, { e_info & ef_modules = ef_modules }, cs)



checkPattern :: !ParsedExpr !(Optional (Bind Ident VarInfoPtr)) !PatternInput !(![Ident], ![ArrayPattern]) !*PatternState !*ExpressionInfo !*CheckState
									-> (!AuxiliaryPattern, !(![Ident], ![ArrayPattern]), !*PatternState, !*ExpressionInfo, !*CheckState)
checkPattern (PE_List [exp]) opt_var p_input accus ps e_info cs=:{cs_symbol_table}
	= case exp of
		PE_Ident ident
			-> checkIdentPattern cIsNotInExpressionList ident opt_var p_input accus ps e_info cs
		_
			-> checkPattern exp opt_var p_input accus ps e_info cs

checkPattern (PE_List [exp1, exp2 : exps]) opt_var p_input accus ps e_info cs
	# (exp_pat, accus, ps, e_info, cs) = check_pattern exp1 p_input accus ps e_info cs
	= check_patterns [exp_pat] exp2 exps opt_var p_input accus ps e_info cs
	where
		check_patterns left middle [] opt_var p_input=:{pi_mod_index} accus ps e_info cs
			# (mid_pat, accus, ps, e_info, cs) = checkPattern middle No p_input accus ps e_info cs
			  (pat, ps, e_info, cs) = combine_patterns pi_mod_index opt_var [mid_pat : left] [] 0 ps e_info cs
			= (pat, accus, ps, e_info, cs)
		check_patterns left middle [right:rest] opt_var p_input=:{pi_mod_index} accus ps e_info cs
			# (mid_pat, accus, ps, e_info, cs) = check_pattern middle p_input accus ps e_info cs
			= case mid_pat of
				AP_Constant kind constant=:{glob_object={ds_arity,ds_ident}} prio
					| ds_arity == 0
						# (pattern, ps, e_info, cs) = buildPattern pi_mod_index kind constant [] No ps e_info cs
						-> check_patterns [pattern: left] right rest opt_var p_input accus ps e_info cs
					| is_infix_constructor prio
						# (left_arg, ps, e_info, cs) = combine_patterns pi_mod_index No left [] 0 ps e_info cs
						  (right_pat, accus, ps, e_info, cs) = check_pattern right p_input accus ps e_info cs
						-> check_infix_pattern [] left_arg kind constant prio [right_pat] rest
									opt_var p_input accus ps e_info cs
						-> (AP_Empty ds_ident, accus, ps, e_info,
								{ cs & cs_error = checkError ds_ident "arguments of constructor are missing" cs.cs_error })
				_
					-> check_patterns [mid_pat : left] right rest opt_var p_input accus ps e_info cs

		check_pattern (PE_Ident id) p_input accus ps e_info cs
			= checkIdentPattern cIsInExpressionList id No p_input accus ps e_info cs
		check_pattern expr p_input accus ps e_info cs
			= checkPattern expr No p_input accus ps e_info cs
		
	 	check_infix_pattern left_args left kind cons prio middle [] opt_var p_input=:{pi_mod_index} accus ps e_info cs
			# (middle_pat, ps, e_info, cs) = combine_patterns pi_mod_index No middle [] 0 ps e_info cs
			  (pattern, ps, e_info, cs) = buildPattern pi_mod_index kind cons [left,middle_pat] opt_var ps e_info cs
			  (pattern, ps, e_info, cs) = build_final_pattern pi_mod_index left_args pattern ps e_info cs
			= (pattern, accus, ps, e_info, cs)
	 	check_infix_pattern left_args left kind cons prio middle [right] opt_var  p_input=:{pi_mod_index} accus ps e_info cs
			# (right_pat, accus, ps, e_info, cs) = checkPattern right No p_input accus ps e_info cs
			  (right_arg, ps, e_info, cs) = combine_patterns pi_mod_index No [right_pat : middle] [] 0 ps e_info cs
			  (pattern, ps, e_info, cs) = buildPattern pi_mod_index kind cons [left,right_arg] opt_var ps e_info cs
			  (pattern, ps, e_info, cs) = build_final_pattern pi_mod_index left_args pattern ps e_info cs
			= (pattern, accus, ps, e_info, cs)
	 	check_infix_pattern left_args left kind1 cons1 prio1 middle [inf_cons, arg : rest] opt_var p_input=:{pi_mod_index} accus ps e_info cs
			# (inf_cons_pat, accus, ps, e_info, cs) = check_pattern inf_cons p_input accus ps e_info cs
			= case inf_cons_pat of
				AP_Constant kind2 cons2=:{glob_object={ds_ident,ds_arity}} prio2
					| ds_arity == 0
						# (middle_pat, ps, e_info, cs) = combine_patterns pi_mod_index No middle [] 0 ps e_info cs
						  (pattern2, ps, e_info, cs) = buildPattern pi_mod_index kind2 cons2 [] No ps e_info cs
						  (pattern1, ps, e_info, cs) = buildPattern pi_mod_index kind1 cons1 [left,middle_pat] No ps e_info cs
						  (pattern1, ps, e_info, cs) = build_final_pattern pi_mod_index left_args pattern1 ps e_info cs
						-> check_patterns [pattern2,pattern1] arg rest opt_var p_input accus ps e_info cs
					| is_infix_constructor prio2
						# optional_prio = determinePriority prio1 prio2
						-> case optional_prio of
							Yes priority
								# (arg_pat, accus, ps, e_info, cs) = check_pattern arg p_input accus ps e_info cs
								| priority
									# (middle_pat, ps, e_info, cs) = combine_patterns pi_mod_index No middle [] 0 ps e_info cs
								      (pattern, ps, e_info, cs) = buildPattern pi_mod_index kind1 cons1 [left,middle_pat] No ps e_info cs
								      (left_args, pattern, ps, e_info, cs) = build_left_pattern pi_mod_index left_args prio2 pattern ps e_info cs
									-> check_infix_pattern left_args pattern kind2 cons2 prio2 [arg_pat] rest opt_var p_input accus ps e_info cs 
									# (middle_pat, ps, e_info, cs) = combine_patterns pi_mod_index No middle [] 0 ps e_info cs
									-> check_infix_pattern [(kind1, cons1, prio1, left) : left_args]
									  				middle_pat kind2 cons2 prio2 [arg_pat] rest No p_input accus ps e_info cs
							No
								-> (AP_Empty ds_ident, accus, ps, e_info, { cs & cs_error = checkError ds_ident "conflicting priorities" cs.cs_error })
						-> (AP_Empty ds_ident, accus, ps, e_info, { cs & cs_error = checkError ds_ident "arguments of constructor are missing" cs.cs_error })
				_
					-> check_infix_pattern left_args left kind1 cons1 prio1 [inf_cons_pat : middle] [arg : rest] opt_var p_input accus ps e_info cs 

		is_infix_constructor (Prio _ _) = True
		is_infix_constructor _ = False

		build_left_pattern mod_index [] _ result_pattern ps e_info cs
			= ([], result_pattern, ps, e_info, cs)		
		build_left_pattern mod_index la=:[(kind, cons, priol, left) : left_args] prior result_pattern ps e_info cs
			# optional_prio = determinePriority priol prior
			= case optional_prio of
				Yes priority
					| priority
						# (result_pattern,  ps, e_info, cs) = buildPattern mod_index kind cons [left,result_pattern] No ps e_info cs
						-> build_left_pattern mod_index left_args prior result_pattern ps e_info cs
						-> (la, result_pattern,  ps, e_info, cs)
				No
					-> (la, result_pattern,  ps, e_info,{ cs & cs_error = checkError cons.glob_object.ds_ident "conflicting priorities" cs.cs_error })

		build_final_pattern mod_index [] result_pattern ps e_info cs
			= (result_pattern,  ps, e_info, cs)		
		build_final_pattern mod_index [(kind, cons, priol, left) : left_appls] result_pattern ps e_info cs
			# (result_pattern, ps, e_info, cs) = buildPattern mod_index kind cons [left,result_pattern] No ps e_info cs
			= build_final_pattern mod_index left_appls result_pattern ps e_info cs

		combine_patterns mod_index opt_var [first_expr] args nr_of_args ps e_info cs
			= case first_expr of
				AP_Constant kind constant=:{glob_object={ds_ident,ds_arity}} _
					| ds_arity == nr_of_args
						# (pattern, ps, e_info, cs) = buildPattern mod_index kind constant args opt_var ps e_info cs
						-> (pattern, ps, e_info, cs)
						-> (AP_Empty ds_ident, ps, e_info, { cs & cs_error = checkError ds_ident "used with wrong arity" cs.cs_error})
				_
					| nr_of_args == 0
						-> (first_expr, ps, e_info, cs)
						-> (first_expr, ps, e_info, { cs & cs_error = checkError "<pattern>" "(curried) application not allowed " cs.cs_error })
		combine_patterns mod_index opt_var [rev_arg : rev_args] args arity ps e_info cs
			= combine_patterns mod_index opt_var rev_args [rev_arg : args] (inc arity) ps e_info cs
/*
		combine_optional_variables (Yes var1) (Yes var2) error
			= (Yes var1, checkError var2.bind_dst "pattern already bound" error)
		combine_optional_variables No opt_var error
			= (opt_var, error)
		combine_optional_variables opt_var _ error
			= (opt_var, error)
*/

checkPattern (PE_DynamicPattern pattern type) opt_var p_input accus ps e_info cs=:{cs_x}
	# (dyn_pat, accus, ps, e_info, cs) = checkPattern pattern No p_input accus ps e_info cs
	= (AP_Dynamic dyn_pat type opt_var, accus, ps, e_info, { cs & cs_x.x_needed_modules = cs_x.x_needed_modules bitor cNeedStdDynamics })

checkPattern (PE_Basic basic_value) opt_var p_input accus ps e_info cs
	= (AP_Basic basic_value opt_var, accus, ps, e_info, cs)

checkPattern (PE_Tuple tuple_args) opt_var p_input accus ps e_info cs
	# (patterns, arity, accus, ps, e_info, cs) = check_tuple_patterns tuple_args p_input accus ps e_info cs
	  (tuple_symbol, cs) = getPredefinedGlobalSymbol (GetTupleConsIndex arity) PD_PredefinedModule STE_Constructor arity cs
	# ({cons_type_index}, e_info) = e_info!ef_modules.[tuple_symbol.glob_module].dcl_common.com_cons_defs.[tuple_symbol.glob_object.ds_index]
	= (AP_Algebraic tuple_symbol cons_type_index patterns opt_var, accus, ps, e_info, cs)
where
	check_tuple_patterns [] p_input accus ps e_info cs
		= ([], 0, accus, ps, e_info, cs)
	check_tuple_patterns [expr : exprs] p_input accus ps e_info cs
		# (pattern, accus, ps, e_info, cs) = checkPattern expr No p_input accus ps e_info cs
		  (patterns, length, accus, ps, e_info, cs) = check_tuple_patterns exprs p_input accus ps e_info cs
		= ([pattern : patterns], inc length, accus, ps, e_info, cs)
checkPattern (PE_Record record opt_type fields) opt_var p_input=:{pi_mod_index, pi_is_node_pattern} accus=:(var_env, array_patterns) ps e_info cs
	# (opt_record_and_fields, e_info, cs) = checkFields pi_mod_index fields opt_type e_info cs
	= case opt_record_and_fields of
		Yes (record_symbol, type_index, new_fields)
			# (patterns, (var_env, array_patterns, ps, e_info, cs)) = mapSt (check_field_pattern p_input) new_fields (var_env, array_patterns, ps, e_info, cs)
			  (patterns, ps_var_heap) = bind_opt_record_variable opt_var pi_is_node_pattern patterns new_fields ps.ps_var_heap
			-> (AP_Algebraic record_symbol type_index patterns opt_var, (var_env, array_patterns), { ps & ps_var_heap = ps_var_heap }, e_info, cs)
		No
			-> (AP_Empty (hd fields).bind_dst, accus, ps, e_info, cs)
where

	check_field_pattern p_input=:{pi_def_level} {bind_src = PE_Empty, bind_dst = {glob_object={fs_var}}} 
						(var_env, array_patterns, ps, e_info, cs)
		# (entry, cs_symbol_table) = readPtr fs_var.id_info cs.cs_symbol_table
		# (new_info_ptr, ps_var_heap) = newPtr VI_Empty ps.ps_var_heap
		  cs = checkPatternVariable pi_def_level entry fs_var new_info_ptr { cs & cs_symbol_table = cs_symbol_table }
		= (AP_Variable fs_var new_info_ptr No, ([ fs_var : var_env ], array_patterns, { ps & ps_var_heap = ps_var_heap }, e_info, cs))
	check_field_pattern p_input {bind_src = PE_WildCard, bind_dst={glob_object={fs_var}}} (var_env, array_patterns, ps, e_info, cs)
		# (new_info_ptr, ps_var_heap) = newPtr VI_Empty ps.ps_var_heap
		= (AP_WildCard (Yes { bind_src = fs_var, bind_dst = new_info_ptr}), (var_env, array_patterns, { ps & ps_var_heap = ps_var_heap }, e_info, cs))
	check_field_pattern p_input {bind_src,bind_dst} (var_env, array_patterns, ps, e_info, cs)
		# (pattern, (var_env, array_patterns), ps, e_info, cs) = checkPattern bind_src No p_input (var_env, array_patterns) ps e_info cs
		= (pattern, (var_env, array_patterns, ps, e_info, cs))


	add_bound_variable (AP_Algebraic symbol index patterns No) {bind_dst = {glob_object={fs_var}}} ps_var_heap
		# (new_info_ptr, ps_var_heap) = newPtr VI_Empty ps_var_heap
		= (AP_Algebraic symbol index patterns (Yes { bind_src = fs_var, bind_dst = new_info_ptr}), ps_var_heap)
	add_bound_variable (AP_Basic bas_val No) {bind_dst = {glob_object={fs_var}}} ps_var_heap
		# (new_info_ptr, ps_var_heap) = newPtr VI_Empty ps_var_heap
		= (AP_Basic bas_val (Yes { bind_src = fs_var, bind_dst = new_info_ptr}), ps_var_heap)
	add_bound_variable (AP_Dynamic dynamic_pattern dynamic_type No) {bind_dst = {glob_object={fs_var}}} ps_var_heap
		# (new_info_ptr, ps_var_heap) = newPtr VI_Empty ps_var_heap
		= (AP_Dynamic dynamic_pattern dynamic_type (Yes { bind_src = fs_var, bind_dst = new_info_ptr}), ps_var_heap)
	add_bound_variable pattern _ ps_var_heap
		= (pattern, ps_var_heap)

	add_bound_variables [] _ var_heap
		= ([] , var_heap)
	add_bound_variables [ap : aps] [field : fields] var_heap
		# (ap, var_heap) = add_bound_variable ap field var_heap
		  (aps, var_heap) = add_bound_variables aps fields var_heap
		= ([ap : aps], var_heap)

	bind_opt_record_variable (Yes {bind_dst}) False patterns fields var_heap
		# (patterns, var_heap) = add_bound_variables patterns fields var_heap
		= (patterns, var_heap <:= (bind_dst, VI_Record patterns))
	bind_opt_record_variable no is_node_pattern patterns _ var_heap
		= (patterns, var_heap)

checkPattern (PE_Bound bind) opt_var p_input accus ps e_info cs
	= checkBoundPattern bind opt_var p_input accus ps e_info cs
checkPattern (PE_Ident id) opt_var p_input accus ps e_info cs
	= checkIdentPattern cIsNotInExpressionList id opt_var p_input accus ps e_info cs
checkPattern PE_WildCard opt_var p_input accus ps e_info cs
	= (AP_WildCard No, accus, ps, e_info, cs)
checkPattern (PE_ArrayPattern selections) opt_var p_input (var_env, array_patterns) ps e_info cs
	# (var_env, ap_selections, ps_var_heap, cs)
			= foldSt (check_array_selection p_input.pi_def_level) selections (var_env, [], ps.ps_var_heap, cs)
	  array_var_ident = case opt_var of 
	  						Yes {bind_src}
	  							-> bind_src
	  						No
	  							-> { id_name = "_a", id_info = nilPtr }
	  (array_var, ps_var_heap) = allocate_free_var array_var_ident ps_var_heap
	= (AP_Variable array_var_ident array_var.fv_info_ptr No, 
		(var_env, [{ ap_opt_var = opt_var, ap_array_var = array_var, ap_selections = ap_selections } :array_patterns]),
		{ ps & ps_var_heap = ps_var_heap }, e_info, cs)
  where
	check_array_selection def_level bind=:{bind_dst} states
		= check_rhs def_level bind (foldSt check_index_expr bind_dst states)
		
	check_index_expr (PE_Ident {id_name}) states
		| isLowerCaseName id_name
			= states
		// further with next alternative
	check_index_expr (PE_Basic (BVI _)) states
			= states
	check_index_expr _ (var_env, ap_selections, var_heap, cs)
		= (var_env, ap_selections, var_heap, { cs & cs_error = checkError "" "variable or integer constant expected as index expression" cs.cs_error })

	check_rhs def_level {bind_src=PE_Ident ident, bind_dst} (var_env, ap_selections, var_heap, cs)
		| isLowerCaseName ident.id_name
			# (entry,cs_symbol_table) = readPtr ident.id_info cs.cs_symbol_table
			# (rhs_var, var_heap) = allocate_free_var ident var_heap
			  cs = checkPatternVariable def_level entry ident rhs_var.fv_info_ptr { cs & cs_symbol_table = cs_symbol_table }
			= ([ident : var_env], [ { bind_src = rhs_var, bind_dst = bind_dst } : ap_selections], var_heap, cs)
		// further with next alternative
	check_rhs _ _ (var_env, ap_selections, var_heap, cs)
		= (var_env, ap_selections, var_heap, 
			{ cs & cs_error = checkError "" "variable expected on right hand side of array pattern" cs.cs_error })
checkPattern expr opt_var p_input accus ps e_info cs
	= abort "checkPattern: do not know how to handle pattern" ---> expr



checkPatternConstructor :: !Index !Bool !SymbolTableEntry !Ident !(Optional (Bind Ident VarInfoPtr)) !*PatternState !*ExpressionInfo !*CheckState
	-> (!AuxiliaryPattern, !*PatternState, !*ExpressionInfo, !*CheckState);
checkPatternConstructor _ _ {ste_kind = STE_Empty} ident _  ps e_info cs=:{cs_error}
	= (AP_Empty ident, ps, e_info, { cs & cs_error = checkError ident " not defined" cs_error })
checkPatternConstructor mod_index is_expr_list {ste_kind = STE_FunctionOrMacro _,ste_index} ident opt_var  ps=:{ps_fun_defs} e_info cs=:{cs_error,cs_x}
	# ({fun_symb,fun_arity,fun_kind,fun_priority},ps_fun_defs) = ps_fun_defs![ste_index]
	  ps = { ps & ps_fun_defs = ps_fun_defs }
	| case fun_kind of FK_DefMacro->True ; FK_ImpMacro->True; _ -> False
		| is_expr_list
			# macro_symbol = { glob_object = MakeDefinedSymbol fun_symb ste_index fun_arity, glob_module = cs_x.x_main_dcl_module_n }
	 		= (AP_Constant APK_Macro macro_symbol fun_priority, ps, e_info, cs)
		| fun_arity == 0
			# (pattern, ps, ef_modules, ef_cons_defs, cs_error)
					= unfoldPatternMacro mod_index ste_index [] opt_var ps e_info.ef_modules e_info.ef_cons_defs cs_error
			= (pattern, ps, { e_info & ef_modules = ef_modules, ef_cons_defs = ef_cons_defs }, { cs & cs_error = cs_error })
			= (AP_Empty ident, ps, e_info, { cs & cs_error = checkError ident " not defined" cs_error })
		= (AP_Empty ident, ps, e_info, { cs & cs_error = checkError fun_symb " not allowed in a pattern" cs_error })
checkPatternConstructor mod_index is_expr_list {ste_index, ste_kind} cons_symb opt_var ps
		e_info=:{ef_cons_defs,ef_modules} cs=:{cs_error}
	# (cons_index, cons_module, cons_arity, cons_priority, cons_type_index, ef_cons_defs, ef_modules, cs_error)
			= determine_pattern_symbol mod_index ste_index ste_kind cons_symb.id_name ef_cons_defs ef_modules cs_error
	  e_info = { e_info & ef_cons_defs = ef_cons_defs, ef_modules = ef_modules }
	  cons_symbol = { glob_object = MakeDefinedSymbol cons_symb cons_index cons_arity, glob_module = cons_module }
   	| is_expr_list
		= (AP_Constant (APK_Constructor cons_type_index) cons_symbol cons_priority, ps, e_info, { cs & cs_error = cs_error })
	| cons_arity == 0
		= (AP_Algebraic cons_symbol cons_type_index [] opt_var, ps, e_info, { cs & cs_error = cs_error })
		= (AP_Algebraic cons_symbol cons_type_index [] opt_var, ps, e_info, { cs & cs_error = checkError cons_symb " constructor arguments are missing" cs_error })
where
	determine_pattern_symbol mod_index id_index STE_Constructor id_name cons_defs modules error
		# ({cons_type={st_arity},cons_priority, cons_type_index}, cons_defs) = cons_defs![id_index]
		= (id_index, mod_index, st_arity, cons_priority, cons_type_index, cons_defs, modules, error)
	determine_pattern_symbol mod_index id_index (STE_Imported STE_Constructor import_mod_index) id_name cons_defs modules error
		# ({dcl_common,dcl_conversions},modules) = modules![import_mod_index]
		  {cons_type={st_arity},cons_priority, cons_type_index} = dcl_common.com_cons_defs.[id_index]
		  id_index = convertIndex id_index (toInt STE_Constructor) dcl_conversions
		= (id_index, import_mod_index, st_arity, cons_priority, cons_type_index, cons_defs, modules, error)
	determine_pattern_symbol mod_index id_index id_kind id_name cons_defs modules error
		= (id_index, NoIndex, 0, NoPrio, NoIndex, cons_defs, modules, checkError id_name " constructor expected" error)



checkBoundPattern {bind_src,bind_dst} opt_var p_input (var_env, array_patterns) ps e_info cs=:{cs_symbol_table}
	| isLowerCaseName bind_dst.id_name
		# (entry, cs_symbol_table) = readPtr bind_dst.id_info cs_symbol_table
		# (new_info_ptr, ps_var_heap) = newPtr VI_Empty ps.ps_var_heap
		  cs = checkPatternVariable p_input.pi_def_level entry bind_dst new_info_ptr { cs & cs_symbol_table = cs_symbol_table }
		  ps = { ps & ps_var_heap = ps_var_heap }
		  new_var_env = [ bind_dst : var_env ]
		= case opt_var of
			Yes bind
				-> checkPattern bind_src (Yes { bind_src = bind_dst, bind_dst = new_info_ptr }) p_input (new_var_env, array_patterns) ps
					 	e_info { cs & cs_error = checkError bind.bind_src "pattern may be bound once only" cs.cs_error }
			No
				-> checkPattern bind_src (Yes { bind_src = bind_dst, bind_dst = new_info_ptr }) p_input (new_var_env, array_patterns) ps e_info cs
	= checkPattern bind_src opt_var p_input (var_env, array_patterns) ps e_info { cs & cs_error = checkError bind_dst "variable expected" cs.cs_error }




checkPatternVariable :: !Level !SymbolTableEntry !Ident !VarInfoPtr !*CheckState -> !*CheckState
checkPatternVariable def_level entry=:{ste_def_level,ste_kind} ident=:{id_info} var_info cs=:{cs_symbol_table,cs_error}
	| ste_kind == STE_Empty || def_level > ste_def_level
		# entry = {ste_kind = STE_Variable var_info, ste_index = NoIndex, ste_def_level = def_level, ste_previous = entry }
		= { cs & cs_symbol_table = cs_symbol_table <:= (id_info,entry)}
		= { cs & cs_error = checkError ident "(pattern variable) already defined" cs_error }



checkIdentPattern :: !Bool !Ident !(Optional (Bind Ident VarInfoPtr)) !PatternInput !(![Ident], ![ArrayPattern]) !*PatternState !*ExpressionInfo !*CheckState
	-> (!AuxiliaryPattern, !(![Ident], ![ArrayPattern]), !*PatternState, !*ExpressionInfo, !*CheckState)
checkIdentPattern is_expr_list id=:{id_name,id_info} opt_var {pi_def_level, pi_mod_index} accus=:(var_env, array_patterns)
					ps e_info cs=:{cs_symbol_table}
	# (entry, cs_symbol_table) = readPtr id_info cs_symbol_table
	| isLowerCaseName id_name
		# (new_info_ptr, ps_var_heap) = newPtr VI_Empty ps.ps_var_heap
		  cs = checkPatternVariable pi_def_level entry id new_info_ptr { cs & cs_symbol_table = cs_symbol_table }
		= (AP_Variable id new_info_ptr opt_var, ([ id : var_env ], array_patterns), { ps & ps_var_heap = ps_var_heap}, e_info, cs)
		# (pattern, ps, e_info, cs) = checkPatternConstructor pi_mod_index is_expr_list entry id opt_var ps e_info { cs & cs_symbol_table = cs_symbol_table }
		= (pattern, accus, ps, e_info, cs)



convertSubPatterns :: [AuxiliaryPattern] Expression Position *(Heap VarInfo) *(Heap ExprInfo) u:[Ptr ExprInfo] *CheckState -> *(!.[FreeVar],!Expression,!Position,!*Heap VarInfo,!*Heap ExprInfo,!u:[Ptr ExprInfo],!*CheckState);
convertSubPatterns [] result_expr pattern_position var_store expr_heap opt_dynamics cs
	= ([], result_expr, pattern_position, var_store, expr_heap, opt_dynamics, cs)
convertSubPatterns [pattern : patterns] result_expr pattern_position var_store expr_heap opt_dynamics cs
	# (var_args, result_expr, pattern_position, var_store, expr_heap, opt_dynamics, cs) 
			= convertSubPatterns patterns result_expr pattern_position var_store expr_heap opt_dynamics cs
	  (var_arg, result_expr, pattern_position, var_store, expr_heap, opt_dynamics, cs)
	  		= convertSubPattern pattern result_expr pattern_position var_store expr_heap opt_dynamics cs
	= ([var_arg : var_args], result_expr, pattern_position, var_store, expr_heap, opt_dynamics, cs)

convertSubPattern :: AuxiliaryPattern Expression Position *(Heap VarInfo) *(Heap ExprInfo) u:[Ptr ExprInfo] *CheckState -> *(!FreeVar,!Expression,!Position,!*Heap VarInfo,!*Heap ExprInfo,!u:[Ptr ExprInfo],!*CheckState);
convertSubPattern (AP_Variable name var_info (Yes {bind_src,bind_dst})) result_expr pattern_position var_store expr_heap opt_dynamics cs
	# (var_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
	  bound_var = { var_name = bind_src, var_info_ptr = bind_dst, var_expr_ptr = var_expr_ptr }
	  free_var = { fv_name = bind_src, fv_info_ptr = bind_dst, fv_def_level = NotALevel, fv_count = 0 }
	  (let_expr, expr_heap)	= buildLetExpression [] [{lb_src = Var bound_var,
	  			lb_dst = { fv_name = name, fv_info_ptr = var_info, fv_def_level = NotALevel, fv_count = 0 },
	  			lb_position = NoPos }] result_expr NoPos expr_heap
	= (free_var, let_expr, pattern_position, var_store, expr_heap, opt_dynamics, cs)
convertSubPattern (AP_Variable name var_info No) result_expr pattern_position var_store expr_heap opt_dynamics cs
	= ({ fv_name = name, fv_info_ptr = var_info, fv_def_level = NotALevel, fv_count = 0 }, result_expr, pattern_position, 
		var_store, expr_heap, opt_dynamics, cs)
convertSubPattern (AP_Algebraic cons_symbol type_index args opt_var) result_expr pattern_position
					var_store expr_heap opt_dynamics cs
	# (var_args, result_expr, pattern_position, var_store, expr_heap, opt_dynamics, cs)
			= convertSubPatterns args result_expr pattern_position var_store expr_heap opt_dynamics cs
	  type_symbol = { glob_module = cons_symbol.glob_module, glob_object = type_index }
	  alg_pattern = { ap_symbol = cons_symbol, ap_vars = var_args, ap_expr = result_expr, ap_position = pattern_position }
	  case_guards = AlgebraicPatterns type_symbol [alg_pattern]
	  ({bind_src,bind_dst}, var_store) = determinePatternVariable opt_var var_store
	  (var_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
	  (case_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
	= ({ fv_name = bind_src, fv_info_ptr = bind_dst, fv_def_level = NotALevel, fv_count = 0 },
		Case { case_expr = Var { var_name = bind_src, var_info_ptr = bind_dst, var_expr_ptr = var_expr_ptr },
				case_guards = case_guards, case_default = No, case_ident = No, case_info_ptr = case_expr_ptr,
				case_default_pos = NoPos },
		NoPos, var_store, expr_heap, opt_dynamics, cs)
convertSubPattern (AP_Basic basic_val opt_var) result_expr pattern_position var_store expr_heap opt_dynamics cs
	# (basic_type, cs) = typeOfBasicValue basic_val cs
	  case_guards = BasicPatterns basic_type [{ bp_value = basic_val, bp_expr = result_expr, bp_position = pattern_position }]
  	  ({bind_src,bind_dst}, var_store) = determinePatternVariable opt_var var_store
	  (var_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
	  (case_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
	= ({ fv_name = bind_src, fv_info_ptr = bind_dst, fv_def_level = NotALevel, fv_count = 0 },
		Case { case_expr = Var { var_name = bind_src, var_info_ptr = bind_dst, var_expr_ptr = var_expr_ptr },
			  case_guards = case_guards, case_default = No, case_ident = No, case_info_ptr = case_expr_ptr,
			  case_default_pos = NoPos},
		NoPos, var_store, expr_heap, opt_dynamics, cs)
convertSubPattern (AP_Dynamic pattern type opt_var) result_expr pattern_position var_store expr_heap opt_dynamics cs
	# (var_arg, result_expr, pattern_position, var_store, expr_heap, opt_dynamics, cs)
			= convertSubPattern pattern result_expr pattern_position var_store expr_heap opt_dynamics cs
 	  ({bind_src,bind_dst}, var_store) = determinePatternVariable opt_var var_store
	  (var_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
	  (type_case_info_ptr, expr_heap) = newPtr EI_Empty expr_heap
	  (dynamic_info_ptr, expr_heap) = newPtr (EI_DynamicType type opt_dynamics) expr_heap
 	  type_case_patterns = [{ dp_var = var_arg, dp_type = dynamic_info_ptr, dp_rhs = result_expr, dp_type_patterns_vars = [],
 	  						dp_type_code = TCE_Empty, dp_position = pattern_position }]
	= ({ fv_name = bind_src, fv_info_ptr = bind_dst, fv_def_level = NotALevel, fv_count = 0 },
		buildTypeCase (Var { var_name = bind_src, var_info_ptr = bind_dst, var_expr_ptr = var_expr_ptr }) 
							type_case_patterns No type_case_info_ptr,
		NoPos, var_store, expr_heap, [dynamic_info_ptr], cs)
convertSubPattern (AP_WildCard opt_var) result_expr pattern_position var_store expr_heap opt_dynamics cs
 	# ({bind_src,bind_dst}, var_store) = determinePatternVariable opt_var var_store
	= ({ fv_name = bind_src, fv_info_ptr = bind_dst, fv_def_level = NotALevel, fv_count = 0  }, result_expr, pattern_position,
		var_store, expr_heap, opt_dynamics, cs)
convertSubPattern (AP_Empty _) result_expr pattern_position var_store expr_heap opt_dynamics cs
	= convertSubPattern (AP_WildCard No) EE pattern_position var_store expr_heap opt_dynamics cs


checkAndTransformPatternIntoBind free_vars [{nd_dst,nd_alts,nd_locals,nd_position} : local_defs] e_input=:{ei_expr_level,ei_mod_index} e_state e_info cs
	# cs = pushErrorAdmin (newPosition {id_name="node definition", id_info=nilPtr} nd_position) cs
	# (bind_src, free_vars, e_state, e_info, cs) = checkRhs free_vars nd_alts nd_locals e_input e_state e_info cs	
	  (binds_of_bind, es_var_heap, es_expr_heap, e_info, cs)
			= transfromPatternIntoBind ei_mod_index ei_expr_level nd_dst bind_src nd_position
				e_state.es_var_heap e_state.es_expr_heap e_info cs
	  e_state = { e_state & es_var_heap = es_var_heap, es_expr_heap = es_expr_heap }
	  (binds_of_local_defs, free_vars, e_state, e_info, cs) = checkAndTransformPatternIntoBind free_vars local_defs e_input e_state e_info cs
	= (binds_of_bind ++ binds_of_local_defs, free_vars, e_state, e_info, popErrorAdmin cs)
checkAndTransformPatternIntoBind free_vars [] e_input e_state e_info cs
	= ([], free_vars, e_state, e_info, cs)



transfromPatternIntoBind :: !Index !Level !AuxiliaryPattern !Expression !Position !*VarHeap !*ExpressionHeap !*ExpressionInfo !*CheckState
	-> *(![LetBind], !*VarHeap, !*ExpressionHeap,  !*ExpressionInfo, !*CheckState)
transfromPatternIntoBind mod_index def_level (AP_Variable name var_info _) src_expr position var_store expr_heap e_info cs
	# bind = {lb_src = src_expr, lb_dst = { fv_name = name, fv_info_ptr = var_info, fv_def_level = def_level, fv_count = 0 }, lb_position = position }
	= ([bind], var_store, expr_heap, e_info, cs)
transfromPatternIntoBind mod_index def_level (AP_Algebraic cons_symbol=:{glob_module,glob_object=ds_cons=:{ds_arity, ds_index, ds_ident}} type_index args opt_var)
		src_expr position var_store expr_heap e_info=:{ef_type_defs,ef_modules} cs
	# (src_expr, opt_var_bind, var_store, expr_heap) = bind_opt_var opt_var src_expr position var_store expr_heap
	| ds_arity == 0
		= ([], var_store, expr_heap, e_info, { cs & cs_error = checkError ds_ident " constant not allowed in a node pattern" cs.cs_error})
	# (is_tuple, cs) = is_tuple_symbol glob_module ds_index cs
	| is_tuple
		# (tuple_var, tuple_bind, var_store, expr_heap) = bind_match_expr src_expr opt_var_bind position var_store expr_heap
		= transform_sub_patterns mod_index def_level args ds_cons 0 tuple_var tuple_bind position var_store expr_heap e_info cs
		# ({td_rhs}, ef_type_defs, ef_modules) = get_type_def mod_index glob_module type_index ef_type_defs ef_modules
		  e_info = { e_info & ef_type_defs = ef_type_defs, ef_modules = ef_modules }
		= case td_rhs of
			RecordType {rt_fields}
				| size rt_fields == 1
					-> transform_sub_patterns_of_record mod_index def_level args rt_fields glob_module 0
							src_expr opt_var_bind position var_store expr_heap e_info cs
					# (record_var, record_bind, var_store, expr_heap)
						= bind_match_expr src_expr opt_var_bind position var_store expr_heap
					-> transform_sub_patterns_of_record mod_index def_level args rt_fields glob_module 0
							record_var record_bind position var_store expr_heap e_info cs
			_
				| ds_arity == 1
		  			# (binds, var_store, expr_heap, e_info, cs)
						= transfromPatternIntoBind mod_index def_level (hd args) (MatchExpr No cons_symbol src_expr)
								position var_store expr_heap e_info cs
					-> (opt_var_bind ++ binds, var_store, expr_heap, e_info, cs)
					# (tuple_type, cs) = getPredefinedGlobalSymbol (GetTupleTypeIndex ds_arity) PD_PredefinedModule STE_Type ds_arity cs
					  (tuple_cons, cs) = getPredefinedGlobalSymbol (GetTupleConsIndex ds_arity) PD_PredefinedModule STE_Constructor ds_arity cs
					  (match_var, match_bind, var_store, expr_heap)
						=  bind_match_expr (MatchExpr (Yes tuple_type) cons_symbol src_expr) opt_var_bind position var_store expr_heap
					-> transform_sub_patterns mod_index def_level args tuple_cons.glob_object 0 match_var match_bind
							position var_store expr_heap e_info cs
where
	get_type_def mod_index type_mod_index type_index ef_type_defs ef_modules
		| mod_index == type_mod_index
			# (type_def, ef_type_defs) = ef_type_defs![type_index]
			= (type_def, ef_type_defs, ef_modules)
			# ({dcl_common},  ef_modules) = ef_modules![type_mod_index]
			= (dcl_common.com_type_defs.[type_index], ef_type_defs, ef_modules)
		
	is_tuple_symbol cons_module cons_index cs
		# (tuple_2_symbol, cs) = getPredefinedGlobalSymbol (GetTupleConsIndex 2) PD_PredefinedModule STE_Constructor 2 cs
		= (tuple_2_symbol.glob_module == cons_module &&
		   tuple_2_symbol.glob_object.ds_index <= cons_index && cons_index <= tuple_2_symbol.glob_object.ds_index + 30, cs)

	transform_sub_patterns mod_index def_level [pattern : patterns] tup_id tup_index arg_var all_binds position var_store expr_heap e_info cs
		# (this_arg_var, expr_heap)
				= adjust_match_expression arg_var expr_heap
		  match_expr
		  		= TupleSelect tup_id tup_index this_arg_var
		  (binds, var_store, expr_heap, e_info, cs)
		  		= transfromPatternIntoBind mod_index def_level pattern match_expr position var_store expr_heap e_info cs
		= transform_sub_patterns mod_index def_level patterns tup_id (inc tup_index) arg_var (binds ++ all_binds)
				position var_store expr_heap e_info cs
	transform_sub_patterns mod_index _ [] _ _ _ binds _ var_store expr_heap e_info cs
		= (binds, var_store, expr_heap, e_info, cs)

	transform_sub_patterns_of_record mod_index def_level [pattern : patterns] fields field_module field_index record_expr
			all_binds position var_store expr_heap e_info cs
		# {fs_name, fs_index} = fields.[field_index]
		  selector = { glob_module = field_module, glob_object = MakeDefinedSymbol fs_name fs_index 1}
		  (this_record_expr, expr_heap) = adjust_match_expression record_expr expr_heap
		  (binds, var_store, expr_heap, e_info, cs)
				= transfromPatternIntoBind mod_index def_level pattern (Selection No this_record_expr [ RecordSelection selector field_index ])
						position var_store expr_heap e_info cs
		= transform_sub_patterns_of_record mod_index def_level patterns fields field_module (inc field_index) record_expr
				(binds ++ all_binds) position var_store expr_heap e_info cs
	transform_sub_patterns_of_record mod_index _ [] _ _ _ _ binds _ var_store expr_heap e_info cs
		= (binds, var_store, expr_heap, e_info, cs)

	bind_opt_var (Yes {bind_src,bind_dst}) src_expr position var_heap expr_heap
		# free_var = { fv_name = bind_src, fv_info_ptr = bind_dst, fv_def_level = NotALevel, fv_count = 0 }
		  (var_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
		  bound_var = { var_name = bind_src, var_info_ptr = bind_dst, var_expr_ptr = var_expr_ptr }
		= (Var bound_var, [{lb_src = src_expr, lb_dst = free_var, lb_position = position}], var_heap <:= (bind_dst, VI_Empty), expr_heap)
	bind_opt_var No src_expr _ var_heap expr_heap
		= (src_expr, [], var_heap, expr_heap)
		
	bind_match_expr var_expr=:(Var var) opt_var_bind _ var_heap expr_heap
		= (var_expr, opt_var_bind, var_heap, expr_heap)
	bind_match_expr match_expr opt_var_bind position var_heap expr_heap
		# new_name = newVarId "_x"
		  (var_info_ptr, var_heap) = newPtr VI_Empty var_heap
//		  (var_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
		  bound_var = { var_name = new_name, var_info_ptr = var_info_ptr, var_expr_ptr = nilPtr }
		  free_var = { fv_name = new_name, fv_info_ptr = var_info_ptr, fv_def_level = def_level, fv_count = 0 }
		= (Var bound_var, [{lb_src = match_expr, lb_dst = free_var, lb_position = position } : opt_var_bind], var_heap, expr_heap)

	adjust_match_expression (Var var) expr_heap
		# (var_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
		= (Var { var & var_expr_ptr = var_expr_ptr }, expr_heap)
	adjust_match_expression match_expr expr_heap
		= (match_expr, expr_heap)
transfromPatternIntoBind mod_index def_level (AP_WildCard _) src_expr _ var_store expr_heap e_info cs
	= ([], var_store, expr_heap, e_info, cs)
transfromPatternIntoBind _ _ pattern src_expr _ var_store expr_heap e_info cs
	= ([], var_store, expr_heap, e_info, { cs & cs_error = checkError "<pattern>" " illegal node pattern" cs.cs_error})



unfoldPatternMacro mod_index macro_index macro_args opt_var ps=:{ps_var_heap, ps_fun_defs} modules cons_defs error
	# (macro, ps_fun_defs) = ps_fun_defs![macro_index]
	= case macro.fun_body of
		TransformedBody {tb_args,tb_rhs}
			| no_sharing tb_args
				# ums = { ums_var_heap = fold2St bind_var tb_args macro_args ps_var_heap, ums_modules = modules, ums_cons_defs = cons_defs, ums_error = error }
				  (pattern, {ums_var_heap,ums_modules,ums_cons_defs,ums_error}) = unfold_pattern_macro mod_index macro.fun_symb opt_var tb_rhs ums
				-> (pattern, { ps_fun_defs = ps_fun_defs, ps_var_heap = ums_var_heap}, ums_modules, ums_cons_defs, ums_error)
				-> (AP_Empty macro.fun_symb, { ps_fun_defs = ps_fun_defs, ps_var_heap = ps_var_heap},
						modules, cons_defs, checkError macro.fun_symb " sharing not allowed" error)
		_
			-> (AP_Empty macro.fun_symb, { ps_fun_defs = ps_fun_defs, ps_var_heap = ps_var_heap},
					modules, cons_defs, checkError macro.fun_symb " illegal macro in pattern" error)
	
where
	no_sharing [{fv_count} : args]
		= fv_count <= 1 && no_sharing args
	no_sharing []
		= True
	
	bind_var {fv_info_ptr} pattern ps_var_heap
		= ps_var_heap <:= (fv_info_ptr, VI_Pattern pattern)

	unfold_pattern_macro mod_index macro_ident _ (Var {var_name,var_info_ptr}) ums=:{ums_var_heap}
		# (VI_Pattern pattern, ums_var_heap) = readPtr var_info_ptr ums_var_heap
		= (pattern, { ums & ums_var_heap = ums_var_heap})
	unfold_pattern_macro mod_index macro_ident opt_var (App {app_symb,app_args}) ums
		= unfold_application  mod_index macro_ident opt_var app_symb app_args ums
	where
		unfold_application  mod_index macro_ident opt_var {symb_kind=SK_Constructor {glob_module,glob_object},symb_name,symb_arity} args 
										ums=:{ums_cons_defs, ums_modules,ums_error}
				# (cons_def, cons_index, ums_cons_defs, ums_modules) = get_cons_def mod_index glob_module glob_object ums_cons_defs ums_modules
				| cons_def.cons_type.st_arity == symb_arity
					# (patterns, ums) = mapSt (unfold_pattern_macro mod_index macro_ident No) app_args { ums & ums_cons_defs = ums_cons_defs, ums_modules = ums_modules }
					  cons_symbol = { glob_object = MakeDefinedSymbol symb_name cons_index symb_arity, glob_module = glob_module }	
					= (AP_Algebraic cons_symbol cons_def.cons_type_index patterns opt_var, ums)	
					= (AP_Empty cons_def.cons_symb, { ums & ums_cons_defs = ums_cons_defs, ums_modules = ums_modules,
							ums_error = checkError cons_def.cons_symb " missing argument(s)" ums_error })

		get_cons_def mod_index cons_mod cons_index cons_defs modules
			| mod_index == cons_mod
				# (cons_def, cons_defs) = cons_defs![cons_index]
				= (cons_def, cons_index, cons_defs, modules)
				# ({dcl_common,dcl_conversions}, modules) = modules![cons_mod]
				  cons_def = dcl_common.com_cons_defs.[cons_index]
				= (cons_def, convertIndex cons_index (toInt STE_Constructor) dcl_conversions, cons_defs, modules)

	unfold_pattern_macro mod_index macro_ident opt_var (BasicExpr bv bt) ums
		= (AP_Basic bv opt_var, ums)
	unfold_pattern_macro mod_index macro_ident opt_var expr ums=:{ums_error}
		= (AP_Empty macro_ident, { ums & ums_error = checkError macro_ident " illegal rhs for a pattern macro" ums_error })
	
	
			
checkSelectors end_with_update free_vars [ selector : selectors ] e_input e_state e_info cs
	| isEmpty selectors
		# (selector, free_vars, e_state, e_info, cs) = check_selector end_with_update free_vars selector e_input e_state e_info cs
		= ([ selector ], free_vars, e_state, e_info, cs)
		# (selector, free_vars, e_state, e_info, cs) = check_selector cEndWithSelection free_vars selector e_input e_state e_info cs
		  (selectors, free_vars, e_state, e_info, cs) = checkSelectors end_with_update free_vars selectors e_input e_state e_info cs
		= ([ selector : selectors ], free_vars, e_state, e_info, cs)
where		
	check_selector _ free_vars (PS_Record selector=:{id_info,id_name} opt_type) e_input=:{ei_mod_index} e_state
			e_info=:{ef_selector_defs, ef_modules} cs=:{cs_symbol_table}
		# (entry, cs_symbol_table) = readPtr id_info cs_symbol_table
		# selectors = retrieveSelectorIndexes ei_mod_index entry 
		  (field_module, field_index, field_nr, ef_selector_defs, ef_modules, cs)
		  		= get_field_nr ei_mod_index selector opt_type selectors ef_selector_defs ef_modules { cs & cs_symbol_table = cs_symbol_table }
		= (RecordSelection { glob_object = MakeDefinedSymbol selector field_index 1, glob_module = field_module } field_nr, free_vars, e_state,
								{e_info & ef_selector_defs = ef_selector_defs, ef_modules = ef_modules }, cs)
	where					
		get_field_nr :: !Index !Ident !(Optional Ident) ![Global Index] !u:{#SelectorDef} !v:{# DclModule} !*CheckState
				-> (!Index, !Index, !Index, u:{#SelectorDef}, v:{#DclModule}, !*CheckState)
		get_field_nr mod_index sel_id _ [] selector_defs modules cs=:{cs_error}
			= (NoIndex, NoIndex, NoIndex, selector_defs, modules, { cs & cs_error = checkError id_name " selector not defined" cs_error })
		get_field_nr mod_index sel_id (Yes type_id=:{id_info}) selectors selector_defs modules cs=:{cs_symbol_table,cs_error}
			# (entry, cs_symbol_table) = readPtr id_info cs_symbol_table
			# (type_index, type_module) = retrieveGlobalDefinition entry STE_Type mod_index
			| type_index <> NotFound
				# (selector_index, selector_offset, selector_defs, modules)
						= determine_selector mod_index type_module type_index selectors selector_defs modules
				| selector_offset <> NoIndex
					= (type_module, selector_index, selector_offset, selector_defs, modules, { cs & cs_symbol_table = cs_symbol_table })
					= (NoIndex, NoIndex, NoIndex, selector_defs, modules, { cs & cs_symbol_table = cs_symbol_table,
								cs_error = checkError id_name " selector not defined" cs_error })
				= (NoIndex, NoIndex, NoIndex, selector_defs, modules, { cs & cs_symbol_table = cs_symbol_table,
						cs_error = checkError type_id " type not defined" cs_error })
		get_field_nr mod_index sel_id No [{glob_object,glob_module}] selector_defs modules cs
			| mod_index == glob_module
				# (selector_offset,selector_defs) = selector_defs![glob_object].sd_field_nr
				= (glob_module, glob_object, selector_offset, selector_defs, modules, cs)
				# (selector_offset,modules) = modules![glob_module].dcl_common.com_selector_defs.[glob_object].sd_field_nr
				= (glob_module, glob_object, selector_offset, selector_defs, modules, cs)
		get_field_nr mod_index sel_id No _  selector_defs modules cs=:{cs_error}
			= (NoIndex, NoIndex, NoIndex, selector_defs, modules, { cs & cs_error = checkError sel_id " ambiguous selector specified" cs_error })

		determine_selector :: !Index !Index !Index ![Global Index] !u:{# SelectorDef} !v:{# DclModule} -> (!Int, !Int, !u:{# SelectorDef}, !v:{# DclModule})
		determine_selector mod_index type_mod_index type_index [] selector_defs modules
			= (NoIndex, NoIndex, selector_defs, modules)
		determine_selector mod_index type_mod_index type_index [{glob_module, glob_object} : selectors] selector_defs modules
			| type_mod_index == glob_module
				| type_mod_index == mod_index
					#! selector_def = selector_defs.[glob_object]
					| selector_def.sd_type_index == type_index
						= (glob_object, selector_def.sd_field_nr, selector_defs, modules)
						= determine_selector mod_index type_mod_index type_index selectors selector_defs modules
					#! {dcl_common={com_selector_defs}} = modules.[glob_module]
					#! selector_def = com_selector_defs.[glob_object]
					| selector_def.sd_type_index == type_index
						= (glob_object, selector_def.sd_field_nr, selector_defs, modules)
						= determine_selector mod_index type_mod_index type_index selectors selector_defs modules
				= determine_selector mod_index type_mod_index type_index selectors selector_defs modules

	check_selector end_with_update free_vars (PS_Array index_expr) e_input e_state e_info cs
		| end_with_update
			# (glob_select_symb, cs) = getPredefinedGlobalSymbol PD_ArrayUpdateFun PD_StdArray STE_Member 3 cs
			= checkArraySelection glob_select_symb free_vars index_expr e_input e_state e_info cs
			# (glob_select_symb, cs) = getPredefinedGlobalSymbol PD_ArraySelectFun PD_StdArray STE_Member 2 cs
			= checkArraySelection glob_select_symb free_vars index_expr e_input e_state e_info cs



checkArraySelection glob_select_symb free_vars index_expr e_input e_state e_info cs
	# (index_expr, free_vars, e_state, e_info, cs) = checkExpression free_vars index_expr e_input e_state e_info cs
	  (new_info_ptr, es_expr_heap) = newPtr EI_Empty e_state.es_expr_heap
	= (ArraySelection glob_select_symb new_info_ptr index_expr, free_vars, { e_state & es_expr_heap = es_expr_heap }, e_info, cs)



checkFields :: !Index ![FieldAssignment] !(Optional Ident) !u:ExpressionInfo !*CheckState
	-> (!Optional ((Global DefinedSymbol), Index, [Bind ParsedExpr (Global FieldSymbol)]), !u:ExpressionInfo, !*CheckState)
checkFields mod_index field_ass opt_type e_info=:{ef_selector_defs,ef_type_defs,ef_modules} cs
	# (ok, field_ass, cs) = check_fields field_ass cs
	| ok
		# (opt_type_def, ef_selector_defs, ef_type_defs, ef_modules, cs)
				= determine_record_type mod_index opt_type field_ass ef_selector_defs ef_type_defs ef_modules cs
		  e_info = { e_info & ef_selector_defs = ef_selector_defs, ef_type_defs = ef_type_defs, ef_modules = ef_modules}
		= case opt_type_def of
			Yes ({td_index,td_rhs = RecordType {rt_constructor,rt_fields}}, type_mod_index)
				# (field_exprs, cs_error) = check_and_rearrange_fields type_mod_index 0 rt_fields field_ass cs.cs_error
				-> (Yes ({ glob_object = rt_constructor, glob_module = type_mod_index }, td_index, field_exprs), e_info, { cs & cs_error = cs_error })
			Yes _
				# (Yes type_ident) = opt_type
				-> (No, e_info, { cs & cs_error = checkError type_ident "not a record constructor" cs.cs_error })
			No
				-> (No, e_info, cs)
		= (No, e_info, cs)
where
	check_fields [ bind=:{bind_dst} : field_ass ] cs=:{cs_symbol_table,cs_error}
		# (entry, cs_symbol_table) = readPtr bind_dst.id_info cs_symbol_table
		# fields = retrieveSelectorIndexes mod_index entry 
		| isEmpty fields
			= (False, [], { cs & cs_symbol_table = cs_symbol_table, cs_error = checkError bind_dst "not defined as a record field" cs_error })
			# (ok, field_ass, cs) = check_fields field_ass { cs & cs_symbol_table = cs_symbol_table }
			= (ok, [{bind & bind_dst = (bind_dst, fields)} : field_ass], cs)
	check_fields [] cs
		= (True, [], cs)

	try_to_get_unique_field []
		= No
	try_to_get_unique_field [ {bind_dst = (field_id, [field])} : fields ]
		= Yes field
	try_to_get_unique_field [ _ : fields ]
		= try_to_get_unique_field fields
	
	determine_record_type mod_index (Yes type_id=:{id_info}) _ selector_defs type_defs modules cs=:{cs_symbol_table, cs_error}
		# (entry, cs_symbol_table) = readPtr id_info cs_symbol_table
		# (type_index, type_mod_index) = retrieveGlobalDefinition entry STE_Type mod_index
		| type_index <> NotFound
			| mod_index == type_mod_index
			 	# (type_def, type_defs) = type_defs![type_index]
			 	= (Yes (type_def, type_mod_index), selector_defs, type_defs, modules, { cs & cs_symbol_table = cs_symbol_table })
				# (type_def, modules) = modules![type_mod_index].dcl_common.com_type_defs.[type_index]
				= (Yes (type_def, type_mod_index), selector_defs, type_defs, modules, { cs & cs_symbol_table = cs_symbol_table })
			= (No, selector_defs, type_defs, modules, { cs & cs_error = checkError type_id " not defined" cs_error, cs_symbol_table = cs_symbol_table})
	determine_record_type mod_index No fields selector_defs type_defs modules cs=:{cs_error}
		# succ = try_to_get_unique_field fields
		= case succ of
			Yes {glob_module, glob_object}
				| glob_module == mod_index
					# (selector_def, selector_defs) = selector_defs![glob_object]
					  (type_def, type_defs) = type_defs![selector_def.sd_type_index]
					-> (Yes (type_def, glob_module), selector_defs, type_defs, modules, cs)
					# ({dcl_common={com_selector_defs,com_type_defs}}, modules) = modules![glob_module]
					  {sd_type_index} = com_selector_defs.[glob_object]
					  type_def = com_type_defs.[sd_type_index]
					-> (Yes (type_def,glob_module), selector_defs, type_defs, modules, cs)
			No
				-> (No, selector_defs, type_defs, modules, { cs & cs_error = checkError "" " could not determine the type of this record" cs.cs_error })

	check_and_rearrange_fields :: !Int !Int !{#FieldSymbol} ![Bind ParsedExpr (Ident,[Global .Int])] !*ErrorAdmin -> (![Bind ParsedExpr .(Global FieldSymbol)],!.ErrorAdmin);
	check_and_rearrange_fields mod_index field_index fields field_ass cs_error
		| field_index < size fields
			# (field_expr, field_ass) = look_up_field mod_index fields.[field_index] field_ass
		 	  (field_exprs, cs_error) = check_and_rearrange_fields mod_index (inc field_index) fields field_ass cs_error
			= ([field_expr : field_exprs], cs_error)
		| isEmpty field_ass
			= ([], cs_error)
			= ([], foldSt field_error field_ass cs_error)

	where			
		look_up_field mod_index field []
			= ({bind_src = PE_WildCard,  bind_dst = { glob_object = field, glob_module = mod_index }}, [])
		look_up_field mod_index field=:{fs_index} [ass=:{bind_src, bind_dst = (_, fields)} : field_ass]
			| field_list_contains_field mod_index fs_index fields
				= ({bind_src = bind_src, bind_dst = { glob_module = mod_index, glob_object = field}}, field_ass)
				# (field_expr, field_ass) = look_up_field mod_index field field_ass
				= (field_expr, [ass : field_ass])

		field_list_contains_field mod_index fs_index []
			= False
		field_list_contains_field mod_index fs_index [{glob_object,glob_module} : fields]
			= mod_index == glob_module && fs_index == glob_object || field_list_contains_field mod_index fs_index fields

		field_error {bind_dst=(field_id,_)} error
			= checkError field_id " field is either multiply used or not a part of this record" error



checkRhssAndTransformLocalDefs free_vars [] rhs_expr e_input e_state e_info cs
	= (rhs_expr, free_vars, e_state, e_info, cs)
checkRhssAndTransformLocalDefs free_vars loc_defs rhs_expr e_input e_state e_info cs
	# (binds, free_vars, e_state, e_info, cs) = checkAndTransformPatternIntoBind free_vars loc_defs e_input e_state e_info cs
	  (rhs_expr, es_expr_heap) = buildLetExpression [] binds rhs_expr NoPos e_state.es_expr_heap
	= (rhs_expr, free_vars, { e_state & es_expr_heap = es_expr_heap }, e_info, cs)

checkLhssOfLocalDefs :: .Int .Int LocalDefs *ExpressionState *ExpressionInfo *CheckState -> (!.[NodeDef AuxiliaryPattern],!(![Ident],![ArrayPattern]),!.ExpressionState,!.ExpressionInfo,!.CheckState);
checkLhssOfLocalDefs def_level mod_index (CollectedLocalDefs {loc_functions={ir_from,ir_to},loc_nodes}) e_state=:{es_var_heap,es_fun_defs} e_info=:{ef_is_macro_fun} cs
	# (loc_defs, accus, {ps_fun_defs,ps_var_heap}, e_info, cs)
			= check_patterns loc_nodes {pi_def_level = def_level, pi_mod_index = mod_index, pi_is_node_pattern = True } ([], [])
					{ps_fun_defs = es_fun_defs, ps_var_heap = es_var_heap} e_info cs
	  (es_fun_defs, cs_symbol_table, cs_error) = addLocalFunctionDefsToSymbolTable def_level ir_from ir_to ef_is_macro_fun ps_fun_defs cs.cs_symbol_table cs.cs_error
	= (loc_defs, accus, { e_state & es_fun_defs = es_fun_defs, es_var_heap = ps_var_heap }, e_info, { cs & cs_symbol_table = cs_symbol_table, cs_error = cs_error })
where
	check_patterns [ (_,node_def) : node_defs ] p_input accus var_store e_info cs
		# (pattern, accus, var_store, e_info, cs) = checkPattern node_def.nd_dst No p_input accus var_store e_info cs
		  (patterns, accus, var_store, e_info, cs) = check_patterns node_defs p_input accus var_store e_info cs
		= ([{ node_def & nd_dst = pattern } : patterns], accus, var_store, e_info, cs)
	check_patterns [] p_input accus var_store e_info cs
		= ([], accus, var_store, e_info, cs)

addArraySelections [] rhs_expr free_vars e_input e_state e_info cs
	= (rhs_expr, free_vars, e_state, e_info, cs)
addArraySelections array_patterns rhs_expr free_vars e_input e_state e_info cs
	# (let_strict_binds, let_lazy_binds, free_vars, e_state, e_info, cs)
			= foldSt (buildSelections e_input) array_patterns ([], [], free_vars, e_state, e_info, cs)
	  (let_expr_ptr, es_expr_heap)
	  		= newPtr EI_Empty e_state.es_expr_heap
	= ( Let {let_strict_binds = let_strict_binds, let_lazy_binds = let_lazy_binds,
				let_expr = rhs_expr, let_info_ptr = let_expr_ptr, let_expr_position = NoPos }
	  , free_vars
	  , { e_state & es_expr_heap = es_expr_heap}
	  , e_info
	  , cs
	  )



buildSelections e_input {ap_opt_var, ap_array_var, ap_selections}
					(strict_binds, lazy_binds, free_vars, e_state, e_info, cs)
	# (ap_array_var, [last_array_selection:lazy_binds], free_vars, e_state, e_info, cs)
			= foldSt (build_sc e_input) (reverse ap_selections) // reverse to make cycle-in-spine behaviour compatible to Clean 1.3
						(ap_array_var, lazy_binds, free_vars, e_state, e_info, cs)
	  (lazy_binds, e_state)
	  		= case ap_opt_var of
	  			Yes { bind_src = opt_var_ident, bind_dst = opt_var_var_info_ptr }
					# (bound_array_var, es_expr_heap) = allocate_bound_var ap_array_var e_state.es_expr_heap
					  free_var = { fv_name = opt_var_ident, fv_info_ptr = opt_var_var_info_ptr, fv_def_level = NotALevel,
					  				fv_count = 0 }
	  				-> ([{ lb_dst = free_var, lb_src = Var bound_array_var, lb_position = NoPos }: lazy_binds],
	  					{ e_state & es_expr_heap = es_expr_heap })
	  			no	-> (lazy_binds, e_state)
	= ([last_array_selection:strict_binds], lazy_binds, free_vars, e_state, e_info, cs)
  where
	build_sc e_input {bind_dst=parsed_index_exprs, bind_src=array_element_var} (ap_array_var, binds, free_vars, e_state, e_info, cs)
		# (var_for_uselect_result, es_var_heap)
				= allocate_free_var { id_name = "_x", id_info = nilPtr } e_state.es_var_heap
		  (new_array_var, es_var_heap)
		  		= allocate_free_var ap_array_var.fv_name es_var_heap
		  (bound_array_var, es_expr_heap)
		  		= allocate_bound_var ap_array_var e_state.es_expr_heap
		  (bound_var_for_uselect_result, es_expr_heap)
		  		= allocate_bound_var var_for_uselect_result es_expr_heap
		  dimension
		  		= length parsed_index_exprs
		  (new_expr_ptrs, es_expr_heap)
		  		= mapSt newPtr (repeatn dimension EI_Empty) es_expr_heap
		  (tuple_cons, cs)
		  		= getPredefinedGlobalSymbol (GetTupleConsIndex 2) PD_PredefinedModule STE_Constructor 2 cs
		  (glob_select_symb, opt_tuple_type, cs)
		  		= case dimension of
		  			1	# (unq_select_symb, cs) = getPredefinedGlobalSymbol PD_UnqArraySelectFun PD_StdArray STE_Member 2 cs
		  				-> (unq_select_symb, No, cs)
		  			_	# (select_symb, cs) = getPredefinedGlobalSymbol PD_ArraySelectFun PD_StdArray STE_Member 2 cs
						  (tuple_type, cs) = getPredefinedGlobalSymbol (GetTupleTypeIndex 2) PD_PredefinedModule STE_Type 2 cs
		  				-> (select_symb, Yes tuple_type, cs)
		  e_state
		  		= { e_state & es_var_heap = es_var_heap, es_expr_heap = es_expr_heap }
		  (index_exprs, (free_vars, e_state, e_info, cs))
		  		= mapSt (check_index_expr e_input) parsed_index_exprs (free_vars, e_state, e_info, cs)
		  selections
		  		= [ ArraySelection glob_select_symb new_expr_ptr index_expr \\ new_expr_ptr<-new_expr_ptrs & index_expr<-index_exprs ]
		= (	new_array_var
		  ,	[ {lb_dst = var_for_uselect_result, lb_src = Selection opt_tuple_type (Var bound_array_var) selections, lb_position = NoPos }
		    , {lb_dst = new_array_var, lb_src = TupleSelect tuple_cons.glob_object 1 (Var bound_var_for_uselect_result), lb_position = NoPos }
		    , {lb_dst = array_element_var, lb_src = TupleSelect tuple_cons.glob_object 0 (Var bound_var_for_uselect_result), lb_position = NoPos }
		  	: binds
			]
		  , free_vars
		  , e_state
		  , e_info 
		  , cs
		  )

	check_index_expr e_input parsed_index_expr (free_vars, e_state, e_info, cs)
		# (index_expr, free_vars, e_state, e_info, cs) = checkExpression free_vars parsed_index_expr e_input e_state e_info cs
		= (index_expr, (free_vars, e_state, e_info, cs))
		


buildLetExpression :: ![LetBind] ![LetBind] !Expression !Position !*ExpressionHeap  -> (!Expression, !*ExpressionHeap)
buildLetExpression [] [] expr _ expr_heap
	= (expr, expr_heap)
buildLetExpression let_strict_binds let_lazy_binds expr let_expr_position expr_heap
	# (let_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
	= (Let {let_strict_binds = let_strict_binds, let_lazy_binds = let_lazy_binds, let_expr = expr,
			let_info_ptr = let_expr_ptr, let_expr_position = let_expr_position }, expr_heap)



buildApplication :: !SymbIdent !Int !Int !Bool ![Expression] !*ExpressionState !*ErrorAdmin -> (!Expression,!*ExpressionState,!*ErrorAdmin)
buildApplication symbol form_arity act_arity is_fun args e_state=:{es_expr_heap} error
	| is_fun
		# (new_info_ptr, es_expr_heap) = newPtr EI_Empty es_expr_heap
		| form_arity < act_arity
			# app = { app_symb = { symbol & symb_arity = form_arity }, app_args = take form_arity args, app_info_ptr = new_info_ptr }
			= (App app @ drop form_arity args, { e_state & es_expr_heap = es_expr_heap }, error)
			# app = { app_symb = { symbol & symb_arity = act_arity }, app_args = take form_arity args, app_info_ptr = new_info_ptr }
			= (App app, { e_state & es_expr_heap = es_expr_heap }, error)
		# app = App { app_symb = { symbol & symb_arity = act_arity }, app_args = args, app_info_ptr = nilPtr }
		| form_arity < act_arity
			= (app, e_state, checkError symbol.symb_name " used with too many arguments" error)
			= (app, e_state, error)



buildPattern mod_index (APK_Constructor type_index) cons_symb args opt_var ps e_info cs
	= (AP_Algebraic cons_symb type_index args opt_var, ps, e_info, cs)
buildPattern mod_index APK_Macro {glob_object} args opt_var ps e_info=:{ef_modules,ef_cons_defs} cs=:{cs_error}
	# (pattern, ps, ef_modules, ef_cons_defs, cs_error)
			= unfoldPatternMacro mod_index glob_object.ds_index args opt_var ps ef_modules ef_cons_defs cs_error
	= (pattern, ps, { e_info & ef_modules = ef_modules, ef_cons_defs = ef_cons_defs }, { cs & cs_error = cs_error })



//////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////

getPredefinedGlobalSymbol :: !Index !Index !STE_Kind !Int !*CheckState -> (!Global DefinedSymbol, !*CheckState)
getPredefinedGlobalSymbol symb_index module_index req_ste_kind arity cs=:{cs_predef_symbols,cs_symbol_table}
	# (pre_def_mod, cs_predef_symbols)	= cs_predef_symbols![module_index]
	# mod_id							= pre_def_mod.pds_ident
	# (mod_entry, cs_symbol_table)		= readPtr mod_id.id_info cs_symbol_table
	| mod_entry.ste_kind == STE_ClosedModule
		# (glob_object, cs) = get_predefined_symbol symb_index req_ste_kind arity mod_entry.ste_index
										{ cs & cs_predef_symbols = cs_predef_symbols, cs_symbol_table = cs_symbol_table}
		= ({ glob_object = glob_object, glob_module = mod_entry.ste_index }, cs)
		= ({ glob_object = { ds_ident = { id_name = "** ERRONEOUS **", id_info = nilPtr }, ds_index = NoIndex, ds_arity = arity }, glob_module = NoIndex},
				  		{ cs & cs_error = checkError mod_id "not imported" cs.cs_error, cs_predef_symbols = cs_predef_symbols, cs_symbol_table = cs_symbol_table })
where
	get_predefined_symbol :: !Index !STE_Kind !Int !Index !*CheckState -> (!DefinedSymbol,!*CheckState)
	get_predefined_symbol symb_index req_ste_kind arity mod_index cs=:{cs_predef_symbols,cs_symbol_table,cs_error}
		# (pre_def_symb, cs_predef_symbols)	= cs_predef_symbols![symb_index]
		  symb_id							= pre_def_symb.pds_ident
		  (symb_entry, cs_symbol_table) 	= readPtr symb_id.id_info cs_symbol_table
		  cs = { cs & cs_predef_symbols = cs_predef_symbols, cs_symbol_table = cs_symbol_table }
		| symb_entry.ste_kind == req_ste_kind
			= ({ ds_ident = symb_id, ds_index = symb_entry.ste_index, ds_arity = arity }, cs)
			= case symb_entry.ste_kind of
				STE_Imported kind module_index
					| mod_index == module_index && kind == req_ste_kind
						-> ({ ds_ident = symb_id, ds_index = symb_entry.ste_index, ds_arity = arity }, cs)
				_
					-> ({ ds_ident = symb_id, ds_index = NoIndex, ds_arity = arity }, { cs & cs_error = checkError symb_id "undefined" cs.cs_error })
		


typeOfBasicValue :: !BasicValue !*CheckState -> (!BasicType, !*CheckState)
typeOfBasicValue (BVI _) cs = (BT_Int, cs)
typeOfBasicValue (BVC _) cs = (BT_Char, cs)
typeOfBasicValue (BVB _) cs = (BT_Bool, cs)
typeOfBasicValue (BVR _) cs = (BT_Real, cs)
typeOfBasicValue (BVS _) cs
	# ({glob_module,glob_object={ds_ident,ds_index,ds_arity}}, cs) = getPredefinedGlobalSymbol PD_StringType PD_PredefinedModule STE_Type 0 cs
	= (BT_String (TA (MakeTypeSymbIdent { glob_object = ds_index, glob_module = glob_module } ds_ident ds_arity) []), cs)



buildTypeCase type_case_dynamic type_case_patterns type_case_default type_case_info_ptr :==
	Case {	case_expr = type_case_dynamic, case_guards = DynamicPatterns type_case_patterns, case_default = type_case_default, 
			case_info_ptr = type_case_info_ptr, case_ident = No, case_default_pos = NoPos }



determinePatternVariable (Yes bind) var_heap
	= (bind, var_heap)
determinePatternVariable No var_heap
	# (new_info_ptr, var_heap) = newPtr VI_Empty var_heap
	= ({ bind_src = newVarId "_x", bind_dst = new_info_ptr }, var_heap)



pushErrorAdmin2 _ NoPos cs=:{cs_error={ea_loc=[top_of_stack:_]}}
	// there is no position info, push current position to balance pop calls
	= pushErrorAdmin top_of_stack cs
pushErrorAdmin2 string pos=:(LinePos _ _) cs
	= pushErrorAdmin (newPosition {id_name=string, id_info=nilPtr} pos) cs



allocate_bound_var :: !FreeVar !*ExpressionHeap -> (!BoundVar, !.ExpressionHeap)
allocate_bound_var {fv_name, fv_info_ptr} expr_heap
	# (var_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
	= ({ var_name = fv_name, var_info_ptr = fv_info_ptr, var_expr_ptr = var_expr_ptr }, expr_heap)



allocate_free_var ident var_heap
	# (new_var_info_ptr, var_heap) = newPtr VI_Empty var_heap
	= ({ fv_def_level = NotALevel, fv_name = ident, fv_info_ptr = new_var_info_ptr,	fv_count = 0 }, var_heap)



newVarId name = { id_name = name, id_info = nilPtr }



retrieveSelectorIndexes mod_index {ste_kind = STE_Selector selector_list, ste_index, ste_previous }
	= map (adjust_mod_index mod_index) selector_list
where
	adjust_mod_index mod_index selector=:{glob_module}
		| glob_module == NoIndex
			= { selector & glob_module = mod_index }
			= selector
retrieveSelectorIndexes mod_index off_kind
	= []



instance <<< FieldSymbol
where
	(<<<) file { fs_var } = file <<< fs_var

