implementation module mergecases

import syntax, check, StdCompare, utilities; //, RWSDebug

/*
cContainsFreeVars 	:== True
cContainsNoFreeVars :== False

cMacroIsCalled 		:== True
cNoMacroIsCalled 	:== False
*/

class GetSetPatternRhs a
where
	get_pattern_rhs :: !a -> Expression
	set_pattern_rhs :: !a !Expression -> a

instance GetSetPatternRhs AlgebraicPattern
	where
		get_pattern_rhs p = p.ap_expr
		set_pattern_rhs p expr = {p & ap_expr=expr}

instance GetSetPatternRhs BasicPattern
	where
		get_pattern_rhs p = p.bp_expr
		set_pattern_rhs p expr = {p & bp_expr=expr};

instance GetSetPatternRhs DynamicPattern
	where
		get_pattern_rhs p = p.dp_rhs
		set_pattern_rhs p expr = {p & dp_rhs=expr}

mergeCases :: !(!Expression, !Position) ![(!Expression, !Position)] !*VarHeap !*ExpressionHeap !*ErrorAdmin
			-> *(!(!Expression, !Position), !*VarHeap, !*ExpressionHeap, !*ErrorAdmin)
mergeCases expr_and_pos [] var_heap symbol_heap error
	= (expr_and_pos, var_heap, symbol_heap, error)
mergeCases (Let lad=:{let_expr}, pos) exprs var_heap symbol_heap error
	# ((let_expr, _), var_heap, symbol_heap, error) = mergeCases (let_expr, NoPos) exprs var_heap symbol_heap error
	= ((Let {lad & let_expr = let_expr}, pos), var_heap,symbol_heap, error)
mergeCases (case_expr=:(Case first_case=:{case_expr = Var {var_info_ptr}, case_default = No}), case_pos)
			[(expr, expr_pos) : exprs] var_heap symbol_heap error
	# (split_result, var_heap, symbol_heap) = split_case var_info_ptr expr var_heap symbol_heap
	= case split_result of
		Yes {case_guards,case_default}
			# (case_guards, var_heap, symbol_heap, error) = merge_guards first_case.case_guards case_guards var_heap symbol_heap error
			-> mergeCases (Case { first_case & case_guards = case_guards, case_default = case_default }, NoPos)
						exprs var_heap symbol_heap error
		No
			# ((case_default, pos), var_heap, symbol_heap, error) = mergeCases (expr, expr_pos) exprs var_heap symbol_heap error
			-> ((Case { first_case & case_default = Yes case_default, case_default_pos = pos }, case_pos),
				var_heap, symbol_heap, error)

where
	split_case split_var_info_ptr (Case this_case=:{case_expr = Var {var_info_ptr}, case_guards, case_default}) var_heap symbol_heap
		| split_var_info_ptr == skip_alias var_info_ptr var_heap
			= (Yes this_case, var_heap, symbol_heap)
		| has_no_default case_default
			= case case_guards of
				AlgebraicPatterns type [alg_pattern]
					# (split_result, var_heap, symbol_heap) = split_case split_var_info_ptr alg_pattern.ap_expr var_heap symbol_heap
					-> case split_result of
						Yes split_case
							# (cees,symbol_heap) = push_expression_into_guards_and_default
													( \ guard_expr -> { this_case & case_guards = AlgebraicPatterns type [{ alg_pattern & ap_expr = guard_expr }] } )
														split_case symbol_heap
							-> (Yes cees, var_heap, symbol_heap)

						No
							-> (No, var_heap, symbol_heap) 
				BasicPatterns type [basic_pattern]
					# (split_result, var_heap, symbol_heap) = split_case split_var_info_ptr basic_pattern.bp_expr var_heap symbol_heap
					-> case split_result of
						Yes split_case
							# (cees,symbol_heap) = push_expression_into_guards_and_default
													( \ guard_expr -> { this_case & case_guards = BasicPatterns type [ { basic_pattern & bp_expr = guard_expr }] })
													split_case symbol_heap
							-> (Yes cees, var_heap, symbol_heap)

						No
							-> (No, var_heap, symbol_heap)
				DynamicPatterns [dynamic_pattern]
					# (split_result, var_heap, symbol_heap) = split_case split_var_info_ptr dynamic_pattern.dp_rhs var_heap symbol_heap
					-> case split_result of
						Yes split_case
							# (cees,symbol_heap) = push_expression_into_guards_and_default
										( \ guard_expr -> { this_case & case_guards = DynamicPatterns [ { dynamic_pattern & dp_rhs = guard_expr }] })
										split_case symbol_heap
							-> (Yes cees, var_heap, symbol_heap)

						No
							-> (No, var_heap, symbol_heap)
				_
					-> (No, var_heap, symbol_heap)
		| otherwise
			= (No, var_heap, symbol_heap)
	split_case split_var_info_ptr (Let lad=:{let_expr,let_strict_binds,let_lazy_binds}) var_heap symbol_heap
		| isEmpty let_strict_binds
			# var_heap = foldSt set_alias let_lazy_binds var_heap
			# (split_result, var_heap, symbol_heap) = split_case split_var_info_ptr let_expr var_heap symbol_heap
			= case split_result of
				Yes split_case
					# (case_guards, var_heap, symbol_heap) = push_let_expression_into_guards lad split_case.case_guards var_heap symbol_heap
					-> (Yes { split_case & case_guards = case_guards }, var_heap, symbol_heap)
				No
					-> (No, var_heap, symbol_heap)
			= (No, var_heap, symbol_heap)
	split_case split_var_info_ptr expr var_heap symbol_heap
		= (No, var_heap, symbol_heap)
	
	has_no_default No 		= True
	has_no_default (Yes _) 	= False
	
	skip_alias var_info_ptr var_heap
		= case sreadPtr var_info_ptr var_heap of
			VI_Alias bv
				-> bv.var_info_ptr
			_
				-> var_info_ptr

	set_alias {lb_src=Var var,lb_dst={fv_info_ptr}} var_heap
		= var_heap <:= (fv_info_ptr, VI_Alias var)
	set_alias _ var_heap
		= var_heap
/*
	push_expression_into_guards expr_fun (AlgebraicPatterns type patterns) 
		= AlgebraicPatterns type (map (\algpattern -> { algpattern & ap_expr = expr_fun algpattern.ap_expr }) patterns)
	push_expression_into_guards expr_fun (BasicPatterns type patterns) 
		= BasicPatterns type (map (\baspattern -> { baspattern & bp_expr = expr_fun baspattern.bp_expr }) patterns)
	push_expression_into_guards expr_fun (DynamicPatterns patterns) 
		= DynamicPatterns (map (\dynpattern -> { dynpattern & dp_rhs = expr_fun dynpattern.dp_rhs }) patterns)
*/
	push_expression_into_guards_and_default expr_fun split_case symbol_heap
		= push_expression_into_guards_and_default split_case symbol_heap
	where
		push_expression_into_guards_and_default split_case=:{case_default=No} symbol_heap
			= push_expression_into_guards split_case symbol_heap
		push_expression_into_guards_and_default split_case=:{case_default=Yes default_expr} symbol_heap
			# (new_default_expr,symbol_heap) = new_case default_expr symbol_heap
			= push_expression_into_guards {split_case & case_default=Yes new_default_expr} symbol_heap
	
		push_expression_into_guards split_case=:{case_guards=AlgebraicPatterns type patterns} symbol_heap
			# (new_patterns,symbol_heap) = push_expression_into_patterns patterns symbol_heap
			= ({split_case & case_guards=AlgebraicPatterns type new_patterns},symbol_heap)
		push_expression_into_guards split_case=:{case_guards=BasicPatterns type patterns} symbol_heap
			# (new_patterns,symbol_heap) = push_expression_into_patterns patterns symbol_heap
			= ({split_case & case_guards=BasicPatterns type new_patterns},symbol_heap)
		push_expression_into_guards split_case=:{case_guards=DynamicPatterns patterns} symbol_heap
			# (new_patterns,symbol_heap) = push_expression_into_patterns patterns symbol_heap
			= ({split_case & case_guards=DynamicPatterns new_patterns},symbol_heap)
		
		push_expression_into_patterns [] symbol_heap
			= ([],symbol_heap)
		push_expression_into_patterns [pattern:patterns] symbol_heap
			# (patterns,symbol_heap) = mapSt f patterns symbol_heap
				with
					f algpattern symbol_heap
						# (case_expr,symbol_heap) = new_case (get_pattern_rhs algpattern) symbol_heap
						= (set_pattern_rhs algpattern case_expr,symbol_heap)
			= ([set_pattern_rhs pattern (Case (expr_fun (get_pattern_rhs pattern))):patterns],symbol_heap)

		new_case expr symbol_heap
			# cees=expr_fun expr
			# (case_info,symbol_heap) = readPtr cees.case_info_ptr symbol_heap
			# (new_case_info_ptr,symbol_heap) = newPtr case_info symbol_heap
			= (Case {cees & case_info_ptr=new_case_info_ptr},symbol_heap)

	replace_variables_in_expression expr var_heap symbol_heap
		# us = { us_var_heap = var_heap, us_symbol_heap = symbol_heap, us_opt_type_heaps = No,us_cleanup_info = [], us_local_macro_functions = No }
		  ui = {ui_handle_aci_free_vars = RemoveThem, ui_convert_module_n = -1, ui_conversion_table = No}
		  (expr, us) = unfold expr ui us
		= (expr, us.us_var_heap, us.us_symbol_heap)

	new_variable fv=:{fv_name, fv_info_ptr} var_heap
		# (new_info_ptr, var_heap) = newPtr VI_Empty var_heap
		= ({fv & fv_info_ptr = new_info_ptr}, var_heap <:= (fv_info_ptr, VI_Variable fv_name new_info_ptr))
		
	rebuild_let_expression lad expr var_heap expr_heap
		# (rev_let_lazy_binds, var_heap) = foldSt renew_let_var lad.let_lazy_binds ([], var_heap)
		  (let_info_ptr, expr_heap) = newPtr EI_Empty expr_heap
		  (expr, var_heap, expr_heap) = replace_variables_in_expression expr var_heap expr_heap
		  (let_lazy_binds, var_heap, expr_heap) = foldSt replace_variables_in_bound_expression rev_let_lazy_binds ([], var_heap, expr_heap)
		= (Let { lad & let_lazy_binds = let_lazy_binds, let_info_ptr = let_info_ptr, let_expr = expr}, var_heap, expr_heap)
	where
		renew_let_var bind=:{lb_dst} (rev_binds, var_heap)
			# (lb_dst, var_heap) = new_variable lb_dst var_heap
			= ([{ bind & lb_dst = lb_dst } : rev_binds], var_heap)

		replace_variables_in_bound_expression bind=:{lb_src} (rev_binds, var_heap, expr_heap)
			# (lb_src, var_heap, expr_heap) = replace_variables_in_expression lb_src var_heap expr_heap
			= ([{ bind & lb_src = lb_src } : rev_binds], var_heap, expr_heap)

	push_let_expression_into_guards lad (AlgebraicPatterns type patterns) var_heap expr_heap
		# (patterns, var_heap, expr_heap) = push_let_expression_into_algebraic_pattern lad patterns var_heap expr_heap
		= (AlgebraicPatterns type patterns, var_heap, expr_heap)
	where
		push_let_expression_into_algebraic_pattern lad [pattern=:{ap_expr}] var_heap expr_heap
			= ([{ pattern & ap_expr = Let { lad & let_expr = ap_expr}}], var_heap, expr_heap)
		push_let_expression_into_algebraic_pattern lad [pattern=:{ap_expr}:patterns] var_heap expr_heap
			# (ap_expr, var_heap, expr_heap) = rebuild_let_expression lad ap_expr var_heap expr_heap
			  (patterns, var_heap, expr_heap) = push_let_expression_into_algebraic_pattern lad patterns var_heap expr_heap
			= ([{pattern & ap_expr = ap_expr} : patterns], var_heap, expr_heap)
	push_let_expression_into_guards lad (BasicPatterns type patterns) var_heap expr_heap 
		# (patterns, var_heap, expr_heap) = push_let_expression_into_basic_pattern lad patterns var_heap expr_heap
		= (BasicPatterns type patterns, var_heap, expr_heap)
	where
		push_let_expression_into_basic_pattern lad [pattern=:{bp_expr}] var_heap expr_heap
			= ([{ pattern & bp_expr = Let { lad & let_expr = bp_expr}}], var_heap, expr_heap)
		push_let_expression_into_basic_pattern lad [pattern=:{bp_expr}:patterns] var_heap expr_heap
			# (bp_expr, var_heap, expr_heap) = rebuild_let_expression lad bp_expr var_heap expr_heap
			  (patterns, var_heap, expr_heap) = push_let_expression_into_basic_pattern lad patterns var_heap expr_heap
			= ([{pattern & bp_expr = bp_expr} : patterns], var_heap, expr_heap)
	push_let_expression_into_guards lad (DynamicPatterns patterns) var_heap expr_heap
		# (patterns, var_heap, expr_heap) = push_let_expression_into_dynamic_pattern lad patterns var_heap expr_heap
		= (DynamicPatterns patterns, var_heap, expr_heap)
	where
		push_let_expression_into_dynamic_pattern lad [pattern=:{dp_rhs}] var_heap expr_heap
			= ([{ pattern & dp_rhs = Let { lad & let_expr = dp_rhs}}], var_heap, expr_heap)
		push_let_expression_into_dynamic_pattern lad [pattern=:{dp_rhs}:patterns] var_heap expr_heap
			# (dp_rhs, var_heap, expr_heap) = rebuild_let_expression lad dp_rhs var_heap expr_heap
			  (patterns, var_heap, expr_heap) = push_let_expression_into_dynamic_pattern lad patterns var_heap expr_heap
			= ([{pattern & dp_rhs = dp_rhs} : patterns], var_heap, expr_heap)

	merge_guards guards=:(AlgebraicPatterns type1 patterns1) (AlgebraicPatterns type2 patterns2) var_heap symbol_heap error
		| type1 == type2
			# (merged_patterns, var_heap, symbol_heap, error) = merge_algebraic_patterns patterns1 patterns2 var_heap symbol_heap error
			= (AlgebraicPatterns type1 merged_patterns, var_heap, symbol_heap, error) 
			= (guards, var_heap, symbol_heap, checkError "" "incompatible patterns in case" error)
	merge_guards guards=:(BasicPatterns basic_type1 patterns1) (BasicPatterns basic_type2 patterns2) var_heap symbol_heap error
		| basic_type1 == basic_type2
			# (merged_patterns, var_heap, symbol_heap, error) = merge_basic_patterns patterns1 patterns2 var_heap symbol_heap error
			= (BasicPatterns basic_type1 merged_patterns, var_heap, symbol_heap, error) 
			= (guards, var_heap, symbol_heap, checkError "" "incompatible patterns in case" error)
	merge_guards guards=:(DynamicPatterns  patterns1) (DynamicPatterns  patterns2) var_heap symbol_heap error
		# (merged_patterns, var_heap, symbol_heap, error) = merge_dynamic_patterns patterns1 patterns2 var_heap symbol_heap error
		= (DynamicPatterns merged_patterns, var_heap, symbol_heap, error) 
	merge_guards patterns1 patterns2 var_heap symbol_heap error
		= (patterns1, var_heap, symbol_heap, checkError "" "incompatible patterns in case" error)
		
	merge_algebraic_patterns patterns [alg_pattern : alg_patterns] var_heap symbol_heap error
		# (patterns, var_heap, symbol_heap, error) = merge_algebraic_pattern_with_patterns alg_pattern patterns var_heap symbol_heap error
		= merge_algebraic_patterns patterns alg_patterns var_heap symbol_heap error
	merge_algebraic_patterns patterns [] var_heap symbol_heap error
		= (patterns, var_heap, symbol_heap, error)
	
	merge_basic_patterns patterns [alg_pattern : alg_patterns] var_heap symbol_heap error
		# (patterns, var_heap, symbol_heap, error) = merge_basic_pattern_with_patterns alg_pattern patterns var_heap symbol_heap error
		= merge_basic_patterns patterns alg_patterns var_heap symbol_heap error
	merge_basic_patterns patterns [] var_heap symbol_heap error
		= (patterns, var_heap, symbol_heap, error)
	
	merge_dynamic_patterns patterns1 patterns2 var_heap symbol_heap error
		= (patterns1 ++ patterns2, var_heap, symbol_heap, error)

	merge_algebraic_pattern_with_patterns new_pattern [pattern=:{ap_symbol,ap_vars,ap_expr} : patterns] var_heap symbol_heap error
		| new_pattern.ap_symbol == ap_symbol
			| isEmpty new_pattern.ap_vars
				# ((ap_expr, _), var_heap, symbol_heap, error) = mergeCases (ap_expr, NoPos) [(new_pattern.ap_expr, NoPos)] var_heap symbol_heap error
				= ([{ pattern & ap_expr = ap_expr} : patterns], var_heap, symbol_heap, error)
				# (new_expr, var_heap, symbol_heap) = replace_variables new_pattern.ap_vars new_pattern.ap_expr ap_vars var_heap symbol_heap
				  ((ap_expr, _), var_heap, symbol_heap, error) = mergeCases (ap_expr, NoPos) [(new_expr, NoPos)] var_heap symbol_heap error
				= ([{ pattern & ap_expr = ap_expr} : patterns], var_heap, symbol_heap, error)
			# (patterns, var_heap, symbol_heap, error) = merge_algebraic_pattern_with_patterns new_pattern patterns var_heap symbol_heap error		
			= ([ pattern : patterns ], var_heap, symbol_heap, error)
	where
		replace_variables vars expr ap_vars var_heap symbol_heap
			# var_heap = build_aliases vars ap_vars var_heap
			# us = { us_var_heap = var_heap, us_symbol_heap = symbol_heap, us_opt_type_heaps = No,us_cleanup_info=[], us_local_macro_functions = No }
			  ui = {ui_handle_aci_free_vars = RemoveThem, ui_convert_module_n= -1, ui_conversion_table=No }
			  (expr, us) = unfold expr ui us
			= (expr, us.us_var_heap, us.us_symbol_heap)

		build_aliases [var1 : vars1] [ {fv_name,fv_info_ptr} : vars2 ] var_heap
			= build_aliases vars1 vars2 (writePtr var1.fv_info_ptr (VI_Variable fv_name fv_info_ptr) var_heap)
		build_aliases [] [] var_heap
			= var_heap

	merge_algebraic_pattern_with_patterns new_pattern [] var_heap symbol_heap error
		= ([new_pattern], var_heap, symbol_heap, error)
	
	merge_basic_pattern_with_patterns new_pattern [pattern=:{bp_value,bp_expr} : patterns]  var_heap symbol_heap error
		| new_pattern.bp_value == bp_value
			# ((bp_expr, _), var_heap, symbol_heap, error) = mergeCases (bp_expr, NoPos) [(new_pattern.bp_expr, NoPos)] var_heap symbol_heap error
			= ([{ pattern & bp_expr = bp_expr} : patterns], var_heap, symbol_heap, error)
			# (patterns, var_heap, symbol_heap, error) = merge_basic_pattern_with_patterns new_pattern patterns var_heap symbol_heap error		
			= ([ pattern : patterns ], var_heap, symbol_heap, error)
	merge_basic_pattern_with_patterns new_pattern [] var_heap symbol_heap error
		= ([new_pattern], var_heap, symbol_heap, error)
	
mergeCases (case_expr=:(Case first_case=:{case_default, case_default_pos}), case_pos) [expr : exprs] var_heap symbol_heap error
	= case case_default of
		Yes default_expr
			# ((default_expr, case_default_pos), var_heap, symbol_heap, error) = mergeCases (default_expr, case_default_pos) [expr : exprs] var_heap symbol_heap error
			-> ((Case { first_case & case_default = Yes default_expr, case_default_pos = case_default_pos }, case_pos),
				var_heap, symbol_heap, error)
		No
			# ((default_expr, pos), var_heap, symbol_heap, error) = mergeCases expr exprs var_heap symbol_heap error
			-> ((Case { first_case & case_default = Yes default_expr, case_default_pos = pos }, case_pos),
				var_heap, symbol_heap, error)
mergeCases expr_and_pos _ var_heap symbol_heap error
	= (expr_and_pos, var_heap, symbol_heap, checkWarning "" " alternative will never match" error)

