implementation module convertcases

import syntax, checksupport, trans

// exactZip fails when its arguments are of unequal length
// move to utilities?
exactZip :: ![.a] ![.b] -> [(.a,.b)]
exactZip [] []
	=	[]
exactZip [x:xs][y:ys]
	=	[(x,y) : exactZip xs ys]

getIdent :: (Optional Ident) Int -> Ident
getIdent (Yes ident) fun_nr
	= ident
getIdent No fun_nr
	= { id_name = "_f" +++ toString fun_nr, id_info = nilPtr }

addLetVars :: [LetBind] [AType] [(FreeVar, AType)] -> [(FreeVar, AType)]
addLetVars [{lb_dst} : binds] [bind_type : bind_types] bound_vars
	= addLetVars binds bind_types [ (lb_dst, bind_type) : bound_vars ]
addLetVars [] _ bound_vars
	= bound_vars

convertCasesOfFunctions :: !*{! Group} !Int !{# {# FunType} } !{# CommonDefs} !*{#FunDef} !*{#{# CheckedTypeDef}}
		!ImportedConstructors !*VarHeap !*TypeHeaps !*ExpressionHeap
			-> (!ImportedFunctions, !*{! Group}, !*{#FunDef}, !*{#{# CheckedTypeDef}}, !ImportedConstructors, !*VarHeap, !*TypeHeaps, !*ExpressionHeap)
convertCasesOfFunctions groups main_dcl_module_n dcl_functions common_defs fun_defs imported_types imported_conses var_heap type_heaps expr_heap
	#! nr_of_funs = size fun_defs
	# (groups, (fun_defs, collected_imports, {cs_new_functions, cs_var_heap, cs_expr_heap, cs_fun_heap}))
			= convert_groups 0 groups dcl_functions common_defs
				(fun_defs, [], { cs_new_functions = [], cs_fun_heap = newHeap, cs_var_heap = var_heap, cs_expr_heap = expr_heap, cs_next_fun_nr = nr_of_funs })
	  (groups, new_fun_defs, imported_types, imported_conses, type_heaps, cs_var_heap)
			= addNewFunctionsToGroups common_defs cs_fun_heap cs_new_functions main_dcl_module_n groups imported_types imported_conses type_heaps cs_var_heap
//	  		= foldSt (add_new_function_to_group cs_fun_heap common_defs) cs_new_functions (groups, [], imported_types, imported_conses, type_heaps, cs_var_heap)
	  (imported_functions, imported_conses) = foldSt split collected_imports ([], imported_conses)
	= (imported_functions, groups, { fundef \\ fundef <- [ fundef \\ fundef <-: fun_defs ] ++ new_fun_defs },
			imported_types, imported_conses, cs_var_heap, type_heaps, cs_expr_heap)
where
	convert_groups group_nr groups dcl_functions common_defs fun_defs_and_ci
		| group_nr == size groups
			= (groups, fun_defs_and_ci)
		// otherwise
			# (group, groups) = groups![group_nr]
			= convert_groups (inc group_nr) groups dcl_functions common_defs
				(foldSt (convert_function group_nr dcl_functions common_defs) group.group_members fun_defs_and_ci)

	convert_function group_index dcl_functions common_defs fun (fun_defs, collected_imports, cs)
		# (fun_def, fun_defs) = fun_defs![fun]
		# {fun_body,fun_type} = fun_def
		  (fun_body, (collected_imports, cs)) = eliminate_code_sharing_in_function dcl_functions common_defs fun_body /* (fun_body ---> ("convert_function", fun_def.fun_symb, fun_body)) */ (collected_imports, cs)		  		
		  (fun_body, cs) = convert_cases_into_function_patterns fun_body fun_type group_index common_defs cs
		= ({fun_defs & [fun] = { fun_def & fun_body = fun_body }}, collected_imports, cs)

	convert_cases_into_function_patterns (TransformedBody {tb_args,tb_rhs=Case {case_expr = Var var=:{var_info_ptr}, case_guards, case_default, case_info_ptr}})
			(Yes {st_result,st_args}) group_index common_defs cs=:{cs_expr_heap}
		# (EI_CaseTypeAndRefCounts case_type _, cs_expr_heap) = readPtr case_info_ptr cs_expr_heap
		  (default_ptr, cs_expr_heap) = makePtrToDefault case_default st_result cHasNoDefault cs_expr_heap
		  vars_with_types = exactZip tb_args st_args
		  (form_var_with_type, left_vars, right_vars) = split_vars var_info_ptr vars_with_types
		  (fun_bodies, cs) = convertPatterns case_guards case_type.ct_cons_types (Yes form_var_with_type) left_vars right_vars default_ptr group_index common_defs
					{ cs & cs_expr_heap = cs_expr_heap }
		  (fun_bodies, cs) = convertDefault default_ptr (Yes form_var_with_type) left_vars right_vars group_index common_defs (fun_bodies, cs) 
		= (BackendBody fun_bodies, cs)
	where
		split_vars var_info_ptr [ form_var_with_type=:({fv_info_ptr},_) : free_vars]
			| var_info_ptr == fv_info_ptr
				= (form_var_with_type, [], free_vars)
				# (form_var, left, right) = split_vars var_info_ptr free_vars
				= (form_var, [form_var_with_type : left], right)			
	convert_cases_into_function_patterns (TransformedBody {tb_args,tb_rhs}) (Yes {st_result,st_args}) group_index common_defs cs
		# (tb_rhs, cs) = convertRootExpression {ci_bound_vars=exactZip tb_args st_args, ci_group_index=group_index, ci_common_defs=common_defs} cHasNoDefault tb_rhs cs
		= (BackendBody [ { bb_args = map FP_Variable tb_args, bb_rhs = tb_rhs }], cs)

	eliminate_code_sharing_in_function dcl_functions common_defs (TransformedBody body=:{tb_rhs}) (collected_imports, cs=:{cs_expr_heap,cs_var_heap})
		# {rcs_var_heap, rcs_expr_heap, rcs_imports}
			= weightedRefCount {rci_imported={cii_dcl_functions=dcl_functions, cii_common_defs=common_defs, cii_main_dcl_module_n=main_dcl_module_n}, rci_depth=1} tb_rhs
				{ rcs_var_heap = cs_var_heap, rcs_expr_heap = cs_expr_heap, rcs_free_vars = [], rcs_imports = collected_imports} 
//		  	---> ("eliminate_code_sharing_in_function (weightedRefCount)", tb_rhs)
		  (tb_rhs, {ds_lets,ds_var_heap,ds_expr_heap}) = distributeLets 1 tb_rhs { ds_lets = [], ds_var_heap = rcs_var_heap, ds_expr_heap = rcs_expr_heap}
		  (tb_rhs, (var_heap, expr_heap)) = buildLetExpr ds_lets tb_rhs (ds_var_heap,ds_expr_heap)
		= (TransformedBody { body & tb_rhs = tb_rhs }, (rcs_imports, { cs & cs_var_heap = var_heap, cs_expr_heap = expr_heap }))
		  	==> ("eliminate_code_sharing_in_function (distributeLets)", tb_rhs)

	split (SK_Function fun_symb) (collected_functions, collected_conses)
		= ([fun_symb : collected_functions], collected_conses)
	split (SK_Constructor cons_symb) (collected_functions, collected_conses)
		= (collected_functions, [ cons_symb : collected_conses])


/*

	weightedRefCount determines the reference counts of variables in an expression. Runtime behaviour of constructs is taken into account: 
	multiple occurrences of variables in different alternatives of the same case clause are counted only once. The outcome
	is used to distribute shared expressions (via let declarations) over cases. In this way code sharing is eliminated.
	As a side effect, weightedRefCount returns a list of all imported functions that have been used inside the expression.
	
*/

::	CheckImportedInfo =
	{	cii_dcl_functions	:: !{# {# FunType} }
	,	cii_common_defs		:: !{# CommonDefs}
	,	cii_main_dcl_module_n :: !Int
	}

::	RCInfo =
	{	rci_imported	:: !CheckImportedInfo
	,	rci_depth		:: !Int
	}

::	RCState =
	{	rcs_free_vars	:: ![VarInfoPtr]
	,	rcs_imports		:: ![SymbKind]
	,	rcs_var_heap		:: !.VarHeap
	,	rcs_expr_heap	:: !.ExpressionHeap
	}

checkImportedSymbol :: SymbKind VarInfoPtr ([SymbKind], *VarHeap) -> ([SymbKind], *VarHeap)
checkImportedSymbol symb_kind symb_type_ptr (collected_imports, var_heap)
	#! type_info = sreadPtr symb_type_ptr var_heap
	= case type_info of
		VI_Used
			-> (collected_imports, var_heap)
		_
			-> ([symb_kind : collected_imports ], var_heap <:= (symb_type_ptr, VI_Used))

weightedRefCountOfVariable depth var_info_ptr lvi=:{lvi_count,lvi_var,lvi_depth,lvi_previous,lvi_new} ref_count new_vars
	| lvi_depth < depth 
		= (True, {lvi & lvi_count = ref_count, lvi_depth = depth, lvi_new = True, lvi_previous =
				[{plvi_count = lvi_count, plvi_depth = lvi_depth, plvi_new = lvi_new } : lvi_previous]}, [var_info_ptr : new_vars])
//					==> (lvi_var, " PUSHED ",lvi_depth)
	| lvi_count == 0
		= (True, { lvi & lvi_count = ref_count }, [var_info_ptr : new_vars])
	// otherwise
		= (lvi_new, { lvi & lvi_count = lvi_count + ref_count }, new_vars)

class weightedRefCount e :: !RCInfo !e !*RCState -> *RCState

instance weightedRefCount BoundVar
where
	weightedRefCount rci=:{rci_depth} {var_name,var_info_ptr} rcs=:{rcs_var_heap,rcs_free_vars}
		#! var_info = sreadPtr var_info_ptr rcs_var_heap
		= case var_info of
			VI_LetVar lvi
				# (is_new, lvi=:{lvi_expression}, rcs_free_vars) = weightedRefCountOfVariable rci_depth var_info_ptr lvi 1 rcs_free_vars
				| is_new
					# rcs = weightedRefCount rci lvi_expression
							{ rcs & rcs_free_vars = rcs_free_vars,
							  rcs_var_heap = rcs.rcs_var_heap  <:= (var_info_ptr, VI_LetVar {lvi & lvi_expression = EE, lvi_new = False})}
					  (VI_LetVar lvi, rcs_var_heap) = readPtr var_info_ptr rcs.rcs_var_heap
					-> { rcs & rcs_var_heap = rcs_var_heap <:= (var_info_ptr, VI_LetVar { lvi & lvi_expression = lvi_expression }) }
//							 ==> (var_name, var_info_ptr, depth, lvi.lvi_count)
				// otherwise
					-> { rcs & rcs_var_heap = rcs.rcs_var_heap <:= (var_info_ptr, VI_LetVar lvi) }
			_
				-> rcs
				
instance weightedRefCount Expression
where
	weightedRefCount rci (Var var) rcs
		= weightedRefCount rci var rcs
	weightedRefCount rci (App app) rcs
		= weightedRefCount rci app rcs
	weightedRefCount rci (fun_expr @ exprs) rcs
		= weightedRefCount rci (fun_expr, exprs) rcs
	weightedRefCount rci=:{rci_depth} (Let {let_strict_binds,let_lazy_binds,let_expr, let_info_ptr}) rcs=:{rcs_var_heap}
		# rcs = weightedRefCount rci let_strict_binds { rcs & rcs_var_heap = foldSt store_binding let_lazy_binds rcs_var_heap }
		  rcs = weightedRefCount rci let_expr rcs
		  (let_info, rcs_expr_heap) = readPtr let_info_ptr rcs.rcs_expr_heap
		  rcs = { rcs & rcs_expr_heap = rcs_expr_heap }
		= case let_info of
			EI_LetType let_type
		  		# (ref_counts, rcs_var_heap) = mapSt get_ref_count let_lazy_binds rcs.rcs_var_heap
				  (rcs_free_vars, rcs_var_heap) = foldl remove_variable (rcs.rcs_free_vars, rcs_var_heap) let_lazy_binds
				-> { rcs & rcs_free_vars = rcs_free_vars, rcs_var_heap = rcs_var_heap,
						rcs_expr_heap = rcs.rcs_expr_heap <:= (let_info_ptr, EI_LetTypeAndRefCounts let_type ref_counts)}
//							---> ("weightedRefCount (EI_LetType)", ptrToInt let_info_ptr, [ x.bind_dst \\ x <- let_lazy_binds])
			_
				# (rcs_free_vars, rcs_var_heap) = foldl remove_variable (rcs.rcs_free_vars, rcs.rcs_var_heap) let_lazy_binds
				-> { rcs & rcs_free_vars = rcs_free_vars, rcs_var_heap = rcs_var_heap }
//							---> ("weightedRefCount (_)", ptrToInt let_info_ptr, [ x.bind_dst \\ x <- let_lazy_binds])
	where
		remove_variable ([], var_heap) let_bind
			= ([], var_heap)
		remove_variable ([var_ptr : var_ptrs], var_heap) bind=:{lb_dst={fv_name,fv_info_ptr}}
			| fv_info_ptr == var_ptr
				# (VI_LetVar {lvi_count,lvi_depth}, var_heap) = readPtr fv_info_ptr var_heap
				= (var_ptrs, var_heap) 
//						==> ("remove_variable (lvi_count,lvi_dpeth) ", fv_name, lvi_count, lvi_depth)
			// otherwise
				# (var_ptrs, var_heap) = remove_variable (var_ptrs, var_heap) bind
				= ([var_ptr : var_ptrs], var_heap)

		store_binding {lb_dst={fv_name,fv_info_ptr},lb_src} var_heap
			= var_heap <:= (fv_info_ptr, VI_LetVar {lvi_count = 0, lvi_depth = rci_depth, lvi_previous = [],
													lvi_new = True, lvi_expression = lb_src, lvi_var = fv_name})

		get_ref_count {lb_dst={fv_name,fv_info_ptr}} var_heap 
			# (VI_LetVar {lvi_count}, var_heap) = readPtr fv_info_ptr var_heap
		  	= (lvi_count, var_heap)
//				==> (fv_name,fv_info_ptr,lvi_count)
	weightedRefCount rci (Case case_expr) rcs=:{rcs_expr_heap}
		# (case_info, rcs_expr_heap) = readPtr case_expr.case_info_ptr rcs_expr_heap
		= weightedRefCountOfCase rci case_expr case_info { rcs & rcs_expr_heap = rcs_expr_heap }
	weightedRefCount rci expr=:(BasicExpr _ _) rcs
		= rcs
	weightedRefCount rci (MatchExpr _ constructor expr) rcs
		= weightedRefCount rci expr rcs
	weightedRefCount rci (Selection opt_tuple expr selections) rcs
		= weightedRefCount rci (expr, selections) rcs
	weightedRefCount rci (Update expr1 selections expr2) rcs
		= weightedRefCount rci (expr1, (selections, expr2)) rcs
	weightedRefCount rci (RecordUpdate cons_symbol expression expressions) rcs
		= weightedRefCount rci (expression, expressions) rcs
	weightedRefCount rci (TupleSelect tuple_symbol arg_nr expr) rcs
		= weightedRefCount rci expr rcs
	weightedRefCount rci (AnyCodeExpr _ _ _) rcs
		= rcs
	weightedRefCount rci (ABCCodeExpr _ _) rcs
		= rcs
	weightedRefCount rci (TypeCodeExpression type_code_expr) rcs
		= weightedRefCount rci type_code_expr rcs
	weightedRefCount rci EE rcs
		= rcs
	weightedRefCount rci (NoBind ptr) rcs
		= rcs
	weightedRefCount rci expr rcs
		= abort ("weightedRefCount [Expression] (convertcases, 864))" ---> expr)

addPatternVariable depth {cv_variable = var_info_ptr, cv_count = ref_count} (free_vars, var_heap)
 	#! var_info = sreadPtr var_info_ptr var_heap
	= case var_info of
		VI_LetVar lvi
			# (_, lvi, free_vars) = weightedRefCountOfVariable depth var_info_ptr lvi ref_count free_vars
			-> (free_vars, var_heap <:= (var_info_ptr, VI_LetVar lvi))
		_
			-> (free_vars, var_heap)

weightedRefCountOfCase rci=:{rci_depth} this_case=:{case_expr, case_guards, case_default, case_info_ptr} (EI_CaseType case_type)
			rcs=:{ rcs_var_heap, rcs_expr_heap, rcs_imports }
	# (local_vars, vars_and_heaps) = weighted_ref_count_in_case_patterns {rci & rci_depth=rci_depth+1} case_guards rcs_imports rcs_var_heap rcs_expr_heap
	  (default_vars, (all_vars, rcs_imports, var_heap, expr_heap)) = weighted_ref_count_in_default {rci & rci_depth=rci_depth+1} case_default vars_and_heaps
	  rcs = weightedRefCount rci case_expr { rcs & rcs_var_heap = var_heap, rcs_expr_heap = expr_heap, rcs_imports = rcs_imports }
	  (rcs_free_vars, rcs_var_heap) = foldSt (addPatternVariable rci_depth) all_vars (rcs.rcs_free_vars, rcs.rcs_var_heap)
	  rcs_expr_heap = rcs.rcs_expr_heap <:= (case_info_ptr, EI_CaseTypeAndRefCounts case_type 
	  		{ rcc_all_variables = all_vars, rcc_default_variables = default_vars, rcc_pattern_variables = local_vars })
	= { rcs & rcs_var_heap = rcs_var_heap, rcs_expr_heap = rcs_expr_heap, rcs_free_vars = rcs_free_vars   }
//			---> ("weightedRefCountOfCase", ptrToInt case_info_ptr, case_expr)
	where
		weighted_ref_count_in_default rci (Yes expr) info
			= weightedRefCountInPatternExpr rci expr info
		weighted_ref_count_in_default rci No info
			= ([], info)
		
		weighted_ref_count_in_case_patterns rci (AlgebraicPatterns type patterns) collected_imports var_heap expr_heap
			= mapSt (weighted_ref_count_in_algebraic_pattern rci) patterns ([], collected_imports, var_heap, expr_heap)
		where
			weighted_ref_count_in_algebraic_pattern rci=:{rci_imported={cii_main_dcl_module_n, cii_common_defs}} {ap_expr,ap_symbol={glob_module, glob_object={ds_index}}} wrcs_state
				# (free_vars_with_rc, (all_free_vars, collected_imports, var_heap, expr_heap))
						= weightedRefCountInPatternExpr rci ap_expr wrcs_state
				| glob_module <> cii_main_dcl_module_n
					# {cons_type_ptr} = cii_common_defs.[glob_module].com_cons_defs.[ds_index]
					  (collected_imports, var_heap) = checkImportedSymbol (SK_Constructor {glob_module = glob_module, glob_object = ds_index})
							cons_type_ptr (collected_imports, var_heap)
					= (free_vars_with_rc, (all_free_vars, collected_imports, var_heap, expr_heap))
					= (free_vars_with_rc, (all_free_vars, collected_imports, var_heap, expr_heap))

		weighted_ref_count_in_case_patterns rci (BasicPatterns type patterns) collected_imports var_heap expr_heap
			= mapSt (\{bp_expr} -> weightedRefCountInPatternExpr rci bp_expr) patterns ([], collected_imports, var_heap, expr_heap)
		weighted_ref_count_in_case_patterns  rci (DynamicPatterns patterns) collected_imports var_heap expr_heap
			= mapSt (\{dp_rhs} -> weightedRefCountInPatternExpr rci dp_rhs) patterns ([], collected_imports, var_heap, expr_heap)

weightedRefCountOfCase rci=:{rci_depth} this_case=:{case_expr, case_guards, case_default, case_info_ptr} (EI_CaseTypeAndRefCounts case_type {rcc_all_variables})
			rcs=:{ rcs_var_heap, rcs_expr_heap, rcs_imports }
	# rcs = weightedRefCount rci case_expr rcs
	  (rcs_free_vars, rcs_var_heap) = foldSt (addPatternVariable rci_depth) rcc_all_variables (rcs.rcs_free_vars, rcs.rcs_var_heap)
	= { rcs & rcs_var_heap = rcs_var_heap, rcs_free_vars = rcs_free_vars }	
//			---> ("weightedRefCountOfCase 2", ptrToInt case_info_ptr, case_expr)

instance weightedRefCount Selection
where
	weightedRefCount rci=:{rci_imported} (ArraySelection {glob_module,glob_object={ds_index}} _ index_expr) rcs
		# rcs = weightedRefCount rci index_expr rcs
		= checkImportOfDclFunction rci_imported glob_module ds_index rcs
	weightedRefCount rci (DictionarySelection _ selectors _ index_expr) rcs
		# rcs = weightedRefCount rci index_expr rcs
		= weightedRefCount rci selectors rcs
	weightedRefCount rci=:{rci_imported} (RecordSelection selector _) rcs
		= checkRecordSelector rci_imported selector rcs

weightedRefCountInPatternExpr rci=:{rci_depth} pattern_expr (previous_free_vars, collected_imports, var_heap, expr_heap)
	# {rcs_free_vars,rcs_var_heap,rcs_imports,rcs_expr_heap} = weightedRefCount rci pattern_expr
				{ rcs_var_heap = var_heap, rcs_expr_heap = expr_heap, rcs_free_vars = [], rcs_imports = collected_imports}
	  (free_vars_with_rc, rcs_var_heap) = mapSt get_ref_count rcs_free_vars rcs_var_heap
	  (previous_free_vars, rcs_var_heap) = foldSt (select_unused_free_variable rci_depth) previous_free_vars ([], rcs_var_heap)
	  (all_free_vars, rcs_var_heap) = foldSt (collect_free_variable rci_depth) rcs_free_vars (previous_free_vars, rcs_var_heap)
//			==> ("remove_vars ", depth, free_vars_with_rc)
	= (free_vars_with_rc, (all_free_vars, rcs_imports, rcs_var_heap, rcs_expr_heap))
where
	select_unused_free_variable depth var=:{cv_variable = var_ptr, cv_count = var_count} (collected_vars, var_heap)
		# (VI_LetVar info=:{lvi_count,lvi_depth}, var_heap) = readPtr var_ptr var_heap
		| lvi_depth == depth && lvi_count > 0
			= (collected_vars, var_heap <:= (var_ptr, VI_LetVar {info & lvi_count = max lvi_count var_count}))
		// otherwise
			= ([ var : collected_vars], var_heap) 
	
	get_ref_count var_ptr var_heap
		# (VI_LetVar {lvi_count}, var_heap) = readPtr var_ptr var_heap
		= ({cv_variable = var_ptr, cv_count = lvi_count}, var_heap)

	collect_free_variable depth var_ptr (collected_vars, var_heap)
		# (VI_LetVar lvi=:{lvi_count,lvi_depth,lvi_previous}, var_heap) = readPtr var_ptr var_heap
		| depth == lvi_depth
			= case lvi_previous of
				[{plvi_depth, plvi_count, plvi_new} : lvi_previous ]
					-> ([ {cv_variable = var_ptr, cv_count = lvi_count} : collected_vars ],
						(var_heap <:= (var_ptr, VI_LetVar {lvi & lvi_count = plvi_count, lvi_depth = plvi_depth,
																 lvi_new = plvi_new, lvi_previous = lvi_previous})))
				[]
					-> (collected_vars, var_heap)
			= ([ {cv_variable = var_ptr, cv_count = lvi_count} : collected_vars ], var_heap)
		
/*
	Here we examine the appplication to see whether an imported function has been used. If so, the 'ft_type_ptr' is examined. Initially
	this pointer contains VI_Empty. After the first occurrence the pointer will be set to 'VI_Used'.

*/
checkImportOfDclFunction :: CheckImportedInfo Int Int *RCState -> *RCState
checkImportOfDclFunction {cii_main_dcl_module_n, cii_dcl_functions} mod_index fun_index rcs=:{rcs_imports, rcs_var_heap}
//	| mod_index <> cIclModIndex
	| mod_index <> cii_main_dcl_module_n
		# {ft_type_ptr} = cii_dcl_functions.[mod_index].[fun_index]
		  (rcs_imports, rcs_var_heap) = checkImportedSymbol (SK_Function {glob_module=mod_index,glob_object=fun_index}) ft_type_ptr (rcs_imports, rcs_var_heap)
		= { rcs & rcs_imports = rcs_imports, rcs_var_heap = rcs_var_heap }
	// otherwise
		= rcs
checkRecordSelector {cii_main_dcl_module_n, cii_common_defs} {glob_module, glob_object={ds_index}} rcs=:{rcs_imports,rcs_var_heap}
	| glob_module <> cii_main_dcl_module_n
		# {com_selector_defs,com_cons_defs,com_type_defs} = cii_common_defs.[glob_module]
		  {sd_type_index} = com_selector_defs.[ds_index]
		  {td_rhs = RecordType {rt_constructor={ds_index=cons_index}, rt_fields}} = com_type_defs.[sd_type_index]
		  {cons_type_ptr} = com_cons_defs.[cons_index]
		  (rcs_imports, rcs_var_heap) = checkImportedSymbol (SK_Constructor {glob_module = glob_module, glob_object = cons_index})
											cons_type_ptr (rcs_imports, rcs_var_heap)
		= { rcs & rcs_imports = rcs_imports, rcs_var_heap = rcs_var_heap }
	// otherwise
		= rcs
	


instance weightedRefCount App
where
	weightedRefCount rci=:{rci_imported} {app_symb,app_args} rcs
		# rcs = weightedRefCount rci app_args rcs
		= check_import rci_imported app_symb rcs
	where
		check_import cci {symb_kind=SK_Function {glob_module,glob_object}} rcs=:{rcs_imports, rcs_var_heap}
			= checkImportOfDclFunction cci glob_module glob_object rcs
		check_import cci=:{cii_dcl_functions, cii_common_defs, cii_main_dcl_module_n} {symb_name,symb_kind=symb_kind=:(SK_Constructor {glob_module,glob_object})} rcs=:{rcs_imports, rcs_var_heap}
			| glob_module <> cii_main_dcl_module_n
				# {cons_type_ptr} = cii_common_defs.[glob_module].com_cons_defs.[glob_object]
				  (rcs_imports, rcs_var_heap) = checkImportedSymbol symb_kind cons_type_ptr (rcs_imports, rcs_var_heap)
				= { rcs & rcs_imports = rcs_imports, rcs_var_heap = rcs_var_heap }
				= rcs
		check_import _ _ rcs
			= rcs


instance weightedRefCount TypeCodeExpression
where
	weightedRefCount rci type_code_expr rcs
		= rcs

instance weightedRefCount [a] | weightedRefCount a
where
	weightedRefCount rci l rcs = foldr (weightedRefCount rci) rcs l 
		
instance weightedRefCount (a,b) | weightedRefCount a & weightedRefCount b
where
	weightedRefCount rci (x,y) rcs = weightedRefCount rci y (weightedRefCount rci x rcs) 

instance weightedRefCount LetBind
where
	weightedRefCount rci {lb_src} rcs
		= weightedRefCount rci lb_src rcs

instance weightedRefCount (Bind a b) | weightedRefCount a
where
	weightedRefCount rci bind=:{bind_src} rcs
		= weightedRefCount rci bind_src rcs


/*
	distributeLets tries to move shared expressions as close as possible to the location at which they are used.
	Case-expressions may require unsharing if the shared expression is used in different alternatives. Of course
	only if the expression is neither used in the pattern nor in a surrounding expression.
*/

::	DistributeState =
	{	ds_lets			:: ![VarInfoPtr]
	,	ds_var_heap		:: !.VarHeap
	,	ds_expr_heap	:: !.ExpressionHeap
	}

class distributeLets e :: !Int !e !*DistributeState -> (!e, !*DistributeState)


instance distributeLets Expression
where
	distributeLets depth (Var var=:{var_name,var_info_ptr}) ds=:{ds_var_heap}
		#! var_info = sreadPtr var_info_ptr ds_var_heap
		= case var_info of
			VI_LetExpression lei
				| lei.lei_count == 1
//						 ==> (var_name, var_info_ptr, lei.lei_count, (lei.lei_expression, lei.lei_depth, depth))
					# (lei_updated_expr, ds) = distributeLets depth lei.lei_expression ds
					-> (lei_updated_expr, { ds &  ds_var_heap = ds.ds_var_heap <:=
							(var_info_ptr, VI_LetExpression { lei & lei_status = LES_Updated lei_updated_expr }) })
				| lei.lei_depth == depth
					# ds = distributeLetsInLetExpression depth var_info_ptr lei ds
					-> (Var { var & var_info_ptr = lei.lei_var.fv_info_ptr }, ds)
				// otherwise
					-> (Var { var & var_info_ptr = lei.lei_var.fv_info_ptr }, ds)
			VI_CaseVar var_info_ptr
				-> (Var { var & var_info_ptr = var_info_ptr }, ds)
			_
				-> (Var var, ds)
	distributeLets depth (Case kees) ds
		# (kees, ds) = distributeLets depth kees ds
		= (Case kees, ds)
	distributeLets depth (App app=:{app_args}) ds
		# (app_args, ds) = distributeLets depth app_args ds
		= (App {app & app_args = app_args}, ds)
	distributeLets depth (fun_expr @ exprs) ds
		# (fun_expr, ds) = distributeLets depth fun_expr ds
		  (exprs, ds) = distributeLets depth exprs ds
		= (fun_expr @ exprs, ds)
	distributeLets depth expr=:(BasicExpr _ _) ds
		= (expr, ds)
	distributeLets depth (MatchExpr opt_tuple constructor expr) ds
		# (expr, ds) = distributeLets depth expr ds
		= (MatchExpr opt_tuple constructor expr, ds)
	distributeLets depth (Selection opt_tuple expr selectors) ds
		# (expr, ds) = distributeLets depth expr ds
		# (selectors, ds) = distributeLets depth selectors ds
		= (Selection opt_tuple expr selectors, ds)
	distributeLets depth (Update expr1 selectors expr2) ds
		# (expr1, ds) = distributeLets depth expr1 ds
		# (selectors, ds) = distributeLets depth selectors ds
		# (expr2, ds) = distributeLets depth expr2 ds
		= (Update expr1 selectors expr2, ds)
	distributeLets depth (RecordUpdate cons_symbol expression expressions) ds
		# (expression, ds) = distributeLets depth expression ds
		# (expressions, ds) = distributeLets depth expressions ds
		= (RecordUpdate cons_symbol expression expressions, ds)
	distributeLets depth (TupleSelect tuple_symbol arg_nr expr) ds
		# (expr, ds) = distributeLets depth expr ds
		= (TupleSelect tuple_symbol arg_nr expr, ds)
	distributeLets depth (Let lad=:{let_strict_binds,let_lazy_binds,let_expr,let_info_ptr}) ds=:{ds_expr_heap,ds_var_heap}
		# (let_info, ds_expr_heap) = readPtr let_info_ptr ds_expr_heap
		# (EI_LetTypeAndRefCounts let_type ref_counts) = let_info
		  nr_of_strict_lets = length let_strict_binds
		  let_binds = [(False, bind) \\ bind <- let_lazy_binds]
		  ds_var_heap = set_let_expression_info depth let_binds ref_counts (drop nr_of_strict_lets let_type) ds_var_heap
		  (let_expr, ds) = distributeLets depth let_expr { ds & ds_var_heap = ds_var_heap, ds_expr_heap = ds_expr_heap }
		  (let_strict_binds, ds) = distributeLets depth let_strict_binds ds
		  ds = foldSt (distribute_lets_in_non_distributed_let depth) let_lazy_binds ds
		| nr_of_strict_lets == 0
		    = (let_expr, ds)
		// otherwise
		    = case let_expr of
		    	Let inner_let=:{let_info_ptr=inner_let_info_ptr}
		    		# (EI_LetType strict_inner_types, ds_expr_heap) = readPtr inner_let_info_ptr ds.ds_expr_heap
		    		  ds_expr_heap = writePtr inner_let_info_ptr (EI_LetType ((take nr_of_strict_lets let_type)++strict_inner_types)) ds_expr_heap
					-> (Let { inner_let & let_strict_binds = let_strict_binds++inner_let.let_strict_binds}, 
						{ds & ds_expr_heap = ds_expr_heap})
				_	-> (Let { lad & let_strict_binds = let_strict_binds, let_expr = let_expr, let_lazy_binds = []}, 
						{ds & ds_expr_heap = ds.ds_expr_heap <:= (let_info_ptr, EI_LetType (take nr_of_strict_lets let_type))})
	where
		set_let_expression_info depth [(let_strict, {lb_src,lb_dst}):binds][ref_count:ref_counts][type:types] var_heap
			# (new_info_ptr, var_heap) = newPtr VI_Empty var_heap
			  lei = { lei_count = ref_count, lei_depth = depth, lei_var = { lb_dst & fv_info_ptr = new_info_ptr },
			  			lei_expression = lb_src, lei_type = type, lei_status = LES_Untouched }
			= set_let_expression_info depth binds ref_counts types (var_heap <:= (lb_dst.fv_info_ptr, VI_LetExpression lei))
		set_let_expression_info depth [] _ _ var_heap
			= var_heap
		
		distribute_lets_in_non_distributed_let depth {lb_dst={fv_name,fv_info_ptr}} ds=:{ds_var_heap}
			# (VI_LetExpression lei=:{lei_depth,lei_count,lei_status}, ds_var_heap) = readPtr fv_info_ptr ds_var_heap
			| lei_count > 0
//			| not lei_moved && lei_count > 0
				= distributeLetsInLetExpression depth fv_info_ptr lei { ds & ds_var_heap = ds_var_heap }
			// otherwise
				= { ds & ds_var_heap = ds_var_heap }
					==> ("distribute_lets_in_non_distributed_let (moved or not used)", lei_count, fv_name)

		is_moved LES_Moved	= True
		is_moved _ 			= False

	distributeLets depth expr=:(TypeCodeExpression _) ds
		= (expr, ds)
	distributeLets depth (AnyCodeExpr in_params out_params code_expr) ds=:{ds_var_heap}
		# (in_params, ds_var_heap) = mapSt determineInputParameter in_params ds_var_heap
		= (AnyCodeExpr in_params out_params code_expr, { ds & ds_var_heap = ds_var_heap })
		where
			determineInputParameter bind=:{bind_dst} var_heap
				# (var_info, var_heap) = readPtr bind_dst.var_info_ptr var_heap
				= case var_info of
					VI_CaseVar new_info_ptr
						-> ({ bind & bind_dst = { bind_dst & var_info_ptr = new_info_ptr }}, var_heap)
					_
						-> (bind, var_heap)

	distributeLets depth expr=:(ABCCodeExpr _ _) ds
		= (expr, ds)
	distributeLets depth EE ds
		= (EE, ds)
	distributeLets depth (NoBind ptr) ds
		= (NoBind ptr, ds)

instance distributeLets Case
where 
	distributeLets depth kees=:{case_info_ptr,case_guards,case_default,case_expr} ds=:{ds_var_heap, ds_expr_heap}	
		# (EI_CaseTypeAndRefCounts case_type { rcc_all_variables = tot_ref_counts , rcc_default_variables = ref_counts_in_default, rcc_pattern_variables = ref_counts_in_patterns }, ds_expr_heap) = readPtr case_info_ptr ds_expr_heap
//		  ds_expr_heap = ds_expr_heap <:= (case_info_ptr, EI_CaseType case_type)
		  new_depth = inc depth
		  (local_lets, ds_var_heap) = foldSt (mark_local_let_var new_depth) tot_ref_counts ([], ds_var_heap)
		  (case_guards, heaps) = distribute_lets_in_patterns new_depth ref_counts_in_patterns case_guards (ds_var_heap, ds_expr_heap)
		  (case_default, (ds_var_heap, ds_expr_heap)) = distribute_lets_in_default new_depth ref_counts_in_default case_default heaps
		  ds_var_heap = foldSt reset_local_let_var local_lets ds_var_heap
		  (case_expr, ds) = distributeLets depth case_expr { ds & ds_var_heap = ds_var_heap, ds_expr_heap = ds_expr_heap }
		= ({ kees & case_guards = case_guards, case_expr = case_expr, case_default = case_default }, ds)
	where
		distribute_lets_in_patterns depth ref_counts (AlgebraicPatterns conses patterns) heaps
			# (patterns, heaps) = mapSt (distribute_lets_in_alg_pattern depth) (exactZip ref_counts patterns) heaps
			= (AlgebraicPatterns conses patterns, heaps)
		where
			distribute_lets_in_alg_pattern depth (ref_counts,pattern) (ds_var_heap, ds_expr_heap)
				# (ap_vars, ds_var_heap) = mapSt refresh_variable pattern.ap_vars ds_var_heap
				  (ap_expr, heaps) = distribute_lets_in_pattern_expr depth ref_counts pattern.ap_expr (ds_var_heap, ds_expr_heap)
				= ({ pattern & ap_vars = ap_vars, ap_expr = ap_expr }, heaps) 
		distribute_lets_in_patterns depth ref_counts (BasicPatterns type patterns) heaps
			# (patterns, heaps) = mapSt (distribute_lets_in_basic_pattern depth) (exactZip ref_counts patterns) heaps
			= (BasicPatterns type patterns, heaps)
		where
			distribute_lets_in_basic_pattern depth (ref_counts,pattern) heaps
				# (bp_expr, heaps) = distribute_lets_in_pattern_expr depth ref_counts pattern.bp_expr heaps
				= ({ pattern & bp_expr = bp_expr }, heaps) 
		distribute_lets_in_patterns depth ref_counts (DynamicPatterns patterns) heaps
			# (patterns, heaps) = mapSt (distribute_lets_in_dynamic_pattern depth) (exactZip ref_counts patterns) heaps
			= (DynamicPatterns patterns, heaps)
		where
			distribute_lets_in_dynamic_pattern depth (ref_counts,pattern) (ds_var_heap, ds_expr_heap)
				# (dp_var, ds_var_heap) = refresh_variable pattern.dp_var ds_var_heap
				  (dp_rhs, heaps) = distribute_lets_in_pattern_expr depth ref_counts pattern.dp_rhs (ds_var_heap, ds_expr_heap)
				= ({ pattern & dp_rhs = dp_rhs, dp_var = dp_var }, heaps) 
				
		distribute_lets_in_default depth ref_counts_in_default (Yes expr) heaps
			# (expr, heaps) = distribute_lets_in_pattern_expr depth ref_counts_in_default expr heaps
			= (Yes expr, heaps)
		distribute_lets_in_default depth ref_counts_in_default No heaps
			= (No, heaps)

		refresh_variable fv=:{fv_info_ptr} var_heap
			# (new_info_ptr, var_heap) = newPtr VI_Empty var_heap
			= ({ fv & fv_info_ptr = new_info_ptr }, var_heap <:= (fv_info_ptr, VI_CaseVar new_info_ptr))

		mark_local_let_var depth {cv_variable, cv_count} (local_vars, var_heap)
			# (VI_LetExpression lei=:{lei_count,lei_depth}, var_heap) = readPtr cv_variable var_heap
			| lei_count == cv_count 
				= ([(cv_variable, lei_count, lei_depth) : local_vars ], var_heap <:= (cv_variable, VI_LetExpression { lei & lei_depth = depth}))
						==> ("mark_local_let_var ", lei.lei_var.fv_name, cv_variable, (lei.lei_var.fv_info_ptr, cv_count, depth))
			// otherwise
				= (local_vars, var_heap)

		reset_local_let_var (var_info_ptr, lei_count, lei_depth)  var_heap
			# (VI_LetExpression lei, var_heap) = readPtr var_info_ptr var_heap
			= var_heap <:= (var_info_ptr, VI_LetExpression { lei & lei_depth = lei_depth, lei_count = lei_count, lei_status = LES_Moved })

		distribute_lets_in_pattern_expr depth local_vars pattern_expr (var_heap, expr_heap)
			# var_heap = foldSt (mark_local_let_var_of_pattern_expr depth) local_vars var_heap
			  (pattern_expr, ds) = distributeLets depth pattern_expr { ds_lets = [], ds_var_heap = var_heap, ds_expr_heap = expr_heap}
			  ds = foldSt (reexamine_local_let_expressions depth) local_vars ds
			= buildLetExpr ds.ds_lets pattern_expr (ds.ds_var_heap, ds.ds_expr_heap)
				==> ("distribute_lets_in_pattern_expr", ds.ds_lets)
	
		mark_local_let_var_of_pattern_expr depth {cv_variable, cv_count} var_heap
			# (VI_LetExpression lei, var_heap) = readPtr cv_variable var_heap
			| depth == lei.lei_depth
				= (var_heap <:= (cv_variable, VI_LetExpression { lei & lei_count = cv_count, lei_status = LES_Untouched }))
						==> ("mark_local_let_var_of_pattern_expr ", lei.lei_var.fv_name, cv_variable, (lei.lei_var.fv_info_ptr, cv_count, depth))
			// otherwise
				= var_heap

		reexamine_local_let_expressions depth {cv_variable, cv_count} ds=:{ds_var_heap}
			| cv_count > 1
				# (VI_LetExpression lei, ds_var_heap) = readPtr cv_variable ds_var_heap
				| depth == lei.lei_depth
					= distributeLetsInLetExpression depth cv_variable lei { ds & ds_var_heap = ds_var_heap }
				// otherwise
					= { ds & ds_var_heap = ds_var_heap }
			// otherwise
				= ds

distributeLetsInLetExpression :: Int VarInfoPtr LetExpressionInfo *DistributeState -> *DistributeState
distributeLetsInLetExpression depth let_var_info_ptr lei=:{lei_expression, lei_status = LES_Moved} ds
	= ds
distributeLetsInLetExpression depth let_var_info_ptr lei=:{lei_expression, lei_status = LES_Updated _} ds
	= ds
distributeLetsInLetExpression depth let_var_info_ptr lei=:{lei_expression, lei_status = LES_Untouched} ds=:{ds_var_heap}
	# ds_var_heap = ds_var_heap <:= (let_var_info_ptr, VI_LetExpression { lei & lei_status = LES_Updated EE}) /* to prevent doing this expression twice */
      (lei_expression, ds) = distributeLets depth lei_expression { ds & ds_var_heap = ds_var_heap }
	= { ds & ds_lets = [ let_var_info_ptr : ds.ds_lets ],
		 ds_var_heap = ds.ds_var_heap <:= (let_var_info_ptr, VI_LetExpression { lei & lei_status = LES_Updated lei_expression })}

	
buildLetExpr :: ![VarInfoPtr] !Expression !*(!*VarHeap, !*ExpressionHeap) -> (!Expression, !(!*VarHeap, !*ExpressionHeap))
buildLetExpr let_vars let_expr (var_heap, expr_heap)
	# (lazy_binds, lazy_binds_types, var_heap) = foldr build_bind ([], [], var_heap) let_vars
	| isEmpty lazy_binds
		= (let_expr, (var_heap, expr_heap))
	// otherwise
		= case let_expr of
			Let inner_let=:{let_info_ptr }
				# (EI_LetType strict_bind_types, expr_heap) = readPtr let_info_ptr expr_heap
				  expr_heap = writePtr let_info_ptr (EI_LetType (strict_bind_types ++ lazy_binds_types)) expr_heap
				-> (Let { inner_let & let_lazy_binds = lazy_binds }, (var_heap, expr_heap))
			_
				# (let_info_ptr, expr_heap) = newPtr (EI_LetType lazy_binds_types) expr_heap
				-> (Let { let_strict_binds = [], let_lazy_binds = lazy_binds, let_expr = let_expr,
						let_info_ptr = let_info_ptr, let_expr_position = NoPos }, (var_heap, expr_heap))
where
	build_bind :: !VarInfoPtr !(![LetBind], ![AType], !*VarHeap)
		-> (![LetBind], ![AType], !*VarHeap)
	build_bind info_ptr (lazy_binds, lazy_binds_types, var_heap)
		# (let_info, var_heap) = readPtr info_ptr var_heap
		# (VI_LetExpression lei=:{lei_var,lei_expression,lei_status,lei_type}) = let_info
		  (LES_Updated updated_expr) = lei_status
		  (new_info_ptr, var_heap) = newPtr VI_Empty var_heap 
		  var_heap = var_heap <:= (info_ptr, VI_LetExpression { lei & lei_status = LES_Untouched, lei_var = { lei_var & fv_info_ptr = new_info_ptr }})
		= ([{ lb_src = updated_expr, lb_dst = lei_var, lb_position = NoPos } : lazy_binds], [lei_type : lazy_binds_types ], var_heap)

instance distributeLets Selection
where
	distributeLets depth (ArraySelection selector expr_ptr expr) cp_state
		# (expr, cp_state) = distributeLets depth expr cp_state
		= (ArraySelection selector expr_ptr expr, cp_state)
	distributeLets depth (DictionarySelection var selectors expr_ptr expr) cp_state
		# (selectors, cp_state) = distributeLets depth selectors cp_state
		# (expr, cp_state) = distributeLets depth expr cp_state
		= (DictionarySelection var selectors expr_ptr expr, cp_state)
	distributeLets depth selection cp_state
		= (selection, cp_state)

instance distributeLets [a] | distributeLets a
where
	distributeLets depth l cp_state = mapSt (distributeLets depth) l cp_state 

instance distributeLets LetBind
where
	distributeLets depth bind=:{lb_src} cp_state
		# (lb_src, cp_state) = distributeLets depth lb_src cp_state
		= ({ bind & lb_src = lb_src }, cp_state)
	
instance distributeLets (Bind a b) | distributeLets a
where
	distributeLets depth bind=:{bind_src} cp_state
		# (bind_src, cp_state) = distributeLets depth bind_src cp_state
		= ({ bind & bind_src = bind_src }, cp_state)

newFunction :: !(Optional Ident) !FunctionBody ![FreeVar] ![AType] !AType !Int !(!Int, ![FunctionInfoPtr],!*FunctionHeap)
	-> (! SymbIdent, !(!Int, ![FunctionInfoPtr],!*FunctionHeap))
newFunction opt_id fun_bodies local_vars arg_types result_type group_index (cs_next_fun_nr, cs_new_functions, cs_fun_heap)
	# (fun_def_ptr, cs_fun_heap) = newPtr FI_Empty cs_fun_heap
	  fun_id = getIdent opt_id cs_next_fun_nr
	  arity = length arg_types
	  fun_type =
	  	{	st_vars			= []
		,	st_args			= arg_types
		,	st_arity		= arity
		,	st_result		= result_type
		,	st_context		= []
		,	st_attr_vars	= []
		,	st_attr_env		= []
		}

	  fun_def = 
			{	fun_symb		= fun_id
			,	fun_arity		= arity
			,	fun_priority	= NoPrio
			,	fun_body		= fun_bodies
			,	fun_type		= Yes fun_type
			,	fun_pos			= NoPos
			,	fun_index		= NoIndex
			,	fun_kind		= FK_ImpFunction cNameNotLocationDependent
			,	fun_lifted		= 0
			,	fun_info		= { EmptyFunInfo & fi_group_index = group_index, fi_local_vars = local_vars }
			}
	= ({ symb_name = fun_id, symb_kind = SK_GeneratedFunction fun_def_ptr cs_next_fun_nr, symb_arity = arity },
			(inc cs_next_fun_nr, [fun_def_ptr : cs_new_functions],
				cs_fun_heap <:= (fun_def_ptr,  FI_Function { gf_fun_def = fun_def, gf_instance_info = II_Empty,
	  				  gf_fun_index = cs_next_fun_nr, gf_cons_args = {cc_size=0, cc_args = [], cc_linear_bits = []} })))

addNewFunctionsToGroups :: !{#.CommonDefs} FunctionHeap ![FunctionInfoPtr] !Int !*{! Group} !*{#{# CheckedTypeDef}} !ImportedFunctions !*TypeHeaps !*VarHeap
	-> (!*{! Group}, ![FunDef],  !*{#{# CheckedTypeDef}}, !ImportedConstructors, !*TypeHeaps, !*VarHeap)
addNewFunctionsToGroups common_defs fun_heap new_functions main_dcl_module_n groups imported_types imported_conses type_heaps var_heap
	= foldSt (add_new_function_to_group fun_heap common_defs) new_functions (groups, [], imported_types, imported_conses, type_heaps, var_heap)
where

	add_new_function_to_group :: !FunctionHeap  !{# CommonDefs} !FunctionInfoPtr
				!(!*{! Group}, ![FunDef], !*{#{# CheckedTypeDef}}, !ImportedConstructors, !*TypeHeaps, !*VarHeap)
					-> (!*{! Group}, ![FunDef],  !*{#{# CheckedTypeDef}}, !ImportedConstructors, !*TypeHeaps, !*VarHeap)
	add_new_function_to_group fun_heap common_defs fun_ptr (groups, fun_defs, imported_types, imported_conses, type_heaps, var_heap)
		# (FI_Function {gf_fun_def,gf_fun_index}) = sreadPtr fun_ptr fun_heap
		  {fun_type = Yes ft, fun_info = {fi_group_index, fi_properties}} = gf_fun_def
		  (Yes ft) = gf_fun_def.fun_type
		  (ft, imported_types, imported_conses, type_heaps, var_heap)
		  		= convertSymbolType (fi_properties bitand FI_HasTypeSpec == 0) common_defs ft main_dcl_module_n
		  		 			imported_types imported_conses type_heaps var_heap
		# (group, groups) = groups![fi_group_index]
		= ({ groups & [fi_group_index] = { group & group_members = [gf_fun_index : group.group_members]} },
				[ { gf_fun_def & fun_type = Yes ft }: fun_defs], imported_types, imported_conses, type_heaps, var_heap)


:: ConvertInfo =
	{	ci_bound_vars :: ![(FreeVar, AType)]
	,	ci_group_index :: !Index
	,	ci_common_defs :: !{#CommonDefs}
	}

::	ConvertState =
	{	cs_new_functions 	:: ![FunctionInfoPtr]
	,	cs_fun_heap			:: !.FunctionHeap
	,	cs_var_heap			:: !.VarHeap
	,	cs_expr_heap		:: !.ExpressionHeap
	,	cs_next_fun_nr		:: !Index
	}



convertRootExpression ci default_ptr (Let lad=:{let_strict_binds,let_lazy_binds,let_expr,let_info_ptr}) cs=:{cs_expr_heap}
	# (EI_LetType let_type, cs_expr_heap) = readPtr let_info_ptr cs_expr_heap
	  bound_vars = addLetVars (let_strict_binds ++ let_lazy_binds) let_type ci.ci_bound_vars
	  ci = {ci & ci_bound_vars=bound_vars}
	  (let_strict_binds, cs)	= convertCases ci let_strict_binds { cs & cs_expr_heap = cs_expr_heap }
	  (let_lazy_binds, cs)		= convertCases ci let_lazy_binds cs
	  (let_expr, cs)			= convertRootExpression ci default_ptr let_expr cs
	= (Let { lad & let_strict_binds = let_strict_binds, let_lazy_binds = let_lazy_binds, let_expr = let_expr }, cs)
convertRootExpression ci default_ptr (Case kees=:{case_expr, case_guards, case_default, case_info_ptr}) cs
	= case case_guards of
		BasicPatterns BT_Bool patterns
			-> convert_boolean_case_into_guard ci default_ptr case_expr patterns case_default case_info_ptr cs
		_
			-> convertCasesInCaseExpression ci default_ptr kees cs

where

//	convert_boolean_case_into_guard bound_vars  group_index common_defs default_ptr guard [ alt : alts ] case_default case_info_ptr cs
	convert_boolean_case_into_guard ci has_default guard [ alt=:{bp_value=BVB sign_of_then_part,bp_expr} : alts ] case_default case_info_ptr cs
		# (guard, cs) = convertRootExpression ci cHasNoDefault guard cs
		# (EI_CaseTypeAndRefCounts case_type _, cs_expr_heap) = readPtr case_info_ptr cs.cs_expr_heap
		# (default_ptr, cs_expr_heap) = makePtrToDefault case_default case_type.ct_result_type has_default cs_expr_heap
		# (then_part, cs) = convertRootExpression ci default_ptr bp_expr {cs &cs_expr_heap=cs_expr_heap}
		# (opt_else_part, cs) = convert_to_else_part ci default_ptr sign_of_then_part alts case_default cs
//		= (Conditional { if_cond = { con_positive = sign_of_then_part, con_expression = guard }, if_then = then_part, if_else = opt_else_part }, cs)
		= (build_conditional sign_of_then_part guard then_part opt_else_part, cs)
	where
		build_conditional True guard then_expr opt_else_expr
			= Conditional { if_cond = guard, if_then = then_expr, if_else = opt_else_expr }
		build_conditional false guard then_expr (Yes else_expr)
			= Conditional { if_cond = guard, if_then = else_expr, if_else = Yes then_expr }
		build_conditional false guard then_expr No
			= Conditional { if_cond = Conditional { if_cond = guard, if_then = BasicExpr (BVB False) BT_Bool, if_else = Yes (BasicExpr (BVB True) BT_Bool) },
								if_then = then_expr, if_else = No }

		convert_to_else_part ci default_ptr sign_of_then_part [ alt=:{bp_value=BVB sign_of_else_part,bp_expr} : alts ] case_default cs
			# (else_part, cs) = convertRootExpression ci default_ptr bp_expr cs
			| sign_of_then_part == sign_of_else_part
				= convert_to_else_part ci default_ptr sign_of_then_part alts case_default cs
				= (Yes else_part, cs)
		convert_to_else_part ci default_ptr sign_of_then_part [ ] (Yes else_part) cs
			# (else_part, cs) = convertRootExpression ci has_default else_part cs
			= (Yes else_part, cs)
		convert_to_else_part ci default_ptr sign_of_then_part [ ] No cs
			= (No, cs)

convertRootExpression ci _ expr cs
	= convertCases ci expr cs

class convertCases a :: !ConvertInfo !a  !*ConvertState -> (!a, !*ConvertState)

instance convertCases [a] | convertCases a
where
	convertCases ci l cs = mapSt (convertCases ci) l cs 

instance convertCases (a,b) | convertCases a & convertCases b
where
	convertCases ci t cs
		= app2St (convertCases ci, convertCases ci) t cs

instance convertCases LetBind
where
	convertCases ci bind=:{lb_src} cs
		# (lb_src, cs) = convertCases ci lb_src cs
		= ({ bind & lb_src = lb_src }, cs)

instance convertCases (Bind a b) | convertCases a
where
	convertCases ci bind=:{bind_src} cs
		# (bind_src, cs) = convertCases ci bind_src cs
		= ({ bind & bind_src = bind_src }, cs)

instance convertCases Let
where
	convertCases ci lad=:{let_strict_binds,let_lazy_binds,let_expr,let_info_ptr} cs=:{cs_expr_heap}
		# (let_info, cs_expr_heap) =  readPtr let_info_ptr cs_expr_heap
		  cs = { cs & cs_expr_heap = cs_expr_heap }
		= case let_info of
			EI_LetType let_type
				# ci = {ci & ci_bound_vars=addLetVars (let_strict_binds ++ let_lazy_binds) let_type ci.ci_bound_vars}
				# (let_strict_binds, cs) = convertCases ci let_strict_binds cs
				# (let_lazy_binds, cs) = convertCases ci let_lazy_binds cs
				# (let_expr, cs) = convertCases ci let_expr cs
				-> ({ lad & let_strict_binds = let_strict_binds, let_lazy_binds = let_lazy_binds, let_expr = let_expr }, cs)
			_
				-> abort "convertCases [Let] (convertcases 53)" // <<- let_info 

instance convertCases Expression  
where
	convertCases ci (App app=:{app_args}) cs
		# (app_args, cs) = convertCases ci app_args cs
		= (App {app & app_args = app_args}, cs)
	convertCases ci (fun_expr @ exprs) cs
		# ((fun_expr, exprs), cs) = convertCases ci (fun_expr, exprs) cs
		= (fun_expr @ exprs, cs)
	convertCases ci (Let lad) cs
		# (lad, cs) = convertCases ci lad cs
		= (Let lad, cs)
	convertCases ci (MatchExpr opt_tuple constructor expr) cs
		# (expr, cs) = convertCases ci expr cs
		= (MatchExpr opt_tuple constructor expr, cs)
	convertCases ci (Selection is_unique expr selectors) cs
		# (expr, cs) = convertCases ci expr cs
		  (selectors, cs) = convertCases ci selectors cs
		= (Selection is_unique expr selectors, cs)		
	convertCases ci (Update expr1 selectors expr2) cs
		# (expr1, cs) = convertCases ci expr1 cs
		  (selectors, cs) = convertCases ci selectors cs
		  (expr2, cs) = convertCases ci expr2 cs
		= (Update expr1 selectors expr2, cs)		
	convertCases ci (RecordUpdate cons_symbol expression expressions) cs
		# (expression, cs) = convertCases ci expression cs
		  (expressions, cs) = convertCases ci expressions cs
		= (RecordUpdate cons_symbol expression expressions, cs)		
	convertCases ci (TupleSelect tuple_symbol arg_nr expr) cs
		# (expr, cs) = convertCases ci expr cs
		= (TupleSelect tuple_symbol arg_nr expr, cs)
	convertCases ci (Case case_expr) cs
		= convertCasesInCaseExpression ci cHasNoDefault case_expr cs
	convertCases ci expr cs
		= (expr, cs)

instance convertCases Selection  
where
	convertCases ci (DictionarySelection record selectors expr_ptr index_expr) cs
		# (index_expr, cs) = convertCases ci index_expr cs
		  (selectors, cs) = convertCases ci selectors cs
		= (DictionarySelection record selectors expr_ptr index_expr, cs)
	convertCases ci (ArraySelection selector expr_ptr index_expr) cs
		# (index_expr, cs) = convertCases ci index_expr cs
		= (ArraySelection selector expr_ptr index_expr, cs)
	convertCases ci selector cs
		= (selector, cs)

cHasNoDefault :== nilPtr

convertDefaultToExpression default_ptr (EI_Default expr type prev_default) ci cs=:{cs_var_heap}
    # cs_var_heap = foldSt (\({fv_info_ptr}, type) -> writePtr fv_info_ptr (VI_BoundVar type)) ci.ci_bound_vars cs_var_heap
	  (expression, {cp_free_vars, cp_var_heap, cp_local_vars}) = copy expr { cp_free_vars = [], cp_var_heap = cs_var_heap, cp_local_vars = [] }
	  (act_args, free_typed_vars, cs_var_heap) = foldSt retrieveVariable cp_free_vars ([], [], cp_var_heap)
	  (fun_symb, cs) = new_default_function free_typed_vars cp_local_vars expression type prev_default ci.ci_group_index ci.ci_common_defs { cs & cs_var_heap = cs_var_heap }
	= (App { app_symb = fun_symb, app_args = act_args, app_info_ptr = nilPtr }, 
		{ cs & cs_expr_heap = cs.cs_expr_heap <:= (default_ptr, EI_DefaultFunction fun_symb act_args)})
where
	new_default_function free_vars local_vars rhs_expr result_type prev_default group_index common_defs cs
		# (guarded_exprs, cs) = convertPatternExpression [] [free_vars] group_index common_defs prev_default rhs_expr cs
		  fun_bodies  = map build_pattern guarded_exprs
		  arg_types = map (\(_,type) -> type) free_vars
		  (fun_symb,  (cs_next_fun_nr, cs_new_functions, cs_fun_heap))
				= newFunction No (BackendBody fun_bodies) local_vars arg_types result_type group_index
						(cs.cs_next_fun_nr, cs.cs_new_functions, cs.cs_fun_heap)
		= (fun_symb, { cs & cs_fun_heap = cs_fun_heap, cs_next_fun_nr = cs_next_fun_nr, cs_new_functions = cs_new_functions })

	build_pattern ([ right_patterns : _ ], bb_rhs)
		= { bb_args = right_patterns, bb_rhs = bb_rhs }

convertDefaultToExpression default_ptr (EI_DefaultFunction fun_symb act_args) ci cs
	= (App { app_symb = fun_symb, app_args = act_args, app_info_ptr = nilPtr }, cs)

combineDefaults default_ptr guards No ci cs=:{cs_expr_heap}
	| isNilPtr default_ptr
		= (No, cs)
	| case_is_partial guards ci.ci_common_defs
		# (default_info, cs_expr_heap) = readPtr default_ptr cs_expr_heap
		  (default_expr, cs) = convertDefaultToExpression default_ptr default_info ci { cs & cs_expr_heap = cs_expr_heap }
		= (Yes default_expr, cs)
		= (No, cs)
where
	case_is_partial (AlgebraicPatterns {glob_module, glob_object} patterns) common_defs
		# {td_rhs} = common_defs.[glob_module].com_type_defs.[glob_object]
		= length patterns < nr_of_alternatives td_rhs || has_partial_pattern patterns
	where
		nr_of_alternatives (AlgType conses)
			= length conses
		nr_of_alternatives _
			= 1

		has_partial_pattern []
			= False
		has_partial_pattern [{ap_expr} : patterns]
			= is_partial_expression ap_expr common_defs || has_partial_pattern patterns
	case_is_partial (BasicPatterns BT_Bool bool_patterns) common_defs
		= length bool_patterns < 2 || has_partial_basic_pattern bool_patterns
	where
		has_partial_basic_pattern []
			= False
		has_partial_basic_pattern [{bp_expr} : patterns]
			= is_partial_expression bp_expr common_defs || has_partial_basic_pattern patterns
	case_is_partial patterns common_defs
		= True
	
	is_partial_expression (Case {case_guards,case_default=No}) common_defs
		= case_is_partial case_guards common_defs
	is_partial_expression (Case {case_guards,case_default=Yes case_default}) common_defs
		= is_partial_expression case_default common_defs && case_is_partial case_guards common_defs
	is_partial_expression (Let {let_expr}) common_defs
		= is_partial_expression let_expr common_defs
	is_partial_expression _ _
		= False

combineDefaults default_ptr guards this_default ci cs
	= (this_default, cs)
	

convertCasesInCaseExpression ci default_ptr { case_expr, case_guards, case_default, case_ident, case_info_ptr} cs
	# (case_default, cs) = combineDefaults default_ptr case_guards case_default ci cs
	  (case_expr, cs) = convertCases ci case_expr cs
	  (EI_CaseTypeAndRefCounts case_type ref_counts, cs_expr_heap) = readPtr case_info_ptr cs.cs_expr_heap
	  (act_vars, form_vars, opt_free_var, local_vars, (case_guards, case_default), cs_var_heap)
			= copy_case_expression ci.ci_bound_vars (get_variable case_expr case_type.ct_pattern_type) (case_guards,case_default) cs.cs_var_heap
	  (fun_symb, cs) = new_case_function case_ident case_guards case_default case_type opt_free_var form_vars local_vars
	  							ci.ci_group_index ci.ci_common_defs default_ptr { cs & cs_var_heap = cs_var_heap, cs_expr_heap = cs_expr_heap }
	= (App { app_symb = fun_symb, app_args = [ case_expr : act_vars ], app_info_ptr = nilPtr }, cs)
where
	get_variable (Var var) pattern_type
		= Yes (var, pattern_type)
	get_variable _ _
		= No
	
	copy_case_expression bound_vars opt_variable guards_and_default var_heap
	    # var_heap = foldSt (\({fv_name,fv_info_ptr},type) -> writePtr fv_info_ptr (VI_BoundVar type)) bound_vars var_heap
		  (opt_copied_var, var_heap) = copy_variable opt_variable var_heap
		  (expression, {cp_free_vars, cp_var_heap, cp_local_vars}) = copy guards_and_default { cp_free_vars = [], cp_var_heap = var_heap, cp_local_vars = [] }
		  (bound_vars, free_typed_vars, var_heap) = foldSt retrieveVariable cp_free_vars ([], [], cp_var_heap)
		  (opt_free_var, var_heap) = toOptionalFreeVar opt_copied_var var_heap
		= (bound_vars, free_typed_vars, opt_free_var, cp_local_vars, expression, var_heap)

	copy_variable (Yes (var=:{var_name,var_info_ptr}, var_type)) var_heap
		# (new_info, var_heap) = newPtr VI_Empty var_heap
		= (Yes (var_info_ptr, var_type), var_heap <:= (var_info_ptr, VI_FreeVar var_name new_info 0 var_type))
	copy_variable No var_heap
		= (No, var_heap)

 	new_case_function opt_id patterns case_default {ct_result_type,ct_pattern_type,ct_cons_types} opt_var free_vars local_vars
			group_index common_defs prev_default cs=:{cs_expr_heap}
		# (default_ptr, cs_expr_heap) = makePtrToDefault case_default ct_result_type prev_default cs_expr_heap
		  (fun_bodies, cs) = convertPatterns patterns ct_cons_types opt_var [] free_vars default_ptr group_index common_defs { cs & cs_expr_heap = cs_expr_heap }
		  (fun_bodies, cs) = convertDefault default_ptr opt_var [] free_vars group_index common_defs (fun_bodies, cs)
		  (fun_symb,  (cs_next_fun_nr, cs_new_functions, cs_fun_heap))
				= newFunction opt_id (BackendBody fun_bodies) local_vars [ct_pattern_type : [ type \\ (_, type) <- free_vars]] ct_result_type group_index
						(cs.cs_next_fun_nr, cs.cs_new_functions, cs.cs_fun_heap)
		= (fun_symb, { cs & cs_fun_heap = cs_fun_heap, cs_next_fun_nr = cs_next_fun_nr, cs_new_functions = cs_new_functions })

makePtrToDefault (Yes default_expr) type prev_default_ptr expr_heap
	= newPtr (EI_Default default_expr type prev_default_ptr) expr_heap
makePtrToDefault No type prev_default_ptr expr_heap
	= (cHasNoDefault, expr_heap)

convertDefault default_ptr opt_var left_vars right_vars group_index common_defs (fun_bodies, cs)
	| isNilPtr default_ptr
		= (fun_bodies, cs)
		# (default_info, cs_expr_heap) = readPtr default_ptr cs.cs_expr_heap
		= convert_default default_info opt_var left_vars right_vars group_index common_defs (fun_bodies, { cs & cs_expr_heap = cs_expr_heap})
where
	convert_default (EI_Default default_expr type prev_default) opt_var left_vars right_vars group_index common_defs (fun_bodies, cs)
		# (bb_rhs, cs) = convertRootExpression {ci_bound_vars=left_vars ++ consOptional opt_var right_vars, ci_group_index=group_index, ci_common_defs=common_defs} prev_default default_expr cs
		  bb_args = build_args opt_var left_vars right_vars
		= (fun_bodies ++ [{ bb_args = bb_args, bb_rhs = bb_rhs }], cs)	
	convert_default (EI_DefaultFunction fun_symb act_args) opt_var left_vars right_vars group_index common_defs (fun_bodies, cs)
		# bb_args = build_args opt_var left_vars right_vars
		  bb_rhs = App { app_symb = fun_symb, app_args = act_args, app_info_ptr = nilPtr }
		= (fun_bodies ++ [{ bb_args = bb_args, bb_rhs = bb_rhs }], cs)	

	build_args (Yes (var,type)) left_vars right_vars
		= mapAppend typed_free_var_to_pattern left_vars [FP_Variable var : map typed_free_var_to_pattern right_vars]
	build_args No left_vars right_vars
		= mapAppend typed_free_var_to_pattern left_vars [FP_Empty : map typed_free_var_to_pattern right_vars]

	typed_free_var_to_pattern (free_var, type) = FP_Variable free_var


consOptional (Yes x) xs = [x : xs]
consOptional No xs = xs

getOptionalFreeVar (Yes (free_var,_)) = Yes free_var
getOptionalFreeVar No = No

optionalToListofLists (Yes x)
	= [[x]]
optionalToListofLists No
	= []

hasOption (Yes _)	= True
hasOption No		= False

convertPatterns :: CasePatterns [[AType]] (Optional (FreeVar,AType)) [.(FreeVar,AType)] [(FreeVar,AType)] (Ptr ExprInfo) Index {#CommonDefs} *ConvertState -> *(!.[BackendBody],!*ConvertState);
convertPatterns (AlgebraicPatterns algtype patterns) cons_types opt_var left_vars right_vars default_ptr group_index common_defs cs
	# (guarded_exprs_list, cs) = mapSt (convert_algebraic_guard_into_function_pattern opt_var left_vars right_vars
			group_index common_defs default_ptr) (exactZip patterns cons_types) cs
	= (flatten guarded_exprs_list, cs)
where
	convert_algebraic_guard_into_function_pattern opt_var left_vars right_vars group_index common_defs default_ptr ({ap_symbol, ap_vars, ap_expr}, cons_arg_types) cs
		# pattern_vars = exactZip ap_vars cons_arg_types
		  (guarded_exprs, cs)
				= convertPatternExpression (consOptional opt_var left_vars) [pattern_vars, right_vars] group_index common_defs default_ptr ap_expr cs
		= (map (complete_pattern left_vars ap_symbol (getOptionalFreeVar opt_var)) guarded_exprs, cs)
	where
		complete_pattern left_vars cons_symbol optional_var ([ pattern_args, right_patterns : _ ], bb_rhs)
			# bb_args = mapAppend selectFreeVar left_vars [FP_Algebraic cons_symbol pattern_args optional_var : right_patterns ]
			= { bb_args = bb_args, bb_rhs = bb_rhs }			
convertPatterns (BasicPatterns bastype patterns) cons_types opt_var left_vars right_vars default_ptr group_index common_defs cs
	# (guarded_exprs_list, cs) = mapSt (convert_basic_guard_into_function_pattern opt_var left_vars right_vars
			group_index common_defs default_ptr) patterns cs
	= (flatten guarded_exprs_list, cs)
where
	convert_basic_guard_into_function_pattern opt_var left_vars right_vars group_index common_defs default_ptr {bp_value, bp_expr} cs
		# (guarded_exprs, cs)
				= convertPatternExpression (consOptional opt_var left_vars) [right_vars] group_index common_defs default_ptr bp_expr cs
		= (map (complete_pattern left_vars bp_value (getOptionalFreeVar opt_var)) guarded_exprs, cs)
	where
		complete_pattern left_vars value optional_var ([ right_patterns : _ ], bb_rhs)
			# bb_args = mapAppend selectFreeVar left_vars [FP_Basic value optional_var : right_patterns ]
			= { bb_args = bb_args, bb_rhs = bb_rhs }

convertPatternExpression :: ![(FreeVar,AType)] ![[(FreeVar,AType)]] !Index !{#CommonDefs} !ExprInfoPtr !Expression !*ConvertState
	-> *(![([[FunctionPattern]], !Expression)], !*ConvertState)
convertPatternExpression left_vars right_vars group_index common_defs default_ptr
		case_expr=:(Case {case_expr = Var var=:{var_info_ptr}, case_guards, case_default, case_info_ptr}) cs
	| list_contains_variable var_info_ptr right_vars
		= case case_guards of
			BasicPatterns type basic_patterns
				# split_result = split_list_of_vars var_info_ptr [] right_vars
				  (default_patterns, cs) = convert_default left_vars split_result group_index common_defs case_default cs
				  (guarded_exprs, cs) = mapSt (convert_basic_guard_into_function_pattern left_vars split_result group_index common_defs) basic_patterns cs
				-> (flatten guarded_exprs ++ default_patterns, cs)
			AlgebraicPatterns type algebraic_patterns
				# (EI_CaseTypeAndRefCounts {ct_cons_types} _, cs_expr_heap) = readPtr case_info_ptr cs.cs_expr_heap
		  		  split_result = split_list_of_vars var_info_ptr [] right_vars
				  (default_patterns, cs) = convert_default left_vars split_result group_index common_defs case_default { cs & cs_expr_heap = cs_expr_heap }
				  (guarded_exprs, cs) = mapSt (convert_algebraic_guard_into_function_pattern left_vars split_result group_index common_defs case_info_ptr)
											(exactZip algebraic_patterns ct_cons_types) cs
				-> (flatten guarded_exprs ++ default_patterns, cs)
			_
				-> convertToRhsExpression left_vars right_vars group_index common_defs default_ptr case_expr cs
		= convertToRhsExpression left_vars right_vars group_index common_defs default_ptr case_expr cs
where
	list_contains_variable var_info_ptr []
		= False
	list_contains_variable var_info_ptr [ right_vars : list_of_right_vars ]
		= contains_variable var_info_ptr right_vars || list_contains_variable var_info_ptr list_of_right_vars
	where
		contains_variable var_info_ptr []
			= False
		contains_variable var_info_ptr [ ({fv_info_ptr},_) : right_vars ]
			= var_info_ptr == fv_info_ptr || contains_variable var_info_ptr right_vars
	
	convert_default left_vars ((fv,fv_type), list_of_left, list_of_right) group_index common_defs (Yes default_expr) cs
		# (guarded_exprs, cs)
				= convertPatternExpression (left_vars ++ [ (fv,fv_type) : flatten list_of_left ]) list_of_right group_index common_defs default_ptr default_expr cs
		= (map (complete_pattern list_of_left fv) guarded_exprs, cs) 
	where
		complete_pattern list_of_left this_var (list_of_patterns, expr)
			= (complete_patterns list_of_left (FP_Variable this_var) list_of_patterns, expr)
	convert_default left_vars ((fv,fv_type), list_of_left, list_of_right) group_index common_defs No cs
		= ([], cs)
	
	convert_basic_guard_into_function_pattern left_vars ((fv,fv_type), list_of_left, list_of_right) group_index common_defs {bp_value, bp_expr} cs
		# (guarded_exprs, cs)
				= convertPatternExpression (left_vars ++ [ (fv,fv_type) : flatten list_of_left ]) list_of_right group_index common_defs default_ptr bp_expr cs
		= (map (complete_pattern list_of_left bp_value (Yes fv)) guarded_exprs, cs) 
	where
		complete_pattern list_of_left value opt_var (list_of_patterns, expr)
			= (complete_patterns list_of_left (FP_Basic value opt_var) list_of_patterns, expr)
	
	convert_algebraic_guard_into_function_pattern left_vars ((fv,fv_type), list_of_left, list_of_right) group_index common_defs case_info_ptr
				({ap_symbol, ap_vars, ap_expr}, arg_types) cs=:{cs_expr_heap}
		# (guarded_exprs, cs)
				= convertPatternExpression (left_vars ++ [ (fv,fv_type) : flatten list_of_left ]) [ exactZip ap_vars arg_types : list_of_right ]
						 group_index common_defs default_ptr ap_expr { cs & cs_expr_heap = cs_expr_heap }
		= (map (complete_pattern list_of_left ap_symbol (Yes fv)) guarded_exprs, cs) 
	where
		complete_pattern :: ![[(FreeVar,a)]] !(Global DefinedSymbol) !(Optional !FreeVar) !([[FunctionPattern]], !b) -> (![[FunctionPattern]], !b)
		complete_pattern list_of_left cons_symbol opt_var ([ patterns : list_of_patterns], expr)
			= (complete_patterns list_of_left (FP_Algebraic cons_symbol patterns opt_var) list_of_patterns, expr)

	split_list_of_vars var_info_ptr list_of_left [ vars : list_of_vars ]
		# (fv, left, list_of_left, list_of_right) = split_vars var_info_ptr [] list_of_left vars list_of_vars
		= (fv, [left : list_of_left], list_of_right)
	where
		split_vars var_info_ptr left list_of_left []  list_of_vars 
			# (fv, list_of_left, list_of_right) =  split_list_of_vars var_info_ptr list_of_left list_of_vars 
			= (fv, left, list_of_left, list_of_right)
	
		split_vars var_info_ptr left list_of_left [ this_var=:(fv,_) : vars ] list_of_vars
			| var_info_ptr == fv.fv_info_ptr
				= (this_var, left, list_of_left, [ vars : list_of_vars ])
				= split_vars var_info_ptr [this_var : left] list_of_left vars list_of_vars

	complete_patterns [ left_args ] current_pattern [ right_args : list_of_right_args ]
		= [ add_free_vars left_args [current_pattern : right_args] : list_of_right_args ]
	complete_patterns [ left_args : list_of_left_args ] current_pattern list_of_right_args
		= [ add_free_vars left_args [] : complete_patterns list_of_left_args current_pattern list_of_right_args ]

	add_free_vars [(fv, _) : left_vars] right_vars
		= add_free_vars left_vars [ FP_Variable fv : right_vars ]
	add_free_vars [] right_vars
		= right_vars

convertPatternExpression left_vars right_vars group_index common_defs default_ptr expr cs
	= convertToRhsExpression left_vars right_vars group_index common_defs default_ptr expr cs

convertToRhsExpression left_vars right_vars group_index common_defs default_ptr expr cs
	# (bb_rhs, cs) = convertRootExpression {ci_bound_vars=left_vars ++ flatten right_vars, ci_group_index=group_index, ci_common_defs=common_defs} default_ptr expr cs
	= ([(map (map selectFreeVar) right_vars, bb_rhs)], cs)
	
selectFreeVar (fv,_) = FP_Variable fv

toFreeVar (var_info_ptr, _) var_heap
	#! var_info = sreadPtr var_info_ptr var_heap
	# (VI_FreeVar name new_ptr count type) = var_info
	= (FP_Variable { fv_def_level = NotALevel, fv_name = name, fv_info_ptr = new_ptr, fv_count = count}, var_heap)
		 	
toOptionalFreeVar (Yes (var_info_ptr, type)) var_heap
	#! var_info = sreadPtr var_info_ptr var_heap
	= case var_info of
		VI_FreeVar name new_ptr count type
			-> (Yes ({ fv_def_level = NotALevel, fv_name = name, fv_info_ptr = new_ptr, fv_count = count}, type), var_heap)
		_
			-> (No, var_heap)
toOptionalFreeVar No var_heap
	= (No, var_heap)

::	TypedVariable =
	{	tv_free_var	:: !FreeVar
	,	tv_type		:: !AType
	}

copyExpression :: ![TypedVariable] !Expression !*VarHeap -> (![Expression], ![TypedVariable], ![FreeVar], !Expression, !*VarHeap)
copyExpression bound_vars expression var_heap
    # var_heap = foldSt (\{tv_free_var={fv_info_ptr},tv_type} -> writePtr fv_info_ptr (VI_BoundVar tv_type)) bound_vars var_heap
	  (expression, {cp_free_vars, cp_var_heap, cp_local_vars}) = copy expression { cp_free_vars = [], cp_var_heap = var_heap, cp_local_vars = [] }
	  (bound_vars, free_typed_vars, var_heap) = foldSt retrieve_variable cp_free_vars ([], [], cp_var_heap)
	= (bound_vars, free_typed_vars, cp_local_vars, expression, var_heap)
where
	retrieve_variable (var_info_ptr, type) (bound_vars, free_typed_vars, var_heap)
		# (VI_FreeVar name new_ptr count type, var_heap) = readPtr var_info_ptr var_heap
		= ( [Var { var_name = name, var_info_ptr = var_info_ptr, var_expr_ptr = nilPtr} : bound_vars],
			[{tv_free_var = { fv_def_level = NotALevel, fv_name = name, fv_info_ptr = new_ptr, fv_count = count }, tv_type = type} : free_typed_vars], var_heap)

retrieveVariable (var_info_ptr, type) (bound_vars, free_typed_vars, var_heap)
	# (VI_FreeVar name new_ptr count type, var_heap) = readPtr var_info_ptr var_heap
	= ( [Var { var_name = name, var_info_ptr = var_info_ptr, var_expr_ptr = nilPtr} : bound_vars],
		[({ fv_def_level = NotALevel, fv_name = name, fv_info_ptr = new_ptr, fv_count = count }, type) : free_typed_vars], var_heap)

::	CopyState =
	{	cp_free_vars	:: ![(VarInfoPtr,AType)]
	,	cp_local_vars	:: ![FreeVar]
	,	cp_var_heap		:: !.VarHeap
	}
	
class copy e :: !e !*CopyState -> (!e, !*CopyState)

instance copy BoundVar
where
	copy var=:{var_name,var_info_ptr} cp_state=:{cp_var_heap}
		# (var_info, cp_var_heap) = readPtr var_info_ptr cp_var_heap
		  cp_state = { cp_state & cp_var_heap = cp_var_heap }
		= case var_info of
			VI_FreeVar name new_info_ptr count type
				-> ({ var & var_info_ptr = new_info_ptr },
					{ cp_state & cp_var_heap = cp_state.cp_var_heap <:= (var_info_ptr, VI_FreeVar name new_info_ptr (inc count) type)})
			VI_LocalVar
				-> (var, cp_state)
			VI_BoundVar type
				# (new_info_ptr, cp_var_heap) = newPtr VI_Empty cp_state.cp_var_heap
				-> ({ var & var_info_ptr = new_info_ptr },
					{ cp_state & cp_free_vars = [ (var_info_ptr, type) : cp_state.cp_free_vars ],
							cp_var_heap = cp_var_heap <:= (var_info_ptr, VI_FreeVar var_name new_info_ptr 1 type) })
			_
				-> abort "copy [BoundVar] (convertcases)" //  <<- (var_info ---> (var_name, ptrToInt var_info_ptr))

instance copy Expression
where
	copy (Var var) cp_state
		# (var, cp_state) = copy var cp_state
		= (Var var, cp_state)
	copy (App app=:{app_args}) cp_state
		# (app_args, cp_state) = copy app_args cp_state
		= (App {app & app_args = app_args}, cp_state)
	copy (fun_expr @ exprs) cp_state
		# ((fun_expr, exprs), cp_state) = copy (fun_expr, exprs) cp_state
		= (fun_expr @ exprs, cp_state)
	copy (Let lad=:{let_strict_binds,let_lazy_binds, let_expr}) cp_state=:{cp_var_heap, cp_local_vars}
		# (cp_local_vars, cp_var_heap) = foldSt bind_let_var let_strict_binds (cp_local_vars, cp_var_heap)
		# (cp_local_vars, cp_var_heap) = foldSt bind_let_var let_lazy_binds (cp_local_vars, cp_var_heap)
		# (let_strict_binds, cp_state) = copy let_strict_binds {cp_state & cp_var_heap = cp_var_heap, cp_local_vars = cp_local_vars }
		# (let_lazy_binds, cp_state) = copy let_lazy_binds cp_state
		# (let_expr, cp_state) = copy let_expr cp_state
		= (Let {lad & let_strict_binds = let_strict_binds, let_lazy_binds = let_lazy_binds, let_expr = let_expr }, cp_state)
	where
		bind_let_var {lb_dst} (local_vars, var_heap)
			= ([lb_dst : local_vars], var_heap <:= (lb_dst.fv_info_ptr, VI_LocalVar))
	copy (Case case_expr) cp_state
		# (case_expr, cp_state) = copy case_expr cp_state
		= (Case case_expr, cp_state)
	copy expr=:(BasicExpr _ _) cp_state
		= (expr, cp_state)
	copy (MatchExpr opt_tuple constructor expr) cp_state
		# (expr, cp_state) = copy expr cp_state
		= (MatchExpr opt_tuple constructor expr, cp_state)
	copy (Selection is_unique expr selectors) cp_state
		# (expr, cp_state) = copy expr cp_state
		  (selectors, cp_state) = copy selectors cp_state
		= (Selection is_unique expr selectors, cp_state)
	copy (Update expr1 selectors expr2) cp_state
		# (expr1, cp_state) = copy expr1 cp_state
		  (selectors, cp_state) = copy selectors cp_state
		  (expr2, cp_state) = copy expr2 cp_state
		= (Update expr1 selectors expr2, cp_state)
	copy (RecordUpdate cons_symbol expression expressions) cp_state
		# (expression, cp_state) = copy expression cp_state
		  (expressions, cp_state) = copy expressions cp_state
		= (RecordUpdate cons_symbol expression expressions, cp_state)
	copy (TupleSelect tuple_symbol arg_nr expr) cp_state
		# (expr, cp_state) = copy expr cp_state
		= (TupleSelect tuple_symbol arg_nr expr, cp_state)
	copy EE cp_state
		= (EE, cp_state)
	copy (NoBind ptr) cp_state
		= (NoBind ptr, cp_state)
	copy expr cp_state
		= abort ("copy (Expression) does not match" ---> expr)

instance copy (Optional a) | copy a
where
	copy (Yes expr) cp_state
		# (expr, cp_state) = copy expr cp_state
		= (Yes expr, cp_state)
	copy No cp_state
		= (No, cp_state)

instance copy Selection  
where
	copy (DictionarySelection record selectors expr_ptr index_expr) cp_state
		# (index_expr, cp_state) = copy index_expr cp_state
		  (selectors, cp_state) = copy selectors cp_state
		  (record, cp_state) = copy record cp_state
		= (DictionarySelection record selectors expr_ptr index_expr, cp_state)
	copy (ArraySelection selector expr_ptr index_expr) cp_state
		# (index_expr, cp_state) = copy index_expr cp_state
		= (ArraySelection selector expr_ptr index_expr, cp_state)
	copy selector cp_state
		= (selector, cp_state)

instance copy Case
where
	copy this_case=:{case_expr, case_guards, case_default} cp_state
		# ((case_expr,(case_guards,case_default)), cp_state) = copy (case_expr,(case_guards,case_default)) cp_state
		= ({ this_case & case_expr = case_expr, case_guards = case_guards, case_default = case_default}, cp_state) 

instance copy CasePatterns
where
	copy (AlgebraicPatterns type patterns) cp_state
		# (patterns, cp_state) = copy patterns cp_state
		= (AlgebraicPatterns type patterns, cp_state) 
	copy (BasicPatterns type patterns) cp_state
		# (patterns, cp_state) = copy patterns cp_state
		= (BasicPatterns type patterns, cp_state) 

instance copy AlgebraicPattern
where
	copy pattern=:{ap_vars,ap_expr} cp_state=:{cp_var_heap}
		# (ap_expr, cp_state) = copy ap_expr { cp_state & cp_var_heap = foldSt (\{fv_info_ptr} -> writePtr fv_info_ptr VI_LocalVar) ap_vars cp_var_heap}
		= ({ pattern & ap_expr = ap_expr }, cp_state) 

instance copy BasicPattern
where
	copy pattern=:{bp_expr} cp_state
		# (bp_expr, cp_state) = copy bp_expr cp_state
		= ({ pattern & bp_expr = bp_expr }, cp_state) 

instance copy [a] | copy a
where
	copy l cp_state = mapSt copy l cp_state 
		
instance copy (a,b) | copy a & copy b
where
	copy t cp_state = app2St (copy, copy) t cp_state 

instance copy LetBind
where
	copy bind=:{lb_src} cp_state
		# (lb_src, cp_state) = copy lb_src cp_state
		= ({ bind & lb_src = lb_src }, cp_state) 

instance copy (Bind a b) | copy a
where
	copy bind=:{bind_src} cp_state
		# (bind_src, cp_state) = copy bind_src cp_state
		= ({ bind & bind_src = bind_src }, cp_state) 

instance <<< ExprInfo
where
	(<<<) file EI_Empty			= file <<< "*Empty*"
	(<<<) file (EI_CaseType _)	= file <<< "CaseType"

instance <<< (Ptr a)
where
	(<<<) file ptr = file <<< ptrToInt ptr  
/*
instance <<< BoundVar
where
	(<<<) file {var_name,var_info_ptr} = file <<< var_name <<< '[' <<< var_info_ptr <<< ']'

instance  <<<  FunctionBody
where
	(<<<) file (TransformedBody {tb_rhs}) = file <<<  tb_rhs
*/

instance  <<<  CountedVariable
where
	(<<<) file {cv_variable,cv_count} = file <<< '<' <<< cv_variable <<< ',' <<< cv_count <<< '>'

(==>) a b :== a
//(==>) a b :== a ---> b
