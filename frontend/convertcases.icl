implementation module convertcases

import syntax, transform, checksupport, StdCompare, check, utilities, trans, general, RWSDebug

// exactZip fails when its arguments are of unequal length
exactZip` :: ![.a] ![.b] -> [(.a,.b)]
exactZip` [] []
	=	[]
exactZip` [x:xs][y:ys]
	=	[(x,y) : exactZip xs ys]
exactZip
	:==	zip2

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
			= convert_groups 0 groups dcl_functions common_defs main_dcl_module_n
				(fun_defs, [], { cs_new_functions = [], cs_fun_heap = newHeap, cs_var_heap = var_heap, cs_expr_heap = expr_heap, cs_next_fun_nr = nr_of_funs })
	  (groups, new_fun_defs, imported_types, imported_conses, type_heaps, cs_var_heap)
			= addNewFunctionsToGroups common_defs cs_fun_heap cs_new_functions main_dcl_module_n groups imported_types imported_conses type_heaps cs_var_heap
	  (imported_functions, imported_conses) = foldSt split collected_imports ([], imported_conses)
	= (imported_functions, groups, { fundef \\ fundef <- [ fundef \\ fundef <-: fun_defs ] ++ new_fun_defs },
			imported_types, imported_conses, cs_var_heap, type_heaps, cs_expr_heap)
where
	convert_groups group_nr groups dcl_functions common_defs main_dcl_module_n fun_defs_and_ci
		| group_nr == size groups
			= (groups, fun_defs_and_ci)
		// otherwise
			# (group, groups) = groups![group_nr]
			= convert_groups (inc group_nr) groups dcl_functions common_defs main_dcl_module_n
				(foldSt (convert_function group_nr dcl_functions common_defs main_dcl_module_n) group.group_members fun_defs_and_ci)

	convert_function group_index dcl_functions common_defs main_dcl_module_n fun (fun_defs, collected_imports, cs)
		# (fun_def, fun_defs) = fun_defs![fun]
		# {fun_body,fun_type} = fun_def -*-> ("*** converting ****", fun_def.fun_symb.id_name)
		  (fun_body, (collected_imports, cs)) = eliminate_code_sharing_in_function dcl_functions main_dcl_module_n common_defs fun_body /* (fun_body 
		   ("convert_function", fun_def.fun_symb, fun_body)) */ (collected_imports, cs)		  		
		  (fun_body, cs) = convertCasesInBody fun_body fun_type group_index common_defs cs
		= ({fun_defs & [fun].fun_body = fun_body }, collected_imports, cs)

	eliminate_code_sharing_in_function dcl_functions main_dcl_module_n common_defs (TransformedBody body=:{tb_rhs}) (collected_imports, cs=:{cs_expr_heap,cs_var_heap})
		# {rcs_var_heap, rcs_expr_heap, rcs_imports} = weightedRefCount {rci_imported = {cii_dcl_functions=dcl_functions, cii_common_defs=common_defs, cii_main_dcl_module_n = main_dcl_module_n}, rci_depth=1} tb_rhs
				{ rcs_var_heap = cs_var_heap, rcs_expr_heap = cs_expr_heap, rcs_free_vars = [],
				  rcs_imports = collected_imports} 
		  	-*-> ("eliminate_code_sharing_in_function (weightedRefCount)", tb_rhs)
		  ds = { ds_lets = [], ds_var_heap = rcs_var_heap, ds_expr_heap = rcs_expr_heap}
		  (tb_rhs, ds) = distributeLets 1 tb_rhs ds -*-> "dis"
		  (tb_rhs, {ds_var_heap, ds_expr_heap}) = buildLetExpr tb_rhs ds -*-> "build"
		= (TransformedBody {body & tb_rhs = tb_rhs }, (rcs_imports, { cs & cs_var_heap = ds_var_heap, cs_expr_heap = ds_expr_heap}))
		  	-*-> ("eliminate_code_sharing_in_function (distributeLets)", 2, tb_rhs)

	split :: SymbKind (ImportedFunctions, ImportedConstructors) -> (ImportedFunctions, ImportedConstructors) 
	split (SK_Function fun_symb) (collected_functions, collected_conses)
		= ([fun_symb : collected_functions], collected_conses)
	split (SK_Constructor cons_symb) (collected_functions, collected_conses)
		= (collected_functions, [ cons_symb : collected_conses])

:: CaseLevel = CaseLevelRoot | CaseLevelAfterGuardRoot

:: ConvertInfo =
	{	ci_bound_vars :: ![(FreeVar, AType)]
	,	ci_group_index :: !Index
	,	ci_common_defs :: !{#CommonDefs}
	,	ci_case_level	:: !CaseLevel
	}

convertCasesInBody :: FunctionBody (Optional SymbolType) Int {#CommonDefs} *ConvertState -> (FunctionBody,  *ConvertState)
convertCasesInBody (TransformedBody body) (Yes type) group_index common_defs cs
	# (body, cs) = convertRootCases
						{	ci_bound_vars = exactZip body.tb_args type.st_args
						,	ci_group_index = group_index
						,	ci_common_defs = common_defs
						,	ci_case_level=CaseLevelRoot
						}
						body cs
	= (TransformedBody body, cs)


/*
	weightedRefCount determines the reference counts of variables in an expr. Runtime behaviour
	of constructs is taken into account:  multiple occurrences of variables in different
	alternatives of the same case clause are counted only once. The outcome is used to distribute
	shared exprs (via let declarations) over cases. In this way code sharing is eliminated.
	As a side effect, weightedRefCount returns a list of all imported functions that have been used
	inside the expr.
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
//					-*-> (lvi_var, " PUSHED ",lvi_depth)
	| lvi_count == 0
		= (True, { lvi & lvi_count = ref_count }, [var_info_ptr : new_vars])
	// otherwise
		= (lvi_new, { lvi & lvi_count = lvi_count + ref_count }, new_vars)

class weightedRefCount e :: RCInfo !e !*RCState -> *RCState

instance weightedRefCount BoundVar
where
	weightedRefCount rci=:{rci_depth} {var_name,var_info_ptr} rs=:{rcs_var_heap,rcs_free_vars}
		#! var_info = sreadPtr var_info_ptr rcs_var_heap
		= case var_info of
			VI_LetVar lvi
				# (is_new, lvi=:{lvi_expression}, rcs_free_vars) = weightedRefCountOfVariable rci_depth var_info_ptr lvi 1 rcs_free_vars
				| is_new
					# rs = weightedRefCount rci lvi_expression
							{ rs & rcs_free_vars = rcs_free_vars,
							  rcs_var_heap = rs.rcs_var_heap  <:= (var_info_ptr, VI_LetVar {lvi & lvi_expression = EE, lvi_new = False})}
					  (VI_LetVar lvi, rcs_var_heap) = readPtr var_info_ptr rs.rcs_var_heap
					-> { rs & rcs_var_heap = rcs_var_heap <:= (var_info_ptr, VI_LetVar { lvi & lvi_expression = lvi_expression }) }
//							 -*-> (var_name, var_info_ptr, depth, lvi.lvi_count)
				// otherwise
					-> { rs & rcs_var_heap = rs.rcs_var_heap <:= (var_info_ptr, VI_LetVar lvi) }
			_
				-> rs

instance weightedRefCount Expression
where
	weightedRefCount rci (Var var) rs
		= weightedRefCount rci var rs
	weightedRefCount rci (App app) rs
		= weightedRefCount rci app rs
	weightedRefCount rci (fun_expr @ exprs) rs
		= weightedRefCount rci (fun_expr, exprs) rs
	weightedRefCount rci=:{rci_depth} (Let {let_strict_binds,let_lazy_binds,let_expr, let_info_ptr}) rs =:{rcs_var_heap}
		# rs = weightedRefCount rci let_strict_binds { rs & rcs_var_heap = foldSt (store_binding rci_depth) let_lazy_binds rcs_var_heap }
		  rs = weightedRefCount rci let_expr rs
		  (let_info, rcs_expr_heap) = readPtr let_info_ptr rs.rcs_expr_heap
		  rs = { rs & rcs_expr_heap = rcs_expr_heap }
		= case let_info of
			EI_LetType let_type
		  		# (ref_counts, rcs_var_heap) = mapSt get_ref_count let_lazy_binds rs.rcs_var_heap
				  (rcs_free_vars, rcs_var_heap) = foldl remove_variable (rs.rcs_free_vars, rcs_var_heap) let_lazy_binds
				-> { rs & rcs_free_vars = rcs_free_vars, rcs_var_heap = rcs_var_heap,
						rcs_expr_heap = rs.rcs_expr_heap <:= (let_info_ptr, EI_LetTypeAndRefCounts let_type ref_counts)}
//							-*-> ("weightedRefCount (EI_LetType)", ptrToInt let_info_ptr, [ x.bind_dst \\ x <- let_lazy_binds])
			_
				# (rcs_free_vars, rcs_var_heap) = foldl remove_variable (rs.rcs_free_vars, rs.rcs_var_heap) let_lazy_binds
				-> { rs & rcs_free_vars = rcs_free_vars, rcs_var_heap = rcs_var_heap }
//							-*-> ("weightedRefCount (_)", ptrToInt let_info_ptr, [ x.bind_dst \\ x <- let_lazy_binds])
	where
		remove_variable ([], var_heap) let_bind
			= ([], var_heap)
		remove_variable ([var_ptr : var_ptrs], var_heap) bind=:{lb_dst={fv_name,fv_info_ptr}}
			| fv_info_ptr == var_ptr
				# (VI_LetVar {lvi_count,lvi_depth}, var_heap) = readPtr fv_info_ptr var_heap
				= (var_ptrs, var_heap) 
//						-*-> ("remove_variable (lvi_count,lvi_dpeth) ", fv_name, lvi_count, lvi_depth)
			// otherwise
				# (var_ptrs, var_heap) = remove_variable (var_ptrs, var_heap) bind
				= ([var_ptr : var_ptrs], var_heap)

		store_binding depth {lb_dst={fv_name,fv_info_ptr},lb_src} var_heap
			= var_heap <:= (fv_info_ptr, VI_LetVar {lvi_count = 0, lvi_depth = depth, lvi_previous = [],
													lvi_new = True, lvi_expression = lb_src, lvi_var = fv_name})

		get_ref_count {lb_dst={fv_name,fv_info_ptr}} var_heap 
			# (VI_LetVar {lvi_count}, var_heap) = readPtr fv_info_ptr var_heap
		  	= (lvi_count, var_heap)
//				-*-> (fv_name,fv_info_ptr,lvi_count)
	weightedRefCount rci (Case case_expr) rs=:{rcs_expr_heap}
		# (case_info, rcs_expr_heap) = readPtr case_expr.case_info_ptr rcs_expr_heap
		= weightedRefCountOfCase rci case_expr case_info { rs & rcs_expr_heap = rcs_expr_heap }
	weightedRefCount rci expr=:(BasicExpr _ _) rs
		= rs
	weightedRefCount rci (MatchExpr _ constructor expr) rs
		= weightedRefCount rci expr rs
	weightedRefCount rci (Selection opt_tuple expr selections) rs
		= weightedRefCount rci (expr, selections) rs
	weightedRefCount rci (Update expr1 selections expr2) rs
		= weightedRefCount rci (expr1, (selections, expr2)) rs
	weightedRefCount rci (RecordUpdate cons_symbol expr exprs) rs
		= weightedRefCount rci (expr, exprs) rs
	weightedRefCount rci (TupleSelect tuple_symbol arg_nr expr) rs
		= weightedRefCount rci expr rs
	weightedRefCount rci (AnyCodeExpr _ _ _) rs
		= rs
	weightedRefCount rci (ABCCodeExpr _ _) rs
		= rs
	weightedRefCount rci (TypeCodeExpression type_code_expr) rs
		= weightedRefCount rci type_code_expr rs
	weightedRefCount rci EE rs
		= rs
	weightedRefCount rci (NoBind ptr) rs
		= rs
	weightedRefCount rci expr rs
		= abort ("weightedRefCount [Expression] (convertcases, 864))" -*-> expr)

addPatternVariable depth {cv_variable = var_info_ptr, cv_count = ref_count} (free_vars, var_heap)
 	#! var_info = sreadPtr var_info_ptr var_heap
	= case var_info of
		VI_LetVar lvi
			# (_, lvi, free_vars) = weightedRefCountOfVariable depth var_info_ptr lvi ref_count free_vars
			-> (free_vars, var_heap <:= (var_info_ptr, VI_LetVar lvi))
		_
			-> (free_vars, var_heap)

weightedRefCountOfCase rci=:{rci_depth} this_case=:{case_expr, case_guards, case_default, case_info_ptr} (EI_CaseType case_type)
			rs=:{ rcs_var_heap, rcs_expr_heap, rcs_imports }
	# (local_vars, vars_and_heaps) = weighted_ref_count_in_case_patterns {rci & rci_depth=rci_depth+1} case_guards rcs_imports rcs_var_heap rcs_expr_heap
	  (default_vars, (all_vars, rcs_imports, var_heap, expr_heap)) = weighted_ref_count_in_default {rci & rci_depth=rci_depth+1} case_default vars_and_heaps
	  rs = weightedRefCount rci case_expr { rs & rcs_var_heap = var_heap, rcs_expr_heap = expr_heap, rcs_imports = rcs_imports }
	  (rcs_free_vars, rcs_var_heap) = foldSt (addPatternVariable rci_depth) all_vars (rs.rcs_free_vars, rs.rcs_var_heap)
	  rcs_expr_heap = rs.rcs_expr_heap <:= (case_info_ptr, EI_CaseTypeAndRefCounts case_type 
	  		{ rcc_all_variables = all_vars, rcc_default_variables = default_vars, rcc_pattern_variables = local_vars })
	= { rs & rcs_var_heap = rcs_var_heap, rcs_expr_heap = rcs_expr_heap, rcs_free_vars = rcs_free_vars   }
//			-*-> ("weightedRefCountOfCase", ptrToInt case_info_ptr, case_expr)
	where
		weighted_ref_count_in_default rci (Yes expr) info
			= weightedRefCountInPatternExpr rci expr info
		weighted_ref_count_in_default rci No info
			= ([], info)

		weighted_ref_count_in_case_patterns rci (AlgebraicPatterns type patterns) collected_imports var_heap expr_heap
			= mapSt (weighted_ref_count_in_algebraic_pattern rci) patterns ([], collected_imports, var_heap, expr_heap)
		where
			weighted_ref_count_in_algebraic_pattern rci=:{rci_imported} {ap_expr,ap_symbol} wrcs_state
				# (free_vars_with_rc, (all_free_vars, collected_imports, var_heap, expr_heap))
					= weightedRefCountInPatternExpr rci ap_expr wrcs_state
				  (collected_imports, var_heap)
					=	check_symbol rci_imported ap_symbol collected_imports var_heap
				=	(free_vars_with_rc, (all_free_vars, collected_imports, var_heap, expr_heap))
				where
					check_symbol {cii_main_dcl_module_n, cii_common_defs} {glob_module, glob_object={ds_index}} collected_imports var_heap
						| glob_module <> cii_main_dcl_module_n
							# {cons_type_ptr} = cii_common_defs.[glob_module].com_cons_defs.[ds_index]
							  (collected_imports, var_heap) = checkImportedSymbol (SK_Constructor {glob_module = glob_module, glob_object = ds_index})
									cons_type_ptr (collected_imports, var_heap)
							= (collected_imports, var_heap)
						// otherwise
							= (collected_imports, var_heap)

		weighted_ref_count_in_case_patterns rci (BasicPatterns type patterns) collected_imports var_heap expr_heap
			= mapSt (\{bp_expr} -> weightedRefCountInPatternExpr rci bp_expr) patterns ([], collected_imports, var_heap, expr_heap)
		weighted_ref_count_in_case_patterns rci (DynamicPatterns patterns) collected_imports var_heap expr_heap
			= mapSt (\{dp_rhs} -> weightedRefCountInPatternExpr rci dp_rhs) patterns ([], collected_imports, var_heap, expr_heap)

weightedRefCountOfCase rci=:{rci_depth} this_case=:{case_expr, case_guards, case_default, case_info_ptr} (EI_CaseTypeAndRefCounts case_type {rcc_all_variables})
			rs=:{ rcs_var_heap, rcs_expr_heap, rcs_imports }
	# rs = weightedRefCount rci case_expr rs
	  (rcs_free_vars, rcs_var_heap) = foldSt (addPatternVariable rci_depth) rcc_all_variables (rs.rcs_free_vars, rs.rcs_var_heap)
	= { rs & rcs_var_heap = rcs_var_heap, rcs_free_vars = rcs_free_vars }	
//			-*-> ("weightedRefCountOfCase 2", ptrToInt case_info_ptr, case_expr)

instance weightedRefCount Selection
where
	weightedRefCount rci=:{rci_imported} (ArraySelection {glob_module,glob_object={ds_index}} _ index_expr) rs
		# rs = weightedRefCount rci index_expr rs
		= checkImportOfDclFunction rci_imported glob_module ds_index rs
	weightedRefCount rci (DictionarySelection _ selectors _ index_expr) rs
		# rs = weightedRefCount rci index_expr rs
		= weightedRefCount rci selectors rs
	weightedRefCount {rci_imported} (RecordSelection selector _) rs
		= checkRecordSelector rci_imported selector rs

weightedRefCountInPatternExpr rci=:{rci_depth} pattern_expr (previous_free_vars, collected_imports, var_heap, expr_heap)
	# {rcs_free_vars,rcs_var_heap,rcs_imports,rcs_expr_heap} = weightedRefCount rci pattern_expr
				{ rcs_var_heap = var_heap, rcs_expr_heap = expr_heap, rcs_free_vars = [], rcs_imports = collected_imports}
	  (free_vars_with_rc, rcs_var_heap) = mapSt get_ref_count rcs_free_vars rcs_var_heap
	  (previous_free_vars, rcs_var_heap) = foldSt (select_unused_free_variable rci_depth) previous_free_vars ([], rcs_var_heap)
	  (all_free_vars, rcs_var_heap) = foldSt (collect_free_variable rci_depth) rcs_free_vars (previous_free_vars, rcs_var_heap)
//			-*-> ("remove_vars ", depth, free_vars_with_rc)
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
	Here we examine the appplication to see whether an imported function has been used. If so,
	the 'ft_type_ptr' is examined. Initially this pointer contains VI_Empty. After the first
	occurrence the pointer will be set to 'VI_Used'.
*/
checkImportOfDclFunction :: CheckImportedInfo Int Int *RCState -> *RCState
checkImportOfDclFunction {cii_main_dcl_module_n, cii_dcl_functions} mod_index fun_index rs=:{rcs_imports, rcs_var_heap}
	| mod_index <> cii_main_dcl_module_n
		# {ft_type_ptr} = cii_dcl_functions.[mod_index].[fun_index]
		  (rcs_imports, rcs_var_heap) = checkImportedSymbol (SK_Function {glob_module=mod_index,glob_object=fun_index}) ft_type_ptr (rcs_imports, rcs_var_heap)
		= { rs & rcs_imports = rcs_imports, rcs_var_heap = rcs_var_heap }
	// otherwise
		= rs
checkRecordSelector {cii_main_dcl_module_n, cii_common_defs} {glob_module, glob_object={ds_index}} rs=:{rcs_imports,rcs_var_heap}
	| glob_module <> cii_main_dcl_module_n
		# {com_selector_defs,com_cons_defs,com_type_defs} = cii_common_defs.[glob_module]
		  {sd_type_index} = com_selector_defs.[ds_index]
		  {td_rhs = RecordType {rt_constructor={ds_index=cons_index}}} = com_type_defs.[sd_type_index]
		  {cons_type_ptr} = com_cons_defs.[cons_index]
		  (rcs_imports, rcs_var_heap) = checkImportedSymbol (SK_Constructor {glob_module = glob_module, glob_object = cons_index})
											cons_type_ptr (rcs_imports, rcs_var_heap)
		= { rs & rcs_imports = rcs_imports, rcs_var_heap = rcs_var_heap }
	// otherwise
		= rs

instance weightedRefCount App
where
	weightedRefCount rci=:{rci_imported} {app_symb,app_args} rs
		# rs = weightedRefCount rci app_args rs
		= check_import rci_imported app_symb rs
	where
		check_import cii {symb_kind=SK_Function {glob_module,glob_object}} rs=:{rcs_imports, rcs_var_heap}
			= checkImportOfDclFunction cii glob_module glob_object rs
		check_import {cii_main_dcl_module_n, cii_common_defs} {symb_name,symb_kind=symb_kind=:(SK_Constructor {glob_module,glob_object})} rs=:{rcs_imports, rcs_var_heap}
			| glob_module <> cii_main_dcl_module_n
				# {cons_type_ptr} = cii_common_defs.[glob_module].com_cons_defs.[glob_object]
				  (rcs_imports, rcs_var_heap) = checkImportedSymbol symb_kind cons_type_ptr (rcs_imports, rcs_var_heap)
				= { rs & rcs_imports = rcs_imports, rcs_var_heap = rcs_var_heap }
				= rs
		check_import _ _ rs
			= rs

instance weightedRefCount TypeCodeExpression
where
	weightedRefCount rci type_code_expr rs
		= rs

instance weightedRefCount [a] | weightedRefCount a
where
	weightedRefCount rci l rs
		=	foldr (weightedRefCount rci) rs l 
		
instance weightedRefCount (a,b) | weightedRefCount a & weightedRefCount b
where
	weightedRefCount rci (x,y) rs
		=	weightedRefCount rci y (weightedRefCount rci x rs) 

instance weightedRefCount LetBind
where
	weightedRefCount rci {lb_src} rs
		=	weightedRefCount rci lb_src rs

instance weightedRefCount (Bind a b) | weightedRefCount a
where
	weightedRefCount rci bind=:{bind_src} rs
		=	weightedRefCount rci bind_src rs

/*
	distributeLets tries to move shared exprs as close as possible to the location at which they are used.
	Case-exprs may require unsharing if the shared expr is used in different alternatives. Of course
	only if the expr is neither used in the pattern nor in a surrounding expr.
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
//						 -*-> (var_name, var_info_ptr, lei.lei_count, (lei.lei_expression, lei.lei_depth, depth))
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
	distributeLets depth (RecordUpdate cons_symbol expr exprs) ds
		# (expr, ds) = distributeLets depth expr ds
		# (exprs, ds) = distributeLets depth exprs ds
		= (RecordUpdate cons_symbol expr exprs, ds)
	distributeLets depth (TupleSelect tuple_symbol arg_nr expr) ds
		# (expr, ds) = distributeLets depth expr ds
		= (TupleSelect tuple_symbol arg_nr expr, ds)
	distributeLets depth (Let lad=:{let_strict_binds,let_lazy_binds,let_expr,let_info_ptr}) ds=:{ds_expr_heap,ds_var_heap}
		# (let_info, ds_expr_heap) = readPtr let_info_ptr ds_expr_heap
		# (EI_LetTypeAndRefCounts let_type ref_counts) = let_info
		  nr_of_strict_lets = length let_strict_binds
		  ds_var_heap = set_let_expr_info depth let_lazy_binds ref_counts (drop nr_of_strict_lets let_type) ds_var_heap
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
		set_let_expr_info depth [{lb_src,lb_dst}:binds] [ref_count:ref_counts] [type:types] var_heap
			# (new_info_ptr, var_heap) = newPtr (VI_Labelled_Empty "set_let_expr_info") var_heap
			  lei = { lei_count = ref_count, lei_depth = depth, lei_var = { lb_dst & fv_info_ptr = new_info_ptr },
			  			lei_expression = lb_src, lei_type = type, lei_status =  LES_Untouched }-*-> ("set_let_expr_info", lb_dst.fv_info_ptr, new_info_ptr)
			= set_let_expr_info depth binds ref_counts types (var_heap <:= (lb_dst.fv_info_ptr, VI_LetExpression lei))
		set_let_expr_info depth [] _ _ var_heap
			= var_heap

		distribute_lets_in_non_distributed_let depth {lb_dst={fv_name,fv_info_ptr}} ds=:{ds_var_heap}
			# (VI_LetExpression lei=:{lei_count}, ds_var_heap) = readPtr fv_info_ptr ds_var_heap
			| lei_count > 0
//			| not lei_moved && lei_count > 0
				= distributeLetsInLetExpression depth fv_info_ptr lei { ds & ds_var_heap = ds_var_heap }
			// otherwise
				= { ds & ds_var_heap = ds_var_heap }
					-*-> ("distribute_lets_in_non_distributed_let (moved or not used)", lei_count, fv_name)
	distributeLets depth expr=:(TypeCodeExpression _) ds
		= (expr, ds)
	distributeLets depth (AnyCodeExpr in_params out_params code_expr) ds=:{ds_var_heap}
		# (in_params, ds_var_heap) = mapSt determine_input_parameter in_params ds_var_heap
		= (AnyCodeExpr in_params out_params code_expr, { ds & ds_var_heap = ds_var_heap })
		where
			determine_input_parameter bind=:{bind_dst} var_heap
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
		# (EI_CaseTypeAndRefCounts _ { rcc_all_variables = tot_ref_counts , rcc_default_variables = ref_counts_in_default, rcc_pattern_variables = ref_counts_in_patterns }, ds_expr_heap) = readPtr case_info_ptr ds_expr_heap
//		  ds_expr_heap = ds_expr_heap <:= (case_info_ptr, EI_CaseType case_type)
		  new_depth = depth + 1
		  (local_lets, ds_var_heap) = foldSt (mark_local_let_var new_depth) tot_ref_counts ([], ds_var_heap)
		  	-*-> ("ref_counts", case_expr, tot_ref_counts, ref_counts_in_patterns)
	 	  ds = {ds & ds_var_heap=ds_var_heap, ds_expr_heap=ds_expr_heap}
		  (case_guards, ds)  = distribute_lets_in_patterns new_depth ref_counts_in_patterns case_guards ds
		  (case_default, ds=:{ds_var_heap}) = distribute_lets_in_default new_depth ref_counts_in_default case_default ds
		  ds_var_heap = foldSt reset_local_let_var local_lets ds.ds_var_heap
		  (case_expr, ds) = distributeLets depth case_expr { ds & ds_var_heap = ds_var_heap}
		= ({ kees & case_guards = case_guards, case_expr = case_expr, case_default = case_default }, ds)
	where
		distribute_lets_in_patterns depth ref_counts (AlgebraicPatterns conses patterns) ds
			# (patterns, ds) = mapSt (distribute_lets_in_alg_pattern depth) (exactZip ref_counts patterns) ds
			= (AlgebraicPatterns conses patterns, ds)
		where
			distribute_lets_in_alg_pattern depth (ref_counts,pattern) ds=:{ds_var_heap}
				# (ap_vars, ds_var_heap) = mapSt refresh_variable pattern.ap_vars ds_var_heap
				  ds = {ds & ds_var_heap = ds_var_heap}
				  (ap_expr, ds) = distribute_lets_in_pattern_expr depth ref_counts pattern.ap_expr ds
				= ({ pattern & ap_vars = ap_vars, ap_expr = ap_expr }, ds) 
		distribute_lets_in_patterns depth ref_counts (BasicPatterns type patterns) ds
			# (patterns, ds) = mapSt (distribute_lets_in_basic_pattern depth) (exactZip ref_counts patterns) ds
			= (BasicPatterns type patterns, ds)
		where
			distribute_lets_in_basic_pattern depth (ref_counts,pattern) ds
				# (bp_expr, ds) = distribute_lets_in_pattern_expr depth ref_counts pattern.bp_expr ds
				= ({ pattern & bp_expr = bp_expr }, ds)

		distribute_lets_in_default depth ref_counts_in_default (Yes expr) ds
			# (expr, ds) = distribute_lets_in_pattern_expr depth ref_counts_in_default expr ds
			= (Yes expr, ds)
		distribute_lets_in_default depth ref_counts_in_default No ds
			= (No, ds)

		refresh_variable fv=:{fv_info_ptr} var_heap
			# (new_info_ptr, var_heap) = newPtr (VI_Labelled_Empty "refresh_variable") var_heap
			= ({ fv & fv_info_ptr = new_info_ptr }, var_heap <:= (fv_info_ptr, VI_CaseVar new_info_ptr))

		mark_local_let_var depth {cv_variable, cv_count} (local_vars, var_heap)
			# (VI_LetExpression lei=:{lei_count,lei_depth}, var_heap) = readPtr cv_variable var_heap
			| lei_count == cv_count  // -*-> ("mark_test", lei_count, cv_count)
				= ([(cv_variable, lei_count, lei_depth) : local_vars ], var_heap <:= (cv_variable, VI_LetExpression { lei & lei_depth = depth}))
						-*-> ("mark_local_let_var ", lei.lei_var.fv_name, cv_variable, (lei.lei_var.fv_info_ptr, cv_count, depth))
			// otherwise
				= (local_vars, var_heap)

		reset_local_let_var (var_info_ptr, lei_count, lei_depth)  var_heap
			# (VI_LetExpression lei, var_heap) = readPtr var_info_ptr var_heap
			= var_heap <:= (var_info_ptr, VI_LetExpression { lei & lei_depth = lei_depth, lei_count = lei_count, lei_status = LES_Moved })
					-*-> ("reset_local_let_var", var_info_ptr)
/*
		distribute_lets_in_pattern_expr depth local_vars pattern_expr ds=:{ds_var_heap, ds_lets}
			# ds_var_heap = foldSt (mark_local_let_var_of_pattern_expr depth) local_vars ds_var_heap
			  (pattern_expr, ds) = distributeLets depth pattern_expr {ds & ds_lets = []}
			  (ds_lets2, ds) = ds!ds_lets
			  ds = foldSt (reexamine_local_let_exprs depth) local_vars ds
			  (letExpr, ds)
			  	= buildLetExpr pattern_expr ds
				-*-> ("distribute_lets_in_pattern_expr")
			= (letExpr, {ds & ds_lets = ds_lets})
*/
		distribute_lets_in_pattern_expr depth local_vars pattern_expr ds=:{ds_var_heap}
			# ds_var_heap = foldSt (mark_local_let_var_of_pattern_expr depth) local_vars ds_var_heap
			  (ds=:{ds_lets}) = {ds & ds_var_heap = ds_var_heap}
			  ds = {ds & ds_lets = []}
			  (pattern_expr, ds) = distributeLets depth pattern_expr ds
			  (ds_lets2, ds) = ds!ds_lets
			  ds = foldSt (reexamine_local_let_exprs depth) local_vars ds
			  (letExpr, ds)
			  	= buildLetExpr pattern_expr ds
				-*-> ("distribute_lets_in_pattern_expr", ds_lets2)
			  ds = {ds & ds_lets = ds_lets}
			= (letExpr, ds)

		mark_local_let_var_of_pattern_expr depth {cv_variable, cv_count} var_heap
			# (VI_LetExpression lei, var_heap) = readPtr cv_variable var_heap
			| depth == lei.lei_depth
				= (var_heap <:= (cv_variable, VI_LetExpression { lei & lei_count = cv_count, lei_status = LES_Untouched }))
						-*-> ("mark_local_let_var_of_pattern_expr ", lei.lei_var.fv_name, cv_variable, (lei.lei_var.fv_info_ptr, cv_count, depth))
			// otherwise
				= var_heap

		reexamine_local_let_exprs depth {cv_variable, cv_count} ds=:{ds_var_heap}
			| cv_count > 1
				# (VI_LetExpression lei, ds_var_heap) = readPtr cv_variable ds_var_heap
				| depth == lei.lei_depth
					= distributeLetsInLetExpression depth cv_variable lei { ds & ds_var_heap = ds_var_heap }
				// otherwise
					= { ds & ds_var_heap = ds_var_heap }
			// otherwise
				= ds

distributeLetsInLetExpression :: Int VarInfoPtr LetExpressionInfo *DistributeState -> *DistributeState
distributeLetsInLetExpression _ let_var_info_ptr {lei_status = LES_Moved, lei_var} ds
	= ds -*-> ("distributeLetsInLetExpression, LES_Moved", lei_var.fv_name.id_name, let_var_info_ptr)
distributeLetsInLetExpression _ let_var_info_ptr {lei_status = LES_Updated _, lei_var} ds
	= ds -*-> ("distributeLetsInLetExpression, LES_Updated", lei_var.fv_name.id_name, let_var_info_ptr)
distributeLetsInLetExpression depth let_var_info_ptr lei=:{lei_expression, lei_status = LES_Untouched, lei_var} ds=:{ds_var_heap}
	# ds_var_heap = ds_var_heap <:= (let_var_info_ptr, VI_LetExpression { lei & lei_status = LES_Updated EE}) /* to prevent doing this expr twice */ -*-> ("distributeLetsInLetExpression, LES_Untouched", lei_var.fv_name.id_name, let_var_info_ptr)
      (lei_expression, ds) = distributeLets depth lei_expression { ds & ds_var_heap = ds_var_heap }
	= { ds & ds_lets = [ let_var_info_ptr : ds.ds_lets ],
		 ds_var_heap = ds.ds_var_heap <:= (let_var_info_ptr, VI_LetExpression { lei & lei_status = LES_Updated lei_expression })}

buildLetExpr :: !Expression !*DistributeState -> (!Expression, !*DistributeState)
buildLetExpr let_expr ds=:{ds_lets=[]}
	=	(let_expr, ds) -*-> ("buildLetExpr", 0)
buildLetExpr let_expr ds=:{ds_lets, ds_var_heap, ds_expr_heap}
	# (lazy_binds, lazy_binds_types, ds_var_heap) = foldr build_bind ([], [], ds_var_heap) ds_lets
	  ds = {ds & ds_var_heap = ds_var_heap} -*-> ("buildLetExpr", ds_lets)
	// otherwise
	= case let_expr of
		Let inner_let=:{let_info_ptr }
			# ds_expr_heap = ds.ds_expr_heap
			# (EI_LetType strict_bind_types, ds_expr_heap) = readPtr let_info_ptr ds_expr_heap
			  ds_expr_heap = writePtr let_info_ptr (EI_LetType (strict_bind_types ++ lazy_binds_types)) ds_expr_heap
			-> (Let { inner_let & let_lazy_binds = lazy_binds }, {ds & ds_expr_heap=ds_expr_heap})
		_
			# ds_expr_heap = ds.ds_expr_heap
			# (let_info_ptr, ds_expr_heap) = newPtr (EI_LetType lazy_binds_types) ds_expr_heap
			-> (Let { let_strict_binds = [], let_lazy_binds = lazy_binds, let_expr = let_expr,
					let_info_ptr = let_info_ptr, let_expr_position = NoPos }, {ds & ds_expr_heap = ds_expr_heap})
where
	build_bind :: !VarInfoPtr !(![LetBind], ![AType], !*VarHeap)
		-> (![LetBind], ![AType], !*VarHeap)
	build_bind info_ptr (lazy_binds, lazy_binds_types, var_heap)
		# (let_info, var_heap) = readPtr info_ptr var_heap
		# (VI_LetExpression lei=:{lei_var,lei_status,lei_type}) = let_info
		  (LES_Updated updated_expr) = lei_status
		  (new_info_ptr, var_heap) = newPtr (VI_Labelled_Empty "build_bind") var_heap 
		  var_heap = var_heap <:= (info_ptr, VI_LetExpression { lei & lei_status = LES_Untouched, lei_var = { lei_var & fv_info_ptr = new_info_ptr }})
			-*-> ("build_bind", lei_var.fv_name, info_ptr, new_info_ptr)
		= ([{ lb_src = updated_expr, lb_dst = lei_var, lb_position = NoPos } : lazy_binds], [lei_type : lazy_binds_types ], var_heap)

instance distributeLets Selection
where
	distributeLets depth (ArraySelection selector expr_ptr expr) cp_info
		# (expr, cp_info) = distributeLets depth expr cp_info
		= (ArraySelection selector expr_ptr expr, cp_info)
	distributeLets depth (DictionarySelection var selectors expr_ptr expr) cp_info
		# (selectors, cp_info) = distributeLets depth selectors cp_info
		# (expr, cp_info) = distributeLets depth expr cp_info
		= (DictionarySelection var selectors expr_ptr expr, cp_info)
	distributeLets depth selection cp_info
		= (selection, cp_info)

instance distributeLets [a] | distributeLets a
where
	distributeLets depth l cp_info = mapSt (distributeLets depth) l cp_info 

instance distributeLets LetBind
where
	distributeLets depth bind=:{lb_src} cp_info
		# (lb_src, cp_info) = distributeLets depth lb_src cp_info
		= ({ bind & lb_src = lb_src }, cp_info)
	
instance distributeLets (Bind a b) | distributeLets a
where
	distributeLets depth bind=:{bind_src} cp_info
		# (bind_src, cp_info) = distributeLets depth bind_src cp_info
		= ({ bind & bind_src = bind_src }, cp_info)

newFunction :: !(Optional Ident) !FunctionBody ![FreeVar] ![AType] !AType !Int !(!Int, ![FunctionInfoPtr],!*FunctionHeap)
	-> (! SymbIdent, !(!Int, ![FunctionInfoPtr],!*FunctionHeap))
newFunction opt_id fun_bodies local_vars arg_types result_type group_index state
	=	newFunctionWithType opt_id fun_bodies local_vars fun_type group_index state
	where
	  fun_type =
		{	st_vars			= []
		,	st_args			= arg_types
		,	st_arity		= length arg_types // -*-> ("newFunction", fun_id.id_name)
		,	st_result		= result_type
		,	st_context		= []
		,	st_attr_vars	= []
		,	st_attr_env		= []
		}

newFunctionWithType :: !(Optional Ident) !FunctionBody ![FreeVar] !SymbolType !Int !(!Int, ![FunctionInfoPtr],!*FunctionHeap)
	-> (! SymbIdent, !(!Int, ![FunctionInfoPtr],!*FunctionHeap))
newFunctionWithType opt_id fun_bodies local_vars fun_type group_index (cs_next_fun_nr, cs_new_functions, cs_fun_heap)
	# (fun_def_ptr, cs_fun_heap) = newPtr FI_Empty cs_fun_heap
	  fun_id = getIdent opt_id cs_next_fun_nr

	  arity
	  	=	fun_type.st_arity

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

::	ConvertState =
	{	cs_new_functions 	:: ![FunctionInfoPtr]
	,	cs_fun_heap			:: !.FunctionHeap
	,	cs_var_heap			:: !.VarHeap
	,	cs_expr_heap		:: !.ExpressionHeap
	,	cs_next_fun_nr		:: !Index
	}
/*
class caseFree a :: !a -> Bool

instance caseFree [a] | caseFree a where
	caseFree l
		=	and (map caseFree l)

instance caseFree (Optional a) | caseFree a where
	caseFree No
		=	True
	caseFree (Yes a)
		=	caseFree a

instance caseFree BasicPattern where
	caseFree {bp_expr}
		=	caseFree bp_expr

instance caseFree Expression where
	caseFree (Case _)
		=	False
	caseFree _
		=	True
*/
markLocalLetVar :: LetBind *VarHeap -> *VarHeap
markLocalLetVar {lb_dst={fv_info_ptr}} varHeap
	=	varHeap <:= (fv_info_ptr, VI_LocalLetVar)

is_guard_case [{bp_value=BVB True,bp_expr}:patterns] case_default False
	= has_no_rooted_case bp_expr
is_guard_case [{bp_value=BVB False,bp_expr}:patterns] case_default False
	= then_part_exists_and_has_no_rooted_case patterns case_default
	where
		then_part_exists_and_has_no_rooted_case [ alt=:{bp_value=BVB sign_of_alt,bp_expr} : alts ] case_default
			| sign_of_alt
				= has_no_rooted_case bp_expr
				= then_part_exists_and_has_no_rooted_case alts case_default
		then_part_exists_and_has_no_rooted_case [ ] No
			= False
		then_part_exists_and_has_no_rooted_case [ ] (Yes then_expr)
			= False // only when the first alt cannot fail use: has_no_rooted_case then_expr
is_guard_case _ _ _
	= False

has_no_rooted_case (Case {case_guards=BasicPatterns BT_Bool patterns, case_default,case_explicit})
	= is_guard_case patterns case_default case_explicit
has_no_rooted_case (Case {case_explicit})
	= case_explicit
has_no_rooted_case (Let {let_expr})
	= has_no_rooted_case let_expr
has_no_rooted_case _
	= True

is_then_or_else (Case {case_expr,case_guards,case_default})
	= is_if_case case_expr case_guards case_default
is_then_or_else (Let {let_expr})
	= is_then_or_else let_expr
is_then_or_else _
	= True

is_if_case case_expr (BasicPatterns BT_Bool [{bp_value=BVB True,bp_expr=then_expr},{bp_value=BVB False,bp_expr=else_expr}]) No
	= boolean_case_is_if case_expr then_expr else_expr
is_if_case case_expr (BasicPatterns BT_Bool [{bp_value=BVB True,bp_expr=then_expr}]) (Yes else_expr)
	= boolean_case_is_if case_expr then_expr else_expr
is_if_case case_expr case_guards case_default
	= False

boolean_case_is_if case_expr then_expr else_expr
	= has_no_rooted_non_if_cases case_expr && is_then_or_else then_expr && is_then_or_else else_expr

has_no_rooted_non_if_cases (Case {case_expr,case_guards,case_default})
	= is_if_case case_expr case_guards case_default
has_no_rooted_non_if_cases (Let _)
	= False
has_no_rooted_non_if_cases _
	= True

convert_let_binds let_strict_binds let_lazy_binds let_info_ptr ci=:{ci_bound_vars} cs=:{cs_expr_heap}
	# (EI_LetType let_type, cs_expr_heap) = readPtr let_info_ptr cs_expr_heap
	  ci_bound_vars = addLetVars (let_strict_binds ++ let_lazy_binds) let_type ci_bound_vars
	  ci = {ci & ci_bound_vars = ci_bound_vars}
	  (let_strict_binds,cs)	= convertCases ci let_strict_binds { cs & cs_expr_heap = cs_expr_heap }
	  (let_lazy_binds,cs) = convertCases ci let_lazy_binds cs
	= (let_strict_binds,let_lazy_binds,ci,cs)

convert_case_to_if case_expr then_expr else_expr ci cs
	# (case_expr,cs)=convert_condition case_expr ci cs
	# (then_expr,cs)=convert_then_or_else then_expr ci cs
	# (else_expr,cs)=convert_then_or_else else_expr ci cs
	= (Conditional { if_cond = case_expr, if_then = then_expr, if_else = Yes else_expr },cs)
where
	convert_then_or_else (Let lad=:{let_strict_binds,let_lazy_binds,let_expr,let_info_ptr}) ci=:{ci_bound_vars} cs=:{cs_expr_heap}
		# (let_strict_binds,let_lazy_binds,ci,cs) = convert_let_binds let_strict_binds let_lazy_binds let_info_ptr ci cs
		  (let_expr,cs) = convert_condition let_expr ci cs
		= (Let { lad & let_strict_binds = let_strict_binds, let_lazy_binds = let_lazy_binds, let_expr = let_expr }, cs)
	convert_then_or_else expr ci cs
		= convert_condition expr ci cs

convert_condition (Case {case_expr,case_guards=(BasicPatterns BT_Bool [{bp_value=BVB True,bp_expr=then_expr},{bp_value=BVB False,bp_expr=else_expr}]),case_default=No}) ci cs
	= convert_case_to_if case_expr then_expr else_expr ci cs
convert_condition (Case {case_expr,case_guards=(BasicPatterns BT_Bool [{bp_value=BVB True,bp_expr=then_expr}]),case_default=Yes else_expr}) ci cs
	= convert_case_to_if case_expr then_expr else_expr ci cs
convert_condition expr ci cs
	= convertCases ci expr cs

class convertRootCases a :: !ConvertInfo !a *ConvertState -> (a, *ConvertState)

instance convertRootCases TransformedBody where
	convertRootCases ci body=:{tb_rhs} cs
		# (tb_rhs, cs) = convertRootCases ci tb_rhs cs
		= ({body & tb_rhs=tb_rhs}, cs)

instance convertRootCases Expression where
	convertRootCases ci (Let lad=:{let_strict_binds,let_lazy_binds,let_expr,let_info_ptr}) cs=:{cs_var_heap}
		# cs = {cs & cs_var_heap = foldSt markLocalLetVar (let_strict_binds ++ let_lazy_binds) cs_var_heap}
		# (let_strict_binds,let_lazy_binds,ci,cs) = convert_let_binds let_strict_binds let_lazy_binds let_info_ptr ci cs
//		  (let_expr, cs)			= (if (isEmpty let_strict_binds) convertRootCases convertCases) ci let_expr cs
		  (let_expr, cs)			= convertRootCases (if (isEmpty let_strict_binds) ci {ci & ci_case_level=CaseLevelAfterGuardRoot}) let_expr cs
		= (Let { lad & let_strict_binds = let_strict_binds, let_lazy_binds = let_lazy_binds, let_expr = let_expr }, cs)

	convertRootCases ci caseExpr=:(Case kees=:{case_expr, case_guards, case_default, case_explicit, case_info_ptr}) cs=:{cs_var_heap, cs_expr_heap}
		= case case_guards of // -*-> "convertRootCases, guards???" of
			BasicPatterns BT_Bool patterns
				| is_guard_case patterns case_default case_explicit
//				| caseFree patterns && (isTruePattern patterns || caseFree case_default)
					-> convert_boolean_case_into_guard ci case_expr patterns case_default case_info_ptr cs
			_
				-> case case_expr of
					(Var var)
						| not case_explicit || (case ci.ci_case_level of
													CaseLevelAfterGuardRoot -> False 
													_ -> True)
							# (EI_CaseTypeAndRefCounts case_type _, cs_expr_heap) = readPtr case_info_ptr cs.cs_expr_heap
							# (varInfo, cs_var_heap) = readPtr var.var_info_ptr cs.cs_var_heap
							# cs = {cs & cs_expr_heap=cs_expr_heap, cs_var_heap=cs_var_heap} // -*-> varInfo
							-> case varInfo of
								VI_LocalLetVar
									->	convertCases ci caseExpr cs // -*-> "convertRootCases, no guards"
								_
	//								| True <<- ("convertRootCases",varInfo)
							  		# (case_expr, cs)	= convertCases ci case_expr cs
									# (case_guards, cs) = convertRootCasesCasePatterns ci case_guards case_type.ct_cons_types cs
							  		# (case_default, cs)= convertRootCases ci case_default cs
									-> (Case {kees & case_expr=case_expr, case_guards=case_guards, case_default=case_default}, cs)
	
						// otherwise
							-> convertNonRootCase ci kees cs
					expr
//						->	convertCases ci caseExpr cs // -*-> "convertRootCases, no guards"
						-> convertNonRootCase ci kees cs

	where
		isTruePattern [{bp_value=BVB True}:_]
			= True
		isTruePattern _
			= False	

		convert_boolean_case_into_guard ci guard [ alt=:{bp_value=BVB sign_of_then_part,bp_expr} : alts ] case_default case_info_ptr cs
//			# (guard, cs) = convertCases ci guard cs
			# (guard, cs) = convert_guard guard ci cs
//			# (EI_CaseTypeAndRefCounts case_type _, cs_expr_heap) = readPtr case_info_ptr cs.cs_expr_heap
//			# {cs &cs_expr_heap=cs_expr_heap}
			# (then_part, cs) = convertRootCases {ci & ci_case_level = CaseLevelAfterGuardRoot} bp_expr cs
			# (opt_else_part, cs) = convert_to_else_part ci sign_of_then_part alts case_default cs
			= (build_conditional sign_of_then_part guard then_part opt_else_part, cs)
		where
			build_conditional True guard then_expr opt_else_expr
				= Conditional { if_cond = guard, if_then = then_expr, if_else = opt_else_expr }
			build_conditional false guard then_expr (Yes else_expr)
				= Conditional { if_cond = guard, if_then = else_expr, if_else = Yes then_expr }
			build_conditional false guard then_expr No
				= Conditional { if_cond = Conditional { if_cond = guard, if_then = BasicExpr (BVB False) BT_Bool, if_else = Yes (BasicExpr (BVB True) BT_Bool) },
									if_then = then_expr, if_else = No }

			convert_to_else_part ci sign_of_then_part [ alt=:{bp_value=BVB sign_of_else_part,bp_expr} : alts ] case_default cs
				# (else_part, cs) = convertRootCases {ci & ci_case_level=CaseLevelAfterGuardRoot} bp_expr cs
				| sign_of_then_part == sign_of_else_part
					= convert_to_else_part ci sign_of_then_part alts case_default cs
					= (Yes else_part, cs)
			convert_to_else_part ci sign_of_then_part [ ] (Yes else_part) cs
				# (else_part, cs) = convertRootCases {ci & ci_case_level=CaseLevelAfterGuardRoot} else_part cs
				= (Yes else_part, cs)
			convert_to_else_part ci sign_of_then_part [ ] No cs
				= (No, cs)
		
			convert_guard guard ci cs
				| has_no_rooted_non_if_cases guard
					= convert_condition guard ci cs
					= convertCases ci guard cs

	convertRootCases ci expr cs
		= convertCases ci expr cs

convertRootCasesCasePatterns :: ConvertInfo CasePatterns [[AType]] *ConvertState -> (CasePatterns, *ConvertState)
convertRootCasesCasePatterns ci (BasicPatterns bt patterns) _ cs
	# (patterns, cs)
		=	convertRootCases ci patterns cs
	=	(BasicPatterns bt patterns, cs)
convertRootCasesCasePatterns ci (AlgebraicPatterns gi patterns) arg_types cs
	# (patterns, cs)
		=	convertRootCasesAlgebraicPatterns ci (exactZip patterns arg_types) cs
	=	(AlgebraicPatterns gi patterns, cs)
	where
		convertRootCasesAlgebraicPatterns :: ConvertInfo [(AlgebraicPattern, [AType])] *ConvertState -> ([AlgebraicPattern], *ConvertState)
		convertRootCasesAlgebraicPatterns ci l cs
			=	mapSt (convertRootCasesAlgebraicPattern ci) l cs 

		convertRootCasesAlgebraicPattern :: ConvertInfo (AlgebraicPattern, [AType]) *ConvertState -> (AlgebraicPattern, *ConvertState)
		convertRootCasesAlgebraicPattern ci (pattern=:{ap_expr, ap_vars}, arg_types) cs
			# ci
				=	{ci & ci_bound_vars= exactZip ap_vars arg_types ++ ci.ci_bound_vars}
			# (ap_expr, cs)
				=	convertRootCases ci ap_expr cs
			=	({pattern & ap_expr=ap_expr}, cs)

instance convertRootCases (Optional a) | convertRootCases a where
	convertRootCases ci (Yes expr) cs
		# (expr, cs) = convertRootCases ci expr cs
		= (Yes expr, cs)
	convertRootCases ci No cs
		= (No, cs)

instance convertRootCases [a] | convertRootCases a where
	convertRootCases ci l cs
		=	mapSt (convertRootCases ci) l cs 

instance convertRootCases BasicPattern where
	convertRootCases ci pattern=:{bp_expr} cs
		# (bp_expr, cs)
			=	convertRootCases ci bp_expr cs
		=	({pattern & bp_expr=bp_expr}, cs)

class convertCases a :: !ConvertInfo !a  !*ConvertState -> (!a, !*ConvertState)

instance convertCases [a] | convertCases a
where
	convertCases ci l cs = mapSt (convertCases ci) l cs 

instance convertCases (a,b) | convertCases a & convertCases b
where
	convertCases ci t cs
		= app2St (convertCases ci, convertCases ci) t cs

instance convertCases (Bind a b) | convertCases a
where
	convertCases ci bind=:{bind_src} cs
		# (bind_src, cs) = convertCases ci bind_src cs
		= ({ bind & bind_src = bind_src }, cs)

instance convertCases LetBind
where
	convertCases ci bind=:{lb_src} cs
		# (lb_src, cs) = convertCases ci lb_src cs
		= ({ bind & lb_src = lb_src }, cs)

instance convertCases DynamicExpr
where
	convertCases ci dynamik=:{dyn_expr} cs
		# (dyn_expr, cs) = convertCases ci dyn_expr cs
		= ({ dynamik & dyn_expr = dyn_expr }, cs)

instance convertCases Let
where
	convertCases ci=:{ci_bound_vars} lad=:{let_strict_binds,let_lazy_binds,let_expr,let_info_ptr} cs
		# (let_strict_binds,let_lazy_binds,ci,cs) = convert_let_binds let_strict_binds let_lazy_binds let_info_ptr ci cs
		# (let_expr, cs) = convertCases ci let_expr cs
		= ({ lad & let_strict_binds = let_strict_binds, let_lazy_binds = let_lazy_binds, let_expr = let_expr }, cs)
/*
	convertCases ci=:{ci_bound_vars} lad=:{let_strict_binds,let_lazy_binds,let_expr,let_info_ptr} cs=:{cs_expr_heap}
		# (let_info, cs_expr_heap) =  readPtr let_info_ptr cs_expr_heap
		  cs = { cs & cs_expr_heap = cs_expr_heap }
		= case let_info of
			EI_LetType let_type
				# ci_bound_vars = addLetVars (let_strict_binds ++ let_lazy_binds) let_type ci_bound_vars
				# (let_strict_binds, cs) = convertCases {ci & ci_bound_vars=ci_bound_vars} let_strict_binds cs
				# (let_lazy_binds, cs) = convertCases ci let_lazy_binds cs
				# (let_expr, cs) = convertCases ci let_expr cs
				-> ({ lad & let_strict_binds = let_strict_binds, let_lazy_binds = let_lazy_binds, let_expr = let_expr }, cs)
			_
				-> abort "convertCases [Let] (convertcases 53)" // <<- let_info 
*/

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
	convertCases ci (RecordUpdate cons_symbol expr exprs) cs
		# (expr, cs) = convertCases ci expr cs
		  (exprs, cs) = convertCases ci exprs cs
		= (RecordUpdate cons_symbol expr exprs, cs)		
	convertCases ci (TupleSelect tuple_symbol arg_nr expr) cs
		# (expr, cs) = convertCases ci expr cs
		= (TupleSelect tuple_symbol arg_nr expr, cs)
	convertCases ci (Case case_expr) cs
		= convertNonRootCase ci case_expr cs
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

convertNonRootCase ci=:{ci_bound_vars, ci_group_index, ci_common_defs} kees=:{ case_expr, case_guards, case_default, case_ident, case_info_ptr} cs
	# (EI_CaseTypeAndRefCounts case_type _, cs_expr_heap) = readPtr case_info_ptr cs.cs_expr_heap
	  cs = { cs & cs_expr_heap = cs_expr_heap }

	  (new_info_ptr, cs_var_heap) = newPtr (VI_LocalVar) cs.cs_var_heap
	  var_id = {id_name = "_x", id_info = nilPtr}
	  case_var = Var {var_name = var_id, var_info_ptr = new_info_ptr, var_expr_ptr = nilPtr}
	  case_free_var = {	fv_def_level = NotALevel, fv_name = var_id, fv_info_ptr = new_info_ptr, fv_count = 0}
	  cs = { cs & cs_var_heap = cs_var_heap}

// RWS test...

	  cases	= map (makeCase case_var) (splitGuards case_guards)
	  [firstCases : otherCases] = [(kees, NoPos) \\ kees <- cases]	
	  ((Case {case_guards},_), cs_var_heap, cs_expr_heap, _) =  mergeCases firstCases otherCases cs.cs_var_heap cs.cs_expr_heap NoErrorAdmin
	  cs = { cs & cs_var_heap = cs_var_heap, cs_expr_heap = cs_expr_heap}
	  kees = {kees & case_guards = case_guards}

// .. RWS test

	  kees = {kees & case_expr=case_var}

	  (case_expr, cs) = convertCases ci case_expr cs

	  (act_vars, form_vars, local_vars, caseExpr, old_fv_info_ptr_values,cs_var_heap)
			= copy_case_expr ci_bound_vars (Case kees) cs.cs_var_heap
	  cs = { cs & cs_var_heap = cs_var_heap}

	  (fun_symb, cs) = new_case_function case_ident case_type caseExpr case_free_var form_vars local_vars
	  							ci_bound_vars ci_group_index ci_common_defs cs

	# cs_var_heap=restore_old_fv_info_ptr_values old_fv_info_ptr_values ci_bound_vars cs.cs_var_heap
		with
			restore_old_fv_info_ptr_values [old_fv_info_ptr_value:old_fv_info_ptr_values] [({fv_info_ptr},type):bound_vars] var_heap
				# var_heap=writePtr fv_info_ptr old_fv_info_ptr_value var_heap
				= restore_old_fv_info_ptr_values old_fv_info_ptr_values bound_vars var_heap
			restore_old_fv_info_ptr_values [] bound_vars var_heap
				= var_heap
	# cs = { cs & cs_var_heap = cs_var_heap}

	= (App { app_symb = fun_symb, app_args = [case_expr : act_vars], app_info_ptr = nilPtr }, cs)
where
	get_case_var (Var var)
		=	var

	copy_case_expr bound_vars guards_and_default var_heap
//	    # var_heap = foldSt (\({fv_name,fv_info_ptr},type) -> writePtr fv_info_ptr (VI_BoundVar type) -*-> (fv_name,fv_info_ptr)) bound_vars var_heap
	    # (old_fv_info_ptr_values,var_heap) = store_VI_BoundVar_in_bound_vars_and_save_old_values bound_vars [] var_heap
	    	with
	    		store_VI_BoundVar_in_bound_vars_and_save_old_values [({fv_info_ptr},type):bound_vars] old_fv_info_ptr_values var_heap
    				# (old_fv_info_ptr_value,var_heap)=readPtr fv_info_ptr var_heap
	    			# var_heap=writePtr fv_info_ptr (VI_BoundVar type) var_heap
	    			# (old_fv_info_ptr_values,var_heap) = store_VI_BoundVar_in_bound_vars_and_save_old_values bound_vars old_fv_info_ptr_values var_heap
	    			= ([old_fv_info_ptr_value:old_fv_info_ptr_values],var_heap)
	    		store_VI_BoundVar_in_bound_vars_and_save_old_values [] old_fv_info_ptr_values var_heap
	    			= (old_fv_info_ptr_values,var_heap)
		  (expr, {cp_free_vars, cp_var_heap, cp_local_vars}) = copy guards_and_default { cp_free_vars = [], cp_var_heap = var_heap, cp_local_vars = [] }
		  (bound_vars, free_typed_vars, var_heap) = foldSt retrieve_variable cp_free_vars ([], [], cp_var_heap)
		= (bound_vars, free_typed_vars, cp_local_vars, expr, old_fv_info_ptr_values,var_heap)
//				-*-> ("copy_case_expr", length bound_vars, length free_typed_vars)
		where
			retrieve_variable (var_info_ptr, type) (bound_vars, free_typed_vars, var_heap)
				# (VI_FreeVar name new_ptr count type, var_heap) = readPtr var_info_ptr var_heap
				= ( [Var { var_name = name, var_info_ptr = var_info_ptr, var_expr_ptr = nilPtr} : bound_vars],
					[({ fv_def_level = NotALevel, fv_name = name, fv_info_ptr = new_ptr, fv_count = count }, type) : free_typed_vars], var_heap)

 	new_case_function opt_id {ct_result_type,ct_pattern_type,ct_cons_types} caseExpr case_var free_vars local_vars
			bound_vars group_index common_defs cs=:{cs_expr_heap}

		# body
			=	TransformedBody {tb_args=[case_var : [var \\ (var, _) <- free_vars]], tb_rhs=caseExpr}
	  	  type
			=	{	st_vars			= []
				,	st_args			= [ct_pattern_type : [ type \\ (_, type) <- free_vars]]
				,	st_arity		= 1 + length free_vars
				,	st_result		= ct_result_type
				,	st_context		= []
				,	st_attr_vars	= []
				,	st_attr_env		= []
				}
		  (body, cs)
		  	=	convertCasesInBody body (Yes type) group_index common_defs cs

		# (fun_symb,  (cs_next_fun_nr, cs_new_functions, cs_fun_heap))
				= newFunctionWithType opt_id body local_vars type group_index
						(cs.cs_next_fun_nr, cs.cs_new_functions, cs.cs_fun_heap)
		= (fun_symb, { cs & cs_fun_heap = cs_fun_heap, cs_next_fun_nr = cs_next_fun_nr, cs_new_functions = cs_new_functions })

splitGuards :: CasePatterns -> [CasePatterns]
splitGuards (AlgebraicPatterns index patterns)
	=	[AlgebraicPatterns index [pattern] \\ pattern <- patterns]
splitGuards (BasicPatterns basicType patterns)
	=	[BasicPatterns basicType [pattern] \\ pattern <- patterns]

makeCase :: Expression CasePatterns -> Expression
makeCase expr guard
	=	Case
	{	case_expr		= expr
	,	case_guards		= guard
	,	case_default	= No
	,	case_ident		= No
	,	case_info_ptr	= nilPtr
	,	case_explicit=False
	,	case_default_pos= NoPos
	}

::	TypedVariable =
	{	tv_free_var	:: !FreeVar
	,	tv_type		:: !AType
	}

copyExpression :: ![TypedVariable] !Expression !*VarHeap -> (![Expression], ![TypedVariable], ![FreeVar], !Expression, !*VarHeap)
copyExpression bound_vars expr var_heap
    # var_heap = foldSt (\{tv_free_var={fv_info_ptr},tv_type} -> writePtr fv_info_ptr (VI_BoundVar tv_type)) bound_vars var_heap
	  (expr, {cp_free_vars, cp_var_heap, cp_local_vars}) = copy expr { cp_free_vars = [], cp_var_heap = var_heap, cp_local_vars = [] }
	  (bound_vars, free_typed_vars, var_heap) = foldSt retrieve_variable cp_free_vars ([], [], cp_var_heap)
	= (bound_vars, free_typed_vars, cp_local_vars, expr, var_heap)
where
	retrieve_variable (var_info_ptr, type) (bound_vars, free_typed_vars, var_heap)
		# (VI_FreeVar name new_ptr count type, var_heap) = readPtr var_info_ptr var_heap
		= ( [Var { var_name = name, var_info_ptr = var_info_ptr, var_expr_ptr = nilPtr} : bound_vars],
			[{tv_free_var = { fv_def_level = NotALevel, fv_name = name, fv_info_ptr = new_ptr, fv_count = count }, tv_type = type} : free_typed_vars], var_heap)

::	CopyState =
	{	cp_free_vars	:: ![(VarInfoPtr,AType)]
	,	cp_local_vars	:: ![FreeVar]
	,	cp_var_heap		:: !.VarHeap
	}

class copy e :: !e !*CopyState -> (!e, !*CopyState)

instance copy BoundVar
where
	copy var=:{var_name,var_info_ptr} cp_info=:{cp_var_heap}
		# (var_info, cp_var_heap) = readPtr var_info_ptr cp_var_heap
		  cp_info = { cp_info & cp_var_heap = cp_var_heap }
		= case var_info of
			VI_FreeVar name new_info_ptr count type
				-> ({ var & var_info_ptr = new_info_ptr },
					{ cp_info & cp_var_heap = cp_info.cp_var_heap <:= (var_info_ptr, VI_FreeVar name new_info_ptr (inc count) type)})
						-*-> ("copy: VI_FreeVar", var_name.id_name, ptrToInt var_info_ptr)
			VI_LocalVar
				-> (var, cp_info)
						-*-> ("copy: VI_LocalVar", var_name.id_name)
			VI_BoundVar type
				# (new_info_ptr, cp_var_heap) = newPtr (VI_Labelled_Empty "copy [BoundVar]") cp_info.cp_var_heap // RWS ??? 
				-> ({ var & var_info_ptr = new_info_ptr },
					{ cp_info & cp_free_vars = [ (var_info_ptr, type) : cp_info.cp_free_vars ],
							cp_var_heap = cp_var_heap <:= (var_info_ptr, VI_FreeVar var_name new_info_ptr 1 type) })
						-*-> ("copy: VI_BoundVar", var_name.id_name, ptrToInt new_info_ptr)
			_
//				| True <<- ("copy BoundVar", var_name.id_name, ptrToInt var_info_ptr, var_info)
//				-> (var,cp_info)
				-> abort "copy [BoundVar] (convertcases, 612)" // <<- ("copy BoundVar", var_name.id_name, ptrToInt var_info_ptr, var_info)

instance copy Expression
where
	copy (Var var) cp_info
		# (var, cp_info) = copy var cp_info
		= (Var var, cp_info)
	copy (App app=:{app_args}) cp_info
		# (app_args, cp_info) = copy app_args cp_info
		= (App {app & app_args = app_args}, cp_info)
	copy (fun_expr @ exprs) cp_info
		# ((fun_expr, exprs), cp_info) = copy (fun_expr, exprs) cp_info
		= (fun_expr @ exprs, cp_info)
 	copy (Let lad=:{let_strict_binds,let_lazy_binds, let_expr}) cp_info=:{cp_var_heap, cp_local_vars}
		# (cp_local_vars, cp_var_heap) = foldSt bind_let_var let_strict_binds (cp_local_vars, cp_var_heap)
		# (cp_local_vars, cp_var_heap) = foldSt bind_let_var let_lazy_binds (cp_local_vars, cp_var_heap)
		# (let_strict_binds, cp_info) = copy let_strict_binds {cp_info & cp_var_heap = cp_var_heap, cp_local_vars = cp_local_vars }
		# (let_lazy_binds, cp_info) = copy let_lazy_binds cp_info
		# (let_expr, cp_info) = copy let_expr cp_info
		= (Let {lad & let_strict_binds = let_strict_binds, let_lazy_binds = let_lazy_binds, let_expr = let_expr }, cp_info)
	where
		bind_let_var {lb_dst} (local_vars, var_heap)
			= ([lb_dst : local_vars], var_heap <:= (lb_dst.fv_info_ptr, VI_LocalVar))
	copy (Case case_expr) cp_info
		# (case_expr, cp_info) = copy case_expr cp_info
		= (Case case_expr, cp_info)
	copy (Conditional cond) cp_info
		# (cond, cp_info) = copy cond cp_info
		= (Conditional cond, cp_info)
	copy expr=:(BasicExpr _ _) cp_info
		= (expr, cp_info)
	copy (MatchExpr opt_tuple constructor expr) cp_info
		# (expr, cp_info) = copy expr cp_info
		= (MatchExpr opt_tuple constructor expr, cp_info)
	copy (Selection is_unique expr selectors) cp_info
		# (expr, cp_info) = copy expr cp_info
		  (selectors, cp_info) = copy selectors cp_info
		= (Selection is_unique expr selectors, cp_info)
	copy (Update expr1 selectors expr2) cp_info
		# (expr1, cp_info) = copy expr1 cp_info
		  (selectors, cp_info) = copy selectors cp_info
		  (expr2, cp_info) = copy expr2 cp_info
		= (Update expr1 selectors expr2, cp_info)
	copy (RecordUpdate cons_symbol expr exprs) cp_info
		# (expr, cp_info) = copy expr cp_info
		  (exprs, cp_info) = copy exprs cp_info
		= (RecordUpdate cons_symbol expr exprs, cp_info)
	copy (TupleSelect tuple_symbol arg_nr expr) cp_info
		# (expr, cp_info) = copy expr cp_info
		= (TupleSelect tuple_symbol arg_nr expr, cp_info)
	copy EE cp_info
		= (EE, cp_info)
	copy (NoBind ptr) cp_info
		= (NoBind ptr, cp_info)
	copy expr cp_info
		= abort ("copy (Expression) does not match" -*-> expr)

instance copy (Optional a) | copy a
where
	copy (Yes expr) cp_info
		# (expr, cp_info) = copy expr cp_info
		= (Yes expr, cp_info)
	copy No cp_info
		= (No, cp_info)

instance copy Selection  
where
	copy (DictionarySelection record selectors expr_ptr index_expr) cp_info
		# (index_expr, cp_info) = copy index_expr cp_info
		  (selectors, cp_info) = copy selectors cp_info
		  (record, cp_info) = copy record cp_info
		= (DictionarySelection record selectors expr_ptr index_expr, cp_info)
	copy (ArraySelection selector expr_ptr index_expr) cp_info
		# (index_expr, cp_info) = copy index_expr cp_info
		= (ArraySelection selector expr_ptr index_expr, cp_info)
	copy selector cp_info
		= (selector, cp_info)

instance copy Case
where
	copy this_case=:{case_expr, case_guards, case_default} cp_info
		# ((case_expr,(case_guards,case_default)), cp_info) = copy (case_expr,(case_guards,case_default)) cp_info
		= ({ this_case & case_expr = case_expr, case_guards = case_guards, case_default = case_default}, cp_info) 

instance copy Conditional
where
	copy cond=:{if_cond, if_then, if_else} cp_info
		# ((if_cond,(if_then, if_else)), cp_info) = copy (if_cond,(if_then, if_else)) cp_info
		= ({ cond & if_cond=if_cond, if_then=if_then, if_else=if_else}, cp_info) 

instance copy CasePatterns
where
	copy (AlgebraicPatterns type patterns) cp_info
		# (patterns, cp_info) = copy patterns cp_info
		= (AlgebraicPatterns type patterns, cp_info) 
	copy (BasicPatterns type patterns) cp_info
		# (patterns, cp_info) = copy patterns cp_info
		= (BasicPatterns type patterns, cp_info) 

instance copy AlgebraicPattern
where
	copy pattern=:{ap_vars,ap_expr} cp_info=:{cp_var_heap}
		# (ap_expr, cp_info) = copy ap_expr { cp_info & cp_var_heap = foldSt (\{fv_info_ptr} -> writePtr fv_info_ptr VI_LocalVar) ap_vars cp_var_heap}
		= ({ pattern & ap_expr = ap_expr }, cp_info) 

instance copy BasicPattern
where
	copy pattern=:{bp_expr} cp_info
		# (bp_expr, cp_info) = copy bp_expr cp_info
		= ({ pattern & bp_expr = bp_expr }, cp_info) 

instance copy [a] | copy a
where
	copy l cp_info = mapSt copy l cp_info 

instance copy (a,b) | copy a & copy b
where
	copy t cp_info = app2St (copy, copy) t cp_info 

instance copy LetBind
where
	copy bind=:{lb_src} cp_info
		# (lb_src, cp_info) = copy lb_src cp_info
		= ({ bind & lb_src = lb_src }, cp_info) 

instance copy (Bind a b) | copy a
where
	copy bind=:{bind_src} cp_info
		# (bind_src, cp_info) = copy bind_src cp_info
		= ({ bind & bind_src = bind_src }, cp_info) 

instance <<< ExprInfo
where
	(<<<) file EI_Empty			= file <<< "*Empty*"
	(<<<) file (EI_CaseType _)	= file <<< "CaseType"

instance <<< (Ptr a)
where
	(<<<) file ptr = file <<< ptrToInt ptr  
/*
instance  <<<  FunctionBody
where
	(<<<) file (TransformedBody {tb_rhs}) = file <<<  tb_rhs

instance  <<<  CountedVariable
where
	(<<<) file {cv_variable,cv_count} = file <<< '<' <<< cv_variable <<< ',' <<< cv_count <<< '>'
*/

(-*->) infixl
(-*->) a b :== a // ---> b

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

:: NoErrorAdmin = NoErrorAdmin

mergeCases :: !(!Expression, !Position) ![(!Expression, !Position)] !*VarHeap !*ExpressionHeap !*NoErrorAdmin
			-> *(!(!Expression, !Position), !*VarHeap, !*ExpressionHeap, !*NoErrorAdmin)
mergeCases expr_and_pos [] var_heap symbol_heap error
	= (expr_and_pos, var_heap, symbol_heap, error)
mergeCases (Let lad=:{let_expr}, pos) exprs var_heap symbol_heap error
	# ((let_expr, _), var_heap, symbol_heap, error) = mergeCases (let_expr, NoPos) exprs var_heap symbol_heap error
	= ((Let {lad & let_expr = let_expr}, pos), var_heap,symbol_heap, error)
mergeCases (case_expr=:(Case first_case=:{case_expr = Var {var_info_ptr}, case_default = No}), case_pos)
			[(expr, expr_pos) : exprs] var_heap symbol_heap error
	# (split_result, var_heap, symbol_heap) = split_case var_info_ptr expr var_heap symbol_heap -*-> "mergeCases: Case (Var)"
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
		# us = { us_var_heap = var_heap, us_symbol_heap = symbol_heap, us_opt_type_heaps = No,us_cleanup_info = [], us_local_macro_functions = No}
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
			= (guards, var_heap, symbol_heap, /* checkError "" "incompatible patterns in case" */ error)
	merge_guards guards=:(BasicPatterns basic_type1 patterns1) (BasicPatterns basic_type2 patterns2) var_heap symbol_heap error
		| basic_type1 == basic_type2
			# (merged_patterns, var_heap, symbol_heap, error) = merge_basic_patterns patterns1 patterns2 var_heap symbol_heap error
			= (BasicPatterns basic_type1 merged_patterns, var_heap, symbol_heap, error) 
			= (guards, var_heap, symbol_heap, /* checkError "" "incompatible patterns in case" */ error)
	merge_guards guards=:(DynamicPatterns  patterns1) (DynamicPatterns  patterns2) var_heap symbol_heap error
		# (merged_patterns, var_heap, symbol_heap, error) = merge_dynamic_patterns patterns1 patterns2 var_heap symbol_heap error
		= (DynamicPatterns merged_patterns, var_heap, symbol_heap, error) 
	merge_guards patterns1 patterns2 var_heap symbol_heap error
		= (patterns1, var_heap, symbol_heap, /* checkError "" "incompatible patterns in case" */ error)
		
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
		| new_pattern.ap_symbol == ap_symbol -*-> ("merge_algebraic_pattern_with_patterns", new_pattern.ap_symbol == ap_symbol)
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
			# us = { us_var_heap = build_aliases vars ap_vars var_heap, us_symbol_heap = symbol_heap, us_opt_type_heaps = No,us_cleanup_info=[], us_local_macro_functions = No}
			  ui = {ui_handle_aci_free_vars = RemoveThem, ui_convert_module_n= -1, ui_conversion_table=No}
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
	= case case_default -*-> "mergeCases: Case (No Var)" of
		Yes default_expr
			# ((default_expr, case_default_pos), var_heap, symbol_heap, error) = mergeCases (default_expr, case_default_pos) [expr : exprs] var_heap symbol_heap error
			-> ((Case { first_case & case_default = Yes default_expr, case_default_pos = case_default_pos }, case_pos),
				var_heap, symbol_heap, error)
		No
			# ((default_expr, pos), var_heap, symbol_heap, error) = mergeCases expr exprs var_heap symbol_heap error
			-> ((Case { first_case & case_default = Yes default_expr, case_default_pos = pos }, case_pos),
				var_heap, symbol_heap, error)
mergeCases expr_and_pos _ var_heap symbol_heap error
	= (expr_and_pos, var_heap, symbol_heap, /* checkWarning "" " alternative will never match" */ error)



