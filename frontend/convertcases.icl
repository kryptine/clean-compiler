implementation module convertcases

import syntax, transform, checksupport, StdCompare, check, utilities, trans, general, RWSDebug


::	*ConversionInfo =
	{	ci_new_functions 	:: ![FunctionInfoPtr]
	,	ci_fun_heap			:: !*FunctionHeap
	,	ci_var_heap			:: !*VarHeap
	,	ci_expr_heap		:: !*ExpressionHeap
	,	ci_next_fun_nr		:: !Index
	}
	 
getIdent (Yes ident) fun_nr
	= ident
getIdent No fun_nr
	= { id_name = "_f" +++ toString fun_nr, id_info = nilPtr }


class convertCases a :: ![(FreeVar, AType)] !Index !{# CommonDefs } !a  !*ConversionInfo -> (!a, !*ConversionInfo)

instance convertCases [a] | convertCases a
where
	convertCases bound_vars group_index common_defs l ci = mapSt (convertCases bound_vars group_index common_defs) l ci 
		
instance convertCases (a,b) | convertCases a & convertCases b
where
	convertCases bound_vars group_index common_defs t ci
		= app2St (convertCases bound_vars group_index common_defs, convertCases bound_vars group_index common_defs) t ci

instance convertCases (Bind a b) | convertCases a
where
	convertCases bound_vars group_index common_defs bind=:{bind_src} ci
		# (bind_src, ci) = convertCases bound_vars group_index common_defs bind_src ci
		= ({ bind & bind_src = bind_src }, ci)

instance convertCases DynamicExpr
where
	convertCases bound_vars group_index common_defs dynamik=:{dyn_expr} ci
		# (dyn_expr, ci) = convertCases bound_vars group_index common_defs dyn_expr ci
		= ({ dynamik & dyn_expr = dyn_expr }, ci)
	
instance convertCases Let
where
	convertCases bound_vars group_index common_defs lad=:{let_strict_binds,let_lazy_binds,let_expr,let_info_ptr} ci=:{ci_expr_heap}
		# (let_info, ci_expr_heap) =  readPtr let_info_ptr ci_expr_heap
		  ci = { ci & ci_expr_heap = ci_expr_heap }
		= case let_info of
			EI_LetType let_type
				# bound_vars = addLetVars (let_strict_binds ++ let_lazy_binds) let_type bound_vars
				# (let_strict_binds, ci) = convertCases bound_vars group_index common_defs let_strict_binds ci
				# (let_lazy_binds, ci) = convertCases bound_vars group_index common_defs let_lazy_binds ci
				# (let_expr, ci) = convertCases bound_vars group_index common_defs let_expr ci
				-> ({ lad & let_strict_binds = let_strict_binds, let_lazy_binds = let_lazy_binds, let_expr = let_expr }, ci)
			_
				-> abort "convertCases [Let] (convertcases 53)" // <<- let_info 

addLetVars [{bind_dst} : binds] [bind_type : bind_types] bound_vars
	= addLetVars binds bind_types [ (bind_dst, bind_type) : bound_vars ]
addLetVars [] _ bound_vars
	= bound_vars

instance convertCases Expression  
where
	convertCases bound_vars group_index common_defs (App app=:{app_args}) ci
		# (app_args, ci) = convertCases bound_vars group_index common_defs app_args ci
		= (App {app & app_args = app_args}, ci)
	convertCases bound_vars group_index common_defs (fun_expr @ exprs) ci
		# ((fun_expr, exprs), ci) = convertCases bound_vars group_index common_defs (fun_expr, exprs) ci
		= (fun_expr @ exprs, ci)
	convertCases bound_vars group_index common_defs (Let lad) ci
		# (lad, ci) = convertCases bound_vars group_index common_defs lad ci
		= (Let lad, ci)
	convertCases bound_vars group_index common_defs (MatchExpr opt_tuple constructor expr) ci
		# (expr, ci) = convertCases bound_vars group_index common_defs expr ci
		= (MatchExpr opt_tuple constructor expr, ci)
	convertCases bound_vars group_index common_defs (Selection is_unique expr selectors) ci
		# (expr, ci) = convertCases bound_vars group_index common_defs expr ci
		  (selectors, ci) = convertCases bound_vars group_index common_defs selectors ci
		= (Selection is_unique expr selectors, ci)		
	convertCases bound_vars group_index common_defs (Update expr1 selectors expr2) ci
		# (expr1, ci) = convertCases bound_vars group_index common_defs expr1 ci
		  (selectors, ci) = convertCases bound_vars group_index common_defs selectors ci
		  (expr2, ci) = convertCases bound_vars group_index common_defs expr2 ci
		= (Update expr1 selectors expr2, ci)		
	convertCases bound_vars group_index common_defs (RecordUpdate cons_symbol expression expressions) ci
		# (expression, ci) = convertCases bound_vars group_index common_defs expression ci
		  (expressions, ci) = convertCases bound_vars group_index common_defs expressions ci
		= (RecordUpdate cons_symbol expression expressions, ci)		
	convertCases bound_vars group_index common_defs (TupleSelect tuple_symbol arg_nr expr) ci
		# (expr, ci) = convertCases bound_vars group_index common_defs expr ci
		= (TupleSelect tuple_symbol arg_nr expr, ci)
	convertCases bound_vars group_index common_defs (Case case_expr) ci
		= convertCasesInCaseExpression bound_vars group_index common_defs cHasNoDefault case_expr ci
/*
	convertCases bound_vars group_index common_defs (DynamicExpr dynamik) ci
		# (dynamik, ci) = convertCases bound_vars group_index common_defs dynamik ci
		= (DynamicExpr dynamik, ci)
*/
	convertCases bound_vars group_index common_defs expr ci
		= (expr, ci)

instance convertCases Selection  
where
	convertCases bound_vars group_index common_defs (DictionarySelection record selectors expr_ptr index_expr) ci
		# (index_expr, ci) = convertCases bound_vars group_index common_defs index_expr ci
		  (selectors, ci) = convertCases bound_vars group_index common_defs selectors ci
		= (DictionarySelection record selectors expr_ptr index_expr, ci)
	convertCases bound_vars group_index common_defs (ArraySelection selector expr_ptr index_expr) ci
		# (index_expr, ci) = convertCases bound_vars group_index common_defs index_expr ci
		= (ArraySelection selector expr_ptr index_expr, ci)
	convertCases bound_vars group_index common_defs selector ci
		= (selector, ci)

cHasNoDefault :== nilPtr

convertDefaultToExpression default_ptr (EI_Default expr type prev_default) bound_vars group_index common_defs ci=:{ci_var_heap}
    # ci_var_heap = foldSt (\({fv_info_ptr}, type) -> writePtr fv_info_ptr (VI_BoundVar type)) bound_vars ci_var_heap
	  (expression, {cp_free_vars, cp_var_heap, cp_local_vars}) = copy expr { cp_free_vars = [], cp_var_heap = ci_var_heap, cp_local_vars = [] }
	  (act_args, free_typed_vars, ci_var_heap) = foldSt retrieveVariable cp_free_vars ([], [], cp_var_heap)
	  (fun_symb, ci) = new_default_function free_typed_vars cp_local_vars expression type prev_default group_index common_defs { ci & ci_var_heap = ci_var_heap }
	= (App { app_symb = fun_symb, app_args = act_args, app_info_ptr = nilPtr }, 
		{ ci & ci_expr_heap = ci.ci_expr_heap <:= (default_ptr, EI_DefaultFunction fun_symb act_args)})
where
	new_default_function free_vars local_vars rhs_expr result_type prev_default group_index common_defs ci
		# (guarded_exprs, ci) = convertPatternExpression [] [free_vars] group_index common_defs prev_default rhs_expr ci
		  fun_bodies  = map build_pattern guarded_exprs
		  arg_types = map (\(_,type) -> type) free_vars
		  (fun_symb,  (ci_next_fun_nr, ci_new_functions, ci_fun_heap))
				= newFunction No (BackendBody fun_bodies) local_vars arg_types result_type group_index
						(ci.ci_next_fun_nr, ci.ci_new_functions, ci.ci_fun_heap)
		= (fun_symb, { ci & ci_fun_heap = ci_fun_heap, ci_next_fun_nr = ci_next_fun_nr, ci_new_functions = ci_new_functions })

	build_pattern ([ right_patterns : _ ], bb_rhs)
		= { bb_args = right_patterns, bb_rhs = bb_rhs }

convertDefaultToExpression default_ptr (EI_DefaultFunction fun_symb act_args) bound_vars group_index common_defs ci
	= (App { app_symb = fun_symb, app_args = act_args, app_info_ptr = nilPtr }, ci)

combineDefaults default_ptr No bound_vars guards group_index common_defs ci=:{ci_expr_heap}
	| isNilPtr default_ptr
		= (No, ci)
	| case_is_partial guards common_defs
		# (default_info, ci_expr_heap) = readPtr default_ptr ci_expr_heap
		  (default_expr, ci) = convertDefaultToExpression default_ptr default_info bound_vars group_index common_defs { ci & ci_expr_heap = ci_expr_heap }
		= (Yes default_expr, ci)
		= (No, ci)
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
			= is_partial_expression ap_expr || has_partial_pattern patterns
	case_is_partial (BasicPatterns BT_Bool bool_patterns) common_defs
		= length bool_patterns < 2 || has_partial_basic_pattern bool_patterns
	where
		has_partial_basic_pattern []
			= False
		has_partial_basic_pattern [{bp_expr} : patterns]
			= is_partial_expression bp_expr || has_partial_basic_pattern patterns
	case_is_partial patterns common_defs
		= True
	
	is_partial_expression (Case {case_guards,case_default=No})
		= case_is_partial case_guards common_defs
	is_partial_expression (Case {case_guards,case_default=Yes case_default})
		= is_partial_expression case_default && case_is_partial case_guards common_defs
	is_partial_expression (Let {let_expr})
		= is_partial_expression let_expr
	is_partial_expression _
		= False

combineDefaults default_ptr this_default bound_vars guards group_index common_defs ci
	= (this_default, ci)
	

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

convertCasesInCaseExpression bound_vars group_index common_defs default_ptr { case_expr, case_guards, case_default, case_ident, case_info_ptr} ci
	# (case_default, ci) = combineDefaults default_ptr case_default bound_vars case_guards group_index common_defs ci
	  (case_expr, ci) = convertCases bound_vars group_index common_defs case_expr ci
	  (EI_CaseTypeAndRefCounts case_type ref_counts, ci_expr_heap) = readPtr case_info_ptr ci.ci_expr_heap
	  (act_vars, form_vars, opt_free_var, local_vars, (case_guards, case_default), ci_var_heap)
			= copy_case_expression bound_vars (get_variable case_expr case_type.ct_pattern_type) (case_guards,case_default) ci.ci_var_heap
	  (fun_symb, ci) = new_case_function case_ident case_guards case_default case_type opt_free_var form_vars local_vars
	  							group_index common_defs default_ptr { ci & ci_var_heap = ci_var_heap, ci_expr_heap = ci_expr_heap }
	= (App { app_symb = fun_symb, app_args = [ case_expr : act_vars ], app_info_ptr = nilPtr }, ci)
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
			group_index common_defs prev_default ci=:{ci_expr_heap}
		# (default_ptr, ci_expr_heap) = makePtrToDefault case_default ct_result_type prev_default ci_expr_heap
		  (fun_bodies, ci) = convertPatterns patterns ct_cons_types opt_var [] free_vars default_ptr group_index common_defs { ci & ci_expr_heap = ci_expr_heap }
		  (fun_bodies, ci) = convertDefault default_ptr opt_var [] free_vars group_index common_defs (fun_bodies, ci)
		  (fun_symb,  (ci_next_fun_nr, ci_new_functions, ci_fun_heap))
				= newFunction opt_id (BackendBody fun_bodies) local_vars [ct_pattern_type : [ type \\ (_, type) <- free_vars]] ct_result_type group_index
						(ci.ci_next_fun_nr, ci.ci_new_functions, ci.ci_fun_heap)
		= (fun_symb, { ci & ci_fun_heap = ci_fun_heap, ci_next_fun_nr = ci_next_fun_nr, ci_new_functions = ci_new_functions })



makePtrToDefault (Yes default_expr) type prev_default_ptr expr_heap
	= newPtr (EI_Default default_expr type prev_default_ptr) expr_heap
makePtrToDefault No type prev_default_ptr expr_heap
	= (cHasNoDefault, expr_heap)


convertDefault default_ptr opt_var left_vars right_vars group_index common_defs (fun_bodies, ci)
	| isNilPtr default_ptr
		= (fun_bodies, ci)
		# (default_info, ci_expr_heap) = readPtr default_ptr ci.ci_expr_heap
		= convert_default default_info opt_var left_vars right_vars group_index common_defs (fun_bodies, { ci & ci_expr_heap = ci_expr_heap})
where
	convert_default (EI_Default default_expr type prev_default) opt_var left_vars right_vars group_index common_defs (fun_bodies, ci)
		# (bb_rhs, ci) = convertRootExpression (left_vars ++ consOptional opt_var right_vars) group_index common_defs prev_default default_expr ci
		  bb_args = build_args opt_var left_vars right_vars
		= (fun_bodies ++ [{ bb_args = bb_args, bb_rhs = bb_rhs }], ci)	
	convert_default (EI_DefaultFunction fun_symb act_args) opt_var left_vars right_vars group_index common_defs (fun_bodies, ci)
		# bb_args = build_args opt_var left_vars right_vars
		  bb_rhs = App { app_symb = fun_symb, app_args = act_args, app_info_ptr = nilPtr }
		= (fun_bodies ++ [{ bb_args = bb_args, bb_rhs = bb_rhs }], ci)	

	build_args (Yes (var,type)) left_vars right_vars
		= mapAppend typed_free_var_to_pattern left_vars [FP_Variable var : map typed_free_var_to_pattern right_vars]
	build_args No left_vars right_vars
		= mapAppend typed_free_var_to_pattern left_vars [FP_Empty : map typed_free_var_to_pattern right_vars]

	typed_free_var_to_pattern (free_var, type) = FP_Variable free_var


newFunction :: !(Optional Ident) !FunctionBody ![FreeVar] ![AType] !AType !Int !(!Int, ![FunctionInfoPtr],!*FunctionHeap)
	-> (! SymbIdent, !(!Int, ![FunctionInfoPtr],!*FunctionHeap))
newFunction opt_id fun_bodies local_vars arg_types result_type group_index (ci_next_fun_nr, ci_new_functions, ci_fun_heap)
	# (fun_def_ptr, ci_fun_heap) = newPtr FI_Empty ci_fun_heap
	  fun_id = getIdent opt_id ci_next_fun_nr
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
			,	fun_kind		= FK_Function cNameNotLocationDependent
			,	fun_lifted		= 0
			,	fun_info		= { EmptyFunInfo & fi_group_index = group_index, fi_local_vars = local_vars }
			}
	= ({ symb_name = fun_id, symb_kind = SK_GeneratedFunction fun_def_ptr ci_next_fun_nr, symb_arity = arity },
			(inc ci_next_fun_nr, [fun_def_ptr : ci_new_functions],
				ci_fun_heap <:= (fun_def_ptr,  FI_Function { gf_fun_def = fun_def, gf_instance_info = II_Empty,
	  				  gf_fun_index = ci_next_fun_nr, gf_cons_args = {cc_size=0, cc_args = [], cc_linear_bits = []} })))


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

convertPatterns :: CasePatterns [[AType]] (Optional (FreeVar,AType)) [.(FreeVar,AType)] [(FreeVar,AType)] (Ptr ExprInfo) Index {#CommonDefs} *ConversionInfo -> *(!.[BackendBody],!*ConversionInfo);
convertPatterns (AlgebraicPatterns algtype patterns) cons_types opt_var left_vars right_vars default_ptr group_index common_defs ci
	# (guarded_exprs_list, ci) = mapSt (convert_algebraic_guard_into_function_pattern opt_var left_vars right_vars
			group_index common_defs default_ptr) (zip2 patterns cons_types) ci
	= (flatten guarded_exprs_list, ci)
where
	convert_algebraic_guard_into_function_pattern opt_var left_vars right_vars group_index common_defs default_ptr ({ap_symbol, ap_vars, ap_expr}, cons_arg_types) ci
		# pattern_vars = zip2 ap_vars cons_arg_types
		  (guarded_exprs, ci)
				= convertPatternExpression (consOptional opt_var left_vars) [pattern_vars, right_vars] group_index common_defs default_ptr ap_expr ci
		= (map (complete_pattern left_vars ap_symbol (getOptionalFreeVar opt_var)) guarded_exprs, ci)
	where
		complete_pattern left_vars cons_symbol optional_var ([ pattern_args, right_patterns : _ ], bb_rhs)
			# bb_args = mapAppend selectFreeVar left_vars [FP_Algebraic cons_symbol pattern_args optional_var : right_patterns ]
			= { bb_args = bb_args, bb_rhs = bb_rhs }			
convertPatterns (BasicPatterns bastype patterns) cons_types opt_var left_vars right_vars default_ptr group_index common_defs ci
	# (guarded_exprs_list, ci) = mapSt (convert_basic_guard_into_function_pattern opt_var left_vars right_vars
			group_index common_defs default_ptr) patterns ci
	= (flatten guarded_exprs_list, ci)
where
	convert_basic_guard_into_function_pattern opt_var left_vars right_vars group_index common_defs default_ptr {bp_value, bp_expr} ci
		# (guarded_exprs, ci)
				= convertPatternExpression (consOptional opt_var left_vars) [right_vars] group_index common_defs default_ptr bp_expr ci
		= (map (complete_pattern left_vars bp_value (getOptionalFreeVar opt_var)) guarded_exprs, ci)
	where
		complete_pattern left_vars value optional_var ([ right_patterns : _ ], bb_rhs)
			# bb_args = mapAppend selectFreeVar left_vars [FP_Basic value optional_var : right_patterns ]
			= { bb_args = bb_args, bb_rhs = bb_rhs }

convertPatternExpression :: ![(FreeVar,AType)] ![[(FreeVar,AType)]] !Index !{#CommonDefs} !ExprInfoPtr !Expression !*ConversionInfo
	-> *(![([[FunctionPattern]], !Expression)], !*ConversionInfo)
convertPatternExpression left_vars right_vars group_index common_defs default_ptr
		case_expr=:(Case {case_expr = Var var=:{var_info_ptr}, case_guards, case_default, case_info_ptr}) ci
	| list_contains_variable var_info_ptr right_vars
		= case case_guards of
			BasicPatterns type basic_patterns
				# split_result = split_list_of_vars var_info_ptr [] right_vars
				  (default_patterns, ci) = convert_default left_vars split_result group_index common_defs case_default ci
				  (guarded_exprs, ci) = mapSt (convert_basic_guard_into_function_pattern left_vars split_result group_index common_defs) basic_patterns ci
				-> (flatten guarded_exprs ++ default_patterns, ci)
			AlgebraicPatterns type algebraic_patterns
				# (EI_CaseTypeAndRefCounts {ct_cons_types} _, ci_expr_heap) = readPtr case_info_ptr ci.ci_expr_heap
		  		  split_result = split_list_of_vars var_info_ptr [] right_vars
				  (default_patterns, ci) = convert_default left_vars split_result group_index common_defs case_default { ci & ci_expr_heap = ci_expr_heap }
				  (guarded_exprs, ci) = mapSt (convert_algebraic_guard_into_function_pattern left_vars split_result group_index common_defs case_info_ptr)
											(zip2 algebraic_patterns ct_cons_types) ci
				-> (flatten guarded_exprs ++ default_patterns, ci)
			_
				-> convertToRhsExpression left_vars right_vars group_index common_defs default_ptr case_expr ci
		= convertToRhsExpression left_vars right_vars group_index common_defs default_ptr case_expr ci
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
	
	convert_default left_vars ((fv,fv_type), list_of_left, list_of_right) group_index common_defs (Yes default_expr) ci
		# (guarded_exprs, ci)
				= convertPatternExpression (left_vars ++ [ (fv,fv_type) : flatten list_of_left ]) list_of_right group_index common_defs default_ptr default_expr ci
		= (map (complete_pattern list_of_left fv) guarded_exprs, ci) 
	where
		complete_pattern list_of_left this_var (list_of_patterns, expr)
			= (complete_patterns list_of_left (FP_Variable this_var) list_of_patterns, expr)
	convert_default left_vars ((fv,fv_type), list_of_left, list_of_right) group_index common_defs No ci
		= ([], ci)
	
	convert_basic_guard_into_function_pattern left_vars ((fv,fv_type), list_of_left, list_of_right) group_index common_defs {bp_value, bp_expr} ci
		# (guarded_exprs, ci)
				= convertPatternExpression (left_vars ++ [ (fv,fv_type) : flatten list_of_left ]) list_of_right group_index common_defs default_ptr bp_expr ci
		= (map (complete_pattern list_of_left bp_value (Yes fv)) guarded_exprs, ci) 
	where
		complete_pattern list_of_left value opt_var (list_of_patterns, expr)
			= (complete_patterns list_of_left (FP_Basic value opt_var) list_of_patterns, expr)
	
	convert_algebraic_guard_into_function_pattern left_vars ((fv,fv_type), list_of_left, list_of_right) group_index common_defs case_info_ptr
				({ap_symbol, ap_vars, ap_expr}, arg_types) ci=:{ci_expr_heap}
		# (guarded_exprs, ci)
				= convertPatternExpression (left_vars ++ [ (fv,fv_type) : flatten list_of_left ]) [ zip2 ap_vars arg_types : list_of_right ]
						 group_index common_defs default_ptr ap_expr { ci & ci_expr_heap = ci_expr_heap }
		= (map (complete_pattern list_of_left ap_symbol (Yes fv)) guarded_exprs, ci) 
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

convertPatternExpression left_vars right_vars group_index common_defs default_ptr expr ci
	= convertToRhsExpression left_vars right_vars group_index common_defs default_ptr expr ci

convertToRhsExpression left_vars right_vars group_index common_defs default_ptr expr ci
	# (bb_rhs, ci) = convertRootExpression (left_vars ++ flatten right_vars) group_index common_defs default_ptr expr ci
	= ([(map (map selectFreeVar) right_vars, bb_rhs)], ci)
	
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

::	ImportedFunctions 	:== [Global Index]

addNewFunctionsToGroups :: !{#.CommonDefs} FunctionHeap ![FunctionInfoPtr] !*{! Group} !*{#{# CheckedTypeDef}} !ImportedFunctions !*TypeHeaps !*VarHeap
	-> (!*{! Group}, ![FunDef],  !*{#{# CheckedTypeDef}}, !ImportedConstructors, !*TypeHeaps, !*VarHeap)
addNewFunctionsToGroups common_defs fun_heap new_functions groups imported_types imported_conses type_heaps var_heap
	= foldSt (add_new_function_to_group fun_heap common_defs) new_functions (groups, [], imported_types, imported_conses, type_heaps, var_heap)
where

	add_new_function_to_group :: !FunctionHeap  !{# CommonDefs} !FunctionInfoPtr
				!(!*{! Group}, ![FunDef], !*{#{# CheckedTypeDef}}, !ImportedConstructors, !*TypeHeaps, !*VarHeap)
					-> (!*{! Group}, ![FunDef],  !*{#{# CheckedTypeDef}}, !ImportedConstructors, !*TypeHeaps, !*VarHeap)
	add_new_function_to_group fun_heap common_defs fun_ptr (groups, fun_defs, imported_types, imported_conses, type_heaps, var_heap)
		# (FI_Function {gf_fun_def,gf_fun_index}) = sreadPtr fun_ptr fun_heap
		  group_index = gf_fun_def.fun_info.fi_group_index
		  (Yes ft) = gf_fun_def.fun_type
		  (ft, imported_types, imported_conses, type_heaps, var_heap) = convertSymbolType common_defs ft imported_types imported_conses type_heaps var_heap
		# (group, groups) = groups![group_index]
		= ({ groups & [group_index] = { group & group_members = [gf_fun_index : group.group_members]} },
				[ { gf_fun_def & fun_type = Yes ft }: fun_defs], imported_types, imported_conses, type_heaps, var_heap)

convertCasesOfFunctionsIntoPatterns :: !*{! Group} !{# {# FunType} } !{# CommonDefs} !*{#FunDef} !*{#{# CheckedTypeDef}}
		!ImportedConstructors !*VarHeap !*TypeHeaps !*ExpressionHeap
			-> (!ImportedFunctions, !*{! Group}, !*{#FunDef}, !*{#{# CheckedTypeDef}}, !ImportedConstructors, !*VarHeap, !*TypeHeaps, !*ExpressionHeap)
convertCasesOfFunctionsIntoPatterns groups dcl_functions common_defs fun_defs imported_types imported_conses var_heap type_heaps expr_heap
	#! nr_of_funs = size fun_defs
	# (groups, (fun_defs, collected_imports, {ci_new_functions, ci_var_heap, ci_expr_heap, ci_fun_heap}))
			= convert_groups 0 groups dcl_functions common_defs
				(fun_defs, [], { ci_new_functions = [], ci_fun_heap = newHeap, ci_var_heap = var_heap, ci_expr_heap = expr_heap, ci_next_fun_nr = nr_of_funs })
	  (groups, new_fun_defs, imported_types, imported_conses, type_heaps, ci_var_heap)
			= addNewFunctionsToGroups common_defs ci_fun_heap ci_new_functions groups imported_types imported_conses type_heaps ci_var_heap
//	  		= foldSt (add_new_function_to_group ci_fun_heap common_defs) ci_new_functions (groups, [], imported_types, imported_conses, type_heaps, ci_var_heap)
	  (imported_functions, imported_conses) = foldSt split collected_imports ([], imported_conses)
	= (imported_functions, groups, { fundef \\ fundef <- [ fundef \\ fundef <-: fun_defs ] ++ new_fun_defs },
			imported_types, imported_conses, ci_var_heap, type_heaps, ci_expr_heap)
where
	convert_groups group_nr groups dcl_functions common_defs fun_defs_and_ci
		| group_nr == size groups
			= (groups, fun_defs_and_ci)
			# (group, groups) = groups![group_nr]
			= convert_groups (inc group_nr) groups dcl_functions common_defs
				(foldSt (convert_function group_nr dcl_functions common_defs) group.group_members fun_defs_and_ci)


	convert_function group_index dcl_functions common_defs fun (fun_defs, collected_imports, ci)
		# (fun_def, fun_defs) = fun_defs![fun]
		# {fun_body,fun_type} = fun_def
		  (fun_body, (collected_imports, ci)) = eliminate_code_sharing_in_function dcl_functions common_defs fun_body /* (fun_body ---> ("convert_function", fun_def.fun_symb, fun_body)) */ (collected_imports, ci)		  		
		  (fun_body, ci) = convert_cases_into_function_patterns fun_body fun_type group_index common_defs ci
		= ({fun_defs & [fun] = { fun_def & fun_body = fun_body }}, collected_imports, ci)

	convert_cases_into_function_patterns (TransformedBody {tb_args,tb_rhs=Case {case_expr = Var var=:{var_info_ptr}, case_guards, case_default, case_info_ptr}})
			(Yes {st_result,st_args}) group_index common_defs ci=:{ci_expr_heap}
		# (EI_CaseTypeAndRefCounts case_type _, ci_expr_heap) = readPtr case_info_ptr ci_expr_heap
		  (default_ptr, ci_expr_heap) = makePtrToDefault case_default st_result cHasNoDefault ci_expr_heap
		  vars_with_types = zip2 tb_args st_args
		  (form_var_with_type, left_vars, right_vars) = split_vars var_info_ptr vars_with_types
		  (fun_bodies, ci) = convertPatterns case_guards case_type.ct_cons_types (Yes form_var_with_type) left_vars right_vars default_ptr group_index common_defs
					{ ci & ci_expr_heap = ci_expr_heap }
		  (fun_bodies, ci) = convertDefault default_ptr (Yes form_var_with_type) left_vars right_vars group_index common_defs (fun_bodies, ci) 
		= (BackendBody fun_bodies, ci)
	where
		split_vars var_info_ptr [ form_var_with_type=:({fv_info_ptr},_) : free_vars]
			| var_info_ptr == fv_info_ptr
				= (form_var_with_type, [], free_vars)
				# (form_var, left, right) = split_vars var_info_ptr free_vars
				= (form_var, [form_var_with_type : left], right)			
	convert_cases_into_function_patterns (TransformedBody {tb_args,tb_rhs}) (Yes {st_result,st_args}) group_index common_defs ci
		# (tb_rhs, ci) = convertRootExpression (zip2 tb_args st_args) group_index common_defs cHasNoDefault tb_rhs ci
		= (BackendBody [ { bb_args = map FP_Variable tb_args, bb_rhs = tb_rhs }], ci)

	eliminate_code_sharing_in_function dcl_functions common_defs (TransformedBody body=:{tb_rhs}) (collected_imports, ci=:{ci_expr_heap,ci_var_heap})
		# {rc_var_heap, rc_expr_heap, rc_imports} = weightedRefCount dcl_functions common_defs 1 tb_rhs
				{ rc_var_heap = ci_var_heap, rc_expr_heap = ci_expr_heap, rc_free_vars = [], rc_imports = collected_imports} 
//		  	---> ("eliminate_code_sharing_in_function (weightedRefCount)", tb_rhs)
		  (tb_rhs, {di_lets,di_var_heap,di_expr_heap}) = distributeLets 1 tb_rhs { di_lets = [], di_var_heap = rc_var_heap, di_expr_heap = rc_expr_heap}
		  (tb_rhs, (var_heap, expr_heap)) = buildLetExpr di_lets tb_rhs (di_var_heap,di_expr_heap)
		= (TransformedBody { body & tb_rhs = tb_rhs }, (rc_imports, { ci & ci_var_heap = var_heap, ci_expr_heap = expr_heap }))
		  	==> ("eliminate_code_sharing_in_function (distributeLets)", tb_rhs)

	split (SK_Function fun_symb) (collected_functions, collected_conses)
		= ([fun_symb : collected_functions], collected_conses)
	split (SK_Constructor cons_symb) (collected_functions, collected_conses)
		= (collected_functions, [ cons_symb : collected_conses])

convertDclModule :: !{# DclModule} !{# CommonDefs} !*{#{# CheckedTypeDef}} !ImportedConstructors !*VarHeap !*TypeHeaps
	-> (!*{#{# CheckedTypeDef}}, !ImportedConstructors, !*VarHeap, !*TypeHeaps)
convertDclModule dcl_mods common_defs imported_types imported_conses var_heap type_heaps
	# {dcl_functions,dcl_common=dcl_common=:{com_type_defs,com_cons_defs,com_selector_defs},dcl_conversions} = dcl_mods.[cIclModIndex]
	= case dcl_conversions of
		Yes conversion_table
			# (icl_type_defs, imported_types) = imported_types![cIclModIndex]
			  common_defs = { common \\ common <-: common_defs }
			  common_defs = { common_defs & [cIclModIndex] = dcl_common }
			  types_and_heaps = convert_dcl_functions dcl_functions common_defs ( { imported_types & [cIclModIndex] = com_type_defs }, imported_conses, var_heap, type_heaps)
			  types_and_heaps = convertConstructorTypes com_cons_defs common_defs types_and_heaps
			  (imported_types, imported_conses, var_heap, type_heaps) = convertSelectorTypes com_selector_defs common_defs types_and_heaps
			-> ({ imported_types & [cIclModIndex] = icl_type_defs}, imported_conses, var_heap, type_heaps)
		No
			-> (imported_types, imported_conses, var_heap, type_heaps)
where
	convert_dcl_functions dcl_functions common_defs types_and_heaps
		= iFoldSt (convert_dcl_function dcl_functions common_defs) 0 (size dcl_functions) types_and_heaps

	convert_dcl_function dcl_functions common_defs dcl_index (imported_types, imported_conses, var_heap, type_heaps)
		# {ft_type, ft_type_ptr} = dcl_functions.[dcl_index]
		  (ft_type, imported_types, imported_conses, type_heaps, var_heap) = convertSymbolType common_defs ft_type imported_types imported_conses type_heaps var_heap
		= (imported_types, imported_conses, var_heap <:= (ft_type_ptr, VI_ExpandedType ft_type), type_heaps)

convertConstructorTypes cons_defs common_defs types_and_heaps
	= iFoldSt (convert_constructor_type common_defs cons_defs) 0 (size cons_defs) types_and_heaps
where
	convert_constructor_type common_defs cons_defs cons_index (imported_types, imported_conses, var_heap, type_heaps)  
		# {cons_type_ptr, cons_type} = cons_defs.[cons_index]
		  (cons_type, imported_types, imported_conses, type_heaps, var_heap)
				= convertSymbolType common_defs cons_type imported_types imported_conses type_heaps var_heap
		= (imported_types, imported_conses, var_heap <:= (cons_type_ptr, VI_ExpandedType cons_type), type_heaps)
		

convertSelectorTypes selector_defs common_defs types_and_heaps
	= iFoldSt (convert_selector_type common_defs selector_defs) 0 (size selector_defs) types_and_heaps
where
	convert_selector_type common_defs selector_defs sel_index (imported_types, imported_conses, var_heap, type_heaps)  
		# {sd_type_ptr, sd_type} = selector_defs.[sel_index]
		  (sd_type, imported_types, imported_conses, type_heaps, var_heap)
				= convertSymbolType common_defs sd_type imported_types imported_conses type_heaps var_heap
		= (imported_types, imported_conses, var_heap <:= (sd_type_ptr, VI_ExpandedType sd_type), type_heaps)

convertIclModule :: !{# CommonDefs} !*{#{# CheckedTypeDef}} !ImportedConstructors !*VarHeap !*TypeHeaps
	-> (!*{#{# CheckedTypeDef}}, !ImportedConstructors, !*VarHeap, !*TypeHeaps)
convertIclModule common_defs imported_types imported_conses var_heap type_heaps
	# types_and_heaps = convertConstructorTypes common_defs.[cIclModIndex].com_cons_defs common_defs (imported_types, imported_conses, var_heap, type_heaps)
	= convertSelectorTypes common_defs.[cIclModIndex].com_selector_defs common_defs types_and_heaps

convertImportedTypeSpecifications :: !{# DclModule}  !{# {# FunType} } !{# CommonDefs} !ImportedConstructors !ImportedFunctions
	!*{# {#CheckedTypeDef}} !*TypeHeaps !*VarHeap -> (!*{#{#CheckedTypeDef}}, !*TypeHeaps, !*VarHeap)
convertImportedTypeSpecifications dcl_mods dcl_functions common_defs imported_conses imported_functions imported_types type_heaps var_heap
	# {dcl_common={com_type_defs},dcl_conversions} = dcl_mods.[cIclModIndex]
	= case dcl_conversions of
		Yes conversion_table
			# abstract_type_indexes = iFoldSt (determine_abstract_type com_type_defs) 0 (size com_type_defs) []
			| isEmpty abstract_type_indexes
				-> convert_imported_type_specs dcl_functions common_defs imported_conses imported_functions imported_types type_heaps var_heap
				# (icl_type_defs, imported_types) = imported_types![cIclModIndex]
				  type_defs = foldSt (insert_abstract_type conversion_table.[cTypeDefs]) abstract_type_indexes { icl_type_def \\ icl_type_def <-: icl_type_defs }
				  (imported_types, type_heaps, var_heap)
				  		= convert_imported_type_specs dcl_functions common_defs imported_conses imported_functions
							{ imported_types & [cIclModIndex] = type_defs } type_heaps var_heap
				-> ({ imported_types & [cIclModIndex] = icl_type_defs }, type_heaps, var_heap)
		No
			-> convert_imported_type_specs dcl_functions common_defs imported_conses imported_functions imported_types type_heaps var_heap
			  

where
	determine_abstract_type dcl_type_defs type_index abstract_type_indexes
		# {td_rhs} = dcl_type_defs.[type_index]
		= case td_rhs of
			AbstractType _
				-> [type_index : abstract_type_indexes]
			_
				-> abstract_type_indexes
					
	insert_abstract_type conversion_table type_index type_defs
		# icl_index = conversion_table.[type_index]
		  (type_def, type_defs) = type_defs![icl_index]
		= { type_defs & [icl_index] = { type_def & td_rhs = AbstractType cAllBitsClear }}

	convert_imported_type_specs dcl_functions common_defs imported_conses imported_functions imported_types type_heaps var_heap
		# (imported_types, imported_conses, type_heaps, var_heap)
				= foldSt (convert_imported_function dcl_functions common_defs) imported_functions (imported_types, imported_conses, type_heaps, var_heap)
		= convert_imported_constructors common_defs imported_conses imported_types type_heaps var_heap

	convert_imported_function dcl_functions common_defs {glob_object,glob_module} (imported_types, imported_conses, type_heaps, var_heap)
		# {ft_type_ptr,ft_type} = dcl_functions.[glob_module].[glob_object]
		  (ft_type, imported_types, imported_conses, type_heaps, var_heap)
				= convertSymbolType common_defs ft_type imported_types imported_conses type_heaps var_heap
		= (imported_types, imported_conses, type_heaps, var_heap <:= (ft_type_ptr, VI_ExpandedType ft_type))

	convert_imported_constructors common_defs [] imported_types type_heaps var_heap
		= (imported_types, type_heaps, var_heap)
	convert_imported_constructors common_defs [ {glob_module, glob_object} : conses ] imported_types type_heaps var_heap 
		# {com_cons_defs,com_selector_defs} = common_defs.[glob_module]
		  {cons_type_ptr,cons_type,cons_type_index,cons_symb} = common_defs.[glob_module].com_cons_defs.[glob_object]
		  (cons_type, imported_types, conses, type_heaps, var_heap) = convertSymbolType common_defs cons_type imported_types conses type_heaps var_heap
		  var_heap = var_heap <:= (cons_type_ptr, VI_ExpandedType cons_type)
		  ({td_rhs}, imported_types) = imported_types![glob_module].[cons_type_index]
//				---> ("convert_imported_constructors", cons_symb, cons_type)
		= case td_rhs of
			RecordType {rt_fields}
				# (imported_types, conses, type_heaps, var_heap)
						= iFoldSt (convert_type_of_imported_field glob_module com_selector_defs rt_fields) 0 (size rt_fields)
							(imported_types, conses, type_heaps, var_heap)
				-> convert_imported_constructors common_defs conses imported_types type_heaps var_heap
			_
				-> convert_imported_constructors common_defs conses imported_types type_heaps var_heap
		where
			convert_type_of_imported_field module_index selector_defs fields field_index (imported_types, conses, type_heaps, var_heap)
				# field_index = fields.[field_index].fs_index
				  {sd_type_ptr,sd_type} = selector_defs.[field_index]
				  (sd_type, imported_types, conses, type_heaps, var_heap) = convertSymbolType common_defs sd_type imported_types conses type_heaps var_heap
				= (imported_types, conses, type_heaps, var_heap <:= (sd_type_ptr, VI_ExpandedType sd_type))

convertRootExpression bound_vars group_index common_defs default_ptr (Let lad=:{let_strict_binds,let_lazy_binds,let_expr,let_info_ptr}) ci=:{ci_expr_heap}
	# (EI_LetType let_type, ci_expr_heap) = readPtr let_info_ptr ci_expr_heap
	  bound_vars = addLetVars (let_strict_binds ++ let_lazy_binds) let_type bound_vars
	  (let_strict_binds, ci)	= convertCases bound_vars group_index common_defs let_strict_binds { ci & ci_expr_heap = ci_expr_heap }
	  (let_lazy_binds, ci)		= convertCases bound_vars group_index common_defs let_lazy_binds ci
	  (let_expr, ci)			= convertRootExpression bound_vars group_index common_defs default_ptr let_expr ci
	= (Let { lad & let_strict_binds = let_strict_binds, let_lazy_binds = let_lazy_binds, let_expr = let_expr }, ci)
convertRootExpression bound_vars group_index common_defs default_ptr (Case kees=:{case_expr, case_guards, case_default, case_info_ptr}) ci
	= case case_guards of
		BasicPatterns BT_Bool patterns
			-> convert_boolean_case_into_guard bound_vars group_index common_defs default_ptr case_expr patterns case_default case_info_ptr ci
		_
			-> convertCasesInCaseExpression bound_vars group_index common_defs default_ptr kees ci

where
/*
	convert_boolean_case_into_guard bound_vars  group_index common_defs default_ptr guard [ alt : alts ] case_default case_info_ptr ci
		# (guard, ci) = convertRootExpression bound_vars group_index common_defs cHasNoDefault guard ci
		  (then_bool, then_expr, opt_else_expr) = check_reachability alt alts
		= case opt_else_expr of
			Yes else_expr
				# (then_expr, ci) = convertRootExpression bound_vars group_index common_defs cHasNoDefault then_expr ci
				  (else_expr, ci) = convertRootExpression bound_vars group_index common_defs cHasNoDefault else_expr ci
				-> (build_conditional then_bool guard then_expr else_expr, ci)
			No
				-> case case_default of
					Yes default_expr
						# (EI_CaseTypeAndRefCounts case_type ref_counts, ci_expr_heap) = readPtr case_info_ptr ci.ci_expr_heap
						  (default_ptr, ci_expr_heap) = makePtrToDefault case_default case_type.ct_result_type default_ptr ci_expr_heap
						  (then_expr, ci) = convertRootExpression bound_vars group_index common_defs default_ptr then_expr { ci & ci_expr_heap = ci_expr_heap }
						  (default_info, ci_expr_heap) = readPtr default_ptr ci.ci_expr_heap
						  (else_expr, ci) = convertDefaultToExpression default_ptr default_info bound_vars group_index common_defs
													{ ci & ci_expr_heap = ci_expr_heap }
						-> (build_conditional then_bool guard then_expr else_expr, ci)
					No
						# (then_expr, ci) = convertRootExpression bound_vars group_index common_defs default_ptr then_expr ci
						| isNilPtr default_ptr
							-> (Conditional { if_cond = convert_guard then_bool guard, if_then = then_expr, if_else = No }, ci)
							# (default_info, ci_expr_heap) = readPtr default_ptr ci.ci_expr_heap
							  (else_expr, ci) = convertDefaultToExpression default_ptr default_info bound_vars group_index common_defs
														{ ci & ci_expr_heap = ci_expr_heap }
							-> (build_conditional then_bool guard then_expr else_expr, ci)

	convert_guard guard_bool guard
		| guard_bool
			= guard
			= Conditional { if_cond = guard, if_then = BasicExpr (BVB False) BT_Bool, if_else = Yes (BasicExpr (BVB True) BT_Bool) }

	build_conditional then_bool guard then_expr else_expr
		| then_bool
			= Conditional { if_cond = guard, if_then = then_expr, if_else =  Yes else_expr }
			= Conditional { if_cond = guard, if_then = else_expr, if_else =  Yes then_expr }
		

	check_reachability {bp_value=BVB bool,bp_expr} alts
		= (bool, bp_expr, check_other_alternatives bool alts)
	where
		check_other_alternatives then_bool []
			= No
		check_other_alternatives then_bool [{bp_value=BVB else_bool,bp_expr} : alts ]
			| then_bool == else_bool
				= check_other_alternatives then_bool alts
				= Yes bp_expr
*/

//	convert_boolean_case_into_guard bound_vars  group_index common_defs default_ptr guard [ alt : alts ] case_default case_info_ptr ci
	convert_boolean_case_into_guard bound_vars  group_index common_defs has_default guard [ alt=:{bp_value=BVB sign_of_then_part,bp_expr} : alts ] case_default case_info_ptr ci
		# (guard, ci) = convertRootExpression bound_vars group_index common_defs cHasNoDefault guard ci
		# (EI_CaseTypeAndRefCounts case_type _, ci_expr_heap) = readPtr case_info_ptr ci.ci_expr_heap
		# (default_ptr, ci_expr_heap) = makePtrToDefault case_default case_type.ct_result_type has_default ci_expr_heap
		# (then_part, ci) = convertRootExpression bound_vars group_index common_defs default_ptr bp_expr {ci &ci_expr_heap=ci_expr_heap}
		# (opt_else_part, ci) = convert_to_else_part bound_vars group_index common_defs default_ptr sign_of_then_part alts case_default ci
//		= (Conditional { if_cond = { con_positive = sign_of_then_part, con_expression = guard }, if_then = then_part, if_else = opt_else_part }, ci)
		= (build_conditional sign_of_then_part guard then_part opt_else_part, ci)
	where
		build_conditional True guard then_expr opt_else_expr
			= Conditional { if_cond = guard, if_then = then_expr, if_else = opt_else_expr }
		build_conditional false guard then_expr (Yes else_expr)
			= Conditional { if_cond = guard, if_then = else_expr, if_else = Yes then_expr }
		build_conditional false guard then_expr No
			= Conditional { if_cond = Conditional { if_cond = guard, if_then = BasicExpr (BVB False) BT_Bool, if_else = Yes (BasicExpr (BVB True) BT_Bool) },
								if_then = then_expr, if_else = No }

		convert_to_else_part bound_vars group_index common_defs default_ptr sign_of_then_part [ alt=:{bp_value=BVB sign_of_else_part,bp_expr} : alts ] case_default ci
			# (else_part, ci) = convertRootExpression bound_vars group_index common_defs default_ptr bp_expr ci
			| sign_of_then_part == sign_of_else_part
				= convert_to_else_part bound_vars group_index common_defs default_ptr sign_of_then_part alts case_default ci
				= (Yes else_part, ci)
		convert_to_else_part bound_vars group_index common_defs default_ptr sign_of_then_part [ ] (Yes else_part) ci
			# (else_part, ci) = convertRootExpression bound_vars group_index common_defs has_default else_part ci
			= (Yes else_part, ci)
		convert_to_else_part bound_vars group_index common_defs default_ptr sign_of_then_part [ ] No ci
			= (No, ci)

convertRootExpression bound_vars group_index common_defs _ expr ci
	= convertCases bound_vars group_index common_defs expr ci


::	CopyInfo =
	{	cp_free_vars	:: ![(VarInfoPtr,AType)]
	,	cp_local_vars	:: ![FreeVar]
	,	cp_var_heap		:: !.VarHeap
	}
	
class copy e :: !e !*CopyInfo -> (!e, !*CopyInfo)

instance copy BoundVar
where
	copy var=:{var_name,var_info_ptr} cp_info=:{cp_var_heap}
		# (var_info, cp_var_heap) = readPtr var_info_ptr cp_var_heap
		  cp_info = { cp_info & cp_var_heap = cp_var_heap }
		= case var_info of
			VI_FreeVar name new_info_ptr count type
				-> ({ var & var_info_ptr = new_info_ptr },
					{ cp_info & cp_var_heap = cp_info.cp_var_heap <:= (var_info_ptr, VI_FreeVar name new_info_ptr (inc count) type)})
			VI_LocalVar
				-> (var, cp_info)
			VI_BoundVar type
				# (new_info_ptr, cp_var_heap) = newPtr VI_Empty cp_info.cp_var_heap
				-> ({ var & var_info_ptr = new_info_ptr },
					{ cp_info & cp_free_vars = [ (var_info_ptr, type) : cp_info.cp_free_vars ],
							cp_var_heap = cp_var_heap <:= (var_info_ptr, VI_FreeVar var_name new_info_ptr 1 type) })
			_
				-> abort "copy [BoundVar] (convertcases, 612)" <<- (var_info ---> (var_name, ptrToInt var_info_ptr))

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
		bind_let_var {bind_dst} (local_vars, var_heap)
			= ([bind_dst : local_vars], var_heap <:= (bind_dst.fv_info_ptr, VI_LocalVar))
	copy (Case case_expr) cp_info
		# (case_expr, cp_info) = copy case_expr cp_info
		= (Case case_expr, cp_info)
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
	copy (RecordUpdate cons_symbol expression expressions) cp_info
		# (expression, cp_info) = copy expression cp_info
		  (expressions, cp_info) = copy expressions cp_info
		= (RecordUpdate cons_symbol expression expressions, cp_info)
	copy (TupleSelect tuple_symbol arg_nr expr) cp_info
		# (expr, cp_info) = copy expr cp_info
		= (TupleSelect tuple_symbol arg_nr expr, cp_info)
/*
	copy (DynamicExpr dynamik) cp_info
		# (dynamik, cp_info) = copy dynamik cp_info
		= (DynamicExpr dynamik, cp_info)
*/
	copy EE cp_info
		= (EE, cp_info)
	copy (NoBind ptr) cp_info
		= (NoBind ptr, cp_info)
	copy expr cp_info
		= abort ("copy (Expression) does not match" ---> expr)

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

/*
instance copy DynamicExpr
where
	copy dynamik=:{dyn_expr,dyn_uni_vars,dyn_type_code} cp_info=:{cp_var_heap}
		# ((dyn_expr, dyn_type_code), cp_info) = copy (dyn_expr,dyn_type_code)
				{ cp_info & cp_var_heap = foldSt (\info_ptr -> writePtr info_ptr VI_LocalVar) dyn_uni_vars cp_var_heap }
		= ({ dynamik & dyn_expr = dyn_expr, dyn_type_code = dyn_type_code }, cp_info)

instance copy TypeCodeExpression
where
	copy (TCE_Var var_info_ptr) cp_info=:{cp_free_vars, cp_var_heap}
		# (new_info_ptr, cp_info) = copyVarInfo var_info_ptr cp_info
		= (TCE_Var new_info_ptr, cp_info)
	copy (TCE_Constructor index type_codes) cp_info
		# (type_codes, cp_info) = copy type_codes cp_info
		= (TCE_Constructor index type_codes, cp_info)
	copy (TCE_Selector selections var_info_ptr) cp_info
		# (new_info_ptr, cp_info) = copyVarInfo var_info_ptr cp_info
		= (TCE_Selector selections new_info_ptr, cp_info)

copyVarInfo var_info_ptr cp_info=:{cp_free_vars, cp_var_heap}
	#! var_info = sreadPtr var_info_ptr cp_var_heap
	= case var_info of
		VI_FreeVar name new_info_ptr count type
			-> (new_info_ptr, { cp_free_vars = cp_free_vars, cp_var_heap = cp_var_heap <:= (var_info_ptr, VI_FreeVar name new_info_ptr (inc count) type)})
		VI_LocalVar
			-> (var_info_ptr, {cp_free_vars = cp_free_vars, cp_var_heap = cp_var_heap})
		VI_BoundVar type
			# (new_info_ptr, cp_var_heap) = newPtr VI_Empty cp_var_heap
			-> (new_info_ptr, { cp_free_vars = [ (var_info_ptr, type) : cp_free_vars ],
						cp_var_heap = cp_var_heap <:= (var_info_ptr, VI_FreeVar { id_name = "_t", id_info = nilPtr } new_info_ptr 1 type) })

*/

instance copy Case
where
	copy this_case=:{case_expr, case_guards, case_default} cp_info
		# ((case_expr,(case_guards,case_default)), cp_info) = copy (case_expr,(case_guards,case_default)) cp_info
		= ({ this_case & case_expr = case_expr, case_guards = case_guards, case_default = case_default}, cp_info) 

instance copy CasePatterns
where
	copy (AlgebraicPatterns type patterns) cp_info
		# (patterns, cp_info) = copy patterns cp_info
		= (AlgebraicPatterns type patterns, cp_info) 
	copy (BasicPatterns type patterns) cp_info
		# (patterns, cp_info) = copy patterns cp_info
		= (BasicPatterns type patterns, cp_info) 
/*
	copy (DynamicPatterns patterns) cp_info
		# (patterns, cp_info) = copy patterns cp_info
		= (DynamicPatterns patterns, cp_info) 
*/

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
/*
instance copy DynamicPattern
where
	copy pattern=:{dp_var={fv_info_ptr},dp_rhs,dp_type_patterns_vars, dp_type_code} cp_info=:{cp_var_heap}
		# (dp_rhs, cp_info) = copy dp_rhs
				{ cp_info & cp_var_heap = foldSt (\info_ptr -> writePtr info_ptr VI_LocalVar) dp_type_patterns_vars cp_var_heap
				 			<:= (fv_info_ptr, VI_LocalVar) }
		  (dp_type_code, cp_info) = copy dp_type_code cp_info
		= ({ pattern & dp_rhs = dp_rhs, dp_type_code = dp_type_code }, cp_info) 
*/
instance copy [a] | copy a
where
	copy l cp_info = mapSt copy l cp_info 
		
instance copy (a,b) | copy a & copy b
where
	copy t cp_info = app2St (copy, copy) t cp_info 

instance copy (Bind a b) | copy a
where
	copy bind=:{bind_src} cp_info
		# (bind_src, cp_info) = copy bind_src cp_info
		= ({ bind & bind_src = bind_src }, cp_info) 

/*

	weightedRefCount determines the reference counts of variables in an expression. Runtime behaviour of constructs is taken into account: 
	multiple occurrences of variables in different alternatives of the same case clause are counted only once. The outcome
	is used to distribute shared expressions (via let declarations) over cases. In this way code sharing is eliminated.
	As a side effect, weightedRefCount returns a list of all imported functions that have been used inside the expression.
	
*/

::	RCInfo =
	{	rc_free_vars	:: ![VarInfoPtr]
	,	rc_imports		:: ![SymbKind]
	,	rc_var_heap		:: !.VarHeap
	,	rc_expr_heap	:: !.ExpressionHeap
	}
	

weightedRefCountOfVariable depth var_info_ptr lvi=:{lvi_count,lvi_var,lvi_depth,lvi_previous,lvi_new} ref_count new_vars
	| lvi_depth < depth 
		= (True, {lvi & lvi_count = ref_count, lvi_depth = depth, lvi_new = True, lvi_previous =
				[{plvi_count = lvi_count, plvi_depth = lvi_depth, plvi_new = lvi_new } : lvi_previous]}, [var_info_ptr : new_vars])
//					==> (lvi_var, " PUSHED ",lvi_depth)
	| lvi_count == 0
		= (True, { lvi & lvi_count = ref_count }, [var_info_ptr : new_vars])
		= (lvi_new, { lvi & lvi_count = lvi_count + ref_count }, new_vars)

class weightedRefCount e :: !{# {# FunType} } !{# CommonDefs} !Int !e !*RCInfo -> *RCInfo

instance weightedRefCount BoundVar
where
	weightedRefCount dcl_functions common_defs depth {var_name,var_info_ptr} rc_info=:{rc_var_heap,rc_free_vars}
		#! var_info = sreadPtr var_info_ptr rc_var_heap
		= case var_info of
			VI_LetVar lvi
				# (is_new, lvi=:{lvi_expression}, rc_free_vars) = weightedRefCountOfVariable depth var_info_ptr lvi 1 rc_free_vars
				| is_new
					# rc_info = weightedRefCount dcl_functions common_defs depth lvi_expression
							{ rc_info & rc_free_vars = rc_free_vars,
							  rc_var_heap = rc_info.rc_var_heap  <:= (var_info_ptr, VI_LetVar {lvi & lvi_expression = EE, lvi_new = False})}
					  (VI_LetVar lvi, rc_var_heap) = readPtr var_info_ptr rc_info.rc_var_heap
					-> { rc_info & rc_var_heap = rc_var_heap <:= (var_info_ptr, VI_LetVar { lvi & lvi_expression = lvi_expression }) }
//							 ==> (var_name, var_info_ptr, depth, lvi.lvi_count)
					-> { rc_info & rc_var_heap = rc_info.rc_var_heap <:= (var_info_ptr, VI_LetVar lvi) }
			_
				-> rc_info
				
instance weightedRefCount Expression
where
	weightedRefCount dcl_functions common_defs depth (Var var) rc_info
		= weightedRefCount dcl_functions common_defs depth var rc_info
	weightedRefCount dcl_functions common_defs depth (App app) rc_info
		= weightedRefCount dcl_functions common_defs depth app rc_info
	weightedRefCount dcl_functions common_defs depth (fun_expr @ exprs) rc_info
		= weightedRefCount dcl_functions common_defs depth (fun_expr, exprs) rc_info
	weightedRefCount dcl_functions common_defs depth (Let {let_strict_binds,let_lazy_binds,let_expr, let_info_ptr}) rc_info=:{rc_var_heap}
		# rc_info = weightedRefCount dcl_functions common_defs depth let_strict_binds { rc_info & rc_var_heap = foldSt store_binding let_lazy_binds rc_var_heap }
		  rc_info = weightedRefCount dcl_functions common_defs depth let_expr rc_info
		  (let_info, rc_expr_heap) = readPtr let_info_ptr rc_info.rc_expr_heap
		  rc_info = { rc_info & rc_expr_heap = rc_expr_heap }
		= case let_info of
			EI_LetType let_type
		  		# (ref_counts, rc_var_heap) = mapSt get_ref_count let_lazy_binds rc_info.rc_var_heap
				  (rc_free_vars, rc_var_heap) = foldl remove_variable (rc_info.rc_free_vars, rc_var_heap) let_lazy_binds
				-> { rc_info & rc_free_vars = rc_free_vars, rc_var_heap = rc_var_heap,
						rc_expr_heap = rc_info.rc_expr_heap <:= (let_info_ptr, EI_LetTypeAndRefCounts let_type ref_counts)}
//							---> ("weightedRefCount (EI_LetType)", ptrToInt let_info_ptr, [ x.bind_dst \\ x <- let_lazy_binds])
			_
				# (rc_free_vars, rc_var_heap) = foldl remove_variable (rc_info.rc_free_vars, rc_info.rc_var_heap) let_lazy_binds
				-> { rc_info & rc_free_vars = rc_free_vars, rc_var_heap = rc_var_heap }
//							---> ("weightedRefCount (_)", ptrToInt let_info_ptr, [ x.bind_dst \\ x <- let_lazy_binds])
	where
		remove_variable ([], var_heap) let_bind
			= ([], var_heap)
		remove_variable ([var_ptr : var_ptrs], var_heap) bind=:{bind_dst={fv_name,fv_info_ptr}}
			| fv_info_ptr == var_ptr
				# (VI_LetVar {lvi_count,lvi_depth}, var_heap) = readPtr fv_info_ptr var_heap
				= (var_ptrs, var_heap) 
//						==> ("remove_variable (lvi_count,lvi_dpeth) ", fv_name, lvi_count, lvi_depth)
				# (var_ptrs, var_heap) = remove_variable (var_ptrs, var_heap) bind
				= ([var_ptr : var_ptrs], var_heap)

		store_binding {bind_dst={fv_name,fv_info_ptr},bind_src} var_heap
			= var_heap <:= (fv_info_ptr, VI_LetVar {lvi_count = 0, lvi_depth = depth, lvi_previous = [],
													lvi_new = True, lvi_expression = bind_src, lvi_var = fv_name})

		get_ref_count {bind_dst={fv_name,fv_info_ptr}} var_heap 
			# (VI_LetVar {lvi_count}, var_heap) = readPtr fv_info_ptr var_heap
		  	= (lvi_count, var_heap)
//				==> (fv_name,fv_info_ptr,lvi_count)
	weightedRefCount dcl_functions common_defs depth (Case case_expr) rc_info=:{rc_expr_heap}
		# (case_info, rc_expr_heap) = readPtr case_expr.case_info_ptr rc_expr_heap
		= weightedRefCountOfCase dcl_functions common_defs depth case_expr case_info { rc_info & rc_expr_heap = rc_expr_heap }
	weightedRefCount dcl_functions common_defs depth expr=:(BasicExpr _ _) rc_info
		= rc_info
	weightedRefCount dcl_functions common_defs depth (MatchExpr _ constructor expr) rc_info
		= weightedRefCount dcl_functions common_defs depth expr rc_info
	weightedRefCount dcl_functions common_defs depth (Selection opt_tuple expr selections) rc_info
		= weightedRefCount dcl_functions common_defs depth (expr, selections) rc_info
	weightedRefCount dcl_functions common_defs depth (Update expr1 selections expr2) rc_info
		= weightedRefCount dcl_functions common_defs depth (expr1, (selections, expr2)) rc_info
	weightedRefCount dcl_functions common_defs depth (RecordUpdate cons_symbol expression expressions) rc_info
		= weightedRefCount dcl_functions common_defs depth (expression, expressions) rc_info
	weightedRefCount dcl_functions common_defs depth (TupleSelect tuple_symbol arg_nr expr) rc_info
		= weightedRefCount dcl_functions common_defs depth expr rc_info
/*
	weightedRefCount dcl_functions common_defs depth (DynamicExpr {dyn_expr}) rc_info
		= weightedRefCount dcl_functions common_defs depth dyn_expr rc_info
*/
	weightedRefCount dcl_functions common_defs depth (AnyCodeExpr _ _ _) rc_info
		= rc_info
	weightedRefCount dcl_functions common_defs depth (ABCCodeExpr _ _) rc_info
		= rc_info
	weightedRefCount dcl_functions common_defs depth (TypeCodeExpression type_code_expr) rc_info
		= weightedRefCount dcl_functions common_defs depth type_code_expr rc_info
	weightedRefCount dcl_functions common_defs depth EE rc_info
		= rc_info
	weightedRefCount dcl_functions common_defs depth (NoBind ptr) rc_info
		= rc_info
	weightedRefCount dcl_functions common_defs depth expr rc_info
		= abort ("weightedRefCount [Expression] (convertcases, 864))" ---> expr)

addPatternVariable depth {cv_variable = var_info_ptr, cv_count = ref_count} (free_vars, var_heap)
 	#! var_info = sreadPtr var_info_ptr var_heap
	= case var_info of
		VI_LetVar lvi
			# (_, lvi, free_vars) = weightedRefCountOfVariable depth var_info_ptr lvi ref_count free_vars
			-> (free_vars, var_heap <:= (var_info_ptr, VI_LetVar lvi))
		_
			-> (free_vars, var_heap)

weightedRefCountOfCase dcl_functions common_defs depth this_case=:{case_expr, case_guards, case_default, case_info_ptr} (EI_CaseType case_type)
			rc_info=:{ rc_var_heap, rc_expr_heap, rc_imports }
	# (local_vars, vars_and_heaps) = weighted_ref_count_in_case_patterns dcl_functions common_defs (inc depth) case_guards rc_imports rc_var_heap rc_expr_heap
	  (default_vars, (all_vars, rc_imports, var_heap, expr_heap)) = weighted_ref_count_in_default dcl_functions common_defs (inc depth) case_default vars_and_heaps
	  rc_info = weightedRefCount dcl_functions common_defs depth case_expr { rc_info & rc_var_heap = var_heap, rc_expr_heap = expr_heap, rc_imports = rc_imports }
	  (rc_free_vars, rc_var_heap) = foldSt (addPatternVariable depth) all_vars (rc_info.rc_free_vars, rc_info.rc_var_heap)
	  rc_expr_heap = rc_info.rc_expr_heap <:= (case_info_ptr, EI_CaseTypeAndRefCounts case_type 
	  		{ rcc_all_variables = all_vars, rcc_default_variables = default_vars, rcc_pattern_variables = local_vars })
	= { rc_info & rc_var_heap = rc_var_heap, rc_expr_heap = rc_expr_heap, rc_free_vars = rc_free_vars   }
//			---> ("weightedRefCountOfCase", ptrToInt case_info_ptr, case_expr)
	where
		weighted_ref_count_in_default dcl_functions common_defs depth (Yes expr) info
			= weightedRefCountInPatternExpr dcl_functions common_defs depth expr info
		weighted_ref_count_in_default dcl_functions common_defs depth No info
			= ([], info)
						
		weighted_ref_count_in_case_patterns dcl_functions common_defs depth (AlgebraicPatterns type patterns) collected_imports var_heap expr_heap
			= mapSt (weighted_ref_count_in_algebraic_pattern dcl_functions common_defs depth) patterns ([], collected_imports, var_heap, expr_heap)
		where
			weighted_ref_count_in_algebraic_pattern dcl_functions common_defs depth {ap_expr,ap_symbol={glob_module, glob_object={ds_index}}} wrc_state
				# (free_vars_with_rc, (all_free_vars, collected_imports, var_heap, expr_heap))
						= weightedRefCountInPatternExpr dcl_functions common_defs depth ap_expr wrc_state
				| glob_module <> cIclModIndex
					# {cons_type_ptr} = common_defs.[glob_module].com_cons_defs.[ds_index]
					  (collected_imports, var_heap) = checkImportedSymbol (SK_Constructor {glob_module = glob_module, glob_object = ds_index})
							cons_type_ptr (collected_imports, var_heap)
					= (free_vars_with_rc, (all_free_vars, collected_imports, var_heap, expr_heap))
					= (free_vars_with_rc, (all_free_vars, collected_imports, var_heap, expr_heap))

		weighted_ref_count_in_case_patterns dcl_functions common_defs depth (BasicPatterns type patterns) collected_imports var_heap expr_heap
			= mapSt (\{bp_expr} -> weightedRefCountInPatternExpr dcl_functions common_defs depth bp_expr) patterns ([], collected_imports, var_heap, expr_heap)
		weighted_ref_count_in_case_patterns dcl_functions common_defs depth (DynamicPatterns patterns) collected_imports var_heap expr_heap
			= mapSt (\{dp_rhs} -> weightedRefCountInPatternExpr dcl_functions common_defs depth dp_rhs) patterns ([], collected_imports, var_heap, expr_heap)

weightedRefCountOfCase dcl_functions common_defs depth this_case=:{case_expr, case_guards, case_default, case_info_ptr} (EI_CaseTypeAndRefCounts case_type {rcc_all_variables})
			rc_info=:{ rc_var_heap, rc_expr_heap, rc_imports }
	# rc_info = weightedRefCount dcl_functions common_defs depth case_expr rc_info
	  (rc_free_vars, rc_var_heap) = foldSt (addPatternVariable depth) rcc_all_variables (rc_info.rc_free_vars, rc_info.rc_var_heap)
	= { rc_info & rc_var_heap = rc_var_heap, rc_free_vars = rc_free_vars }	
//			---> ("weightedRefCountOfCase 2", ptrToInt case_info_ptr, case_expr)

checkRecordSelector common_defs {glob_module, glob_object={ds_index}} rc_info=:{rc_imports,rc_var_heap}
	| glob_module <> cIclModIndex
		# {com_selector_defs,com_cons_defs,com_type_defs} = common_defs.[glob_module]
		  {sd_type_index} = com_selector_defs.[ds_index]
		  {td_rhs = RecordType {rt_constructor={ds_index=cons_index}, rt_fields}} = com_type_defs.[sd_type_index]
		  {cons_type_ptr} = com_cons_defs.[cons_index]
		  (rc_imports, rc_var_heap) = checkImportedSymbol (SK_Constructor {glob_module = glob_module, glob_object = cons_index})
											cons_type_ptr (rc_imports, rc_var_heap)
		= { rc_info & rc_imports = rc_imports, rc_var_heap = rc_var_heap }
		= rc_info
	
instance weightedRefCount Selection
where
	weightedRefCount dcl_functions common_defs depth (ArraySelection {glob_module,glob_object={ds_index}} _ index_expr) rc_info
		# rc_info = weightedRefCount dcl_functions common_defs depth index_expr rc_info
		= checkImportOfDclFunction dcl_functions common_defs glob_module ds_index rc_info
	weightedRefCount dcl_functions common_defs depth (DictionarySelection _ selectors _ index_expr) rc_info
		# rc_info = weightedRefCount dcl_functions common_defs depth index_expr rc_info
		= weightedRefCount dcl_functions common_defs depth selectors rc_info
	weightedRefCount dcl_functions common_defs depth (RecordSelection selector _) rc_info
		= checkRecordSelector common_defs selector rc_info

weightedRefCountInPatternExpr dcl_functions common_defs depth pattern_expr (previous_free_vars, collected_imports, var_heap, expr_heap)
	# {rc_free_vars,rc_var_heap,rc_imports,rc_expr_heap} = weightedRefCount dcl_functions common_defs depth pattern_expr
				{ rc_var_heap = var_heap, rc_expr_heap = expr_heap, rc_free_vars = [], rc_imports = collected_imports}
	  (free_vars_with_rc, rc_var_heap) = mapSt get_ref_count rc_free_vars rc_var_heap
	  (previous_free_vars, rc_var_heap) = foldSt (select_unused_free_variable depth) previous_free_vars ([], rc_var_heap)
	  (all_free_vars, rc_var_heap) = foldSt (collect_free_variable depth) rc_free_vars (previous_free_vars, rc_var_heap)
//			==> ("remove_vars ", depth, free_vars_with_rc)
	= (free_vars_with_rc, (all_free_vars, rc_imports, rc_var_heap, rc_expr_heap))
where
	select_unused_free_variable depth var=:{cv_variable = var_ptr, cv_count = var_count} (collected_vars, var_heap)
		# (VI_LetVar info=:{lvi_count,lvi_depth}, var_heap) = readPtr var_ptr var_heap
		| lvi_depth == depth && lvi_count > 0
			= (collected_vars, var_heap <:= (var_ptr, VI_LetVar {info & lvi_count = max lvi_count var_count}))
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

checkImportOfDclFunction dcl_functions common_defs mod_index fun_index rc_info=:{rc_imports, rc_var_heap}
	| mod_index <> cIclModIndex
		# {ft_type_ptr} = dcl_functions.[mod_index].[fun_index]
		  (rc_imports, rc_var_heap) = checkImportedSymbol (SK_Function {glob_module=mod_index,glob_object=fun_index}) ft_type_ptr (rc_imports, rc_var_heap)
		= { rc_info & rc_imports = rc_imports, rc_var_heap = rc_var_heap }
		= rc_info

instance weightedRefCount App
where
	weightedRefCount dcl_functions common_defs depth {app_symb,app_args} rc_info
		# rc_info = weightedRefCount dcl_functions common_defs depth app_args rc_info
		= check_import dcl_functions common_defs app_symb rc_info
	where
		check_import dcl_functions common_defs {symb_kind=SK_Function {glob_module,glob_object}} rc_info=:{rc_imports, rc_var_heap}
			= checkImportOfDclFunction dcl_functions common_defs glob_module glob_object rc_info
		check_import dcl_functions common_defs {symb_name,symb_kind=symb_kind=:(SK_Constructor {glob_module,glob_object})} rc_info=:{rc_imports, rc_var_heap}
			| glob_module <> cIclModIndex
				# {cons_type_ptr} = common_defs.[glob_module].com_cons_defs.[glob_object]
				  (rc_imports, rc_var_heap) = checkImportedSymbol symb_kind cons_type_ptr (rc_imports, rc_var_heap)
				= { rc_info & rc_imports = rc_imports, rc_var_heap = rc_var_heap }
				= rc_info
		check_import dcl_functions common_defs _ rc_info
			= rc_info


instance weightedRefCount TypeCodeExpression
where
	weightedRefCount dcl_functions common_defs depth type_code_expr rc_info
		= rc_info

instance weightedRefCount [a] | weightedRefCount a
where
	weightedRefCount dcl_functions common_defs depth l rc_info = foldr (weightedRefCount dcl_functions common_defs depth) rc_info l 
		
instance weightedRefCount (a,b) | weightedRefCount a & weightedRefCount b
where
	weightedRefCount dcl_functions common_defs depth (x,y) rc_info = weightedRefCount dcl_functions common_defs depth y (weightedRefCount dcl_functions common_defs depth x rc_info) 

instance weightedRefCount (Bind a b) | weightedRefCount a
where
	weightedRefCount dcl_functions common_defs depth bind=:{bind_src} rc_info
		= weightedRefCount dcl_functions common_defs depth bind_src rc_info

checkImportedSymbol symb_kind symb_type_ptr (collected_imports, var_heap)
	#! type_info = sreadPtr symb_type_ptr var_heap
	= case type_info of
		VI_Used
			-> (collected_imports, var_heap)
		_
			-> ([symb_kind : collected_imports ], var_heap <:= (symb_type_ptr, VI_Used))

::	DistributeInfo =
	{	di_lets			:: ![VarInfoPtr]
	,	di_var_heap		:: !.VarHeap
	,	di_expr_heap	:: !.ExpressionHeap
	}
/*
	distributeLets tries to move shared expressions as close as possible to the location at which they are used.
	Case-expressions may require unsharing if the shared expression is used in different alternatives. Of course
	only if the expression is neither used in the pattern nor in a surrounding expression.
*/

class distributeLets e :: !Int !e !*DistributeInfo -> (!e, !*DistributeInfo)


instance distributeLets Expression
where
	distributeLets depth (Var var=:{var_name,var_info_ptr}) dl_info=:{di_var_heap}
		#! var_info = sreadPtr var_info_ptr di_var_heap
		= case var_info of
			VI_LetExpression lei
				| lei.lei_count == 1
//						 ==> (var_name, var_info_ptr, lei.lei_count, (lei.lei_expression, lei.lei_depth, depth))
					# (lei_updated_expr, dl_info) = distributeLets depth lei.lei_expression dl_info
					-> (lei_updated_expr, { dl_info &  di_var_heap = dl_info.di_var_heap <:=
							(var_info_ptr, VI_LetExpression { lei & lei_status = LES_Updated lei_updated_expr }) })
				| lei.lei_depth == depth
					# dl_info = distributeLetsInLetExpression depth var_info_ptr lei dl_info
					-> (Var { var & var_info_ptr = lei.lei_var.fv_info_ptr }, dl_info)
					-> (Var { var & var_info_ptr = lei.lei_var.fv_info_ptr }, dl_info)
			VI_CaseVar var_info_ptr
				-> (Var { var & var_info_ptr = var_info_ptr }, dl_info)
			_
				-> (Var var, dl_info)
	distributeLets depth (Case kees) dl_info
		# (kees, dl_info) = distributeLets depth kees dl_info
		= (Case kees, dl_info)
	distributeLets depth (App app=:{app_args}) dl_info
		# (app_args, dl_info) = distributeLets depth app_args dl_info
		= (App {app & app_args = app_args}, dl_info)
	distributeLets depth (fun_expr @ exprs) dl_info
		# (fun_expr, dl_info) = distributeLets depth fun_expr dl_info
		  (exprs, dl_info) = distributeLets depth exprs dl_info
		= (fun_expr @ exprs, dl_info)
	distributeLets depth expr=:(BasicExpr _ _) dl_info
		= (expr, dl_info)
	distributeLets depth (MatchExpr opt_tuple constructor expr) dl_info
		# (expr, dl_info) = distributeLets depth expr dl_info
		= (MatchExpr opt_tuple constructor expr, dl_info)
	distributeLets depth (Selection opt_tuple expr selectors) dl_info
		# (expr, dl_info) = distributeLets depth expr dl_info
		# (selectors, dl_info) = distributeLets depth selectors dl_info
		= (Selection opt_tuple expr selectors, dl_info)
	distributeLets depth (Update expr1 selectors expr2) dl_info
		# (expr1, dl_info) = distributeLets depth expr1 dl_info
		# (selectors, dl_info) = distributeLets depth selectors dl_info
		# (expr2, dl_info) = distributeLets depth expr2 dl_info
		= (Update expr1 selectors expr2, dl_info)
	distributeLets depth (RecordUpdate cons_symbol expression expressions) dl_info
		# (expression, dl_info) = distributeLets depth expression dl_info
		# (expressions, dl_info) = distributeLets depth expressions dl_info
		= (RecordUpdate cons_symbol expression expressions, dl_info)
	distributeLets depth (TupleSelect tuple_symbol arg_nr expr) dl_info
		# (expr, dl_info) = distributeLets depth expr dl_info
		= (TupleSelect tuple_symbol arg_nr expr, dl_info)
	distributeLets depth (Let lad=:{let_strict_binds,let_lazy_binds,let_expr,let_info_ptr}) dl_info=:{di_expr_heap,di_var_heap}
		# (let_info, di_expr_heap) = readPtr let_info_ptr di_expr_heap
		# (EI_LetTypeAndRefCounts let_type ref_counts) = let_info
		  nr_of_strict_lets = length let_strict_binds
		  let_binds = [(False, bind) \\ bind <- let_lazy_binds]
		  di_var_heap = set_let_expression_info depth let_binds ref_counts (drop nr_of_strict_lets let_type) di_var_heap
		  (let_expr, dl_info) = distributeLets depth let_expr { dl_info & di_var_heap = di_var_heap, di_expr_heap = di_expr_heap }
		  (let_strict_binds, dl_info) = distributeLets depth let_strict_binds dl_info
		  dl_info = foldSt (distribute_lets_in_non_distributed_let depth) let_lazy_binds dl_info
		| nr_of_strict_lets == 0
		    = (let_expr, dl_info)
		    = case let_expr of
		    	Let inner_let=:{let_info_ptr=inner_let_info_ptr}
		    		# (EI_LetType strict_inner_types, di_expr_heap) = readPtr inner_let_info_ptr dl_info.di_expr_heap
		    		  di_expr_heap = writePtr inner_let_info_ptr (EI_LetType ((take nr_of_strict_lets let_type)++strict_inner_types)) di_expr_heap
					-> (Let { inner_let & let_strict_binds = let_strict_binds++inner_let.let_strict_binds}, 
						{dl_info & di_expr_heap = di_expr_heap})
				_	-> (Let { lad & let_strict_binds = let_strict_binds, let_expr = let_expr, let_lazy_binds = []}, 
						{dl_info & di_expr_heap = dl_info.di_expr_heap <:= (let_info_ptr, EI_LetType (take nr_of_strict_lets let_type))})
	where
		set_let_expression_info depth [(let_strict, {bind_src,bind_dst}):binds][ref_count:ref_counts][type:types] var_heap
			# (new_info_ptr, var_heap) = newPtr VI_Empty var_heap
			  lei = { lei_count = ref_count, lei_depth = depth, lei_var = { bind_dst & fv_info_ptr = new_info_ptr },
			  			lei_expression = bind_src, lei_type = type, lei_status = LES_Untouched }
			= set_let_expression_info depth binds ref_counts types (var_heap <:= (bind_dst.fv_info_ptr, VI_LetExpression lei))
		set_let_expression_info depth [] _ _ var_heap
			= var_heap
		
		distribute_lets_in_non_distributed_let depth {bind_dst={fv_name,fv_info_ptr}} dl_info=:{di_var_heap}
			# (VI_LetExpression lei=:{lei_depth,lei_count,lei_status}, di_var_heap) = readPtr fv_info_ptr di_var_heap
			| lei_count > 0
//			| not lei_moved && lei_count > 0
				= distributeLetsInLetExpression depth fv_info_ptr lei { dl_info & di_var_heap = di_var_heap }
				= { dl_info & di_var_heap = di_var_heap }
					==> ("distribute_lets_in_non_distributed_let (moved or not used)", lei_count, fv_name)

		is_moved LES_Moved	= True
		is_moved _ 			= False

/*	distributeLets depth (DynamicExpr dynamik=:{dyn_expr}) dl_info
		# (dyn_expr, dl_info) = distributeLets depth dyn_expr dl_info
		= (DynamicExpr { dynamik & dyn_expr = dyn_expr }, dl_info)
*/
	distributeLets depth expr=:(TypeCodeExpression _) dl_info
		= (expr, dl_info)
	distributeLets depth (AnyCodeExpr in_params out_params code_expr) dl_info=:{di_var_heap}
		# (in_params, di_var_heap) = mapSt determineInputParameter in_params di_var_heap
		= (AnyCodeExpr in_params out_params code_expr, { dl_info & di_var_heap = di_var_heap })
		where
			determineInputParameter bind=:{bind_dst} var_heap
				# (var_info, var_heap) = readPtr bind_dst.var_info_ptr var_heap
				= case var_info of
					VI_CaseVar new_info_ptr
						-> ({ bind & bind_dst = { bind_dst & var_info_ptr = new_info_ptr }}, var_heap)
					_
						-> (bind, var_heap)

	distributeLets depth expr=:(ABCCodeExpr _ _) dl_info
		= (expr, dl_info)
	distributeLets depth EE dl_info
		= (EE, dl_info)
	distributeLets depth (NoBind ptr) dl_info
		= (NoBind ptr, dl_info)
	
my_zip [] [] = []
my_zip [x:xs][y:ys] = [(x,y) : my_zip xs ys]

instance distributeLets Case
where 
	distributeLets depth kees=:{case_info_ptr,case_guards,case_default,case_expr} dl_info=:{di_var_heap, di_expr_heap}
		# (EI_CaseTypeAndRefCounts case_type { rcc_all_variables = tot_ref_counts , rcc_default_variables = ref_counts_in_default, rcc_pattern_variables = ref_counts_in_patterns }, di_expr_heap) = readPtr case_info_ptr di_expr_heap
//		  di_expr_heap = di_expr_heap <:= (case_info_ptr, EI_CaseType case_type)
		  new_depth = inc depth
		  (local_lets, di_var_heap) = foldSt (mark_local_let_var new_depth) tot_ref_counts ([], di_var_heap)
		  (case_guards, heaps) = distribute_lets_in_patterns new_depth ref_counts_in_patterns case_guards (di_var_heap, di_expr_heap)
		  (case_default, (di_var_heap, di_expr_heap)) = distribute_lets_in_default new_depth ref_counts_in_default case_default heaps
		  di_var_heap = foldSt reset_local_let_var local_lets di_var_heap
		  (case_expr, dl_info) = distributeLets depth case_expr { dl_info & di_var_heap = di_var_heap, di_expr_heap = di_expr_heap }
		= ({ kees & case_guards = case_guards, case_expr = case_expr, case_default = case_default }, dl_info)
	where
		distribute_lets_in_patterns depth ref_counts (AlgebraicPatterns conses patterns) heaps
			# (patterns, heaps) = mapSt (distribute_lets_in_alg_pattern depth) (my_zip ref_counts patterns) heaps
			= (AlgebraicPatterns conses patterns, heaps)
		where
			distribute_lets_in_alg_pattern depth (ref_counts,pattern) (di_var_heap, di_expr_heap)
				# (ap_vars, di_var_heap) = mapSt refresh_variable pattern.ap_vars di_var_heap
				  (ap_expr, heaps) = distribute_lets_in_pattern_expr depth ref_counts pattern.ap_expr (di_var_heap, di_expr_heap)
				= ({ pattern & ap_vars = ap_vars, ap_expr = ap_expr }, heaps) 
		distribute_lets_in_patterns depth ref_counts (BasicPatterns type patterns) heaps
			# (patterns, heaps) = mapSt (distribute_lets_in_basic_pattern depth) (zip2 ref_counts patterns) heaps
			= (BasicPatterns type patterns, heaps)
		where
			distribute_lets_in_basic_pattern depth (ref_counts,pattern) heaps
				# (bp_expr, heaps) = distribute_lets_in_pattern_expr depth ref_counts pattern.bp_expr heaps
				= ({ pattern & bp_expr = bp_expr }, heaps) 
		distribute_lets_in_patterns depth ref_counts (DynamicPatterns patterns) heaps
			# (patterns, heaps) = mapSt (distribute_lets_in_dynamic_pattern depth) (zip2 ref_counts patterns) heaps
			= (DynamicPatterns patterns, heaps)
		where
			distribute_lets_in_dynamic_pattern depth (ref_counts,pattern) (di_var_heap, di_expr_heap)
				# (dp_var, di_var_heap) = refresh_variable pattern.dp_var di_var_heap
				  (dp_rhs, heaps) = distribute_lets_in_pattern_expr depth ref_counts pattern.dp_rhs (di_var_heap, di_expr_heap)
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
				= (local_vars, var_heap)

		reset_local_let_var (var_info_ptr, lei_count, lei_depth)  var_heap
			# (VI_LetExpression lei, var_heap) = readPtr var_info_ptr var_heap
			= var_heap <:= (var_info_ptr, VI_LetExpression { lei & lei_depth = lei_depth, lei_count = lei_count, lei_status = LES_Moved })

		distribute_lets_in_pattern_expr depth local_vars pattern_expr (var_heap, expr_heap)
			# var_heap = foldSt (mark_local_let_var_of_pattern_expr depth) local_vars var_heap
			  (pattern_expr, dl_info) = distributeLets depth pattern_expr { di_lets = [], di_var_heap = var_heap, di_expr_heap = expr_heap}
			  dl_info = foldSt (reexamine_local_let_expressions depth) local_vars dl_info
			= buildLetExpr dl_info.di_lets pattern_expr (dl_info.di_var_heap, dl_info.di_expr_heap)
				==> ("distribute_lets_in_pattern_expr", dl_info.di_lets)
	
		mark_local_let_var_of_pattern_expr depth {cv_variable, cv_count} var_heap
			# (VI_LetExpression lei, var_heap) = readPtr cv_variable var_heap
			| depth == lei.lei_depth
				= (var_heap <:= (cv_variable, VI_LetExpression { lei & lei_count = cv_count, lei_status = LES_Untouched }))
						==> ("mark_local_let_var_of_pattern_expr ", lei.lei_var.fv_name, cv_variable, (lei.lei_var.fv_info_ptr, cv_count, depth))
				= var_heap

		reexamine_local_let_expressions depth {cv_variable, cv_count} dl_info=:{di_var_heap}
			| cv_count > 1
				# (VI_LetExpression lei, di_var_heap) = readPtr cv_variable di_var_heap
				| depth == lei.lei_depth
					= distributeLetsInLetExpression depth cv_variable lei { dl_info & di_var_heap = di_var_heap }
					= { dl_info & di_var_heap = di_var_heap }
				= dl_info


distributeLetsInLetExpression depth let_var_info_ptr lei=:{lei_expression, lei_status = LES_Moved} dl_info
	= dl_info
distributeLetsInLetExpression depth let_var_info_ptr lei=:{lei_expression, lei_status = LES_Updated _} dl_info
	= dl_info
distributeLetsInLetExpression depth let_var_info_ptr lei=:{lei_expression, lei_status = LES_Untouched} dl_info=:{di_var_heap}
	# di_var_heap = di_var_heap <:= (let_var_info_ptr, VI_LetExpression { lei & lei_status = LES_Updated EE}) /* to prevent doing this expression twice */
      (lei_expression, dl_info) = distributeLets depth lei_expression { dl_info & di_var_heap = di_var_heap }
	= { dl_info & di_lets = [ let_var_info_ptr : dl_info.di_lets ],
		 di_var_heap = dl_info.di_var_heap <:= (let_var_info_ptr, VI_LetExpression { lei & lei_status = LES_Updated lei_expression })}

	
buildLetExpr :: ![VarInfoPtr] !Expression !*(!*VarHeap, !*ExpressionHeap) -> (!Expression, !(!*VarHeap, !*ExpressionHeap))
buildLetExpr let_vars let_expr (var_heap, expr_heap)
	# (lazy_binds, lazy_binds_types, var_heap) = foldr build_bind ([], [], var_heap) let_vars
	| isEmpty lazy_binds
		= (let_expr, (var_heap, expr_heap))
		= case let_expr of
			Let inner_let=:{let_info_ptr }
				# (EI_LetType strict_bind_types, expr_heap) = readPtr let_info_ptr expr_heap
				  expr_heap = writePtr let_info_ptr (EI_LetType (strict_bind_types ++ lazy_binds_types)) expr_heap
				-> (Let { inner_let & let_lazy_binds = lazy_binds }, (var_heap, expr_heap))
			_
				# (let_info_ptr, expr_heap) = newPtr (EI_LetType lazy_binds_types) expr_heap
				-> (Let { let_strict_binds = [], let_lazy_binds = lazy_binds, let_expr = let_expr, let_info_ptr = let_info_ptr }, (var_heap, expr_heap))
where
	build_bind :: !VarInfoPtr !(!Env Expression FreeVar, ![AType], !*VarHeap)
		-> (!Env Expression FreeVar, ![AType], !*VarHeap)
	build_bind info_ptr (lazy_binds, lazy_binds_types, var_heap)
		# (let_info, var_heap) = readPtr info_ptr var_heap
		# (VI_LetExpression lei=:{lei_var,lei_expression,lei_status,lei_type}) = let_info
		  (LES_Updated updated_expr) = lei_status
		  (new_info_ptr, var_heap) = newPtr VI_Empty var_heap 
		  var_heap = var_heap <:= (info_ptr, VI_LetExpression { lei & lei_status = LES_Untouched, lei_var = { lei_var & fv_info_ptr = new_info_ptr }})
//			==> (lei_var.fv_name, info_ptr, new_info_ptr)
		= ([{ bind_src = updated_expr, bind_dst = lei_var } : lazy_binds], [lei_type : lazy_binds_types ], var_heap)

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

instance distributeLets (Bind a b) | distributeLets a
where
	distributeLets depth bind=:{bind_src} cp_info
		# (bind_src, cp_info) = distributeLets depth bind_src cp_info
		= ({ bind & bind_src = bind_src }, cp_info)
	
instance <<< ExprInfo
where
	(<<<) file EI_Empty			= file <<< "*Empty*"
	(<<<) file (EI_CaseType _)	= file <<< "CaseType"

instance <<< (Ptr a)
where
	(<<<) file ptr = file <<< ptrToInt ptr  

instance <<< BoundVar
where
	(<<<) file {var_name,var_info_ptr} = file <<< var_name <<< '[' <<< var_info_ptr <<< ']'

instance  <<<  FunctionBody
where
	(<<<) file (TransformedBody {tb_rhs}) = file <<<  tb_rhs

instance  <<<  CountedVariable
where
	(<<<) file {cv_variable,cv_count} = file <<< '<' <<< cv_variable <<< ',' <<< cv_count <<< '>'

(==>) a b :== a
//(==>) a b :== a ---> b
