implementation module convertDynamics

import syntax, transform, utilities, convertcases

::	*ConversionInfo =
	{	ci_predef_symb		:: !*PredefinedSymbols
	,	ci_var_heap			:: !*VarHeap
	,	ci_expr_heap		:: !*ExpressionHeap
	,	ci_new_functions 	:: ![FunctionInfoPtr]
	,	ci_fun_heap			:: !*FunctionHeap
	,	ci_next_fun_nr		:: !Index
	}

::	ConversionInput =
	{	cinp_glob_type_inst	:: !{! GlobalTCType} 
	,	cinp_group_index	:: !Int
	}

:: OpenedDynamic =
	{	opened_dynamic_expr :: Expression
	, 	opened_dynamic_type :: Expression
	}

:: DefaultExpression :== Optional (BoundVar, [IndirectionVar])   //DefaultRecord
:: DefaultRecord =
	{	c_i				:: BoundVar
	,	indirections	:: [IndirectionVar]
	}
:: BoundVariables 	 :== [(FreeVar, AType)]
:: IndirectionVar    :== BoundVar

convertDynamicPatternsIntoUnifyAppls :: {! GlobalTCType} !{# CommonDefs} !*{! Group} !*{#FunDef} !*PredefinedSymbols
		!*{#{# CheckedTypeDef}} !ImportedFunctions !*VarHeap !*TypeHeaps !*ExpressionHeap
			-> (!*{! Group}, !*{#FunDef}, !*PredefinedSymbols, !*{#{# CheckedTypeDef}}, !ImportedConstructors, !*VarHeap, !*TypeHeaps, !*ExpressionHeap)
convertDynamicPatternsIntoUnifyAppls global_type_instances common_defs groups fun_defs predefined_symbols
		imported_types imported_conses var_heap type_heaps expr_heap
	#! nr_of_funs = size fun_defs
	# (groups, (fun_defs, {ci_predef_symb, ci_var_heap, ci_expr_heap, ci_fun_heap, ci_new_functions}))
			= convert_groups 0 groups global_type_instances (fun_defs, {	
							ci_predef_symb = predefined_symbols, ci_var_heap = var_heap, ci_expr_heap = expr_heap,
							ci_new_functions = [], ci_fun_heap = newHeap, ci_next_fun_nr = nr_of_funs })
	  (groups, new_fun_defs, imported_types, imported_conses, type_heaps, ci_var_heap)
			= addNewFunctionsToGroups common_defs ci_fun_heap ci_new_functions groups imported_types imported_conses type_heaps ci_var_heap
	= (groups, { fundef \\ fundef <- [ fundef \\ fundef <-: fun_defs ] ++ new_fun_defs }, ci_predef_symb, imported_types, imported_conses, ci_var_heap, type_heaps, ci_expr_heap)
where
	convert_groups group_nr groups global_type_instances fun_defs_and_ci
		| group_nr == size groups
			= (groups, fun_defs_and_ci)
			#! group = groups.[group_nr]
			= convert_groups (inc group_nr) groups global_type_instances (foldSt (convert_function group_nr global_type_instances) group.group_members fun_defs_and_ci)

	convert_function group_nr global_type_instances fun (fun_defs, ci)
		#! fun_def = fun_defs.[fun]
		# {fun_body,fun_type} = fun_def
		  (fun_body, ci) = convert_dynamics_in_body {cinp_glob_type_inst = global_type_instances, cinp_group_index = group_nr} fun_body fun_type ci
		= ({fun_defs & [fun] = { fun_def & fun_body = fun_body }}, ci)

	convert_dynamics_in_body global_type_instances (TransformedBody {tb_args,tb_rhs}) (Yes {st_args}) ci
		# vars_with_types = zip2 tb_args st_args
		  (tb_rhs, ci) = convertDynamics global_type_instances vars_with_types No tb_rhs ci
		= (TransformedBody {tb_args = tb_args,tb_rhs = tb_rhs}, ci)
	convert_dynamics_in_body global_type_instances other fun_type ci
		= abort "unexpected value in 'convert dynamics.convert_dynamics_in_body'"



class convertDynamics a :: !ConversionInput !BoundVariables !DefaultExpression !a !*ConversionInfo -> (!a, !*ConversionInfo)

instance convertDynamics [a]  |  convertDynamics a
where
	convertDynamics :: !ConversionInput !BoundVariables !DefaultExpression ![a] !*ConversionInfo -> (![a], !*ConversionInfo)  |  convertDynamics a
	convertDynamics cinp bound_vars default_expr xs ci = mapSt (convertDynamics cinp bound_vars default_expr) xs ci

instance convertDynamics (Optional a)  |  convertDynamics a
where
	convertDynamics :: !ConversionInput !BoundVariables !DefaultExpression !(Optional a) !*ConversionInfo -> (!Optional a, !*ConversionInfo)  |  convertDynamics a
	convertDynamics cinp bound_vars default_expr (Yes x)	ci
		# (x, ci) = convertDynamics cinp bound_vars default_expr x ci
		= (Yes x, ci)
	convertDynamics _ _ _ No ci
		= (No, ci)

instance convertDynamics (Bind a b)  |  convertDynamics a
where
	convertDynamics :: !ConversionInput !BoundVariables !DefaultExpression !(Bind a b) !*ConversionInfo -> (!Bind a b, !*ConversionInfo)  |  convertDynamics a
	convertDynamics cinp bound_vars default_expr binding=:{bind_src} ci
		# (bind_src, ci) = convertDynamics cinp bound_vars default_expr bind_src ci
		= ({binding &  bind_src = bind_src}, ci)

convertDynamicsOfAlgebraicPattern :: !ConversionInput !BoundVariables !DefaultExpression !(!AlgebraicPattern,[AType]) !*ConversionInfo -> (!AlgebraicPattern,!*ConversionInfo)
convertDynamicsOfAlgebraicPattern cinp bound_vars default_expr (algebraic_pattern=:{ap_vars, ap_expr}, arg_types_of_conses) ci
	# (ap_expr, ci) = convertDynamics cinp (zipAppend2 ap_vars arg_types_of_conses bound_vars) default_expr ap_expr ci
	= ({algebraic_pattern &  ap_expr = ap_expr}, ci)

instance convertDynamics BasicPattern
where
	convertDynamics :: !ConversionInput !BoundVariables !DefaultExpression !BasicPattern !*ConversionInfo -> (!BasicPattern, !*ConversionInfo)
	convertDynamics cinp bound_vars default_expr basic_pattern=:{bp_expr} ci
		# (bp_expr, ci) = convertDynamics cinp bound_vars default_expr bp_expr ci
		= ({basic_pattern &  bp_expr = bp_expr}, ci)


instance convertDynamics Expression
where
	convertDynamics :: !ConversionInput !BoundVariables !DefaultExpression !Expression !*ConversionInfo -> (!Expression, !*ConversionInfo)
	convertDynamics cinp bound_vars default_expr (Var var) ci
		= (Var var, ci)
	convertDynamics cinp bound_vars default_expr (App appje=:{app_args}) ci
		# (app_args,ci) = convertDynamics cinp bound_vars default_expr app_args ci
		= (App {appje &  app_args = app_args}, ci)
	convertDynamics cinp bound_vars default_expr (expr @ exprs) ci
		# (expr,  ci) = convertDynamics cinp bound_vars default_expr expr  ci
		  (exprs, ci) = convertDynamics cinp bound_vars default_expr exprs ci
		= (expr @ exprs, ci)
	convertDynamics cinp bound_vars default_expr (Let letje=:{let_binds, let_expr,let_info_ptr}) ci
		# (let_types, ci) = determine_let_types let_info_ptr ci
		  bound_vars = zipAppend2 [ bind.bind_dst \\ bind <- let_binds ] let_types bound_vars
		  (let_binds, ci) = convertDynamics cinp bound_vars default_expr let_binds ci
		  (let_expr,  ci) = convertDynamics cinp bound_vars default_expr let_expr  ci
		= (Let { letje &  let_binds = let_binds, let_expr = let_expr}, ci)
	where
		determine_let_types let_info_ptr ci=:{ci_expr_heap}
			# (EI_LetType let_types, ci_expr_heap) = readPtr let_info_ptr ci_expr_heap
			= (let_types, { ci & ci_expr_heap = ci_expr_heap })

	convertDynamics cinp bound_vars default_expr (Case keesje=:{case_expr, case_guards, case_default, case_info_ptr}) ci
		# (case_expr,    ci) = convertDynamics cinp bound_vars default_expr case_expr ci
		  (case_default, ci) = convertDynamics cinp bound_vars default_expr case_default ci
		  (this_case_default, nested_case_default, ci) = determine_defaults case_default default_expr ci
		  (EI_CaseType {ct_cons_types, ct_result_type}, ci_expr_heap) = readPtr case_info_ptr ci.ci_expr_heap
		  ci = { ci & ci_expr_heap = ci_expr_heap }
		= case case_guards of
			(AlgebraicPatterns type algebraic_patterns)
				#  (algebraic_patterns, ci) = mapSt (convertDynamicsOfAlgebraicPattern cinp bound_vars nested_case_default)
													(zip2 algebraic_patterns ct_cons_types) ci
				-> (Case {keesje &  case_expr = case_expr, case_guards = AlgebraicPatterns type algebraic_patterns, case_default = this_case_default}, ci)
			(BasicPatterns type basic_patterns)
				#  (basic_patterns, ci) = convertDynamics  cinp bound_vars nested_case_default basic_patterns ci
				-> (Case {keesje &  case_expr = case_expr, case_guards = BasicPatterns type basic_patterns, case_default = this_case_default}, ci)
			(DynamicPatterns dynamic_patterns)
				#  keesje = {keesje &  case_expr = case_expr, case_default = this_case_default}
				-> convertDynamicPatterns cinp bound_vars keesje ci
			NoPattern
				-> (Case {keesje &  case_expr = case_expr, case_guards = NoPattern, case_default = this_case_default}, ci)
			_
				-> abort "unexpected value in convertDynamics: 'convertDynamics.CasePatterns'"
	convertDynamics cinp bound_vars default_expr (Selection opt_symb expression selections) ci
		# (expression,ci) = convertDynamics cinp bound_vars default_expr expression ci
		= (Selection opt_symb expression selections, ci)
	convertDynamics cinp bound_vars default_expr (Update expression1 selections expression2) ci
		# (expression1,ci) = convertDynamics cinp bound_vars default_expr expression1 ci
		# (expression2,ci) = convertDynamics cinp bound_vars default_expr expression2 ci
		= (Update expression1 selections expression2, ci)
	convertDynamics cinp bound_vars default_expr (RecordUpdate cons_symbol expression expressions) ci
		# (expression,ci) = convertDynamics cinp bound_vars default_expr expression ci
		# (expressions,ci) = convertDynamics cinp bound_vars default_expr expressions ci
		= (RecordUpdate cons_symbol expression expressions, ci)
	convertDynamics cinp bound_vars default_expr (TupleSelect definedSymbol int expression) ci
		# (expression,ci) = convertDynamics cinp bound_vars default_expr expression ci
		= (TupleSelect definedSymbol int expression, ci)
	convertDynamics _ _ _ (BasicExpr basicValue basicType) ci
		= (BasicExpr basicValue basicType, ci)
	convertDynamics _ _ _ (AnyCodeExpr codeBinding1 codeBinding2 strings) ci
		= (AnyCodeExpr codeBinding1 codeBinding2 strings, ci)
	convertDynamics _ _ _ (ABCCodeExpr strings bool) ci
		= (ABCCodeExpr strings bool, ci)
	convertDynamics cinp bound_vars default_expr (MatchExpr opt_symb symb expression) ci
		# (expression,ci) = convertDynamics cinp bound_vars default_expr expression ci
		= (MatchExpr opt_symb symb expression, ci)
	convertDynamics cinp bound_vars default_expr  (DynamicExpr {dyn_expr, dyn_info_ptr, dyn_uni_vars, dyn_type_code}) ci
		# (twoTuple_symb, ci) = getSymbol (GetTupleConsIndex 2) SK_Constructor 2 ci
		  (let_binds,     ci) = createVariables dyn_uni_vars [] ci
		  (dyn_expr,      ci) = convertDynamics cinp bound_vars default_expr dyn_expr ci
		  (dyn_type_code, ci) = convertTypecode cinp dyn_type_code ci
		= case let_binds of
			[]	-> (App {	app_symb		= twoTuple_symb,
							app_args 		= [dyn_expr, dyn_type_code],
							app_info_ptr	= nilPtr }, ci)
			_ 	#  (let_info_ptr,  ci) = let_ptr ci
				-> ( Let {	let_strict		= False,
							let_binds		= let_binds,
							let_expr		= App {	app_symb		= twoTuple_symb,
													app_args 		= [dyn_expr, dyn_type_code],
													app_info_ptr	= nilPtr },
							let_info_ptr	= let_info_ptr}, ci)
	convertDynamics cinp bound_vars default_expr (TypeCodeExpression type_code) ci
		= convertTypecode cinp type_code ci
	convertDynamics cinp bound_vars default_expr EE ci
		= (EE, ci)
	convertDynamics cinp bound_vars default_expr expression ci
		= abort "unexpected value in convertDynamics: 'convertDynamics.Expression'"

convertTypecode ::  !ConversionInput TypeCodeExpression !*ConversionInfo  -> (Expression,!*ConversionInfo)
convertTypecode cinp TCE_Empty ci
	= (EE, ci)
convertTypecode cinp (TCE_Var var_info_ptr) ci
	= (Var {var_name = a_ij_var_name, var_info_ptr = var_info_ptr, var_expr_ptr = nilPtr}, ci)
convertTypecode cinp (TCE_Constructor index typecode_exprs) ci
	# (typecons_symb,  ci) 	= getSymbol PD_TypeConsSymbol SK_Constructor 2 ci
	  constructor			= get_constructor cinp.cinp_glob_type_inst index
	  (typecode_exprs, ci)	= convertTypecodes cinp typecode_exprs ci
	= (App {app_symb		= typecons_symb,
			app_args 		= [constructor , typecode_exprs],
			app_info_ptr	= nilPtr}, ci)
convertTypecode cinp (TCE_Selector selections var_info_ptr) ci
	= (Selection No (Var { var_name = a_ij_var_name, var_info_ptr = var_info_ptr, var_expr_ptr = nilPtr }) selections, ci)

convertTypecodes :: !ConversionInput [TypeCodeExpression] !*ConversionInfo  -> (Expression,!*ConversionInfo)
convertTypecodes _ [] ci
	# (nil_symb, ci) = getSymbol PD_NilSymbol SK_Constructor 0 ci
	= (App {	app_symb		= nil_symb,
				app_args 		= [],
				app_info_ptr	= nilPtr}, ci)
convertTypecodes cinp [typecode_expr : typecode_exprs] ci
	# (cons_symb, ci) = getSymbol PD_ConsSymbol SK_Constructor 2 ci
	  (expr,      ci) = convertTypecode  cinp typecode_expr  ci
	  (exprs,     ci) = convertTypecodes cinp typecode_exprs ci
	= (App {	app_symb		= cons_symb,
				app_args 		= [expr , exprs],
				app_info_ptr	= nilPtr}, ci)


determine_defaults :: (Optional Expression) DefaultExpression !*ConversionInfo -> (Optional Expression, DefaultExpression, !*ConversionInfo)
/***
determine_defaults :: case_default default_expr varheap -> (this_case_default, nested_case_default, var_heap)
	this_case_default =	IF this case has no default, but there is a surrounding default
						THEN that is now the default and its reference count must be increased.
						ELSE it keeps this default
	nested_case_default  = 	IF this case has no default
		 					THEN the deault_expr remains default in the nested cases.
							ELSE nested cases get this default. This is semantically already the case, so nothing has to be changed.
***/
determine_defaults No default_expr=:(Yes (var=:{var_info_ptr}, indirection_var_list)) ci=:{ci_var_heap}
	#! var_info = sreadPtr var_info_ptr ci_var_heap
	# (expression, ci) = toExpression default_expr {ci & ci_var_heap = ci_var_heap}
	= case var_info of
		VI_Default ref_count
			-> (expression, default_expr, {ci & ci_var_heap = ci.ci_var_heap <:= (var_info_ptr, VI_Default (inc ref_count))} )
		_
			-> (expression, default_expr, ci )
determine_defaults case_default _ ci
	= (case_default, No, ci)


add_dynamic_bound_vars :: ![DynamicPattern] BoundVariables -> BoundVariables
add_dynamic_bound_vars [] bound_vars = bound_vars
add_dynamic_bound_vars [{dp_var, dp_type_patterns_vars} : patterns] bound_vars
	= add_dynamic_bound_vars patterns [(dp_var, empty_attributed_type) : mapAppend bind_info_ptr dp_type_patterns_vars bound_vars]
where
	bind_info_ptr var_info_ptr
		= ({fv_def_level = NotALevel, fv_name = a_ij_var_name, fv_info_ptr = var_info_ptr, fv_count = 0}, empty_attributed_type)


open_dynamic :: Expression !*ConversionInfo -> (OpenedDynamic, Bind Expression FreeVar, !*ConversionInfo)
open_dynamic dynamic_expr ci
	# (twotuple, ci) = getTupleSymbol 2 ci
	  (dynamicType_var, ci) = newVariable "dt" VI_Empty ci
	= (	{ opened_dynamic_expr = TupleSelect twotuple 0 dynamic_expr,   opened_dynamic_type = Var dynamicType_var },
	  	{ bind_src = TupleSelect twotuple 1 dynamic_expr,   bind_dst = varToFreeVar dynamicType_var 0 },
	  	ci)

/**************************************************************************************************/

convertDynamicPatterns :: !ConversionInput !BoundVariables !Case *ConversionInfo -> (Expression, *ConversionInfo)
convertDynamicPatterns cinp bound_vars {case_guards = DynamicPatterns [], case_default} ci
	= case case_default of
		(Yes expr)	-> (expr, ci)
		No			-> abort "unexpected value in convertDynamics: 'convertDynamicPatterns'"
convertDynamicPatterns cinp bound_vars {case_expr, case_guards = DynamicPatterns patterns, case_default, case_info_ptr} ci
	# (opened_dynamic, dt_bind, ci) = open_dynamic case_expr ci
	  (ind_0, ci) = newVariable "ind_0" VI_Empty ci
	  (c_1,   ci) = newVariable "c_1" (VI_Default 0) ci
      new_default = newDefault c_1 ind_0
      (result_type, ci) = getResultType case_info_ptr ci
      bound_vars = addToBoundVars (freeVarToVar dt_bind.bind_dst) empty_attributed_type (addToBoundVars ind_0 empty_attributed_type
      							  (addToBoundVars c_1 result_type (add_dynamic_bound_vars patterns bound_vars)))
	  (binds, expr, ci) = convertDynamicPattern cinp bound_vars new_default 1 opened_dynamic result_type case_default patterns ci
	  (let_info_ptr, ci) = let_ptr ci
	= (Let {let_strict = False, let_binds = [ dt_bind : binds ], let_expr = expr, let_info_ptr = let_info_ptr}, ci)

convertDynamicPattern :: !ConversionInput !BoundVariables DefaultExpression Int OpenedDynamic AType (Optional Expression) ![DynamicPattern] *ConversionInfo -> (Env Expression FreeVar, Expression, *ConversionInfo)
convertDynamicPattern cinp bound_vars this_default pattern_number opened_dynamic result_type last_default
																		[{ dp_var, dp_type_patterns_vars, dp_type_code, dp_rhs } : patterns] ci
	# /***  The last case may noy have a default  ***/
	  ind_var = getIndirectionVar this_default
      this_default = if (isEmpty patterns && (isNo last_default))  No  this_default

	  /***  convert the elements of this pattern  ***/
	  x_i_bind = { bind_src = opened_dynamic.opened_dynamic_expr,  bind_dst = dp_var }
	  (a_ij_binds, ci) = createVariables dp_type_patterns_vars [] ci
 	  (type_code, ci) = convertTypecode cinp dp_type_code ci
 	  (dp_rhs,    ci) = convertDynamics cinp bound_vars this_default dp_rhs ci

	  /***  recursively convert the other patterns  ***/
	  (binds, ci) = convertOtherPatterns cinp bound_vars this_default pattern_number opened_dynamic result_type last_default patterns ci

	  /***  generate the expression  ***/
 	  (unify_symb, ci) = getSymbol PD_unify SK_Function 2 ci
	  (twotuple,   ci) = getTupleSymbol 2 ci
	  (let_info_ptr,  ci) = let_ptr ci
	  (case_info_ptr, ci) = case_ptr ci
	  (default_expr, ci) = toExpression this_default ci
	  (unify_result, ci) = newVariable "result" VI_Empty ci
	  (unify_bool,   ci) = newVariable "unify_bool" VI_Empty ci
	  let_expr = Let {	let_strict = False,
	  					let_binds = [{ bind_src = App { app_symb = unify_symb,  app_args = [opened_dynamic.opened_dynamic_type, type_code],  app_info_ptr = nilPtr },
	  								   bind_dst = varToFreeVar unify_result 0 },
	  								 { bind_src = TupleSelect twotuple 0 (Var unify_result),
	  								   bind_dst = varToFreeVar unify_bool 0 },
	  								 { bind_src = TupleSelect twotuple 1 (Var unify_result),
	  								   bind_dst = varToFreeVar ind_var 0 }
	  								],
	  					let_expr = Case {	case_expr 		= Var unify_bool,
											case_guards		= BasicPatterns BT_Bool [{bp_value = BVB True, bp_expr = dp_rhs}],
											case_default	= default_expr,
											case_ident		= No,
											case_info_ptr	= case_info_ptr	},
	  					let_info_ptr = let_info_ptr	}
	= ([x_i_bind : a_ij_binds ++ binds],  let_expr,  ci)

convertOtherPatterns :: ConversionInput BoundVariables DefaultExpression Int OpenedDynamic AType !(Optional Expression) ![DynamicPattern] !*ConversionInfo -> (Env Expression FreeVar, *ConversionInfo)
convertOtherPatterns _ _ _ _ _ _  No  []  ci
	= ([], ci)
convertOtherPatterns cinp bound_vars this_default _ _ result_type (Yes last_default_expr) [] ci
	# c_i = getVariable this_default
	  (c_bind, ci) = generateBinding cinp bound_vars c_i last_default_expr result_type ci
	= ([c_bind], ci)
convertOtherPatterns cinp bound_vars this_default pattern_number opened_dynamic result_type last_default patterns ci
	# (ind_i,   ci) = newVariable ("ind_"+++toString (pattern_number)) VI_Empty ci
	  (c_inc_i, ci) = newVariable ("c_"+++toString (inc pattern_number)) (VI_Default 0) ci
      new_default = newDefault c_inc_i ind_i
      bound_vars = addToBoundVars ind_i empty_attributed_type (addToBoundVars c_inc_i result_type bound_vars)
 	  (binds, expr, ci) = convertDynamicPattern cinp bound_vars new_default (inc pattern_number) opened_dynamic result_type last_default patterns ci
	  c_i = getVariable this_default
	  (c_bind, ci) = generateBinding cinp bound_vars c_i expr result_type ci
   = ([c_bind : binds], ci)

generateBinding :: !ConversionInput BoundVariables BoundVar Expression AType !*ConversionInfo -> *(Bind Expression FreeVar, *ConversionInfo)
generateBinding cinp bound_vars var bind_expr result_type ci
	# (ref_count, ci) = get_reference_count var ci
	| ref_count == 0
		= ({ bind_src = bind_expr, bind_dst = varToFreeVar var 1}, ci)
		# (saved_defaults, ci_var_heap) = foldSt save_default bound_vars ([], ci.ci_var_heap)
		  (act_args, free_typed_vars, tb_rhs, ci_var_heap) = copyExpression bound_vars bind_expr ci_var_heap
		  ci_var_heap = foldSt restore_default saved_defaults ci_var_heap
		  tb_args = [ arg \\ (arg, _) <- free_typed_vars ]
		  arg_types = [ type \\ (_, type) <- free_typed_vars ]
		  (fun_symb,  (ci_next_fun_nr, ci_new_functions, ci_fun_heap))
				= newFunction No (TransformedBody {tb_args = tb_args, tb_rhs = tb_rhs}) arg_types result_type cinp.cinp_group_index
						(ci.ci_next_fun_nr, ci.ci_new_functions, ci.ci_fun_heap)
		= ({	bind_src = App {	app_symb 		= fun_symb,
									app_args 		= act_args,
									app_info_ptr	= nilPtr },
				bind_dst = varToFreeVar var (inc ref_count) },
		   { ci & ci_var_heap = ci_var_heap, ci_next_fun_nr = ci_next_fun_nr, ci_new_functions = ci_new_functions, ci_fun_heap = ci_fun_heap })
	where
		get_reference_count {var_name,var_info_ptr} ci=:{ci_var_heap}
			# (info, ci_var_heap) = readPtr var_info_ptr ci_var_heap
			  ci = { ci & ci_var_heap = ci_var_heap }
			= case info of
				VI_Default ref_count	-> (ref_count, ci)
//				_						-> (0, ci) ---> ("get_reference_count", var_name)  /* A predicted variable always has a ref_count */ 
		
		save_default ({fv_info_ptr},_) (saved_defaults, ci_var_heap)
			# (info, ci_var_heap) = readPtr fv_info_ptr ci_var_heap
			= case info of
				VI_Default ref_count	-> ([(fv_info_ptr, ref_count) : saved_defaults] , ci_var_heap)
				_						-> (saved_defaults, ci_var_heap)
				
		restore_default (var_info_ptr,ref_count) ci_var_heap
			= ci_var_heap <:= (var_info_ptr, VI_Default ref_count)


/**************************************************************************************************/

createVariables :: [VarInfoPtr] !(Env Expression FreeVar) !*ConversionInfo -> (!Env Expression FreeVar, !*ConversionInfo)
createVariables var_info_ptrs binds ci
	= mapAppendSt create_variable var_info_ptrs binds ci
where
	create_variable :: VarInfoPtr !*ConversionInfo -> (Bind Expression FreeVar, !*ConversionInfo)
	create_variable var_info_ptr ci
		# (placeholder_symb, ci) = getSymbol PD_variablePlaceholder SK_Constructor 3 ci
		  cyclic_var = {var_name = a_ij_var_name, var_info_ptr = var_info_ptr, var_expr_ptr = nilPtr}	
		= ({ bind_src = App {	app_symb = placeholder_symb,
								app_args = [Var cyclic_var, Var cyclic_var],
								app_info_ptr = nilPtr },
			 bind_dst = varToFreeVar cyclic_var 1
		   },
		   ci)

/**************************************************************************************************/

newVariable :: String !VarInfo !*ConversionInfo -> *(!BoundVar,!*ConversionInfo)
newVariable var_name var_info ci=:{ci_var_heap}
	# (var_info_ptr, ci_var_heap) = newPtr var_info ci_var_heap
	= ( { var_name = {id_name = var_name, id_info = nilPtr},  var_info_ptr = var_info_ptr, var_expr_ptr = nilPtr},
	    { ci & ci_var_heap = ci_var_heap })	


newDefault :: BoundVar IndirectionVar -> DefaultExpression
newDefault variable indirection_var = Yes (variable, [indirection_var])

getVariable :: DefaultExpression -> BoundVar
getVariable (Yes (variable, _)) = variable
getVariable No = abort "unexpected value in convertDynamics: 'getVariable'"

getIndirectionVar (Yes (_, [ind_var:_])) = ind_var
getIndirectionVar No = abort "unexpected value in convertDynamics: 'getIndirectionVar'"

toExpression :: DefaultExpression !*ConversionInfo -> (Optional Expression, !*ConversionInfo)
toExpression No ci = (No, ci)
toExpression (Yes (variable, indirection_var_list)) ci
	# (expression, ci) = toExpression2 variable indirection_var_list ci
	= (Yes expression, ci)
where
	toExpression2 variable [] ci = (Var variable, ci)
	toExpression2 variable [indirection_var : indirection_vars] ci
		# (expression, ci) = toExpression2 variable indirection_vars ci
		  (undo_symb, ci) = getSymbol PD_undo_indirections SK_Function 2 ci
		= (App {	app_symb = undo_symb,
					app_args = [expression, Var indirection_var],
					app_info_ptr = nilPtr }, ci)

varToFreeVar :: BoundVar Int -> FreeVar
varToFreeVar {var_name, var_info_ptr} count
	= {fv_def_level = NotALevel, fv_name = var_name, fv_info_ptr = var_info_ptr, fv_count = count}

freeVarToVar ::  FreeVar -> BoundVar
freeVarToVar {fv_name, fv_info_ptr}
	= { var_name = fv_name,  var_info_ptr = fv_info_ptr, var_expr_ptr = nilPtr}


addToBoundVars :: BoundVar AType BoundVariables -> BoundVariables
addToBoundVars var type bound_vars
	= [ (varToFreeVar var 0, type) : bound_vars ]


get_constructor :: !{!GlobalTCType} Index -> Expression
get_constructor glob_type_inst index
	= BasicExpr (BVS ("\"" +++ toString  glob_type_inst.[index] +++ "\"")) (BT_String TE)


instance toString GlobalTCType
where
	toString (GTT_Basic basic_type)				= toString basic_type
	toString GTT_Function						= " -> "
	toString (GTT_Constructor type_symb_indent)	= type_symb_indent.type_name.id_name

instance toString BasicType
where
	toString BT_Int 		= "Int"
	toString BT_Char		= "Char"
	toString BT_Real		= "Real"
	toString BT_Bool		= "Bool"
	toString BT_Dynamic		= "Dynamic"
	toString BT_File		= "File"
	toString BT_World		= "World"
	toString (BT_String _)	= "String"


getResultType :: ExprInfoPtr !*ConversionInfo -> (!AType, !*ConversionInfo)
getResultType case_info_ptr ci=:{ci_expr_heap}
	# (EI_CaseType {ct_result_type}, ci_expr_heap) = readPtr case_info_ptr ci_expr_heap
	= (ct_result_type, {ci & ci_expr_heap = ci_expr_heap})

getSymbol :: Index ((Global Index) -> SymbKind) Int !*ConversionInfo -> (SymbIdent, !*ConversionInfo)
getSymbol index symb_kind arity ci=:{ci_predef_symb}
	# ({pds_module, pds_def, pds_ident}, ci_predef_symb) = ci_predef_symb![index]
	  ci = {ci & ci_predef_symb = ci_predef_symb}
	  symbol = { symb_name = pds_ident, symb_kind = symb_kind { glob_module = pds_module, glob_object = pds_def}, symb_arity = arity }
	= (symbol, ci)

getTupleSymbol arity ci=:{ci_predef_symb}
	# ({pds_def, pds_ident}, ci_predef_symb) = ci_predef_symb![GetTupleConsIndex arity]
    = ( {ds_ident = pds_ident, ds_arity = arity, ds_index = pds_def}, {ci & ci_predef_symb = ci_predef_symb })

getGlobalIndex :: Index !*ConversionInfo -> (Global Index, !*ConversionInfo)
getGlobalIndex index ci=:{ci_predef_symb}
	# ({pds_module, pds_def}, ci_predef_symb) = ci_predef_symb![index]
	= ( { glob_module = pds_module, glob_object = pds_def} , {ci & ci_predef_symb = ci_predef_symb} )

getConstructor :: Index Int !*ConversionInfo -> (Global DefinedSymbol, !*ConversionInfo)
getConstructor index arity ci=:{ci_predef_symb}
	# ({pds_module, pds_def, pds_ident}, ci_predef_symb) = ci_predef_symb![index]
	  defined_symbol = { ds_ident = pds_ident, ds_arity = arity, ds_index = pds_def}
	= (	{glob_object = defined_symbol, glob_module = pds_module} , {ci & ci_predef_symb = ci_predef_symb} )


a_ij_var_name :== { id_name = "a_ij", id_info = nilPtr }

case_ptr :: !*ConversionInfo -> (ExprInfoPtr, !*ConversionInfo)
case_ptr ci=:{ci_expr_heap}
	# (expr_info_ptr, ci_expr_heap) = newPtr (EI_CaseType {	ct_pattern_type = empty_attributed_type,
															ct_result_type = empty_attributed_type,
															ct_cons_types = repeat (repeat empty_attributed_type)}) ci_expr_heap
	= (expr_info_ptr, {ci &  ci_expr_heap = ci_expr_heap})

let_ptr :: !*ConversionInfo -> (ExprInfoPtr, !*ConversionInfo)
let_ptr ci=:{ci_expr_heap}
	# (expr_info_ptr, ci_expr_heap) = newPtr (EI_LetType (repeat empty_attributed_type)) ci_expr_heap
	= (expr_info_ptr, {ci &  ci_expr_heap = ci_expr_heap})


empty_attributed_type :: AType
empty_attributed_type = { at_attribute = TA_Multi, at_annotation = AN_None, at_type = TE }



isNo :: (Optional a) -> Bool
isNo (Yes _) = False
isNo No = True

zipAppend2 :: [.a] [.b] u:[w:(.a,.b)] -> v:[x:(.a,.b)], [w <= x, u <= v]
zipAppend2   []       ys     zs = zs
zipAppend2   xs       []     zs = zs
zipAppend2 [x : xs] [y : ys] zs = [ (x,y)  :  zipAppend2 xs ys zs ]


instance <<< FreeVar
where
	(<<<) file {fv_name,fv_info_ptr} = file <<< fv_name <<< '[' <<< fv_info_ptr <<< ']'

instance <<< Ptr a
where
	(<<<) file ptr = file <<< ptrToInt ptr  



