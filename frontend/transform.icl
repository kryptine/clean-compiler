implementation module transform

import syntax, check, StdCompare, utilities, mergecases; //, RWSDebug

::	LiftState =
	{	ls_var_heap		:: !.VarHeap
	,	ls_x :: !.LiftStateX
	,	ls_expr_heap	:: !.ExpressionHeap
	}
	
::	LiftStateX = {
		x_fun_defs :: !.{#FunDef},
		x_main_dcl_module_n :: !Int
	}

class lift a :: !a !*LiftState -> (!a, !*LiftState)

instance lift [a] | lift a
where
	lift l ls = mapSt lift l ls

instance lift (a,b) | lift a & lift b
where
	lift t ls = app2St (lift,lift) t ls

instance lift (Optional a) | lift a
where
	lift (Yes x) ls
		# (x, ls) = lift x ls
		= (Yes x, ls)
	lift no ls
		= (no, ls)
	
instance lift CheckedAlternative
where
	lift ca=:{ca_rhs} ls
		# (ca_rhs, ls) = lift ca_rhs ls
		= ({ ca & ca_rhs = ca_rhs }, ls)
	
instance lift Expression
where
	lift (FreeVar {fv_name,fv_info_ptr}) ls=:{ls_var_heap}
		#! var_info = sreadPtr fv_info_ptr ls_var_heap
		= case var_info of
			 VI_LiftedVariable var_info_ptr
			 	# (var_expr_ptr, ls_expr_heap) = newPtr EI_Empty ls.ls_expr_heap
			 	-> (Var { var_name = fv_name, var_info_ptr = var_info_ptr, var_expr_ptr = var_expr_ptr }, { ls & ls_expr_heap = ls_expr_heap})
			 _
			 	# (var_expr_ptr, ls_expr_heap) = newPtr EI_Empty ls.ls_expr_heap
			 	-> (Var { var_name = fv_name, var_info_ptr = fv_info_ptr, var_expr_ptr = var_expr_ptr }, { ls & ls_expr_heap = ls_expr_heap})
	lift (App app) ls
		# (app, ls) = lift app ls
		= (App app, ls)
	lift (expr @ exprs) ls
		# ((expr,exprs), ls) = lift (expr,exprs) ls
		= (expr @ exprs, ls)
	lift (Let lad=:{let_strict_binds, let_lazy_binds, let_expr}) ls
		# (let_strict_binds, ls) = lift let_strict_binds ls
		  (let_lazy_binds, ls) = lift let_lazy_binds ls
		  (let_expr, ls) = lift let_expr ls
		= (Let {lad & let_strict_binds = let_strict_binds, let_lazy_binds = let_lazy_binds, let_expr = let_expr}, ls)
	lift (Case case_expr) ls
		# (case_expr, ls) = lift case_expr ls
		= (Case case_expr, ls)
	lift (Selection is_unique expr selectors) ls
		# (selectors, ls) = lift selectors ls
		  (expr, ls) = lift expr ls
		= (Selection is_unique expr selectors, ls)
	lift (Update expr1 selectors expr2) ls
		# (selectors, ls) = lift selectors ls
		  (expr1, ls) = lift expr1 ls
		  (expr2, ls) = lift expr2 ls
		= (Update expr1 selectors expr2, ls)
	lift (RecordUpdate cons_symbol expression expressions) ls
		# (expression, ls) = lift expression ls
		  (expressions, ls) = lift expressions ls
		= (RecordUpdate cons_symbol expression expressions, ls)
	lift (TupleSelect symbol argn_nr expr) ls
		# (expr, ls) = lift expr ls
		= (TupleSelect symbol argn_nr expr, ls)
/*	lift (Lambda vars expr) ls
		# (expr, ls) = lift expr ls
		= (Lambda vars expr, ls)
*/	lift (MatchExpr opt_tuple cons_symb expr) ls
		# (expr, ls) = lift expr ls
		= (MatchExpr opt_tuple cons_symb expr, ls)
	lift expr ls
		= (expr, ls)

instance lift Selection
where
	lift (ArraySelection array_select expr_ptr index_expr) ls
		# (index_expr, ls) = lift index_expr ls
		= (ArraySelection array_select expr_ptr index_expr, ls)
	lift record_selection ls
		= (record_selection, ls)

instance lift App
where
	lift app=:{app_symb = app_symbol=:{symb_arity,symb_kind = SK_Function {glob_object,glob_module}}, app_args} ls
		# (app_args, ls) = lift app_args ls
		| glob_module == ls.ls_x.LiftStateX.x_main_dcl_module_n
			#! fun_def = ls.ls_x.x_fun_defs.[glob_object]
			# {fun_info={fi_free_vars}} = fun_def
			  fun_lifted = length fi_free_vars
			| fun_lifted > 0
				# (app_args, ls_var_heap, ls_expr_heap) = add_free_variables_in_app fi_free_vars app_args ls.ls_var_heap ls.ls_expr_heap
				= ({ app & app_args = app_args, app_symb = { app_symbol & symb_arity = symb_arity + fun_lifted }},
						{ ls & ls_var_heap = ls_var_heap, ls_expr_heap = ls_expr_heap })
				= ({ app & app_args = app_args }, ls)
			= ({ app & app_args = app_args }, ls)
	lift app=:{app_symb = app_symbol=:{symb_arity,symb_kind = SK_LocalMacroFunction glob_object}, app_args} ls
		# (app_args, ls) = lift app_args ls
		#! fun_def = ls.ls_x.x_fun_defs.[glob_object]
		# {fun_info={fi_free_vars}} = fun_def
		  fun_lifted = length fi_free_vars
		| fun_lifted > 0
			# (app_args, ls_var_heap, ls_expr_heap) = add_free_variables_in_app fi_free_vars app_args ls.ls_var_heap ls.ls_expr_heap
			= ({ app & app_args = app_args, app_symb = { app_symbol & symb_arity = symb_arity + fun_lifted }},
					{ ls & ls_var_heap = ls_var_heap, ls_expr_heap = ls_expr_heap })
			= ({ app & app_args = app_args }, ls)
	lift app=:{app_args} ls
		# (app_args, ls) = lift app_args ls
		= ({ app & app_args = app_args }, ls)

add_free_variables_in_app :: ![FreeVar] ![Expression] !u:VarHeap !*ExpressionHeap -> (![Expression],!u:VarHeap,!*ExpressionHeap)
add_free_variables_in_app [] app_args var_heap expr_heap
	= (app_args, var_heap, expr_heap)
add_free_variables_in_app [{fv_name, fv_info_ptr} : free_vars] app_args var_heap expr_heap
	#! var_info = sreadPtr fv_info_ptr var_heap
	= case var_info of
		VI_LiftedVariable var_info_ptr
		 	# (var_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
			-> add_free_variables_in_app free_vars [Var { var_name = fv_name, var_info_ptr = var_info_ptr, var_expr_ptr = var_expr_ptr } : app_args]
					var_heap expr_heap
		_
		 	# (var_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
			-> add_free_variables_in_app free_vars [Var { var_name = fv_name, var_info_ptr = fv_info_ptr, var_expr_ptr = var_expr_ptr } : app_args]
					var_heap expr_heap

instance lift LetBind
where
	lift bind=:{lb_src} ls
		# (lb_src, ls) = lift lb_src ls
		= ({ bind & lb_src = lb_src }, ls)

instance lift (Bind a b) | lift a
where
	lift bind=:{bind_src} ls
		# (bind_src, ls) = lift bind_src ls
		= ({ bind & bind_src = bind_src }, ls)

instance lift Case
where
	lift kees=:{ case_expr,case_guards,case_default } ls
		# ((case_expr,(case_guards,case_default)), ls) = lift (case_expr,(case_guards,case_default)) ls
		= ({ kees & case_expr = case_expr,case_guards = case_guards, case_default = case_default }, ls)

instance lift CasePatterns
where
	lift (AlgebraicPatterns type patterns) ls
		# (patterns, ls) = lift patterns ls
		= (AlgebraicPatterns type patterns, ls)
	lift (BasicPatterns type patterns) ls
		# (patterns, ls) = lift patterns ls
		= (BasicPatterns type patterns, ls)
	lift (DynamicPatterns patterns) ls
		# (patterns, ls) = lift patterns ls
		= (DynamicPatterns patterns, ls)

instance lift AlgebraicPattern
where
	lift pattern=:{ap_expr} ls
		# (ap_expr, ls) = lift ap_expr ls
		= ({ pattern & ap_expr = ap_expr }, ls)

instance lift BasicPattern
where
	lift pattern=:{bp_expr} ls
		# (bp_expr, ls) = lift bp_expr ls
		= ({ pattern & bp_expr = bp_expr }, ls)

instance lift DynamicPattern
where
	lift pattern=:{dp_rhs} ls
		# (dp_rhs, ls) = lift dp_rhs ls
		= ({ pattern & dp_rhs = dp_rhs }, ls)

unfoldVariable :: !BoundVar UnfoldInfo !*UnfoldState -> (!Expression, !*UnfoldState)
unfoldVariable var=:{var_name,var_info_ptr} ui us
	#! (var_info, us) = readVarInfo var_info_ptr us
	= case var_info of 
		VI_Expression expr
			-> (expr, us)
		VI_Variable var_name var_info_ptr
		 	# (var_expr_ptr, us_symbol_heap) = newPtr EI_Empty us.us_symbol_heap
			-> (Var {var_name = var_name, var_info_ptr = var_info_ptr, var_expr_ptr = var_expr_ptr}, { us & us_symbol_heap = us_symbol_heap})
		VI_Body fun_symb _ vars
			-> (App {	app_symb = fun_symb,
						app_args = [ Var { var_name=fv_name, var_info_ptr=fv_info_ptr, var_expr_ptr=nilPtr }
									\\ {fv_name,fv_info_ptr}<-vars],
						app_info_ptr = nilPtr }, us)
		VI_Dictionary app_symb app_args class_type
			# (new_class_type, us_opt_type_heaps) = substitute_class_types class_type us.us_opt_type_heaps
			  (new_info_ptr, us_symbol_heap) = newPtr (EI_DictionaryType new_class_type) us.us_symbol_heap
			  app = App { app_symb = app_symb, app_args = app_args, app_info_ptr = new_info_ptr }
			  us = { us & us_opt_type_heaps = us_opt_type_heaps, us_symbol_heap = us_symbol_heap }
			-> unfold app ui us
		_
			-> (Var var, us)
  where
	substitute_class_types class_types No
		= (class_types, No)
	substitute_class_types class_types (Yes type_heaps)
		# (_,new_class_types, type_heaps) = substitute class_types type_heaps
		= (new_class_types, Yes type_heaps)


readVarInfo var_info_ptr us
	#! var_info = sreadPtr var_info_ptr us.us_var_heap
	= case var_info of
		VI_Extended _ original	-> (original, us)
		_						-> (var_info, us)

writeVarInfo :: VarInfoPtr VarInfo *VarHeap -> *VarHeap
writeVarInfo var_info_ptr new_var_info var_heap
	# (old_var_info, var_heap) = readPtr var_info_ptr var_heap
	= case old_var_info of
		VI_Extended extensions _	-> writePtr var_info_ptr (VI_Extended extensions new_var_info) var_heap
		_							-> writePtr var_info_ptr new_var_info var_heap

::	CopiedLocalFunction = {
		old_function_n :: !Int,
		new_function_n :: !Int
	}

::	CopiedLocalFunctions = {
		copied_local_functions :: [CopiedLocalFunction],
		used_copied_local_functions :: [CopiedLocalFunction],
		new_copied_local_functions :: [CopiedLocalFunction],
		next_local_function_n :: !Int
	}

::	UnfoldState =
	{	us_var_heap				:: !.VarHeap
	,	us_symbol_heap			:: !.ExpressionHeap
	,	us_opt_type_heaps		:: !.Optional .TypeHeaps,
		us_cleanup_info			:: ![ExprInfoPtr],
		us_local_macro_functions :: !Optional CopiedLocalFunctions
	}

::	UnfoldInfo =
	{	ui_handle_aci_free_vars	:: !AciFreeVarHandleMode,
		ui_convert_module_n :: !Int, // -1 if no conversion
		ui_conversion_table :: !Optional ConversionTable
	}

:: AciFreeVarHandleMode = LeaveThem | RemoveThem | SubstituteThem

class unfold a :: !a !UnfoldInfo !*UnfoldState -> (!a, !*UnfoldState)

instance unfold Expression
where
	unfold (Var var) ui us
		= unfoldVariable var ui us
	unfold (App app) ui us
		# (app, us) = unfold app ui us
		= (App app, us)
	unfold (expr @ exprs) ui us
		# ((expr,exprs), us) = unfold (expr,exprs) ui us
		= (expr @ exprs, us)
	unfold (Let lad) ui us
		# (lad, us) = unfold lad ui us
		= (Let lad, us)
	unfold (Case case_expr) ui us
		# (case_expr, us) = unfold case_expr ui us
		= (Case case_expr, us)
	unfold (Selection is_unique expr selectors) ui us
		# ((expr, selectors), us) = unfold (expr, selectors) ui us
		= (Selection is_unique expr selectors, us)
	unfold (Update expr1 selectors expr2) ui us
		# (((expr1, expr2), selectors), us) = unfold ((expr1, expr2), selectors) ui us
		= (Update expr1 selectors expr2, us)
	unfold (RecordUpdate cons_symbol expression expressions) ui us
		# ((expression, expressions), us) = unfold (expression, expressions) ui us
		= (RecordUpdate cons_symbol expression expressions, us)
	unfold (TupleSelect symbol argn_nr expr) ui us
		# (expr, us) = unfold expr ui us
		= (TupleSelect symbol argn_nr expr, us)
/*	unfold (Lambda vars expr) ui us
		# (expr, us) = unfold expr ui us
		= (Lambda vars expr, us)
*/	unfold (MatchExpr opt_tuple cons_symb expr) ui us
		# (expr, us) = unfold expr ui us
		= (MatchExpr opt_tuple cons_symb expr, us)
	unfold (DynamicExpr expr) ui us
		# (expr, us) = unfold expr ui us
		= (DynamicExpr expr, us)
	unfold expr ui us
		= (expr, us)

instance unfold DynamicExpr
where
	unfold expr=:{dyn_expr} ui us
		# (dyn_expr, us) = unfold dyn_expr ui us
		= ({ expr & dyn_expr = dyn_expr }, us)

instance unfold Selection
where
	unfold (ArraySelection array_select expr_ptr index_expr) ui us=:{us_symbol_heap}
		# (new_ptr, us_symbol_heap) = newPtr EI_Empty us_symbol_heap
		  (index_expr, us) = unfold index_expr ui { us & us_symbol_heap = us_symbol_heap}
		= (ArraySelection array_select new_ptr index_expr, us)
	unfold (DictionarySelection var selectors expr_ptr index_expr) ui us=:{us_symbol_heap}
		# (new_ptr, us_symbol_heap) = newPtr EI_Empty us_symbol_heap
		  (index_expr, us) = unfold index_expr ui { us & us_symbol_heap = us_symbol_heap}
		  (var_expr, us) = unfoldVariable var ui us
		= case var_expr of 
			App {app_symb={symb_kind= SK_Constructor _ }, app_args}
				# [RecordSelection _ field_index:_] = selectors
				  (App { app_symb = {symb_name, symb_kind = SK_Function array_select}}) =  app_args !! field_index
				-> (ArraySelection { array_select & glob_object = { ds_ident = symb_name, ds_arity = 2, ds_index = array_select.glob_object}}
							new_ptr index_expr, us)
			Var var
				-> (DictionarySelection var selectors new_ptr index_expr, us)
	unfold record_selection ui us
		= (record_selection, us)

instance unfold FreeVar
where
	unfold fv=:{fv_info_ptr,fv_name} ui us=:{us_var_heap}
		# (new_info_ptr, us_var_heap) = newPtr VI_Empty us_var_heap
		= ({ fv & fv_info_ptr = new_info_ptr }, { us & us_var_heap = writePtr fv_info_ptr (VI_Variable fv_name new_info_ptr) us_var_heap })
instance unfold App
where
	unfold app=:{app_symb={symb_kind}, app_args, app_info_ptr} ui=:{ui_convert_module_n,ui_conversion_table} us
		= case symb_kind of
			SK_Function {glob_module,glob_object}
				| ui_convert_module_n==glob_module 
					# (Yes conversion_table) = ui_conversion_table
					# app={app & app_symb.symb_kind=SK_Function {glob_module=glob_module,glob_object=conversion_table.[cFunctionDefs].[glob_object]}}
					-> unfold_function_app app ui us
					-> unfold_function_app app ui us
			SK_Macro {glob_module,glob_object}
				| ui_convert_module_n==glob_module
					# (Yes conversion_table) = ui_conversion_table
					# app={app & app_symb.symb_kind=SK_Macro {glob_module=glob_module,glob_object=conversion_table.[cMacroDefs].[glob_object]}}
					-> unfold_function_app app ui us
					-> unfold_function_app app ui us
			SK_OverloadedFunction {glob_module,glob_object}
				| ui_convert_module_n==glob_module
					# (Yes conversion_table) = ui_conversion_table
					# app={app & app_symb.symb_kind=SK_OverloadedFunction {glob_module=glob_module,glob_object=conversion_table.[cFunctionDefs].[glob_object]}}
					-> unfold_function_app app ui us
					-> unfold_function_app app ui us
			SK_LocalMacroFunction local_macro_function_n
				# (us_local_macro_functions,us) = us!us_local_macro_functions
				-> case us_local_macro_functions of
					No
						-> unfold_function_app app ui us
					uslocal_macro_functions=:(Yes local_macro_functions)
						# (new_local_macro_function_n,us_local_macro_functions) = determine_new_local_macro_function_n local_macro_function_n local_macro_functions
							with
								determine_new_local_macro_function_n local_macro_function_n local_macro_functions=:{copied_local_functions,used_copied_local_functions,new_copied_local_functions,next_local_function_n}
									# new_local_macro_function_n = search_new_local_macro_function_n used_copied_local_functions
									| new_local_macro_function_n>=0
										= (new_local_macro_function_n,us_local_macro_functions)
									# (new_local_macro_function_n,used_copied_local_functions) = search_new_local_macro_function_n_and_add_to_used_functions copied_local_functions used_copied_local_functions
									| new_local_macro_function_n>=0
										= (new_local_macro_function_n,Yes {local_macro_functions & used_copied_local_functions=used_copied_local_functions})
									# (new_local_macro_function_n,used_copied_local_functions) = search_new_local_macro_function_n_and_add_to_used_functions new_copied_local_functions used_copied_local_functions
									| new_local_macro_function_n>=0
										= (new_local_macro_function_n,Yes {local_macro_functions & used_copied_local_functions=used_copied_local_functions})
										# new_local_function = {old_function_n=local_macro_function_n,new_function_n=next_local_function_n}
										# new_copied_local_functions=new_copied_local_functions++[new_local_function]
										# us_local_macro_functions=Yes {copied_local_functions=copied_local_functions,
																		new_copied_local_functions=new_copied_local_functions,
																		used_copied_local_functions=[new_local_function:used_copied_local_functions],
																		next_local_function_n=next_local_function_n+1}
										= (next_local_function_n,us_local_macro_functions)
									where
										search_new_local_macro_function_n [{old_function_n,new_function_n}:local_functions]
											| local_macro_function_n==old_function_n
												= new_function_n
											 	= search_new_local_macro_function_n local_functions
										search_new_local_macro_function_n []
											= -1

										search_new_local_macro_function_n_and_add_to_used_functions [copied_local_function=:{old_function_n,new_function_n}:local_functions] used_copied_local_functions
											| local_macro_function_n==old_function_n
												= (new_function_n,[copied_local_function:used_copied_local_functions])
											 	= search_new_local_macro_function_n_and_add_to_used_functions local_functions used_copied_local_functions
										search_new_local_macro_function_n_and_add_to_used_functions [] used_copied_local_functions
											= (-1,used_copied_local_functions)
						# us={us & us_local_macro_functions=us_local_macro_functions}
						# app={app & app_symb.symb_kind=SK_LocalMacroFunction new_local_macro_function_n}
						-> unfold_function_app app ui us
			SK_Constructor _
				| not (isNilPtr app_info_ptr)
					# (app_info, us_symbol_heap) = readPtr app_info_ptr us.us_symbol_heap
					  (new_app_info, us_opt_type_heaps) = substitute_EI_DictionaryType app_info us.us_opt_type_heaps
					  (new_info_ptr, us_symbol_heap) = newPtr new_app_info us_symbol_heap
					  us={ us & us_symbol_heap = us_symbol_heap, us_opt_type_heaps = us_opt_type_heaps }
					  (app_args, us) = unfold app_args ui us
					-> ({ app & app_args = app_args, app_info_ptr = new_info_ptr}, us) 
					# (app_args, us) = unfold app_args ui us
					-> ({ app & app_args = app_args}, us)
			_
				# (app_args, us) = unfold app_args ui us
				-> ({ app & app_args = app_args, app_info_ptr = nilPtr}, us) 
	where
		unfold_function_app app=:{app_args, app_info_ptr} ui us
			# (new_info_ptr, us_symbol_heap) = newPtr EI_Empty us.us_symbol_heap
			# us={ us & us_symbol_heap = us_symbol_heap }
			# (app_args, us) = unfold app_args ui us
			= ({ app & app_args = app_args, app_info_ptr = new_info_ptr}, us) 

		substitute_EI_DictionaryType (EI_DictionaryType class_type) (Yes type_heaps)
			# (_,new_class_type, type_heaps) = substitute class_type type_heaps
			= (EI_DictionaryType new_class_type, Yes type_heaps)
		substitute_EI_DictionaryType x opt_type_heaps
			= (x, opt_type_heaps)

instance unfold LetBind
where
	unfold bind=:{lb_src} ui us
		# (lb_src, us) = unfold lb_src ui us
		= ({ bind & lb_src = lb_src }, us)

instance unfold (Bind a b) | unfold a
where
	unfold bind=:{bind_src} ui us
		# (bind_src, us) = unfold bind_src ui us
		= ({ bind & bind_src = bind_src }, us)

instance unfold Case
where
	unfold kees=:{ case_expr,case_guards,case_default,case_info_ptr} ui us=:{us_cleanup_info}
		# (old_case_info, us_symbol_heap) = readPtr case_info_ptr us.us_symbol_heap
		  (new_case_info, us_opt_type_heaps) = substitute_let_or_case_type old_case_info us.us_opt_type_heaps
		  (new_info_ptr, us_symbol_heap) = newPtr new_case_info us_symbol_heap
		  us_cleanup_info = case old_case_info of
								EI_Extended _ _	-> [new_info_ptr:us_cleanup_info]
								_				-> us_cleanup_info
		  us = { us & us_symbol_heap = us_symbol_heap, us_opt_type_heaps = us_opt_type_heaps, us_cleanup_info=us_cleanup_info }
		  ((case_guards,case_default), us) = unfold (case_guards,case_default) ui us
		  (case_expr, us) = update_active_case_info_and_unfold case_expr new_info_ptr us
		= ({ kees & case_expr = case_expr,case_guards = case_guards, case_default = case_default, case_info_ptr =  new_info_ptr}, us)
	where
		update_active_case_info_and_unfold case_expr=:(Var {var_info_ptr}) case_info_ptr us
			# (case_info, us_symbol_heap) = readPtr case_info_ptr us.us_symbol_heap
			  us = { us & us_symbol_heap = us_symbol_heap }
			= case case_info of
				EI_Extended (EEI_ActiveCase aci=:{aci_free_vars}) ei
					#!(new_aci_free_vars, us) = case ui.ui_handle_aci_free_vars of
													LeaveThem		-> (aci_free_vars, us)
													RemoveThem		-> (No, us)
													SubstituteThem	-> case aci_free_vars of
																		No		-> (No, us)
																		Yes fvs	# (fvs_subst, us) = mapSt unfoldBoundVar fvs us
																				-> (Yes fvs_subst, us)
					  (var_info, us) = readVarInfo var_info_ptr us
					-> case var_info of
						VI_Body fun_symb {tb_args, tb_rhs} new_aci_params
							# tb_args_ptrs = [ fv_info_ptr \\ {fv_info_ptr}<-tb_args ] 
							  (original_bindings, us_var_heap) = mapSt readPtr tb_args_ptrs us.us_var_heap
							  us_var_heap = fold2St bind tb_args_ptrs new_aci_params us_var_heap
							  (tb_rhs, us) = unfold tb_rhs ui { us & us_var_heap = us_var_heap }
							  us_var_heap = fold2St writePtr tb_args_ptrs original_bindings us.us_var_heap
							  new_aci = { aci & aci_params = new_aci_params, aci_opt_unfolder = Yes fun_symb, aci_free_vars = new_aci_free_vars }
							  new_eei = (EI_Extended (EEI_ActiveCase new_aci) ei)
							  us_symbol_heap = writePtr case_info_ptr new_eei us.us_symbol_heap
							-> (tb_rhs, { us & us_var_heap = us_var_heap, us_symbol_heap = us_symbol_heap })
						_	# new_eei = EI_Extended (EEI_ActiveCase { aci & aci_free_vars = new_aci_free_vars }) ei
							  us_symbol_heap = writePtr case_info_ptr new_eei us.us_symbol_heap
							-> unfold case_expr ui { us & us_symbol_heap = us_symbol_heap }
				_	-> unfold case_expr ui us	
		  where 
			// XXX consider to store BoundVars in VI_Body
			bind fv_info_ptr {fv_name=name, fv_info_ptr=info_ptr} var_heap
				= writeVarInfo fv_info_ptr (VI_Expression (Var {var_name=name, var_info_ptr=info_ptr, var_expr_ptr = nilPtr})) var_heap
/*
			bind ({fv_info_ptr}, var_bound_var) var_heap
				= writeVarInfo fv_info_ptr (VI_Expression var_bound_var) var_heap
*/

/*		update_active_case_info_and_unfold case_expr=:(Var {var_info_ptr}) case_info_ptr us
			#! var_info = sreadPtr var_info_ptr us.us_var_heap
			= case var_info of
				VI_Body fun_symb fun_body new_aci_var_info_ptr
					# (fun_body, us) = unfold fun_body us
					  (EI_Extended (EEI_ActiveCase aci) ei, us_symbol_heap) = readPtr case_info_ptr us.us_symbol_heap
					  new_aci = { aci & aci_var_info_ptr = new_aci_var_info_ptr, aci_opt_unfolder = Yes fun_symb }
					  us_symbol_heap = writePtr case_info_ptr (EI_Extended (EEI_ActiveCase new_aci) ei) us_symbol_heap
					-> (fun_body, { us & us_symbol_heap = us_symbol_heap })
				_	-> unfold case_expr us
*/
		update_active_case_info_and_unfold case_expr _ us
			= unfold case_expr ui us

		unfoldBoundVar {var_info_ptr} us
			# (VI_Expression (Var act_var), us_var_heap) = readPtr var_info_ptr us.us_var_heap
			= (act_var, { us & us_var_heap = us_var_heap })

instance unfold Let
where
	unfold lad=:{let_strict_binds, let_lazy_binds, let_expr, let_info_ptr} ui us
		# (let_strict_binds, us) = copy_bound_vars let_strict_binds us
		# (let_lazy_binds, us) = copy_bound_vars let_lazy_binds us
		# (let_strict_binds, us) = unfold let_strict_binds ui us
		# (let_lazy_binds, us) = unfold let_lazy_binds ui us
		# (let_expr, us) = unfold let_expr ui us
		  (old_let_info, us_symbol_heap) = readPtr let_info_ptr us.us_symbol_heap
		  (new_let_info, us_opt_type_heaps) = substitute_let_or_case_type old_let_info us.us_opt_type_heaps
		  (new_info_ptr, us_symbol_heap) = newPtr new_let_info us_symbol_heap
		= ({lad & let_strict_binds = let_strict_binds, let_lazy_binds = let_lazy_binds, let_expr = let_expr, let_info_ptr = new_info_ptr},
			{ us & us_symbol_heap = us_symbol_heap, us_opt_type_heaps = us_opt_type_heaps })
		where
			copy_bound_vars [bind=:{lb_dst} : binds] us
				# (lb_dst, us) = unfold lb_dst ui us
				  (binds, us) = copy_bound_vars binds us
				= ([ {bind & lb_dst = lb_dst} : binds ], us)
			copy_bound_vars [] us
				= ([], us)

substitute_let_or_case_type	expr_info No
	= (expr_info, No)
substitute_let_or_case_type	(EI_Extended extensions expr_info) yes_type_heaps
	# (new_expr_info, yes_type_heaps) = substitute_let_or_case_type expr_info yes_type_heaps
	= (EI_Extended extensions new_expr_info, yes_type_heaps)
substitute_let_or_case_type	(EI_CaseType case_type) (Yes type_heaps)
	# (_,new_case_type, type_heaps) = substitute case_type type_heaps
	= (EI_CaseType new_case_type, Yes type_heaps)
substitute_let_or_case_type	(EI_LetType let_type) (Yes type_heaps)
	# (_,new_let_type, type_heaps) = substitute let_type type_heaps
	= (EI_LetType new_let_type, Yes type_heaps)

instance unfold CasePatterns
where
	unfold (AlgebraicPatterns type patterns) ui us
		# (patterns, us) = unfold patterns ui us
		= (AlgebraicPatterns type patterns, us)
	unfold (BasicPatterns type patterns) ui us
		# (patterns, us) = unfold patterns ui us
		= (BasicPatterns type patterns, us)
	unfold (DynamicPatterns patterns) ui us
		# (patterns, us) = unfold patterns ui us
		= (DynamicPatterns patterns, us)

instance unfold BasicPattern
where
	unfold guard=:{bp_expr} ui us
		# (bp_expr, us) = unfold bp_expr ui us
		= ({ guard & bp_expr = bp_expr }, us)

instance unfold AlgebraicPattern
where
	unfold guard=:{ap_vars,ap_expr} ui us
		# (ap_vars, us) = unfold ap_vars ui us
		  (ap_expr, us) = unfold ap_expr ui us
		= ({ guard & ap_vars = ap_vars, ap_expr = ap_expr }, us)

instance unfold DynamicPattern
where
	unfold guard=:{dp_var,dp_rhs} ui us
		# (dp_var, us) = unfold dp_var ui us
		  (dp_rhs, us) = unfold dp_rhs ui us
		= ({ guard & dp_var = dp_var, dp_rhs = dp_rhs }, us)

instance unfold [a] | unfold a
where
	unfold l ui us
		// = mapSt unfold l ui us
		= map_st l us
		where
			map_st [x : xs] s
			 	# (x, s) = unfold x ui s
				  (xs, s) = map_st xs s
				#! s = s
				= ([x : xs], s)
			map_st [] s
			 	= ([], s)

instance unfold (a,b) | unfold a & unfold b
where
//	unfold t ui us = app2St (unfold,unfold) t ui us
	unfold (a,b) ui us
		# (a,us) = unfold a ui us
		# (b,us) = unfold b ui us
		= ((a,b),us)

instance unfold (Optional a) | unfold a
where
	unfold (Yes x) ui us
		# (x, us) = unfold x ui us
		= (Yes x, us)
	unfold no ui us
		= (no, us)

//import StdDebug

updateFunctionCalls :: ![FunCall] ![FunCall] !*{# FunDef} !*SymbolTable
	-> (![FunCall], !*{# FunDef}, !*SymbolTable)
updateFunctionCalls calls collected_calls fun_defs symbol_table
	= foldSt add_function_call calls (collected_calls, fun_defs, symbol_table)
where
	add_function_call fc=:{fc_index} (collected_calls, fun_defs, symbol_table)
//		# fc_index = trace ("add_function_call: "+++toString fc_index+++" ") fc_index
		# ({fun_symb}, fun_defs) = fun_defs![fc_index]
		  (collected_calls, symbol_table) = examineFunctionCall fun_symb fc (collected_calls, symbol_table) 
		= (collected_calls, fun_defs, symbol_table)

examineFunctionCall {id_info} fc=:{fc_index} (calls, symbol_table)
	# (entry, symbol_table) = readPtr id_info symbol_table
	= case entry.ste_kind of
		STE_Called indexes
			| isMember fc_index indexes
				-> (calls, symbol_table)
				-> ([ fc : calls ], symbol_table <:= (id_info, { entry & ste_kind = STE_Called [ fc_index : indexes ]}))
		_
			-> ( [ fc : calls ], symbol_table <:=
					(id_info, { ste_kind = STE_Called [fc_index], ste_index = NoIndex, ste_def_level = NotALevel, ste_previous = entry }))

copy_macro_and_local_functions :: FunDef (Optional CopiedLocalFunctions) *ExpandState -> (!FunDef,![(CopiedLocalFunction,FunDef)],!Optional CopiedLocalFunctions,!*ExpandState);
copy_macro_and_local_functions macro=:{fun_kind} local_macro_functions es
	# is_def_macro=case fun_kind of FK_DefMacro->True; _->False
	# (macro,local_macro_functions,es) = copy_macro_or_local_macro_function is_def_macro macro local_macro_functions es
	# (new_functions,local_macro_functions,es) = copy_local_functions_of_macro local_macro_functions is_def_macro [] es
	= (macro,new_functions,local_macro_functions,es)

copy_local_functions_of_macro :: (Optional CopiedLocalFunctions) Bool [CopiedLocalFunction] *ExpandState -> (![(CopiedLocalFunction,FunDef)],!Optional CopiedLocalFunctions,!*ExpandState);
copy_local_functions_of_macro local_macro_functions is_def_macro local_functions_to_be_copied es
	# (local_functions_to_be_copied,local_macro_functions) = add_new_local_functions_to_be_copied local_functions_to_be_copied local_macro_functions
		with
			add_new_local_functions_to_be_copied local_functions_to_be_copied local_macro_functions=:(Yes copied_local_macro_functions=:{new_copied_local_functions=[]})
				= (local_functions_to_be_copied,Yes {copied_local_macro_functions & used_copied_local_functions=[]})
			add_new_local_functions_to_be_copied local_functions_to_be_copied (Yes {copied_local_functions,new_copied_local_functions,next_local_function_n})
				# local_macro_functions=Yes {copied_local_functions=copied_local_functions++new_copied_local_functions,
											new_copied_local_functions=[],used_copied_local_functions=[],next_local_function_n=next_local_function_n}
				= (local_functions_to_be_copied++new_copied_local_functions,local_macro_functions)
	= case local_functions_to_be_copied of
		[]
			-> ([],local_macro_functions,es)
		[(old_and_new_function_n=:{old_function_n,new_function_n}):local_functions_to_be_copied]
			# (function,es)=es!es_fun_defs.[old_function_n]
			
			#! function_group_index=function.fun_info.fi_group_index
			# es = {es & es_fun_defs.[old_function_n].fun_info.fi_group_index= if (function_group_index>NoIndex) (-2-function_group_index) function_group_index}
			# function = {function & fun_info.fi_group_index=if (function_group_index<NoIndex) (-2-function_group_index) function_group_index}

			# (function,local_macro_functions,es) = copy_macro_or_local_macro_function is_def_macro function local_macro_functions es
			# function={function & fun_index=new_function_n}
			# (new_functions,local_macro_functions,es) = copy_local_functions_of_macro local_macro_functions is_def_macro local_functions_to_be_copied es
			-> ([(old_and_new_function_n,function):new_functions],local_macro_functions,es)

update_calls calls No
	= calls
update_calls calls (Yes {used_copied_local_functions=[]})
	= calls
update_calls calls (Yes {used_copied_local_functions})
	# calls = remove_old_calls calls
	= add_new_calls used_copied_local_functions calls
where
	remove_old_calls [call=:{fc_index}:calls]
		| contains_old_function_n used_copied_local_functions
//			# calls = trace ("remove_old_calls1: "+++toString fc_index) calls
			= remove_old_calls calls
//			# calls = trace ("remove_old_calls2: "+++toString fc_index) calls
			= [call:remove_old_calls calls]
	where
		contains_old_function_n [{old_function_n}:local_functions]
			= fc_index==old_function_n || contains_old_function_n local_functions
		contains_old_function_n []
			= False
	remove_old_calls []
		= []
	
	add_new_calls [{new_function_n}:local_functions] calls
//		# local_functions = trace ("add_new_calls: "+++toString new_function_n) local_functions
		= add_new_calls local_functions [{fc_index=new_function_n,fc_level=NotALevel}:calls]
	add_new_calls [] calls
		= calls

copy_macro_or_local_macro_function :: !Bool !FunDef !(Optional CopiedLocalFunctions) !*ExpandState -> (!FunDef,!Optional CopiedLocalFunctions,!.ExpandState);
copy_macro_or_local_macro_function is_def_macro macro=:{fun_body = TransformedBody {tb_args,tb_rhs},fun_kind,fun_info={fi_local_vars,fi_calls}} local_macro_functions es=:{es_var_heap,es_symbol_heap,es_expand_in_imp_module,es_main_dcl_module_n,es_dcl_modules}
	# (tb_args,es_var_heap) = create_new_arguments tb_args es_var_heap
		with
			create_new_arguments [var=:{fv_name,fv_info_ptr} : vars] var_heap
				# (new_vars,var_heap) = create_new_arguments vars var_heap
				# (new_info, var_heap) = newPtr VI_Empty var_heap
				# new_var = { fv_name = fv_name, fv_def_level = NotALevel, fv_info_ptr = new_info, fv_count = 0 }
				= ([new_var : new_vars], writePtr fv_info_ptr (VI_Variable fv_name new_info) var_heap)
			create_new_arguments [] var_heap
				= ([],var_heap)
	# us = { us_symbol_heap = es_symbol_heap, us_var_heap = es_var_heap, us_opt_type_heaps = No,us_cleanup_info = [],
			 us_local_macro_functions = local_macro_functions }
	# (result_expr,dcl_modules,{us_local_macro_functions,us_symbol_heap,us_var_heap}) = unfold_and_convert es_dcl_modules us
		with
			unfold_and_convert dcl_modules us
				| es_expand_in_imp_module && is_def_macro
					# (dcl_mod,dcl_modules) = dcl_modules![es_main_dcl_module_n]
					# ui = {ui_handle_aci_free_vars = RemoveThem, ui_convert_module_n = es_main_dcl_module_n, ui_conversion_table=dcl_mod.dcl_conversions }
					# (expr,es) = unfold tb_rhs ui us
					= (expr,dcl_modules,es)
			
					# ui = {ui_handle_aci_free_vars = RemoveThem, ui_convert_module_n = -1 ,ui_conversion_table=No }
					# (expr,es) = unfold tb_rhs ui us
					= (expr,dcl_modules,es)
	# (fi_local_vars,us_var_heap) = update_local_vars fi_local_vars us_var_heap
		with
			update_local_vars :: ![FreeVar] !*(Heap VarInfo) -> (![FreeVar],!*Heap VarInfo);
			update_local_vars [fv=:{fv_info_ptr}:fvs] var_heap
				# (fvs,var_heap)=update_local_vars fvs var_heap
				# (fv_info,var_heap) = readPtr fv_info_ptr var_heap
//				# fv = {fv & fv_info_ptr=case fv_info of (VI_Variable _ info_ptr) -> info_ptr}
				# fv = {fv & fv_info_ptr=case fv_info of 
											(VI_Variable _ info_ptr) -> info_ptr
						}
				= ([fv:fvs],var_heap)
			update_local_vars [] var_heap
				= ([],var_heap)
	# fi_calls = update_calls fi_calls us_local_macro_functions
	= ({macro & fun_body = TransformedBody {tb_args=tb_args,tb_rhs=result_expr},fun_info.fi_local_vars=fi_local_vars,fun_info.fi_calls=fi_calls},us_local_macro_functions,
		{es & es_var_heap=us_var_heap, es_symbol_heap=us_symbol_heap, es_dcl_modules=dcl_modules})

unfoldMacro :: !FunDef ![Expression] !*ExpandInfo -> (!Expression, !*ExpandInfo)
unfoldMacro {fun_body = TransformedBody {tb_args,tb_rhs}, fun_info = {fi_calls},fun_kind,fun_symb} args (calls, es=:{es_var_heap,es_symbol_heap,es_fun_defs,es_expand_in_imp_module,es_main_dcl_module_n,es_dcl_modules})
	# is_def_macro=case fun_kind of FK_DefMacro->True; _->False
	# (let_binds, var_heap) = bind_expressions tb_args args [] es_var_heap
	#! size_fun_defs = size es_fun_defs
	# copied_local_functions = Yes { copied_local_functions=[],used_copied_local_functions=[],new_copied_local_functions=[],next_local_function_n=size_fun_defs}
	# us = { us_symbol_heap = es_symbol_heap, us_var_heap = var_heap, us_opt_type_heaps = No,us_cleanup_info = [], us_local_macro_functions = copied_local_functions }
	# (result_expr,dcl_modules,{us_local_macro_functions,us_symbol_heap,us_var_heap}) = unfold_and_convert es_dcl_modules us
		with
			unfold_and_convert dcl_modules us
				| es_expand_in_imp_module && is_def_macro
					# (dcl_mod,dcl_modules) = dcl_modules![es_main_dcl_module_n]
					# ui = {ui_handle_aci_free_vars = RemoveThem, ui_convert_module_n = es_main_dcl_module_n, ui_conversion_table=dcl_mod.dcl_conversions }
					# (result_expr,us) = unfold tb_rhs ui us
					= (result_expr,dcl_modules,us)

					# ui = {ui_handle_aci_free_vars = RemoveThem, ui_convert_module_n = -1 ,ui_conversion_table=No }
					# (result_expr,us) = unfold tb_rhs ui us
					= (result_expr,dcl_modules,us)
					
	# es = {es & es_var_heap = us_var_heap, es_symbol_heap = us_symbol_heap, es_dcl_modules=dcl_modules}
	# fi_calls = update_calls fi_calls us_local_macro_functions
	# (new_functions,us_local_macro_functions,es) = copy_local_functions_of_macro us_local_macro_functions is_def_macro [] es
	# {es_symbol_heap,es_symbol_table,es_fun_defs,es_new_fun_def_numbers} = es
	# (es_fun_defs,es_new_fun_def_numbers) = case new_functions of
		[]
			-> (es_fun_defs,es_new_fun_def_numbers)
		_
			# last_function_index = case us_local_macro_functions of (Yes {next_local_function_n}) -> next_local_function_n-1
			# new_fun_defs = new_fun_defs
				with
					new_fun_defs :: *{!FunDef}
					new_fun_defs => {fun_def \\ (_,fun_def)<-new_functions}
			-> ({if (i<size_fun_defs) es_fun_defs.[i] new_fun_defs.[i-size_fun_defs] \\ i<-[0..last_function_index]} // inefficient
				,[size_fun_defs:es_new_fun_def_numbers])
	# (calls, fun_defs, es_symbol_table) = updateFunctionCalls fi_calls calls es_fun_defs es_symbol_table
	| isEmpty let_binds
		= (result_expr, (calls, { es & es_symbol_table = es_symbol_table, es_fun_defs=fun_defs,es_new_fun_def_numbers=es_new_fun_def_numbers }))
		# (new_info_ptr, es_symbol_heap) = newPtr EI_Empty es_symbol_heap
		# result_expr=Let { let_strict_binds = [], let_lazy_binds = let_binds, let_expr = result_expr, let_info_ptr = new_info_ptr, let_expr_position = NoPos }
		= (result_expr, (calls, { es & es_symbol_table = es_symbol_table, es_symbol_heap=es_symbol_heap, es_fun_defs=fun_defs,es_new_fun_def_numbers=es_new_fun_def_numbers }))
where
	bind_expressions [var : vars] [expr : exprs] binds var_heap
		# (binds, var_heap) = bind_expressions vars exprs binds var_heap
		= bind_expression var expr binds var_heap
	bind_expressions _ _ binds var_heap
		= (binds, var_heap)

	bind_expression :: FreeVar Expression [LetBind] *(Heap VarInfo) -> (![LetBind],!*Heap VarInfo);
	bind_expression {fv_count} expr binds var_heap
		| fv_count == 0
			= (binds, var_heap)
	bind_expression {fv_info_ptr} (Var {var_name,var_info_ptr}) binds var_heap
		= (binds, writePtr fv_info_ptr (VI_Variable var_name var_info_ptr) var_heap)
	bind_expression {fv_name,fv_info_ptr,fv_count} expr binds var_heap
		| fv_count == 1
			= (binds, writePtr fv_info_ptr (VI_Expression expr) var_heap)
		# (new_info, var_heap) = newPtr VI_Empty var_heap
		  new_var = { fv_name = fv_name, fv_def_level = NotALevel, fv_info_ptr = new_info, fv_count = 0 }
		= ([{ lb_src = expr, lb_dst = new_var, lb_position = NoPos} : binds], writePtr fv_info_ptr (VI_Variable fv_name new_info) var_heap)

::	Group =
	{	group_members	:: ![Int]
//	,	group_number	:: !Int
	}

::	PartitioningInfo = 
	{	pi_symbol_table	:: !.SymbolTable
//	,	pi_marks		:: !.{# Int}
	,	pi_var_heap		:: !.VarHeap
	,	pi_symbol_heap	:: !.ExpressionHeap
	,	pi_error		:: !.ErrorAdmin
	,	pi_next_num		:: !Int
	,	pi_next_group	:: !Int
	,	pi_groups		:: ![[Int]]
	,	pi_deps			:: ![Int]
	}

NotChecked :== -1	

:: PredefSymbolsForTransform = { predef_alias_dummy :: !PredefinedSymbol, predef_and :: !PredefinedSymbol, predef_or :: !PredefinedSymbol };

partitionateMacros :: !IndexRange !Index !PredefSymbolsForTransform !*{# FunDef} !*{# DclModule} !*VarHeap !*ExpressionHeap !*SymbolTable !*ErrorAdmin
	-> (!*{# FunDef}, !.{# DclModule}, !*VarHeap, !*ExpressionHeap, !*SymbolTable, !*ErrorAdmin )
partitionateMacros {ir_from,ir_to} mod_index predef_symbols_for_transform fun_defs modules var_heap symbol_heap symbol_table error
	#! max_fun_nr = size fun_defs
	# partitioning_info = { pi_var_heap = var_heap, pi_symbol_heap = symbol_heap,
							pi_symbol_table = symbol_table,
							pi_error = error, pi_deps = [], pi_next_num = 0, pi_next_group = 0, pi_groups = [] }
	  (fun_defs, modules, {pi_symbol_table, pi_var_heap, pi_symbol_heap, pi_error, pi_next_group, pi_groups, pi_deps})
	  		= iFoldSt (pationate_macro mod_index max_fun_nr) ir_from ir_to (fun_defs, modules, partitioning_info)

//	# (size_fun_defs,fun_defs) = usize fun_defs
//	# fun_defs=trace ("size_fun_defs: "+++toString size_fun_defs+++" ") fun_defs;

	= (foldSt reset_body_of_rhs_macro pi_deps fun_defs, modules, pi_var_heap, pi_symbol_heap, pi_symbol_table, pi_error)
where
	reset_body_of_rhs_macro macro_index macro_defs
		# (macro_def, macro_defs) = macro_defs![macro_index]
		= case macro_def.fun_body of
			RhsMacroBody body
				-> { macro_defs & [macro_index] = { macro_def & fun_body = CheckedBody body }}
			_
				-> macro_defs

	pationate_macro mod_index max_fun_nr macro_index (macro_defs, modules, pi)
		# (macro_def, macro_defs) = macro_defs![macro_index]
//		| macro_def.fun_kind == FK_Macro
		| case macro_def.fun_kind of FK_DefMacro->True ; FK_ImpMacro->True; _ -> False
		 	= case macro_def.fun_body of
		 		CheckedBody body
			  		# macros_modules_pi = foldSt (visit_macro mod_index max_fun_nr) macro_def.fun_info.fi_calls
			  					({ macro_defs & [macro_index] = { macro_def & fun_body = PartioningMacro }}, modules, pi)
					-> expand_simple_macro mod_index macro_index macro_def macros_modules_pi
		 		PartioningMacro
		  			# identPos = newPosition macro_def.fun_symb macro_def.fun_pos
		 			-> (macro_defs,  modules, { pi &  pi_error = checkError macro_def.fun_symb "recursive macro definition" (setErrorAdmin identPos pi.pi_error)  })
		 		_
		 			-> (macro_defs, modules, pi)
			= (macro_defs, modules, pi)

	visit_macro mod_index max_fun_nr {fc_index} macros_modules_pi
		= pationate_macro mod_index max_fun_nr fc_index macros_modules_pi
	
	expand_simple_macro mod_index macro_index macro=:{fun_body = CheckedBody body, fun_info, fun_symb, fun_pos,fun_kind}
			(macro_defs, modules, pi=:{pi_symbol_table,pi_symbol_heap,pi_var_heap,pi_error})
		| macros_are_simple fun_info.fi_calls macro_defs
		  	# identPos = newPosition fun_symb fun_pos
			# expand_in_imp_module=case fun_kind of FK_ImpMacro->True; _ -> False
			  es = { es_symbol_table = pi_symbol_table, es_var_heap = pi_var_heap,
					 es_symbol_heap = pi_symbol_heap, es_error = setErrorAdmin identPos pi_error,
					 es_fun_defs=macro_defs, es_main_dcl_module_n = mod_index, es_dcl_modules=modules,
					 es_expand_in_imp_module=expand_in_imp_module,es_new_fun_def_numbers=[]
					  }			
			# (tb_args, tb_rhs, local_vars, fi_calls, fun_info, {es_symbol_table, es_var_heap, es_symbol_heap, es_error,es_dcl_modules,es_fun_defs})
					= expandMacrosInBody [] body predef_symbols_for_transform macro_index es
			# macro = { macro & fun_body = TransformedBody { tb_args = tb_args, tb_rhs = tb_rhs},
			  			fun_info = { fun_info & fi_calls = fi_calls, fi_local_vars = local_vars }}
			= ({ es_fun_defs & [macro_index] = macro }, es_dcl_modules,
					{ pi & pi_symbol_table = es_symbol_table, pi_symbol_heap = es_symbol_heap, pi_var_heap = es_var_heap, pi_error = es_error })
			# pi = { pi & pi_deps = [macro_index:pi.pi_deps] }
			= ({ macro_defs & [macro_index] = { macro & fun_body = RhsMacroBody body }}, modules, pi)

	macros_are_simple [] macro_defs
		= True
	macros_are_simple [ {fc_index} : calls ] macro_defs
		# {fun_kind,fun_body} = macro_defs.[fc_index]
		= is_a_pattern_macro fun_kind fun_body && macros_are_simple calls macro_defs
	where
		is_a_pattern_macro FK_DefMacro (TransformedBody {tb_args})
			= True
		is_a_pattern_macro FK_ImpMacro (TransformedBody {tb_args})
			= True
		is_a_pattern_macro _ _
			= False

add_new_macros_to_groups :: ![Int] !Int Int *{#FunDef} [Int] [[Int]] -> (!Int,!*{#FunDef},![Int],![[Int]]);
add_new_macros_to_groups [new_macro_fun_def_index] n_fun_defs_after_expanding_macros pi_next_group es_fun_defs functions_in_group pi_groups
	= add_new_macro_and_local_functions_to_groups new_macro_fun_def_index n_fun_defs_after_expanding_macros pi_next_group es_fun_defs functions_in_group pi_groups
add_new_macros_to_groups [new_macro_fun_def_index:macro_fun_def_numbers=:[next_macro_fun_def_index:_]] n_fun_defs_after_expanding_macros pi_next_group es_fun_defs functions_in_group pi_groups
	# (pi_next_group,es_fun_defs,functions_in_group,pi_groups)
		= add_new_macro_and_local_functions_to_groups new_macro_fun_def_index next_macro_fun_def_index pi_next_group es_fun_defs functions_in_group pi_groups
	= add_new_macros_to_groups macro_fun_def_numbers n_fun_defs_after_expanding_macros pi_next_group es_fun_defs functions_in_group pi_groups
add_new_macros_to_groups [] n_fun_defs_after_expanding_macros pi_next_group es_fun_defs functions_in_group pi_groups
	= (pi_next_group,es_fun_defs,functions_in_group,pi_groups)

add_new_macro_and_local_functions_to_groups :: !Int !Int Int *{#FunDef} [Int] [[Int]] -> (!Int,!*{#FunDef},![Int],![[Int]]);
add_new_macro_and_local_functions_to_groups new_macro_fun_def_index n_fun_defs_after_expanding_macros pi_next_group es_fun_defs functions_in_group pi_groups
	# (pi_next_group,es_fun_defs,functions_in_group,macros)
		= add_macros_to_current_group new_macro_fun_def_index n_fun_defs_after_expanding_macros pi_next_group es_fun_defs functions_in_group []
	# (macros_with_group_numbers,es_fun_defs) = add_group_numbers macros es_fun_defs
		with
			add_group_numbers [fun_def_index:l] es_fun_defs
				# (group_number,es_fun_defs) = es_fun_defs![fun_def_index].fun_info.fi_group_index
//				# group_number=trace ("add_group_numbers: "+++toString fun_def_index+++" "+++toString group_number+++"\n") group_number;
				# (l,es_fun_defs) = add_group_numbers l es_fun_defs
				= ([(fun_def_index,group_number):l],es_fun_defs)
			add_group_numbers [] es_fun_defs
				= ([],es_fun_defs)
	# sorted_macros_with_group_numbers = sortBy (\(_,group_number1) (_,group_number2) -> group_number1<group_number2) macros_with_group_numbers
	# (pi_next_group,pi_groups) = partition_macros_in_groups sorted_macros_with_group_numbers [] (-1) pi_next_group pi_groups
		with
			partition_macros_in_groups [(fun_def_index,fun_def_group_number):l] [] group_number pi_next_group pi_groups
				= partition_macros_in_groups l [fun_def_index] fun_def_group_number pi_next_group pi_groups
			partition_macros_in_groups [(fun_def_index,fun_def_group_number):l] group group_number pi_next_group pi_groups
				| fun_def_group_number==group_number
					= partition_macros_in_groups l [fun_def_index:group] group_number pi_next_group pi_groups
					# pi_groups=[group:pi_groups]
					# pi_next_group=pi_next_group+1
					= partition_macros_in_groups l [fun_def_index] fun_def_group_number pi_next_group pi_groups			
			partition_macros_in_groups [] [] group_number pi_next_group pi_groups
				= (pi_next_group,pi_groups)
			partition_macros_in_groups [] last_group group_number pi_next_group pi_groups
				= (pi_next_group+1,[last_group:pi_groups])
	= (pi_next_group,es_fun_defs,functions_in_group,pi_groups)

add_macros_to_current_group :: !Int !Int Int *{#FunDef} [Int] [Int] -> (!Int,!*{#FunDef},![Int],![Int]);
add_macros_to_current_group new_macro_fun_def_index n_fun_defs_after_expanding_macros pi_next_group es_fun_defs functions_in_group macros
	| new_macro_fun_def_index>=n_fun_defs_after_expanding_macros
		= (pi_next_group,es_fun_defs,functions_in_group,macros)
	| es_fun_defs.[new_macro_fun_def_index].fun_info.fi_group_index<=NoIndex
		= abort ("add_macros_to_current_group: "+++toString new_macro_fun_def_index)
//				+++" "+++toString es_fun_defs.[new_macro_fun_def_index].fun_info.fi_group_index)

	| es_fun_defs.[new_macro_fun_def_index].fun_info.fi_group_index==pi_next_group
//		# new_macro_fun_def_index=trace ("add_macros_to_current_group1: "+++toString new_macro_fun_def_index+++"\n") new_macro_fun_def_index;
		# functions_in_group=[new_macro_fun_def_index:functions_in_group]
		= add_macros_to_current_group (new_macro_fun_def_index+1) n_fun_defs_after_expanding_macros pi_next_group es_fun_defs functions_in_group macros

//		# new_macro_fun_def_index=trace ("add_macros_to_current_group2: "+++toString new_macro_fun_def_index+++"\n") new_macro_fun_def_index;
//		# pi_groups=[[new_macro_fun_def_index]:pi_groups]
//		# pi_next_group=pi_next_group+1
		= add_macros_to_current_group (new_macro_fun_def_index+1) n_fun_defs_after_expanding_macros pi_next_group es_fun_defs functions_in_group [new_macro_fun_def_index:macros]

partitionateAndLiftFunctions :: ![IndexRange] !Index !PredefSymbolsForTransform !*{# FunDef} !*{# DclModule} !*VarHeap !*ExpressionHeap !*SymbolTable !*ErrorAdmin
	-> (!*{! Group}, !*{# FunDef}, !.{# DclModule}, !*VarHeap, !*ExpressionHeap,  !*SymbolTable, !*ErrorAdmin )
partitionateAndLiftFunctions ranges main_dcl_module_n predef_symbols_for_transform fun_defs modules var_heap symbol_heap symbol_table error
	#! max_fun_nr = size fun_defs
	# partitioning_info = {	pi_var_heap = var_heap, pi_symbol_heap = symbol_heap, pi_symbol_table = symbol_table,
									pi_error = error, pi_deps = [], pi_next_num = 0, pi_next_group = 0, pi_groups = [] }
	  (fun_defs, modules, {pi_groups, pi_symbol_table, pi_var_heap, pi_symbol_heap, pi_error})
	  		= foldSt (partitionate_functions main_dcl_module_n max_fun_nr) ranges (fun_defs, modules, partitioning_info)
	# (reversed_pi_groups,fun_defs) = remove_macros_from_groups_and_reverse pi_groups fun_defs []
	# groups = { {group_members = group} \\ group <- reversed_pi_groups }
//	# groups = { {group_members = group} \\ group <- reverse pi_groups }
	= (groups, fun_defs, modules, pi_var_heap, pi_symbol_heap, pi_symbol_table, pi_error)
where
	remove_macros_from_groups_and_reverse [group:groups] fun_defs result_groups
		# (group,fun_defs) = remove_macros_from_group group fun_defs
		= case group of
			[]	-> remove_macros_from_groups_and_reverse groups fun_defs result_groups
			_	-> remove_macros_from_groups_and_reverse groups fun_defs [group:result_groups]
	where
		remove_macros_from_group [fun:funs] fun_defs
			# (funs,fun_defs)=remove_macros_from_group funs fun_defs

			| fun_defs.[fun].fun_info.fi_group_index<NoIndex
				= (funs,fun_defs)

			= ([fun:funs],fun_defs)
		remove_macros_from_group [] fun_defs
			= ([],fun_defs);
	remove_macros_from_groups_and_reverse [] fun_defs result_groups
		= (result_groups,fun_defs);

	partitionate_functions mod_index max_fun_nr {ir_from,ir_to} funs_modules_pi
		= iFoldSt (partitionate_global_function mod_index max_fun_nr) ir_from ir_to funs_modules_pi
		
	partitionate_global_function mod_index max_fun_nr fun_index funs_modules_pi
		# (_, funs_modules_pi) = partitionate_function mod_index max_fun_nr fun_index funs_modules_pi
		= funs_modules_pi

	partitionate_function mod_index max_fun_nr fun_index (fun_defs, modules, pi)
//		# fun_index = trace ("partitionate_function: "+++toString fun_index+++" ") fun_index
		# (fun_def, fun_defs) = fun_defs![fun_index]
		= case fun_def.fun_body of
			CheckedBody body
				# fun_number = pi.pi_next_num
				# (min_dep, funs_modules_pi) = foldSt (visit_function mod_index max_fun_nr) fun_def.fun_info.fi_calls
						(max_fun_nr, ({ fun_defs & [fun_index] = { fun_def & fun_body = PartioningFunction body fun_number }}, modules,
							{ pi & pi_next_num = inc fun_number, pi_deps = [fun_index : pi.pi_deps] }))
				-> try_to_close_group mod_index max_fun_nr fun_index fun_number min_dep funs_modules_pi
			PartioningFunction _ fun_number
				-> (fun_number, (fun_defs, modules, pi))
			TransformedBody _
				| fun_def.fun_info.fi_group_index == NoIndex
					# (fun_defs, pi) =  add_called_macros fun_def.fun_info.fi_calls (fun_defs, pi)
					-> (max_fun_nr, ({ fun_defs & [fun_index] = {fun_def & fun_info.fi_group_index = pi.pi_next_group }}, modules,
//					-> (max_fun_nr, ({ fun_defs & [fun_index] = {fun_def & fun_info.fi_group_index = -2-pi.pi_next_group }}, modules,
							{pi & pi_next_group = inc pi.pi_next_group, pi_groups = [ [fun_index] : pi.pi_groups]}
//							{pi & pi_next_group = pi.pi_next_group}
							))
					-> (max_fun_nr, (fun_defs, modules, pi))
			
	visit_function mod_index max_fun_nr {fc_index} (min_dep, funs_modules_pi)
		# (next_min, funs_modules_pi) = partitionate_function mod_index max_fun_nr fc_index funs_modules_pi
		= (min next_min min_dep, funs_modules_pi)

	try_to_close_group mod_index max_fun_nr fun_index fun_number min_dep (fun_defs, modules,
					pi=:{pi_symbol_table, pi_var_heap, pi_symbol_heap, pi_deps, pi_groups, pi_next_group, pi_error})
		| fun_number <= min_dep
			# (pi_deps, functions_in_group, macros_in_group, fun_defs)
					= close_group fun_index pi_deps [] [] max_fun_nr pi_next_group fun_defs
			  {ls_x={x_fun_defs=fun_defs}, ls_var_heap=pi_var_heap, ls_expr_heap=pi_symbol_heap}
			  		= liftFunctions (functions_in_group ++ macros_in_group) pi_next_group main_dcl_module_n fun_defs pi_var_heap pi_symbol_heap		  
			# es
			  		= expand_macros_in_group macros_in_group
			  			{	es_symbol_table = pi_symbol_table, es_var_heap = pi_var_heap, es_symbol_heap = pi_symbol_heap,
			  				es_fun_defs=fun_defs, es_main_dcl_module_n=mod_index, es_dcl_modules=modules, es_new_fun_def_numbers=[],
			  				es_expand_in_imp_module=False, // function expand_macros fills in correct value
				  			es_error = pi_error }
			# {es_symbol_table, es_var_heap, es_symbol_heap, es_error,es_dcl_modules,es_fun_defs,es_new_fun_def_numbers}
			  		= expand_macros_in_group functions_in_group es
			# (n_fun_defs_after_expanding_macros,es_fun_defs) = usize es_fun_defs
			# (pi_next_group,es_fun_defs,functions_in_group,pi_groups)
				= add_new_macros_to_groups (reverse es_new_fun_def_numbers) n_fun_defs_after_expanding_macros pi_next_group es_fun_defs functions_in_group pi_groups
			= (max_fun_nr, (es_fun_defs, es_dcl_modules, { pi & pi_deps = pi_deps, pi_var_heap = es_var_heap,
						pi_symbol_table = es_symbol_table, pi_error = es_error, pi_symbol_heap = es_symbol_heap, 
						pi_next_group = inc pi_next_group, 
						pi_groups = [ functions_in_group ++ macros_in_group : pi_groups ] }))
			= (min_dep, (fun_defs, modules, pi))
	where
		close_group fun_index [d:ds] functions_in_group macros_in_group nr_of_fun_defs group_number fun_defs
			# (fun_def, fun_defs) = fun_defs![d]
//			  fun_defs = { fun_defs & [d] = { fun_def & fun_info.fi_group_index = group_number }}
//			| fun_def.fun_kind == FK_Macro
			| case fun_def.fun_kind of FK_DefMacro->True ; FK_ImpMacro->True; _ -> False
				# fun_defs = { fun_defs & [d] = { fun_def & fun_info.fi_group_index = -2-group_number }}
//				# fun_defs = { fun_defs & [d] = { fun_def & fun_info.fi_group_index = group_number }}
				# macros_in_group = [d : macros_in_group]
				| d == fun_index
					= (ds, functions_in_group, macros_in_group, fun_defs)
					= close_group fun_index ds functions_in_group macros_in_group nr_of_fun_defs group_number fun_defs
				# fun_defs = { fun_defs & [d] = { fun_def & fun_info.fi_group_index = group_number }}
				# functions_in_group = [d : functions_in_group]
				| d == fun_index
					= (ds, functions_in_group, macros_in_group, fun_defs)
					= close_group fun_index ds functions_in_group macros_in_group nr_of_fun_defs group_number fun_defs
		
		expand_macros_in_group group es
			= foldSt expand_macros group es

		expand_macros fun_index es
			# (fun_def,es) = es!es_fun_defs.[fun_index]
			  {fun_symb,fun_body = PartioningFunction body _, fun_info, fun_pos,fun_kind} = fun_def
		  	  identPos = newPosition fun_symb fun_pos
			# expand_in_imp_module=case fun_kind of FK_ImpFunction _->True; FK_ImpMacro->True; FK_ImpCaf->True; _ -> False
			  es={ es & es_expand_in_imp_module=expand_in_imp_module, es_error = setErrorAdmin identPos es.es_error }
			# (tb_args, tb_rhs, fi_local_vars, fi_calls, fun_info, es)
					= expandMacrosInBody fun_info.fi_calls body predef_symbols_for_transform fun_index es
			  fun_def = { fun_def & fun_body = TransformedBody { tb_args = tb_args, tb_rhs = tb_rhs},
			  			fun_info = { fun_info & fi_calls = fi_calls, fi_local_vars = fi_local_vars }}
			= {es & es_fun_defs.[fun_index] = fun_def }
	
	add_called_macros calls macro_defs_and_pi
		= foldSt add_called_macro calls macro_defs_and_pi
	where
		add_called_macro {fc_index} (macro_defs, pi)		
//			# fc_index = trace ("add_called_macro: "+++toString fc_index+++" ") fc_index
			# (macro_def, macro_defs) = macro_defs![fc_index]
			= case macro_def.fun_body of
				TransformedBody _
					| macro_def.fun_info.fi_group_index == NoIndex
						# (macro_defs, pi) = add_called_macros macro_def.fun_info.fi_calls (macro_defs, pi)
//						->	({ macro_defs & [fc_index] = {macro_def & fun_info.fi_group_index = pi.pi_next_group }},
//						# fc_index = trace ("add_called_macro2: "+++toString fc_index+++" ") fc_index
//						->	({ macro_defs & [fc_index] = {macro_def & fun_info.fi_group_index = -2-pi.pi_next_group }},
						->	({ macro_defs & [fc_index] = {macro_def & fun_info.fi_group_index = pi.pi_next_group }},
								{pi & pi_next_group = inc pi.pi_next_group,pi_groups = [ [fc_index] : pi.pi_groups]}
//								{pi & pi_next_group = pi.pi_next_group}
								)
						-> (macro_defs, pi)

addFunctionCallsToSymbolTable calls fun_defs symbol_table
	= foldSt add_function_call_to_symbol_table calls ([], fun_defs, symbol_table)
where
	add_function_call_to_symbol_table fc=:{fc_index} (collected_calls, fun_defs, symbol_table)
		# ({fun_symb = { id_info }, fun_kind}, fun_defs) = fun_defs![fc_index]
//		| fun_kind == FK_Macro
		= case fun_kind of
			FK_DefMacro
				-> (collected_calls, fun_defs, symbol_table)
			FK_ImpMacro
				-> (collected_calls, fun_defs, symbol_table)
			_
				# (entry, symbol_table) = readPtr id_info symbol_table
				-> ([fc : collected_calls], fun_defs,
					symbol_table <:= (id_info, { ste_kind = STE_Called [fc_index], ste_index = NoIndex, ste_def_level = NotALevel, ste_previous = entry }))

removeFunctionCallsFromSymbolTable calls fun_defs symbol_table
	= foldSt remove_function_call_from_symbol_table calls (fun_defs, symbol_table)
where
	remove_function_call_from_symbol_table {fc_index} (fun_defs, symbol_table)
		# ({fun_symb = { id_info }}, fun_defs) = fun_defs![fc_index]
		  (entry, symbol_table) = readPtr id_info symbol_table
		= case entry.ste_kind of
			STE_Called indexes
				-> (fun_defs, symbol_table <:= (id_info, entry.ste_previous))
			_
				-> (fun_defs, symbol_table)

expandMacrosInBody :: [.FunCall] CheckedBody PredefSymbolsForTransform !Int *ExpandState -> ([FreeVar],Expression,[FreeVar],[FunCall],/* MV ... */ !FunInfo, /* ... MV */ .ExpandState);
expandMacrosInBody fi_calls {cb_args,cb_rhs} predef_symbols_for_transform es_current_fun_index es=:{es_symbol_heap,es_fun_defs}
// MV ...
	# (fun_def=:{fun_info},es_fun_defs)
		= es_fun_defs![es_current_fun_index]
	# (max_index,es_symbol_heap)
		= determine_amount_of_dynamics 0 fun_info.fi_dynamics es_symbol_heap 
	# (es=:{es_symbol_table,es_fun_defs})
		= { es & es_symbol_heap = es_symbol_heap, es_fun_defs = es_fun_defs } 
	# cos_used_dynamics
		= createArray (inc max_index) False // means not removed
// ... MV

	# (prev_calls, fun_defs, es_symbol_table)
			= addFunctionCallsToSymbolTable fi_calls es_fun_defs es_symbol_table
	  ([rhs:rhss], (all_calls, es) )
	  		= mapSt expandCheckedAlternative cb_rhs (prev_calls, { es & es_fun_defs=fun_defs, es_symbol_table = es_symbol_table })
	  (fun_defs, symbol_table)
	  		= removeFunctionCallsFromSymbolTable all_calls es.es_fun_defs es.es_symbol_table
	  ((merged_rhs, _), es_var_heap, es_symbol_heap, es_error)
	  		= mergeCases rhs rhss es.es_var_heap es.es_symbol_heap es.es_error
	  (new_rhs, new_args, local_vars, {cos_error, cos_var_heap, cos_symbol_heap /* MV ... */, cos_used_dynamics /* ... MV */})
	  		= determineVariablesAndRefCounts cb_args merged_rhs
	  				{ cos_error = es_error, cos_var_heap = es_var_heap, cos_symbol_heap = es_symbol_heap,
	  					cos_predef_symbols_for_transform = predef_symbols_for_transform, cos_used_dynamics = cos_used_dynamics }
	// MV ...
	# (changed,fi_dynamics,_,cos_symbol_heap)
		= foldSt remove_fi_dynamic fun_info.fi_dynamics (False,[],cos_used_dynamics,cos_symbol_heap)
	# fun_info
		= if changed { fun_info & fi_dynamics = fi_dynamics } fun_info
	// ... MV
	= (new_args, new_rhs, local_vars, all_calls, /* MV ... */ fun_info, /* ... MV */
		{ es & es_error = cos_error, es_var_heap = cos_var_heap, es_symbol_heap = cos_symbol_heap,
												es_fun_defs=fun_defs, es_symbol_table = symbol_table })
//		---> ("expandMacrosInBody", (cb_args, ca_rhs, '\n'), ("merged_rhs", merged_rhs, '\n'), ("new_rhs", new_args, local_vars, (new_rhs, '\n')))
// MV ...
where
	remove_fi_dynamic dyn_expr_ptr (changed,accu,cos_used_dynamics,cos_symbol_heap)
		# (expr_info,cos_symbol_heap)
			= readPtr dyn_expr_ptr cos_symbol_heap
		| not (isEI_Dynamic expr_info)
			= (changed,[dyn_expr_ptr:accu],cos_used_dynamics,cos_symbol_heap)
			
		# (EI_Dynamic _ id)
			= expr_info
		| cos_used_dynamics.[id]
			= (changed,[dyn_expr_ptr:accu],cos_used_dynamics,cos_symbol_heap)
	
			// unused
			= (True,accu,cos_used_dynamics,cos_symbol_heap)
	where
		isEI_Dynamic (EI_Dynamic _ _)	= True
		isEI_Dynamic _					= False

	determine_amount_of_dynamics max_index [] es_symbol_table
		= (max_index,es_symbol_table)
	determine_amount_of_dynamics max_index [expr_info_ptr:expr_info_ptrs] es_symbol_table
		# (expr_info,es_symbol_table)
			= readPtr expr_info_ptr es_symbol_table
		# (max_index,es_symbol_table)
			= case expr_info of
				EI_Dynamic _ id
					-> (max max_index id,es_symbol_table)
				EI_DynamicTypeWithVars _ _ expr_info_ptrs2
					-> determine_amount_of_dynamics max_index expr_info_ptrs2 es_symbol_table
				// EI_DynamicType _ expr_info_ptrs2
				//	-> determine_amount_of_dynamics max_index expr_info_ptrs2 es_symbol_table
		= determine_amount_of_dynamics max_index expr_info_ptrs es_symbol_table
// ... MV

expandCheckedAlternative {ca_rhs, ca_position} ei
	# (ca_rhs, ei) = expand ca_rhs ei
	= ((ca_rhs, ca_position), ei)

/*
cContainsFreeVars 	:== True
cContainsNoFreeVars :== False

cMacroIsCalled 		:== True
cNoMacroIsCalled 	:== False
*/

liftFunctions group group_index main_dcl_module_n fun_defs var_heap expr_heap
	# (contains_free_vars, lifted_function_called, fun_defs)
			= foldSt (add_free_vars_of_non_recursive_calls_to_function group_index) group (False, False, fun_defs)
	| contains_free_vars
		# fun_defs = iterateSt (add_free_vars_of_recursive_calls_to_functions group_index group) fun_defs
//		= lift_functions group fun_defs var_heap expr_heap
		= lift_functions group {ls_x={x_fun_defs=fun_defs,x_main_dcl_module_n=main_dcl_module_n},ls_var_heap=var_heap,ls_expr_heap=expr_heap}
	| lifted_function_called
		= lift_functions group {ls_x={x_fun_defs=fun_defs,x_main_dcl_module_n=main_dcl_module_n},ls_var_heap=var_heap,ls_expr_heap=expr_heap}
//		= (fun_defs, var_heap, expr_heap)
		= {ls_x={x_fun_defs=fun_defs,x_main_dcl_module_n=main_dcl_module_n},ls_var_heap=var_heap, ls_expr_heap=expr_heap}
where
	add_free_vars_of_non_recursive_calls_to_function group_index fun (contains_free_vars, lifted_function_called, fun_defs)
		# (fun_def=:{fun_info}, fun_defs) = fun_defs![fun]
		  { fi_free_vars,fi_def_level,fi_calls } = fun_info
		  (lifted_function_called, fi_free_vars, fun_defs)
				= foldSt (add_free_vars_of_non_recursive_call fi_def_level group_index) fi_calls (lifted_function_called, fi_free_vars, fun_defs)
		= (contains_free_vars || not (isEmpty fi_free_vars), lifted_function_called, 
			{ fun_defs & [fun] = { fun_def & fun_info = { fun_info & fi_free_vars = fi_free_vars }}})
	where
		add_free_vars_of_non_recursive_call fun_def_level group_index {fc_index} (lifted_function_called, free_vars, fun_defs)
			# ({fun_info = {fi_free_vars,fi_group_index}}, fun_defs) = fun_defs![fc_index]
//			| fi_group_index == group_index
			| if (fi_group_index>=NoIndex) (fi_group_index==group_index) (-2-fi_group_index==group_index)
				= (lifted_function_called, free_vars, fun_defs)
				| isEmpty fi_free_vars
					= (lifted_function_called, free_vars, fun_defs)
					# (free_vars_added, free_vars) = add_free_variables fun_def_level fi_free_vars (False, free_vars)
					= (True, free_vars, fun_defs)
	
	add_free_vars_of_recursive_calls_to_functions group_index group fun_defs
		= foldSt (add_free_vars_of_recursive_calls_to_function group_index) group (False, fun_defs)

	add_free_vars_of_recursive_calls_to_function group_index fun (free_vars_added, fun_defs)
		# (fun_def=:{fun_info}, fun_defs) = fun_defs![fun]
		  { fi_free_vars,fi_def_level,fi_calls } = fun_info
		  (free_vars_added, fi_free_vars, fun_defs)
				= foldSt (add_free_vars_of_recursive_call fi_def_level group_index) fi_calls (free_vars_added, fi_free_vars, fun_defs)
		= (free_vars_added, { fun_defs & [fun] = { fun_def & fun_info = { fun_info & fi_free_vars = fi_free_vars }}})
	where
		add_free_vars_of_recursive_call fun_def_level group_index {fc_index} (free_vars_added, free_vars, fun_defs)
			# ({fun_info = {fi_free_vars,fi_group_index}}, fun_defs) = fun_defs![fc_index]
//			| fi_group_index == group_index
			| if (fi_group_index>=NoIndex) (fi_group_index==group_index) (-2-fi_group_index==group_index)
				# (free_vars_added, free_vars) = add_free_variables fun_def_level fi_free_vars (free_vars_added, free_vars)
				= (free_vars_added, free_vars, fun_defs)
				= (free_vars_added, free_vars, fun_defs)

	add_free_variables fun_level new_vars (free_vars_added, free_vars)
		= add_free_global_variables (skip_local_variables fun_level new_vars) (free_vars_added, free_vars)
	where
		skip_local_variables level vars=:[{fv_def_level}:rest_vars]
			| fv_def_level > level
				= skip_local_variables level rest_vars
				= vars
		skip_local_variables _ []
			= []

		add_free_global_variables []  (free_vars_added, free_vars)
			= (free_vars_added, free_vars)
		add_free_global_variables free_vars (free_vars_added, [])
			= (True, free_vars)
		add_free_global_variables [var:vars] (free_vars_added, free_vars)
			# (free_var_added, free_vars) = newFreeVariable var free_vars
			= add_free_global_variables vars (free_var_added || free_vars_added, free_vars)

//	lift_functions group fun_defs var_heap expr_heap
//		= foldSt lift_function group (fun_defs, var_heap, expr_heap)
	lift_functions group lift_state
		= foldSt lift_function group lift_state
	where
//		lift_function fun (fun_defs=:{[fun] = fun_def}, var_heap, expr_heap)
		lift_function fun {ls_x=ls_x=:{x_fun_defs=fun_defs=:{[fun] = fun_def}}, ls_var_heap=var_heap, ls_expr_heap=expr_heap}
			# {fi_free_vars} = fun_def.fun_info
			  fun_lifted = length fi_free_vars
			  (PartioningFunction {cb_args,cb_rhs} fun_number) = fun_def.fun_body
			  (cb_args, var_heap) = add_lifted_args fi_free_vars cb_args var_heap
//			  (cb_rhs, {ls_fun_defs,ls_var_heap,ls_expr_heap}) = lift cb_rhs { ls_fun_defs = fun_defs, ls_var_heap = var_heap, ls_expr_heap = expr_heap }
			  (cb_rhs, {ls_x,ls_var_heap,ls_expr_heap}) = lift cb_rhs { ls_x={ls_x & x_fun_defs = fun_defs}, ls_var_heap = var_heap, ls_expr_heap = expr_heap }
			  ls_var_heap = remove_lifted_args fi_free_vars ls_var_heap
			  ls_fun_defs = ls_x.x_fun_defs
			  ls_fun_defs = { ls_fun_defs & [fun] = { fun_def & fun_lifted = fun_lifted, fun_body = PartioningFunction {cb_args = cb_args, cb_rhs = cb_rhs} fun_number}}
//			= (ls_fun_defs, ls_var_heap, ls_expr_heap)
			= {ls_x={ls_x & x_fun_defs=ls_fun_defs}, ls_var_heap=ls_var_heap, ls_expr_heap= ls_expr_heap}
//				 ---> ("lift_function", fun_def.fun_symb, fi_free_vars, cb_args, cb_rhs)

		remove_lifted_args vars var_heap
			= foldl (\var_heap {fv_name,fv_info_ptr} -> writePtr fv_info_ptr VI_Empty var_heap) var_heap vars
	
		add_lifted_args [lifted_arg=:{fv_name,fv_info_ptr} : lifted_args] args var_heap
			# (new_info_ptr, var_heap) = newPtr VI_Empty var_heap
			  args = [{ lifted_arg & fv_info_ptr = new_info_ptr } : args ]
			= add_lifted_args lifted_args args (writePtr fv_info_ptr (VI_LiftedVariable new_info_ptr) var_heap)
		add_lifted_args [] args var_heap
			= (args, var_heap)

::	ExpandInfo :== (![FunCall], !.ExpandState)

::	ExpandState =
	{	es_symbol_table	:: !.SymbolTable
	,	es_var_heap		:: !.VarHeap
	,	es_symbol_heap 	:: !.ExpressionHeap
	,	es_error 		:: !.ErrorAdmin,
		es_fun_defs :: !.{#FunDef},
		es_main_dcl_module_n :: !Int,
		es_dcl_modules :: !.{# DclModule},
		es_expand_in_imp_module :: !Bool,
		es_new_fun_def_numbers :: ![Int]
	}

class expand a :: !a !*ExpandInfo -> (!a, !*ExpandInfo)

instance expand Expression
where
	expand (App app=:{app_symb = symb=:{symb_arity, symb_kind = SK_Macro {glob_object,glob_module}}, app_args}) ei
		# (app_args, (calls, es)) = expand app_args ei
		# (macro, es) = es!es_fun_defs.[glob_object]
		#! macro_group_index=macro.fun_info.fi_group_index
		# es = {es & es_fun_defs.[glob_object].fun_info.fi_group_index= if (macro_group_index>NoIndex) (-2-macro_group_index) macro_group_index}
		| macro.fun_arity == symb_arity			
			= unfoldMacro macro app_args (calls, es)

			# macro = {macro & fun_info.fi_group_index=if (macro_group_index<NoIndex) (-2-macro_group_index) macro_group_index}
			#! new_function_index = size es.es_fun_defs
			# copied_local_functions = Yes { copied_local_functions=[],used_copied_local_functions=[],new_copied_local_functions=[],next_local_function_n=new_function_index+1}

			# (macro,new_functions,local_macro_functions,es) = copy_macro_and_local_functions macro copied_local_functions es			
//			# new_function_index=trace ("new_function_index: "+++toString new_function_index+++"\n") new_function_index;
			# macro={macro & fun_index=new_function_index}
			# last_function_index = case local_macro_functions of (Yes {next_local_function_n}) -> next_local_function_n-1
			# es = add_new_fun_defs [({old_function_n=glob_object,new_function_n=new_function_index},macro):new_functions] new_function_index last_function_index es
				with
					add_new_fun_defs new_functions new_function_index last_function_index es=:{es_fun_defs,es_new_fun_def_numbers}
						# new_fun_defs = new_fun_defs
							with
								new_fun_defs :: *{!FunDef}
								new_fun_defs => {fun_def \\ (_,fun_def)<-new_functions}
						# es_fun_defs = {if (i<new_function_index) es_fun_defs.[i] new_fun_defs.[i-new_function_index] \\ i<-[0..last_function_index]} // inefficient
						= {es & es_fun_defs=es_fun_defs,es_new_fun_def_numbers=[new_function_index:es_new_fun_def_numbers]}

			# (calls, es_symbol_table) = examineFunctionCall macro.fun_symb {fc_index = new_function_index, fc_level = NotALevel} (calls, es.es_symbol_table)
			# app = App { app & app_symb = { symb & symb_kind = SK_LocalMacroFunction new_function_index }, app_args = app_args }

/*			| macro.fun_info.fi_group_index>NoIndex
				# macro = {macro & fun_info.fi_group_index= -2-macro.fun_info.fi_group_index}
				# es= {es & es_fun_defs.[new_function_index]=macro}
				= (app, (calls, { es & es_symbol_table = es_symbol_table }))
*/
			= (app, (calls, { es & es_symbol_table = es_symbol_table }))

/*
			# (calls, es_symbol_table) = examineFunctionCall macro.fun_symb {fc_index = glob_object, fc_level = NotALevel} (calls, es.es_symbol_table)
			# app = App { app & app_symb = { symb & symb_kind = SK_Function {glob_object = glob_object, glob_module = glob_module} }, app_args = app_args }
			| macro.fun_info.fi_group_index<NoIndex
				# macro = {macro & fun_info.fi_group_index= -2-macro.fun_info.fi_group_index}
				# es= {es & es_fun_defs.[glob_object]=macro}
				= (app, (calls, { es & es_symbol_table = es_symbol_table }))
				= (app, (calls, { es & es_symbol_table = es_symbol_table }))
*/
	expand (App app=:{app_args}) ei
		# (app_args, ei) = expand app_args ei
		= (App { app & app_args = app_args }, ei)
	expand (expr @ exprs) ei
		# ((expr,exprs), ei) = expand (expr,exprs) ei
		= (expr @ exprs, ei)
	expand (Let lad=:{let_strict_binds, let_lazy_binds, let_expr}) ei
		# (let_strict_binds, ei) = expand let_strict_binds ei
		# (let_lazy_binds, ei) = expand let_lazy_binds ei
		# (let_expr, ei) = expand let_expr ei
		= (Let {lad & let_expr = let_expr, let_strict_binds = let_strict_binds, let_lazy_binds = let_lazy_binds}, ei)
	expand (Case case_expr) ei
		# (case_expr, ei) = expand case_expr ei
		= (Case case_expr, ei)
	expand (Selection is_unique expr selectors) ei
		# ((expr, selectors), ei) = expand (expr, selectors) ei
		= (Selection is_unique expr selectors, ei)
	expand (Update expr1 selectors expr2) ei
		# (((expr1, expr2), selectors), ei) = expand ((expr1, expr2), selectors) ei
		= (Update expr1 selectors expr2, ei)
	expand (RecordUpdate cons_symbol expression expressions) ei
		# ((expression, expressions), ei) = expand (expression, expressions) ei
		= (RecordUpdate cons_symbol expression expressions, ei)
	expand (TupleSelect symbol argn_nr expr) ei
		# (expr, ei) = expand expr ei
		= (TupleSelect symbol argn_nr expr, ei)
/*	expand (Lambda vars expr) ei
		# (expr, ei) = expand expr ei
		= (Lambda vars expr, ei)
*/	expand (MatchExpr opt_tuple cons_symb expr) ei
		# (expr, ei) = expand expr ei
		= (MatchExpr opt_tuple cons_symb expr, ei)
	expand expr ei
		= (expr, ei)

instance expand Selection
where
	expand (ArraySelection array_select expr_ptr index_expr) ei
		# (index_expr, ei) = expand index_expr ei
		= (ArraySelection array_select expr_ptr index_expr, ei)
	expand record_selection ei
		= (record_selection, ei)

instance expand LetBind
where
	expand bind=:{lb_src} ei
		# (lb_src, ei) = expand lb_src ei
		= ({ bind & lb_src = lb_src }, ei)

instance expand (Bind a b) | expand a
where
	expand bind=:{bind_src} ei
		# (bind_src, ei) = expand bind_src ei
		= ({ bind & bind_src = bind_src }, ei)

instance expand Case
where
	expand kees=:{ case_expr,case_guards,case_default } ei
		# ((case_expr,(case_guards,case_default)), ei) = expand (case_expr,(case_guards,case_default)) ei
		= ({ kees & case_expr = case_expr,case_guards = case_guards, case_default = case_default }, ei)

instance expand CasePatterns
where
	expand (AlgebraicPatterns type patterns) ei
		# (patterns, ei) = expand patterns ei
		= (AlgebraicPatterns type patterns, ei) 
	expand (BasicPatterns type patterns) ei
		# (patterns, ei) = expand patterns ei
		= (BasicPatterns type patterns, ei) 
	expand (DynamicPatterns patterns) ei
		# (patterns, ei) = expand patterns ei
		= (DynamicPatterns patterns, ei) 

instance expand AlgebraicPattern
where
	expand alg_pattern=:{ap_expr} ei
		# (ap_expr, ei) = expand ap_expr ei
		= ({ alg_pattern & ap_expr = ap_expr }, ei)

instance expand BasicPattern
where
	expand bas_pattern=:{bp_expr} ei
		# (bp_expr, ei) = expand bp_expr ei
		= ({ bas_pattern & bp_expr = bp_expr }, ei)

instance expand DynamicPattern
where
	expand dyn_pattern=:{dp_rhs} ei
		# (dp_rhs, ei) = expand dp_rhs ei
		= ({ dyn_pattern & dp_rhs = dp_rhs }, ei)

instance expand [a] | expand a
where
	expand [x:xs] ei
		# (x, ei) = expand x ei
		  (xs, ei) = expand xs ei
		= ([x:xs], ei)
	expand [] ei
		= ([], ei)

instance expand (a,b) | expand a & expand b
where
	expand (x,y) ei
		# (x, ei) = expand x ei
		  (y, ei) = expand y ei
		= ((x,y), ei)

instance expand (Optional a) | expand a
where
	expand (Yes x) ei
		# (x, ei) = expand x ei
		= (Yes x, ei)
	expand no ei
		= (no, ei)

::	CollectState =
	{	cos_var_heap	:: !.VarHeap
	,	cos_symbol_heap :: !.ExpressionHeap
	,	cos_error		:: !.ErrorAdmin
	,	cos_predef_symbols_for_transform :: !PredefSymbolsForTransform
	,	cos_used_dynamics	:: !.{#Bool}
	}

determineVariablesAndRefCounts :: ![FreeVar] !Expression !*CollectState -> (!Expression , ![FreeVar], ![FreeVar], !*CollectState)
determineVariablesAndRefCounts free_vars expr cos=:{cos_var_heap}
	# (expr, local_vars, cos) = collectVariables expr [] { cos & cos_var_heap = clearCount free_vars cIsAGlobalVar cos_var_heap }
	  (free_vars, cos_var_heap) = retrieveRefCounts free_vars cos.cos_var_heap
	  (local_vars, cos_var_heap) = retrieveRefCounts local_vars cos_var_heap
	= (expr, free_vars, local_vars, { cos & cos_var_heap = cos_var_heap })

retrieveRefCounts free_vars var_heap
	= mapSt retrieveRefCount free_vars var_heap

retrieveRefCount :: FreeVar *VarHeap -> (!FreeVar,!.VarHeap)
retrieveRefCount fv=:{fv_info_ptr} var_heap
	# (VI_Count count _, var_heap) = readPtr fv_info_ptr var_heap
	= ({ fv & fv_count = count }, var_heap)

/*
	'clearCount' initialises the 'fv_info_ptr' field of each 'FreeVar'
*/

class clearCount a :: !a !Bool !*VarHeap -> *VarHeap

instance clearCount [a] | clearCount a
where
	clearCount [x:xs] locality var_heap
		= clearCount x locality (clearCount xs locality var_heap)
	clearCount [] locality var_heap
		= var_heap

instance clearCount LetBind
where
	clearCount bind=:{lb_dst} locality var_heap
		= clearCount lb_dst locality var_heap

instance clearCount FreeVar
where
	clearCount{fv_info_ptr} locality var_heap
		= var_heap <:= (fv_info_ptr, VI_Count 0 locality)

/*
	In 'collectVariables' all local variables are collected. Moreover the reference counts
	of the local as well as of the global variables are determined. Aliases and unreachable 
	bindings introduced in a 'let' are removed.
*/	

class collectVariables a :: !a ![FreeVar] !*CollectState -> !(!a, ![FreeVar],!*CollectState)

cContainsACycle		:== True
cContainsNoCycle	:== False

instance collectVariables Expression
where
	collectVariables (Var var) free_vars cos
		# (var, free_vars, cos) = collectVariables var free_vars cos
		= (Var var, free_vars, cos)
	/* optimize && and || */
	collectVariables (App app=:{app_symb={symb_kind=SK_Function {glob_object,glob_module}},app_args}) free_vars cos=:{cos_predef_symbols_for_transform={predef_and,predef_or}}
		# ([e1,e2:_], free_vars, cos) = collectVariables app_args free_vars cos
		| glob_object==predef_and.pds_def && glob_module==predef_and.pds_module && two_args app_args
			# (kase,cos) = if_expression e1 e2 (BasicExpr (BVB False) BT_Bool) cos
			= (kase, free_vars, cos)
		| glob_object==predef_or.pds_def && glob_module==predef_or.pds_module && two_args app_args
			# (kase,cos) = if_expression e1 (BasicExpr (BVB True) BT_Bool) e2 cos
			= (kase, free_vars, cos)
		where
			if_expression :: Expression Expression Expression *CollectState -> (!Expression,!.CollectState);
			if_expression e1 e2 e3 cos
				# (new_info_ptr,symbol_heap) = newPtr EI_Empty cos.cos_symbol_heap
				# kase = Case {	case_expr=e1, case_guards=BasicPatterns BT_Bool [{bp_value=BVB True,bp_expr=e2,bp_position=NoPos}],
								case_default=Yes e3, case_ident=No, case_info_ptr=new_info_ptr, case_default_pos = NoPos,
// RWS ...
								case_explicit = False }
// ... RWS
				= (kase,{cos & cos_symbol_heap=symbol_heap});
			
			two_args [_,_]
				= True;
			two_args app_args
				= False;
	collectVariables (App app=:{app_args}) free_vars cos
		# (app_args, free_vars, cos) = collectVariables app_args free_vars cos
		= (App { app & app_args = app_args}, free_vars, cos)
	collectVariables (expr @ exprs) free_vars cos
		# ((expr, exprs), free_vars, cos) = collectVariables (expr, exprs) free_vars cos
		= (expr @ exprs, free_vars, cos)
	collectVariables (Let lad=:{let_strict_binds, let_lazy_binds, let_expr}) free_vars cos=:{cos_var_heap}
		# cos_var_heap = determine_aliases let_strict_binds cos_var_heap
		  cos_var_heap = determine_aliases let_lazy_binds cos_var_heap
		  (is_cyclic_s, let_strict_binds, cos) 
		  		= detect_cycles_and_handle_alias_binds True let_strict_binds
		  											{ cos & cos_var_heap = cos_var_heap }
		  (is_cyclic_l, let_lazy_binds, cos) 
		  		= detect_cycles_and_handle_alias_binds False let_lazy_binds cos
		| is_cyclic_s || is_cyclic_l
			= (Let {lad & let_strict_binds = let_strict_binds, let_lazy_binds = let_lazy_binds }, free_vars,
					{ cos & cos_error = checkError "" "cyclic let definition" cos.cos_error})
//		| otherwise
			# (let_expr, free_vars, cos) = collectVariables let_expr free_vars cos
			  all_binds = mapAppend (\sb->(True, sb)) let_strict_binds [(False, lb) \\ lb<-let_lazy_binds]
			  (collected_binds, free_vars, cos) = collect_variables_in_binds all_binds [] free_vars cos
			  (let_strict_binds, let_lazy_binds) = split collected_binds
			| isEmpty let_strict_binds && isEmpty let_lazy_binds
				= (let_expr, free_vars, cos)
				= (Let {lad & let_expr = let_expr, let_strict_binds = let_strict_binds, let_lazy_binds = let_lazy_binds}, free_vars, cos)
		where

		/*	Set the 'var_info_field' of each  bound variable to either 'VI_Alias var' (if
			this variable is an alias for 'var') or to 'VI_Count 0 cIsALocalVar' to initialise
		   	the reference count info.
		*/	   
		   
			determine_aliases [{lb_dst={fv_info_ptr}, lb_src = Var var} : binds] var_heap
				= determine_aliases binds (writePtr fv_info_ptr (VI_Alias var) var_heap)
			determine_aliases [bind : binds] var_heap
				= determine_aliases binds (clearCount bind cIsALocalVar var_heap)
			determine_aliases [] var_heap
				= var_heap

			
		/*	Remove all aliases from the list of lazy 'let'-binds. Add a _dummyForStrictAlias
			function call for the strict aliases. Be careful with cycles! */
		
			detect_cycles_and_handle_alias_binds is_strict [] cos
				= (cContainsNoCycle, [], cos)
//			detect_cycles_and_handle_alias_binds is_strict [bind=:{bind_dst={fv_info_ptr}} : binds] cos
			detect_cycles_and_handle_alias_binds is_strict [bind=:{lb_dst={fv_info_ptr}} : binds] cos
				#! var_info = sreadPtr fv_info_ptr cos.cos_var_heap
				= case var_info of
					VI_Alias {var_info_ptr}
						| is_cyclic fv_info_ptr var_info_ptr cos.cos_var_heap
							-> (cContainsACycle, binds, cos)
						| is_strict
							# cos_var_heap = writePtr fv_info_ptr (VI_Count 0 cIsALocalVar) cos.cos_var_heap
							  (new_bind_src, cos) = add_dummy_id_for_strict_alias bind.lb_src 
							  								{ cos & cos_var_heap = cos_var_heap }
							  (is_cyclic, binds, cos) 
							  		= detect_cycles_and_handle_alias_binds is_strict binds cos
							-> (is_cyclic, [{ bind & lb_src = new_bind_src } : binds], cos)
						-> detect_cycles_and_handle_alias_binds is_strict binds cos
					_
						# (is_cyclic, binds, cos) = detect_cycles_and_handle_alias_binds is_strict binds cos
						-> (is_cyclic, [bind : binds], cos)
			where
				is_cyclic orig_info_ptr info_ptr var_heap
					| orig_info_ptr == info_ptr
						= True
						#! var_info = sreadPtr info_ptr var_heap
						= case var_info of
							VI_Alias {var_info_ptr}
								-> is_cyclic orig_info_ptr var_info_ptr var_heap
							_
								-> False
				
				add_dummy_id_for_strict_alias bind_src cos=:{cos_symbol_heap, cos_predef_symbols_for_transform}
					# (new_app_info_ptr, cos_symbol_heap) = newPtr EI_Empty cos_symbol_heap
					  {pds_ident, pds_module, pds_def} = cos_predef_symbols_for_transform.predef_alias_dummy
					  app_symb = { symb_name = pds_ident, 
					  				symb_kind = SK_Function {glob_module = pds_module, glob_object = pds_def},
									symb_arity = 1 }
					= (App { app_symb = app_symb, app_args = [bind_src], app_info_ptr = new_app_info_ptr },
						{ cos & cos_symbol_heap = cos_symbol_heap } )
								
		/*	Apply 'collectVariables' to the bound expressions (the 'bind_src' field of 'let'-bind) if
		    the corresponding bound variable (the 'bind_dst' field) has been used. This can be determined
		    by examining the reference count.
		*/

			collect_variables_in_binds binds collected_binds free_vars cos
				# (continue, binds, collected_binds, free_vars, cos) = examine_reachable_binds False binds collected_binds free_vars cos
				| continue
					= collect_variables_in_binds binds collected_binds free_vars cos
					= (collected_binds, free_vars, cos)
		
			examine_reachable_binds bind_found [bind=:(is_strict, {lb_dst=fv=:{fv_info_ptr},lb_src}) : binds] collected_binds free_vars cos
				# (bind_found, binds, collected_binds, free_vars, cos) = examine_reachable_binds bind_found binds collected_binds free_vars cos
				#! var_info = sreadPtr fv_info_ptr cos.cos_var_heap
				# (VI_Count count is_global) = var_info
				| count > 0
					# (lb_src, free_vars, cos) = collectVariables lb_src free_vars cos
					= (True, binds, [ (is_strict, { snd bind & lb_dst = { fv & fv_count = count }, lb_src = lb_src }) : collected_binds ], free_vars, cos)
					= (bind_found, [bind : binds], collected_binds, free_vars, cos)
			examine_reachable_binds bind_found [] collected_binds free_vars cos
				= (bind_found, [], collected_binds, free_vars, cos)

			split :: ![(Bool, x)] -> (![x], ![x])
			split []
				= ([], [])
			split [(p, x):xs]
				# (l, r) = split xs
				| p
					= ([x:l], r)
				= (l, [x:r])

	collectVariables (Case case_expr) free_vars cos
		# (case_expr, free_vars, cos) = collectVariables case_expr free_vars cos
		= (Case case_expr, free_vars, cos)
	collectVariables (Selection is_unique expr selectors) free_vars cos
		# ((expr, selectors), free_vars, cos) = collectVariables (expr, selectors) free_vars cos
		= (Selection is_unique expr selectors, free_vars, cos)
	collectVariables (Update expr1 selectors expr2) free_vars cos
		# (((expr1, expr2), selectors), free_vars, cos) = collectVariables ((expr1, expr2), selectors) free_vars cos
		= (Update expr1 selectors expr2, free_vars, cos)
	collectVariables (RecordUpdate cons_symbol expression expressions) free_vars cos
		# ((expression, expressions), free_vars, cos) = collectVariables (expression, expressions) free_vars cos
		= (RecordUpdate cons_symbol expression expressions, free_vars, cos)
	collectVariables (TupleSelect symbol argn_nr expr) free_vars cos
		# (expr, free_vars, cos) = collectVariables expr free_vars cos
		= (TupleSelect symbol argn_nr expr, free_vars, cos)
	collectVariables (MatchExpr opt_tuple cons_symb expr) free_vars cos
		# (expr, free_vars, cos) = collectVariables expr free_vars cos
		= (MatchExpr opt_tuple cons_symb expr, free_vars, cos)
	collectVariables (DynamicExpr dynamic_expr=:{dyn_expr /* MV ... */ , dyn_info_ptr /* ... MV */}) free_vars cos
		#! (dyn_expr, free_vars, cos /* MV ... */ =:{cos_symbol_heap} /* ... MV */) = collectVariables dyn_expr free_vars cos
// MV ...
		# (expr_info,cos_symbol_heap)
			= readPtr dyn_info_ptr cos_symbol_heap
		# cos
			= { cos & cos_symbol_heap = cos_symbol_heap }
		# cos
			= case expr_info of 
				EI_Dynamic _ id		->  { cos & cos_used_dynamics = { cos.cos_used_dynamics & [id] = True } }
				_					-> cos
// ... MV
		= (DynamicExpr {dynamic_expr & dyn_expr = dyn_expr}, free_vars, cos);
	collectVariables expr free_vars cos
		= (expr, free_vars, cos)

instance collectVariables Selection
where
	collectVariables (ArraySelection array_select expr_ptr index_expr) free_vars cos
		# (index_expr, free_vars, cos) = collectVariables index_expr free_vars cos
		= (ArraySelection array_select expr_ptr index_expr, free_vars, cos)
	collectVariables record_selection free_vars cos
		= (record_selection, free_vars, cos)


instance collectVariables [a] | collectVariables a
where
	collectVariables [x:xs] free_vars cos
		# (x, free_vars, cos) = collectVariables x free_vars cos
		# (xs, free_vars, cos) = collectVariables xs free_vars cos
		= ([x:xs], free_vars, cos)
	collectVariables [] free_vars cos
		= ([], free_vars, cos)

instance collectVariables (!a,!b) | collectVariables a & collectVariables b
where
	collectVariables (x,y) free_vars cos
		# (x, free_vars, cos) = collectVariables x free_vars cos
		# (y, free_vars, cos) = collectVariables y free_vars cos
		= ((x,y), free_vars, cos)

instance collectVariables (Optional a) | collectVariables a
where
	collectVariables (Yes x) free_vars cos
		# (x, free_vars, cos) = collectVariables x free_vars cos
		= (Yes x, free_vars, cos)
	collectVariables no free_vars cos
		= (no, free_vars, cos)

instance collectVariables (Bind a b) | collectVariables a where
	collectVariables bind=:{bind_src} free_vars cos
		# (bind_src, free_vars, cos) = collectVariables bind_src free_vars cos
		= ({bind & bind_src = bind_src}, free_vars, cos)

instance collectVariables Case
where
	collectVariables kees=:{ case_expr, case_guards, case_default } free_vars cos
		# (case_expr, free_vars, cos) = collectVariables case_expr free_vars cos
		# (case_guards, free_vars, cos) = collectVariables case_guards free_vars cos
		# (case_default, free_vars, cos) = collectVariables case_default free_vars cos
		=  ({ kees & case_expr = case_expr, case_guards = case_guards, case_default = case_default }, free_vars, cos)

instance collectVariables CasePatterns
where
	collectVariables (AlgebraicPatterns type patterns) free_vars cos
		# (patterns, free_vars, cos) = collectVariables patterns free_vars cos
		= (AlgebraicPatterns type patterns, free_vars, cos)
	collectVariables (BasicPatterns type patterns) free_vars cos
		# (patterns, free_vars, cos) = collectVariables patterns free_vars cos
		= (BasicPatterns type patterns, free_vars, cos)
	collectVariables (DynamicPatterns patterns) free_vars cos
		# (patterns, free_vars, cos) = collectVariables patterns free_vars cos
		= (DynamicPatterns patterns, free_vars, cos)


instance collectVariables AlgebraicPattern
where
	collectVariables pattern=:{ap_vars,ap_expr} free_vars cos
		# (ap_expr, free_vars, cos) = collectVariables ap_expr free_vars { cos & cos_var_heap = clearCount ap_vars cIsALocalVar cos.cos_var_heap}
		  (ap_vars, cos_var_heap) = retrieveRefCounts ap_vars cos.cos_var_heap
		= ({ pattern & ap_expr = ap_expr, ap_vars = ap_vars }, free_vars, { cos & cos_var_heap = cos_var_heap })
	
instance collectVariables BasicPattern
where
	collectVariables pattern=:{bp_expr} free_vars cos
		# (bp_expr, free_vars, cos) = collectVariables bp_expr free_vars cos
		= ({ pattern & bp_expr = bp_expr }, free_vars, cos)

instance collectVariables DynamicPattern
where
	collectVariables pattern=:{dp_var,dp_rhs} free_vars cos
		# (dp_rhs, free_vars, cos) = collectVariables dp_rhs free_vars { cos & cos_var_heap = clearCount dp_var cIsALocalVar cos.cos_var_heap}
		  (dp_var, cos_var_heap) = retrieveRefCount dp_var cos.cos_var_heap
		= ({ pattern & dp_rhs = dp_rhs, dp_var = dp_var }, free_vars, { cos & cos_var_heap = cos_var_heap })

instance collectVariables BoundVar
where
	collectVariables var=:{var_name,var_info_ptr,var_expr_ptr} free_vars cos=:{cos_var_heap}
		#! var_info = sreadPtr var_info_ptr cos_var_heap
		= case var_info of
			VI_Alias alias
				#  (original, free_vars, cos) = collectVariables alias free_vars cos
				-> ({ original & var_expr_ptr = var_expr_ptr }, free_vars, cos)
			VI_Count count is_global
				| count > 0 || is_global
					-> (var, free_vars, { cos & cos_var_heap = writePtr var_info_ptr (VI_Count (inc count) is_global) cos.cos_var_heap })
					-> (var, [{fv_name = var_name, fv_info_ptr = var_info_ptr, fv_def_level = NotALevel, fv_count = 0} : free_vars ],
								{ cos & cos_var_heap = writePtr var_info_ptr (VI_Count 1 is_global) cos.cos_var_heap })
			_
				-> abort "collectVariables [BoundVar] (transform, 1227)" // <<- (var_info ---> (var_name, ptrToInt var_info_ptr))

instance <<< (Ptr a)
where
	(<<<) file p = file <<< ptrToInt p

instance <<< FunCall
where
	(<<<) file {fc_index} = file <<< fc_index

instance <<< VarInfo
  where
	(<<<) file (VI_Expression expr) = file <<< expr
	(<<<) file vi					= file <<< "VI??"
