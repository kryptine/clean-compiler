implementation module transform

import syntax, check, StdCompare, utilities, RWSDebug

::	LiftState =
	{	ls_var_heap		:: !.VarHeap
	,	ls_fun_defs		:: !.{#FunDef}
	,	ls_expr_heap	:: !.ExpressionHeap
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
	lift (Lambda vars expr) ls
		# (expr, ls) = lift expr ls
		= (Lambda vars expr, ls)
	lift (MatchExpr opt_tuple cons_symb expr) ls
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
		| glob_module == cIclModIndex
			#! fun_def = ls.ls_fun_defs.[glob_object]
			# {fun_info={fi_free_vars}} = fun_def
			  fun_lifted = length fi_free_vars
			| fun_lifted > 0
				# (app_args, ls_var_heap, ls_expr_heap) = add_free_variables fi_free_vars app_args ls.ls_var_heap ls.ls_expr_heap
				= ({ app & app_args = app_args, app_symb = { app_symbol & symb_arity = symb_arity + fun_lifted }},
						{ ls & ls_var_heap = ls_var_heap, ls_expr_heap = ls_expr_heap })
				= ({ app & app_args = app_args }, ls)
			= ({ app & app_args = app_args }, ls)
	where
		add_free_variables :: ![FreeVar] ![Expression] !u:VarHeap !*ExpressionHeap -> (![Expression],!u:VarHeap,!*ExpressionHeap)
		add_free_variables [] app_args var_heap expr_heap
			= (app_args, var_heap, expr_heap)
		add_free_variables [{fv_name, fv_info_ptr} : free_vars] app_args var_heap expr_heap
			#! var_info = sreadPtr fv_info_ptr var_heap
			= case var_info of
				VI_LiftedVariable var_info_ptr
				 	# (var_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
					-> add_free_variables free_vars [Var { var_name = fv_name, var_info_ptr = var_info_ptr, var_expr_ptr = var_expr_ptr } : app_args]
							var_heap expr_heap
				_
				 	# (var_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
					-> add_free_variables free_vars [Var { var_name = fv_name, var_info_ptr = fv_info_ptr, var_expr_ptr = var_expr_ptr } : app_args]
							var_heap expr_heap

	lift app=:{app_args} ls
		# (app_args, ls) = lift app_args ls
		= ({ app & app_args = app_args }, ls)

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

::	UnfoldState =
	{	us_var_heap				:: !.VarHeap
	,	us_symbol_heap			:: !.ExpressionHeap
	,	us_opt_type_heaps		:: !.Optional .TypeHeaps
	,	us_cleanup_info			:: ![ExprInfoPtr]
	,	us_handle_aci_free_vars	:: !AciFreeVarHandleMode
	}
	
:: AciFreeVarHandleMode = LeaveThem | RemoveThem | SubstituteThem

class unfold a :: !a !*UnfoldState -> (!a, !*UnfoldState)

instance unfold [a] | unfold a
where
	unfold l us = mapSt unfold l us

instance unfold (a,b) | unfold a & unfold b
where
	unfold t us = app2St (unfold,unfold) t us

instance unfold (Optional a) | unfold a
where
	unfold (Yes x) us
		# (x, us) = unfold x us
		= (Yes x, us)
	unfold no us
		= (no, us)

unfoldVariable :: !BoundVar !*UnfoldState -> (!Expression, !*UnfoldState)
unfoldVariable var=:{var_name,var_info_ptr} us
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
			-> (App { app_symb = app_symb, app_args = app_args, app_info_ptr = new_info_ptr },
				{ us & us_opt_type_heaps = us_opt_type_heaps, us_symbol_heap = us_symbol_heap })
		_
			-> (Var var, us)
  where
	substitute_class_types class_types no=:No
		= (class_types, no)
	substitute_class_types class_types (Yes type_heaps)
		# (new_class_types, type_heaps) = substitute class_types type_heaps
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

instance unfold Expression
where
	unfold (Var var) us
		= unfoldVariable var us
	unfold (App app) us
		# (app, us) = unfold app us
		= (App app, us)
	unfold (expr @ exprs) us
		# ((expr,exprs), us) = unfold (expr,exprs) us
		= (expr @ exprs, us)
	unfold (Let lad) us
		# (lad, us) = unfold lad us
		= (Let lad, us)
	unfold (Case case_expr) us
		# (case_expr, us) = unfold case_expr us
		= (Case case_expr, us)
	unfold (Selection is_unique expr selectors) us
		# ((expr, selectors), us) = unfold (expr, selectors) us
		= (Selection is_unique expr selectors, us)
	unfold (Update expr1 selectors expr2) us
		# (((expr1, expr2), selectors), us) = unfold ((expr1, expr2), selectors) us
		= (Update expr1 selectors expr2, us)
	unfold (RecordUpdate cons_symbol expression expressions) us
		# ((expression, expressions), us) = unfold (expression, expressions) us
		= (RecordUpdate cons_symbol expression expressions, us)
	unfold (TupleSelect symbol argn_nr expr) us
		# (expr, us) = unfold expr us
		= (TupleSelect symbol argn_nr expr, us)
	unfold (Lambda vars expr) us
		# (expr, us) = unfold expr us
		= (Lambda vars expr, us)
	unfold (MatchExpr opt_tuple cons_symb expr) us
		# (expr, us) = unfold expr us
		= (MatchExpr opt_tuple cons_symb expr, us)
	unfold expr us
		= (expr, us)

/* Sjaak ... */
instance unfold Selection
where
	unfold (ArraySelection array_select expr_ptr index_expr) us=:{us_symbol_heap}
		# (new_ptr, us_symbol_heap) = newPtr EI_Empty us_symbol_heap
		  (index_expr, us) = unfold index_expr { us & us_symbol_heap = us_symbol_heap}
		= (ArraySelection array_select new_ptr index_expr, us)
	unfold (DictionarySelection var selectors expr_ptr index_expr) us=:{us_symbol_heap}
		# (new_ptr, us_symbol_heap) = newPtr EI_Empty us_symbol_heap
		  (index_expr, us) = unfold index_expr { us & us_symbol_heap = us_symbol_heap}
		  (var_expr, us) = unfoldVariable var us
		= case var_expr of 
			App {app_symb={symb_kind= SK_Constructor _ }, app_args}
				# [RecordSelection _ field_index:_] = selectors
				  (App { app_symb = {symb_name, symb_kind = SK_Function array_select}}) =  app_args !! field_index
				-> (ArraySelection { array_select & glob_object = { ds_ident = symb_name, ds_arity = 2, ds_index = array_select.glob_object}}
							new_ptr index_expr, us)
			Var var
				-> (DictionarySelection var selectors new_ptr index_expr, us)
	unfold record_selection ls
		= (record_selection, ls)
/* ... Sjaak */

instance unfold FreeVar
where
	unfold fv=:{fv_info_ptr,fv_name} us=:{us_var_heap}
		# (new_info_ptr, us_var_heap) = newPtr VI_Empty us_var_heap
		= ({ fv & fv_info_ptr = new_info_ptr }, { us & us_var_heap = writePtr fv_info_ptr (VI_Variable fv_name new_info_ptr) us_var_heap })

instance unfold App
where
	unfold app=:{app_symb, app_args, app_info_ptr} us
		# (new_info_ptr, us)
				= case is_function_or_macro app_symb.symb_kind of
					True	# (new_ptr, us_symbol_heap) = newPtr EI_Empty us.us_symbol_heap
							-> (new_ptr, { us & us_symbol_heap = us_symbol_heap })
					_		-> case (app_symb.symb_kind, isNilPtr app_info_ptr) of
								(SK_Constructor _, False)
									# (app_info, us_symbol_heap) = readPtr app_info_ptr us.us_symbol_heap
									  (new_app_info, us_opt_type_heaps) = substitute_EI_DictionaryType app_info us.us_opt_type_heaps
									  (new_ptr, us_symbol_heap) = newPtr new_app_info us_symbol_heap
									-> (new_ptr, { us & us_symbol_heap = us_symbol_heap, us_opt_type_heaps = us_opt_type_heaps })
								_	-> (nilPtr, us)
		  (app_args, us) = unfold app_args us
		= ({ app & app_args = app_args, app_info_ptr = new_info_ptr}, us) 
	where
		is_function_or_macro (SK_Function _)
			= True
		is_function_or_macro (SK_Macro _)
			= True
		is_function_or_macro (SK_OverloadedFunction _)
			= True
		is_function_or_macro _
			= False

		substitute_EI_DictionaryType (EI_DictionaryType class_type) (Yes type_heaps)
			# (new_class_type, type_heaps) = substitute class_type type_heaps
			= (EI_DictionaryType new_class_type, Yes type_heaps)
		substitute_EI_DictionaryType x opt_type_heaps
			= (x, opt_type_heaps)

instance unfold (Bind a b) | unfold a
where
	unfold bind=:{bind_src} us
		# (bind_src, us) = unfold bind_src us
		= ({ bind & bind_src = bind_src }, us)

instance unfold Case
where
	unfold kees=:{ case_expr,case_guards,case_default,case_info_ptr} us=:{us_cleanup_info}
		# (old_case_info, us_symbol_heap) = readPtr case_info_ptr us.us_symbol_heap
		  (new_case_info, us_opt_type_heaps) = substitute_let_or_case_type old_case_info us.us_opt_type_heaps
		  (new_info_ptr, us_symbol_heap) = newPtr new_case_info us_symbol_heap
		  us_cleanup_info = case old_case_info of
								EI_Extended _ _	-> [new_info_ptr:us_cleanup_info]
								_				-> us_cleanup_info
		  us = { us & us_symbol_heap = us_symbol_heap, us_opt_type_heaps = us_opt_type_heaps, us_cleanup_info=us_cleanup_info }
		  ((case_guards,case_default), us) = unfold (case_guards,case_default) us
		  (case_expr, us) = update_active_case_info_and_unfold case_expr new_info_ptr us
		= ({ kees & case_expr = case_expr,case_guards = case_guards, case_default = case_default, case_info_ptr =  new_info_ptr}, us)
	where
		update_active_case_info_and_unfold case_expr=:(Var {var_info_ptr}) case_info_ptr us=:{us_handle_aci_free_vars}
			# (case_info, us_symbol_heap) = readPtr case_info_ptr us.us_symbol_heap
			  us = { us & us_symbol_heap = us_symbol_heap }
			= case case_info of
				EI_Extended (EEI_ActiveCase aci=:{aci_free_vars}) ei
					#!(new_aci_free_vars, us) = case us_handle_aci_free_vars of
													LeaveThem		-> (aci_free_vars, us)
													RemoveThem		-> (No, us)
													SubstituteThem	-> case aci_free_vars of
																		No		-> (No, us)
																		Yes fvs	# (fvs_subst, us) = mapSt unfoldBoundVar fvs us
																				-> (Yes fvs_subst, us)
					  (var_info, us_var_heap) = readPtr var_info_ptr us.us_var_heap
					  us = { us & us_var_heap = us_var_heap }
					-> case var_info of
						VI_Body fun_symb {tb_args, tb_rhs} new_aci_params
							# tb_args_ptrs = [ fv_info_ptr \\ {fv_info_ptr}<-tb_args ] 
							  (original_bindings, us_var_heap) = mapSt readPtr tb_args_ptrs us.us_var_heap
							  us_var_heap = fold2St bind tb_args_ptrs new_aci_params us_var_heap
							  (tb_rhs, us) = unfold tb_rhs { us & us_var_heap = us_var_heap }
							  us_var_heap = fold2St writePtr tb_args_ptrs original_bindings us.us_var_heap
							  new_aci = { aci & aci_params = new_aci_params, aci_opt_unfolder = Yes fun_symb, aci_free_vars = new_aci_free_vars }
							  new_eei = (EI_Extended (EEI_ActiveCase new_aci) ei)
							  us_symbol_heap = writePtr case_info_ptr new_eei us.us_symbol_heap
							-> (tb_rhs, { us & us_var_heap = us_var_heap, us_symbol_heap = us_symbol_heap })
						_	# new_eei = EI_Extended (EEI_ActiveCase { aci & aci_free_vars = new_aci_free_vars }) ei
							  us_symbol_heap = writePtr case_info_ptr new_eei us.us_symbol_heap
							-> unfold case_expr { us & us_symbol_heap = us_symbol_heap }
				_	-> unfold case_expr us	
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
			= unfold case_expr us

		unfoldBoundVar {var_info_ptr} us
			# (VI_Expression (Var act_var), us_var_heap) = readPtr var_info_ptr us.us_var_heap
			= (act_var, { us & us_var_heap = us_var_heap })


instance unfold Let
where
	unfold lad=:{let_strict_binds, let_lazy_binds, let_expr, let_info_ptr} us
		# (let_strict_binds, us) = copy_bound_vars let_strict_binds us
		# (let_lazy_binds, us) = copy_bound_vars let_lazy_binds us
		# (let_strict_binds, us) = unfold let_strict_binds us
		# (let_lazy_binds, us) = unfold let_lazy_binds us
		# (let_expr, us) = unfold let_expr us
		  (old_let_info, us_symbol_heap) = readPtr let_info_ptr us.us_symbol_heap
		  (new_let_info, us_opt_type_heaps) = substitute_let_or_case_type old_let_info us.us_opt_type_heaps
		  (new_info_ptr, us_symbol_heap) = newPtr new_let_info us_symbol_heap
		= ({lad & let_strict_binds = let_strict_binds, let_lazy_binds = let_lazy_binds, let_expr = let_expr, let_info_ptr = new_info_ptr},
			{ us & us_symbol_heap = us_symbol_heap, us_opt_type_heaps = us_opt_type_heaps })
		where
			copy_bound_vars [bind=:{bind_dst} : binds] us
				# (bind_dst, us) = unfold bind_dst us
				  (binds, us) = copy_bound_vars binds us
				= ([ {bind & bind_dst = bind_dst} : binds ], us)
			copy_bound_vars [] us
				= ([], us)

substitute_let_or_case_type	expr_info No
	= (expr_info, No)
substitute_let_or_case_type	(EI_Extended extensions expr_info) yes_type_heaps
	# (new_expr_info, yes_type_heaps) = substitute_let_or_case_type expr_info yes_type_heaps
	= (EI_Extended extensions new_expr_info, yes_type_heaps)
substitute_let_or_case_type	(EI_CaseType case_type) (Yes type_heaps)
	# (new_case_type, type_heaps) = substitute case_type type_heaps
	= (EI_CaseType new_case_type, Yes type_heaps)
//	= (EI_CaseType case_type, Yes type_heaps)
substitute_let_or_case_type	(EI_LetType let_type) (Yes type_heaps)
	# (new_let_type, type_heaps) = substitute let_type type_heaps
	= (EI_LetType new_let_type, Yes type_heaps)

instance unfold CasePatterns
where
	unfold (AlgebraicPatterns type patterns) us
		# (patterns, us) = unfold patterns us
		= (AlgebraicPatterns type patterns, us)
	unfold (BasicPatterns type patterns) us
		# (patterns, us) = unfold patterns us
		= (BasicPatterns type patterns, us)
	unfold (DynamicPatterns patterns) us
		# (patterns, us) = unfold patterns us
		= (DynamicPatterns patterns, us)

instance unfold BasicPattern
where
	unfold guard=:{bp_expr} us
		# (bp_expr, us) = unfold bp_expr us
		= ({ guard & bp_expr = bp_expr }, us)

instance unfold AlgebraicPattern
where
	unfold guard=:{ap_vars,ap_expr} us
		# (ap_vars, us) = unfold ap_vars us
		  (ap_expr, us) = unfold ap_expr us
		= ({ guard & ap_vars = ap_vars, ap_expr = ap_expr }, us)

instance unfold DynamicPattern
where
	unfold guard=:{dp_var,dp_rhs} us
		# (dp_var, us) = unfold dp_var us
		  (dp_rhs, us) = unfold dp_rhs us
		= ({ guard & dp_var = dp_var, dp_rhs = dp_rhs }, us)

updateFunctionCalls :: ![FunCall] ![FunCall] !*{# FunDef} !*SymbolTable
	-> (![FunCall], !*{# FunDef}, !*SymbolTable)
updateFunctionCalls calls collected_calls fun_defs symbol_table
	= foldSt add_function_call calls (collected_calls, fun_defs, symbol_table)
where
	add_function_call fc (collected_calls, fun_defs, symbol_table)
		# ({fun_symb}, fun_defs) = fun_defs![fc.fc_index]
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

//unfoldMacro :: !FunDef ![Expression] !*ExpandInfo -> (!Expression, !*ExpandInfo)
unfoldMacro {fun_body = TransformedBody {tb_args,tb_rhs}, fun_info = {fi_calls}} args fun_defs (calls, es=:{es_var_heap,es_symbol_heap, es_symbol_table})
	# (let_binds, var_heap) = bind_expressions tb_args args [] es_var_heap
	  us = { us_symbol_heap = es_symbol_heap, us_var_heap = var_heap, us_opt_type_heaps = No, us_cleanup_info = [],
			 us_handle_aci_free_vars = RemoveThem }
	  (result_expr, {us_symbol_heap,us_var_heap}) = unfold tb_rhs us
	  (calls, fun_defs, es_symbol_table) = updateFunctionCalls fi_calls calls fun_defs es_symbol_table
	| isEmpty let_binds
		= (result_expr, fun_defs, (calls, { es & es_var_heap = us_var_heap, es_symbol_heap = us_symbol_heap, es_symbol_table = es_symbol_table }))
		#  (new_info_ptr, us_symbol_heap) = newPtr EI_Empty us_symbol_heap
		= (Let { let_strict_binds = [], let_lazy_binds = let_binds, let_expr = result_expr, let_info_ptr = new_info_ptr}, fun_defs, 
					(calls, { es & es_var_heap = us_var_heap, es_symbol_heap = us_symbol_heap, es_symbol_table = es_symbol_table }))
where

	bind_expressions [var : vars] [expr : exprs] binds var_heap
		# (binds, var_heap) = bind_expressions vars exprs binds var_heap
		= bind_expression var expr binds var_heap
	bind_expressions _ _ binds var_heap
		= (binds, var_heap)

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
		= ([{ bind_src = expr, bind_dst = new_var} : binds], writePtr fv_info_ptr (VI_Variable fv_name new_info) var_heap)


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

partitionateMacros :: !IndexRange !Index !PredefinedSymbol !*{# FunDef} !u:{# DclModule} !*VarHeap !*ExpressionHeap !*SymbolTable !*ErrorAdmin
	-> (!*{# FunDef}, !u:{# DclModule}, !*VarHeap, !*ExpressionHeap, !*SymbolTable, !*ErrorAdmin )
partitionateMacros {ir_from,ir_to} mod_index alias_dummy fun_defs modules var_heap symbol_heap symbol_table error
	#! max_fun_nr = size fun_defs
	# partitioning_info = { pi_var_heap = var_heap, pi_symbol_heap = symbol_heap,
							pi_symbol_table = symbol_table,
							pi_error = error, pi_deps = [], pi_next_num = 0, pi_next_group = 0, pi_groups = [] }
	  (fun_defs, modules, {pi_symbol_table, pi_var_heap, pi_symbol_heap, pi_error, pi_next_group, pi_groups, pi_deps})
	  		= iFoldSt (pationate_macro mod_index max_fun_nr) ir_from ir_to (fun_defs, modules, partitioning_info)
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
		| macro_def.fun_kind == FK_Macro
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
		
	expand_simple_macro mod_index macro_index macro=:{fun_body = CheckedBody body, fun_info, fun_symb, fun_pos}
			(macro_defs, modules, pi=:{pi_symbol_table,pi_symbol_heap,pi_var_heap,pi_error})
		| macros_are_simple fun_info.fi_calls macro_defs
		  	# identPos = newPosition fun_symb fun_pos
			  es = { es_symbol_table = pi_symbol_table, es_var_heap = pi_var_heap,
					 es_symbol_heap = pi_symbol_heap, es_error = setErrorAdmin identPos pi_error }
			  (tb_args, tb_rhs, local_vars, fi_calls, macro_defs, modules, {es_symbol_table, es_var_heap, es_symbol_heap, es_error})
					= expandMacrosInBody [] body macro_defs mod_index alias_dummy modules es
			  macro = { macro & fun_body = TransformedBody { tb_args = tb_args, tb_rhs = tb_rhs},
			  			fun_info = { fun_info & fi_calls = fi_calls, fi_local_vars = local_vars }}
			= ({ macro_defs & [macro_index] = macro }, modules,
					{ pi & pi_symbol_table = es_symbol_table, pi_symbol_heap = es_symbol_heap, pi_var_heap = es_var_heap, pi_error = es_error })
			# pi = { pi & pi_deps = [macro_index:pi.pi_deps] }
			= ({ macro_defs & [macro_index] = { macro & fun_body = RhsMacroBody body }}, modules, pi)

	macros_are_simple [] macro_defs
		= True
	macros_are_simple [ {fc_index} : calls ] macro_defs
		# {fun_kind,fun_body} = macro_defs.[fc_index]
		= is_a_pattern_macro fun_kind fun_body && macros_are_simple calls macro_defs
	where
		is_a_pattern_macro FK_Macro (TransformedBody {tb_args})
			= True
		is_a_pattern_macro _ _
			= False
			
partitionateAndLiftFunctions :: ![IndexRange] !Index !PredefinedSymbol !*{# FunDef} !u:{# DclModule} !*VarHeap !*ExpressionHeap !*SymbolTable !*ErrorAdmin
	-> (!*{! Group}, !*{# FunDef}, !u:{# DclModule}, !*VarHeap, !*ExpressionHeap,  !*SymbolTable, !*ErrorAdmin )
partitionateAndLiftFunctions ranges mod_index alias_dummy fun_defs modules var_heap symbol_heap symbol_table error
	#! max_fun_nr = size fun_defs
	# partitioning_info = { pi_var_heap = var_heap, pi_symbol_heap = symbol_heap, pi_symbol_table = symbol_table,
							pi_error = error, pi_deps = [], pi_next_num = 0, pi_next_group = 0, pi_groups = [] }
	  (fun_defs, modules, {pi_groups, pi_symbol_table, pi_var_heap, pi_symbol_heap, pi_error})
	  		= foldSt (partitionate_functions mod_index max_fun_nr) ranges (fun_defs, modules, partitioning_info)
	  groups = { {group_members = group} \\ group <- reverse pi_groups }
	= (groups, fun_defs, modules, pi_var_heap, pi_symbol_heap, pi_symbol_table, pi_error)
where
		
	partitionate_functions mod_index max_fun_nr {ir_from,ir_to} funs_modules_pi
		= iFoldSt (partitionate_global_function mod_index max_fun_nr) ir_from ir_to funs_modules_pi
		
	partitionate_global_function mod_index max_fun_nr fun_index funs_modules_pi
		# (_, funs_modules_pi) = partitionate_function mod_index max_fun_nr fun_index funs_modules_pi
		= funs_modules_pi

	partitionate_function mod_index max_fun_nr fun_index (fun_defs, modules, pi)
		# (fun_def, fun_defs) = fun_defs![fun_index]
		= case fun_def.fun_body of
			CheckedBody body
				# fun_number = pi.pi_next_num
				# (min_dep, funs_modules_pi) = foldSt (visit_function mod_index max_fun_nr) fun_def.fun_info.fi_calls
						(max_fun_nr, ({ fun_defs & [fun_index] = { fun_def & fun_body = PartioningFunction body fun_number }}, modules,
							{ pi & pi_next_num = inc fun_number, pi_deps = [fun_index : pi.pi_deps] }))
				-> try_to_close_group mod_index max_fun_nr fun_index fun_number min_dep fun_def.fun_info.fi_def_level funs_modules_pi
			PartioningFunction _ fun_number
				-> (fun_number, (fun_defs, modules, pi))
			TransformedBody _
				| fun_def.fun_info.fi_group_index == NoIndex
					# (fun_defs, pi) =  add_called_macros fun_def.fun_info.fi_calls (fun_defs, pi)
					-> (max_fun_nr, ({ fun_defs & [fun_index] = {fun_def & fun_info.fi_group_index = pi.pi_next_group }}, modules,
							{pi & pi_next_group = inc pi.pi_next_group, pi_groups = [ [fun_index] : pi.pi_groups]}))
					-> (max_fun_nr, (fun_defs, modules, pi))

	visit_function mod_index max_fun_nr {fc_index} (min_dep, funs_modules_pi)
		# (next_min, funs_modules_pi) = partitionate_function mod_index max_fun_nr fc_index funs_modules_pi
		= (min next_min min_dep, funs_modules_pi)
		
	try_to_close_group mod_index max_fun_nr fun_index fun_number min_dep def_level (fun_defs, modules,
					pi=:{pi_symbol_table, pi_var_heap, pi_symbol_heap, pi_deps, pi_groups, pi_next_group, pi_error})
		| fun_number <= min_dep
			# (pi_deps, group_without_macros, group_without_funs, fun_defs)
					= close_group fun_index pi_deps [] [] max_fun_nr pi_next_group fun_defs
			  (fun_defs, pi_var_heap, pi_symbol_heap)
			  		= liftFunctions def_level (group_without_macros ++ group_without_funs) pi_next_group fun_defs pi_var_heap pi_symbol_heap
			  (fun_defs, modules, es)
			  		= expand_macros_in_group mod_index group_without_funs (fun_defs, modules,
			  				{ es_symbol_table = pi_symbol_table, es_var_heap = pi_var_heap, es_symbol_heap = pi_symbol_heap,
			  				  es_error = pi_error })
			  (fun_defs, modules, {es_symbol_table, es_var_heap, es_symbol_heap, es_error})
			  		= expand_macros_in_group mod_index group_without_macros (fun_defs, modules, es)
			= (max_fun_nr, (fun_defs, modules, { pi & pi_deps = pi_deps, pi_var_heap = es_var_heap,
						pi_symbol_table = es_symbol_table, pi_error = es_error, pi_symbol_heap = es_symbol_heap, 
						pi_next_group = inc pi_next_group, pi_groups = [ group_without_macros ++ group_without_funs : pi_groups ] }))
			= (min_dep, (fun_defs, modules, pi))
	where
		close_group fun_index [d:ds] group_without_macros group_without_funs nr_of_fun_defs group_number fun_defs
			# (fun_def, fun_defs) = fun_defs![d]
			  fun_defs = { fun_defs & [d] = { fun_def & fun_info.fi_group_index = group_number }}
			| fun_def.fun_kind == FK_Macro
				# group_without_funs = [d : group_without_funs]
				| d == fun_index
					= (ds, group_without_macros, group_without_funs, fun_defs)
					= close_group fun_index ds group_without_macros group_without_funs nr_of_fun_defs group_number fun_defs
				# group_without_macros = [d : group_without_macros]
				| d == fun_index
					= (ds, group_without_macros, group_without_funs, fun_defs)
					= close_group fun_index ds group_without_macros group_without_funs nr_of_fun_defs group_number fun_defs
		
		expand_macros_in_group mod_index group funs_modules_es
			= foldSt (expand_macros mod_index) group (funs_modules_es)

		expand_macros mod_index fun_index (fun_and_macro_defs, modules, es)
			# (fun_def, fun_and_macro_defs) = fun_and_macro_defs![fun_index]
			  {fun_symb,fun_body = PartioningFunction body _, fun_info, fun_pos} = fun_def
		  	  identPos = newPosition fun_symb fun_pos
			  (tb_args, tb_rhs, fi_local_vars, fi_calls, fun_and_macro_defs, modules, es)
					= expandMacrosInBody fun_info.fi_calls body fun_and_macro_defs mod_index alias_dummy modules
							{ es & es_error = setErrorAdmin identPos es.es_error }
			  fun_def = { fun_def & fun_body = TransformedBody { tb_args = tb_args, tb_rhs = tb_rhs},
			  			fun_info = { fun_info & fi_calls = fi_calls, fi_local_vars = fi_local_vars }}
			= ({ fun_and_macro_defs & [fun_index] = fun_def }, modules, es)
					---> ("expand_macros", fun_symb, fi_local_vars)
	 
	add_called_macros calls macro_defs_and_pi
		= foldSt add_called_macro calls macro_defs_and_pi
	where
		add_called_macro {fc_index} (macro_defs, pi)
			# (macro_def, macro_defs) = macro_defs![fc_index]
			= case macro_def.fun_body of
				TransformedBody _
					| macro_def.fun_info.fi_group_index == NoIndex
						# (macro_defs, pi) = add_called_macros macro_def.fun_info.fi_calls (macro_defs, pi)
						->	({ macro_defs & [fc_index] = {macro_def & fun_info.fi_group_index = pi.pi_next_group }},
								{pi & pi_next_group = inc pi.pi_next_group, pi_groups = [ [fc_index] : pi.pi_groups]})
						-> (macro_defs, pi)



addFunctionCallsToSymbolTable calls fun_defs symbol_table
	= foldSt add_function_call_to_symbol_table calls ([], fun_defs, symbol_table)
where
	add_function_call_to_symbol_table fc=:{fc_index} (collected_calls, fun_defs, symbol_table)
		# ({fun_symb = { id_info }, fun_kind}, fun_defs) = fun_defs![fc_index]
		| fun_kind == FK_Macro
			= (collected_calls, fun_defs, symbol_table)
			# (entry, symbol_table) = readPtr id_info symbol_table
			= ([fc : collected_calls], fun_defs,
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
		

expandMacrosInBody fi_calls {cb_args,cb_rhs} fun_defs mod_index alias_dummy modules es=:{es_symbol_table}
	# (prev_calls, fun_defs, es_symbol_table) = addFunctionCallsToSymbolTable fi_calls fun_defs es_symbol_table
	  ([rhs:rhss], fun_defs, modules, (all_calls, es)) = expand cb_rhs fun_defs mod_index modules (prev_calls, { es & es_symbol_table = es_symbol_table })
	  (fun_defs, es_symbol_table) = removeFunctionCallsFromSymbolTable all_calls fun_defs es.es_symbol_table
	  (merged_rhs, es_var_heap, es_symbol_heap, es_error) = mergeCases rhs rhss es.es_var_heap es.es_symbol_heap es.es_error
	  (new_rhs, new_args, local_vars, {cos_error, cos_var_heap, cos_symbol_heap})
	  		= determineVariablesAndRefCounts cb_args merged_rhs
	  				{ cos_error = es_error, cos_var_heap = es_var_heap, cos_symbol_heap = es_symbol_heap,
	  					cos_alias_dummy = alias_dummy }
	= (new_args, new_rhs, local_vars, all_calls, fun_defs, modules,
		{ es & es_error = cos_error, es_var_heap = cos_var_heap, es_symbol_heap = cos_symbol_heap,
												es_symbol_table = es_symbol_table })
		---> ("expandMacrosInBody", (cb_args, cb_rhs, '\n'), ("merged_rhs", merged_rhs, '\n'), (new_args, local_vars, new_rhs, '\n'))

cContainsFreeVars 	:== True
cContainsNoFreeVars :== False

cMacroIsCalled 		:== True
cNoMacroIsCalled 	:== False


mergeCases :: !Expression ![Expression] !*VarHeap !*ExpressionHeap !*ErrorAdmin -> *(!Expression, !*VarHeap, !*ExpressionHeap, !*ErrorAdmin);
mergeCases expr [] var_heap symbol_heap error
	= (expr, var_heap, symbol_heap, error)
mergeCases (Let lad=:{let_expr}) exprs var_heap symbol_heap error
	# (let_expr, var_heap, symbol_heap, error) = mergeCases let_expr exprs var_heap symbol_heap error
	= (Let {lad & let_expr = let_expr}, var_heap,symbol_heap, error)
mergeCases case_expr=:(Case first_case=:{case_expr = Var {var_info_ptr}, case_default = No}) [expr : exprs] var_heap symbol_heap error
	# (split_result, var_heap, symbol_heap) = split_case var_info_ptr expr var_heap symbol_heap
	= case split_result of
		Yes {case_guards,case_default}
			# (case_guards, var_heap, symbol_heap, error) = merge_guards first_case.case_guards case_guards var_heap symbol_heap error
			-> mergeCases (Case { first_case & case_guards = case_guards, case_default = case_default }) exprs var_heap symbol_heap error
		No
			# (case_default, var_heap, symbol_heap, error) = mergeCases expr exprs var_heap symbol_heap error
			-> (Case { first_case & case_default = Yes case_default}, var_heap, symbol_heap, error)

where
	split_case split_var_info_ptr (Case this_case=:{case_expr = Var {var_info_ptr}, case_guards, case_default}) var_heap symbol_heap
		| split_var_info_ptr == var_info_ptr
			= (Yes this_case, var_heap, symbol_heap)
		| has_no_default case_default
			= case case_guards of
				AlgebraicPatterns type [alg_pattern]
					# (split_result, var_heap, symbol_heap) = split_case split_var_info_ptr alg_pattern.ap_expr var_heap symbol_heap
					-> case split_result of
						Yes split_case
							-> (Yes { split_case & case_guards = push_expression_into_guards (
										\guard_expr -> Case { this_case & case_guards = 
												AlgebraicPatterns type [ { alg_pattern & ap_expr = guard_expr }] })
													split_case.case_guards }, var_heap, symbol_heap)
									
						No
							-> (No, var_heap, symbol_heap) 
				BasicPatterns type [basic_pattern]
					# (split_result, var_heap, symbol_heap) = split_case split_var_info_ptr basic_pattern.bp_expr var_heap symbol_heap
					-> case split_result of
						Yes split_case
							-> (Yes { split_case & case_guards = push_expression_into_guards (
										\guard_expr -> Case { this_case & case_guards = 
												BasicPatterns type [ { basic_pattern & bp_expr = guard_expr }] })
													split_case.case_guards }, var_heap, symbol_heap)
									
						No
							-> (No, var_heap, symbol_heap)
				DynamicPatterns [dynamic_pattern]
					# (split_result, var_heap, symbol_heap) = split_case split_var_info_ptr dynamic_pattern.dp_rhs var_heap symbol_heap
					-> case split_result of
						Yes split_case
							-> (Yes { split_case & case_guards = push_expression_into_guards (
										\guard_expr -> Case { this_case & case_guards = 
												DynamicPatterns [ { dynamic_pattern & dp_rhs = guard_expr }] })
													split_case.case_guards }, var_heap, symbol_heap)
									
						No
							-> (No, var_heap, symbol_heap)
				_
					-> (No, var_heap, symbol_heap)
		| otherwise
			= (No, var_heap, symbol_heap)
	split_case split_var_info_ptr (Let lad=:{let_expr,let_strict_binds}) var_heap symbol_heap
		| isEmpty let_strict_binds
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

	push_expression_into_guards expr_fun (AlgebraicPatterns type patterns) 
		= AlgebraicPatterns type (map (\algpattern -> { algpattern & ap_expr = expr_fun algpattern.ap_expr }) patterns)
	push_expression_into_guards expr_fun (BasicPatterns type patterns) 
		= BasicPatterns type (map (\baspattern -> { baspattern & bp_expr = expr_fun baspattern.bp_expr }) patterns)
	push_expression_into_guards expr_fun (DynamicPatterns patterns) 
		= DynamicPatterns (map (\dynpattern -> { dynpattern & dp_rhs = expr_fun dynpattern.dp_rhs }) patterns)

	replace_variables_in_expression expr var_heap symbol_heap
		# us = { us_var_heap = var_heap, us_symbol_heap = symbol_heap, us_opt_type_heaps = No,
				 us_cleanup_info = [], us_handle_aci_free_vars = RemoveThem }
		  (expr, us) = unfold expr us
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
		renew_let_var bind=:{bind_dst} (rev_binds, var_heap)
			# (bind_dst, var_heap) = new_variable bind_dst var_heap
			= ([{ bind & bind_dst = bind_dst } : rev_binds], var_heap)

		replace_variables_in_bound_expression bind=:{bind_src} (rev_binds, var_heap, expr_heap)
			# (bind_src, var_heap, expr_heap) = replace_variables_in_expression bind_src var_heap expr_heap
			= ([{ bind & bind_src = bind_src } : rev_binds], var_heap, expr_heap)

		
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
				# (ap_expr, var_heap, symbol_heap, error) = mergeCases ap_expr [new_pattern.ap_expr] var_heap symbol_heap error
				= ([{ pattern & ap_expr = ap_expr} : patterns], var_heap, symbol_heap, error)
				# (new_expr, var_heap, symbol_heap) = replace_variables new_pattern.ap_vars new_pattern.ap_expr ap_vars var_heap symbol_heap
				  (ap_expr, var_heap, symbol_heap, error) = mergeCases ap_expr [new_expr] var_heap symbol_heap error
				= ([{ pattern & ap_expr = ap_expr} : patterns], var_heap, symbol_heap, error)
			# (patterns, var_heap, symbol_heap, error) = merge_algebraic_pattern_with_patterns new_pattern patterns var_heap symbol_heap error		
			= ([ pattern : patterns ], var_heap, symbol_heap, error)
	where
		replace_variables vars expr ap_vars var_heap symbol_heap
			# us = { us_var_heap = build_aliases vars ap_vars var_heap, us_symbol_heap = symbol_heap, us_opt_type_heaps = No,
					 us_cleanup_info=[], us_handle_aci_free_vars = RemoveThem }
			  (expr, us) = unfold expr us
			= (expr, us.us_var_heap, us.us_symbol_heap)

		build_aliases [var1 : vars1] [ {fv_name,fv_info_ptr} : vars2 ] var_heap
			= build_aliases vars1 vars2 (writePtr var1.fv_info_ptr (VI_Variable fv_name fv_info_ptr) var_heap)
		build_aliases [] [] var_heap
			= var_heap

	merge_algebraic_pattern_with_patterns new_pattern [] var_heap symbol_heap error
		= ([new_pattern], var_heap, symbol_heap, error)
	
	merge_basic_pattern_with_patterns new_pattern [pattern=:{bp_value,bp_expr} : patterns]  var_heap symbol_heap error
		| new_pattern.bp_value == bp_value
			# (bp_expr, var_heap, symbol_heap, error) = mergeCases bp_expr [new_pattern.bp_expr] var_heap symbol_heap error
			= ([{ pattern & bp_expr = bp_expr} : patterns], var_heap, symbol_heap, error)
			# (patterns, var_heap, symbol_heap, error) = merge_basic_pattern_with_patterns new_pattern patterns var_heap symbol_heap error		
			= ([ pattern : patterns ], var_heap, symbol_heap, error)
	merge_basic_pattern_with_patterns new_pattern [] var_heap symbol_heap error
		= ([new_pattern], var_heap, symbol_heap, error)
	
mergeCases case_expr=:(Case first_case=:{case_default}) [expr : exprs] var_heap symbol_heap error
	= case case_default of
		Yes default_expr
			# (default_expr, var_heap, symbol_heap, error) = mergeCases default_expr [expr : exprs] var_heap symbol_heap error
			-> (Case { first_case & case_default = Yes default_expr }, var_heap, symbol_heap, error)
		No
			# (default_expr, var_heap, symbol_heap, error) = mergeCases expr exprs var_heap symbol_heap error
			-> (Case { first_case & case_default = Yes default_expr }, var_heap, symbol_heap, error)
mergeCases expr _ var_heap symbol_heap error
	= (expr, var_heap, symbol_heap, checkWarning "" " alternative will never match" error)

 
liftFunctions min_level group group_index fun_defs var_heap expr_heap
	# (contains_free_vars, lifted_function_called, fun_defs)
			= foldSt (add_free_vars_of_non_recursive_calls_to_function group_index) group (False, False, fun_defs)
	| contains_free_vars
		# fun_defs = iterateSt (add_free_vars_of_recursive_calls_to_functions group_index group) fun_defs
		= lift_functions group fun_defs var_heap expr_heap
	| lifted_function_called
		= lift_functions group fun_defs var_heap expr_heap
		= (fun_defs, var_heap, expr_heap)
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
			| fi_group_index == group_index
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
			| fi_group_index == group_index
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

	lift_functions group fun_defs var_heap expr_heap
		= foldSt lift_function group (fun_defs, var_heap, expr_heap)
	where
		lift_function fun (fun_defs=:{[fun] = fun_def}, var_heap, expr_heap)
			# {fi_free_vars} = fun_def.fun_info
			  fun_lifted = length fi_free_vars
			  (PartioningFunction {cb_args,cb_rhs} fun_number) = fun_def.fun_body
			  (cb_args, var_heap) = add_lifted_args fi_free_vars cb_args var_heap
			  (cb_rhs, {ls_fun_defs,ls_var_heap,ls_expr_heap}) = lift cb_rhs { ls_fun_defs = fun_defs, ls_var_heap = var_heap, ls_expr_heap = expr_heap }
			  ls_var_heap = remove_lifted_args fi_free_vars ls_var_heap
			  ls_fun_defs = { ls_fun_defs & [fun] = { fun_def & fun_lifted = fun_lifted, fun_body = PartioningFunction {cb_args = cb_args, cb_rhs = cb_rhs} fun_number}}
			= (ls_fun_defs, ls_var_heap, ls_expr_heap)
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
	,	es_error 		:: !.ErrorAdmin
	}

class expand a :: !a !*{#FunDef} !Int !v:{# DclModule} !*ExpandInfo -> (!a, !*{#FunDef}, !v:{# DclModule}, !*ExpandInfo)

instance expand [a] | expand a
where
	expand [x:xs] fun_and_macro_defs mod_index modules es
		# (x, fun_and_macro_defs, modules, es) = expand x fun_and_macro_defs mod_index modules es
		  (xs, fun_and_macro_defs, modules, es) = expand xs fun_and_macro_defs mod_index modules es
		= ([x:xs], fun_and_macro_defs, modules, es)
	expand [] fun_and_macro_defs mod_index modules es
		= ([], fun_and_macro_defs, modules, es)

instance expand (a,b) | expand a & expand b
where
	expand (x,y) fun_and_macro_defs mod_index modules es
		# (x, fun_and_macro_defs, modules, es) = expand x fun_and_macro_defs mod_index modules es
		  (y, fun_and_macro_defs, modules, es) = expand y fun_and_macro_defs mod_index modules es
		= ((x,y), fun_and_macro_defs, modules, es)

instance expand (Optional a) | expand a
where
	expand (Yes x) fun_and_macro_defs mod_index modules es
		# (x, fun_and_macro_defs, modules, es) = expand x fun_and_macro_defs mod_index modules es
		= (Yes x, fun_and_macro_defs, modules, es)
	expand no fun_and_macro_defs mod_index modules es
		= (no, fun_and_macro_defs, modules, es)

instance expand Expression
where

	expand (App app=:{app_symb = symb=:{symb_arity, symb_kind = SK_Macro {glob_object,glob_module}}, app_args}) fun_and_macro_defs mod_index modules es
		# (app_args, fun_and_macro_defs, modules, (calls, state)) = expand app_args fun_and_macro_defs mod_index modules es
		# (macro, fun_and_macro_defs) = fun_and_macro_defs![glob_object]
		| macro.fun_arity == symb_arity
			# (expr, fun_and_macro_defs, es) = unfoldMacro macro app_args fun_and_macro_defs (calls, state)
			= (expr, fun_and_macro_defs, modules, es)
			# (calls, es_symbol_table) = examineFunctionCall macro.fun_symb {fc_index = glob_object, fc_level = NotALevel} (calls, state.es_symbol_table)
			= (App { app & app_symb = { symb & symb_kind = SK_Function {glob_object = glob_object, glob_module = glob_module} }, app_args = app_args },
					fun_and_macro_defs, modules, (calls, { state & es_symbol_table = es_symbol_table }))
	expand (App app=:{app_args}) fun_and_macro_defs mod_index modules es
		# (app_args, fun_and_macro_defs, modules, es) = expand app_args fun_and_macro_defs mod_index modules es
		= (App { app & app_args = app_args }, fun_and_macro_defs, modules, es)
	expand (expr @ exprs) fun_and_macro_defs mod_index modules es
		# ((expr,exprs), fun_and_macro_defs, modules, es) = expand (expr,exprs) fun_and_macro_defs mod_index modules es
		= (expr @ exprs, fun_and_macro_defs, modules, es)
	expand (Let lad=:{let_strict_binds, let_lazy_binds, let_expr}) fun_and_macro_defs mod_index modules es
		# (let_strict_binds, fun_and_macro_defs, modules, es) = expand let_strict_binds fun_and_macro_defs mod_index modules es
		# (let_lazy_binds, fun_and_macro_defs, modules, es) = expand let_lazy_binds fun_and_macro_defs mod_index modules es
		# (let_expr, fun_and_macro_defs, modules, es) = expand let_expr fun_and_macro_defs mod_index modules es
		= (Let {lad & let_expr = let_expr, let_strict_binds = let_strict_binds, let_lazy_binds = let_lazy_binds}, fun_and_macro_defs, modules, es)
	expand (Case case_expr) fun_and_macro_defs mod_index modules es
		# (case_expr, fun_and_macro_defs, modules, es) = expand case_expr fun_and_macro_defs mod_index modules es
		= (Case case_expr, fun_and_macro_defs, modules, es)
	expand (Selection is_unique expr selectors) fun_and_macro_defs mod_index modules es
		# ((expr, selectors), fun_and_macro_defs, modules, es) = expand (expr, selectors) fun_and_macro_defs mod_index modules es
		= (Selection is_unique expr selectors, fun_and_macro_defs, modules, es)
	expand (Update expr1 selectors expr2) fun_and_macro_defs mod_index modules es
		# (((expr1, expr2), selectors), fun_and_macro_defs, modules, es) = expand ((expr1, expr2), selectors) fun_and_macro_defs mod_index modules es
		= (Update expr1 selectors expr2, fun_and_macro_defs, modules, es)
	expand (RecordUpdate cons_symbol expression expressions) fun_and_macro_defs mod_index modules es
		# ((expression, expressions), fun_and_macro_defs, modules, es) = expand (expression, expressions) fun_and_macro_defs mod_index modules es
		= (RecordUpdate cons_symbol expression expressions, fun_and_macro_defs, modules, es)
	expand (TupleSelect symbol argn_nr expr) fun_and_macro_defs mod_index modules es
		# (expr, fun_and_macro_defs, modules, es) = expand expr fun_and_macro_defs mod_index modules es
		= (TupleSelect symbol argn_nr expr, fun_and_macro_defs, modules, es)
	expand (Lambda vars expr) fun_and_macro_defs mod_index modules es
		# (expr, fun_and_macro_defs, modules, es) = expand expr fun_and_macro_defs mod_index modules es
		= (Lambda vars expr, fun_and_macro_defs, modules, es)
	expand (MatchExpr opt_tuple cons_symb expr) fun_and_macro_defs mod_index modules es
		# (expr, fun_and_macro_defs, modules, es) = expand expr fun_and_macro_defs mod_index modules es
		= (MatchExpr opt_tuple cons_symb expr, fun_and_macro_defs, modules, es)
	expand expr fun_and_macro_defs mod_index modules es
		= (expr, fun_and_macro_defs, modules, es)

instance expand Selection
where
	expand (ArraySelection array_select expr_ptr index_expr) fun_and_macro_defs mod_index modules es
		# (index_expr, fun_and_macro_defs, modules, es) = expand index_expr fun_and_macro_defs mod_index modules es
		= (ArraySelection array_select expr_ptr index_expr, fun_and_macro_defs, modules, es)
	expand record_selection fun_and_macro_defs mod_index modules es
		= (record_selection, fun_and_macro_defs, modules, es)


instance expand (Bind a b) | expand a
where
	expand bind=:{bind_src} fun_and_macro_defs mod_index modules es
		# (bind_src, fun_and_macro_defs, modules, es) = expand bind_src fun_and_macro_defs mod_index modules es
		= ({ bind & bind_src = bind_src }, fun_and_macro_defs, modules, es)

instance expand Case
where
	expand kees=:{ case_expr,case_guards,case_default } fun_and_macro_defs mod_index modules es
		# ((case_expr,(case_guards,case_default)), fun_and_macro_defs, modules, es) = expand (case_expr,(case_guards,case_default)) fun_and_macro_defs mod_index modules es
		= ({ kees & case_expr = case_expr,case_guards = case_guards, case_default = case_default }, fun_and_macro_defs, modules, es)

instance expand CasePatterns
where
	expand (AlgebraicPatterns type patterns) fun_and_macro_defs mod_index modules es
		# (patterns, fun_and_macro_defs, modules, es) = expand patterns fun_and_macro_defs mod_index modules es
		= (AlgebraicPatterns type patterns, fun_and_macro_defs, modules, es) 
	expand (BasicPatterns type patterns) fun_and_macro_defs mod_index modules es
		# (patterns, fun_and_macro_defs, modules, es) = expand patterns fun_and_macro_defs mod_index modules es
		= (BasicPatterns type patterns, fun_and_macro_defs, modules, es) 
	expand (DynamicPatterns patterns) fun_and_macro_defs mod_index modules es
		# (patterns, fun_and_macro_defs, modules, es) = expand patterns fun_and_macro_defs mod_index modules es
		= (DynamicPatterns patterns, fun_and_macro_defs, modules, es) 

instance expand AlgebraicPattern
where
	expand alg_pattern=:{ap_expr} fun_and_macro_defs mod_index modules es
		# (ap_expr, fun_and_macro_defs, modules, es) = expand ap_expr fun_and_macro_defs mod_index modules es
		= ({ alg_pattern & ap_expr = ap_expr }, fun_and_macro_defs, modules, es)

instance expand BasicPattern
where
	expand bas_pattern=:{bp_expr} fun_and_macro_defs mod_index modules es
		# (bp_expr, fun_and_macro_defs, modules, es) = expand bp_expr fun_and_macro_defs mod_index modules es
		= ({ bas_pattern & bp_expr = bp_expr }, fun_and_macro_defs, modules, es)

instance expand DynamicPattern
where
	expand dyn_pattern=:{dp_rhs} fun_and_macro_defs mod_index modules es
		# (dp_rhs, fun_and_macro_defs, modules, es) = expand dp_rhs fun_and_macro_defs mod_index modules es
		= ({ dyn_pattern & dp_rhs = dp_rhs }, fun_and_macro_defs, modules, es)


::	CollectState =
	{	cos_var_heap	:: !.VarHeap
	,	cos_symbol_heap :: !.ExpressionHeap
	,	cos_error		:: !.ErrorAdmin
	,	cos_alias_dummy	:: !PredefinedSymbol
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

instance clearCount (Bind a b) | clearCount b
where
	clearCount bind=:{bind_dst} locality var_heap
		= clearCount bind_dst locality var_heap

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
		   
			determine_aliases [{bind_dst={fv_info_ptr}, bind_src = Var var} : binds] var_heap
				= determine_aliases binds (writePtr fv_info_ptr (VI_Alias var) var_heap)
			determine_aliases [bind : binds] var_heap
				= determine_aliases binds (clearCount bind cIsALocalVar var_heap)
			determine_aliases [] var_heap
				= var_heap

			
		/*	Remove all aliases from the list of lazy 'let'-binds. Add a _dummyForStrictAlias
			function call for the strict aliases. Be careful with cycles! */
		
			detect_cycles_and_handle_alias_binds is_strict [] cos
				= (cContainsNoCycle, [], cos)
			detect_cycles_and_handle_alias_binds is_strict [bind=:{bind_dst={fv_info_ptr}} : binds] cos
				#! var_info = sreadPtr fv_info_ptr cos.cos_var_heap
				= case var_info of
					VI_Alias {var_info_ptr}
						| is_cyclic fv_info_ptr var_info_ptr cos.cos_var_heap
							-> (cContainsACycle, binds, cos)
						| is_strict
							# cos_var_heap = writePtr fv_info_ptr (VI_Count 0 cIsALocalVar) cos.cos_var_heap
							  (new_bind_src, cos) = add_dummy_id_for_strict_alias bind.bind_src 
							  								{ cos & cos_var_heap = cos_var_heap }
							  (is_cyclic, binds, cos) 
							  		= detect_cycles_and_handle_alias_binds is_strict binds cos
							-> (is_cyclic, [{ bind & bind_src = new_bind_src } : binds], cos)
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
				
				add_dummy_id_for_strict_alias bind_src cos=:{cos_symbol_heap, cos_alias_dummy}
					# (new_app_info_ptr, cos_symbol_heap) = newPtr EI_Empty cos_symbol_heap
					  {pds_ident, pds_module, pds_def} = cos_alias_dummy
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
		
			examine_reachable_binds bind_found [bind=:(is_strict, {bind_dst=fv=:{fv_info_ptr},bind_src}) : binds] collected_binds free_vars cos
				# (bind_found, binds, collected_binds, free_vars, cos) = examine_reachable_binds bind_found binds collected_binds free_vars cos
				#! var_info = sreadPtr fv_info_ptr cos.cos_var_heap
				# (VI_Count count is_global) = var_info
				| count > 0
					# (bind_src, free_vars, cos) = collectVariables bind_src free_vars cos
					= (True, binds, [ (is_strict, { bind_dst = { fv & fv_count = count }, bind_src = bind_src }) : collected_binds ], free_vars, cos)
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
	collectVariables (DynamicExpr dynamic_expr=:{dyn_expr}) free_vars cos
		#! (dyn_expr, free_vars, cos) = collectVariables dyn_expr free_vars cos
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
				-> abort "collectVariables [BoundVar] (transform, 1227)"  <<- (var_info ---> var_name)

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
