implementation module trans

import StdEnv

import syntax, transform, checksupport, StdCompare, check, utilities

import RWSDebug

::	PartitioningInfo = 
	{	pi_marks :: 		!.{# Int}
	,	pi_next_num ::		!Int
	,	pi_next_group ::	!Int
	,	pi_groups ::		![[Int]]
	,	pi_deps ::			![Int]
	}

NotChecked :== -1	

partitionateFunctions :: !*{# FunDef} ![IndexRange] -> (!*{! Group}, !*{# FunDef})
partitionateFunctions fun_defs ranges
	#! max_fun_nr = size fun_defs
	# partitioning_info = { pi_marks = createArray max_fun_nr NotChecked, pi_deps = [], pi_next_num = 0, pi_next_group = 0, pi_groups = [] }
	  (fun_defs, {pi_groups,pi_next_group}) = 
	  		foldSt (partitionate_functions max_fun_nr) ranges (fun_defs, partitioning_info)
	  groups = { {group_members = group} \\ group <- reverse pi_groups }
	= (groups, fun_defs)
where
	partitionate_functions :: !Index !IndexRange !(!*{# FunDef}, !*PartitioningInfo) -> (!*{# FunDef}, !*PartitioningInfo)
	partitionate_functions max_fun_nr ir=:{ir_from,ir_to} (fun_defs, pi=:{pi_marks})
		| ir_from == ir_to
			= (fun_defs, pi)
		| pi_marks.[ir_from] == NotChecked
			# (_, fun_defs, pi) = partitionate_function ir_from max_fun_nr fun_defs pi
			= partitionate_functions max_fun_nr { ir & ir_from = inc ir_from } (fun_defs, pi)
			= partitionate_functions max_fun_nr { ir & ir_from = inc ir_from } (fun_defs, pi)

	partitionate_function :: !Int !Int !*{# FunDef} !*PartitioningInfo -> *(!Int, !*{# FunDef}, !*PartitioningInfo)
	partitionate_function fun_index max_fun_nr fun_defs pi=:{pi_next_num}
		#! fd = fun_defs.[fun_index]
		# {fi_calls} = fd.fun_info
		  (min_dep, fun_defs, pi) = visit_functions fi_calls max_fun_nr max_fun_nr fun_defs (push_on_dep_stack fun_index pi)
		= try_to_close_group fun_index pi_next_num min_dep max_fun_nr fun_defs pi

/*				  
	partitionate_function :: !Int !Int !*{# FunDef} !*PartitioningInfo -> *(!Int, !*{# FunDef}, !*PartitioningInfo)
	partitionate_function fun_index max_fun_nr fun_defs pi=:{pi_next_num}
		#! fd = fun_defs.[fun_index]
		| fd.fun_kind
			# {fi_calls} = fd.fun_info
			  (min_dep, fun_defs, pi) = visit_functions fi_calls max_fun_nr max_fun_nr fun_defs (push_on_dep_stack fun_index pi)
			= try_to_close_group fun_index pi_next_num min_dep max_fun_nr fun_defs pi
			= (max_fun_nr, fun_defs, pi)
*/
	push_on_dep_stack :: !Int !*PartitioningInfo -> *PartitioningInfo;
	push_on_dep_stack fun_index pi=:{pi_deps,pi_marks,pi_next_num}
		= { pi & pi_deps = [fun_index : pi_deps], pi_marks = { pi_marks & [fun_index] = pi_next_num}, pi_next_num = inc pi_next_num}

	visit_functions :: ![FunCall] !Int !Int !*{# FunDef} !*PartitioningInfo -> *(!Int, !*{# FunDef}, !*PartitioningInfo)
	visit_functions [{fc_index}:funs] min_dep max_fun_nr fun_defs pi=:{pi_marks} 
		#! mark = pi_marks.[fc_index]
		| mark == NotChecked
			# (mark, fun_defs, pi) = partitionate_function fc_index max_fun_nr fun_defs  pi
			= visit_functions funs (min min_dep mark) max_fun_nr fun_defs pi
			= visit_functions funs (min min_dep mark) max_fun_nr fun_defs pi
	visit_functions [] min_dep max_fun_nr fun_defs pi
		= (min_dep, fun_defs, pi)
		

	try_to_close_group :: !Int !Int !Int !Int !*{# FunDef} !*PartitioningInfo -> *(!Int, !*{# FunDef}, !*PartitioningInfo)
	try_to_close_group fun_index fun_nr min_dep max_fun_nr fun_defs pi=:{pi_marks, pi_deps, pi_groups, pi_next_group}
		| fun_nr <= min_dep
			# (pi_deps, pi_marks, group, fun_defs)
				= close_group fun_index pi_deps pi_marks [] max_fun_nr pi_next_group fun_defs
			  pi = { pi & pi_deps = pi_deps, pi_marks = pi_marks, pi_next_group = inc pi_next_group,  pi_groups = [group : pi_groups] }
			= (max_fun_nr, fun_defs, pi)
			= (min_dep, fun_defs, pi)
	where
		close_group :: !Int ![Int] !*{# Int} ![Int] !Int !Int !*{# FunDef} -> (![Int], !*{# Int}, ![Int], !*{# FunDef})
		close_group fun_index [d:ds] marks group max_fun_nr group_number fun_defs
			# marks = { marks & [d] = max_fun_nr }
			#! fd = fun_defs.[d]
			# fun_defs = { fun_defs & [d] = { fd & fun_info.fi_group_index = group_number }}
			| d == fun_index
				= (ds, marks, [d : group], fun_defs)
				= close_group fun_index ds marks [d : group] max_fun_nr group_number fun_defs

::	BitVector :== Int

::	*AnalyseInfo =
	{	ai_heap			:: !*VarHeap
	,	ai_cons_class	:: !*{! ConsClasses}
	,	ai_class_subst	:: !* ConsClassSubst
	,	ai_next_var		:: !Int
	}

::	ConsClassSubst	:== {# ConsClass}

/*
	The argument classification (i.e. 'accumulating', 'active' or 'passive') of consumers
	is represented by an negative integer value.
	Possitive classifications are used to identify variables.
	Unification of classifications is done on-the-fly
*/


cPassive   		:== -1
cActive			:== -2
cAccumulating   :== -3

IsAVariable cons_class :== cons_class >= 0

combineClasses cc1 cc2
	| IsAVariable cc1
		= cAccumulating
	| IsAVariable cc2
		= cAccumulating
		= min cc1 cc2
 
unifyClassifications :: !ConsClass !ConsClass !*ConsClassSubst -> *ConsClassSubst
unifyClassifications cc1 cc2 subst
	#  (cc1,subst) = skip_indirections_of_variables cc1 subst
	   (cc2,subst) = skip_indirections_of_variables cc2 subst
	= combine_cons_classes cc1 cc2 subst
where		   

	skip_indirections_of_variables :: Int !*ConsClassSubst -> (!Int,!*ConsClassSubst)
	skip_indirections_of_variables cc subst
		| IsAVariable cc
			#! cc = skip_indirections cc subst
			= (cc, subst)
			= (cc, subst)
	where	
		skip_indirections cons_var subst
			#! redir = subst.[cons_var]
			| IsAVariable redir
				= skip_indirections redir subst
				= cons_var
			
	combine_cons_classes :: !Int !Int !*ConsClassSubst -> *ConsClassSubst
	combine_cons_classes cc1 cc2 subst
		| cc1 == cc2
			= subst
		| IsAVariable cc1
			#! cc_val1 = subst.[cc1]
			| IsAVariable cc2
				#! cc_val2 = subst.[cc2]
				= { subst & [cc2] = cc1, [cc1] = combine_cons_constants cc_val1 cc_val2 }
				= { subst & [cc1] = combine_cons_constants cc_val1 cc2 }
		| IsAVariable cc2
			#! cc_val2 = subst.[cc2]
			= { subst & [cc2] = combine_cons_constants cc1 cc_val2 }
			= subst
				   
	combine_cons_constants cc1 cc2
		= min cc1 cc2

write_ptr ptr val heap mess
	| isNilPtr ptr
		= abort mess
		= heap <:=  (ptr,val)

class consumerRequirements a :: !a !AnalyseInfo -> (!ConsClass, !AnalyseInfo)

instance consumerRequirements BoundVar
where
	consumerRequirements {var_info_ptr} ai=:{ai_heap}
		#! var_info = sreadPtr var_info_ptr ai_heap
		= case var_info of
			VI_AccVar temp_var
				-> (temp_var, ai)
			_
				-> (cPassive, ai)

instance consumerRequirements Expression where
	consumerRequirements (Var var) ai
		= consumerRequirements var ai
	consumerRequirements (App app) ai
		= consumerRequirements app ai
	consumerRequirements (fun_expr @ exprs) ai
		# (cc_fun, ai) = consumerRequirements fun_expr ai
		  ai_class_subst = unifyClassifications cActive cc_fun ai.ai_class_subst
		= consumerRequirements exprs { ai & ai_class_subst = ai_class_subst }
	consumerRequirements (Let {let_binds,let_expr}) ai=:{ai_next_var,ai_heap}
		# (new_next_var, ai_heap) = init_variables let_binds ai_next_var ai_heap
		# ai = acc_requirements_of_let_binds let_binds ai_next_var { ai & ai_next_var = new_next_var, ai_heap = ai_heap }
		= consumerRequirements let_expr ai
		where
			init_variables [{bind_dst={fv_info_ptr}} : binds] ai_next_var ai_heap
				= init_variables binds (inc ai_next_var) (write_ptr fv_info_ptr (VI_AccVar ai_next_var) ai_heap "init_variables")
			init_variables [] ai_next_var ai_heap
				= (ai_next_var, ai_heap)
				
			acc_requirements_of_let_binds [ {bind_src, bind_dst={fv_info_ptr}} : binds ] ai_next_var ai
				# (bind_var, ai) = consumerRequirements bind_src ai
		  		  ai_class_subst = unifyClassifications ai_next_var bind_var ai.ai_class_subst
				= acc_requirements_of_let_binds binds (inc ai_next_var) { ai & ai_class_subst = ai_class_subst }
			acc_requirements_of_let_binds [] ai_next_var ai
				= ai
				
	consumerRequirements (Case case_expr) ai
		= consumerRequirements case_expr ai
	consumerRequirements (BasicExpr _ _) ai
		= (cPassive, ai)
	consumerRequirements (MatchExpr _ _ expr) ai
		= consumerRequirements expr ai
	consumerRequirements (Selection _ expr selectors) ai
		# (cc, ai) = consumerRequirements expr ai
		  ai_class_subst = unifyClassifications cActive cc ai.ai_class_subst
		  ai = requirementsOfSelectors selectors { ai & ai_class_subst = ai_class_subst }
		= (cPassive, ai)
	consumerRequirements (Update expr1 selectors expr2) ai
		# (cc, ai) = consumerRequirements expr1 ai
		  ai = requirementsOfSelectors selectors ai
		  (cc, ai) = consumerRequirements expr2 ai
		= (cPassive, ai)
	consumerRequirements (RecordUpdate cons_symbol expression expressions) ai
		# (cc, ai) = consumerRequirements expression ai
		  (cc, ai) = consumerRequirements expressions ai
		= (cPassive, ai)
	consumerRequirements (TupleSelect tuple_symbol arg_nr expr) ai
		= consumerRequirements expr ai
	consumerRequirements (AnyCodeExpr _ _ _) ai
		= (cPassive, ai)
	consumerRequirements (ABCCodeExpr _ _) ai
		= (cPassive, ai)
	consumerRequirements (DynamicExpr dynamic_expr) ai
		= consumerRequirements dynamic_expr ai
	consumerRequirements (TypeCodeExpression _) ai
		= (cPassive, ai)
	consumerRequirements EE ai
		= (cPassive, ai)
	consumerRequirements expr ai
		= abort ("consumerRequirements " <<- expr)

requirementsOfSelectors selectors ai
	= foldSt reqs_of_selector selectors ai
where
	reqs_of_selector (ArraySelection _ _ index_expr) ai
		# (_, ai) = consumerRequirements index_expr ai
		= ai
	reqs_of_selector (DictionarySelection dict_var _ _ index_expr) ai
		# (_, ai) = consumerRequirements index_expr ai
		  (cc_var, ai) = consumerRequirements dict_var ai
		= { ai & ai_class_subst = unifyClassifications cActive cc_var ai.ai_class_subst }
	reqs_of_selector _ ai
		= ai
			
instance consumerRequirements App where
	consumerRequirements {app_symb={symb_kind = SK_Function {glob_module,glob_object}, symb_arity, symb_name}, app_args} ai=:{ai_cons_class}
		| glob_module == cIclModIndex
			| glob_object < size ai_cons_class
				#! fun_class = ai_cons_class.[glob_object]
				= reqs_of_args fun_class.cc_args app_args cPassive ai
				= consumerRequirements app_args ai
			= consumerRequirements app_args ai
	where
		reqs_of_args _ [] cumm_arg_class ai
			= (cumm_arg_class, ai)
		reqs_of_args [] _ cumm_arg_class ai
			= (cumm_arg_class, ai)
		reqs_of_args [form_cc : ccs] [arg : args] cumm_arg_class ai
			# (act_cc, ai) = consumerRequirements arg ai
			  ai_class_subst = unifyClassifications form_cc act_cc ai.ai_class_subst
			= reqs_of_args ccs args (combineClasses act_cc cumm_arg_class) { ai & ai_class_subst = ai_class_subst }
/*
	consumerRequirements {app_symb={symb_kind = SK_InternalFunction _}, app_args=[arg:_]} ai
		# (cc, ai) = consumerRequirements arg ai
		  ai_class_subst = unifyClassifications cActive cc ai.ai_class_subst
		= (cPassive, { ai & ai_class_subst = ai_class_subst })
*/
	consumerRequirements {app_args} ai
		=  consumerRequirements app_args ai

instance consumerRequirements Case where
	consumerRequirements {case_expr,case_guards,case_default} ai
		# (cce, ai) = consumerRequirements case_expr ai
//		  ai_class_subst = unifyClassifications cActive cce ai.ai_class_subst
		  (ccgs, ai) = consumerRequirements (case_guards,case_default) ai //{ ai & ai_class_subst = ai_class_subst }
		= (ccgs, ai)

instance consumerRequirements DynamicExpr where
	consumerRequirements {dyn_expr} ai
		= consumerRequirements dyn_expr ai

/*
instance consumerRequirements TypeCase where
	consumerRequirements {type_case_dynamic,type_case_patterns,type_case_default} ai
		# (_, ai) = consumerRequirements type_case_dynamic ai
		  (ccgs, ai) = consumerRequirements (type_case_patterns,type_case_default) ai
		= (ccgs, ai)
*/

instance consumerRequirements DynamicPattern where
	consumerRequirements {dp_rhs} ai
		= consumerRequirements dp_rhs ai

instance consumerRequirements CasePatterns where
	consumerRequirements (AlgebraicPatterns type patterns) ai
		= consumerRequirements patterns ai
	consumerRequirements (BasicPatterns type patterns) ai
		= consumerRequirements patterns ai
	consumerRequirements (DynamicPatterns dyn_patterns) ai
		= consumerRequirements dyn_patterns ai
	
instance consumerRequirements AlgebraicPattern where
	consumerRequirements {ap_vars,ap_expr} ai=:{ai_heap}
		# ai_heap = bind_pattern_vars ap_vars ai_heap
		= consumerRequirements ap_expr { ai & ai_heap = ai_heap }
	where
		bind_pattern_vars [{fv_info_ptr,fv_count} : vars] var_heap
			| fv_count > 0
				= bind_pattern_vars vars (write_ptr fv_info_ptr (VI_AccVar cPassive) var_heap "bind_pattern_vars")
				= bind_pattern_vars vars var_heap
		bind_pattern_vars [] var_heap
			= var_heap

instance consumerRequirements BasicPattern where
	consumerRequirements {bp_expr} ai
		= consumerRequirements bp_expr ai

instance consumerRequirements (Optional a) | consumerRequirements a where
	consumerRequirements (Yes x) ai
		= consumerRequirements x ai
	consumerRequirements No ai
		= (cPassive, ai)

instance consumerRequirements (!a,!b) | consumerRequirements a & consumerRequirements b where
	consumerRequirements (x, y) ai
		# (ccx, ai) = consumerRequirements x ai
		  (ccy, ai) = consumerRequirements y ai
		= (combineClasses ccx ccy, ai)
		
instance consumerRequirements [a] | consumerRequirements a where
	consumerRequirements [x : xs] ai
		# (ccx, ai) = consumerRequirements x ai
		  (ccxs, ai) = consumerRequirements xs ai
		= (combineClasses ccx ccxs, ai)
	consumerRequirements [] ai
		= (cPassive, ai)

instance consumerRequirements (Bind a b) | consumerRequirements a where
	consumerRequirements {bind_src} ai
		= consumerRequirements bind_src ai

analyseGroups :: !*{! Group} !*{#FunDef} !*VarHeap -> (!*{! ConsClasses}, !*{! Group}, !*{#FunDef}, !*VarHeap)
analyseGroups groups fun_defs var_heap
	#! nr_of_funs = size fun_defs
	= analyse_groups 0 groups var_heap (createArray nr_of_funs { cc_size = 0, cc_args = [] }) fun_defs
where	
	analyse_groups group_nr groups var_heap class_env fun_defs
		| group_nr == size groups
			= (class_env, groups, fun_defs, var_heap)
			#! fun_indexes = groups.[group_nr]
			# (class_env, fun_defs, var_heap) = analyse_group fun_indexes.group_members var_heap class_env fun_defs
			= analyse_groups (inc group_nr) groups var_heap class_env fun_defs

	analyse_group group var_heap class_env fun_defs
		# (nr_of_vars, nr_of_local_vars, var_heap, class_env, fun_defs) = initial_cons_class group 0 0 var_heap class_env fun_defs
		  initial_subst = createArray (nr_of_vars + nr_of_local_vars) cPassive
		  (ai, fun_defs) = analyse_functions group { ai_heap = var_heap, ai_cons_class = class_env,
		  											 ai_class_subst = initial_subst, ai_next_var = nr_of_vars } fun_defs
		  class_env = collect_classifications group ai.ai_cons_class ai.ai_class_subst
		= (class_env, fun_defs, ai.ai_heap)
		
	
	initial_cons_class [fun : funs] next_var_number nr_of_local_vars var_heap class_env fun_defs
		#! fun_def = fun_defs.[fun]
		#  (TransformedBody {tb_args}) = fun_def.fun_body
		   (fresh_vars, next_var_number, var_heap) = fresh_variables tb_args next_var_number var_heap
		= initial_cons_class funs next_var_number (length fun_def.fun_info.fi_local_vars + nr_of_local_vars) var_heap
			{ class_env & [fun] = { cc_size = 0, cc_args = fresh_vars }} fun_defs
	initial_cons_class [] next_var_number nr_of_local_vars var_heap class_env fun_defs
		= (next_var_number, nr_of_local_vars, var_heap, class_env, fun_defs)
		
	fresh_variables [{fv_name,fv_info_ptr} : vars] next_var_number var_heap
		# (fresh_vars, last_var_number, var_heap) = fresh_variables vars (inc next_var_number) var_heap
		  var_heap = write_ptr fv_info_ptr (VI_AccVar next_var_number) var_heap "fresh_variables"
		= ([next_var_number : fresh_vars], last_var_number, var_heap)
	fresh_variables [] next_var_number var_heap
		= ([], next_var_number, var_heap)

	analyse_functions [fun : funs] ai fun_defs
		#! fun_def = fun_defs.[fun]
		#  (TransformedBody {tb_rhs}) = fun_def.fun_body
		   (_, ai) = consumerRequirements tb_rhs ai
		= analyse_functions funs ai fun_defs
	analyse_functions [] ai fun_defs
		= (ai, fun_defs)

	collect_classifications [] class_env class_subst
		= class_env
	collect_classifications [fun : funs] class_env class_subst
		#! fun_class = class_env.[fun]
		= collect_classifications funs { class_env & [fun] = determine_classification fun_class.cc_args class_subst } class_subst
	where
		determine_classification cc class_subst
			# (cc_size, cc_args) = mapAndLength (skip_indirections class_subst) cc
			= { cc_size = cc_size, cc_args = cc_args }

		skip_indirections class_subst cc
			| IsAVariable cc
				= skip_indirections class_subst class_subst.[cc]
				= cc

mapAndLength f [x : xs]
	#! x = f x
	   (length, xs) = mapAndLength f xs
	=  (inc length, [x : xs])
mapAndLength f []
	= (0, [])
	
::	*TransformInfo =
	{	ti_fun_defs			:: !*{# FunDef}
	,	ti_instances 		:: !*{! InstanceInfo }
	,	ti_cons_args 		:: !{! ConsClasses}
	,	ti_new_functions 	:: ![FunctionInfoPtr]
	,	ti_fun_heap			:: !*FunctionHeap
	,	ti_var_heap			:: !*VarHeap
	,	ti_symbol_heap		:: !*ExpressionHeap
	,	ti_type_heaps		:: !*TypeHeaps
	,	ti_next_fun_nr		:: !Index
	}

class transform a :: !a !{# {# FunType} } !TransformInfo -> (!a, !TransformInfo)

instance transform Expression
where
	transform expr=:(App app=:{app_symb,app_args}) imported_funs ti
		# (app_args, ti) = transform app_args imported_funs ti
		= transformApplication { app & app_args = app_args } [] imported_funs ti
	transform appl_expr=:(expr @ exprs) imported_funs ti
		# (expr, ti) = transform expr imported_funs ti
		  (exprs, ti) = transform exprs imported_funs ti
		= case expr of
			App app
				-> transformApplication app exprs imported_funs ti
			_
				-> (expr @ exprs, ti)
	transform (Let lad=:{let_binds, let_expr}) imported_funs ti
		# (let_binds, ti) = transform let_binds imported_funs ti
		  (let_expr, ti) = transform let_expr imported_funs ti
		= (Let { lad & let_binds = let_binds, let_expr = let_expr}, ti)
	transform (Case case_expr) imported_funs ti
//		= transformCase case_expr imported_funs ti
		# (case_expr, ti) = transform case_expr imported_funs ti
		= (Case case_expr, ti)
	transform (Selection opt_type expr selectors) imported_funs ti
		# (expr, ti) = transform expr imported_funs ti
		= transformSelection opt_type selectors expr ti
	transform (DynamicExpr dynamic_expr) imported_funs ti
		# (dynamic_expr, ti) = transform dynamic_expr imported_funs ti
		= (DynamicExpr dynamic_expr, ti)
	transform expr imported_funs ti
		= (expr, ti)

neverMatchingCase = { case_expr = EE, case_guards = NoPattern, case_default = No, case_ident = No, case_info_ptr = nilPtr }

instance transform Case
where
	transform kees=:{case_expr, case_guards, case_default} imported_funs ti
		# (case_expr, ti) = transform case_expr imported_funs ti
		  (case_guards, ti) = transform case_guards imported_funs ti
		  (case_default, ti) = transform case_default imported_funs ti
		= ({kees & case_expr = case_expr, case_guards = case_guards, case_default = case_default}, ti)

instance transform DynamicExpr where
	transform dyn=:{dyn_expr} imported_funs ti
		# (dyn_expr, ti) = transform dyn_expr imported_funs ti
		= ({dyn & dyn_expr = dyn_expr}, ti)

instance transform DynamicPattern where
	transform dp=:{dp_rhs} imported_funs ti
		# (dp_rhs, ti) = transform dp_rhs imported_funs ti
		= ({ dp & dp_rhs = dp_rhs }, ti)

/*		
transformCase :: !Case !*TransformInfo -> *(!Expression, !*TransformInfo)
transformCase this_case=:{case_expr,case_guards,case_default,case_ident} imported_funs ti
	= case case_expr of
		Case case_in_case
	  		-> lift_case case_in_case case_guards case_default case_ident ti
	  	App {app_symb,app_args}
	  		-> case app_symb.symb_kind of
	  			SK_Constructor cons_index
					# (may_be_match_expr, ti) = match_and_instantiate cons_index app_args case_guards case_default ti
					-> case may_be_match_expr of
						Yes match_expr
							-> (match_expr, ti)
						No
							-> (Case neverMatchingCase, ti)
	  			_
	  				# (may_be_unfolded_expr, ti) = tryToUnfoldExpression app_symb app_args ti
	  				-> case may_be_unfolded_expr of
	  					(Yes unfolded_expr)
	  						-> transformCase {this_case & case_expr = unfolded_expr } ti
	  					No
							# (this_case, ti) = transform this_case ti
							-> (Case this_case, ti)
	  	_
			# (this_case, ti) = transform this_case ti
			-> (Case this_case, ti)

where
	lift_case :: !Case ![PatternExpression] !(Optional Expression) !(Optional Ident) !*TransformInfo -> *(!Expression, !*TransformInfo)
	lift_case nested_case=:{case_guards,case_default} outer_guards outer_default outer_ident ti
		# (case_guards, ti) = lift_patterns case_guards outer_guards outer_default outer_ident ti
		  (case_default, ti) = lift_default case_default outer_guards outer_default outer_ident ti
		= (Case {nested_case & case_guards = case_guards, case_default = case_default}, ti)

	lift_patterns :: ![PatternExpression] ![PatternExpression] !(Optional Expression) !(Optional Ident) !*TransformInfo -> *(![PatternExpression], !*TransformInfo)
	lift_patterns [guard=:{guard_expr}] outer_guards outer_default outer_ident ti
		# (guard_expr, ti) = transformCase {case_expr = guard_expr,case_guards = outer_guards,case_default = outer_default, case_ident = outer_ident} ti
		= ([{guard & guard_expr = guard_expr}], ti)
	lift_patterns [guard=:{guard_expr} : nested_guards] outer_guards outer_default outer_ident ti=:{ti_var_heap}
		# (outer_guards, ti_var_heap) = copy_guards outer_guards ti_var_heap
		# (guard_expr, ti) = transformCase {case_expr = guard_expr,case_guards = outer_guards,case_default = outer_default, case_ident = outer_ident} { ti & ti_var_heap = ti_var_heap }
		  (nested_guards, ti) = lift_patterns nested_guards outer_guards outer_default outer_ident ti
		= ([{guard & guard_expr = guard_expr} : nested_guards], ti)
	lift_patterns [] outer_guards outer_default outer_ident ti
		= ([], ti)
		
	copy_guards [guard : guards] var_heap
		# (guard, _, var_heap) = unfold guard 0 var_heap
		  (guards, var_heap) = copy_guards guards var_heap
		= ([ guard : guards ], var_heap)
	copy_guards [] var_heap
		= ([], var_heap)
	
	lift_default :: !(Optional Expression) ![PatternExpression] !(Optional Expression) !(Optional Ident) !*TransformInfo -> *(!Optional Expression, !*TransformInfo)
	lift_default (Yes default_expr) outer_guards outer_default outer_ident ti
		# (default_expr, ti) = transformCase {case_expr = default_expr, case_guards = outer_guards, case_default = outer_default, case_ident = outer_ident} ti
		= (Yes default_expr, ti)
	lift_default No outer_guards outer_default outer_ident ti
		= (No, ti)
		
	match_and_instantiate :: !(Global Index) ![Expression] ![PatternExpression] !(Optional Expression) !*TransformInfo -> *(!Optional Expression, !*TransformInfo)
	match_and_instantiate cons_index app_args [{guard_pattern = AlgebraicPattern {glob_module,glob_object={ds_index}} vars, guard_expr} : guards]
			case_default ti
		| cons_index.glob_module == glob_module && cons_index.glob_object == ds_index
			# (unfolded_guard_expr, _, ti_var_heap) = unfold guard_expr 0 (bindVariables vars app_args  ti.ti_var_heap)
			  (guard_expr, ti) = transform unfolded_guard_expr { ti & ti_var_heap = ti_var_heap }
			= (Yes guard_expr, ti)
			= match_and_instantiate cons_index app_args guards case_default ti
	match_and_instantiate cons_index app_args [guard : guards] case_default ti
		= match_and_instantiate cons_index app_args guards case_default ti
	match_and_instantiate cons_index app_args [] default_expr ti
		= transform default_expr ti

		
tryToUnfoldExpression :: !SymbIdent ![Expression] !*TransformInfo -> *(!Optional Expression, ! *TransformInfo)
tryToUnfoldExpression {symb_kind = SK_Function {glob_module,glob_object},symb_arity} app_args ti=:{ti_fun_defs, ti_var_heap, ti_symbol_heap}
	| glob_module == cIclModIndex
		#! fd = ti_fun_defs.[glob_object]
		| fd.fun_arity == symb_arity
			# (expr, ti_var_heap, ti_symbol_heap) = unfoldFunction fd.fun_body app_args ti_var_heap ti_symbol_heap
			= (Yes expr, { ti & ti_var_heap = ti_var_heap, ti_symbol_heap = ti_symbol_heap})
			= (No, ti)
		= (No, ti)
tryToUnfoldExpression {symb_kind = SK_GeneratedFunction fun_ptr fun_index,symb_arity} app_args ti=:{ti_fun_heap, ti_var_heap, ti_symbol_heap}
	#! fun_info = sreadPtr fun_ptr ti_fun_heap
	# (FI_Function {gf_fun_def}) = fun_info
	| gf_fun_def.fun_arity == symb_arity
		# (expr, ti_var_heap, ti_symbol_heap) = unfoldFunction gf_fun_def.fun_body app_args ti_var_heap ti_symbol_heap
		= (Yes expr, { ti & ti_var_heap = ti_var_heap, ti_symbol_heap = ti_symbol_heap })
		= (No, ti)
tryToUnfoldExpression expr app_args ti
	= (No, ti)

unfoldFunction :: !FunctionBody ![Expression] !*VarHeap !*ExpressionHeap -> (!Expression, !*VarHeap, !*ExpressionHeap)
unfoldFunction (TransformedBody {tb_args,tb_rhs}) act_args var_heap symbol_heap
	# var_heap = foldr2 (\{fv_info_ptr} arg -> writePtr fv_info_ptr (VI_Expression arg)) var_heap tb_args act_args
	# (unfolded_rhs, {us_var_heap,us_symbol_heap}) = unfold tb_rhs { us_var_heap = var_heap, us_symbol_heap = symbol_heap }
	= (unfolded_rhs, us_var_heap, us_symbol_heap)
*/

instance transform Bind a b | transform a
where
	transform bind=:{bind_src} imported_funs ti
		# (bind_src, ti) = transform bind_src imported_funs ti
		= ({ bind & bind_src = bind_src }, ti)

instance transform BasicPattern
where
	transform pattern=:{bp_expr} imported_funs ti
		# (bp_expr, ti) = transform bp_expr imported_funs ti
		= ({ pattern & bp_expr = bp_expr }, ti)

instance transform AlgebraicPattern
where
	transform pattern=:{ap_expr} imported_funs ti
		# (ap_expr, ti) = transform ap_expr imported_funs ti
		= ({ pattern & ap_expr = ap_expr }, ti)

instance transform CasePatterns
where
	transform (AlgebraicPatterns type patterns) imported_funs ti
		# (patterns, ti) = transform patterns imported_funs ti
		= (AlgebraicPatterns type patterns, ti)
	transform (BasicPatterns type patterns) imported_funs ti
		# (patterns, ti) = transform patterns imported_funs ti
		= (BasicPatterns type patterns, ti)
	transform (DynamicPatterns patterns) imported_funs ti
		# (patterns, ti) = transform patterns imported_funs ti
		= (DynamicPatterns patterns, ti)

instance transform Optional a | transform a
where
	transform (Yes x) imported_funs ti
		# (x, ti) = transform x imported_funs ti
		= (Yes x, ti)
	transform no imported_funs ti
		= (no, ti)

instance transform [a] | transform a
where
	transform [x : xs]  imported_funs ti
		# (x, ti) = transform x imported_funs ti
		  (xs, ti) = transform xs imported_funs ti
		= ([x : xs], ti)
	transform [] imported_funs ti
		= ([], ti)

compareProducers prods1 prods2
	#! nr_of_prods = size prods1
	= compare_producers 0 nr_of_prods prods1 prods2
where
	compare_producers prod_index nr_of_prods prods1 prods2
		| prod_index == nr_of_prods
			= Equal
			# cmp = prods1.[prod_index] =< prods2.[prod_index]
			| cmp == Equal
				= compare_producers (inc prod_index) nr_of_prods prods1 prods2
				= cmp

instance =< Producer
where
	(=<) pr1 pr2
		| equal_constructor pr1 pr2
			= compare_constructor_arguments  pr1 pr2
		| less_constructor pr1 pr2
			= Smaller
			= Greater
	where
		compare_constructor_arguments (PR_Function _ index1) (PR_Function _ index2)
			= index1 =< index2
		compare_constructor_arguments (PR_GeneratedFunction _ index1) (PR_GeneratedFunction _ index2)
			= index1 =< index2
		compare_constructor_arguments (PR_Class app1 _ _) (PR_Class app2 _ _) 
			= app1.app_args =< app2.app_args
		compare_constructor_arguments _ _
			= Equal

cIsANewFunction		:== True
cIsNotANewFunction	:== False

tryToFindInstance :: !{! Producer} !InstanceInfo !*(Heap FunctionInfo) -> (!Bool, !FunctionInfoPtr, !InstanceInfo, !.FunctionHeap)
tryToFindInstance new_prods II_Empty fun_heap
	# (fun_def_ptr, fun_heap) = newPtr FI_Empty fun_heap
	= (cIsANewFunction, fun_def_ptr, II_Node new_prods fun_def_ptr II_Empty II_Empty, fun_heap)
tryToFindInstance new_prods instances=:(II_Node prods fun_def_ptr left right) fun_heap
	# cmp = compareProducers new_prods prods
	| cmp == Equal
		= (cIsNotANewFunction, fun_def_ptr, instances, fun_heap)
	| cmp == Greater
		# (is_new, new_fun_def_ptr, right, fun_heap) = tryToFindInstance new_prods right fun_heap
		= (is_new, new_fun_def_ptr, II_Node prods fun_def_ptr left right, fun_heap)
		# (is_new, new_fun_def_ptr, left, fun_heap) = tryToFindInstance new_prods left fun_heap
		= (is_new, new_fun_def_ptr, II_Node prods fun_def_ptr left right, fun_heap)


generateFunction :: !FunDef ![Int] !{! Producer} !FunctionInfoPtr !{# {# FunType} } !*TransformInfo -> (!Index, !Int, !*TransformInfo)
generateFunction fd=:{fun_body = TransformedBody {tb_args,tb_rhs},fun_info = info =: {fi_group_index}} cc_args prods fun_def_ptr
			imported_funs ti=:{ti_var_heap,ti_next_fun_nr,ti_new_functions,ti_fun_heap,ti_symbol_heap,ti_fun_defs,ti_type_heaps,ti_cons_args}
	#! fi_group_index = max_group_index 0 prods fi_group_index ti_fun_defs ti_fun_heap ti_cons_args
	# (Yes fun_type=:{st_vars,st_attr_vars,st_args,st_result}) = fd.fun_type
	
	  th_vars = foldSt (\tv type_var_heap -> type_var_heap <:= (tv.tv_info_ptr, TVI_Type (TV tv))) st_vars ti_type_heaps.th_vars 
	  th_attrs = foldSt (\av attr_var_heap -> attr_var_heap <:= (av.av_info_ptr, AVI_Attr (TA_Var av))) st_attr_vars ti_type_heaps.th_attrs 

	  (new_fun_args, new_arg_types, new_cons_args, th_vars, ti_var_heap) = determine_args cc_args 0 prods tb_args st_args th_vars ti_var_heap

	  (fresh_arg_types, ti_type_heaps) = substitute new_arg_types { ti_type_heaps & th_vars = th_vars, th_attrs = th_attrs }
	  (fresh_result_type, ti_type_heaps) = substitute st_result ti_type_heaps

	  new_gen_fd = { gf_fun_def = { fd & fun_body = Expanding, fun_info = { info & fi_group_index = fi_group_index }},
	  					gf_instance_info = II_Empty,
	  					gf_fun_index = ti_next_fun_nr, gf_cons_args = {cc_args = new_cons_args, cc_size = length new_cons_args} }
	  ti_fun_heap = writePtr fun_def_ptr (FI_Function new_gen_fd) ti_fun_heap

	  (tb_rhs, {us_var_heap,us_symbol_heap}) = unfold tb_rhs { us_var_heap = ti_var_heap, us_symbol_heap = ti_symbol_heap }

	  (new_fun_rhs, ti) = transform tb_rhs imported_funs { ti & ti_var_heap = us_var_heap, ti_fun_heap = ti_fun_heap, ti_symbol_heap = us_symbol_heap,
	  			ti_next_fun_nr = inc ti_next_fun_nr, ti_new_functions = [fun_def_ptr : ti_new_functions], ti_type_heaps = ti_type_heaps }
	  fun_arity = length new_fun_args
	  new_fd = { fd & fun_body = TransformedBody {tb_args = new_fun_args, tb_rhs = new_fun_rhs}, fun_arity = fun_arity, fun_index = ti_next_fun_nr,
	  				fun_type = Yes { fun_type & st_args = fresh_arg_types, st_result = fresh_result_type }}
	= (ti_next_fun_nr, fun_arity, { ti & ti_fun_heap = ti.ti_fun_heap <:= (fun_def_ptr, FI_Function { new_gen_fd & gf_fun_def = new_fd })})
where
	determine_args [] prod_index producers forms types type_var_heap var_heap
		# (vars, var_heap) = new_variables forms var_heap
		= (vars, types, [], type_var_heap, var_heap)
	determine_args [cons_arg : cons_args ] prod_index producers [form : forms] [type : types] type_var_heap var_heap
		| cons_arg == cActive
			# new_args = determine_args cons_args (inc prod_index) prods forms types type_var_heap var_heap
			= determine_arg producers.[prod_index] form type new_args
			# (vars, types, new_cons_args, type_var_heap, var_heap) = determine_args cons_args prod_index prods forms types type_var_heap var_heap
			  (new_info_ptr, var_heap) = newPtr VI_Empty var_heap
			= ([{ form & fv_info_ptr = new_info_ptr } : vars], [type : types], [cons_arg : new_cons_args], type_var_heap, 
					var_heap <:= (form.fv_info_ptr, VI_Variable form.fv_name new_info_ptr))
	where
/*
		build_var_args new_name arity form_vars act_vars var_heap
			| arity == 0
				= (form_vars, act_vars, var_heap)
				# (info_ptr, var_heap) = newPtr VI_Empty var_heap
				  form_var = { fv_name = new_name, fv_info_ptr = info_ptr, fv_count = 0, fv_def_level = NotALevel }
				  act_var = { var_name = new_name, var_info_ptr = info_ptr, var_expr_ptr = nilPtr }
				= build_var_args new_name (dec arity) [form_var : form_vars] [Var act_var : act_vars] var_heap
*/		
		determine_arg PR_Empty form=:{fv_name,fv_info_ptr} type (vars, types, new_cons_args, type_var_heap, var_heap)
			# (new_info_ptr, var_heap) = newPtr VI_Empty var_heap
			= ([{ form & fv_info_ptr = new_info_ptr } : vars], [ type : types ], [cActive : new_cons_args], type_var_heap,
					var_heap <:= (fv_info_ptr, VI_Variable fv_name new_info_ptr))
/*
		determine_arg (PR_Function symbol _) vars {fv_info_ptr,fv_name} new_cons_args var_heap
			# (form_vars, act_vars, var_heap) = build_var_args fv_name symbol.symb_arity vars [] var_heap
			= (form_vars, writePtr fv_info_ptr (
						VI_Expression (App { app_symb = symbol, app_args = act_vars, app_info_ptr = nilPtr })) var_heap)
		determine_arg (PR_GeneratedFunction symbol _) vars {fv_info_ptr,fv_name} var_heap
			# (form_vars, act_vars, var_heap) = build_var_args fv_name symbol.symb_arity vars [] var_heap
			= (form_vars, writePtr fv_info_ptr (
						VI_Expression (App { app_symb = symbol, app_args = act_vars, app_info_ptr = nilPtr  })) var_heap)
*/
		determine_arg (PR_Class class_app free_vars class_types) {fv_info_ptr,fv_name} type (vars, types, new_cons_args, type_var_heap, var_heap)
			= (mapAppend (\{var_info_ptr,var_name} -> {	fv_name = var_name, fv_info_ptr = var_info_ptr, fv_def_level = NotALevel, fv_count = 0 }) free_vars vars,
		        	mapAppend (\_ -> { at_attribute = TA_Multi, at_annotation = AN_None, at_type = TE }) free_vars types,
				        mapAppend (\_ -> cActive) free_vars new_cons_args,
				        	bind_class_types type.at_type class_types type_var_heap,
								var_heap <:= (fv_info_ptr, VI_Expression (App class_app)))
		
		bind_class_types (TA _ context_types) instance_types type_var_heap
			= bind_context_types context_types instance_types type_var_heap
		where
			bind_context_types [atype : atypes] [type : types] type_var_heap
				= bind_context_types atypes types (bind_type atype.at_type type type_var_heap)
			bind_context_types [] [] type_var_heap
				= type_var_heap
		bind_class_types _ _ type_var_heap
			= type_var_heap
			
		bind_type (TV {tv_info_ptr}) type type_var_heap
			= type_var_heap <:= (tv_info_ptr, TVI_Type type)
		bind_type (TA _ arg_types1) (TA _ arg_types2) type_var_heap
			= bind_types arg_types1 arg_types2 type_var_heap
		bind_type _ _ type_var_heap
			= type_var_heap
		
		bind_types [type1 : types1] [type2 : types2] type_var_heap
			= bind_types types1 types2 (bind_type type1.at_type type2.at_type type_var_heap)
		bind_types [] [] type_var_heap
			= type_var_heap
		
	new_variables [] var_heap
		= ([], var_heap)
	new_variables [form=:{fv_name,fv_info_ptr}:forms] var_heap
		# (vars, var_heap) = new_variables forms var_heap
		  (new_info_ptr, var_heap) = newPtr VI_Empty var_heap
		= ([{ form & fv_info_ptr = new_info_ptr } : vars], writePtr fv_info_ptr (VI_Variable fv_name new_info_ptr) var_heap)

	max_group_index prod_index producers current_max fun_defs fun_heap cons_args
		| prod_index == size producers
			= current_max
			# current_max = max_group_index_of_producer producers.[prod_index] current_max fun_defs fun_heap cons_args
			= max_group_index (inc prod_index) producers current_max fun_defs fun_heap cons_args

	max_group_index_of_producer PR_Empty current_max fun_defs fun_heap cons_args
		= current_max
	max_group_index_of_producer (PR_Class {app_args} _ _) current_max fun_defs fun_heap cons_args
		= max_group_index_of_members app_args current_max fun_defs fun_heap cons_args
	max_group_index_of_producer prod current_max fun_defs fun_heap cons_args
		= abort ("trans.icl: max_group_index_of_producer" ---> prod)

	max_group_index_of_member fun_defs fun_heap cons_args current_max (App {app_symb = {symb_name, symb_kind = SK_Function { glob_object = fun_index, glob_module = mod_index}}}) 
		| mod_index == cIclModIndex
			| fun_index < size cons_args
				# {fun_info = {fi_group_index}} = fun_defs.[fun_index]
				= max fi_group_index current_max
			= current_max
		= current_max
	max_group_index_of_member fun_defs fun_heap cons_args current_max (App {app_symb = {symb_kind = SK_GeneratedFunction fun_ptr fun_index }})
		# (FI_Function {gf_fun_def={fun_info = {fi_group_index}}}) = sreadPtr fun_ptr fun_heap
		= max fi_group_index current_max
	max_group_index_of_member fun_defs fun_heap cons_args current_max (App {app_symb = {symb_kind = SK_Constructor _}, app_args}) 
		= max_group_index_of_members app_args current_max fun_defs fun_heap cons_args
	
	max_group_index_of_members members current_max fun_defs fun_heap cons_args
		= foldl (max_group_index_of_member fun_defs fun_heap cons_args) current_max members
			

transformFunctionApplication fun_def instances {cc_size, cc_args} app=:{app_symb,app_args} extra_args imported_funs ti
	# (app_symb, app_args, extra_args) = complete_application app_symb fun_def.fun_arity app_args extra_args
	| cc_size > 0
	  	# (producers, new_args, ti) = determineProducers cc_args app_args 0 (createArray cc_size PR_Empty) ti
	  	| containsProducer cc_size producers
	  		# (is_new, fun_def_ptr, instances, ti_fun_heap) = tryToFindInstance producers instances ti.ti_fun_heap
	  		| is_new
	  			# (fun_index, fun_arity, ti) = generateFunction fun_def cc_args producers fun_def_ptr imported_funs
	  					(update_instance_info app_symb.symb_kind instances { ti & ti_fun_heap = ti_fun_heap })
	  			  app_symb = { app_symb & symb_kind = SK_GeneratedFunction fun_def_ptr fun_index, symb_arity = length new_args}
				  (app_symb, app_args, extra_args) = complete_application app_symb fun_arity new_args extra_args
	  			= (build_application { app & app_symb = app_symb, app_args = app_args } extra_args, ti)
	  			# (FI_Function {gf_fun_index, gf_fun_def}, ti_fun_heap) = readPtr fun_def_ptr ti_fun_heap
	  			  app_symb = { app_symb & symb_kind = SK_GeneratedFunction fun_def_ptr gf_fun_index, symb_arity = length new_args}
				  (app_symb, app_args, extra_args) = complete_application app_symb gf_fun_def.fun_arity new_args extra_args
	  			= (build_application { app & app_symb = app_symb, app_args = app_args } extra_args, {ti & ti_fun_heap = ti_fun_heap })
			= (build_application { app & app_symb = app_symb, app_args = app_args } extra_args, ti)
		= (build_application { app & app_symb = app_symb, app_args = app_args } extra_args, ti)
where
	update_instance_info (SK_Function {glob_object}) instances ti=:{ti_instances}
		 = { ti & ti_instances = { ti_instances & [glob_object] = instances } }
	update_instance_info (SK_GeneratedFunction fun_def_ptr _) instances ti=:{ti_fun_heap}
		# (FI_Function fun_info, ti_fun_heap) = readPtr fun_def_ptr ti_fun_heap
		= { ti & ti_fun_heap = ti_fun_heap <:= (fun_def_ptr, FI_Function { fun_info & gf_instance_info = instances })}

	complete_application symb form_arity args []
		= (symb, args, [])
	complete_application symb=:{symb_arity} form_arity args extra_args
		# arity_diff = min (form_arity - symb_arity) (length extra_args)
		= ({ symb & symb_arity = symb_arity + arity_diff }, args ++ take arity_diff extra_args, drop arity_diff extra_args)

	build_application app []
		= App app
	build_application app extra_args
		= App app @ extra_args
		
transformApplication :: !App ![Expression] !{# {# FunType} } !*TransformInfo -> *(!Expression,!*TransformInfo)
transformApplication app=:{app_symb=symb=:{symb_kind = SK_Function {glob_module, glob_object},symb_arity}, app_args} extra_args
	imported_funs ti=:{ti_cons_args,ti_instances,ti_fun_defs}
	| glob_module == cIclModIndex
		| glob_object < size ti_cons_args
			#! cons_class = ti_cons_args.[glob_object]
			   instances = ti_instances.[glob_object]
			   fun_def = ti_fun_defs.[glob_object]
			= transformFunctionApplication fun_def instances cons_class app extra_args imported_funs ti
// It seems as if we have an array function 
			| isEmpty extra_args
				= (App app, ti)
				= (App { app & app_symb = { symb & symb_arity = symb_arity + length extra_args}, app_args = app_args ++ extra_args}, ti)
// This function is imported
		| isEmpty extra_args
			= (App app, ti)
			# ar_diff = imported_funs.[glob_module].[glob_object].ft_arity - symb_arity
			  nr_of_extra_args = length extra_args
			| nr_of_extra_args <= ar_diff
				= (App {app  &  app_args = app_args ++ extra_args, app_symb = { symb & symb_arity = symb_arity + nr_of_extra_args }}, ti)
				= (App {app  &  app_args = app_args ++ take ar_diff extra_args, app_symb = { symb & symb_arity = symb_arity + ar_diff }} @
						drop ar_diff extra_args, ti)
				
transformApplication app=:{app_symb={symb_kind = SK_GeneratedFunction fun_def_ptr fun_index}} extra_args imported_funs ti=:{ti_fun_heap}
	# (FI_Function {gf_fun_def,gf_instance_info,gf_cons_args}, ti_fun_heap) = readPtr fun_def_ptr ti_fun_heap
	= transformFunctionApplication gf_fun_def gf_instance_info gf_cons_args app extra_args imported_funs { ti & ti_fun_heap = ti_fun_heap }
transformApplication app [] imported_funs ti
	= (App app, ti)
transformApplication app extra_args imported_funs ti
	= (App app @ extra_args, ti)

transformSelection opt_type [RecordSelection _ field_index : selectors] (App {app_symb={symb_kind= SK_Constructor _ }, app_args}) ti
	= transform_selections selectors (app_args !! field_index) ti
where
	transform_selections [] expr ti
		= (expr, ti)
	transform_selections [RecordSelection _ field_index : selectors] (App {app_symb={symb_kind= SK_Constructor _ }, app_args}) ti
		= transform_selections selectors (app_args !! field_index) ti
	transform_selections selectors expr ti
		= (Selection No expr selectors, ti)
transformSelection opt_type selectors expr ti
	= (Selection opt_type expr selectors, ti)

determineProducers :: ![Int] ![Expression] !Index !*{! Producer} !*TransformInfo -> (!*{! Producer},![Expression],!*TransformInfo)
determineProducers cons_args [] prod_index producers ti
	= (producers, [], ti)
determineProducers [ cons_arg : cons_args ] [ arg : args ] prod_index producers ti
	| cons_arg == cActive
		# (producers, new_args, ti) = determineProducers cons_args args (inc prod_index) producers ti
		= determine_producer arg new_args prod_index producers ti
		# (producers, new_args, ti) = determineProducers cons_args args prod_index producers ti
		= (producers, [arg : new_args], ti)
where
	determine_producer arg=:(App app=:{app_info_ptr}) new_args prod_index producers ti
		| isNilPtr app_info_ptr
			= (producers, [arg : new_args], ti)
			# (app_info, ti_symbol_heap) = readPtr app_info_ptr ti.ti_symbol_heap
			= determineProducer app  app_info new_args prod_index producers { ti & ti_symbol_heap = ti_symbol_heap }
	determine_producer arg new_args prod_index producers ti
		= (producers, [arg : new_args], ti)
		
determineProducer :: !App !ExprInfo ![Expression] !Index !*{! Producer} !*TransformInfo -> (!*{! Producer}, ![Expression], !*TransformInfo)
determineProducer app=:{app_symb = symb=:{symb_kind = SK_Constructor _}, app_args} (EI_ClassTypes types) new_args prod_index producers ti
	# (app_args, (new_vars, ti_var_heap)) = renewVariables app_args ([], ti.ti_var_heap)
	  (new_args, ti_var_heap) = mapAppendSt retrieve_old_var new_vars new_args ti_var_heap
	= ({ producers & [prod_index] = PR_Class { app & app_args = app_args } new_vars types}, new_args, { ti & ti_var_heap = ti_var_heap })
where
	retrieve_old_var {var_info_ptr} var_heap
		#! var_info = sreadPtr var_info_ptr var_heap
		# (VI_Forward var) = var_info
		= (Var var, writePtr var_info_ptr VI_Empty (writePtr var.var_info_ptr VI_Empty var_heap))
/*
determineProducer app=:{app_symb = symb=:{symb_kind = SK_Function { glob_module, glob_object }}, app_args} new_args prod_index producers ti
	| glob_module == cIclModIndex
		= ({ producers & [prod_index] = PR_Function symb glob_object}, app_args ++ new_args, ti)
		= (producers, [App app : new_args ], ti)
determineProducer app=:{app_symb = symb=:{ symb_kind = SK_GeneratedFunction _ fun_index}, app_args} new_args prod_index producers ti=:{ti_fun_heap}
	= ({ producers & [prod_index] = PR_GeneratedFunction symb fun_index }, app_args ++ new_args, ti)
determineProducer {app_symb = symb=:{symb_kind = SK_Constructor glob_index}, app_args} new_args prod_index producers ti
	= ({ producers & [prod_index] = PR_Constructor symb app_args}, new_args, ti)
*/
determineProducer app _ new_args _ producers ti
	= (producers, [App app : new_args ], ti)
	
		
/*
	verify_class_members [ App {app_symb, app_args} : mems]
		= verify_class_members app_args && verify_class_members mems
	verify_class_members [ _ : mems]
		= False
	verify_class_members []
		= True
	

	verify_function fun_nr act_arity ti=:{ti_fun_defs,ti_new_functions}
		| fun_nr < size ti_fun_defs
			#! fd = ti_fun_defs.[fun_nr]
			= (True, ti)
			= (verify_new_function fun_nr act_arity ti_new_functions, ti)
	where
		verify_new_function fun_nr act_arity [{nf_fun_def={fun_index,fun_arity}}:new_functions]
			| fun_nr == fun_index
				= True
				= verify_new_function fun_nr act_arity new_functions
		verify_new_function fun_nr _ []
			= False
/*
	verify_function fun_nr act_arity ti=:{ti_fun_defs,ti_new_functions}
		| fun_nr < size ti_fun_defs
			#! fd = ti_fun_defs.[fun_nr]
			= (fd.fun_arity > act_arity, ti)
			= (verify_new_function fun_nr act_arity ti_new_functions, ti)
	where
		verify_new_function fun_nr act_arity [{nf_fun_def={fun_index,fun_arity}}:new_functions]
			| fun_nr == fun_index
				= fun_arity > act_arity
				= verify_new_function fun_nr act_arity new_functions
		verify_new_function fun_nr _ []
			= False ---> fun_nr
*/
*/

containsProducer prod_index producers
	| prod_index == 0
		= False
		#! prod_index = dec prod_index
		= is_a_producer producers.[prod_index] || containsProducer prod_index producers
where
	is_a_producer PR_Empty	= False
	is_a_producer _ 		= True

class renewVariables a :: !a !(![BoundVar], !*VarHeap) -> (!a, !(![BoundVar], !*VarHeap))

instance renewVariables Expression
where
	renewVariables (Var var=:{var_info_ptr}) (new_vars, var_heap)
		#! var_info = sreadPtr var_info_ptr var_heap
		= case var_info of
			VI_Forward new_var
				-> (Var { var & var_info_ptr = new_var.var_info_ptr }, (new_vars, var_heap))
			_
				# (new_info_ptr, var_heap) = newPtr (VI_Forward var) var_heap
				  new_var = { var & var_info_ptr = new_info_ptr }
				  var_heap = writePtr var_info_ptr (VI_Forward new_var) var_heap
				-> (Var new_var, ([new_var : new_vars], var_heap))
	renewVariables (App app=:{app_args}) state
		# (app_args, state) = renewVariables app_args state
		= (App { app & app_args = app_args }, state)
	renewVariables expr state
		= (expr, state)
		
instance renewVariables [a] | renewVariables a
where
	renewVariables l state = mapSt renewVariables l state

::	ImportedConstructors	:== [Global Index]

transformGroups :: !*{! Group} !*{#FunDef} !{!.ConsClasses} !{# CommonDefs}  !{# {# FunType} } !*VarHeap !*TypeHeaps !*ExpressionHeap
	-> (!*{! Group}, !*{#FunDef}, !*{#{# CheckedTypeDef}}, !ImportedConstructors, !*VarHeap, !*TypeHeaps, !*ExpressionHeap)
transformGroups groups fun_defs cons_args common_defs imported_funs var_heap type_heaps symbol_heap
	#! nr_of_funs = size fun_defs
	# imported_types = {com_type_defs \\ {com_type_defs} <-: common_defs }
	  (groups, imported_types, collected_imports, {ti_fun_defs,ti_new_functions,ti_var_heap,ti_symbol_heap,ti_fun_heap,ti_next_fun_nr,ti_type_heaps})
		= transform_groups 0 groups common_defs imported_funs imported_types []
			{ti_fun_defs = fun_defs, ti_instances = createArray nr_of_funs II_Empty, ti_cons_args = cons_args,
				ti_new_functions = [], ti_fun_heap = newHeap, ti_var_heap = var_heap, ti_symbol_heap = symbol_heap,
					ti_type_heaps = type_heaps, ti_next_fun_nr = nr_of_funs}
	  (groups, new_fun_defs, imported_types, collected_imports, ti_type_heaps, ti_var_heap) 
	  		= foldSt (add_new_function_to_group common_defs ti_fun_heap) ti_new_functions
	  				(groups, [], imported_types, collected_imports, ti_type_heaps, ti_var_heap)
	= ( groups, { fundef \\ fundef <- [ fundef \\ fundef <-: ti_fun_defs ] ++ new_fun_defs }, imported_types, collected_imports,
			ti_var_heap, ti_type_heaps, ti_symbol_heap)

where
	transform_groups group_nr groups common_defs imported_funs imported_types collected_imports ti
		| group_nr < size groups
			#! group = groups.[group_nr]
			# {group_members} = group
			# (ti_fun_defs, imported_types, collected_imports, ti_type_heaps, ti_var_heap) = foldSt (convert_function_type common_defs) group_members
				(ti.ti_fun_defs, imported_types, collected_imports, ti.ti_type_heaps, ti.ti_var_heap)
			= transform_groups (inc  group_nr) groups common_defs imported_funs imported_types collected_imports
					(foldSt (transform_function imported_funs) group_members
						{ ti & ti_fun_defs = ti_fun_defs, ti_type_heaps = ti_type_heaps, ti_var_heap = ti_var_heap })
			= (groups, imported_types, collected_imports, ti)
	
	transform_function imported_funs fun ti=:{ti_fun_defs}
		#! fun_def = ti_fun_defs.[fun]
		# {fun_body = TransformedBody tb} = fun_def
		  (fun_rhs, ti) = transform tb.tb_rhs imported_funs ti
		= { ti & ti_fun_defs = {ti.ti_fun_defs & [fun] = { fun_def & fun_body = TransformedBody { tb & tb_rhs = fun_rhs }}}}

	add_new_function_to_group ::  !{# CommonDefs} !FunctionHeap  !FunctionInfoPtr !(!*{! Group}, ![FunDef], !*{#{# CheckedTypeDef}}, !ImportedConstructors, !*TypeHeaps, !*VarHeap)
		-> (!*{! Group}, ![FunDef], !*{#{# CheckedTypeDef}}, !ImportedConstructors, !*TypeHeaps, !*VarHeap)
	add_new_function_to_group common_defs ti_fun_heap fun_ptr (groups, fun_defs, imported_types, collected_imports, type_heaps, var_heap)
		# (FI_Function {gf_fun_def,gf_fun_index}) = sreadPtr fun_ptr ti_fun_heap
		  group_index = gf_fun_def.fun_info.fi_group_index
		  (Yes ft=:{st_args,st_result}) = gf_fun_def.fun_type
		  ((st_result,st_args), {ets_type_defs, ets_collected_conses, ets_type_heaps, ets_var_heap}) = expandSynTypes common_defs (st_result,st_args)
		  		{ ets_type_defs = imported_types, ets_collected_conses = collected_imports, ets_type_heaps = type_heaps, ets_var_heap = var_heap }
		#! group = groups.[group_index]
		= ({ groups & [group_index] = { group & group_members = [gf_fun_index : group.group_members]} },
				[ { gf_fun_def & fun_type = Yes { ft &  st_result = st_result, st_args = st_args }} : fun_defs],
					ets_type_defs, ets_collected_conses, ets_type_heaps, ets_var_heap)
	
	convert_function_type common_defs fun_index (fun_defs, imported_types, collected_imports, type_heaps, var_heap)
		# (fun_def=:{fun_type = Yes fun_type}, fun_defs) = fun_defs![fun_index]
		  (fun_type, imported_types, collected_imports, type_heaps, var_heap)
		  		= convertSymbolType common_defs fun_type imported_types collected_imports type_heaps var_heap
		= ({ fun_defs & [fun_index] = { fun_def & fun_type = Yes fun_type }}, imported_types, collected_imports, type_heaps, var_heap)

convertSymbolType :: !{# CommonDefs} !SymbolType !*{#{# CheckedTypeDef}} !ImportedConstructors !*TypeHeaps !*VarHeap 
	-> (!SymbolType, !*{#{# CheckedTypeDef}}, !ImportedConstructors, !*TypeHeaps, !*VarHeap)
convertSymbolType  common_defs st imported_types collected_imports type_heaps var_heap
	# (st, {ets_type_defs, ets_collected_conses, ets_type_heaps, ets_var_heap}) = expandSynTypes common_defs st
		  		{ ets_type_defs = imported_types, ets_collected_conses = collected_imports, ets_type_heaps= type_heaps, ets_var_heap = var_heap }
	= (st, ets_type_defs, ets_collected_conses, ets_type_heaps, ets_var_heap)


::	ExpandTypeState =
	{	ets_type_defs			:: !.{#{#CheckedTypeDef}}
	,	ets_collected_conses	:: !ImportedConstructors
	,	ets_type_heaps			:: !.TypeHeaps
	,	ets_var_heap			:: !.VarHeap
	}
	
class expandSynTypes a :: !{# CommonDefs} !a !*ExpandTypeState -> (!a, !*ExpandTypeState)

/*
class expandSynTypes a ::   !a (!*{#{#CheckedTypeDef}}, !*TypeHeaps) -> (!a, (!*{#{#CheckedTypeDef}}, !*TypeHeaps))
*/

instance expandSynTypes SymbolType
where
	expandSynTypes common_defs st=:{st_args,st_result,st_context} ets
		# ((st_args,st_result), ets) = expandSynTypes common_defs (st_args,st_result) ets
		# st_args = mapAppend (add_types_of_dictionary common_defs) st_context st_args
		= ({st & st_args = st_args, st_result = st_result, st_arity = length st_args, st_context = [] }, ets)
	where
		add_types_of_dictionary common_defs {tc_class = {glob_module, glob_object={ds_index}}, tc_types}
			# {class_arity, class_dictionary={ds_ident,ds_index}} = common_defs.[glob_module].com_class_defs.[ds_index]
			  dict_type_symb = MakeTypeSymbIdent { glob_object = ds_index, glob_module = glob_module } ds_ident class_arity
			= { at_attribute = TA_Multi, at_annotation = AN_Strict, at_type = TA dict_type_symb (
					map (\type -> { at_attribute = TA_Multi, at_annotation = AN_None, at_type = type }) tc_types) }

instance expandSynTypes Type
where
	expandSynTypes common_defs (TA type_symb=:{type_index={glob_object,glob_module},type_name} types) ets=:{ets_type_defs}
		# ({td_rhs,td_name,td_args},ets_type_defs) = ets_type_defs![glob_module].[glob_object]
		  ets = { ets & ets_type_defs = ets_type_defs }
		= case td_rhs of
			SynType rhs_type
				# (type, ets_type_heaps) = substitute rhs_type.at_type (fold2St bind_var_and_attr td_args types ets.ets_type_heaps)
						// ---> (td_name, td_args, rhs_type.at_type))
				-> expandSynTypes common_defs type { ets & ets_type_heaps = ets_type_heaps }
			_
				# (types, ets) = expandSynTypes common_defs types ets
				| glob_module == cIclModIndex
					-> (TA type_symb types, ets)
					-> (TA type_symb types, collect_imported_constructors common_defs glob_module td_rhs ets)
	where	
		bind_var_and_attr {	atv_attribute = TA_Var {av_info_ptr},  atv_variable = {tv_info_ptr} } {at_attribute,at_type} type_heaps=:{th_vars,th_attrs}
			= { type_heaps & th_vars = th_vars <:= (tv_info_ptr, TVI_Type at_type), th_attrs = th_attrs <:= (av_info_ptr, AVI_Attr at_attribute) }
		bind_var_and_attr { atv_variable  = {tv_info_ptr}} {at_type} type_heaps=:{th_vars}
			= { type_heaps & th_vars = th_vars <:= (tv_info_ptr, TVI_Type at_type) }

		collect_imported_constructors common_defs mod_index (RecordType {rt_constructor}) ets=:{ets_collected_conses,ets_var_heap}
			# (ets_collected_conses, ets_var_heap)
					= collect_imported_constructor mod_index common_defs.[mod_index].com_cons_defs rt_constructor (ets_collected_conses, ets_var_heap)
			= { ets & ets_collected_conses = ets_collected_conses, ets_var_heap = ets_var_heap }
		collect_imported_constructors common_defs mod_index (AlgType constructors) ets=:{ets_collected_conses,ets_var_heap}
			# (ets_collected_conses, ets_var_heap) 
					= foldSt (collect_imported_constructor mod_index common_defs.[mod_index].com_cons_defs) constructors (ets_collected_conses, ets_var_heap)
			= { ets & ets_collected_conses = ets_collected_conses, ets_var_heap = ets_var_heap }
		collect_imported_constructors common_defs mod_index _ ets
			= ets

		collect_imported_constructor mod_index cons_defs {ds_index} (collected_conses, var_heap)
			# {cons_type_ptr} = cons_defs.[ds_index]
			  (type_info, var_heap) = readPtr cons_type_ptr var_heap
			| has_been_collected (sreadPtr cons_type_ptr var_heap)
				= (collected_conses, var_heap)
				= ([{ glob_module = mod_index, glob_object = ds_index } : collected_conses ], var_heap <:= (cons_type_ptr, VI_Used))

		has_been_collected VI_Used				= True
		has_been_collected (VI_ExpandedType _)	= True
		has_been_collected _					= False


	expandSynTypes common_defs (arg_type --> res_type) ets
		# ((arg_type, res_type), ets) = expandSynTypes common_defs (arg_type, res_type) ets
		= (arg_type --> res_type, ets)
	expandSynTypes common_defs (cons_var :@: types) ets
		# (types, ets) = expandSynTypes common_defs types ets
		= (cons_var :@: types, ets) 
	expandSynTypes common_defs type ets
		= (type, ets)

instance expandSynTypes [a] | expandSynTypes a
where
	expandSynTypes common_defs list ets
		= mapSt (expandSynTypes common_defs) list ets


instance expandSynTypes (a,b) | expandSynTypes a & expandSynTypes b
where
	expandSynTypes common_defs tuple ets
		= app2St (expandSynTypes common_defs, expandSynTypes common_defs) tuple ets

instance expandSynTypes AType
where
	expandSynTypes common_defs atype=:{at_type} ets
		# (at_type, ets) = expandSynTypes common_defs at_type ets
		= ({ atype & at_type = at_type }, ets)


/*
instance <<< InstanceInfo
where
	(<<<) file (II_Node prods _ left right) = file <<< left <<< prods <<< right 
	(<<<) file II_Empty = file 
*/	

	
instance <<< Producer
where
	(<<<) file (PR_Function symbol index)
		= file <<< "F" <<< symbol.symb_name
	(<<<) file (PR_GeneratedFunction symbol index)
		= file <<< "G" <<< symbol.symb_name <<< index
	(<<<) file PR_Empty = file <<< 'E'
	(<<<) file _ = file

instance <<< FunCall
where
	(<<<) file {fc_index} = file <<< fc_index
	
	
