implementation module trans

import StdEnv

import syntax, transform, checksupport, StdCompare, check, utilities

import RWSDebug, StdDebug

::	PartitioningInfo = 
	{	pi_marks :: 		!.{# Int}
	,	pi_next_num ::		!Int
	,	pi_next_group ::	!Int
	,	pi_groups ::		![[Int]]
	,	pi_deps ::			![Int]
	}

NotChecked :== -1	
implies a b :== not a || b

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
	{	ai_heap							:: !*VarHeap
	,	ai_cons_class					:: !*{! ConsClasses}
	,	ai_cur_ref_counts				:: !*{#Int} // for each variable 0,1 or 2
	,	ai_class_subst					:: !* ConsClassSubst
	,	ai_next_var						:: !Int
	,	ai_cases_of_vars_for_function	:: ![(!ExprInfoPtr,!VarInfoPtr)]
	}

::	ConsClassSubst	:== {# ConsClass}

::	CleanupInfo :== [ExprInfoPtr]
/*
	The argument classification (i.e. 'accumulating', 'active' or 'passive') of consumers
	is represented by an negative integer value.
	Possitive classifications are used to identify variables.
	Unification of classifications is done on-the-fly
*/

cNoFunArg		:== -1

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
		= continuation var_info ai
	  where
		continuation (VI_AccVar temp_var arg_position) ai=:{ai_cur_ref_counts}
			| arg_position<0
				= (temp_var, ai)
			#! ref_count = ai_cur_ref_counts.[arg_position] 
			   ai_cur_ref_counts = { ai_cur_ref_counts & [arg_position]=min (ref_count+1) 2 }
			= (temp_var, { ai & ai_cur_ref_counts=ai_cur_ref_counts })
//		continuation vi ai
//			= (cPassive, ai)

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
				= init_variables binds (inc ai_next_var) 
					(write_ptr fv_info_ptr (VI_AccVar ai_next_var cNoFunArg) ai_heap "init_variables")
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
	consumerRequirements {case_expr,case_guards,case_default,case_info_ptr} ai
		# ai = case case_expr of
				(Var {var_info_ptr}) -> { ai & ai_cases_of_vars_for_function=[(case_info_ptr,var_info_ptr):ai.ai_cases_of_vars_for_function] }
				_ -> ai
		  (cce, ai) = consumerRequirements case_expr ai
		  ai_class_subst = unifyClassifications cActive cce ai.ai_class_subst
		  (ccgs, ai) = consumerRequirements case_guards { ai & ai_class_subst = ai_class_subst }
		  (ccd, ai) = consumerRequirements case_default ai
		= (combineClasses ccgs ccd, ai)
/* XXX was
instance consumerRequirements Case where
	consumerRequirements {case_expr,case_guards,case_default} ai
		# (cce, ai) = consumerRequirements case_expr ai
		  ai_class_subst = unifyClassifications cActive cce ai.ai_class_subst
		  (ccgs, ai) = consumerRequirements (case_guards,case_default) { ai & ai_class_subst = ai_class_subst }
		= (ccgs, ai)
*/

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
		# pattern_exprs = [ ap_expr \\ {ap_expr}<-patterns]
		  pattern_vars = flatten [ filter (\{fv_count}->fv_count>0) ap_vars \\ {ap_vars}<-patterns]
		  (ai_next_var, ai_heap) = bind_pattern_vars pattern_vars ai.ai_next_var ai.ai_heap
		= independentConsumerRequirements pattern_exprs { ai & ai_heap=ai_heap, ai_next_var=ai_next_var }
	  where
		bind_pattern_vars [{fv_info_ptr,fv_count} : vars] next_var var_heap
			| fv_count > 0
				= bind_pattern_vars vars (inc next_var) (write_ptr fv_info_ptr (VI_AccVar next_var cNoFunArg) var_heap "bind_pattern_vars")
				= bind_pattern_vars vars (inc next_var) var_heap
		bind_pattern_vars [] next_var var_heap
			= (next_var, var_heap)
	consumerRequirements (BasicPatterns type patterns) ai
		# pattern_exprs = [ bp_expr \\ {bp_expr}<-patterns]
		= independentConsumerRequirements pattern_exprs ai
	consumerRequirements (DynamicPatterns dyn_patterns) ai
		= abort "trans.icl: consumerRequirements CasePatterns case missing"
// XXX was before adding reference counting		= consumerRequirements dyn_patterns ai
	
/*
instance consumerRequirements AlgebraicPattern where
	consumerRequirements {ap_vars,ap_expr} ai=:{ai_heap}
		# ai_heap = bind_pattern_vars ap_vars ai_heap
		= consumerRequirements ap_expr { ai & ai_heap = ai_heap }
	where
		bind_pattern_vars [{fv_info_ptr,fv_count} : vars] var_heap
			| fv_count > 0
				= bind_pattern_vars vars (write_ptr fv_info_ptr (VI_AccVar cPassive cNoFunArg) var_heap "bind_pattern_vars") -!-> "NOT BINDING"
				= bind_pattern_vars vars var_heap
		bind_pattern_vars [] var_heap
			= var_heap
*/

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

independentConsumerRequirements exprs ai=:{ai_cur_ref_counts}
// reference counting happens independently for each pattern expression
	#! s = size ai_cur_ref_counts
	   zero_array = createArray s 0
	   (_, cc, ai) = foldSt independent_consumer_requirements exprs (zero_array, cPassive, ai)
	= (cc, ai)
  where	
	independent_consumer_requirements :: Expression (*{#Int}, ConsClass, AnalyseInfo) -> (*{#Int}, ConsClass, AnalyseInfo)
	independent_consumer_requirements expr (zero_array, cc, ai=:{ai_cur_ref_counts})
		#! s = size ai_cur_ref_counts
		   ai = { ai & ai_cur_ref_counts=zero_array }
		   (cce, ai) = consumerRequirements expr ai
		   (unused, unified_ref_counts) = unify_ref_count_arrays s ai_cur_ref_counts ai.ai_cur_ref_counts
		   ai = { ai & ai_cur_ref_counts=unified_ref_counts }
		= ({ unused & [i]=0 \\ i<-[0..s-1]}, combineClasses cce cc, ai)
	unify_ref_count_arrays 0 src1 src2_dest
		= (src1, src2_dest)
	unify_ref_count_arrays i src1 src2_dest
		#! i1 = dec i
		   rc1 = src1.[i1]
		   rc2 = src2_dest.[i1]
		= unify_ref_count_arrays i1 src1 { src2_dest & [i1]= unify_ref_counts rc1 rc2} 

	// unify_ref_counts outer_ref_count ref_count_in_pattern
	unify_ref_counts 0 x = if (x==2) 2 0
	unify_ref_counts 1 x = if (x==0) 1 2
	unify_ref_counts 2 _ = 2



analyseGroups	:: !*{! Group} !*{#FunDef} !*VarHeap !*ExpressionHeap 
				-> (!CleanupInfo, !*{! ConsClasses}, !*{! Group}, !*{#FunDef}, !*VarHeap, !*ExpressionHeap)
analyseGroups groups fun_defs var_heap expr_heap
	#! nr_of_funs = size fun_defs
	   nr_of_groups = size groups
	= iFoldSt analyse_group 0 nr_of_groups
				([], createArray nr_of_funs { cc_size = 0, cc_args = [], cc_linear_bits = []}, groups, fun_defs, var_heap, expr_heap)
//	= analyse_groups 0 groups (createArray nr_of_funs { cc_size = 0, cc_args = [], cc_linear_bits = []})
//						fun_defs var_heap expr_heap
where	
/*	analyse_groups group_nr groups class_env fun_defs var_heap expr_heap
		| group_nr == size groups
			= (class_env, groups, fun_defs, var_heap, expr_heap)
			#! fun_indexes = groups.[group_nr]
			# (class_env, fun_defs, var_heap, expr_heap)
				= analyse_group fun_indexes.group_members class_env fun_defs var_heap expr_heap
			= analyse_groups (inc group_nr) groups class_env fun_defs var_heap expr_heap

*/
	analyse_group group_nr (cleanup_info, class_env, groups, fun_defs, var_heap, expr_heap)
		#! {group_members} = groups.[group_nr]
		# (nr_of_vars, nr_of_local_vars, var_heap, class_env, fun_defs) = initial_cons_class group_members 0 0 var_heap class_env fun_defs
		  initial_subst = createArray (nr_of_vars + nr_of_local_vars) cPassive
		  (ai_cases_of_vars_for_group, ai, fun_defs)
				 = analyse_functions group_members []
						{	ai_heap = var_heap,
						 	ai_cons_class = class_env, 
							ai_cur_ref_counts = {}, ai_class_subst = initial_subst,
							ai_next_var = nr_of_vars,
							ai_cases_of_vars_for_function = [] } fun_defs
		  class_env = collect_classifications group_members ai.ai_cons_class ai.ai_class_subst
		  (cleanup_info, class_env, fun_defs, var_heap, expr_heap)
				 = foldSt set_case_expr_info (flatten ai_cases_of_vars_for_group) (cleanup_info,class_env, fun_defs, ai.ai_heap, expr_heap)
		= (cleanup_info, class_env, groups, fun_defs, var_heap, expr_heap)
	  where
		set_case_expr_info ((expr_info_ptr,var_info_ptr),fun_index) (cleanup_acc, class_env, fun_defs, var_heap, expr_heap)
			# (VI_AccVar _ arg_position, var_heap) = readPtr var_info_ptr var_heap
			  ({cc_args, cc_linear_bits},class_env) = class_env![fun_index]
			| arg_position<>cNoFunArg && cc_args!!arg_position==cActive && cc_linear_bits!!arg_position
				// mark cases whose case_expr is an active linear function argument
				# aci = { aci_arg_pos = arg_position, aci_opt_unfolder = No, aci_free_vars=No } 
				= ([expr_info_ptr:cleanup_acc], class_env, fun_defs, var_heap, add_extended_expr_info expr_info_ptr (EEI_ActiveCase aci) expr_heap)
			= (cleanup_acc, class_env, fun_defs, var_heap, expr_heap)
	initial_cons_class [fun : funs] next_var_number nr_of_local_vars var_heap class_env fun_defs
		#! fun_def = fun_defs.[fun]
		#  (TransformedBody {tb_args}) = fun_def.fun_body
		   (fresh_vars, next_var_number, var_heap) = fresh_variables tb_args 0 next_var_number var_heap
		= initial_cons_class funs next_var_number (length fun_def.fun_info.fi_local_vars + nr_of_local_vars) var_heap
			{ class_env & [fun] = { cc_size = 0, cc_args = fresh_vars, cc_linear_bits=[]}} fun_defs
	initial_cons_class [] next_var_number nr_of_local_vars var_heap class_env fun_defs
		= (next_var_number, nr_of_local_vars, var_heap, class_env, fun_defs)
		
	fresh_variables [{fv_name,fv_info_ptr} : vars] arg_position next_var_number var_heap
		# (fresh_vars, last_var_number, var_heap) = fresh_variables vars (inc arg_position) (inc next_var_number) var_heap
		  var_heap = write_ptr fv_info_ptr (VI_AccVar next_var_number arg_position) var_heap "fresh_variables"
		= ([next_var_number : fresh_vars], last_var_number, var_heap)
	fresh_variables [] _ next_var_number var_heap
		= ([], next_var_number, var_heap)

	analyse_functions [fun : funs] cfvog_accu ai fun_defs
		#! fun_def = fun_defs.[fun]
		#  (TransformedBody {tb_args, tb_rhs}) = fun_def.fun_body
		   ai = { ai & ai_cur_ref_counts = createArray (length tb_args) 0 }
		   (_, ai) = consumerRequirements tb_rhs ai
		   ai_cur_ref_counts = ai.ai_cur_ref_counts
		   ai = { ai & ai_cur_ref_counts={} }
		   ai_cons_class = update_array_element ai.ai_cons_class fun
		   						(\cc->{ cc & cc_linear_bits=[ ref_count<2 \\ ref_count<-:ai_cur_ref_counts] })
		   cases_of_vars_for_function = [(a,fun) \\ a<-ai.ai_cases_of_vars_for_function ]
		   ai = { ai & ai_cons_class=ai_cons_class, ai_cases_of_vars_for_function=[] }
		= analyse_functions funs [cases_of_vars_for_function:cfvog_accu] ai fun_defs
	  where
		update_array_element array index transition
			# (before, array) = array![index]
			= { array & [index]=transition before }
	analyse_functions [] cfvog_accu ai fun_defs
		= (cfvog_accu, ai, fun_defs)

	collect_classifications [] class_env class_subst
		= class_env
	collect_classifications [fun : funs] class_env class_subst
		#! fun_class = class_env.[fun]
		# fun_class = determine_classification fun_class class_subst
		= collect_classifications funs { class_env & [fun] = fun_class/* ---> (fun, fun_class)*/} class_subst
	where
		determine_classification cc class_subst
			# (cc_size, cc_args) = mapAndLength (skip_indirections class_subst) cc.cc_args
			= { cc & cc_size = cc_size, cc_args = cc_args }

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
	,	ti_cleanup_info		:: !CleanupInfo
	,	ti_recursion_introduced	:: !Bool
	}

::	ReadOnlyTI = 
	{	ro_imported_funs	:: !{# {# FunType} }
	,	ro_is_root_case		:: !Bool
	,	ro_fun				:: !SymbIdent
	,	ro_fun_args			:: ![FreeVar]
	}

class transform a :: !a !ReadOnlyTI !TransformInfo -> (!a, !TransformInfo)

instance transform Expression
where
	transform expr=:(App app=:{app_symb,app_args}) ro ti
		# (app_args, ti) = transform app_args ro ti
		= transformApplication { app & app_args = app_args } [] ro ti
	transform appl_expr=:(expr @ exprs) ro ti
		# (expr, ti) = transform expr ro ti
		  (exprs, ti) = transform exprs ro ti
		= case expr of
			App app
				-> transformApplication app exprs ro ti
			_
				-> (expr @ exprs, ti)
	transform (Let lad=:{let_binds, let_expr}) ro ti
		# (let_binds, ti) = transform let_binds ro ti
		  (let_expr, ti) = transform let_expr ro ti
		= (Let { lad & let_binds = let_binds, let_expr = let_expr}, ti)
	transform (Case case_expr) ro ti
		= transformCase case_expr ro ti
	transform (Selection opt_type expr selectors) ro ti
		# (expr, ti) = transform expr ro ti
		= transformSelection opt_type selectors expr ti
	transform (DynamicExpr dynamic_expr) ro ti
		# (dynamic_expr, ti) = transform dynamic_expr ro ti
		= (DynamicExpr dynamic_expr, ti)
	transform expr ro ti
		= (expr, ti)

neverMatchingCase = { case_expr = EE, case_guards = NoPattern, case_default = No, case_ident = No, case_info_ptr = nilPtr }

instance transform DynamicExpr where
	transform dyn=:{dyn_expr} ro ti
		# (dyn_expr, ti) = transform dyn_expr ro ti
		= ({dyn & dyn_expr = dyn_expr}, ti)

instance transform DynamicPattern where
	transform dp=:{dp_rhs} ro ti
		# (dp_rhs, ti) = transform dp_rhs ro ti
		= ({ dp & dp_rhs = dp_rhs }, ti)

ti_to_unfold_state ti
	:== { us_var_heap = ti.ti_var_heap, us_symbol_heap = ti.ti_symbol_heap, us_cleanup_info=ti.ti_cleanup_info }
unfold_state_to_ti us ti
	:== { ti & ti_var_heap = us.us_var_heap, ti_symbol_heap = us.us_symbol_heap, ti_cleanup_info=us.us_cleanup_info }

transformCase this_case=:{case_expr,case_guards,case_default,case_ident,case_info_ptr} ro ti
	| not do_fusion
		= skip_over this_case ro ti
	= case case_expr of
		Case case_in_case
	  		-> lift_case case_in_case this_case ro ti
	  	App app=:{app_symb,app_args}
			# (opt_aci, ti_symbol_heap) = get_opt_active_case_info case_info_ptr ti.ti_symbol_heap
			  ti = { ti & ti_symbol_heap=ti_symbol_heap }
			-> case app_symb.symb_kind of
				SK_Constructor cons_index
					# algebraicPatterns = getAlgebraicPatterns case_guards
					  (may_be_match_expr, ti) = match_and_instantiate cons_index app_args algebraicPatterns case_default
																		ro ti
					-> case may_be_match_expr of
						Yes match_expr
							-> (match_expr, ti)
						No
							-> (Case neverMatchingCase, ti)
				// otherwise it's a function application
				_	-> case opt_aci of
						Yes aci=:{ aci_arg_pos, aci_opt_unfolder, aci_free_vars }
							-> case aci_opt_unfolder of
								No	| not ro.ro_is_root_case
// ReadOnlyTI
										-> possibly_generate_case_function this_case app aci ro ti
									# (may_be_unfolded_expr, ti) = tryToUnfoldExpression app_symb app_args ti
									-> case may_be_unfolded_expr of
										(Yes unfolded_expr)
											# ti_symbol_heap = app_EEI_ActiveCase (\aci-> {aci & aci_opt_unfolder=Yes app_symb}) case_info_ptr ti.ti_symbol_heap
											  ti = { ti & ti_symbol_heap=ti_symbol_heap }
											-> transformCase {this_case & case_expr = unfolded_expr } ro ti
										No	-> skip_over this_case ro ti
								Yes unfolder
									| not (equal app_symb.symb_kind unfolder.symb_kind)
										-> abort ("unrecognized case !!!!!!!!!!!!!!!!!"->>(app_symb.symb_kind, unfolder.symb_kind))
									# variables = [ Var {var_name=fv_name, var_info_ptr=fv_info_ptr, var_expr_ptr=nilPtr}
														\\ {fv_name, fv_info_ptr} <- ro.ro_fun_args ]
									  ti = { ti & ti_recursion_introduced = True }
									-> (App {app_symb=ro.ro_fun, app_args=replace_at aci_arg_pos app_args variables, app_info_ptr=nilPtr}, ti)
						No	-> skip_over this_case ro ti
		BasicExpr basic_value _
			# basicPatterns = getBasicPatterns case_guards
			# may_be_match_pattern = dropWhile (\{bp_value} -> bp_value<>basic_value) basicPatterns
			| isEmpty may_be_match_pattern
				-> case case_default of
					Yes default_expr-> (default_expr, ti)
					No				-> (Case neverMatchingCase, ti)
			-> ((hd may_be_match_pattern).bp_expr, ti)
	  	_	-> skip_over this_case ro ti
where
	skip_over this_case=:{case_expr,case_guards,case_default} ro ti
		# ro_lost_root = { ro & ro_is_root_case = False }
		  (new_case_expr, ti) = transform case_expr ro_lost_root ti
		  (new_case_guards, ti) = transform case_guards ro_lost_root ti
		  (new_case_default, ti) = transform case_default ro_lost_root ti
		= (Case { this_case & case_expr=new_case_expr, case_guards=new_case_guards, case_default=new_case_default }, ti)

	equal (SK_Function glob_index1) (SK_Function glob_index2)
		= glob_index1==glob_index2
	equal (SK_GeneratedFunction _ index1) (SK_GeneratedFunction _ index2)
		= index1==index2
	equal _ _
		= False

	get_opt_active_case_info case_info_ptr symbol_heap
		# (expr_info, symbol_heap) = readPtr case_info_ptr symbol_heap
		= case expr_info of 
			EI_Extended extensions _
				-> (lookup extensions, symbol_heap)
			_	-> (No, symbol_heap)
	  where
		lookup []						= No
		lookup [EEI_ActiveCase aci:t]	= Yes aci
		lookup [h:t]					= lookup t
	
	get_instance_info (SK_Function {glob_object}) instances fun_heap
		# (instance_info, instances) = instances![glob_object]
		= (instance_info, instances, fun_heap)
	get_instance_info (SK_GeneratedFunction fun_info_ptr _) instances fun_heap
		# (FI_Function {gf_instance_info, gf_fun_def}, fun_heap) = readPtr fun_info_ptr fun_heap
		= (gf_instance_info, instances, fun_heap)

	replace_at :: !Int [x] [x] -> [x]
	replace_at _ _ []
		= abort "compiler bug nr 67 in module trans"
	replace_at 0 x l
		= x++(drop (length x) l)
	replace_at i x [h:t]
		= [h : replace_at (dec i ) x t]

	// XXX this function has free variables .. and isnt used at all (hehe)
	case_of_app_but_no_fold app_symb=:{symb_kind=SK_Constructor cons_index} app_args ti
		# algebraicPatterns = getAlgebraicPatterns case_guards
		# (may_be_match_expr, ti) = match_and_instantiate cons_index app_args algebraicPatterns case_default ro ti
		= case may_be_match_expr of
			Yes match_expr
				-> (match_expr, ti)
			No
				-> (Case neverMatchingCase, ti)
	case_of_app_but_no_fold app_symb app_args ti
		# (may_be_unfolded_expr, ti) = tryToUnfoldExpression app_symb app_args ti
		= case may_be_unfolded_expr of
			(Yes unfolded_expr)
				-> transformCase {this_case & case_expr = unfolded_expr } ro ti
			No
				# (this_case, ti) = transform this_case ro ti
				-> (Case this_case, ti)

	getAlgebraicPatterns (AlgebraicPatterns _ algebraicPatterns)
		= algebraicPatterns
	getBasicPatterns (BasicPatterns _ basicPatterns)
		= basicPatterns
	
	lift_case nested_case=:{case_guards,case_default} outer_case ro ti
		# default_exists = case case_default of
							Yes _	-> True
							No		-> False
		  (case_guards, ti) = lift_patterns default_exists case_guards outer_case ro ti
		  (case_default, ti) = lift_default case_default outer_case ro ti
		  (EI_CaseType outer_case_type, ti_symbol_heap) = readExprInfo outer_case.case_info_ptr ti.ti_symbol_heap
		// the result type of the nested case becomes the result type of the outer case
		  ti_symbol_heap = overwrite_result_type nested_case.case_info_ptr outer_case_type.ct_result_type ti_symbol_heap
		  ti = { ti & ti_symbol_heap = ti_symbol_heap }
		= (Case {nested_case & case_guards = case_guards, case_default = case_default}, ti)
	  where
		overwrite_result_type case_info_ptr new_result_type ti_symbol_heap
			#! (EI_CaseType case_type, ti_symbol_heap)	= readExprInfo case_info_ptr ti_symbol_heap
			= writeExprInfo case_info_ptr (EI_CaseType { case_type & ct_result_type = new_result_type}) ti_symbol_heap
	lift_patterns default_exists (AlgebraicPatterns type case_guards) outer_case ro ti
		# guard_exprs	= [ ap_expr \\ {ap_expr} <- case_guards ]
		# (guard_exprs_with_case, ti) = lift_patterns_2 default_exists guard_exprs outer_case ro ti
		= (AlgebraicPatterns type [ { case_guard & ap_expr=guard_expr } \\ case_guard<-case_guards & guard_expr<-guard_exprs_with_case], ti)
	lift_patterns default_exists (BasicPatterns basic_type case_guards) outer_case ro ti
		# guard_exprs	= [ bp_expr \\ {bp_expr} <- case_guards ]
		# (guard_exprs_with_case, ti) = lift_patterns_2 default_exists guard_exprs outer_case ro ti
		= (BasicPatterns basic_type [ { case_guard & bp_expr=guard_expr } \\ case_guard<-case_guards & guard_expr<-guard_exprs_with_case], ti)

	lift_patterns_2 False [guard_expr] outer_case ro ti
		// if no default pattern exists, then the outer case expression does not have to be copied for the last pattern
		# (guard_expr, ti) = transformCase {outer_case & case_expr = guard_expr} ro ti
		= ([guard_expr], ti)
	lift_patterns_2 default_exists [guard_expr : guard_exprs] outer_case ro ti
		# (outer_guards, unfold_state) = unfold outer_case.case_guards (ti_to_unfold_state ti)
		  ti = unfold_state_to_ti unfold_state ti
		# (guard_expr, ti) = transformCase { outer_case & case_expr = guard_expr, case_guards=outer_guards } ro ti
		  (guard_exprs, ti) = lift_patterns_2 default_exists guard_exprs outer_case ro ti
		= ([guard_expr : guard_exprs], ti)
	lift_patterns_2 _ [] _ _ ti
		= ([], ti)
		
	lift_default (Yes default_expr) outer_case ro ti
		# (default_expr, ti) = transformCase { outer_case & case_expr = default_expr } ro ti
		= (Yes default_expr, ti)
	lift_default No _ _ ti
		= (No, ti)

	match_and_instantiate cons_index app_args [{ap_symbol={glob_module,glob_object={ds_index}}, ap_vars, ap_expr} : guards]
			case_default ro ti
		| cons_index.glob_module == glob_module && cons_index.glob_object == ds_index
			# ti_var_heap = fold2St (\{fv_info_ptr} arg -> writePtr fv_info_ptr (VI_Expression arg)) ap_vars app_args ti.ti_var_heap
// XXX was			# (unfolded_ap_expr, unfold_state) = unfold ap_expr (bindVariables ap_vars app_args (ti_to_unfold_state ti))
			  unfold_state = { us_var_heap = ti_var_heap, us_symbol_heap = ti.ti_symbol_heap, us_cleanup_info=ti.ti_cleanup_info }
			  (unfolded_ap_expr, unfold_state) = unfold ap_expr unfold_state
			  (ap_expr, ti) = transform unfolded_ap_expr ro (unfold_state_to_ti unfold_state ti)
			= (Yes ap_expr, ti)
			= match_and_instantiate cons_index app_args guards case_default ro ti
	match_and_instantiate cons_index app_args [guard : guards] case_default ro ti
		= match_and_instantiate cons_index app_args guards case_default ro ti
	match_and_instantiate cons_index app_args [] default_expr ro ti
		= transform default_expr ro ti

	possibly_generate_case_function kees app aci=:{aci_free_vars} ro ti
		# old_ti_recursion_introduced = ti.ti_recursion_introduced
		  (free_vars, ti)
			 = case aci_free_vars of
				Yes free_vars
					-> (free_vars, ti)
				No	# fvi = { fvi_var_heap = ti.ti_var_heap, fvi_expr_heap = ti.ti_symbol_heap, fvi_variables = [],
							  fvi_expr_ptrs = ti.ti_cleanup_info }
					  {fvi_var_heap, fvi_expr_heap, fvi_variables, fvi_expr_ptrs} = freeVariables (Case kees) fvi
					  ti = { ti & ti_var_heap = fvi_var_heap, ti_symbol_heap = fvi_expr_heap, ti_cleanup_info = fvi_expr_ptrs }
					-> (fvi_variables, ti)
		  (outer_fun_def, outer_cons_args, ti_fun_defs, ti_fun_heap) = get_fun_def_and_cons_args ro.ro_fun.symb_kind ti.ti_cons_args ti.ti_fun_defs ti.ti_fun_heap
			// ti.ti_cons_args shared
		  outer_arguments = case outer_fun_def.fun_body of
							TransformedBody {tb_args} 	-> tb_args
							Expanding args				-> args
		  outer_info_ptrs = [ fv_info_ptr \\ {fv_info_ptr}<-outer_arguments]
		  free_var_info_ptrs = map (\{v_info_ptr}->v_info_ptr) free_vars
		  arguments_from_outer_fun = filter (\{fv_info_ptr}->isMember fv_info_ptr free_var_info_ptrs) outer_arguments
		  lifted_arguments = [ { fv_def_level = undeff, fv_name = v_name, fv_info_ptr = v_info_ptr, fv_count = undeff}
								\\ {v_name, v_info_ptr} <- free_vars | not (isMember v_info_ptr outer_info_ptrs)]
		  all_args = lifted_arguments++arguments_from_outer_fun
		  (fun_info_ptr, ti_fun_heap) = newPtr FI_Empty ti_fun_heap
		  fun_ident = { id_name = ro.ro_fun.symb_name.id_name+++"_case", id_info = nilPtr }
		  fun_symb = { symb_name = fun_ident, symb_kind=SK_GeneratedFunction fun_info_ptr ti.ti_next_fun_nr, symb_arity = length all_args }
		  new_ro = {ro_imported_funs = ro.ro_imported_funs, ro_is_root_case = True, ro_fun = fun_symb, ro_fun_args = all_args }
		  ti = { ti & ti_fun_defs = ti_fun_defs, ti_fun_heap = ti_fun_heap, ti_next_fun_nr = inc ti.ti_next_fun_nr, ti_recursion_introduced = False }
		  (new_expr, ti) = transformCase kees new_ro ti
		| ti.ti_recursion_introduced
			= generate_case_function new_expr outer_fun_def outer_cons_args new_ro ti
		= (new_expr, ti)
	  where
		get_fun_def_and_cons_args (SK_Function {glob_object}) cons_args fun_defs fun_heap
			# (fun_def, fun_defs) = fun_defs![glob_object]
			= (fun_def, cons_args.[glob_object], fun_defs, fun_heap)
		get_fun_def_and_cons_args (SK_GeneratedFunction fun_info_ptr _) cons_args fun_defs fun_heap
			# (FI_Function {gf_fun_def, gf_cons_args}, fun_heap) = readPtr fun_info_ptr fun_heap
			= (gf_fun_def, gf_cons_args, fun_defs, fun_heap)

		generate_case_function new_expr outer_fun_def outer_cons_args {ro_fun=ro_fun=:{symb_kind=SK_GeneratedFunction fun_info_ptr fun_index}, ro_fun_args} ti
			# (r_act_vars, ti_var_heap) = foldSt bind_to_fresh_var ro_fun_args ([], ti.ti_var_heap)
			  act_vars = reverse r_act_vars
			  us = { us_var_heap = ti_var_heap, us_symbol_heap = ti.ti_symbol_heap, us_cleanup_info=ti.ti_cleanup_info }
			  (copied_expr, {us_var_heap, us_symbol_heap}) = unfold new_expr us
			  fun_arity = length ro_fun_args
			  fun_def =	{	fun_symb = ro_fun.symb_name
						,	fun_arity = fun_arity
						,	fun_priority = NoPrio
						,	fun_body = TransformedBody { tb_args = ro_fun_args, tb_rhs = copied_expr}
						,	fun_type = No
						,	fun_pos = NoPos
						,	fun_index = fun_index
						,	fun_kind = FK_Function
						,	fun_lifted = undeff
						,	fun_info = 	{	fi_calls = []
										,	fi_group_index = outer_fun_def.fun_info.fi_group_index
										,	fi_def_level = undeff
										,	fi_free_vars =  []
										,	fi_local_vars = []
										,	fi_dynamics = []
										,	fi_is_macro_fun = outer_fun_def.fun_info.fi_is_macro_fun
										}	
						}
			  nr_of_lifted_vars = fun_arity - outer_fun_def.fun_arity
			  new_cons_args = { cc_size	= fun_arity, cc_args = repeatn nr_of_lifted_vars cPassive++outer_cons_args.cc_args,
								cc_linear_bits = repeatn nr_of_lifted_vars False++outer_cons_args.cc_linear_bits }
			  gf = { gf_fun_def = fun_def, gf_instance_info = II_Empty, gf_cons_args = new_cons_args, gf_fun_index = fun_index}
			  ti_fun_heap = writePtr fun_info_ptr (FI_Function gf) ti.ti_fun_heap
			  ti = { ti & ti_new_functions = [fun_info_ptr:ti.ti_new_functions], ti_var_heap = us_var_heap, ti_fun_heap = ti_fun_heap, ti_symbol_heap = us_symbol_heap }
			= (App { app_symb = ro_fun,	app_args = map Var act_vars, app_info_ptr = nilPtr }, ti)
		  where
			bind_to_fresh_var {fv_name, fv_info_ptr} (accu, var_heap)
				# (new_info_ptr, var_heap) = newPtr VI_Empty var_heap
				  form_var = { fv_name = new_name, fv_info_ptr = info_ptr, fv_count = undeff, fv_def_level = NotALevel }
				  act_var = { var_name = fv_name, var_info_ptr = new_info_ptr, var_expr_ptr = nilPtr }
				= ([act_var:accu], writePtr fv_info_ptr (VI_Expression (Var act_var)) var_heap)

// GGG SymbolType VarId Let BoundVar
undeff :== -1

readExprInfo expr_info_ptr symbol_heap
	# (expr_info, symbol_heap) = readPtr expr_info_ptr symbol_heap
	= case expr_info of
		EI_Extended _ ei	-> (ei, symbol_heap)
		_					-> (expr_info, symbol_heap)

writeExprInfo expr_info_ptr new_expr_info symbol_heap
	# (expr_info, symbol_heap) = readPtr expr_info_ptr symbol_heap
	= case expr_info of
		EI_Extended extensions _	-> writePtr expr_info_ptr (EI_Extended extensions new_expr_info) symbol_heap
		_							-> writePtr expr_info_ptr new_expr_info symbol_heap

tryToUnfoldExpression :: !SymbIdent ![Expression] !*TransformInfo -> *(!Optional Expression, ! *TransformInfo)
tryToUnfoldExpression {symb_kind = SK_Function {glob_module,glob_object},symb_arity} app_args
						ti=:{ti_fun_defs, ti_var_heap, ti_symbol_heap, ti_cleanup_info}
	| glob_module == cIclModIndex
		#! fd = ti_fun_defs.[glob_object]
		| fd.fun_arity == symb_arity
			# (expr, ti_cleanup_info, ti_var_heap, ti_symbol_heap) = unfoldFunction fd.fun_body app_args ti_cleanup_info ti_var_heap ti_symbol_heap
			= (Yes expr, { ti & ti_var_heap = ti_var_heap, ti_symbol_heap = ti_symbol_heap, ti_cleanup_info=ti_cleanup_info})
			= (No, ti)
		= (No, ti)
tryToUnfoldExpression {symb_kind = SK_GeneratedFunction fun_ptr fun_index,symb_arity} app_args
					 ti=:{ti_fun_heap, ti_var_heap, ti_symbol_heap, ti_cleanup_info}
	#! fun_info = sreadPtr fun_ptr ti_fun_heap
	# (FI_Function {gf_fun_def}) = fun_info
	| gf_fun_def.fun_arity == symb_arity
		# (expr, ti_cleanup_info, ti_var_heap, ti_symbol_heap) = unfoldFunction gf_fun_def.fun_body app_args ti_cleanup_info ti_var_heap ti_symbol_heap
		= (Yes expr, { ti & ti_var_heap = ti_var_heap, ti_symbol_heap = ti_symbol_heap, ti_cleanup_info=ti_cleanup_info })
		= (No, ti)
tryToUnfoldExpression expr app_args ti
	= (No, ti)

unfoldFunction :: !FunctionBody ![Expression] ![ExprInfoPtr] !*VarHeap !*ExpressionHeap -> (!Expression, ![ExprInfoPtr], !*VarHeap, !*ExpressionHeap)
unfoldFunction (TransformedBody {tb_args,tb_rhs}) act_args cleanup_info var_heap symbol_heap
	# var_heap = foldr2 (\{fv_info_ptr} arg -> writePtr fv_info_ptr (VI_Expression arg)) var_heap tb_args act_args
	  us = { us_var_heap = var_heap, us_symbol_heap = symbol_heap, us_cleanup_info=cleanup_info }
	  (unfolded_rhs, {us_var_heap,us_symbol_heap,us_cleanup_info}) = unfold tb_rhs us
	= (unfolded_rhs, us_cleanup_info, us_var_heap, us_symbol_heap)

instance transform Bind a b | transform a
where
	transform bind=:{bind_src} ro ti
		# (bind_src, ti) = transform bind_src ro ti
		= ({ bind & bind_src = bind_src }, ti)

instance transform BasicPattern
where
	transform pattern=:{bp_expr} ro ti
		# (bp_expr, ti) = transform bp_expr ro ti
		= ({ pattern & bp_expr = bp_expr }, ti)

instance transform AlgebraicPattern
where
	transform pattern=:{ap_expr} ro ti
		# (ap_expr, ti) = transform ap_expr ro ti
		= ({ pattern & ap_expr = ap_expr }, ti)

instance transform CasePatterns
where
	transform (AlgebraicPatterns type patterns) ro ti
		# (patterns, ti) = transform patterns ro ti
		= (AlgebraicPatterns type patterns, ti)
	transform (BasicPatterns type patterns) ro ti
		# (patterns, ti) = transform patterns ro ti
		= (BasicPatterns type patterns, ti)
	transform (DynamicPatterns patterns) ro ti
		# (patterns, ti) = transform patterns ro ti
		= (DynamicPatterns patterns, ti)

instance transform Optional a | transform a
where
	transform (Yes x) ro ti
		# (x, ti) = transform x ro ti
		= (Yes x, ti)
	transform no ro ti
		= (no, ti)

instance transform [a] | transform a
where
	transform [x : xs]  ro ti
		# (x, ti) = transform x ro ti
		  (xs, ti) = transform xs ro ti
		= ([x : xs], ti)
	transform [] ro ti
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
		compare_constructor_arguments (PR_Function _ index1 _) (PR_Function _ index2 _)
			= index1 =< index2
		compare_constructor_arguments (PR_GeneratedFunction _ index1 _) (PR_GeneratedFunction _ index2 _)
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

/*searchInstance :: !{! Producer} !InstanceInfo -> FunctionInfoPtr
searchInstance prods II_Empty
	= nilPtr
searchInstance prods1 (II_Node prods2 fun_info_ptr left right)
	# cmp = compareProducers prods1 prods2
	| cmp == Equal
		= fun_info_ptr
	| cmp == Greater
		= searchInstance prods1 right
	= searchInstance prods1 left
*/
/* Fragen/to do:
	- wird die neu generierte Funktion bereits in der folgenden Transformation gebraucht ?
		Antwort: Ich verbiete das einfach, indem generierte funktionen,deren Koerper "Expanding" nicht als Produzent
				klassifiziert werden.
	- wie wird die neu generierte Funktion klassifiziert ? Antwort: Die Klassifikationen werden weitervererbt (auch die linear_bits)
	- type attributes
*/
generateFunction :: !FunDef !ConsClasses !{! Producer} !FunctionInfoPtr !{# {# FunType} } !*TransformInfo -> (!Index, !Int, !*TransformInfo)
generateFunction fd=:{fun_body = TransformedBody {tb_args,tb_rhs},fun_info = {fi_group_index}} 
				 {cc_args,cc_linear_bits} prods fun_def_ptr imported_funs
				 ti=:{ti_var_heap,ti_next_fun_nr,ti_new_functions,ti_fun_heap,ti_symbol_heap,ti_fun_defs,ti_type_heaps,ti_cons_args,ti_cleanup_info}
	#!fi_group_index = max_group_index 0 prods fi_group_index ti_fun_defs ti_fun_heap ti_cons_args
	# (Yes fun_type=:{st_vars,st_attr_vars,st_args,st_result}) = fd.fun_type
	
	  th_vars = foldSt (\tv type_var_heap -> type_var_heap <:= (tv.tv_info_ptr, TVI_Type (TV tv))) st_vars ti_type_heaps.th_vars 
	  th_attrs = foldSt (\av attr_var_heap -> attr_var_heap <:= (av.av_info_ptr, if do_fusion AVI_Empty (AVI_Attr (TA_Var av)))) st_attr_vars ti_type_heaps.th_attrs 

	  (new_fun_args, new_arg_types, new_linear_bits, new_cons_args, th_vars, ti_symbol_heap, ti_fun_defs, ti_fun_heap, ti_var_heap)
			= determine_args cc_linear_bits cc_args 0 prods tb_args st_args (st_vars, ti_cons_args, tb_rhs) th_vars
							 ti_symbol_heap ti_fun_defs ti_fun_heap ti_var_heap
	  (fresh_arg_types, ti_type_heaps) = substitute new_arg_types { ti_type_heaps & th_vars = th_vars, th_attrs = th_attrs }
	  (fresh_result_type, ti_type_heaps) = substitute st_result ti_type_heaps

	  new_fun_type = Yes { fun_type & st_args = fresh_arg_types, st_result = fresh_result_type }
	  fun_arity = length new_fun_args

	  new_fd_expanding = { fd & fun_body = Expanding new_fun_args, fun_arity = fun_arity,fun_type=new_fun_type, fun_index = ti_next_fun_nr,
								fun_info.fi_group_index = fi_group_index}
	  new_gen_fd = { gf_fun_def = new_fd_expanding,	gf_instance_info = II_Empty, gf_fun_index = ti_next_fun_nr,
					 gf_cons_args = {cc_args = new_cons_args, cc_size = length new_cons_args, cc_linear_bits=new_linear_bits} }
	  ti_fun_heap = writePtr fun_def_ptr (FI_Function new_gen_fd) ti_fun_heap
	  us = { us_var_heap = ti_var_heap, us_symbol_heap = ti_symbol_heap, us_cleanup_info=ti_cleanup_info }
	  (tb_rhs, {us_var_heap,us_symbol_heap,us_cleanup_info}) = unfold tb_rhs us
	  ro =	{	ro_imported_funs = imported_funs
			,	ro_is_root_case = case tb_rhs of {Case _ -> True; _ -> False}
			,	ro_fun= { symb_name = fd.fun_symb, symb_kind = SK_GeneratedFunction fun_def_ptr ti_next_fun_nr, symb_arity = fun_arity}
			,	ro_fun_args = new_fun_args
			}
	  (new_fun_rhs, ti) = transform tb_rhs ro { ti & ti_var_heap = us_var_heap, ti_fun_heap = ti_fun_heap, ti_symbol_heap = us_symbol_heap,
	  			ti_next_fun_nr = inc ti_next_fun_nr, ti_new_functions = [fun_def_ptr : ti_new_functions],
				ti_fun_defs = ti_fun_defs, ti_type_heaps = ti_type_heaps, ti_cleanup_info = us_cleanup_info }
	  new_fd = { new_fd_expanding & fun_body = TransformedBody {tb_args = new_fun_args, tb_rhs = new_fun_rhs} }
	= (ti_next_fun_nr, fun_arity, { ti & ti_fun_heap = ti.ti_fun_heap <:= (fun_def_ptr, FI_Function { new_gen_fd & gf_fun_def = new_fd })})
where
	determine_args [] [] prod_index producers forms types _ type_var_heap symbol_heap fun_defs fun_heap var_heap
		# (vars, var_heap) = new_variables forms var_heap
		= (vars, types, [], [], type_var_heap, symbol_heap, fun_defs, fun_heap, var_heap)
	determine_args [linear_bit : linear_bits] [cons_arg : cons_args ] prod_index producers [form : forms] [type : types]
					outer_type_vars type_var_heap symbol_heap fun_defs fun_heap var_heap
		| cons_arg == cActive
			# new_args = determine_args linear_bits cons_args (inc prod_index) prods forms types outer_type_vars type_var_heap 
									symbol_heap fun_defs fun_heap var_heap
			= determine_arg producers.[prod_index] form type ((linear_bit,cons_arg),outer_type_vars) new_args
			# (vars, types, new_linear_bits, new_cons_args, type_var_heap, symbol_heap, fun_defs, fun_heap, var_heap) 
					= determine_args linear_bits cons_args prod_index prods forms types outer_type_vars type_var_heap symbol_heap fun_defs fun_heap var_heap
			  (new_info_ptr, var_heap) = newPtr VI_Empty var_heap
			= ([{ form & fv_info_ptr = new_info_ptr } : vars], [type : types], [linear_bit : new_linear_bits], [cons_arg : new_cons_args], type_var_heap, symbol_heap, fun_defs,
					fun_heap, var_heap <:= (form.fv_info_ptr, VI_Variable form.fv_name new_info_ptr))
	where
		build_var_args [] form_vars act_vars var_heap
			= (form_vars, act_vars, var_heap)
		build_var_args [{fv_name=new_name}:new_names] form_vars act_vars var_heap
			# (info_ptr, var_heap) = newPtr VI_Empty var_heap
			  form_var = { fv_name = new_name, fv_info_ptr = info_ptr, fv_count = 0, fv_def_level = NotALevel }
			  act_var = { var_name = new_name, var_info_ptr = info_ptr, var_expr_ptr = nilPtr }
			= build_var_args new_names [form_var : form_vars] [Var act_var : act_vars] var_heap

		determine_arg PR_Empty form=:{fv_name,fv_info_ptr} type ((linear_bit,cons_arg),_)
						(vars, types, new_linear_bits, new_cons_args, type_var_heap, symbol_heap, fun_defs, fun_heap, var_heap)
			# (new_info_ptr, var_heap) = newPtr VI_Empty var_heap
			= (	[{ form & fv_info_ptr = new_info_ptr } : vars], [ type : types ], 
				[linear_bit : new_linear_bits], [cons_arg /* was cActive*/ : new_cons_args], type_var_heap, symbol_heap, fun_defs, fun_heap,
				var_heap <:= (fv_info_ptr, VI_Variable fv_name new_info_ptr))

		determine_arg (PR_Class class_app free_vars class_types) {fv_info_ptr,fv_name} type _
					  (vars, types, new_linear_bits, new_cons_args, type_var_heap, symbol_heap, fun_defs, fun_heap, var_heap)
			= ( mapAppend (\{var_info_ptr,var_name} 
							-> { fv_name = var_name, fv_info_ptr = var_info_ptr, fv_def_level = NotALevel, fv_count = 0 })
						  free_vars vars
			  , mapAppend (\_ -> { at_attribute = TA_Multi, at_annotation = AN_None, at_type = TE }) free_vars types
			  , mapAppend (\_ -> True) free_vars new_linear_bits
			  , mapAppend (\_ -> cActive) free_vars new_cons_args
			  , bind_class_types type.at_type class_types type_var_heap
			  , symbol_heap
			  , fun_defs
			  , fun_heap
			  , var_heap <:= (fv_info_ptr, VI_Expression (App class_app))
			  )

		determine_arg producer {fv_info_ptr,fv_name} type (_,(outer_type_vars, ti_cons_args, consumer_body_rhs))
						(vars, types, new_linear_bits, new_cons_args, type_var_heap, symbol_heap, fun_defs, fun_heap, var_heap)
			# ((symbol, nr_of_applied_args, fun_def, {cc_args, cc_linear_bits}), fun_defs, fun_heap)
					= from_function_or_generated_function producer fun_defs fun_heap
			  (TransformedBody tb) = fun_def.fun_body
			  (form_vars, act_vars, var_heap) = build_var_args (reverse (take nr_of_applied_args tb.tb_args)) vars [] var_heap
			  (Yes symbol_type) = fun_def.fun_type
			  application_type = build_application_type symbol_type nr_of_applied_args
			# type_var_heap = createBindingsForUnifiedTypes application_type type (symbol_type.st_vars++outer_type_vars) type_var_heap
			= (	form_vars
			  , (take nr_of_applied_args symbol_type.st_args)++types
			  , (take nr_of_applied_args cc_linear_bits)++new_linear_bits
			  , (take nr_of_applied_args cc_args)++new_cons_args
			  , type_var_heap
			  , symbol_heap
			  , fun_defs
			  , fun_heap
			  ,	writePtr fv_info_ptr
						(VI_Expression (App { app_symb = symbol, app_args = act_vars, app_info_ptr = nilPtr })) var_heap
			  ) 
		  where
			from_function_or_generated_function (PR_Function symbol index nr_of_applied_args) fun_defs fun_heap
				# (fun_def, fun_defs) = fun_defs![index]
				= ((symbol, nr_of_applied_args, fun_def, ti_cons_args.[index]), fun_defs, fun_heap)
			from_function_or_generated_function (PR_GeneratedFunction symbol=:{ symb_kind = SK_GeneratedFunction fun_ptr fun_index} _ nr_of_applied_args)
												fun_defs fun_heap
				# (FI_Function generated_function, fun_heap) = readPtr fun_ptr fun_heap
				= ((symbol, nr_of_applied_args, generated_function.gf_fun_def, generated_function.gf_cons_args), fun_defs, fun_heap)

		build_application_type :: !SymbolType !Int -> AType
		build_application_type symbol_type=:{st_arity, st_result, st_args} nr_of_applied_args
			| st_arity==nr_of_applied_args
				= st_result
// XXX ask Sjaak, whether this is correct
			= foldr (\atype1 atype2->{at_attribute=TA_None, at_annotation=AN_None, at_type=atype1-->atype2})
					st_result (drop nr_of_applied_args st_args)

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
	max_group_index_of_producer (PR_Function _ fun_index _) current_max fun_defs fun_heap cons_args
		# (fun_def, fun_defs) = fun_defs![fun_index]
		= max fun_def.fun_info.fi_group_index current_max
	max_group_index_of_producer (PR_GeneratedFunction { symb_kind = SK_GeneratedFunction fun_ptr fun_index} _ _)
								current_max fun_defs fun_heap cons_args
		# (FI_Function generated_function) = sreadPtr fun_ptr fun_heap
		  fun_def = generated_function.gf_fun_def
		= max fun_def.fun_info.fi_group_index current_max
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
			

(-!->) infix :: !.a !b -> .a | <<< b
(-!->) a b = a ---> b

createBindingsForUnifiedTypes :: !AType !AType !.[TypeVar] *TypeVarHeap -> .TypeVarHeap;
createBindingsForUnifiedTypes type_1 type_2 all_type_vars type_var_heap
	# type_var_heap = foldSt (\tv type_var_heap -> type_var_heap <:= (tv.tv_info_ptr, TVI_Empty)) all_type_vars type_var_heap
	# type_var_heap = bind_and_unify_atypes type_1 type_2 type_var_heap
//	  type_var_heap = type_var_heap -!-> ""
//	  type_var_heap = foldSt trace_type_var all_type_vars type_var_heap
	  type_var_heap = foldSt (\ a b -> snd (set_root_tvi_to_non_variable_type_or_fresh_type_var a b)) all_type_vars type_var_heap
//	  type_var_heap = type_var_heap -!-> ""
//	  type_var_heap = foldSt trace_type_var all_type_vars type_var_heap
	  type_var_heap = foldSt bind_to_fresh_type_variable_or_non_variable_type all_type_vars type_var_heap
//	  type_var_heap = type_var_heap -!-> ""
//	  type_var_heap = foldSt trace_type_var all_type_vars type_var_heap
	= type_var_heap
  where
	bind_and_unify_types (TV tv_1) (TV tv_2) type_var_heap
		# (root_1, type_var_heap) = get_root tv_1 type_var_heap
		  (root_2, type_var_heap) = get_root tv_2 type_var_heap
		  maybe_root_tv_1 = only_tv root_1
		  maybe_root_tv_2 = only_tv root_2
		= case (maybe_root_tv_1, maybe_root_tv_2) of
			(Yes root_tv_1, No)
				-> bind_root_variable_to_type root_tv_1 root_2 type_var_heap
			(No, Yes root_tv_2)
				-> bind_root_variable_to_type root_tv_2 root_1 type_var_heap
			(Yes root_tv_1, Yes root_tv_2)
				| root_tv_1.tv_info_ptr==root_tv_2.tv_info_ptr
					-> type_var_heap
				-> bind_roots_together root_tv_1 root_2 type_var_heap
			(No, No)
				-> type_var_heap
	bind_and_unify_types (TV tv_1) type type_var_heap
		| not (is_non_variable_type type)
			= abort "compiler error in trans.icl: assertion failed (1)"
		= bind_variable_to_type tv_1 type type_var_heap 
	bind_and_unify_types type (TV tv_1) type_var_heap
		| not (is_non_variable_type type)
			= abort "compiler error in trans.icl: assertion failed (2)"
		= bind_variable_to_type tv_1 type type_var_heap
	bind_and_unify_types (TA _ arg_types1) (TA _ arg_types2) type_var_heap
		= bind_and_unify_atype_lists arg_types1 arg_types2 type_var_heap
	bind_and_unify_types (l1 --> r1) (l2 --> r2) type_var_heap
		= bind_and_unify_atypes r1 r2 (bind_and_unify_atypes l1 l2 type_var_heap)
	bind_and_unify_types (TB _) (TB _) type_var_heap
		= type_var_heap
	bind_and_unify_types ((CV l1) :@: r1) ((CV l2) :@: r2) type_var_heap
		= bind_and_unify_atype_lists r1 r2 (bind_and_unify_types (TV l1) (TV l2) type_var_heap)
//	bind_and_unify_types x y _
//		= abort ("bind_and_unify_types"--->(x,y))

	bind_and_unify_atype_lists [] [] type_var_heap
		= type_var_heap
	bind_and_unify_atype_lists [x:xs] [y:ys] type_var_heap
		= bind_and_unify_atype_lists xs ys (bind_and_unify_atypes x y type_var_heap)
	
	bind_and_unify_atypes {at_type=t1} {at_type=t2} type_var_heap
			= bind_and_unify_types t1 t2 type_var_heap

	set_root_tvi_to_non_variable_type_or_fresh_type_var :: !TypeVar !*(Heap TypeVarInfo) -> *(TypeVarInfo,*Heap TypeVarInfo);
	set_root_tvi_to_non_variable_type_or_fresh_type_var this_tv type_var_heap
		# (tv_info, type_var_heap) = readPtr this_tv.tv_info_ptr type_var_heap
		= case tv_info of
			(TVI_FreshTypeVar fresh_type_var)
				-> (tv_info, type_var_heap)
			TVI_Empty
				# (fresh_type_var, type_var_heap) = allocate_fresh_type_variable this_tv.tv_name type_var_heap
				  type_var_heap = type_var_heap <:= (fresh_type_var.tv_info_ptr, TVI_Empty)
				  type_var_heap = type_var_heap <:= (this_tv.tv_info_ptr, TVI_FreshTypeVar fresh_type_var)
				-> (TVI_FreshTypeVar fresh_type_var, type_var_heap)
			(TVI_Type type)
				| is_non_variable_type type
					 -> (tv_info, type_var_heap)
				-> case type of
					(TV next_tv)
						# (destination, type_var_heap) = set_root_tvi_to_non_variable_type_or_fresh_type_var next_tv type_var_heap
						  type_var_heap = type_var_heap <:= (this_tv.tv_info_ptr, destination)
						-> (destination, type_var_heap)
	
	bind_to_fresh_type_variable_or_non_variable_type :: !TypeVar !*(Heap TypeVarInfo) -> .Heap TypeVarInfo;
	bind_to_fresh_type_variable_or_non_variable_type {tv_info_ptr} type_var_heap
		# (tv_info, type_var_heap) = readPtr tv_info_ptr type_var_heap
		= case tv_info of
			(TVI_FreshTypeVar fresh_variable)
				-> type_var_heap <:= (tv_info_ptr,TVI_Type (TV fresh_variable))
			(TVI_Type type)
				-> type_var_heap
	
	allocate_fresh_type_variable new_name type_var_heap
		# new_ident = { id_name=new_name, id_info=nilPtr }
		  (new_tv_info_ptr, type_var_heap) = newPtr TVI_Empty type_var_heap
		= ({ tv_name=new_name, tv_info_ptr=new_tv_info_ptr }, type_var_heap)
							  
	
	only_tv :: u:Type -> Optional u:TypeVar;
	only_tv (TV tv) = Yes tv
	only_tv _ = No
	
	is_non_variable_type (TA _ _)	= True
	is_non_variable_type (_ --> _)	= True
	is_non_variable_type (_ :@: _)	= True
	is_non_variable_type (TB _)		= True
	is_non_variable_type _			= False
	
	bind_variable_to_type tv type type_var_heap
		# (root, type_var_heap) = get_root tv type_var_heap
		= case (only_tv root) of
			(Yes tv)	-> bind_root_variable_to_type tv type type_var_heap
			No 			-> type_var_heap
	
	bind_root_variable_to_type {tv_info_ptr} type type_var_heap
		= type_var_heap <:= (tv_info_ptr, TVI_Type type)
	
	bind_roots_together :: TypeVar Type *(Heap TypeVarInfo) -> .Heap TypeVarInfo;
	bind_roots_together root_tv_1 root_type_2 type_var_heap
		= type_var_heap <:= (root_tv_1.tv_info_ptr, TVI_Type root_type_2)
	
	get_root :: TypeVar *(Heap TypeVarInfo) -> (Type,.Heap TypeVarInfo);
	get_root this_tv type_var_heap
		# (tv_info, type_var_heap) = readPtr this_tv.tv_info_ptr type_var_heap
		= case tv_info of
			TVI_Empty
				-> (TV this_tv, type_var_heap)
			(TVI_Type type)
				| is_non_variable_type type
					 -> (type, type_var_heap)
				-> case type of
					(TV next_tv) -> get_root next_tv type_var_heap
	// XXX for tracing
	trace_type_var tv type_var_heap
		= trace_type_vars tv (type_var_heap -!-> "TYPE VARIABLE")
	
	trace_type_vars this_tv type_var_heap
		# type_var_heap = type_var_heap -!-> this_tv
		# (tv_info, type_var_heap) = readPtr this_tv.tv_info_ptr type_var_heap
		= case tv_info of
			TVI_Empty
				-> type_var_heap
			(TVI_Type type)
				| is_non_variable_type type
					-> (type_var_heap -!-> ("TVI_Type", type))
				-> case type of
					(TV next_tv) -> trace_type_vars next_tv type_var_heap
			(TVI_FreshTypeVar root_type_var)
				-> type_var_heap -!-> ("TVI_FreshTypeVar",root_type_var)

	
transformFunctionApplication fun_def instances cc=:{cc_size, cc_args, cc_linear_bits} app=:{app_symb,app_args} extra_args ro ti
	# (app_symb, app_args, extra_args) = complete_application app_symb fun_def.fun_arity app_args extra_args
	| cc_size > 0
	  	# (producers, new_args, ti) = determineProducers fun_def.fun_info.fi_is_macro_fun cc_linear_bits cc_args app_args
														 0 (createArray cc_size PR_Empty) ti
	  	| containsProducer cc_size producers
	  		# (is_new, fun_def_ptr, instances, ti_fun_heap) = tryToFindInstance producers instances ti.ti_fun_heap
	  		| is_new
	  			# (fun_index, fun_arity, ti) = generateFunction fun_def cc producers fun_def_ptr ro.ro_imported_funs
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
		
transformApplication :: !App ![Expression] !ReadOnlyTI !*TransformInfo -> *(!Expression,!*TransformInfo)
transformApplication app=:{app_symb=symb=:{symb_kind = SK_Function {glob_module, glob_object},symb_arity}, app_args} extra_args
	ro ti=:{ti_cons_args,ti_instances,ti_fun_defs}
	| glob_module == cIclModIndex
		| glob_object < size ti_cons_args
			#! cons_class = ti_cons_args.[glob_object]
			   instances = ti_instances.[glob_object]
			   fun_def = ti_fun_defs.[glob_object]
			= transformFunctionApplication fun_def instances cons_class app extra_args ro ti
// It seems as if we have an array function 
			| isEmpty extra_args
				= (App app, ti)
				= (App { app & app_symb = { symb & symb_arity = symb_arity + length extra_args}, app_args = app_args ++ extra_args}, ti)
// This function is imported
		| isEmpty extra_args
			= (App app, ti)
			# ar_diff = ro.ro_imported_funs.[glob_module].[glob_object].ft_arity - symb_arity
			  nr_of_extra_args = length extra_args
			| nr_of_extra_args <= ar_diff
				= (App {app  &  app_args = app_args ++ extra_args, app_symb = { symb & symb_arity = symb_arity + nr_of_extra_args }}, ti)
				= (App {app  &  app_args = app_args ++ take ar_diff extra_args, app_symb = { symb & symb_arity = symb_arity + ar_diff }} @
						drop ar_diff extra_args, ti)
				
// XXX linear_bits field has to be added for generated functions
transformApplication app=:{app_symb={symb_kind = SK_GeneratedFunction fun_def_ptr fun_index}} extra_args ro ti=:{ti_fun_heap}
	# (FI_Function {gf_fun_def,gf_instance_info,gf_cons_args}, ti_fun_heap) = readPtr fun_def_ptr ti_fun_heap
	= transformFunctionApplication gf_fun_def gf_instance_info gf_cons_args app extra_args ro { ti & ti_fun_heap = ti_fun_heap }
transformApplication app [] ro ti
	= (App app, ti)
transformApplication app extra_args ro ti
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

// XXX store linear_bits and cc_args together ?

determineProducers :: !Bool ![Bool] ![Int] ![Expression] !Index !*{! Producer} !*TransformInfo -> (!*{! Producer},![Expression],!*TransformInfo)
determineProducers _ _ _ [] _ producers ti
	= (producers, [], ti)
determineProducers is_applied_to_macro_fun [linear_bit : linear_bits] [ cons_arg : cons_args ] [ arg : args ] prod_index producers ti
	| cons_arg == cActive
		# (producers, new_args, ti) = determineProducers is_applied_to_macro_fun linear_bits cons_args args (inc prod_index) producers ti
		= determine_producer is_applied_to_macro_fun linear_bit arg new_args prod_index producers ti
		# (producers, new_args, ti) = determineProducers is_applied_to_macro_fun linear_bits cons_args args prod_index producers ti
		= (producers, [arg : new_args], ti)
where
	determine_producer is_applied_to_macro_fun linear_bit arg=:(App app=:{app_info_ptr}) new_args prod_index producers ti
		| isNilPtr app_info_ptr
			= determineProducer is_applied_to_macro_fun linear_bit app EI_Empty new_args prod_index producers ti
// XXX XXX was			= (producers, [arg : new_args], ti)
			# (app_info, ti_symbol_heap) = readPtr app_info_ptr ti.ti_symbol_heap
			= determineProducer is_applied_to_macro_fun linear_bit app app_info new_args prod_index producers { ti & ti_symbol_heap = ti_symbol_heap }
	determine_producer _ _ arg new_args prod_index producers ti
		= (producers, [arg : new_args], ti)
		
determineProducer :: !Bool !Bool !App !ExprInfo ![Expression] !Index !*{! Producer} !*TransformInfo -> (!*{! Producer}, ![Expression], !*TransformInfo)
// XXX check for linear_bit also in case of a constructor ?
determineProducer _ _ app=:{app_symb = symb=:{symb_kind = SK_Constructor _}, app_args} (EI_ClassTypes types) new_args prod_index producers ti
	# (app_args, (new_vars, ti_var_heap)) = renewVariables app_args ([], ti.ti_var_heap)
	  (new_args, ti_var_heap) = mapAppendSt retrieve_old_var new_vars new_args ti_var_heap
	= ({ producers & [prod_index] = PR_Class { app & app_args = app_args } new_vars types}, new_args, { ti & ti_var_heap = ti_var_heap })
where
	retrieve_old_var {var_info_ptr} var_heap
		#! var_info = sreadPtr var_info_ptr var_heap
		# (VI_Forward var) = var_info
		= (Var var, writePtr var_info_ptr VI_Empty (writePtr var.var_info_ptr VI_Empty var_heap))
// XXX /*
determineProducer is_applied_to_macro_fun linear_bit app=:{app_symb = symb=:{symb_kind = SK_Function { glob_module, glob_object }}, app_args} _
				  new_args prod_index producers ti
	| glob_module <> cIclModIndex
		= (producers, [App app : new_args ], ti)
	# (fun_def, ti_fun_defs) = (ti.ti_fun_defs)![glob_object]
	  ti = { ti & ti_fun_defs=ti_fun_defs }
	# is_curried = fun_def.fun_arity<>length app_args
	  is_good_producer = (implies is_curried is_applied_to_macro_fun) && (implies (not is_curried) (linear_bit && do_fusion))
	| is_good_producer
		// curried applications may be fused with non linear consumers in functions local to a macro
		= ({ producers & [prod_index] = PR_Function symb glob_object (length app_args)}, app_args ++ new_args, ti)
	= (producers, [App app : new_args ], ti)
determineProducer is_applied_to_macro_fun linear_bit app=:{app_symb = symb=:{ symb_kind = SK_GeneratedFunction fun_ptr fun_index}, app_args} _
				  new_args prod_index producers ti
	# (FI_Function {gf_fun_def}, ti_fun_heap) = readPtr fun_ptr ti.ti_fun_heap
	  ti = { ti & ti_fun_heap=ti_fun_heap }
	# is_curried = gf_fun_def.fun_arity<>length app_args
	  is_good_producer = (implies is_curried is_applied_to_macro_fun) && (implies (not is_curried) (linear_bit && do_fusion))
	| is_good_producer
		// curried applications may be fused with non linear consumers in functions local to a macro
		= case gf_fun_def.fun_body of
			Expanding _	-> (producers, [App app : new_args ], ti)
			_			-> ({ producers & [prod_index] = PR_GeneratedFunction symb fun_index (length app_args)}, app_args ++ new_args, ti)
	= (producers, [App app : new_args ], ti)
/* MW..
	| linear_bit
		# (FI_Function {gf_fun_def}, ti_fun_heap) = readPtr fun_ptr ti_fun_heap
		  ti = { ti & ti_fun_heap=ti_fun_heap }
		= case gf_fun_def.fun_body of
			Expanding	-> (producers, [App app : new_args ], ti)
// ..MW
			_			-> ({ producers & [prod_index] = PR_GeneratedFunction symb fun_index (length app_args)}, app_args ++ new_args, ti)
	= (producers, [App app : new_args ], ti)
*/
// XXX determineProducer {app_symb = symb=:{symb_kind = SK_Constructor glob_index}, app_args} new_args prod_index producers ti
//	= ({ producers & [prod_index] = PR_Constructor symb app_args}, new_args, ti)
// XXX */
determineProducer _ _ app _ new_args _ producers ti
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

transformGroups :: !CleanupInfo !*{! Group} !*{#FunDef} !{!.ConsClasses} !{# CommonDefs}  !{# {# FunType} }  !*VarHeap !*TypeHeaps !*ExpressionHeap
	-> (!*{! Group}, !*{#FunDef}, !*{#{# CheckedTypeDef}}, !ImportedConstructors, !*VarHeap, !*TypeHeaps, !*ExpressionHeap)
transformGroups cleanup_info groups fun_defs cons_args common_defs imported_funs var_heap type_heaps symbol_heap
	#! (nr_of_funs, fun_defs) = usize fun_defs
	# imported_types = {com_type_defs \\ {com_type_defs} <-: common_defs }
	  (groups, imported_types, collected_imports, ti)
		= transform_groups 0 groups common_defs imported_funs imported_types []
			{ti_fun_defs = fun_defs, ti_instances = createArray nr_of_funs II_Empty,
				ti_cons_args = cons_args, ti_new_functions = [], ti_fun_heap = newHeap, ti_var_heap = var_heap,
				ti_symbol_heap = symbol_heap, ti_type_heaps = type_heaps, ti_next_fun_nr = nr_of_funs, ti_cleanup_info = cleanup_info,
				ti_recursion_introduced = False }
	  {ti_fun_defs,ti_new_functions,ti_var_heap,ti_symbol_heap,ti_fun_heap,ti_next_fun_nr,ti_type_heaps,ti_cleanup_info} = ti
	  (groups, new_fun_defs, imported_types, collected_imports, ti_type_heaps, ti_var_heap) 
	  		= foldSt (add_new_function_to_group common_defs ti_fun_heap) ti_new_functions
	  				(groups, [], imported_types, collected_imports, ti_type_heaps, ti_var_heap)
	# ti_symbol_heap = foldSt cleanup ti_cleanup_info ti_symbol_heap
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
		  ro =	{	ro_imported_funs = imported_funs
				,	ro_is_root_case = case tb of {{tb_rhs=Case _} -> True; _ -> False}
				,	ro_fun = fun_def_to_symb_ident fun fun_def
				,	ro_fun_args = tb.tb_args
				}
		  (fun_rhs, ti) = transform tb.tb_rhs ro ti
		= { ti & ti_fun_defs = {ti.ti_fun_defs & [fun] = { fun_def & fun_body = TransformedBody { tb & tb_rhs = fun_rhs }}}}
	  where
		fun_def_to_symb_ident fun_index {fun_symb,fun_arity}
			= { symb_name=fun_symb, symb_kind=SK_Function {glob_object=fun_index, glob_module=cIclModIndex } , symb_arity=fun_arity }

	add_new_function_to_group ::  !{# CommonDefs} !FunctionHeap  !FunctionInfoPtr !(!*{! Group}, ![FunDef], !*{#{# CheckedTypeDef}}, !ImportedConstructors, !*TypeHeaps, !*VarHeap)
		-> (!*{! Group}, ![FunDef], !*{#{# CheckedTypeDef}}, !ImportedConstructors, !*TypeHeaps, !*VarHeap)
	add_new_function_to_group common_defs ti_fun_heap fun_ptr (groups, fun_defs, imported_types, collected_imports, type_heaps, var_heap)
		# (FI_Function {gf_fun_def,gf_fun_index}) = sreadPtr fun_ptr ti_fun_heap
		  group_index = gf_fun_def.fun_info.fi_group_index
		# (Yes ft=:{st_args,st_result}) = gf_fun_def.fun_type
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

	cleanup expr_info_ptr symbol_heap
		# (expr_info, symbol_heap) = readPtr expr_info_ptr symbol_heap
		= case expr_info of
			EI_Extended _ expr_info -> writePtr expr_info_ptr expr_info symbol_heap
			_ -> symbol_heap

add_extended_expr_info expr_info_ptr extension expr_info_heap
	# (expr_info, expr_info_heap) = readPtr expr_info_ptr expr_info_heap
	= case expr_info of
		EI_Extended extensions ei
			-> expr_info_heap <:= (expr_info_ptr, EI_Extended [extension:extensions] ei)
		ei	-> expr_info_heap <:= (expr_info_ptr, EI_Extended [extension] ei)
		
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
			  dict_type_symb = 	MakeTypeSymbIdent { glob_object = ds_index, glob_module = glob_module } ds_ident class_arity
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


::	FreeVarInfo =
	{	fvi_var_heap	:: !.VarHeap
	,	fvi_expr_heap	:: !.ExpressionHeap
	,	fvi_variables	:: ![VarId]
	,	fvi_expr_ptrs	:: ![ExprInfoPtr]
	}

class freeVariables expr ::  !expr !*FreeVarInfo -> !*FreeVarInfo

instance freeVariables [a] | freeVariables a
where
	freeVariables list fvi
		= foldSt freeVariables list fvi

instance freeVariables (Bind a b) | freeVariables a
where
	freeVariables {bind_src} fvi
		= freeVariables bind_src fvi

instance freeVariables (Optional a) | freeVariables a
where
	freeVariables (Yes x) fvi
		= freeVariables x fvi
	freeVariables No fvi
		= fvi

removeLocalVariables local_variables all_variables global_variables var_heap
	# var_heap = foldSt mark_local_var local_variables var_heap
	= foldSt filter_local_var all_variables (global_variables, var_heap)
where
	mark_local_var {fv_info_ptr} var_heap
		= var_heap <:= (fv_info_ptr, VI_LocalVar)

	filter_local_var v=:{v_info_ptr} (global_vars, var_heap)
		# (var_info, var_heap) = readPtr v_info_ptr var_heap
		= case var_info of
			VI_LocalVar
				-> (global_vars, var_heap)
			_
				-> ([ v : global_vars ], var_heap)

instance freeVariables BoundVar
where
	freeVariables {var_name, var_info_ptr} fvi=:{fvi_var_heap, fvi_variables}
		# (var_info, fvi_var_heap) = readPtr var_info_ptr fvi_var_heap
		  (fvi_variables, fvi_var_heap) = adjust_var_info var_name var_info_ptr var_info fvi_variables fvi_var_heap
		= {fvi & fvi_variables = fvi_variables, fvi_var_heap = fvi_var_heap }
	where
		adjust_var_info _ _ (VI_UsedVar _) fvi_variables fvi_var_heap
			= (fvi_variables, fvi_var_heap)
		adjust_var_info var_name var_info_ptr _ fvi_variables fvi_var_heap
			= ([{v_name = var_name, v_info_ptr = var_info_ptr} : fvi_variables ], writePtr var_info_ptr (VI_UsedVar var_name) fvi_var_heap)

instance freeVariables Expression
where
	freeVariables (Var var) fvi
		= freeVariables var fvi
	freeVariables (App {app_args}) fvi
		= freeVariables app_args fvi
	freeVariables (fun @ args) fvi
		= freeVariables args (freeVariables fun fvi)
	freeVariables (Let {let_binds,let_expr,let_info_ptr}) fvi=:{fvi_variables = global_variables}
		# (removed_variables, fvi_var_heap) = removeVariables global_variables fvi.fvi_var_heap
		  fvi = freeVariables let_binds { fvi & fvi_variables = [], fvi_var_heap = fvi_var_heap }
		  {fvi_expr_heap, fvi_variables, fvi_var_heap, fvi_expr_ptrs} = freeVariables let_expr fvi
		  (fvi_variables, fvi_var_heap) = removeLocalVariables [bind_dst \\ {bind_dst} <- let_binds] fvi_variables [] fvi_var_heap		
		  (unbound_variables, fvi_var_heap) = determineGlobalVariables fvi_variables fvi_var_heap
		  (fvi_variables, fvi_var_heap) = restoreVariables removed_variables fvi_variables fvi_var_heap
		  (let_info, fvi_expr_heap) = readPtr let_info_ptr fvi_expr_heap
		= { fvi & fvi_variables = fvi_variables
		  , fvi_var_heap = fvi_var_heap
		  , fvi_expr_heap = fvi_expr_heap // XXX<:= (let_info_ptr, EI_FreeVariables unbound_variables let_info)
		  , fvi_expr_ptrs = [let_info_ptr : fvi_expr_ptrs]
		  }
	freeVariables (Case kees) fvi
		= freeVariablesOfCase kees fvi
	freeVariables (Selection _ expr selectors) fvi
		= freeVariables expr fvi
	freeVariables (Update expr1 selectors expr2) fvi
		= freeVariables expr2 (freeVariables expr1 fvi)
	freeVariables (RecordUpdate cons_symbol expression expressions) fvi
		= free_variables_of_record_expression expression expressions fvi
	where
		free_variables_of_record_expression (Var var) fields fvi
			= free_variables_of_fields fields var fvi
		free_variables_of_record_expression expression fields fvi
			# fvi = freeVariables expression fvi
			= freeVariables fields fvi
	
		free_variables_of_fields [] var fvi
			= fvi
		free_variables_of_fields [{bind_src = EE} : fields] var fvi
			# fvi = freeVariables var fvi
			= free_variables_of_fields fields var fvi
		free_variables_of_fields [{bind_src} : fields] var fvi
			# fvi = freeVariables bind_src fvi
			= free_variables_of_fields fields var fvi
	freeVariables (TupleSelect _ arg_nr expr) fvi
		= freeVariables expr fvi
	freeVariables (MatchExpr _ _ expr) fvi
		= freeVariables expr fvi
	freeVariables EE fvi
		= fvi
	freeVariables _ fvi
		= fvi

removeVariables global_variables var_heap
	= foldSt remove_variable global_variables ([], var_heap)
where
	remove_variable v=:{v_info_ptr} (removed_variables, var_heap)
		# (VI_UsedVar used_var, var_heap) = readPtr v_info_ptr var_heap
		= ([(v, used_var) : removed_variables], var_heap <:= (v_info_ptr, VI_Empty))

restoreVariables removed_variables global_variables var_heap
	= foldSt restore_variable removed_variables (global_variables, var_heap)
where
	restore_variable (v=:{v_info_ptr}, var_id) (restored_variables, var_heap)
		# (var_info, var_heap) = readPtr v_info_ptr var_heap
		= case var_info of
			VI_UsedVar _
				-> (restored_variables, var_heap)
			_
				-> ([ v : restored_variables ], var_heap <:= (v_info_ptr, VI_UsedVar var_id))

// XXX doet deze funktie iets ?
determineGlobalVariables global_variables var_heap
	= foldSt determine_global_variable global_variables ([], var_heap)
where		
	determine_global_variable {v_info_ptr} (global_variables, var_heap)
		# (VI_UsedVar v_name, var_heap) = readPtr v_info_ptr var_heap
		= ([{v_name = v_name, v_info_ptr = v_info_ptr} : global_variables], var_heap)

freeVariablesOfCase {case_expr,case_guards,case_default, case_info_ptr} fvi=:{fvi_variables, fvi_var_heap}
	# (removed_variables, fvi_var_heap) = removeVariables fvi_variables fvi_var_heap
	  fvi = free_variables_of_guards case_guards { fvi & fvi_variables = [], fvi_var_heap = fvi_var_heap }
	  {fvi_expr_heap, fvi_variables, fvi_var_heap, fvi_expr_ptrs} = freeVariables case_default fvi
	  (unbound_variables, fvi_var_heap) = determineGlobalVariables fvi_variables fvi_var_heap
	  (fvi_variables, fvi_var_heap) = restoreVariables removed_variables fvi_variables fvi_var_heap
	  (case_info, fvi_expr_heap) = readPtr case_info_ptr fvi_expr_heap
	= freeVariables case_expr { fvi & fvi_variables = fvi_variables, fvi_var_heap = fvi_var_heap,
			fvi_expr_heap = app_EEI_ActiveCase (\aci -> { aci & aci_free_vars=Yes unbound_variables }) case_info_ptr fvi_expr_heap,
			fvi_expr_ptrs = [case_info_ptr : fvi_expr_ptrs] }
where
	free_variables_of_guards (AlgebraicPatterns _ alg_patterns) fvi
		= foldSt free_variables_of_alg_pattern alg_patterns fvi
	where
		free_variables_of_alg_pattern {ap_vars, ap_expr} fvi=:{fvi_variables}
			# fvi = freeVariables ap_expr { fvi & fvi_variables = [] }
			  (fvi_variables, fvi_var_heap) = removeLocalVariables ap_vars fvi.fvi_variables fvi_variables fvi.fvi_var_heap
			= { fvi & fvi_var_heap = fvi_var_heap, fvi_variables = fvi_variables }

	free_variables_of_guards (BasicPatterns _ basic_patterns) fvi
		= foldSt free_variables_of_basic_pattern basic_patterns fvi
	where
		free_variables_of_basic_pattern {bp_expr} fvi
			= freeVariables bp_expr fvi

	free_variables_of_guards (DynamicPatterns dynamic_patterns) fvi
		= foldSt free_variables_of_dynamic_pattern dynamic_patterns fvi
	where
		free_variables_of_dynamic_pattern {dp_var, dp_rhs} fvi=:{fvi_variables}
			# fvi = freeVariables dp_rhs { fvi & fvi_variables = [] }
			  (fvi_variables, fvi_var_heap) = removeLocalVariables [dp_var] fvi.fvi_variables fvi_variables fvi.fvi_var_heap
			= { fvi & fvi_var_heap = fvi_var_heap, fvi_variables = fvi_variables }

app_EEI_ActiveCase transformer expr_info_ptr expr_heap
	# (expr_info, expr_heap) = readPtr expr_info_ptr expr_heap
	= case expr_info of
		(EI_Extended extensions original_expr_info)
			-> lookup_and_perform transformer [] extensions original_expr_info expr_info_ptr expr_heap
		_	-> expr_heap
  where
	lookup_and_perform _ _ [] _ _ expr_heap
		= expr_heap
	lookup_and_perform transformer accu [EEI_ActiveCase aci:extensions] original_expr_info expr_info_ptr expr_heap
		= writePtr expr_info_ptr (EI_Extended (reverse accu++[EEI_ActiveCase (transformer aci)]++extensions) original_expr_info) expr_heap
	lookup_and_perform transformer accu [extension:extensions] original_expr_info expr_info_ptr expr_heap
		= lookup_and_perform transformer [extension:accu] extensions original_expr_info expr_info_ptr expr_heap

/*
instance <<< InstanceInfo
where
	(<<<) file (II_Node prods _ left right) = file <<< left <<< prods <<< right 
	(<<<) file II_Empty = file 
*/	

	
instance <<< Producer
where
	(<<<) file (PR_Function symbol index _)
		= file <<< "F" <<< symbol.symb_name
	(<<<) file (PR_GeneratedFunction symbol index _)
		= file <<< "G" <<< symbol.symb_name <<< index
	(<<<) file PR_Empty = file <<< 'E'
	(<<<) file _ = file

instance <<< FunCall
where
	(<<<) file {fc_index} = file <<< fc_index
	
instance <<< ConsClasses
where
	(<<<) file {cc_args,cc_linear_bits} = file <<< cc_args <<< cc_linear_bits
	
