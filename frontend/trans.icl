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
		# (fd, fun_defs) = fun_defs![fun_index]
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
	{	ai_var_heap						:: !*VarHeap
	,	ai_cons_class					:: !*{! ConsClasses}
	,	ai_cur_ref_counts				:: !*{#Int} // for each variable 0,1 or 2
	,	ai_class_subst					:: !* ConsClassSubst
	,	ai_next_var						:: !Int
	,	ai_next_var_of_fun				:: !Int
	,	ai_cases_of_vars_for_function	:: ![Case]
	}

::	SharedAI =
	{	sai_common_defs		:: !{# CommonDefs }
	,	sai_imported_funs	:: !{# {# FunType} }
	}

::	ConsClassSubst	:== {# ConsClass}

::	CleanupInfo :== [ExprInfoPtr]

cNoFunArg		:== -1
cNope			:== -1

/*
	The argument classification (i.e. 'accumulating', 'active' or 'passive') of consumers
	is represented by a negative integer value.
	Positive classifications are used to identify variables.
	Unification of classifications is done on-the-fly
*/

cPassive   				:== -1
cActive					:== -2
cAccumulating   		:== -3
cVarOfMultimatchCase	:== -4

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

readVarInfo :: VarInfoPtr *VarHeap -> (VarInfo, !*VarHeap)
readVarInfo var_info_ptr var_heap
	# (var_info, var_heap) = readPtr var_info_ptr var_heap
	= case var_info of
		VI_Extended _ original_var_info	-> (original_var_info, var_heap)
		_								-> (var_info, var_heap)

writeVarInfo :: VarInfoPtr VarInfo *VarHeap -> *VarHeap
writeVarInfo var_info_ptr new_var_info var_heap
	# (old_var_info, var_heap) = readPtr var_info_ptr var_heap
	= case old_var_info of
		VI_Extended extensions _	-> writePtr var_info_ptr (VI_Extended extensions new_var_info) var_heap
		_							-> writePtr var_info_ptr new_var_info var_heap

class consumerRequirements a :: !a !{# CommonDefs} !AnalyseInfo -> (!ConsClass, !UnsafePatternBool, !AnalyseInfo)

::	UnsafePatternBool :== Bool

not_an_unsafe_pattern (cc, _, ai) = (cc, False, ai)

instance consumerRequirements BoundVar
where
	consumerRequirements {var_name,var_info_ptr} _ ai=:{ai_var_heap}
		# (var_info, ai_var_heap) = readPtr var_info_ptr ai_var_heap
		= continuation var_info { ai & ai_var_heap=ai_var_heap }
	  where
		continuation (VI_AccVar temp_var arg_position) ai=:{ai_cur_ref_counts}
//			| arg_position<0
//				= (temp_var, ai)
			#! ref_count = ai_cur_ref_counts.[arg_position] 
			   ai_cur_ref_counts = { ai_cur_ref_counts & [arg_position]=min (ref_count+1) 2 }
			= (temp_var, False, { ai & ai_cur_ref_counts=ai_cur_ref_counts })
		continuation var_info ai=:{ai_cur_ref_counts}
			=  abort ("consumerRequirements" ---> (var_name))//  <<- var_info))
//		continuation vi ai
//			= (cPassive, ai)

instance consumerRequirements Expression where
	consumerRequirements (Var var) common_defs ai
		= consumerRequirements var common_defs ai
	consumerRequirements (App app) common_defs ai
		= consumerRequirements app common_defs ai
	consumerRequirements (fun_expr @ exprs) common_defs ai
		# (cc_fun, _, ai) = consumerRequirements fun_expr common_defs ai
		  ai_class_subst = unifyClassifications cActive cc_fun ai.ai_class_subst
		= consumerRequirements exprs common_defs { ai & ai_class_subst = ai_class_subst }
	consumerRequirements (Let {let_strict_binds, let_lazy_binds,let_expr}) common_defs ai=:{ai_next_var,ai_next_var_of_fun,ai_var_heap}
		# let_binds = let_strict_binds ++ let_lazy_binds
		# (new_next_var, new_ai_next_var_of_fun, ai_var_heap) = init_variables let_binds ai_next_var ai_next_var_of_fun ai_var_heap
		# ai = acc_requirements_of_let_binds let_binds ai_next_var common_defs
					{ ai & ai_next_var = new_next_var, ai_next_var_of_fun = new_ai_next_var_of_fun, ai_var_heap = ai_var_heap }
		= consumerRequirements let_expr common_defs ai // XXX why not not_an_unsafe_pattern
		where
			init_variables [{bind_dst={fv_name, fv_count, fv_info_ptr}} : binds] ai_next_var ai_next_var_of_fun ai_var_heap
				| fv_count > 0
					= init_variables binds (inc ai_next_var) (inc ai_next_var_of_fun)
						(writePtr fv_info_ptr (VI_AccVar ai_next_var ai_next_var_of_fun) ai_var_heap)
					= init_variables binds ai_next_var ai_next_var_of_fun ai_var_heap
			init_variables [] ai_next_var ai_next_var_of_fun ai_var_heap
				= (ai_next_var, ai_next_var_of_fun, ai_var_heap)
				
			acc_requirements_of_let_binds [ {bind_src, bind_dst} : binds ] ai_next_var common_defs ai
				| bind_dst.fv_count > 0
					# (bind_var, _, ai) = consumerRequirements bind_src common_defs ai
			  		  ai_class_subst = unifyClassifications ai_next_var bind_var ai.ai_class_subst
					= acc_requirements_of_let_binds binds (inc ai_next_var) common_defs { ai & ai_class_subst = ai_class_subst }
					= acc_requirements_of_let_binds binds ai_next_var common_defs ai
			acc_requirements_of_let_binds [] ai_next_var _ ai
				= ai
				
	consumerRequirements (Case case_expr) common_defs ai
		= consumerRequirements case_expr common_defs ai
	consumerRequirements (BasicExpr _ _) _ ai
		= (cPassive, False, ai)
	consumerRequirements (MatchExpr _ _ expr) common_defs ai
		= consumerRequirements expr common_defs ai
	consumerRequirements (Selection _ expr selectors) common_defs ai
		# (cc, _, ai) = consumerRequirements expr common_defs ai
		  ai_class_subst = unifyClassifications cActive cc ai.ai_class_subst
		  ai = requirementsOfSelectors selectors common_defs { ai & ai_class_subst = ai_class_subst }
		= (cPassive, False, ai)
	consumerRequirements (Update expr1 selectors expr2) common_defs ai
		# (cc, _, ai) = consumerRequirements expr1 common_defs ai
		  ai = requirementsOfSelectors selectors common_defs ai
		  (cc, _, ai) = consumerRequirements expr2 common_defs ai
		= (cPassive, False, ai)
	consumerRequirements (RecordUpdate cons_symbol expression expressions) common_defs ai
		# (cc, _, ai) = consumerRequirements expression common_defs ai
		  (cc, _, ai) = consumerRequirements expressions common_defs ai
		= (cPassive, False, ai)
	consumerRequirements (TupleSelect tuple_symbol arg_nr expr) common_defs ai
		= consumerRequirements expr common_defs ai
	consumerRequirements (AnyCodeExpr _ _ _) _ ai
		= (cPassive, False, ai)
	consumerRequirements (ABCCodeExpr _ _) _ ai
		= (cPassive, False, ai)
	consumerRequirements (DynamicExpr dynamic_expr) common_defs ai
		= consumerRequirements dynamic_expr common_defs ai
	consumerRequirements (TypeCodeExpression _) _ ai
		= (cPassive, False, ai)
	consumerRequirements EE _ ai
		= (cPassive, False, ai)
	consumerRequirements (NoBind _) _ ai
		= (cPassive, False, ai)
	consumerRequirements expr _ ai
		= abort ("consumerRequirements ") // <<- expr)

requirementsOfSelectors selectors common_defs ai
	= foldSt (reqs_of_selector common_defs) selectors ai
where
	reqs_of_selector common_defs (ArraySelection _ _ index_expr) ai
		# (_, _, ai) = consumerRequirements index_expr common_defs ai
		= ai
	reqs_of_selector common_defs (DictionarySelection dict_var _ _ index_expr) ai
		# (_, _, ai) = consumerRequirements index_expr common_defs ai
		  (cc_var, _, ai) = consumerRequirements dict_var common_defs ai
		= { ai & ai_class_subst = unifyClassifications cActive cc_var ai.ai_class_subst }
	reqs_of_selector _ _ ai
		= ai
			
instance consumerRequirements App where
	consumerRequirements {app_symb={symb_kind = SK_Function {glob_module,glob_object}, symb_arity, symb_name}, app_args} common_defs ai=:{ai_cons_class}
		| glob_module == cIclModIndex
			| glob_object < size ai_cons_class
				#! fun_class = ai_cons_class.[glob_object]
				= reqs_of_args fun_class.cc_args app_args cPassive common_defs ai
				= consumerRequirements app_args common_defs ai
			= consumerRequirements app_args common_defs ai
	where
		reqs_of_args _ [] cumm_arg_class _ ai
			= (cumm_arg_class, False, ai)
		reqs_of_args [] _ cumm_arg_class _ ai
			= (cumm_arg_class, False, ai)
		reqs_of_args [form_cc : ccs] [arg : args] cumm_arg_class common_defs ai
			# (act_cc, _, ai) = consumerRequirements arg common_defs ai
			  ai_class_subst = unifyClassifications form_cc act_cc ai.ai_class_subst
			= reqs_of_args ccs args (combineClasses act_cc cumm_arg_class) common_defs { ai & ai_class_subst = ai_class_subst }

/*
	consumerRequirements {app_symb={symb_kind = SK_InternalFunction _}, app_args=[arg:_]} ai
		# (cc, ai) = consumerRequirements arg ai
		  ai_class_subst = unifyClassifications cActive cc ai.ai_class_subst
		= (cPassive, { ai & ai_class_subst = ai_class_subst })
*/
	consumerRequirements {app_args} common_defs ai
		=  not_an_unsafe_pattern (consumerRequirements app_args common_defs ai)

instance consumerRequirements Case where
	consumerRequirements kees=:{case_expr,case_guards,case_default,case_info_ptr} common_defs ai
		# (cce, _, ai) = consumerRequirements case_expr common_defs ai
		  (ccgs, unsafe_bits, ai) = consumer_requirements_of_guards case_guards common_defs ai
		  has_default = case case_default of
		  		Yes _ -> True
		  		_ -> False
		  (ccd, default_is_unsafe, ai) = consumerRequirements case_default common_defs ai
		  (every_constructor_appears_in_safe_pattern, may_be_active) = inspect_patterns common_defs has_default case_guards unsafe_bits
		  safe = (has_default && not default_is_unsafe) || every_constructor_appears_in_safe_pattern
		  ai_class_subst = unifyClassifications (if may_be_active cActive cVarOfMultimatchCase) cce ai.ai_class_subst
		  ai = { ai & ai_class_subst = ai_class_subst }
		  ai = case case_expr of
				Var {var_info_ptr}
					| may_be_active
						-> { ai & ai_cases_of_vars_for_function=[kees:ai.ai_cases_of_vars_for_function] }
						-> ai
				_	-> ai
		= (combineClasses ccgs ccd, not safe, ai)
	  where
		inspect_patterns common_defs has_default (AlgebraicPatterns {glob_object, glob_module} algebraic_patterns) unsafe_bits
			# type_def = common_defs.[glob_module].com_type_defs.[glob_object]
			  defined_symbols = case type_def.td_rhs of
									AlgType defined_symbols		-> defined_symbols
									RecordType {rt_constructor}	-> [rt_constructor]
			  all_constructors = [ ds_index \\ {ds_index}<-defined_symbols ]
			  pattern_constructors = [ glob_object.ds_index \\ {ap_symbol={glob_object}}<-algebraic_patterns]	
			  sorted_pattern_constructors = sort pattern_constructors unsafe_bits
			  all_sorted_constructors = if (is_sorted all_constructors) all_constructors (quicksort (<) all_constructors)
			= (appearance_loop all_sorted_constructors sorted_pattern_constructors, not (multimatch_loop has_default sorted_pattern_constructors))
		  where
			is_sorted [x]
				= True
			is_sorted [h1:t=:[h2:_]]
				= h1 < h2 && is_sorted t
		inspect_patterns common_defs has_default (BasicPatterns BT_Bool basic_patterns) unsafe_bits
			# bools_indices = [ if bool 1 0 \\ {bp_value=BVB bool}<-basic_patterns ]
			  sorted_pattern_constructors = sort bools_indices unsafe_bits
			= (appearance_loop [0,1] sorted_pattern_constructors,
				not (multimatch_loop has_default sorted_pattern_constructors))
		inspect_patterns _ _ _ _
			= (False, False)

		sort constr_indices unsafe_bits
			= quicksort smaller (zip3 constr_indices [0..] unsafe_bits)
		  where
			smaller (i1,si1,_) (i2,si2,_)
				| i1<i2		= True
				| i1>i2		= False
							= si1<si2
			zip3 [h1:t1] [h2:t2] [h3:t3]
				= [(h1,h2,h3):zip3 t1 t2 t3]
			zip3 _ _ _
				= []

		appearance_loop [] _
			= True
		appearance_loop _ []
			= False
		appearance_loop l1=:[constructor_in_type:constructors_in_type] [(constructor_in_pattern,_,is_unsafe_pattern):constructors_in_pattern]
			| constructor_in_type < constructor_in_pattern
				= False
			// constructor_in_type==constructor_in_pattern
			| is_unsafe_pattern
				 // maybe there is another pattern that is safe for this constructor
				= appearance_loop l1 constructors_in_pattern
			// the constructor will match safely. Skip over patterns with the same constructor and test the following constructor
			= appearance_loop constructors_in_type (dropWhile (\(ds_index,_,_)->ds_index==constructor_in_pattern) constructors_in_pattern)

		multimatch_loop has_default []
			= False
		multimatch_loop has_default [(cip, _, iup):t]
			= a_loop has_default cip iup t
		  where
			a_loop has_default cip iup []
				= iup && has_default
			a_loop has_default cip iup [(constructor_in_pattern, _, is_unsafe_pattern):constructors_in_pattern]
				| cip<constructor_in_pattern
					| iup && has_default
						= True
					= a_loop has_default constructor_in_pattern is_unsafe_pattern constructors_in_pattern
				| iup
					= True
				= multimatch_loop has_default (dropWhile (\(ds_index,_,_)->ds_index==cip) constructors_in_pattern)

instance consumerRequirements DynamicExpr where
	consumerRequirements {dyn_expr} common_defs ai
		= consumerRequirements dyn_expr common_defs ai

/*
instance consumerRequirements TypeCase where
	consumerRequirements {type_case_dynamic,type_case_patterns,type_case_default} ai
		# (_, ai) = consumerRequirements type_case_dynamic ai
		  (ccgs, ai) = consumerRequirements (type_case_patterns,type_case_default) ai
		= (ccgs, ai)
*/

instance consumerRequirements DynamicPattern where
	consumerRequirements {dp_rhs} common_defs ai
		= consumerRequirements dp_rhs common_defs ai

bindPatternVars [fv=:{fv_info_ptr,fv_count} : vars] next_var next_var_of_fun var_heap
	| fv_count > 0
		= bindPatternVars vars (inc next_var) (inc next_var_of_fun) (writePtr fv_info_ptr (VI_AccVar next_var next_var_of_fun) var_heap)
		= bindPatternVars vars next_var next_var_of_fun (writePtr fv_info_ptr (VI_Count 0 False) var_heap)
bindPatternVars [] next_var next_var_of_fun var_heap
	= (next_var, next_var_of_fun, var_heap)

consumer_requirements_of_guards (AlgebraicPatterns type patterns) common_defs ai
	# pattern_exprs = [ ap_expr \\ {ap_expr}<-patterns]
	  pattern_vars = flatten [ ap_vars \\ {ap_vars}<-patterns]
	  (ai_next_var, ai_next_var_of_fun, ai_var_heap) = bindPatternVars pattern_vars ai.ai_next_var ai.ai_next_var_of_fun ai.ai_var_heap
	  ai = { ai & ai_var_heap=ai_var_heap, ai_next_var=ai_next_var, ai_next_var_of_fun = ai_next_var_of_fun }
	= independentConsumerRequirements pattern_exprs common_defs ai
consumer_requirements_of_guards (BasicPatterns type patterns) common_defs ai
	# pattern_exprs = [ bp_expr \\ {bp_expr}<-patterns]
	= independentConsumerRequirements pattern_exprs common_defs ai
consumer_requirements_of_guards (DynamicPatterns dyn_patterns) common_defs ai
	# pattern_exprs = [ dp_rhs \\ {dp_rhs}<-dyn_patterns]
	  pattern_vars = [ dp_var \\ {dp_var}<-dyn_patterns]
	  (ai_next_var, ai_next_var_of_fun, ai_var_heap) = bindPatternVars pattern_vars ai.ai_next_var ai.ai_next_var_of_fun ai.ai_var_heap
	  ai = { ai & ai_var_heap=ai_var_heap, ai_next_var=ai_next_var, ai_next_var_of_fun = ai_next_var_of_fun }
	= independentConsumerRequirements pattern_exprs common_defs ai

instance consumerRequirements BasicPattern where
	consumerRequirements {bp_expr} common_defs ai
		= consumerRequirements bp_expr common_defs ai

instance consumerRequirements (Optional a) | consumerRequirements a where
	consumerRequirements (Yes x) common_defs ai
		= consumerRequirements x common_defs ai
	consumerRequirements No _ ai
		= (cPassive, False, ai)

instance consumerRequirements (!a,!b) | consumerRequirements a & consumerRequirements b where
	consumerRequirements (x, y) common_defs ai
		# (ccx, _, ai) = consumerRequirements x common_defs ai
		  (ccy, _, ai) = consumerRequirements y common_defs ai
		= (combineClasses ccx ccy, False, ai)
		
instance consumerRequirements [a] | consumerRequirements a where
	consumerRequirements [x : xs] common_defs ai
		# (ccx, _, ai) = consumerRequirements x common_defs ai
		  (ccxs, _, ai) = consumerRequirements xs common_defs ai
		= (combineClasses ccx ccxs, False, ai)
	consumerRequirements [] _ ai
		= (cPassive, False, ai)

instance consumerRequirements (Bind a b) | consumerRequirements a where
	consumerRequirements {bind_src} common_defs ai
		= consumerRequirements bind_src common_defs ai

independentConsumerRequirements exprs common_defs ai=:{ai_cur_ref_counts}
// reference counting happens independently for each pattern expression
	#! s = size ai_cur_ref_counts
	   zero_array = createArray s 0
	   (_, cc, r_unsafe_bits ,ai) = foldSt (independent_consumer_requirements common_defs) exprs (zero_array, cPassive, [], ai)
	= (cc, reverse r_unsafe_bits, ai)
  where	
	independent_consumer_requirements common_defs expr (zero_array, cc, unsafe_bits_accu, ai=:{ai_cur_ref_counts})
		#! s = size ai_cur_ref_counts
		   ai = { ai & ai_cur_ref_counts=zero_array }
		   (cce, is_unsafe_case, ai) = consumerRequirements expr common_defs ai
		   (unused, unified_ref_counts) = unify_ref_count_arrays s ai_cur_ref_counts ai.ai_cur_ref_counts
		   ai = { ai & ai_cur_ref_counts=unified_ref_counts }
		= ({ unused & [i]=0 \\ i<-[0..s-1]}, combineClasses cce cc, [is_unsafe_case:unsafe_bits_accu], ai)
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


analyseGroups	:: !{# CommonDefs} !IndexRange !*{! Group} !*{#FunDef} !*VarHeap !*ExpressionHeap 
				-> (!CleanupInfo, !*{! ConsClasses}, !*{! Group}, !*{#FunDef}, !*VarHeap, !*ExpressionHeap)
analyseGroups common_defs {ir_from, ir_to} groups fun_defs var_heap expr_heap
	#! nr_of_funs = size fun_defs + ir_from - ir_to /* Sjaak */
	   nr_of_groups = size groups
	= iFoldSt (analyse_group common_defs) 0 nr_of_groups
				([], createArray nr_of_funs { cc_size = 0, cc_args = [], cc_linear_bits = []}, groups, fun_defs, var_heap, expr_heap)
where	
	analyse_group common_defs group_nr (cleanup_info, class_env, groups, fun_defs, var_heap, expr_heap)
		# ({group_members}, groups) = groups![group_nr]
		# (nr_of_vars, nr_of_local_vars, var_heap, class_env, fun_defs) = initial_cons_class group_members 0 0 var_heap class_env fun_defs
		  initial_subst = createArray (nr_of_vars + nr_of_local_vars) cPassive
		  (ai_cases_of_vars_for_group, ai, fun_defs)
				 = analyse_functions common_defs group_members []
						{	ai_var_heap = var_heap,
						 	ai_cons_class = class_env, 
							ai_cur_ref_counts = {}, ai_class_subst = initial_subst,
							ai_next_var = nr_of_vars,
							ai_next_var_of_fun = 0,
							ai_cases_of_vars_for_function = [] } fun_defs
		  class_env = collect_classifications group_members ai.ai_cons_class ai.ai_class_subst
		  (cleanup_info, class_env, fun_defs, var_heap, expr_heap)
				 = foldSt set_case_expr_info (flatten ai_cases_of_vars_for_group) (cleanup_info,class_env, fun_defs, ai.ai_var_heap, expr_heap)
		= (cleanup_info, class_env, groups, fun_defs, var_heap, expr_heap)
	  where
		set_case_expr_info ({case_expr=(Var {var_info_ptr}), case_guards, case_info_ptr},fun_index) (cleanup_acc, class_env, fun_defs, var_heap, expr_heap)
			# (VI_AccVar _ arg_position, var_heap) = readPtr var_info_ptr var_heap
			  ({cc_size, cc_args, cc_linear_bits},class_env) = class_env![fun_index]
			  (aci_linearity_of_patterns, var_heap) = get_linearity_info cc_linear_bits case_guards var_heap
			| arg_position<cc_size && (arg_position>=cc_size || cc_args!!arg_position==cActive) && cc_linear_bits!!arg_position
				// mark non multimatch cases whose case_expr is an active linear function argument
				# aci = { aci_params = [], aci_opt_unfolder = No, aci_free_vars=No, aci_linearity_of_patterns = aci_linearity_of_patterns }
				= ([case_info_ptr:cleanup_acc], class_env, fun_defs, var_heap, 
					set_extended_expr_info case_info_ptr (EEI_ActiveCase aci) expr_heap)
			= (cleanup_acc, class_env, fun_defs, var_heap, expr_heap)
		get_linearity_info cc_linear_bits (AlgebraicPatterns _ algebraic_patterns) var_heap
			= mapSt (get_linearity_info_of_pattern cc_linear_bits) algebraic_patterns var_heap
		  where
			get_linearity_info_of_pattern cc_linear_bits {ap_vars} var_heap
				# (var_indices, var_heap) = mapSt get_var_index ap_vars var_heap
				= ([if (index==cNope) True (cc_linear_bits!!index) \\ index<-var_indices], var_heap)
			get_var_index {fv_info_ptr} var_heap
				# (vi, var_heap) = readPtr fv_info_ptr var_heap
				  index = case vi of
							VI_AccVar _ index	-> index
							VI_Count 0 False	-> cNope
				= (index, var_heap) 
		get_linearity_info cc_linear_bits _ var_heap
			= ([], var_heap)

	initial_cons_class [fun : funs] next_var_number nr_of_local_vars var_heap class_env fun_defs
		#  (fun_def, fun_defs) = fun_defs![fun]
		#  (TransformedBody {tb_args}) = fun_def.fun_body
		   (fresh_vars, next_var_number, var_heap) = fresh_variables tb_args 0 next_var_number var_heap
		= initial_cons_class funs next_var_number (length fun_def.fun_info.fi_local_vars + nr_of_local_vars) var_heap
			{ class_env & [fun] = { cc_size = 0, cc_args = fresh_vars, cc_linear_bits=[]}} fun_defs
	initial_cons_class [] next_var_number nr_of_local_vars var_heap class_env fun_defs
		= (next_var_number, nr_of_local_vars, var_heap, class_env, fun_defs)
		
	fresh_variables [{fv_name,fv_info_ptr} : vars] arg_position next_var_number var_heap
		# (fresh_vars, last_var_number, var_heap) = fresh_variables vars (inc arg_position) (inc next_var_number) var_heap
		  var_heap = writePtr fv_info_ptr (VI_AccVar next_var_number arg_position) var_heap
		= ([next_var_number : fresh_vars], last_var_number, var_heap)
	fresh_variables [] _ next_var_number var_heap
		= ([], next_var_number, var_heap)

	analyse_functions common_defs [fun : funs] cfvog_accu ai fun_defs
		#  (fun_def, fun_defs) = fun_defs![fun]
		#  (TransformedBody {tb_args, tb_rhs}) = fun_def.fun_body
		   nr_of_args = length tb_args
		   ai = { ai & ai_cur_ref_counts = createArray (nr_of_args + length fun_def.fun_info.fi_local_vars) 0,
						ai_next_var_of_fun = nr_of_args }
		   (_, _, ai) = consumerRequirements tb_rhs common_defs ai
		   ai_cur_ref_counts = ai.ai_cur_ref_counts
		   ai = { ai & ai_cur_ref_counts={} }
		   ai_cons_class = update_array_element ai.ai_cons_class fun
		   						(\cc->{ cc & cc_linear_bits=[ ref_count<2 \\ ref_count<-:ai_cur_ref_counts] })
		   cases_of_vars_for_function = [(a,fun) \\ a<-ai.ai_cases_of_vars_for_function ]
		   ai = { ai & ai_cons_class=ai_cons_class, ai_cases_of_vars_for_function=[] }
		= analyse_functions common_defs funs [cases_of_vars_for_function:cfvog_accu] ai fun_defs
	  where
		update_array_element array index transition
			# (before, array) = array![index]
			= { array & [index]=transition before }
	analyse_functions common_defs [] cfvog_accu ai fun_defs
		= (cfvog_accu, ai, fun_defs)

	collect_classifications [] class_env class_subst
		= class_env
	collect_classifications [fun : funs] class_env class_subst
		# (fun_class, class_env) = class_env![fun]
		# fun_class = determine_classification fun_class class_subst
 		= collect_classifications funs { class_env & [fun] = fun_class /*---> (fun, fun_class)*/} class_subst
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
	
::	TransformInfo =
	{	ti_fun_defs				:: !.{# FunDef}
	,	ti_instances 			:: !.{! InstanceInfo }
	,	ti_cons_args 			:: !{! ConsClasses}
	,	ti_new_functions 		:: ![FunctionInfoPtr]
	,	ti_fun_heap				:: !.FunctionHeap
	,	ti_var_heap				:: !.VarHeap
	,	ti_symbol_heap			:: !.ExpressionHeap
	,	ti_type_heaps			:: !.TypeHeaps
	,	ti_next_fun_nr			:: !Index
	,	ti_cleanup_info			:: !CleanupInfo
	,	ti_recursion_introduced	:: !Optional Index
	,	ti_trace				:: !Bool // XXX just for tracing
	}

::	ReadOnlyTI = 
	{	ro_imported_funs	:: !{# {# FunType} }
	,	ro_common_defs		:: !{# CommonDefs }
	,	ro_root_case_mode	:: !RootCaseMode
	,	ro_fun				:: !SymbIdent
	,	ro_fun_args			:: ![FreeVar]
	}

::	RootCaseMode = NotRootCase | RootCase | RootCaseOfZombie

class transform a :: !a !ReadOnlyTI !*TransformInfo -> (!a, !*TransformInfo)

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
	transform (Let lad=:{let_strict_binds, let_lazy_binds, let_expr}) ro ti
		# ti = store_type_info_of_bindings_in_heap lad ti
		  (let_strict_binds, ti) = transform let_strict_binds ro ti
		  (let_lazy_binds, ti) = transform let_lazy_binds ro ti
		  (let_expr, ti) = transform let_expr ro ti
		= (Let { lad & let_lazy_binds = let_lazy_binds, let_strict_binds = let_strict_binds, let_expr = let_expr}, ti)
	  where
		store_type_info_of_bindings_in_heap {let_strict_binds, let_lazy_binds,let_info_ptr} ti
			# let_binds = let_strict_binds ++ let_lazy_binds
			# (EI_LetType var_types, ti_symbol_heap) = readExprInfo let_info_ptr ti.ti_symbol_heap
			  ti_var_heap = foldSt (\(var_type, {bind_dst={fv_info_ptr}}) var_heap
										 ->setExtendedVarInfo fv_info_ptr (EVI_VarType var_type) var_heap)
								   (zip2 var_types let_binds) ti.ti_var_heap
			= { ti & ti_symbol_heap = ti_symbol_heap, ti_var_heap = ti_var_heap }
	transform (Case kees) ro ti
		# ti = store_type_info_of_patterns_in_heap kees ti
		= transformCase kees ro ti
	  where
		store_type_info_of_patterns_in_heap {case_guards,case_info_ptr} ti
			= case case_guards of
				AlgebraicPatterns _ patterns
					# (EI_CaseType {ct_cons_types},ti_symbol_heap) = readExprInfo case_info_ptr ti.ti_symbol_heap
					  ti_var_heap = foldSt store_type_info_of_alg_pattern (zip2 ct_cons_types patterns) ti.ti_var_heap
					-> { ti & ti_symbol_heap = ti_symbol_heap, ti_var_heap = ti_var_heap }
				BasicPatterns _ _
					-> ti // no variables occur
				DynamicPatterns dynamic_patterns
					# (EI_CaseType {ct_cons_types},ti_symbol_heap) = readExprInfo case_info_ptr ti.ti_symbol_heap
					  ti_var_heap = foldSt store_type_info_of_dyn_pattern (zip2 ct_cons_types dynamic_patterns) ti.ti_var_heap
					-> { ti & ti_symbol_heap = ti_symbol_heap, ti_var_heap = ti_var_heap }
				NoPattern
					-> ti
		store_type_info_of_alg_pattern (var_types,{ap_vars}) var_heap
			= foldSt (\(var_type, {fv_info_ptr}) var_heap
						->setExtendedVarInfo fv_info_ptr (EVI_VarType var_type) var_heap) (zip2 var_types ap_vars) var_heap

		store_type_info_of_dyn_pattern ([var_type:_],{dp_var}) var_heap
			= setExtendedVarInfo dp_var.fv_info_ptr (EVI_VarType var_type) var_heap

	transform (Selection opt_type expr selectors) ro ti
		# (expr, ti) = transform expr ro ti
		= transformSelection opt_type selectors expr ti
	transform (DynamicExpr dynamic_expr) ro ti
		# (dynamic_expr, ti) = transform dynamic_expr ro ti
		= (DynamicExpr dynamic_expr, ti)
	transform expr ro ti
		= (expr, ti)

setExtendedVarInfo var_info_ptr extension var_heap
	# (old_var_info, var_heap) = readPtr var_info_ptr var_heap
	= case old_var_info of
		VI_Extended _ original_var_info	-> writePtr var_info_ptr (VI_Extended extension original_var_info) var_heap
		_								-> writePtr var_info_ptr (VI_Extended extension old_var_info) var_heap
neverMatchingCase = { case_expr = EE, case_guards = NoPattern, case_default = No, case_ident = No, case_info_ptr = nilPtr }

instance transform DynamicExpr where
	transform dyn=:{dyn_expr} ro ti
		# (dyn_expr, ti) = transform dyn_expr ro ti
		= ({dyn & dyn_expr = dyn_expr}, ti)

instance transform DynamicPattern where
	transform dp=:{dp_rhs} ro ti
		# (dp_rhs, ti) = transform dp_rhs ro ti
		= ({ dp & dp_rhs = dp_rhs }, ti)

unfold_state_to_ti us ti
	:== { ti & ti_var_heap = us.us_var_heap, ti_symbol_heap = us.us_symbol_heap, ti_cleanup_info=us.us_cleanup_info }

transformCase this_case=:{case_expr,case_guards,case_default,case_ident,case_info_ptr} ro ti
	| SwitchFusion False True
		= skip_over this_case ro ti
	# (case_info, ti_symbol_heap) = readPtr case_info_ptr ti.ti_symbol_heap
	  ti = { ti & ti_symbol_heap=ti_symbol_heap }
	  (result_expr, ti)	= case case_info of
							EI_Extended (EEI_ActiveCase aci) _
								| is_variable case_expr
									-> skip_over this_case ro ti
								-> case ro.ro_root_case_mode of
									NotRootCase	-> possibly_generate_case_function this_case aci ro ti
									_			-> transCase True (Yes aci) this_case ro ti
							_	-> transCase False No this_case ro ti
	  ti = { ti & ti_symbol_heap = remove_aci_free_vars_info case_info_ptr ti.ti_symbol_heap }
	= (removeNeverMatchingSubcases result_expr, ti)
  where
	skip_over this_case=:{case_expr,case_guards,case_default} ro ti
		# ro_lost_root = { ro & ro_root_case_mode = NotRootCase }
		  (new_case_expr, ti) = transform case_expr ro_lost_root ti
		  (new_case_guards, ti) = transform case_guards ro_lost_root ti
		  (new_case_default, ti) = transform case_default ro_lost_root ti
		= (Case { this_case & case_expr=new_case_expr, case_guards=new_case_guards, case_default=new_case_default }, ti)

	is_variable (Var _) = True
	is_variable _ 		= False

	remove_aci_free_vars_info case_info_ptr ti_symbol_heap
		= app_EEI_ActiveCase (\aci->{aci & aci_free_vars = No }) case_info_ptr ti_symbol_heap

	transCase is_active opt_aci this_case=:{case_expr,case_guards,case_default,case_ident,case_info_ptr} ro ti
		| ti.ti_trace && (False--->("transCase",Case this_case))
			= undef
		= case case_expr of
			Case case_in_case
		  		| is_active
					-> lift_case case_in_case this_case ro ti
				-> skip_over this_case ro ti
			App app=:{app_symb,app_args}
				-> case app_symb.symb_kind of
					SK_Constructor cons_index
						| not is_active
							-> skip_over this_case ro ti // XXX currently only active cases are matched at runtime (multimatch problem)
						# algebraicPatterns = getAlgebraicPatterns case_guards
						  aci = case opt_aci of
						  			Yes aci -> aci
						  (may_be_match_expr, ti) = match_and_instantiate aci.aci_linearity_of_patterns cons_index app_args algebraicPatterns case_default ro ti
						-> case may_be_match_expr of
							Yes match_expr
								-> (match_expr, ti)
							No
								-> (Case neverMatchingCase, ti)
					// otherwise it's a function application
					_	-> case opt_aci of
							Yes aci=:{ aci_params, aci_opt_unfolder }
								-> case aci_opt_unfolder of
									No	-> skip_over this_case ro ti
									Yes unfolder
										| not (equal app_symb.symb_kind unfolder.symb_kind)
											// in this case a third function could be fused in
											-> skip_over this_case ro ti
										# variables = [ Var {var_name=fv_name, var_info_ptr=fv_info_ptr, var_expr_ptr=nilPtr}
														\\ {fv_name, fv_info_ptr} <- ro.ro_fun_args ]
										  (ti_next_fun_nr, ti) = ti!ti_next_fun_nr
										  (new_next_fun_nr, app_symb)
											= case ro.ro_root_case_mode of
													RootCaseOfZombie
														# (ro_fun=:{symb_kind=SK_GeneratedFunction fun_info_ptr _}) = ro.ro_fun
														-> (inc ti_next_fun_nr,
														    { ro_fun & symb_kind=SK_GeneratedFunction fun_info_ptr ti_next_fun_nr })
													RootCase
														-> (ti_next_fun_nr, ro.ro_fun)
										  ti = { ti & ti_next_fun_nr = new_next_fun_nr, ti_recursion_introduced = Yes ti_next_fun_nr }
										  app_args1 = replace_arg [ fv_info_ptr \\ {fv_info_ptr}<-aci_params ] app_args variables
										  (app_args2, ti) = transform app_args1 { ro & ro_root_case_mode = NotRootCase } ti
										-> (App {app_symb=app_symb, app_args=app_args2, app_info_ptr=nilPtr}, ti)
							No	-> skip_over this_case ro ti
			BasicExpr basic_value _
				| not is_active
					-> skip_over this_case ro ti // XXX currently only active cases are matched at runtime (multimatch problem)
				# basicPatterns = getBasicPatterns case_guards
				  may_be_match_pattern = dropWhile (\{bp_value} -> bp_value<>basic_value) basicPatterns
				| isEmpty may_be_match_pattern
					-> case case_default of
						Yes default_expr-> transform default_expr { ro & ro_root_case_mode = NotRootCase } ti
						No				-> (Case neverMatchingCase, ti)
				-> transform (hd may_be_match_pattern).bp_expr { ro & ro_root_case_mode = NotRootCase } ti
			Let lad
				| not is_active
					-> skip_over this_case ro ti
				# ro_not_root = { ro & ro_root_case_mode = NotRootCase }
				  (new_let_strict_binds, ti) = transform lad.let_strict_binds ro_not_root ti
				  (new_let_lazy_binds, ti) = transform lad.let_lazy_binds ro_not_root ti
				  (new_let_expr, ti) = transform (Case { this_case & case_expr = lad.let_expr }) ro ti
				-> (Let { lad & let_expr = new_let_expr, let_strict_binds = new_let_strict_binds, let_lazy_binds = new_let_lazy_binds }, ti)
		  	_	-> skip_over this_case ro ti
	where
		equal (SK_Function glob_index1) (SK_Function glob_index2)
			= glob_index1==glob_index2
		equal (SK_GeneratedFunction _ index1) (SK_GeneratedFunction _ index2)
			= index1==index2
		equal _ _
			= False
	
		replace_arg producer_vars=:[fv_info_ptr:_] act_pars form_pars=:[h_form_pars=:(Var {var_info_ptr}):t_form_pars]
			| fv_info_ptr<>var_info_ptr
				= [h_form_pars:replace_arg producer_vars act_pars t_form_pars]
			= replacement producer_vars act_pars form_pars
		  where
			replacement producer_vars [] form_pars
				= form_pars
			replacement producer_vars _ []
				= []
			replacement producer_vars [h_act_pars:t_act_pars] [form_par=:(Var {var_info_ptr}):form_pars]
				| isMember var_info_ptr producer_vars
					= [h_act_pars:replacement producer_vars t_act_pars form_pars]
				= replacement producer_vars t_act_pars form_pars
	
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
			// after this transformation the aci_free_vars information doesn't hold anymore
			  ti_symbol_heap = remove_aci_free_vars_info nested_case.case_info_ptr ti_symbol_heap
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
			# us = { us_var_heap = ti.ti_var_heap, us_symbol_heap = ti.ti_symbol_heap, us_opt_type_heaps = No,
					 us_cleanup_info=ti.ti_cleanup_info, us_handle_aci_free_vars = LeaveThem }
			  (outer_guards, us=:{us_cleanup_info}) = unfold outer_case.case_guards us
			  (expr_info, ti_symbol_heap) = readPtr outer_case.case_info_ptr us.us_symbol_heap
			  (new_info_ptr, ti_symbol_heap) = newPtr expr_info ti_symbol_heap
			  new_cleanup_info = case expr_info of 
			  		EI_Extended _ _
			  			-> [new_info_ptr:us_cleanup_info]
			  		_ 	-> us_cleanup_info
			  ti = { ti & ti_var_heap = us.us_var_heap, ti_symbol_heap = ti_symbol_heap, ti_cleanup_info=new_cleanup_info }
			  new_case = { outer_case & case_expr = guard_expr, case_guards=outer_guards, case_info_ptr=new_info_ptr }
			  (guard_expr, ti) = transformCase new_case ro ti
			  (guard_exprs, ti) = lift_patterns_2 default_exists guard_exprs outer_case ro ti
			= ([guard_expr : guard_exprs], ti)
		lift_patterns_2 _ [] _ _ ti
			= ([], ti)
			
		lift_default (Yes default_expr) outer_case ro ti
			# (default_expr, ti) = transformCase { outer_case & case_expr = default_expr } ro ti
			= (Yes default_expr, ti)
		lift_default No _ _ ti
			= (No, ti)
	
		match_and_instantiate [linearity:linearities] cons_index app_args 
								[{ap_symbol={glob_module,glob_object={ds_index}}, ap_vars, ap_expr} : guards] case_default ro ti
			| cons_index.glob_module == glob_module && cons_index.glob_object == ds_index
				# zipped = zip2 ap_vars app_args
				  unfoldables = [ linear || in_normal_form app_arg \\ linear <- linearity & app_arg <- app_args ]
				  unfoldable_args = filterWith unfoldables zipped
				  not_unfoldable = map not unfoldables
				  non_unfoldable_args = filterWith not_unfoldable zipped
				  ti_var_heap = foldSt (\({fv_info_ptr}, arg) -> writeVarInfo fv_info_ptr (VI_Expression arg)) unfoldable_args ti.ti_var_heap
				  (new_expr, ti_symbol_heap) = possibly_add_let non_unfoldable_args ap_expr not_unfoldable glob_module ds_index ro ti.ti_symbol_heap
				  unfold_state = { us_var_heap = ti_var_heap, us_symbol_heap = ti_symbol_heap, us_opt_type_heaps = No,
									us_cleanup_info=ti.ti_cleanup_info, us_handle_aci_free_vars = LeaveThem }
				  (unfolded_expr, unfold_state) = unfold new_expr unfold_state
				  (final_expr, ti) = transform unfolded_expr { ro & ro_root_case_mode = NotRootCase } (unfold_state_to_ti unfold_state ti)
				= (Yes final_expr, ti)
			= match_and_instantiate linearities cons_index app_args guards case_default ro ti
		  where
		  	in_normal_form (Var _)			= True
		  	in_normal_form (BasicExpr _ _)	= True
		  	in_normal_form _				= False
		  	
			filterWith [True:t2] [h1:t1]
				= [h1:filterWith t2 t1]
			filterWith [False:t2] [h1:t1]
				= filterWith t2 t1
			filterWith _ _
				= []
			
			possibly_add_let [] ap_expr _ _ _ _ ti_symbol_heap
				= (ap_expr, ti_symbol_heap)
			possibly_add_let non_unfoldable_args ap_expr not_unfoldable glob_module glob_index ro ti_symbol_heap
				# {cons_type} = ro.ro_common_defs.[glob_module].com_cons_defs.[glob_index]
				  let_type = filterWith not_unfoldable cons_type.st_args
				  (new_info_ptr, ti_symbol_heap) = newPtr (EI_LetType let_type) ti_symbol_heap
				= ( Let	{	let_strict_binds	= []
						,	let_lazy_binds		= [ {bind_src=bind_src, bind_dst=bind_dst} \\ (bind_dst,bind_src)<-non_unfoldable_args]
						,	let_expr			= ap_expr
						,	let_info_ptr		= new_info_ptr
						}
				  , ti_symbol_heap
				  ) 

		match_and_instantiate [linearity:linearities] cons_index app_args [guard : guards] case_default ro ti
			= match_and_instantiate linearities cons_index app_args guards case_default ro ti
		match_and_instantiate _ cons_index app_args [] default_expr ro ti
			= transform default_expr { ro & ro_root_case_mode = NotRootCase } ti

possibly_generate_case_function :: !Case !ActiveCaseInfo !ReadOnlyTI !*TransformInfo -> *(!Expression, !*TransformInfo)
possibly_generate_case_function kees=:{case_info_ptr} aci=:{aci_free_vars} ro ti=:{ti_recursion_introduced=old_ti_recursion_introduced}
//	| False->>("possibly_generate_case_function")
//		= undef
	# (free_vars, ti)
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
	  free_var_info_ptrs = [ var_info_ptr \\ {var_info_ptr}<-free_vars ]
	  used_mask = [isMember fv_info_ptr free_var_info_ptrs \\ {fv_info_ptr}<-outer_arguments]
	  arguments_from_outer_fun = [ outer_argument \\ outer_argument<-outer_arguments & used<-used_mask | used ]
	  lifted_arguments = [ { fv_def_level = undeff, fv_name = var_name, fv_info_ptr = var_info_ptr, fv_count = undeff}
							\\ {var_name, var_info_ptr} <- free_vars | not (isMember var_info_ptr outer_info_ptrs)]
	  all_args = lifted_arguments++arguments_from_outer_fun
	  (fun_info_ptr, ti_fun_heap) = newPtr FI_Empty ti_fun_heap
	  fun_ident = { id_name = ro.ro_fun.symb_name.id_name+++"_case", id_info = nilPtr }
	  fun_symb = { symb_name = fun_ident, symb_kind=SK_GeneratedFunction fun_info_ptr undeff, symb_arity = length all_args }
	  new_ro = { ro & ro_root_case_mode = RootCaseOfZombie , ro_fun = fun_symb, ro_fun_args = all_args }
	  ti = { ti & ti_fun_defs = ti_fun_defs, ti_fun_heap = ti_fun_heap, ti_recursion_introduced = No }
	  (new_expr, ti) = transformCase kees new_ro ti
	  (ti_recursion_introduced, ti) = ti!ti_recursion_introduced
	= case ti_recursion_introduced of
		Yes fun_index
			-> generate_case_function old_ti_recursion_introduced fun_index case_info_ptr new_expr
										outer_fun_def outer_cons_args used_mask new_ro ti
		No	-> (new_expr, { ti & ti_recursion_introduced = old_ti_recursion_introduced })
  where

	get_fun_def_and_cons_args :: !SymbKind !{!ConsClasses} !u:{# FunDef} !*FunctionHeap -> (!FunDef, !ConsClasses, !u:{# FunDef}, !*FunctionHeap)
	get_fun_def_and_cons_args (SK_Function {glob_object}) cons_args fun_defs fun_heap
		# (fun_def, fun_defs) = fun_defs![glob_object]
		= (fun_def, cons_args.[glob_object], fun_defs, fun_heap)
	get_fun_def_and_cons_args (SK_GeneratedFunction fun_info_ptr fun_index) cons_args fun_defs fun_heap
		| fun_index < size fun_defs
			# (fun_def, fun_defs) = fun_defs![fun_index]
			= (fun_def, cons_args.[fun_index], fun_defs, fun_heap)
		# (FI_Function {gf_fun_def, gf_cons_args}, fun_heap) = readPtr fun_info_ptr fun_heap
		= (gf_fun_def, gf_cons_args, fun_defs, fun_heap)

/*
	get_fun_def_and_cons_args (SK_Function {glob_object}) cons_args fun_defs fun_heap
		# (fun_def, fun_defs) = fun_defs![glob_object]
		= (fun_def, cons_args.[glob_object], fun_defs, fun_heap)
	get_fun_def_and_cons_args (SK_GeneratedFunction fun_info_ptr _) cons_args fun_defs fun_heap
		# (FI_Function {gf_fun_def, gf_cons_args}, fun_heap) = readPtr fun_info_ptr fun_heap
		= (gf_fun_def, gf_cons_args, fun_defs, fun_heap)
*/
	generate_case_function old_ti_recursion_introduced fun_index case_info_ptr new_expr outer_fun_def outer_cons_args used_mask
						{ro_fun=ro_fun=:{symb_kind=SK_GeneratedFunction fun_info_ptr _}, ro_fun_args} ti
//		| False->>"generate_case_function"
//			= undef
		# fun_arity = length ro_fun_args
		  (Yes {st_vars,st_args,st_attr_vars}) = outer_fun_def.fun_type
		  types_from_outer_fun = [ st_arg \\ st_arg <- st_args & used <- used_mask | used ]
		  nr_of_lifted_vars = fun_arity-(length types_from_outer_fun)
		  (lifted_types, ti_var_heap) = mapSt get_type_of_local_var (take nr_of_lifted_vars ro_fun_args) ti.ti_var_heap
		  (EI_CaseType {ct_result_type}, ti_symbol_heap) = readExprInfo case_info_ptr ti.ti_symbol_heap
		  (form_vars, ti_var_heap) = mapSt bind_to_fresh_var ro_fun_args ti_var_heap
		  arg_types = lifted_types++types_from_outer_fun
		  type_variables = getTypeVars [ct_result_type:arg_types]
		  {th_vars,th_attrs} = ti.ti_type_heaps
		  (fresh_type_vars, th_vars) = mapSt bind_to_fresh_type_var type_variables th_vars
		  (fresh_arg_types, ti_type_heaps) = substitute arg_types { th_vars = th_vars, th_attrs = th_attrs }
		  (fresh_result_type, ti_type_heaps) = substitute ct_result_type ti_type_heaps
		  us = { us_var_heap = ti_var_heap, us_symbol_heap = ti_symbol_heap, us_opt_type_heaps = Yes ti_type_heaps, 
					us_cleanup_info=ti.ti_cleanup_info, us_handle_aci_free_vars = SubstituteThem }
		  (copied_expr, {us_var_heap=ti_var_heap, us_symbol_heap=ti_symbol_heap, us_cleanup_info=ti_cleanup_info,
						 us_opt_type_heaps = Yes ti_type_heaps}) = unfold new_expr us
		  fun_type = { st_vars = fresh_type_vars, st_args = fresh_arg_types, st_arity = fun_arity, st_result = fresh_result_type,
						st_context = [], st_attr_vars = [], st_attr_env = [] }
		  fun_def =	{	fun_symb = ro_fun.symb_name
					,	fun_arity = fun_arity
					,	fun_priority = NoPrio
					,	fun_body = TransformedBody { tb_args = form_vars, tb_rhs = copied_expr}
					,	fun_type = Yes fun_type
					,	fun_pos = NoPos
					,	fun_index = fun_index
					,	fun_kind = FK_Function cNameNotLocationDependent
					,	fun_lifted = undeff
					,	fun_info = 	{	fi_calls = []
									,	fi_group_index = outer_fun_def.fun_info.fi_group_index
									,	fi_def_level = NotALevel
									,	fi_free_vars =  []
									,	fi_local_vars = []
									,	fi_dynamics = []
									,	fi_is_macro_fun = outer_fun_def.fun_info.fi_is_macro_fun
									}	
					}
		  cc_args_from_outer_fun = [ cons_arg \\ cons_arg <- outer_cons_args.cc_args & used <- used_mask | used ]
		  cc_linear_bits_from_outer_fun = [ cons_arg \\ cons_arg <- outer_cons_args.cc_linear_bits & used <- used_mask | used ]
		  new_cons_args = { cc_size	= fun_arity, cc_args = repeatn nr_of_lifted_vars cPassive++cc_args_from_outer_fun,
							cc_linear_bits = repeatn nr_of_lifted_vars False++cc_linear_bits_from_outer_fun }
		  gf = { gf_fun_def = fun_def, gf_instance_info = II_Empty, gf_cons_args = new_cons_args, gf_fun_index = fun_index}
		  ti_fun_heap = writePtr fun_info_ptr (FI_Function gf) ti.ti_fun_heap
		  ti = { ti & ti_new_functions = [fun_info_ptr:ti.ti_new_functions], ti_var_heap = ti_var_heap, ti_fun_heap = ti_fun_heap,
					ti_symbol_heap = ti_symbol_heap, ti_type_heaps = ti_type_heaps, ti_cleanup_info = ti_cleanup_info,
					ti_recursion_introduced = old_ti_recursion_introduced }
		= ( App { app_symb = { ro_fun & symb_kind = SK_GeneratedFunction fun_info_ptr fun_index},
				 app_args = map free_var_to_bound_var ro_fun_args, app_info_ptr = nilPtr }
		  , ti
		  )
	  where
		bind_to_fresh_var {fv_name, fv_info_ptr} var_heap
			# (new_info_ptr, var_heap) = newPtr VI_Empty var_heap
			  form_var = { fv_name = fv_name, fv_info_ptr = new_info_ptr, fv_count = undeff, fv_def_level = NotALevel }
			  act_var = { var_name = fv_name, var_info_ptr = new_info_ptr, var_expr_ptr = nilPtr }
			= (form_var, writeVarInfo fv_info_ptr (VI_Expression (Var act_var)) var_heap)
		bind_to_fresh_type_var tv type_var_heap
			# (new_info_ptr, type_var_heap) = newPtr TVI_Empty type_var_heap
			  new_type_var = { tv_name = tv.tv_name, tv_info_ptr = new_info_ptr }
			= (new_type_var, writePtr tv.tv_info_ptr (TVI_Type (TV new_type_var)) type_var_heap)
		get_type_of_local_var {fv_info_ptr} var_heap
			# (VI_Extended (EVI_VarType a_type) _, var_heap) = readPtr fv_info_ptr var_heap
			= (a_type, var_heap)
		free_var_to_bound_var {fv_name, fv_info_ptr}
			= Var { var_name = fv_name, var_info_ptr = fv_info_ptr, var_expr_ptr = nilPtr}

removeNeverMatchingSubcases keesExpr=:(Case kees)
	// remove those case guards whose right hand side is a never matching case
	| is_never_matching_case keesExpr
		= keesExpr
	# {case_guards, case_default} = kees
	  filtered_default = get_filtered_default case_default
	= case case_guards of
		AlgebraicPatterns i alg_patterns
			| not (any (is_never_matching_case o get_alg_rhs) alg_patterns)
				-> keesExpr // frequent case: all subexpressions can't fail
			# filtered_case_guards = filter (not o is_never_matching_case o get_alg_rhs) alg_patterns
			| has_become_never_matching filtered_default filtered_case_guards
				-> Case neverMatchingCase
			| is_default_only filtered_default filtered_case_guards
				-> fromYes case_default
			-> Case {kees & case_guards = AlgebraicPatterns i filtered_case_guards, case_default = filtered_default }
		BasicPatterns bt basic_patterns
			| not (any (is_never_matching_case o get_basic_rhs) basic_patterns)
				-> keesExpr // frequent case: all subexpressions can't fail
			# filtered_case_guards = filter (not o is_never_matching_case o get_basic_rhs) basic_patterns
			| has_become_never_matching filtered_default filtered_case_guards
				-> Case neverMatchingCase
			| is_default_only filtered_default filtered_case_guards
				-> fromYes case_default
			-> Case {kees & case_guards = BasicPatterns bt filtered_case_guards, case_default = filtered_default }
  where
	get_filtered_default y=:(Yes c_default)
		| is_never_matching_case c_default
			= No
		= y
	get_filtered_default no
		= no
	has_become_never_matching No [] = True
	has_become_never_matching _ _ = False
	is_default_only (Yes _) [] = True
	is_default_only _ _ = False
	is_never_matching_case (Case {case_guards = NoPattern, case_default = No })
		= True
	is_never_matching_case _
		= False
	get_alg_rhs {ap_expr} = ap_expr
	get_basic_rhs {bp_expr} = bp_expr
removeNeverMatchingSubcases expr
	= expr

fromYes (Yes x) = x

	
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

instance transform (Bind a b) | transform a
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

instance transform (Optional a) | transform a
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
		compare_constructor_arguments (PR_Function _ index1) (PR_Function _ index2)
			= index1 =< index2
		compare_constructor_arguments (PR_GeneratedFunction _ index1) (PR_GeneratedFunction _ index2)
			= index1 =< index2
		compare_constructor_arguments (PR_Class app1 _ _) (PR_Class app2 _ _) 
			= app1.app_args =< app2.app_args
		compare_constructor_arguments (PR_Curried symb_ident1) (PR_Curried symb_ident2)
			= symb_ident1 =< symb_ident2
		compare_constructor_arguments PR_Empty PR_Empty
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

generateFunction :: !FunDef !ConsClasses !{! Producer} !FunctionInfoPtr !ReadOnlyTI !*TransformInfo -> (!Index, !Int, !*TransformInfo)
generateFunction fd=:{fun_body = TransformedBody {tb_args,tb_rhs},fun_info = {fi_group_index}} 
				 {cc_args,cc_linear_bits} prods fun_def_ptr ro
				 ti=:{ti_var_heap,ti_next_fun_nr,ti_new_functions,ti_fun_heap,ti_symbol_heap,ti_fun_defs,ti_type_heaps,ti_cons_args,ti_cleanup_info}
/*
	| False->>("generating new function",fd.fun_symb.id_name,fd.fun_index,"->",ti_next_fun_nr)
		= undef
	| False--->("producers:",II_Node prods nilPtr II_Empty II_Empty,("cc_args",cc_args,("cc_linear_bits",cc_linear_bits)))
		= undef
*/
	#!fi_group_index = max_group_index 0 prods fi_group_index ti_fun_defs ti_fun_heap ti_cons_args
	# (Yes fun_type=:{st_vars,st_attr_vars,st_args,st_result}) = fd.fun_type
	  th_vars = foldSt (\tv type_var_heap -> type_var_heap <:= (tv.tv_info_ptr, TVI_Type (TV tv))) st_vars ti_type_heaps.th_vars 
	  th_attrs = foldSt (\av attr_var_heap -> attr_var_heap <:= (av.av_info_ptr, AVI_Attr TA_Multi)) st_attr_vars ti_type_heaps.th_attrs 
	  ti_type_heaps = { ti_type_heaps & th_attrs = th_attrs, th_vars = th_vars }
	  
	  (new_fun_args, new_arg_types_array, new_result_type, new_type_vars, new_linear_bits, new_cons_args, ti_type_heaps, ti_symbol_heap, ti_fun_defs, ti_fun_heap, ti_var_heap)
			= determine_args cc_linear_bits cc_args 0 prods tb_args (st_args_array st_args) st_result st_vars (ti_cons_args, tb_rhs, ro) ti_type_heaps
							 ti_symbol_heap ti_fun_defs ti_fun_heap ti_var_heap
	  new_arg_types = flatten [ el \\ el<-:new_arg_types_array ]
	  fun_arity = length new_fun_args
	  new_fun_type = Yes { st_vars = new_type_vars, st_args = new_arg_types, st_arity = fun_arity,
							st_result = new_result_type, st_context = [], st_attr_vars = [], st_attr_env = [] }

	  new_fd_expanding = { fd & fun_body = Expanding new_fun_args, fun_arity = fun_arity,fun_type=new_fun_type, fun_index = ti_next_fun_nr,
								fun_info.fi_group_index = fi_group_index}
	  new_gen_fd = { gf_fun_def = new_fd_expanding,	gf_instance_info = II_Empty, gf_fun_index = ti_next_fun_nr,
					 gf_cons_args = {cc_args = new_cons_args, cc_size = length new_cons_args, cc_linear_bits=new_linear_bits} }
	  ti_fun_heap = writePtr fun_def_ptr (FI_Function new_gen_fd) ti_fun_heap
	  us = { us_var_heap = ti_var_heap, us_symbol_heap = ti_symbol_heap, us_opt_type_heaps = Yes ti_type_heaps,
			 us_cleanup_info=ti_cleanup_info, us_handle_aci_free_vars = RemoveThem }
	  (tb_rhs, {us_var_heap,us_symbol_heap,us_opt_type_heaps=Yes type_heaps, us_cleanup_info}) = unfold tb_rhs us
	  ro =	{ ro &	ro_root_case_mode = case tb_rhs of 
	  					Case _
	  						-> RootCase
	  					_	-> NotRootCase,
					ro_fun= { symb_name = fd.fun_symb, symb_kind = SK_GeneratedFunction fun_def_ptr ti_next_fun_nr, symb_arity = fun_arity},
					ro_fun_args = new_fun_args
			}
	  ti_trace=False
	| ti_trace && (False--->("transforming new function:",tb_rhs))
		= undef
	# (new_fun_rhs, ti) = transform tb_rhs ro { ti & ti_var_heap = us_var_heap, ti_fun_heap = ti_fun_heap, ti_symbol_heap = us_symbol_heap,
	  			ti_next_fun_nr = inc ti_next_fun_nr, ti_new_functions = [fun_def_ptr : ti_new_functions],
				ti_fun_defs = ti_fun_defs, ti_type_heaps = type_heaps, ti_cleanup_info = us_cleanup_info, ti_trace=ti_trace }
	  new_fd = { new_fd_expanding & fun_body = TransformedBody {tb_args = new_fun_args, tb_rhs = new_fun_rhs} }
//	| False--->("generated function", new_fd, '\n', new_fd.fun_type)
//		= undef
	= (ti_next_fun_nr, fun_arity, { ti & ti_fun_heap = ti.ti_fun_heap <:= (fun_def_ptr, FI_Function { new_gen_fd & gf_fun_def = new_fd })})
where
	st_args_array :: ![AType] -> .{![AType]}
	st_args_array st_args
		= { [el] \\ el <- st_args }
		
	determine_args _ [] prod_index producers forms arg_types result_type type_vars _ type_heaps symbol_heap fun_defs fun_heap var_heap
		# (vars, var_heap) = new_variables forms var_heap
		= (vars, arg_types, result_type, type_vars, [], [], type_heaps, symbol_heap, fun_defs, fun_heap, var_heap)
	determine_args [linear_bit : linear_bits] [cons_arg : cons_args ] prod_index producers [form : forms] arg_types result_type
					type_vars input type_heaps symbol_heap fun_defs fun_heap var_heap
		| cons_arg == cActive
			# new_args = determine_args linear_bits cons_args (inc prod_index) prods forms arg_types result_type type_vars input type_heaps 
									symbol_heap fun_defs fun_heap var_heap
			= determine_arg producers.[prod_index] form prod_index ((linear_bit,cons_arg), input) new_args
			# (vars, arg_types, result_type, type_vars, new_linear_bits, new_cons_args, type_heaps, symbol_heap, fun_defs, fun_heap, var_heap) 
					= determine_args linear_bits cons_args (inc prod_index) prods forms arg_types result_type type_vars input type_heaps symbol_heap fun_defs fun_heap var_heap
			  (new_info_ptr, var_heap) = newPtr VI_Empty var_heap
			= ([{ form & fv_info_ptr = new_info_ptr } : vars], arg_types, result_type, type_vars, [linear_bit : new_linear_bits], [cons_arg : new_cons_args], type_heaps, symbol_heap, fun_defs,
					fun_heap, writeVarInfo form.fv_info_ptr (VI_Variable form.fv_name new_info_ptr) var_heap)
	where
		build_var_args [] form_vars act_vars var_heap
			= (form_vars, act_vars, var_heap)
		build_var_args [new_name:new_names] form_vars act_vars var_heap
			# (info_ptr, var_heap) = newPtr VI_Empty var_heap
			  form_var = { fv_name = new_name, fv_info_ptr = info_ptr, fv_count = 0, fv_def_level = NotALevel }
			  act_var = { var_name = new_name, var_info_ptr = info_ptr, var_expr_ptr = nilPtr }
			= build_var_args new_names [form_var : form_vars] [Var act_var : act_vars] var_heap

		determine_arg PR_Empty form=:{fv_name,fv_info_ptr} _ ((linear_bit,cons_arg), _)
						(vars, arg_types, result_type, type_vars, new_linear_bits, new_cons_args, type_heaps, symbol_heap, fun_defs, fun_heap, var_heap)
			# (new_info_ptr, var_heap) = newPtr VI_Empty var_heap
			= (	[{ form & fv_info_ptr = new_info_ptr } : vars], arg_types, result_type, type_vars,
				[linear_bit : new_linear_bits], [cons_arg /* was cActive*/ : new_cons_args], type_heaps, symbol_heap, fun_defs, fun_heap,
				writeVarInfo fv_info_ptr (VI_Variable fv_name new_info_ptr) var_heap)

		determine_arg (PR_Class class_app free_vars class_type) {fv_info_ptr,fv_name} prod_index _
					  (vars, arg_types, result_type, type_vars, new_linear_bits, new_cons_args, type_heaps=:{th_vars}, symbol_heap, fun_defs, fun_heap, var_heap)
/*
			# (arg_type, arg_types) = arg_types![prod_index]
			  empty_atype = { at_attribute = TA_Multi, at_annotation = AN_None, at_type = TE }
			| False--->("determine_arg", class_type, getTypeVars class_type, arg_type, type_vars)
				= undef
			# (unbounded_type_vars, th_vars)
			  		= createBindingsForUnifiedTypes { empty_atype & at_type = class_type } (hd arg_type)
			  										((getTypeVars class_type)++type_vars) th_vars
			  (arg_types, type_heaps) = substituteArr { arg_types & [prod_index] = repeatn (length free_vars) empty_atype} { type_heaps & th_vars = th_vars }
			  (result_type, type_heaps) = substitute result_type type_heaps
			= ( mapAppend (\{var_info_ptr,var_name} 
							-> { fv_name = var_name, fv_info_ptr = var_info_ptr, fv_def_level = NotALevel, fv_count = 0 })
						  free_vars vars
			  , arg_types
			  , result_type
			  , unbounded_type_vars
			  , mapAppend (\_ -> True) free_vars new_linear_bits
			  , mapAppend (\_ -> cActive) free_vars new_cons_args
			  , type_heaps
			  , symbol_heap
			  , fun_defs
			  , fun_heap
			  , writeVarInfo fv_info_ptr (VI_Dictionary class_app.app_symb class_app.app_args class_type) var_heap
			  )
*/
			# (arg_type, arg_types) = arg_types![prod_index]
			  type_heaps = bind_class_types (hd arg_type).at_type class_type type_heaps
			  empty_atype = { at_attribute = TA_Multi, at_annotation = AN_None, at_type = TE }
			  (arg_types, type_heaps) = substituteArr { arg_types & [prod_index] = repeatn (length free_vars) empty_atype} type_heaps
			  (result_type, type_heaps) = substitute result_type type_heaps
			= ( mapAppend (\{var_info_ptr,var_name} 
							-> { fv_name = var_name, fv_info_ptr = var_info_ptr, fv_def_level = NotALevel, fv_count = 0 })
						  free_vars vars
			  , arg_types
			  , result_type
			  , type_vars
			  , mapAppend (\_ -> True) free_vars new_linear_bits
			  , mapAppend (\_ -> cActive) free_vars new_cons_args
			  , type_heaps
			  , symbol_heap
			  , fun_defs
			  , fun_heap
			  , writeVarInfo fv_info_ptr (VI_Dictionary class_app.app_symb class_app.app_args class_type) var_heap
			  )

		determine_arg producer {fv_info_ptr,fv_name} prod_index ((linear_bit, _),(ti_cons_args, consumer_body_rhs, ro))
						(vars, arg_types, result_type, type_vars, new_linear_bits, new_cons_args, type_heaps=:{th_vars, th_attrs}, symbol_heap, fun_defs, fun_heap, var_heap)
			# symbol = get_producer_symbol producer
			  (symbol_type, fun_defs, fun_heap)
					= get_producer_type symbol ro fun_defs fun_heap
			  curried = is_curried producer
			#! size_fun_defs = size fun_defs
			# ({cc_args, cc_linear_bits}, fun_heap) = calc_cons_args curried symbol ti_cons_args linear_bit size_fun_defs fun_heap
			  nr_of_applied_args = symbol.symb_arity
			  application_type = build_application_type symbol_type nr_of_applied_args
			  (arg_type, arg_types) = arg_types![prod_index]
			  th_attrs = foldSt (\av attr_var_heap -> attr_var_heap <:= (av.av_info_ptr, AVI_Attr TA_Multi)) symbol_type.st_attr_vars th_attrs 
			  (unbounded_type_vars, type_heaps) 
			  		= createBindingsForUnifiedTypes application_type (hd arg_type) (symbol_type.st_vars++type_vars) 
			  								ro.ro_common_defs { th_vars = th_vars, th_attrs = th_attrs }
			  (arg_types, type_heaps) = substituteArr { arg_types & [prod_index] = take nr_of_applied_args symbol_type.st_args }
					  								type_heaps
			  (result_type, type_heaps) = substitute result_type type_heaps
			  (opt_body, var_names, fun_defs, fun_heap)
			  		= case producer of
			  			(PR_Curried {symb_arity, symb_kind=SK_Function {glob_module}})
			  				| glob_module <> cIclModIndex
			  					// we do not have good names for the formal variables of that function: invent some
			  					-> (NoBody, repeatn symb_arity { id_name = "_x", id_info = nilPtr }, fun_defs, fun_heap)
			  				// go further with next alternative
			  			_
							# ({fun_body=fun_body=:TransformedBody tb}, fun_defs, fun_heap)
									= get_fun_def symbol.symb_kind fun_defs fun_heap
							-> (fun_body, take nr_of_applied_args [ fv_name \\ {fv_name}<-tb.tb_args ], fun_defs, fun_heap)
			  (form_vars, act_vars, var_heap) 
			  		= build_var_args (reverse var_names) vars [] var_heap
			  (expr_to_unfold, var_heap)
					= case producer of
						(PR_Curried _)
							-> (VI_Expression (App { app_symb = symbol, app_args = act_vars, app_info_ptr = nilPtr }), var_heap)
						_ // function or generated function
							# (TransformedBody tb) = opt_body
							-> (VI_Body symbol tb (take nr_of_applied_args form_vars), var_heap)
			| nr_of_applied_args<>length cc_linear_bits || nr_of_applied_args<>length cc_args
				= abort "Martin REALLY missed something XXX"
			= (	form_vars
			  , arg_types
			  , result_type
			  , unbounded_type_vars
			  , cc_linear_bits++new_linear_bits
			  , cc_args++new_cons_args
			  , type_heaps
			  , symbol_heap
			  , fun_defs
			  , fun_heap
			  ,	writeVarInfo fv_info_ptr expr_to_unfold var_heap
			  ) 
		  where
			
			get_producer_symbol (PR_Curried symbol)
				= symbol
			get_producer_symbol (PR_Function symbol _)
				= symbol
			get_producer_symbol (PR_GeneratedFunction symbol _)
				= symbol
			
			get_producer_type {symb_kind=SK_Function {glob_module, glob_object}} ro fun_defs fun_heap
				| glob_module == cIclModIndex
					# ({fun_type=Yes symbol_type}, fun_defs) = fun_defs![glob_object]
					= (symbol_type, fun_defs, fun_heap)
				# {ft_type} = ro.ro_imported_funs.[glob_module].[glob_object]
				  st_args = mapAppend (add_types_of_dictionary ro.ro_common_defs) ft_type.st_context ft_type.st_args
				= ({ft_type & st_args = st_args, st_arity = length st_args, st_context = [] },
					fun_defs, fun_heap)
			get_producer_type {symb_kind=SK_GeneratedFunction fun_ptr _} ro fun_defs fun_heap
				# (FI_Function {gf_fun_def={fun_type=Yes symbol_type}}, fun_heap) = readPtr fun_ptr fun_heap
				= (symbol_type, fun_defs, fun_heap)

			calc_cons_args curried {symb_kind, symb_arity} ti_cons_args linear_bit size_fun_defs fun_heap
				# (opt_cons_classes, fun_heap)
						= case symb_kind of
							SK_Function {glob_module, glob_object}
								| glob_module == cIclModIndex && glob_object < size ti_cons_args
									-> (Yes ti_cons_args.[glob_object], fun_heap)
								-> (No, fun_heap)
							SK_GeneratedFunction fun_ptr fun_index
								| fun_index < size ti_cons_args
									-> (Yes ti_cons_args.[fun_index], fun_heap)
								| fun_index < size_fun_defs
									-> abort "sanity check failed in module trans"
								# (FI_Function {gf_cons_args}, fun_heap) = readPtr fun_ptr fun_heap
								-> (Yes gf_cons_args, fun_heap)
				= case opt_cons_classes of
					Yes cons_classes
						| curried
							-> ({ cc_size = symb_arity, cc_args = take symb_arity cons_classes.cc_args, 
					  				cc_linear_bits = repeatn symb_arity linear_bit}, fun_heap)
						-> (cons_classes, fun_heap)
					No
						-> ({cc_size = symb_arity, cc_args = repeatn symb_arity cPassive,
								cc_linear_bits = repeatn symb_arity linear_bit}, fun_heap)

			get_fun_def (SK_Function {glob_module, glob_object}) fun_defs fun_heap
				| glob_module<>cIclModIndex
					= abort "sanity check 2 failed in module trans"
				# (fun_def, fun_defs) = fun_defs![glob_object]
				= (fun_def, fun_defs, fun_heap)
			get_fun_def (SK_GeneratedFunction fun_ptr _) fun_defs fun_heap
				# (FI_Function {gf_fun_def}, fun_heap) = readPtr fun_ptr fun_heap
				= (gf_fun_def, fun_defs, fun_heap)
				
			is_curried (PR_Curried _) = True
			is_curried _ = False
			
		substituteArr :: !*{![AType]} !*TypeHeaps -> (!.{![AType]}, !.TypeHeaps)
		// apply substitute on every array element
		substituteArr arg_types type_heaps
			#! size = size arg_types
			= iFoldSt substitute_element 0 size (arg_types, type_heaps)
		  where
		  	substitute_element i (arg_types, type_heaps)
		  		# (arg_type, arg_types) = arg_types![i]
		  		  (arg_type, type_heaps) = substitute arg_type type_heaps
				= ({ arg_types & [i] = arg_type }, type_heaps)

		build_application_type :: !SymbolType !Int -> AType
		build_application_type symbol_type=:{st_arity, st_context, st_result, st_args} nr_of_applied_args
			# nr_context_args = length st_context
			| st_arity+nr_context_args==nr_of_applied_args
				= st_result
			| nr_of_applied_args<nr_context_args
				= abort "sanity check nr 234 failed in module trans"
			= foldr (\atype1 atype2->{at_attribute=TA_None, at_annotation=AN_None, at_type=atype1-->atype2})
					st_result (drop (nr_of_applied_args-nr_context_args) st_args)

		bind_class_types (TA _ context_types) (TA _ instance_types) type_heaps=:{th_vars}
			# th_vars = bind_context_types context_types instance_types th_vars
			= { type_heaps & th_vars = th_vars }
		where
			bind_context_types [ctype : atypes] [itype : types] th_vars
				= bind_context_types atypes types (bind_type ctype.at_type itype.at_type th_vars)
			bind_context_types [] [] th_vars
				= th_vars
		bind_class_types _ _ th_vars
			= th_vars
			
		bind_type (TV {tv_info_ptr}) type type_var_heap
			= type_var_heap <:= (tv_info_ptr, TVI_Type type)
		bind_type (TA {type_name} arg_types1) (TA _ arg_types2) type_var_heap
			| length arg_types1 == length arg_types2
				= bind_types arg_types1 arg_types2 type_var_heap
				= abort ("bind_type (trans.icl)" ---> (type_name, arg_types1, arg_types2))
		bind_type (CV {tv_info_ptr} :@: arg_types1) (TA type_cons arg_types2) type_var_heap
			# type_arity = type_cons.type_arity - length arg_types1
			  type_var_heap = type_var_heap <:= (tv_info_ptr, TVI_Type (TA {type_cons & type_arity = type_arity} (take type_arity arg_types2)))
			= bind_types arg_types1 (drop type_arity arg_types2) type_var_heap
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
		= ([{ form & fv_info_ptr = new_info_ptr } : vars], writeVarInfo fv_info_ptr (VI_Variable fv_name new_info_ptr) var_heap)

	max_group_index prod_index producers current_max fun_defs fun_heap cons_args
		| prod_index == size producers
			= current_max
			# current_max = max_group_index_of_producer producers.[prod_index] current_max fun_defs fun_heap cons_args
			= max_group_index (inc prod_index) producers current_max fun_defs fun_heap cons_args

	max_group_index_of_producer PR_Empty current_max fun_defs fun_heap cons_args
		= current_max
	max_group_index_of_producer (PR_Class {app_args} _ _) current_max fun_defs fun_heap cons_args
		= max_group_index_of_members app_args current_max fun_defs fun_heap cons_args
	max_group_index_of_producer (PR_Curried _) current_max fun_defs fun_heap cons_args
		= current_max
	max_group_index_of_producer (PR_Function _ fun_index) current_max fun_defs fun_heap cons_args
		# (fun_def, fun_defs) = fun_defs![fun_index]
		= max fun_def.fun_info.fi_group_index current_max
	max_group_index_of_producer (PR_GeneratedFunction { symb_kind = SK_GeneratedFunction fun_ptr fun_index} _)
								current_max fun_defs fun_heap cons_args
		| fun_index < size fun_defs
			# {fun_info} = fun_defs.[fun_index] 
			= max fun_info.fi_group_index current_max
			# (FI_Function generated_function) = sreadPtr fun_ptr fun_heap
			= max generated_function.gf_fun_def.fun_info.fi_group_index current_max
/*
	max_group_index_of_producer (PR_GeneratedFunction { symb_kind = SK_GeneratedFunction fun_ptr _} _ _)
								current_max fun_defs fun_heap cons_args
		# (FI_Function generated_function) = sreadPtr fun_ptr fun_heap
		  fun_def = generated_function.gf_fun_def
		= max fun_def.fun_info.fi_group_index current_max
*/
	max_group_index_of_producer prod current_max fun_defs fun_heap cons_args
		= abort ("trans.icl: max_group_index_of_producer" ---> prod)

	max_group_index_of_member fun_defs fun_heap cons_args current_max (App {app_symb = {symb_name, symb_kind = SK_Function { glob_object = fun_index, glob_module = mod_index}}}) 
		| mod_index == cIclModIndex
			| fun_index < size cons_args
				# {fun_info = {fi_group_index}} = fun_defs.[fun_index]
				= max fi_group_index current_max
			= current_max
		= current_max
	max_group_index_of_member fun_defs fun_heap cons_args current_max (App {app_symb = {symb_kind = SK_GeneratedFunction fun_ptr _ }})
		# (FI_Function {gf_fun_def={fun_info = {fi_group_index}}}) = sreadPtr fun_ptr fun_heap
		= max fi_group_index current_max
	max_group_index_of_member fun_defs fun_heap cons_args current_max (App {app_symb = {symb_kind = SK_Constructor _}, app_args}) 
		= max_group_index_of_members app_args current_max fun_defs fun_heap cons_args
	
	max_group_index_of_members members current_max fun_defs fun_heap cons_args
		= foldl (max_group_index_of_member fun_defs fun_heap cons_args) current_max members
			

(-!->) infix :: !.a !b -> .a | <<< b
(-!->) a b = a ---> b

appTypeVarHeap f type_heaps :== let th_vars = f type_heaps.th_vars in { type_heaps & th_vars = th_vars }

createBindingsForUnifiedTypes :: !AType !AType ![TypeVar] !{#CommonDefs} !*TypeHeaps -> (![TypeVar], !.TypeHeaps)
createBindingsForUnifiedTypes type_1 type_2 all_type_vars common_defs type_heaps=:{th_vars}
	# th_vars = foldSt (\tv th_vars -> th_vars <:= (tv.tv_info_ptr, TVI_Empty)) all_type_vars th_vars
	  (type_heaps=:{th_vars}) = bind_and_unify_atypes type_1 type_2 common_defs { type_heaps & th_vars = th_vars }
//	  th_vars = th_vars -!-> ""
//	  th_vars = foldSt trace_type_var all_type_vars th_vars
	  th_vars = foldSt (\ a b -> snd (set_root_tvi_to_non_variable_type_or_fresh_type_var a b)) all_type_vars th_vars
//	  th_vars = th_vars -!-> ""
//	  th_vars = foldSt trace_type_var all_type_vars th_vars
	  (unsubstituted_type_vars, th_vars) = foldSt bind_to_fresh_type_variable_or_non_variable_type all_type_vars ([], th_vars)
//	  th_vars = th_vars -!-> ""
//	  th_vars = foldSt trace_type_var all_type_vars th_vars
	= (unsubstituted_type_vars, { type_heaps & th_vars = th_vars })
  where
	bind_and_unify_types (TV tv_1) (TV tv_2) common_defs type_heaps=:{th_vars}
		# (root_1, th_vars) = get_root tv_1 th_vars
		  (root_2, th_vars) = get_root tv_2 th_vars
		  maybe_root_tv_1 = only_tv root_1
		  maybe_root_tv_2 = only_tv root_2
		  type_heaps = { type_heaps & th_vars = th_vars }
		= case (maybe_root_tv_1, maybe_root_tv_2) of
						(Yes root_tv_1, No)
							-> appTypeVarHeap (bind_root_variable_to_type root_tv_1 root_2) type_heaps
						(No, Yes root_tv_2)
							-> appTypeVarHeap (bind_root_variable_to_type root_tv_2 root_1) type_heaps
						(Yes root_tv_1, Yes root_tv_2)
							| root_tv_1.tv_info_ptr==root_tv_2.tv_info_ptr
								-> type_heaps
							-> appTypeVarHeap (bind_roots_together root_tv_1 root_2) type_heaps
						(No, No)
							-> bind_and_unify_types root_1 root_2 common_defs type_heaps
	bind_and_unify_types (TV tv_1) type common_defs type_heaps=:{th_vars}
		| not (is_non_variable_type type)
			= abort "compiler error in trans.icl: assertion failed (1) XXX"
		# th_vars = bind_variable_to_type tv_1 type th_vars
		= { type_heaps & th_vars = th_vars }
	bind_and_unify_types type (TV tv_1) common_defs type_heaps=:{th_vars}
		| not (is_non_variable_type type)
			= abort ("compiler error in trans.icl: assertion failed (2) XXX"--->type)
		# th_vars = bind_variable_to_type tv_1 type th_vars
		= { type_heaps & th_vars = th_vars }
	bind_and_unify_types (TA _ arg_types1) (TA _ arg_types2) common_defs type_heaps
		= bind_and_unify_atype_lists arg_types1 arg_types2 common_defs type_heaps
	bind_and_unify_types (l1 --> r1) (l2 --> r2) common_defs type_heaps
		= bind_and_unify_atypes r1 r2 common_defs (bind_and_unify_atypes l1 l2 common_defs type_heaps)
	bind_and_unify_types (TB _) (TB _) common_defs type_heaps
		= type_heaps
	bind_and_unify_types ((CV l1) :@: r1) ((CV l2) :@: r2) common_defs type_heaps
		= bind_and_unify_atype_lists r1 r2 common_defs (bind_and_unify_types (TV l1) (TV l2) common_defs type_heaps)
	bind_and_unify_types (TA type_symb r1) ((CV l2) :@: r2) common_defs type_heaps
		= bind_and_unify_atype_lists r1 r2 common_defs (bind_and_unify_types (TA type_symb []) (TV l2) common_defs type_heaps)
	bind_and_unify_types ((CV l1) :@: r1) (TA type_symb r2) common_defs type_heaps
		= bind_and_unify_atype_lists r1 r2 common_defs (bind_and_unify_types (TV l1) (TA type_symb []) common_defs type_heaps)
	bind_and_unify_types TE y common_defs type_heaps
		= type_heaps
	bind_and_unify_types x TE common_defs type_heaps
		= type_heaps
	bind_and_unify_types x y _ _
		= abort ("bind_and_unify_types"--->(x,y))

	bind_and_unify_atype_lists [] [] common_defs type_heaps
		= type_heaps
	bind_and_unify_atype_lists [x:xs] [y:ys] common_defs type_heaps
		= bind_and_unify_atype_lists xs ys common_defs (bind_and_unify_atypes x y common_defs type_heaps)
	
	bind_and_unify_atypes {at_type=TA type_symb_1 type_args_1} {at_type=TA type_symb_2 type_args_2} common_defs type_heaps
		| type_symb_1==type_symb_2
			= bind_and_unify_atype_lists type_args_1 type_args_2 common_defs type_heaps
		// otherwise further with next alternative ("functional GOTO")
	bind_and_unify_atypes atype_1 atype_2 common_defs type_heaps
		# (mb_expanded_1, type_heaps) = try_to_expand atype_1 common_defs type_heaps
		  (mb_expanded_2, type_heaps) = try_to_expand atype_2 common_defs type_heaps
		= bind_and_unify_types mb_expanded_1 mb_expanded_2 common_defs type_heaps
	  where
		try_to_expand {at_type=actual_type=:TA {type_index={glob_object,glob_module}} actual_args, at_attribute=actual_type_attr}
						common_defs type_heaps
			#! type_def = common_defs.[glob_module].com_type_defs.[glob_object]
			= case type_def.td_rhs of
				SynType {at_type=rhs_type}
					-> expandTypeApplication type_def.td_args type_def.td_attribute rhs_type actual_args actual_type_attr type_heaps
				_
					-> (actual_type, type_heaps)
		try_to_expand {at_type} _ type_heaps
			= (at_type, type_heaps)

	set_root_tvi_to_non_variable_type_or_fresh_type_var :: !TypeVar !*TypeVarHeap -> (!TypeVarInfo,!.TypeVarHeap);
	set_root_tvi_to_non_variable_type_or_fresh_type_var this_tv th_vars
		# (tv_info, th_vars) = readPtr this_tv.tv_info_ptr th_vars
		= case tv_info of
			(TVI_FreshTypeVar fresh_type_var)
				-> (tv_info, th_vars)
			TVI_Empty
				# (fresh_type_var, th_vars) = allocate_fresh_type_variable this_tv.tv_name th_vars
				  th_vars = th_vars <:= (fresh_type_var.tv_info_ptr, TVI_Empty)
				  th_vars = th_vars <:= (this_tv.tv_info_ptr, TVI_FreshTypeVar fresh_type_var)
				-> (TVI_FreshTypeVar fresh_type_var, th_vars)
			(TVI_Type type)
				| is_non_variable_type type
					 -> (tv_info, th_vars)
				-> case type of
					(TV next_tv)
						# (destination, th_vars) = set_root_tvi_to_non_variable_type_or_fresh_type_var next_tv th_vars
						  th_vars = th_vars <:= (this_tv.tv_info_ptr, destination)
						-> (destination, th_vars)
	
	bind_to_fresh_type_variable_or_non_variable_type {tv_info_ptr} (unsubstituted_type_vars_accu, th_vars)
		# (tv_info, th_vars) = readPtr tv_info_ptr th_vars
		= case tv_info of
			(TVI_FreshTypeVar fresh_variable)
				-> ([fresh_variable:unsubstituted_type_vars_accu], th_vars <:= (tv_info_ptr,TVI_Type (TV fresh_variable)))
			(TVI_Type type)
				-> (unsubstituted_type_vars_accu, th_vars)
	
	allocate_fresh_type_variable new_name th_vars
		# new_ident = { id_name=new_name, id_info=nilPtr }
		  (new_tv_info_ptr, th_vars) = newPtr TVI_Empty th_vars
		= ({ tv_name=new_name, tv_info_ptr=new_tv_info_ptr }, th_vars)
							  
	
	only_tv :: Type -> Optional TypeVar
	only_tv (TV tv) = Yes tv
	only_tv _ = No
	
	is_non_variable_type (TA _ _)	= True
	is_non_variable_type (_ --> _)	= True
	is_non_variable_type (_ :@: _)	= True
	is_non_variable_type (TB _)		= True
	is_non_variable_type _			= False
	
	bind_variable_to_type tv type th_vars
		# (root, th_vars) = get_root tv th_vars
		= case (only_tv root) of
			(Yes tv)	-> bind_root_variable_to_type tv type th_vars
			No 			-> th_vars
	
	bind_root_variable_to_type {tv_info_ptr} type th_vars
		= th_vars <:= (tv_info_ptr, TVI_Type type)
	
	bind_roots_together :: TypeVar Type *(Heap TypeVarInfo) -> .Heap TypeVarInfo;
	bind_roots_together root_tv_1 root_type_2 th_vars
		= th_vars <:= (root_tv_1.tv_info_ptr, TVI_Type root_type_2)
	
	get_root :: TypeVar *(Heap TypeVarInfo) -> (Type,.Heap TypeVarInfo);
	get_root this_tv th_vars
		# (tv_info, th_vars) = readPtr this_tv.tv_info_ptr th_vars
		= case tv_info of
			TVI_Empty
				-> (TV this_tv, th_vars)
			(TVI_Type type)
				| is_non_variable_type type
					 -> (type, th_vars)
				-> case type of
					(TV next_tv) -> get_root next_tv th_vars
	// XXX for tracing
	trace_type_var tv th_vars
		= trace_type_vars tv (th_vars -!-> "TYPE VARIABLE")
	
	trace_type_vars this_tv th_vars
		# th_vars = th_vars -!-> this_tv
		# (tv_info, th_vars) = readPtr this_tv.tv_info_ptr th_vars
		= case tv_info of
			TVI_Empty
				-> th_vars
			(TVI_Type type)
				| is_non_variable_type type
					-> (th_vars -!-> ("TVI_Type", type))
				-> case type of
					(TV next_tv) -> trace_type_vars next_tv th_vars
			(TVI_FreshTypeVar root_type_var)
				-> th_vars -!-> ("TVI_FreshTypeVar",root_type_var)

	
transformFunctionApplication fun_def instances cc=:{cc_size, cc_args, cc_linear_bits} app=:{app_symb,app_args} extra_args ro ti
	# (app_symb, app_args, extra_args) = complete_application app_symb fun_def.fun_arity app_args extra_args
	| cc_size > 0
	  	# (producers, new_args, ti) = determineProducers fun_def.fun_info.fi_is_macro_fun cc_linear_bits cc_args app_args
														 0 (createArray cc_size PR_Empty) ro ti
		| ti.ti_trace && False--->("determineProducers",(cc_linear_bits,cc_args,app_args),("results in",II_Node producers nilPtr II_Empty II_Empty))
			= undef
	  	| containsProducer cc_size producers
	  		# (is_new, fun_def_ptr, instances, ti_fun_heap) = tryToFindInstance producers instances ti.ti_fun_heap
	  		| is_new
	  			# (fun_index, fun_arity, ti) = generateFunction fun_def cc producers fun_def_ptr ro
	  					(update_instance_info app_symb.symb_kind instances { ti & ti_fun_heap = ti_fun_heap, ti_trace = False })
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
	update_instance_info (SK_GeneratedFunction fun_def_ptr fun_index) instances ti=:{ti_fun_heap, ti_instances}
		| fun_index < size ti_instances
			= { ti & ti_instances = { ti_instances & [fun_index] = instances } }
		# (FI_Function fun_info, ti_fun_heap) = readPtr fun_def_ptr ti_fun_heap
		= { ti & ti_fun_heap = ti_fun_heap <:= (fun_def_ptr, FI_Function { fun_info & gf_instance_info = instances })}
/*
	update_instance_info (SK_Function {glob_object}) instances ti=:{ti_instances}
		 = { ti & ti_instances = { ti_instances & [glob_object] = instances } }
	update_instance_info (SK_GeneratedFunction fun_def_ptr _) instances ti=:{ti_fun_heap}
		# (FI_Function fun_info, ti_fun_heap) = readPtr fun_def_ptr ti_fun_heap
		= { ti & ti_fun_heap = ti_fun_heap <:= (fun_def_ptr, FI_Function { fun_info & gf_instance_info = instances })}
*/

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
			   (instances, ti_instances) = ti_instances![glob_object]
			   (fun_def, ti_fun_defs) = ti_fun_defs![glob_object]
			= transformFunctionApplication fun_def instances cons_class app extra_args ro { ti & ti_instances = ti_instances, ti_fun_defs = ti_fun_defs }
// It seems as if we have an array function 
			| isEmpty extra_args
				= (App app, ti)
				= (App { app & app_symb = { symb & symb_arity = symb_arity + length extra_args}, app_args = app_args ++ extra_args}, ti)
// This function is imported
		| isEmpty extra_args
			= (App app, ti)
			# {ft_arity,ft_type} = ro.ro_imported_funs.[glob_module].[glob_object]
			  form_arity = ft_arity + length ft_type.st_context
			  ar_diff = form_arity - symb_arity
			  nr_of_extra_args = length extra_args
			| nr_of_extra_args <= ar_diff
				= (App {app  &  app_args = app_args ++ extra_args, app_symb = { symb & symb_arity = symb_arity + nr_of_extra_args }}, ti)
				= (App {app  &  app_args = app_args ++ take ar_diff extra_args, app_symb = { symb & symb_arity = symb_arity + ar_diff }} @
						drop ar_diff extra_args, ti)
				
// XXX linear_bits field has to be added for generated functions
transformApplication app=:{app_symb={symb_name,symb_kind = SK_GeneratedFunction fun_def_ptr fun_index}} extra_args
			ro ti=:{ti_cons_args,ti_instances,ti_fun_defs,ti_fun_heap}
	| fun_index < size ti_cons_args
		#! cons_class = ti_cons_args.[fun_index]
		   (instances, ti_instances) = ti_instances![fun_index]
		   (fun_def, ti_fun_defs) = ti_fun_defs![fun_index]
		= transformFunctionApplication fun_def instances cons_class app extra_args ro { ti & ti_instances = ti_instances, ti_fun_defs = ti_fun_defs }
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

determineProducers _ _ _ [] _ producers _ ti
	= (producers, [], ti)
determineProducers is_applied_to_macro_fun [linear_bit : linear_bits] [ cons_arg : cons_args ] [ arg : args ] prod_index producers ro ti
	# (producers, new_args, ti) = determineProducers is_applied_to_macro_fun linear_bits cons_args args (inc prod_index) producers ro ti
	| cons_arg == cActive
		= determine_producer is_applied_to_macro_fun linear_bit arg new_args prod_index producers ro ti
	= (producers, [arg : new_args], ti)
where
	determine_producer is_applied_to_macro_fun linear_bit arg=:(App app=:{app_info_ptr}) new_args prod_index producers ro ti
		| isNilPtr app_info_ptr
			= determineProducer is_applied_to_macro_fun linear_bit app EI_Empty new_args prod_index producers ro ti
// XXX XXX was			= (producers, [arg : new_args], ti)
			# (app_info, ti_symbol_heap) = readPtr app_info_ptr ti.ti_symbol_heap
			= determineProducer is_applied_to_macro_fun linear_bit app app_info new_args prod_index producers ro { ti & ti_symbol_heap = ti_symbol_heap }
	determine_producer _ _ arg new_args _ producers _ ti
		= (producers, [arg : new_args], ti)

// XXX check for linear_bit also in case of a constructor ?
determineProducer _ _ {app_symb = {symb_arity}, app_args} _ new_args prod_index producers _ ti
	| symb_arity<>length app_args
		= abort "XXX Martin missed something"
determineProducer _ _ app=:{app_symb = symb=:{symb_kind = SK_Constructor _}, app_args} (EI_DictionaryType type) new_args prod_index producers _ ti
	# (app_args, (new_vars, ti_var_heap)) = renewVariables app_args ([], ti.ti_var_heap)
	  (new_args, ti_var_heap) = mapAppendSt retrieve_old_var new_vars new_args ti_var_heap
	= ({ producers & [prod_index] = PR_Class { app & app_args = app_args } new_vars type}, new_args, { ti & ti_var_heap = ti_var_heap })
  where
	retrieve_old_var {var_info_ptr} var_heap
		# (var_info, var_heap) = readVarInfo var_info_ptr var_heap
		  (VI_Forward var) = var_info
		= (Var var, writeVarInfo var_info_ptr VI_Empty (writeVarInfo var.var_info_ptr VI_Empty var_heap))
determineProducer is_applied_to_macro_fun linear_bit app=:{app_symb = symb=:{symb_kind = SK_Function { glob_module, glob_object }, symb_arity}, app_args} _
				  new_args prod_index producers ro ti
	# (fun_arity, ti) = get_fun_arity glob_module glob_object ro ti
	| symb_arity<>fun_arity
		| is_applied_to_macro_fun
			= ({ producers & [prod_index] = PR_Curried symb}, app_args ++ new_args, ti)
		= (producers, [App app : new_args ], ti)
	#! max_index = size ti.ti_cons_args
	| glob_module <> cIclModIndex || glob_object >= max_index /* Sjaak, to skip array functions */
		= (producers, [App app : new_args ], ti)
	# ({fun_body}, ti_fun_defs) = (ti.ti_fun_defs)![glob_object]
	  ti = { ti & ti_fun_defs=ti_fun_defs }
	  (TransformedBody {tb_rhs}) = fun_body
	  is_good_producer = SwitchFusion (linear_bit && is_sexy_body tb_rhs) False
	| is_good_producer
		= ({ producers & [prod_index] = (PR_Function symb glob_object)}, app_args ++ new_args, ti)
	= (producers, [App app : new_args ], ti)
  where
	get_fun_arity glob_module glob_object ro ti
		| glob_module <> cIclModIndex
			# {st_arity, st_context} = ro.ro_imported_funs.[glob_module].[glob_object].ft_type
			= (st_arity+length st_context, ti)
		// for imported functions you have to add ft_arity and length st_context, but for unimported
		// functions fun_arity alone is sufficient
		# ({fun_arity}, ti_fun_defs) = (ti.ti_fun_defs)![glob_object]
		= (fun_arity, { ti & ti_fun_defs=ti_fun_defs })
determineProducer is_applied_to_macro_fun linear_bit app=:{app_symb = symb=:{ symb_kind = SK_GeneratedFunction fun_ptr fun_index, symb_arity}, app_args} _
				  new_args prod_index producers ro ti
	# (FI_Function {gf_fun_def={fun_body, fun_arity, fun_type=Yes symbol_type}}, ti_fun_heap) = readPtr fun_ptr ti.ti_fun_heap
	  ti = { ti & ti_fun_heap=ti_fun_heap }
	  is_overloaded = length symbol_type.st_context>0
	| is_overloaded // XXX this restriction (producers must not be overloaded) is just temporary 
		= (producers, [App app : new_args ], ti)
	| symb_arity<>fun_arity
		| is_applied_to_macro_fun
			= ({ producers & [prod_index] = PR_Curried symb}, app_args ++ new_args, ti)
		= (producers, [App app : new_args ], ti)
	# is_good_producer
		= case fun_body of
			Expanding _
				-> False
			(TransformedBody {tb_rhs})
				-> SwitchFusion (linear_bit && is_sexy_body tb_rhs) False
	| is_good_producer
		= ({ producers & [prod_index] = (PR_GeneratedFunction symb fun_index)}, app_args ++ new_args, ti)
	= (producers, [App app : new_args ], ti)
// XXX determineProducer {app_symb = symb=:{symb_kind = SK_Constructor glob_index}, app_args} new_args prod_index producers ti
//	= ({ producers & [prod_index] = PR_Constructor symb app_args}, new_args, ti)
// XXX */
determineProducer _ _ app _ new_args _ producers _ ti
	= (producers, [App app : new_args ], ti)
	
// when two function bodies have fusion with each other this only leads into satisfaction if one body
// fulfills the following sexyness property
is_sexy_body (AnyCodeExpr _ _ _) = False	
is_sexy_body (ABCCodeExpr _ _) = False	
is_sexy_body (Let {let_strict_binds}) = isEmpty let_strict_binds	
	// currently a producer's body must not be a let with strict bindings. The code sharing elimination algorithm assumes that
	// all strict let bindings are on the top level expression (see "convertCasesOfFunctionsIntoPatterns"). This assumption
	// could otherwise be violated during fusion.
	// -> Here is place for optimisation: Either the fusion algorithm or the code sharing elimination algorithm could be
	// extended to generate new functions when a strict let ends up during fusion in a non top level position (MW)
is_sexy_body _ = True	


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
		# (var_info, var_heap) = readVarInfo var_info_ptr var_heap
		= case var_info of
			VI_Forward new_var
				-> (Var { var & var_info_ptr = new_var.var_info_ptr }, (new_vars, var_heap))
			_	# (new_info_ptr, var_heap) = newPtr (VI_Forward var) var_heap
				  new_var = { var & var_info_ptr = new_info_ptr }
				  var_heap = writeVarInfo var_info_ptr (VI_Forward new_var) var_heap
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

transformGroups :: !CleanupInfo !*{! Group} !*{#FunDef} !{!.ConsClasses} !{# CommonDefs}  !{# {# FunType} }
		!*{#{# CheckedTypeDef}} !ImportedConstructors !*VarHeap !*TypeHeaps !*ExpressionHeap
			-> (!*{! Group}, !*{#FunDef}, !*{#{# CheckedTypeDef}}, !ImportedConstructors, !*VarHeap, !*TypeHeaps, !*ExpressionHeap)

transformGroups cleanup_info  groups fun_defs cons_args common_defs imported_funs imported_types collected_imports var_heap type_heaps symbol_heap
	#! (nr_of_funs, fun_defs) = usize fun_defs
	# (groups, imported_types, collected_imports, ti)
		= transform_groups 0 groups common_defs imported_funs imported_types collected_imports
			{ti_fun_defs = fun_defs, ti_instances = createArray nr_of_funs II_Empty,
				ti_cons_args = cons_args, ti_new_functions = [], ti_fun_heap = newHeap, ti_var_heap = var_heap,
				ti_symbol_heap = symbol_heap, ti_type_heaps = type_heaps, ti_next_fun_nr = nr_of_funs, ti_cleanup_info = cleanup_info,
				ti_recursion_introduced = No, ti_trace = False }
	  {ti_fun_defs,ti_new_functions,ti_var_heap,ti_symbol_heap,ti_fun_heap,ti_next_fun_nr,ti_type_heaps,ti_cleanup_info} = ti
	  (groups, new_fun_defs, imported_types, collected_imports, ti_type_heaps, ti_var_heap) 
	  		= foldSt (add_new_function_to_group common_defs ti_fun_heap) ti_new_functions
	  				(groups, [], imported_types, collected_imports, ti_type_heaps, ti_var_heap)
	  ti_symbol_heap = foldSt cleanup ti_cleanup_info ti_symbol_heap
	= ( groups, { fundef \\ fundef <- [ fundef \\ fundef <-: ti_fun_defs ] ++ new_fun_defs }, imported_types, collected_imports,
			ti_var_heap, ti_type_heaps, ti_symbol_heap)

where
	transform_groups group_nr groups common_defs imported_funs imported_types collected_imports ti
		| group_nr < size groups
			# (group, groups) = groups![group_nr]
			# {group_members} = group
			# (ti_fun_defs, imported_types, collected_imports, ti_type_heaps, ti_var_heap) 
					= foldSt (convert_function_type common_defs) group_members
							(ti.ti_fun_defs, imported_types, collected_imports, ti.ti_type_heaps, ti.ti_var_heap)
			= transform_groups (inc  group_nr) groups common_defs imported_funs imported_types collected_imports
					(foldSt (transform_function common_defs imported_funs) group_members
						{ ti & ti_fun_defs = ti_fun_defs, ti_type_heaps = ti_type_heaps, ti_var_heap = ti_var_heap })
			= (groups, imported_types, collected_imports, ti)

	transform_function common_defs imported_funs fun ti=:{ti_fun_defs}
		# (fun_def, ti_fun_defs) = ti_fun_defs![fun]
		# {fun_body = TransformedBody tb} = fun_def
		  ro =	{	ro_imported_funs	= imported_funs
				,	ro_common_defs 		= common_defs
				,	ro_root_case_mode	= get_root_case_mode tb
				,	ro_fun				= fun_def_to_symb_ident fun fun_def
				,	ro_fun_args			= tb.tb_args
				}
		  (fun_rhs, ti) = transform tb.tb_rhs ro { ti & ti_fun_defs = ti_fun_defs }
		= { ti & ti_fun_defs = {ti.ti_fun_defs & [fun] = { fun_def & fun_body = TransformedBody { tb & tb_rhs = fun_rhs }}}}
	  where
		fun_def_to_symb_ident fun_index {fun_symb,fun_arity}
			= { symb_name=fun_symb, symb_kind=SK_Function {glob_object=fun_index, glob_module=cIclModIndex } , symb_arity=fun_arity }

		get_root_case_mode {tb_rhs=Case _}	= RootCase
		get_root_case_mode _ 				= NotRootCase

	add_new_function_to_group ::  !{# CommonDefs} !FunctionHeap  !FunctionInfoPtr !(!*{! Group}, ![FunDef], !*{#{# CheckedTypeDef}}, !ImportedConstructors, !*TypeHeaps, !*VarHeap)
		-> (!*{! Group}, ![FunDef], !*{#{# CheckedTypeDef}}, !ImportedConstructors, !*TypeHeaps, !*VarHeap)
	add_new_function_to_group common_defs ti_fun_heap fun_ptr (groups, fun_defs, imported_types, collected_imports, type_heaps, var_heap)
		# (FI_Function {gf_fun_def,gf_fun_index}) = sreadPtr fun_ptr ti_fun_heap
		  group_index = gf_fun_def.fun_info.fi_group_index
		# (Yes ft=:{st_args,st_result}) = gf_fun_def.fun_type
		  ((st_result,st_args), {ets_type_defs, ets_collected_conses, ets_type_heaps, ets_var_heap}) = expandSynTypes common_defs (st_result,st_args)
		  		{ ets_type_defs = imported_types, ets_collected_conses = collected_imports, ets_type_heaps = type_heaps, ets_var_heap = var_heap }
		# (group, groups) = groups![group_index]
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

set_extended_expr_info expr_info_ptr extension expr_info_heap
	# (expr_info, expr_info_heap) = readPtr expr_info_ptr expr_info_heap
	= case expr_info of
		EI_Extended _ ei
			-> expr_info_heap <:= (expr_info_ptr, EI_Extended extension ei)
		ei	-> expr_info_heap <:= (expr_info_ptr, EI_Extended extension ei)
		
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

add_types_of_dictionary common_defs {tc_class = {glob_module, glob_object={ds_index}}, tc_types}
	# {class_arity, class_dictionary={ds_ident,ds_index}} = common_defs.[glob_module].com_class_defs.[ds_index]
	  dict_type_symb = 	MakeTypeSymbIdent { glob_object = ds_index, glob_module = glob_module } ds_ident class_arity
	= { at_attribute = TA_Multi, at_annotation = AN_Strict, at_type = TA dict_type_symb (
			map (\type -> { at_attribute = TA_Multi, at_annotation = AN_None, at_type = type }) tc_types) }

instance expandSynTypes Type
where
	expandSynTypes common_defs (arg_type --> res_type) ets
		# ((arg_type, res_type), ets) = expandSynTypes common_defs (arg_type, res_type) ets
		= (arg_type --> res_type, ets)
	expandSynTypes common_defs type=:(TB _) ets
		= (type, ets)
	expandSynTypes common_defs (cons_var :@: types) ets
		# (types, ets) = expandSynTypes common_defs types ets
		= (cons_var :@: types, ets) 
	expandSynTypes common_defs type=:(TA type_symb types) ets
		= expand_syn_types_in_TA common_defs type_symb types TA_Multi ets
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

expand_syn_types_in_TA common_defs type_symb=:{type_index={glob_object,glob_module},type_name} types attribute ets=:{ets_type_defs}
	# ({td_rhs,td_name,td_args,td_attribute},ets_type_defs) = ets_type_defs![glob_module].[glob_object]
	  ets = { ets & ets_type_defs = ets_type_defs }
	= case td_rhs of
		SynType rhs_type
			# ets_type_heaps = bind_attr td_attribute attribute ets.ets_type_heaps
			  ets_type_heaps = (fold2St bind_var_and_attr td_args types ets_type_heaps)
			  (type, ets_type_heaps) = substitute rhs_type.at_type ets_type_heaps
			-> expandSynTypes common_defs type { ets & ets_type_heaps = ets_type_heaps }
		_
			# (types, ets) = expandSynTypes common_defs types ets
			| glob_module == cIclModIndex
				-> ( TA type_symb types, ets)
				-> ( TA type_symb types, collect_imported_constructors common_defs glob_module td_rhs ets)
where
		bind_var_and_attr {	atv_attribute = TA_Var {av_info_ptr},  atv_variable = {tv_info_ptr} } {at_attribute,at_type} type_heaps=:{th_vars,th_attrs}
			= { type_heaps & th_vars = th_vars <:= (tv_info_ptr, TVI_Type at_type), th_attrs = th_attrs <:= (av_info_ptr, AVI_Attr at_attribute) }
		bind_var_and_attr { atv_variable  = {tv_info_ptr}} {at_type} type_heaps=:{th_vars}
			= { type_heaps & th_vars = th_vars <:= (tv_info_ptr, TVI_Type at_type) }

		bind_attr (TA_Var {av_info_ptr}) attribute type_heaps=:{th_attrs}
			= { type_heaps & th_attrs = th_attrs <:= (av_info_ptr, AVI_Attr attribute) }
		bind_attr _ attribute type_heaps
			= type_heaps

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
			  (type_info, var_heap) = readVarInfo cons_type_ptr var_heap
			| has_been_collected type_info
				= (collected_conses, var_heap)
				= ([{ glob_module = mod_index, glob_object = ds_index } : collected_conses ], writeVarInfo cons_type_ptr VI_Used var_heap)

		has_been_collected VI_Used				= True
		has_been_collected (VI_ExpandedType _)	= True
		has_been_collected _					= False


instance expandSynTypes AType
where
	expandSynTypes common_defs atype ets
		= expand_syn_types_in_a_type common_defs atype ets
	where
		expand_syn_types_in_a_type common_defs atype=:{at_type = TA type_symb types, at_attribute} ets
			# (at_type, ets) = expand_syn_types_in_TA common_defs type_symb types at_attribute ets
			= ({ atype & at_type = at_type }, ets)
		expand_syn_types_in_a_type common_defs atype ets
			# (at_type, ets) = expandSynTypes common_defs atype.at_type ets
			= ({ atype & at_type = at_type }, ets)

::	FreeVarInfo =
	{	fvi_var_heap	:: !.VarHeap
	,	fvi_expr_heap	:: !.ExpressionHeap
	,	fvi_variables	:: ![BoundVar]
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
		= writeVarInfo fv_info_ptr VI_LocalVar var_heap

	filter_local_var v=:{var_info_ptr} (global_vars, var_heap)
		# (var_info, var_heap) = readVarInfo var_info_ptr var_heap
		= case var_info of
			VI_LocalVar
				-> (global_vars, var_heap)
			_
				-> ([ v : global_vars ], var_heap)

instance freeVariables BoundVar
where
	freeVariables bound_var=:{var_info_ptr} fvi=:{fvi_var_heap, fvi_variables}
		# (var_info, fvi_var_heap) = readVarInfo var_info_ptr fvi_var_heap
		  (fvi_variables, fvi_var_heap) = adjust_var_info bound_var var_info fvi_variables fvi_var_heap
		= {fvi & fvi_variables = fvi_variables, fvi_var_heap = fvi_var_heap }
	where
		adjust_var_info _ (VI_UsedVar _) fvi_variables fvi_var_heap
			= (fvi_variables, fvi_var_heap)
		adjust_var_info bound_var=:{var_name} _ fvi_variables fvi_var_heap
			= ([bound_var : fvi_variables], writeVarInfo var_info_ptr (VI_UsedVar var_name) fvi_var_heap)

instance freeVariables Expression
where
	freeVariables (Var var) fvi
		= freeVariables var fvi
	freeVariables (App {app_args}) fvi
		= freeVariables app_args fvi
	freeVariables (fun @ args) fvi
		= freeVariables args (freeVariables fun fvi)
	freeVariables (Let {let_strict_binds,let_lazy_binds,let_expr,let_info_ptr}) fvi=:{fvi_variables = global_variables}
		# let_binds = let_strict_binds ++ let_lazy_binds
		  (removed_variables, fvi_var_heap) = removeVariables global_variables fvi.fvi_var_heap
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
		= freeVariables expr2 (freeVariables selectors (freeVariables expr1 fvi))
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

instance freeVariables Selection
where
	freeVariables (RecordSelection _ _) fvi
		= fvi
	freeVariables (ArraySelection _ _ expr) fvi
		= freeVariables expr fvi
	freeVariables (DictionarySelection dict_var selections _ expr) fvi
		= freeVariables dict_var (freeVariables selections (freeVariables expr fvi))
	
removeVariables global_variables var_heap
	= foldSt remove_variable global_variables ([], var_heap)
where
	remove_variable v=:{var_info_ptr} (removed_variables, var_heap)
		# (VI_UsedVar used_var, var_heap) = readVarInfo var_info_ptr var_heap
		= ([(v, used_var) : removed_variables], writeVarInfo var_info_ptr VI_Empty var_heap)

restoreVariables removed_variables global_variables var_heap
	= foldSt restore_variable removed_variables (global_variables, var_heap)
where
	restore_variable (v=:{var_info_ptr}, var_id) (restored_variables, var_heap)
		# (var_info, var_heap) = readVarInfo var_info_ptr var_heap
		= case var_info of
			VI_UsedVar _
				-> (restored_variables, var_heap)
			_
				-> ([ v : restored_variables ], writeVarInfo var_info_ptr (VI_UsedVar var_id) var_heap)

// XXX doet deze funktie iets ?
determineGlobalVariables global_variables var_heap
	= foldSt determine_global_variable global_variables ([], var_heap)
where		
	determine_global_variable {var_info_ptr} (global_variables, var_heap)
		# (VI_UsedVar v_name, var_heap) = readVarInfo var_info_ptr var_heap
		= ([{var_name = v_name, var_info_ptr = var_info_ptr, var_expr_ptr = nilPtr} : global_variables], var_heap)

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
		(EI_Extended (EEI_ActiveCase aci) original_expr_info)
			-> writePtr expr_info_ptr (EI_Extended (EEI_ActiveCase (transformer aci)) original_expr_info) expr_heap
		_	-> expr_heap

getTypeVars types
	# (type_variables,_) = get_type_vars types ([],[])
	= removeDuplicates smaller_type_vars type_variables

removeDuplicates smaller l
	// XXX speed this up by using heap
	# sorted = quicksort smaller l
	  partitions = partitionate sorted
	= flatten [removeDup uneq partition \\ partition<-partitions]
  where
	partitionate []
		= []
	partitionate [h:t]
		= partitions_with t [h]
	partitions_with [] accu
		= [accu]
	partitions_with [h2:t] accu=:[h:_]
		| h.tv_name.id_name==h2.tv_name.id_name
			= partitions_with t [h2:accu]
		= [accu:partitions_with t [h2]]
	removeDup uneq [x:xs] = [x:removeDup uneq (filter (uneq x) xs)]
	removeDup uneq _      = []
	uneq {tv_info_ptr=p1} {tv_info_ptr=p2}
		= p1<>p2
		
quicksort _ []
	= []
quicksort smaller [h:t]
	# left = [ el \\ el<-t | smaller el h ]
	  right = [ el \\ el<-t | not (smaller el h) ]
	= (quicksort smaller left)++[h]++(quicksort smaller right)

smaller_type_vars {tv_name={id_name=n1}} {tv_name={id_name=n2}}
	= n1<n2

undeff :== -1

class get_type_vars a :: a !(![TypeVar], ![AttributeVar]) -> (![TypeVar], ![AttributeVar])

instance get_type_vars Type
  where
	get_type_vars (TA _ args) accu
		= get_type_vars args accu
	get_type_vars (at1 --> at2) accu
		= get_type_vars at2 (get_type_vars at1 accu)
	get_type_vars (cv :@: at) accu
		= get_type_vars cv (get_type_vars at accu)
	get_type_vars (GTV t_var) (t_vars,a_vars)
		= ([t_var:t_vars], a_vars)
	get_type_vars (TV t_var) (t_vars,a_vars)
		= ([t_var:t_vars], a_vars)
	get_type_vars (TQV t_var) (t_vars,a_vars)
		= ([t_var:t_vars], a_vars)
	get_type_vars _ accu
		= accu

instance get_type_vars AType
  where
	get_type_vars {at_attribute, at_type} accu
		= get_type_vars at_attribute (get_type_vars at_type accu)

instance get_type_vars ConsVariable
  where
	get_type_vars (CV t_var) (t_vars,a_vars)
		= ([t_var:t_vars], a_vars)

instance get_type_vars TypeAttribute
  where
	get_type_vars (TA_Var a_var) (t_vars,a_vars)
		= (t_vars, [a_var:a_vars])
	get_type_vars (TA_RootVar a_var) (t_vars,a_vars)
		= (t_vars, [a_var:a_vars])
	get_type_vars (TA_List _ ta) accu
		= get_type_vars ta accu
	get_type_vars _ accu
		= accu

instance get_type_vars [a] | get_type_vars a
  where
	get_type_vars [] accu
		= accu
	get_type_vars [h:t] accu
		= get_type_vars t (get_type_vars h accu)

instance get_type_vars (a, b) | get_type_vars a & get_type_vars b
  where
	get_type_vars (a, b) accu
		= get_type_vars a (get_type_vars b accu)


/*
instance <<< InstanceInfo
where
	(<<<) file (II_Node prods _ left right) = file <<< left <<< prods <<< right 
	(<<<) file II_Empty = file 
*/	

// XXX	
instance <<< Producer
where
	(<<<) file (PR_Function symbol index)
		= file <<< "(F)" <<< symbol.symb_name
	(<<<) file (PR_GeneratedFunction symbol index)
		= file <<< "(G)" <<< symbol.symb_name <<< index
	(<<<) file PR_Empty = file <<< 'E'
	(<<<) file (PR_Class _ _ _) = file <<< "(Class)"
	(<<<) file (PR_Curried {symb_name}) = file <<< "(Curried)" <<< symb_name
	(<<<) file _ = file

instance <<< FunCall
where
	(<<<) file {fc_index} = file <<< fc_index
	
instance <<< ConsClasses
where
	(<<<) file {cc_args,cc_linear_bits} = file <<< cc_args <<< cc_linear_bits
	
instance <<< InstanceInfo
  where
	(<<<) file ii = (write_ii ii (file <<< "[")) <<< "]"
	  where
		write_ii II_Empty file
			= file
		write_ii (II_Node producers _ l r) file
			# file = write_ii l file <<< "("
			  file = foldSt (\pr file -> file<<<pr<<<",") [el \\ el<-:producers] file
			= write_ii r (file<<<")")

instance <<< (Ptr a)
where
	(<<<) file p = file <<< ptrToInt p

