implementation module trans

import StdEnv

import syntax, transform, checksupport, StdCompare, check, utilities, unitype, typesupport, type

SwitchCaseFusion		fuse dont_fuse :== dont_fuse
SwitchGeneratedFusion	fuse dont_fuse :== dont_fuse
SwitchFunctionFusion	fuse dont_fuse :== dont_fuse
SwitchConstructorFusion	fuse dont_fuse :== dont_fuse
SwitchCurriedFusion		fuse dont_fuse :== dont_fuse

(-!->) infix :: !.a !b -> .a | <<< b
(-!->) a b = a // ---> b

::	CleanupInfo :== [ExprInfoPtr]

fromYes (Yes x) = x

is_SK_Function_or_SK_LocalMacroFunction (SK_Function _) = True
is_SK_Function_or_SK_LocalMacroFunction (SK_LocalMacroFunction _) = True
is_SK_Function_or_SK_LocalMacroFunction _ = False

undeff :== -1

empty_atype = { at_attribute = TA_Multi, at_type = TE }

get_producer_symbol (PR_Curried symbol arity)
	= (symbol,arity)
get_producer_symbol (PR_Function symbol arity _)
	= (symbol,arity)
get_producer_symbol (PR_GeneratedFunction symbol arity _)
	= (symbol,arity)
get_producer_symbol (PR_Constructor symbol arity _)
	= (symbol,arity)

/*
 *	PARTITIONING
 */

::	PartitioningInfo = 
	{	pi_marks :: 		!.{# Int}
	,	pi_next_num ::		!Int
	,	pi_next_group ::	!Int
	,	pi_groups ::		![[Int]]
	,	pi_deps ::			![Int]
	}

NotChecked :== -1	
/*
implies a b :== not a || b
*/
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
			with
				visit_functions :: ![FunCall] !Int !Int !*{# FunDef} !*PartitioningInfo -> *(!Int, !*{# FunDef}, !*PartitioningInfo)
				visit_functions [FunCall fc_index _:funs] min_dep max_fun_nr fun_defs pi=:{pi_marks} 
					#! mark = pi_marks.[fc_index]
					| mark == NotChecked
						# (mark, fun_defs, pi) = partitionate_function fc_index max_fun_nr fun_defs  pi
						= visit_functions funs (min min_dep mark) max_fun_nr fun_defs pi
						= visit_functions funs (min min_dep mark) max_fun_nr fun_defs pi
				
				visit_functions [MacroCall module_index fc_index _:funs] min_dep max_fun_nr fun_defs pi
					= abort ("visit_functions "+++toString fd.fun_symb+++" "+++toString module_index+++" "+++toString fc_index)
				
				visit_functions [] min_dep max_fun_nr fun_defs pi
					= (min_dep, fun_defs, pi)
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
			# (fd,fun_defs) = fun_defs![d]
			# fun_defs = { fun_defs & [d] = { fd & fun_info.fi_group_index = group_number }}
			| d == fun_index
				= (ds, marks, [d : group], fun_defs)
				= close_group fun_index ds marks [d : group] max_fun_nr group_number fun_defs
/*
::	BitVector :== Int
*/

/*
 *	ANALYSIS: only determines consumerClass; producerClasses are determined after each group is transformed.
 */

::	*AnalyseInfo =
	{	ai_var_heap						:: !*VarHeap
	,	ai_cons_class					:: !*{! ConsClasses}
	,	ai_cur_ref_counts				:: !*{#Int} // for each variable 0,1 or 2
	,	ai_class_subst					:: !* ConsClassSubst
	,	ai_next_var						:: !Int
	,	ai_next_var_of_fun				:: !Int
	,	ai_cases_of_vars_for_function	:: ![Case]
	}

/*	defined in syntax.dcl:

::	ConsClasses =
	{	cc_size			::!Int
	,	cc_args			::![ConsClass]
	,	cc_linear_bits	::![Bool]
	,	cc_producer		::!ProdClass
	}
::	ConsClass		:== Int
*/

::	ConsClassSubst	:== {# ConsClass}

//cNoFunArg		:== -1
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

IsAVariable cons_class	:== cons_class >= 0

combineClasses :: !ConsClass !ConsClass -> ConsClass
combineClasses cc1 cc2
	| IsAVariable cc1
		= cAccumulating
	| IsAVariable cc2
		= cAccumulating
		= min cc1 cc2
 
aiUnifyClassifications cc1 cc2 ai
	:== {ai & ai_class_subst = unifyClassifications cc1 cc2 ai.ai_class_subst}

unifyClassifications :: !ConsClass !ConsClass !*ConsClassSubst -> *ConsClassSubst
unifyClassifications cc1 cc2 subst
	#  (cc1,subst) = skip_indirections_of_variables cc1 subst
	   (cc2,subst) = skip_indirections_of_variables cc2 subst
	= combine_cons_classes cc1 cc2 subst
where		   
	skip_indirections_of_variables :: !ConsClass !*ConsClassSubst -> (!ConsClass,!*ConsClassSubst)
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
			
	combine_cons_classes :: !ConsClass !ConsClass !*ConsClassSubst -> *ConsClassSubst
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
				   
	combine_cons_constants :: !ConsClass !ConsClass -> ConsClass
	combine_cons_constants cc1 cc2
		= min cc1 cc2
/*
write_ptr ptr val heap mess
	| isNilPtr ptr
		= abort mess
		= heap <:=  (ptr,val)
*/

// Extended variable info accessors...

readVarInfo :: VarInfoPtr *VarHeap -> (VarInfo, !*VarHeap)
readVarInfo var_info_ptr var_heap
	# (var_info, var_heap) = readPtr var_info_ptr var_heap
	= case var_info of
		VI_Extended _ original_var_info	-> (original_var_info, var_heap)
		_								-> (var_info, var_heap)

readExtendedVarInfo :: VarInfoPtr *VarHeap -> (ExtendedVarInfo, !*VarHeap)
readExtendedVarInfo var_info_ptr var_heap
	# (var_info, var_heap) = readPtr var_info_ptr var_heap
	= case var_info of
		VI_Extended extensions _	-> (extensions, var_heap)

writeVarInfo :: VarInfoPtr VarInfo *VarHeap -> *VarHeap
writeVarInfo var_info_ptr new_var_info var_heap
	# (old_var_info, var_heap) = readPtr var_info_ptr var_heap
	= case old_var_info of
		VI_Extended extensions _	-> writePtr var_info_ptr (VI_Extended extensions new_var_info) var_heap
		_							-> writePtr var_info_ptr new_var_info var_heap

setExtendedVarInfo :: !VarInfoPtr !ExtendedVarInfo !*VarHeap -> *VarHeap
setExtendedVarInfo var_info_ptr extension var_heap
	# (old_var_info, var_heap) = readPtr var_info_ptr var_heap
	= case old_var_info of
		VI_Extended _ original_var_info	-> writePtr var_info_ptr (VI_Extended extension original_var_info) var_heap
		_								-> writePtr var_info_ptr (VI_Extended extension old_var_info) var_heap

// Extended expression info accessors...

readExprInfo :: !ExprInfoPtr !*ExpressionHeap -> (!ExprInfo,!*ExpressionHeap)
readExprInfo expr_info_ptr symbol_heap
	# (expr_info, symbol_heap) = readPtr expr_info_ptr symbol_heap
	= case expr_info of
		EI_Extended _ ei	-> (ei, symbol_heap)
		_					-> (expr_info, symbol_heap)

writeExprInfo :: !ExprInfoPtr !ExprInfo !*ExpressionHeap -> *ExpressionHeap
writeExprInfo expr_info_ptr new_expr_info symbol_heap
	# (expr_info, symbol_heap) = readPtr expr_info_ptr symbol_heap
	= case expr_info of
		EI_Extended extensions _	-> writePtr expr_info_ptr (EI_Extended extensions new_expr_info) symbol_heap
		_							-> writePtr expr_info_ptr new_expr_info symbol_heap

setExtendedExprInfo :: !ExprInfoPtr !ExtendedExprInfo !*ExpressionHeap -> *ExpressionHeap
setExtendedExprInfo expr_info_ptr extension expr_info_heap
	# (expr_info, expr_info_heap) = readPtr expr_info_ptr expr_info_heap
	= case expr_info of
		EI_Extended _ ei
			-> expr_info_heap <:= (expr_info_ptr, EI_Extended extension ei)
		ei	-> expr_info_heap <:= (expr_info_ptr, EI_Extended extension ei)
		
app_EEI_ActiveCase transformer expr_info_ptr expr_heap
	# (expr_info, expr_heap) = readPtr expr_info_ptr expr_heap
	= case expr_info of
		(EI_Extended (EEI_ActiveCase aci) original_expr_info)
			-> writePtr expr_info_ptr (EI_Extended (EEI_ActiveCase (transformer aci)) original_expr_info) expr_heap
		_	-> expr_heap

set_aci_free_vars_info_case unbound_variables case_info_ptr expr_heap
	= app_EEI_ActiveCase (\aci -> { aci & aci_free_vars=Yes unbound_variables }) case_info_ptr expr_heap

remove_aci_free_vars_info case_info_ptr expr_heap
	= app_EEI_ActiveCase (\aci->{aci & aci_free_vars = No }) case_info_ptr expr_heap

cleanup_attributes expr_info_ptr symbol_heap
	# (expr_info, symbol_heap) = readPtr expr_info_ptr symbol_heap
	= case expr_info of
		EI_Extended _ expr_info -> writePtr expr_info_ptr expr_info symbol_heap
		_ -> symbol_heap

//@ Consumer Analysis datatypes...

:: ConsumerAnalysisRO = ConsumerAnalysisRO !ConsumerAnalysisRORecord;

:: ConsumerAnalysisRORecord = {common_defs::!{# CommonDefs},imported_funs::!{#{#FunType}},main_dcl_module_n::!Int,stdStrictLists_module_n::!Int}

::	UnsafePatternBool :== Bool

not_an_unsafe_pattern (cc, _, ai) = (cc, False, ai)

//@ consumerRequirements

class consumerRequirements a :: !a !ConsumerAnalysisRO !AnalyseInfo -> (!ConsClass, !UnsafePatternBool, !AnalyseInfo)

instance consumerRequirements BoundVar
where
	consumerRequirements {var_name,var_info_ptr} _ ai=:{ai_var_heap}
		# (var_info, ai_var_heap)	= readPtr var_info_ptr ai_var_heap
		  ai						= { ai & ai_var_heap=ai_var_heap }
		= case var_info of
			VI_AccVar temp_var arg_position
				#! (ref_count,ai)	= ai!ai_cur_ref_counts.[arg_position] 
				   ai				= { ai & ai_cur_ref_counts.[arg_position] = min (ref_count+1) 2 }
				-> (temp_var, False, ai)
			_
				-> abort ("consumerRequirements" ---> (var_name))

instance consumerRequirements Expression where
	consumerRequirements (Var var) common_defs ai
		= consumerRequirements var common_defs ai
	consumerRequirements (App app) common_defs ai
		= consumerRequirements app common_defs ai
	consumerRequirements (fun_expr @ exprs) common_defs ai
		# (cc_fun, _, ai)			= consumerRequirements fun_expr common_defs ai
		  ai						= aiUnifyClassifications cActive cc_fun ai
		= consumerRequirements exprs common_defs ai
	consumerRequirements (Let {let_strict_binds, let_lazy_binds,let_expr}) common_defs ai=:{ai_next_var,ai_next_var_of_fun,ai_var_heap}
		# let_binds					= let_strict_binds ++ let_lazy_binds
		# (new_next_var, new_ai_next_var_of_fun, ai_var_heap)
									= init_variables let_binds ai_next_var ai_next_var_of_fun ai_var_heap
		# ai						= { ai & ai_next_var = new_next_var, ai_next_var_of_fun = new_ai_next_var_of_fun, ai_var_heap = ai_var_heap }
		# ai						= acc_requirements_of_let_binds let_binds ai_next_var common_defs ai
		= consumerRequirements let_expr common_defs ai // XXX why not not_an_unsafe_pattern
		where
			init_variables [{lb_dst={fv_count, fv_info_ptr}} : binds] ai_next_var ai_next_var_of_fun ai_var_heap
				| fv_count > 0
					# ai_var_heap = writePtr fv_info_ptr (VI_AccVar ai_next_var ai_next_var_of_fun) ai_var_heap
					= init_variables binds (inc ai_next_var) (inc ai_next_var_of_fun) ai_var_heap
						
					= init_variables binds ai_next_var ai_next_var_of_fun ai_var_heap
			init_variables [] ai_next_var ai_next_var_of_fun ai_var_heap
				= (ai_next_var, ai_next_var_of_fun, ai_var_heap)
				
			acc_requirements_of_let_binds [ {lb_src, lb_dst} : binds ] ai_next_var common_defs ai
				| lb_dst.fv_count > 0
					# (bind_var, _, ai) = consumerRequirements lb_src common_defs ai
			  		  ai = aiUnifyClassifications ai_next_var bind_var ai
					= acc_requirements_of_let_binds binds (inc ai_next_var) common_defs ai
					= acc_requirements_of_let_binds binds ai_next_var common_defs ai
			acc_requirements_of_let_binds [] ai_next_var _ ai
				= ai
				
	consumerRequirements (Case case_expr) common_defs ai
		= consumerRequirements case_expr common_defs ai
	consumerRequirements (BasicExpr _) _ ai
		= (cPassive, False, ai)
	consumerRequirements (MatchExpr _ expr) common_defs ai
		= consumerRequirements expr common_defs ai
	consumerRequirements (Selection _ expr selectors) common_defs ai
		# (cc, _, ai) = consumerRequirements expr common_defs ai
		  ai = aiUnifyClassifications cActive cc ai
		  ai = requirementsOfSelectors selectors common_defs ai
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
		= aiUnifyClassifications cActive cc_var ai
	reqs_of_selector _ _ ai
		= ai
			
instance consumerRequirements App where
	consumerRequirements {app_symb={symb_kind = SK_Function {glob_module,glob_object}, symb_name}, app_args} common_defs=:(ConsumerAnalysisRO {main_dcl_module_n,stdStrictLists_module_n,imported_funs}) ai=:{ai_cons_class/*,ai_main_dcl_module_n*/}
		| glob_module == main_dcl_module_n//ai_main_dcl_module_n
			| glob_object < size ai_cons_class
				#! fun_class = ai_cons_class.[glob_object]
				= reqs_of_args fun_class.cc_args app_args cPassive common_defs ai
				= consumerRequirements app_args common_defs ai

		| glob_module==stdStrictLists_module_n && (not (isEmpty app_args)) && is_nil_cons_or_decons_of_UList_or_UTSList glob_object glob_module imported_funs
//			&& trace_tn ("consumerRequirements "+++symb_name.id_name+++" "+++toString imported_funs.[glob_module].[glob_object].ft_type.st_arity)
			# [app_arg:app_args]=app_args;
			# (cc, _, ai) = consumerRequirements app_arg common_defs ai
			# ai = aiUnifyClassifications cActive cc ai
			= consumerRequirements app_args common_defs ai

			= consumerRequirements app_args common_defs ai
	consumerRequirements {app_symb={symb_kind = SK_LocalMacroFunction glob_object, symb_name}, app_args} common_defs=:(ConsumerAnalysisRO {main_dcl_module_n}) ai=:{ai_cons_class/*,ai_main_dcl_module_n*/}
		| glob_object < size ai_cons_class
			#! fun_class = ai_cons_class.[glob_object]
			= reqs_of_args fun_class.cc_args app_args cPassive common_defs ai
			= consumerRequirements app_args common_defs ai
	consumerRequirements {app_args} common_defs ai
		=  not_an_unsafe_pattern (consumerRequirements app_args common_defs ai)

reqs_of_args :: [.Int] !.[Expression] Int ConsumerAnalysisRO !*AnalyseInfo -> *(!Int,!.Bool,!*AnalyseInfo)
reqs_of_args _ [] cumm_arg_class _ ai
	= (cumm_arg_class, False, ai)
reqs_of_args [] _ cumm_arg_class _ ai
	= (cumm_arg_class, False, ai)
reqs_of_args [form_cc : ccs] [arg : args] cumm_arg_class common_defs ai
	# (act_cc, _, ai) = consumerRequirements arg common_defs ai
	  ai = aiUnifyClassifications form_cc act_cc ai
	= reqs_of_args ccs args (combineClasses act_cc cumm_arg_class) common_defs ai

instance consumerRequirements Case where
	consumerRequirements kees=:{case_expr,case_guards,case_default,case_info_ptr} common_defs=:(ConsumerAnalysisRO {common_defs=common_defs_parameter}) ai
		# (cce, _, ai) = consumerRequirements case_expr common_defs ai
		  (ccgs, unsafe_bits, ai) = consumer_requirements_of_guards case_guards common_defs ai
		  has_default = case case_default of
		  		Yes _ -> True
		  		_ -> False
		  (ccd, default_is_unsafe, ai) = consumerRequirements case_default common_defs ai
		  (every_constructor_appears_in_safe_pattern, may_be_active) = inspect_patterns common_defs_parameter has_default case_guards unsafe_bits
		  safe = (has_default && not default_is_unsafe) || every_constructor_appears_in_safe_pattern
		  ai = aiUnifyClassifications (if may_be_active cActive cVarOfMultimatchCase) cce ai
		  ai = case case_expr of
				Var {var_info_ptr}
					| may_be_active
						-> { ai & ai_cases_of_vars_for_function=[kees:ai.ai_cases_of_vars_for_function] }
						-> ai
				_	-> ai
		# ai = case case_guards of
					OverloadedListPatterns (OverloadedList _ _ _ _) decons_expr=:(App {app_symb={symb_kind=SK_Function _},app_args=[app_arg]}) patterns
						// decons_expr will be optimized to a decons_u Selector in transform
						# (cc, _, ai) = consumerRequirements app_arg common_defs ai
						# ai = aiUnifyClassifications cActive cc ai
						-> ai
					OverloadedListPatterns _ decons_expr _
						# (_,_,ai) = consumerRequirements decons_expr common_defs ai
						-> ai
					_
						-> ai
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
			  all_sorted_constructors = if (is_sorted all_constructors) all_constructors (sortBy (<) all_constructors)
			= (appearance_loop all_sorted_constructors sorted_pattern_constructors, not (multimatch_loop has_default sorted_pattern_constructors))
		inspect_patterns common_defs has_default (BasicPatterns BT_Bool basic_patterns) unsafe_bits
			# bools_indices = [ if bool 1 0 \\ {bp_value=BVB bool}<-basic_patterns ]
			  sorted_pattern_constructors = sort bools_indices unsafe_bits
			= (appearance_loop [0,1] sorted_pattern_constructors,
				not (multimatch_loop has_default sorted_pattern_constructors))
//		inspect_patterns common_defs has_default (OverloadedListPatterns {glob_object, glob_module} algebraic_patterns) unsafe_bits
		inspect_patterns common_defs has_default (OverloadedListPatterns overloaded_list _ algebraic_patterns) unsafe_bits
			# type_def = case overloaded_list of
							UnboxedList {glob_object, glob_module} _ _ _
								-> common_defs.[glob_module].com_type_defs.[glob_object]
							UnboxedTailStrictList {glob_object, glob_module} _ _ _
								-> common_defs.[glob_module].com_type_defs.[glob_object]
							OverloadedList {glob_object, glob_module} _ _ _
								-> common_defs.[glob_module].com_type_defs.[glob_object]
			  defined_symbols = case type_def.td_rhs of
									AlgType defined_symbols		-> defined_symbols
									RecordType {rt_constructor}	-> [rt_constructor]
			  all_constructors = [ ds_index \\ {ds_index}<-defined_symbols ]
			  pattern_constructors = [ glob_object.ds_index \\ {ap_symbol={glob_object}}<-algebraic_patterns]	
			  sorted_pattern_constructors = sort pattern_constructors unsafe_bits
			  all_sorted_constructors = if (is_sorted all_constructors) all_constructors (sortBy (<) all_constructors)
			= (appearance_loop all_sorted_constructors sorted_pattern_constructors, not (multimatch_loop has_default sorted_pattern_constructors))
		inspect_patterns _ _ _ _
			= (False, False)

		is_sorted [x]
			= True
		is_sorted [h1:t=:[h2:_]]
			= h1 < h2 && is_sorted t

		sort constr_indices unsafe_bits
			= sortBy smaller (zip3 constr_indices [0..] unsafe_bits)
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

consumer_requirements_of_guards :: !CasePatterns ConsumerAnalysisRO !*AnalyseInfo -> (!Int,.[Bool],!*AnalyseInfo)
consumer_requirements_of_guards (AlgebraicPatterns type patterns) common_defs ai
	# pattern_exprs = [ ap_expr \\ {ap_expr}<-patterns]
	  pattern_vars = flatten [ ap_vars \\ {ap_vars}<-patterns]
	  (ai_next_var, ai_next_var_of_fun, ai_var_heap) = bindPatternVars pattern_vars ai.ai_next_var ai.ai_next_var_of_fun ai.ai_var_heap
	  ai = { ai & ai_var_heap=ai_var_heap, ai_next_var=ai_next_var, ai_next_var_of_fun = ai_next_var_of_fun }
	= independentConsumerRequirements pattern_exprs common_defs ai
consumer_requirements_of_guards (BasicPatterns type patterns) common_defs ai
	# pattern_exprs = [ bp_expr \\ {bp_expr}<-patterns]
	= independentConsumerRequirements pattern_exprs common_defs ai
consumer_requirements_of_guards (OverloadedListPatterns type _ patterns) common_defs ai
	# pattern_exprs = [ ap_expr \\ {ap_expr}<-patterns]
	  pattern_vars = flatten [ ap_vars \\ {ap_vars}<-patterns]
	  (ai_next_var, ai_next_var_of_fun, ai_var_heap) = bindPatternVars pattern_vars ai.ai_next_var ai.ai_next_var_of_fun ai.ai_var_heap
	  ai = { ai & ai_var_heap=ai_var_heap, ai_next_var=ai_next_var, ai_next_var_of_fun = ai_next_var_of_fun }
	= independentConsumerRequirements pattern_exprs common_defs ai

bindPatternVars :: !.[FreeVar] !Int !Int !*VarHeap -> (!Int,!Int,!*VarHeap)
bindPatternVars [fv=:{fv_info_ptr,fv_count} : vars] next_var next_var_of_fun var_heap
	| fv_count > 0
		= bindPatternVars vars (inc next_var) (inc next_var_of_fun) (writePtr fv_info_ptr (VI_AccVar next_var next_var_of_fun) var_heap)
		= bindPatternVars vars next_var next_var_of_fun (writePtr fv_info_ptr (VI_Count 0 False) var_heap)
bindPatternVars [] next_var next_var_of_fun var_heap
	= (next_var, next_var_of_fun, var_heap)

independentConsumerRequirements :: !.[Expression] ConsumerAnalysisRO !*AnalyseInfo -> (!Int,.[Bool],!*AnalyseInfo)
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

instance consumerRequirements DynamicExpr where
	consumerRequirements {dyn_expr} common_defs ai
		= consumerRequirements dyn_expr common_defs ai

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

//@ Analysis

// determine consumerRequirements for functions
analyseGroups	:: !{# CommonDefs} !{#{#FunType}} !IndexRange !Int !Int !*{! Group} !*{#FunDef} !*VarHeap !*ExpressionHeap 
				-> (!CleanupInfo, !*{! ConsClasses}, !*{! Group}, !*{#FunDef}, !*VarHeap, !*ExpressionHeap)
analyseGroups common_defs imported_funs {ir_from, ir_to} main_dcl_module_n stdStrictLists_module_n groups fun_defs var_heap expr_heap
	#! nr_of_funs = size fun_defs + ir_from - ir_to /* Sjaak */
	   nr_of_groups = size groups
	# consumerAnalysisRO=ConsumerAnalysisRO {common_defs=common_defs,imported_funs=imported_funs,main_dcl_module_n=main_dcl_module_n,stdStrictLists_module_n=stdStrictLists_module_n}
	= iFoldSt (analyse_group consumerAnalysisRO) 0 nr_of_groups
				([], createArray nr_of_funs { cc_size = 0, cc_args = [], cc_linear_bits = [], cc_producer=False}, groups, fun_defs, var_heap, expr_heap)
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
							ai_cases_of_vars_for_function = [] //,
//							ai_main_dcl_module_n=main_dcl_module_n
							} fun_defs
		  class_env = collect_classifications group_members ai.ai_cons_class ai.ai_class_subst
		  (cleanup_info, class_env, fun_defs, var_heap, expr_heap)
				 = foldSt set_case_expr_info (flatten ai_cases_of_vars_for_group) (cleanup_info,class_env, fun_defs, ai.ai_var_heap, expr_heap)
		= (cleanup_info, class_env, groups, fun_defs, var_heap, expr_heap)
	  where
		set_case_expr_info ({case_expr=case_expr=:(Var {var_info_ptr}), case_guards, case_info_ptr},fun_index) (cleanup_acc, class_env, fun_defs, var_heap, expr_heap)
			# (VI_AccVar _ arg_position, var_heap) = readPtr var_info_ptr var_heap
			  ({cc_size, cc_args, cc_linear_bits},class_env) = class_env![fun_index]
			  (aci_linearity_of_patterns, var_heap) = get_linearity_info cc_linear_bits case_guards var_heap
			| arg_position<cc_size && (arg_position>=cc_size || cc_args!!arg_position==cActive) && cc_linear_bits!!arg_position
				// mark non multimatch cases whose case_expr is an active linear function argument
				# aci = { aci_params = [], aci_opt_unfolder = No, aci_free_vars=No, aci_linearity_of_patterns = aci_linearity_of_patterns }
				= ([case_info_ptr:cleanup_acc], class_env, fun_defs, var_heap, 
					setExtendedExprInfo case_info_ptr (EEI_ActiveCase aci) expr_heap)
			= (cleanup_acc, class_env, fun_defs, var_heap, expr_heap)

		get_linearity_info cc_linear_bits (AlgebraicPatterns _ algebraic_patterns) var_heap
			= mapSt (get_linearity_info_of_pattern cc_linear_bits) algebraic_patterns var_heap
		get_linearity_info cc_linear_bits (OverloadedListPatterns _ _ algebraic_patterns) var_heap
			= mapSt (get_linearity_info_of_pattern cc_linear_bits) algebraic_patterns var_heap
		get_linearity_info cc_linear_bits _ var_heap
			= ([], var_heap)

		get_linearity_info_of_pattern cc_linear_bits {ap_vars} var_heap
			# (var_indices, var_heap) = mapSt get_var_index ap_vars var_heap
			= ([if (index==cNope) True (cc_linear_bits!!index) \\ index<-var_indices], var_heap)
		get_var_index {fv_info_ptr} var_heap
			# (vi, var_heap) = readPtr fv_info_ptr var_heap
			  index = case vi of
						VI_AccVar _ index	-> index
						VI_Count 0 False	-> cNope
			= (index, var_heap) 

	initial_cons_class [fun : funs] next_var_number nr_of_local_vars var_heap class_env fun_defs
		#  (fun_def, fun_defs) = fun_defs![fun]
		#  (TransformedBody {tb_args}) = fun_def.fun_body
		   (fresh_vars, next_var_number, var_heap) = fresh_variables tb_args 0 next_var_number var_heap
		= initial_cons_class funs next_var_number (length fun_def.fun_info.fi_local_vars + nr_of_local_vars) var_heap
			{ class_env & [fun] = { cc_size = 0, cc_args = fresh_vars, cc_linear_bits=[], cc_producer=False}} fun_defs
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
 		   (TransformedBody {tb_args, tb_rhs}) = fun_def.fun_body
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

/*
 *	TRANSFORM
 */

::	TransformInfo =
	{	ti_fun_defs				:: !.{# FunDef}
	,	ti_instances 			:: !.{! InstanceInfo }
	,	ti_cons_args 			:: !.{! ConsClasses}
	,	ti_new_functions 		:: ![FunctionInfoPtr]
	,	ti_fun_heap				:: !.FunctionHeap
	,	ti_var_heap				:: !.VarHeap
	,	ti_symbol_heap			:: !.ExpressionHeap
	,	ti_type_heaps			:: !.TypeHeaps
	,	ti_type_def_infos		:: !.TypeDefInfos
	,	ti_next_fun_nr			:: !Index
	,	ti_cleanup_info			:: !CleanupInfo
	,	ti_recursion_introduced	:: !Optional Index
//	,	ti_trace				:: !Bool // XXX just for tracing
	}

::	ReadOnlyTI = 
	{	ro_imported_funs	:: !{# {# FunType} }
	,	ro_common_defs		:: !{# CommonDefs }
// the following four are used when possibly generating functions for cases...
	,	ro_root_case_mode		:: !RootCaseMode
	,	ro_fun_root				:: !SymbIdent		// original function
	,	ro_fun_case				:: !SymbIdent		// original function or possibly generated case
	,	ro_fun_args				:: ![FreeVar]		// args of above

	,	ro_main_dcl_module_n 	:: !Int

	,	ro_transform_fusion		:: !Bool			// fusion switch

	,	ro_stdStrictLists_module_n :: !Int
	}

::	RootCaseMode = NotRootCase | RootCase | RootCaseOfZombie

neverMatchingCase = { case_expr = EE, case_guards = NoPattern, case_default = No, case_ident = No, case_info_ptr = nilPtr, 
// RWS ...
						case_explicit = False,
// ... RWS
						case_default_pos = NoPos }

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
			  ti_var_heap = foldSt (\(var_type, {lb_dst={fv_info_ptr}}) var_heap
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
				OverloadedListPatterns _ _ patterns
					# (EI_CaseType {ct_cons_types},ti_symbol_heap) = readExprInfo case_info_ptr ti.ti_symbol_heap
					  ti_var_heap = foldSt store_type_info_of_alg_pattern (zip2 ct_cons_types patterns) ti.ti_var_heap
					-> { ti & ti_symbol_heap = ti_symbol_heap, ti_var_heap = ti_var_heap }
				NoPattern
					-> ti
		store_type_info_of_alg_pattern (var_types,{ap_vars}) var_heap
			= foldSt (\(var_type, {fv_info_ptr}) var_heap
						->setExtendedVarInfo fv_info_ptr (EVI_VarType var_type) var_heap) (zip2 var_types ap_vars) var_heap
	transform (Selection opt_type expr selectors) ro ti
		# (expr, ti) = transform expr ro ti
		= transformSelection opt_type selectors expr ti
	transform (Update expr1 selectors expr2) ro ti
		# (expr1,ti) = transform expr1 ro ti
		# (selectors,ti) = transform_expressions_in_selectors selectors ti
			with
				transform_expressions_in_selectors [selection=:RecordSelection _ _ : selections] ti
					# (selections,ti) = transform_expressions_in_selectors selections ti
					= ([selection:selections],ti)
				transform_expressions_in_selectors [ArraySelection ds ep expr : selections] ti
					# (expr,ti) = transform expr ro ti
					# (selections,ti) = transform_expressions_in_selectors selections ti
					= ([ArraySelection ds ep expr:selections],ti)
				transform_expressions_in_selectors [DictionarySelection bv dictionary_selections ep expr : selections] ti
					# (expr,ti) = transform expr ro ti
					# (dictionary_selections,ti) = transform_expressions_in_selectors dictionary_selections ti
					# (selections,ti) = transform_expressions_in_selectors selections ti
					= ([DictionarySelection bv dictionary_selections ep expr:selections],ti)
				transform_expressions_in_selectors [] ti
					= ([],ti)
		# (expr2,ti) = transform expr2 ro ti
		= (Update expr1 selectors expr2,ti)
	transform (RecordUpdate cons_symbol expr exprs) ro ti
		# (expr,ti) = transform expr ro ti
		# (exprs,ti) = transform_fields exprs ro ti
		=(RecordUpdate cons_symbol expr exprs,ti)
	where	
		transform_fields [] ro ti
			= ([],ti)
		transform_fields [bind=:{bind_src} : fields] ro ti
			# (bind_src,ti) = transform bind_src ro ti
			# (fields,ti) = transform_fields fields ro ti
			= ([{bind & bind_src=bind_src} : fields],ti)
	transform (TupleSelect a1 arg_nr expr) ro ti
		# (expr,ti) = transform expr ro ti
		= (TupleSelect a1 arg_nr expr,ti)
	transform (MatchExpr a1 expr) ro ti
		# (expr,ti) = transform expr ro ti
		= (MatchExpr a1 expr,ti)
	transform (DynamicExpr dynamic_expr) ro ti
		# (dynamic_expr, ti) = transform dynamic_expr ro ti
		= (DynamicExpr dynamic_expr, ti)	
	transform expr ro ti
		= (expr, ti)

instance transform DynamicExpr where
	transform dyn=:{dyn_expr} ro ti
		# (dyn_expr, ti) = transform dyn_expr ro ti
		= ({dyn & dyn_expr = dyn_expr}, ti)

transformCase this_case=:{case_expr,case_guards,case_default,case_ident,case_info_ptr} ro ti
	| SwitchCaseFusion (not ro.ro_transform_fusion) True -!-> ("transformCase",Case this_case)
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

	transCase is_active opt_aci this_case=:{case_expr,case_guards,case_default,case_ident,case_info_ptr} ro ti
		| False -!-> ("transCase",Case this_case)
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
														# (ro_fun=:{symb_kind=SK_GeneratedFunction fun_info_ptr _}) = ro.ro_fun_case
														-> (inc ti_next_fun_nr,
														    { ro_fun & symb_kind=SK_GeneratedFunction fun_info_ptr ti_next_fun_nr })
													RootCase
														-> (ti_next_fun_nr, ro.ro_fun_root)
										  ti = { ti & ti_next_fun_nr = new_next_fun_nr, ti_recursion_introduced = Yes ti_next_fun_nr }
										  app_args1 = replace_arg [ fv_info_ptr \\ {fv_info_ptr}<-aci_params ] app_args variables
										  (app_args2, ti) = transform app_args1 { ro & ro_root_case_mode = NotRootCase } ti
										-> (App {app_symb=app_symb, app_args=app_args2, app_info_ptr=nilPtr}, ti)
							No	-> skip_over this_case ro ti
			BasicExpr basic_value
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
		equal (SK_LocalMacroFunction glob_index1) (SK_LocalMacroFunction glob_index2)
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
		getAlgebraicPatterns (OverloadedListPatterns _ _ algebraicPatterns)
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
		lift_patterns default_exists (OverloadedListPatterns type decons_expr case_guards) outer_case ro ti
			# guard_exprs	= [ ap_expr \\ {ap_expr} <- case_guards ]
			# (guard_exprs_with_case, ti) = lift_patterns_2 default_exists guard_exprs outer_case ro ti
			= (OverloadedListPatterns type decons_expr [ { case_guard & ap_expr=guard_expr } \\ case_guard<-case_guards & guard_expr<-guard_exprs_with_case], ti)
	
		lift_patterns_2 False [guard_expr] outer_case ro ti
			// if no default pattern exists, then the outer case expression does not have to be copied for the last pattern
			# (guard_expr, ti) = transformCase {outer_case & case_expr = guard_expr} ro ti
			= ([guard_expr], ti)
		lift_patterns_2 default_exists [guard_expr : guard_exprs] outer_case ro ti
			# us = { us_var_heap = ti.ti_var_heap, us_symbol_heap = ti.ti_symbol_heap, us_opt_type_heaps = No
					,us_cleanup_info=ti.ti_cleanup_info, us_local_macro_functions = No }
			  ui = {ui_handle_aci_free_vars = LeaveThem, ui_convert_module_n= -1,ui_conversion_table=No }
			  (outer_guards, us=:{us_cleanup_info})	= unfold outer_case.case_guards ui us
			  (expr_info, ti_symbol_heap)			= readPtr outer_case.case_info_ptr us.us_symbol_heap
			  (new_info_ptr, ti_symbol_heap)		= newPtr expr_info ti_symbol_heap
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
				  {cons_type} = ro.ro_common_defs.[glob_module].com_cons_defs.[ds_index]
				  unfoldables = [ ((not (arg_is_strict i cons_type.st_args_strictness)) && linear) || in_normal_form app_arg \\ linear <- linearity & app_arg <- app_args & i <- [0..]]
				  unfoldable_args = filterWith unfoldables zipped
				  not_unfoldable = map not unfoldables
				  non_unfoldable_args = filterWith not_unfoldable zipped
				  ti_var_heap = foldSt (\({fv_info_ptr}, arg) -> writeVarInfo fv_info_ptr (VI_Expression arg)) unfoldable_args ti.ti_var_heap
				  (new_expr, ti_symbol_heap) = possibly_add_let non_unfoldable_args ap_expr not_unfoldable glob_module ds_index ro ti.ti_symbol_heap
				  unfold_state = { us_var_heap = ti_var_heap, us_symbol_heap = ti_symbol_heap, us_opt_type_heaps = No,us_cleanup_info=ti.ti_cleanup_info,
				  				   us_local_macro_functions = No }
				  ui= {ui_handle_aci_free_vars = LeaveThem, ui_convert_module_n= -1,ui_conversion_table=No }
				  (unfolded_expr, unfold_state) = unfold new_expr ui unfold_state
				  (final_expr, ti) = transform unfolded_expr
				  						{ ro & ro_root_case_mode = NotRootCase }
				  						{ ti & ti_var_heap = unfold_state.us_var_heap, ti_symbol_heap = unfold_state.us_symbol_heap,ti_cleanup_info=unfold_state.us_cleanup_info }
				= (Yes final_expr, ti)
			= match_and_instantiate linearities cons_index app_args guards case_default ro ti
		  where
		  	in_normal_form (Var _)			= True
		  	in_normal_form (BasicExpr _)	= True
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
/* DvA... STRICT_LET
				= ( Let	{	let_strict_binds	= [ {lb_src=lb_src, lb_dst=lb_dst, lb_position = NoPos}
													\\ (lb_dst,lb_src)<-non_unfoldable_args
													& type <- let_type | type.at_annotation == AN_Strict
													]
						,	let_lazy_binds		= [ {lb_src=lb_src, lb_dst=lb_dst, lb_position = NoPos}
													\\ (lb_dst,lb_src)<-non_unfoldable_args
													& type <- let_type | type.at_annotation == AN_None
													]
...DvA */
				= ( Let	{	let_strict_binds	= []
						,	let_lazy_binds		= [ {lb_src=lb_src, lb_dst=lb_dst, lb_position = NoPos}
													\\ (lb_dst,lb_src)<-non_unfoldable_args]
						,	let_expr			= ap_expr
						,	let_info_ptr		= new_info_ptr
						,	let_expr_position	= NoPos
						}
				  , ti_symbol_heap
				  ) 

		match_and_instantiate [linearity:linearities] cons_index app_args [guard : guards] case_default ro ti
			= match_and_instantiate linearities cons_index app_args guards case_default ro ti
		match_and_instantiate _ cons_index app_args [] default_expr ro ti
			= transform default_expr { ro & ro_root_case_mode = NotRootCase } ti

possibly_generate_case_function :: !Case !ActiveCaseInfo !ReadOnlyTI !*TransformInfo -> *(!Expression, !*TransformInfo)
possibly_generate_case_function kees=:{case_info_ptr} aci=:{aci_free_vars} ro ti=:{ti_recursion_introduced=old_ti_recursion_introduced}
	| False -!-> ("possibly_generate_case_function",ro.ro_fun_root.symb_name.id_name,ro.ro_fun_case.symb_name.id_name,ro.ro_root_case_mode)
		= undef
	// determine free variables
	# (free_vars, ti)
		 = case aci_free_vars of
			Yes free_vars
				-> (free_vars, ti)
			No	# fvi	= { fvi_var_heap = ti.ti_var_heap, fvi_expr_heap = ti.ti_symbol_heap, fvi_variables = [],
						  fvi_expr_ptrs = ti.ti_cleanup_info }
				  {fvi_var_heap, fvi_expr_heap, fvi_variables, fvi_expr_ptrs}
				  		= freeVariables (Case kees) fvi
				  ti	= { ti & ti_var_heap = fvi_var_heap, ti_symbol_heap = fvi_expr_heap, ti_cleanup_info = fvi_expr_ptrs }
				-> (fvi_variables, ti)
	// search function definition and consumer arguments
	  (outer_fun_def, outer_cons_args, ti_cons_args, ti_fun_defs, ti_fun_heap)
	  		= get_fun_def_and_cons_args ro.ro_fun_root.symb_kind ti.ti_cons_args ti.ti_fun_defs ti.ti_fun_heap
	  outer_arguments
	  		= case outer_fun_def.fun_body of
							TransformedBody {tb_args} 	-> tb_args
							Expanding args				-> args
	  outer_info_ptrs
	  		= [ fv_info_ptr \\ {fv_info_ptr}<-outer_arguments]
	  free_var_info_ptrs
	  		= [ var_info_ptr \\ {var_info_ptr}<-free_vars ]
	  used_mask
	  		= [isMember fv_info_ptr free_var_info_ptrs \\ {fv_info_ptr}<-outer_arguments]
	  arguments_from_outer_fun
	  		= [ outer_argument \\ outer_argument<-outer_arguments & used<-used_mask | used ]
	  lifted_arguments
	  		= [ { fv_def_level = undeff, fv_name = var_name, fv_info_ptr = var_info_ptr, fv_count = undeff}
							\\ {var_name, var_info_ptr} <- free_vars | not (isMember var_info_ptr outer_info_ptrs)]
	  all_args
	  		= lifted_arguments++arguments_from_outer_fun
	  (fun_info_ptr, ti_fun_heap)
	  		= newPtr FI_Empty ti_fun_heap
	  fun_ident
	  		= { id_name = ro.ro_fun_root.symb_name.id_name+++"_case", id_info = nilPtr }
	  fun_symb
	  		= { symb_name = fun_ident, symb_kind=SK_GeneratedFunction fun_info_ptr undeff }
	  new_ro
	  		= { ro & ro_root_case_mode = RootCaseOfZombie , ro_fun_case = fun_symb, ro_fun_args = all_args }
	  ti
	  		= { ti & ti_cons_args = ti_cons_args, ti_fun_defs = ti_fun_defs, ti_fun_heap = ti_fun_heap, ti_recursion_introduced = No }
	  (new_expr, ti)
	  		= transformCase kees new_ro ti
	  (ti_recursion_introduced, ti)
	  		= ti!ti_recursion_introduced
	  ti	= { ti & ti_recursion_introduced = old_ti_recursion_introduced }
	= case ti_recursion_introduced of
		Yes fun_index
			-> generate_case_function fun_index case_info_ptr new_expr outer_fun_def outer_cons_args used_mask new_ro ti
		No	-> (new_expr, ti)

generate_case_function :: !Int !ExprInfoPtr !Expression FunDef .ConsClasses [.Bool] !.ReadOnlyTI !*TransformInfo -> (!Expression,!*TransformInfo)
generate_case_function fun_index case_info_ptr new_expr outer_fun_def outer_cons_args used_mask
					{ro_fun_case=ro_fun=:{symb_kind=SK_GeneratedFunction fun_info_ptr _}, ro_fun_args} ti
	| False -!-> ("generate_case_function",ro_fun.symb_name)		= undef
	# fun_arity								= length ro_fun_args
	  (Yes {st_vars,st_args,st_attr_vars})	= outer_fun_def.fun_type
	  types_from_outer_fun					= [ st_arg \\ st_arg <- st_args & used <- used_mask | used ]
	  nr_of_lifted_vars						= fun_arity-(length types_from_outer_fun)
	  (lifted_types, ti_var_heap)			= mapSt get_type_of_local_var (take nr_of_lifted_vars ro_fun_args) ti.ti_var_heap
	  (EI_CaseType {ct_result_type}, ti_symbol_heap) = readExprInfo case_info_ptr ti.ti_symbol_heap
	  (form_vars, ti_var_heap)				= mapSt bind_to_fresh_expr_var ro_fun_args ti_var_heap

	  arg_types								= lifted_types++types_from_outer_fun

	# {ti_type_heaps}						= ti
	  {th_vars}								= ti_type_heaps
	  (type_variables, th_vars)				= getTypeVars [ct_result_type:arg_types] th_vars
	  (fresh_type_vars, th_vars)			= mapSt bind_to_fresh_type_variable type_variables th_vars
	  ti_type_heaps							= { ti_type_heaps & th_vars = th_vars }

	  (_, fresh_arg_types, ti_type_heaps)	= substitute arg_types ti_type_heaps
	  (_, fresh_result_type, ti_type_heaps)	= substitute ct_result_type ti_type_heaps

	  // unfold...
	  us =		{ us_var_heap				= ti_var_heap
	  			, us_symbol_heap			= ti_symbol_heap
	  			, us_opt_type_heaps			= Yes ti_type_heaps
	  			, us_cleanup_info			= ti.ti_cleanup_info
	  			, us_local_macro_functions	= No 
	  			}
	  ui =
	  			{ ui_handle_aci_free_vars	= SubstituteThem
	  			, ui_convert_module_n		= -1
	  			, ui_conversion_table		= No 
	  			}
	  (copied_expr, us)
			= unfold new_expr ui us
	  {us_var_heap=ti_var_heap, us_symbol_heap=ti_symbol_heap, us_cleanup_info=ti_cleanup_info, us_opt_type_heaps = Yes ti_type_heaps}
	  		= us
	  // generated function...
	  fun_type =
	  			{ st_vars					= fresh_type_vars
	  			, st_args					= fresh_arg_types
	  			, st_arity					= fun_arity
	  			, st_args_strictness		= NotStrict
	  			, st_result					= fresh_result_type
	  			, st_context				= []
	  			, st_attr_vars				= []
	  			, st_attr_env				= []
	  			}
	  fun_def =	{ fun_symb					= ro_fun.symb_name
				, fun_arity					= fun_arity
				, fun_priority				= NoPrio
				, fun_body					= TransformedBody { tb_args = form_vars, tb_rhs = copied_expr}
				, fun_type					= Yes fun_type
				, fun_pos					= NoPos
				, fun_kind					= FK_Function cNameNotLocationDependent
				, fun_lifted				= undeff
				, fun_info = 	{	fi_calls		= []
								,	fi_group_index	= outer_fun_def.fun_info.fi_group_index
								,	fi_def_level	= NotALevel
								,	fi_free_vars	= []
								,	fi_local_vars	= []
								,	fi_dynamics		= []
// Sjaak: 							,	fi_is_macro_fun = outer_fun_def.fun_info.fi_is_macro_fun
								,	fi_properties	= outer_fun_def.fun_info.fi_properties
								}	
				}
	# cc_args_from_outer_fun		= [ cons_arg \\ cons_arg <- outer_cons_args.cc_args & used <- used_mask | used ]
	  cc_linear_bits_from_outer_fun	= [ cons_arg \\ cons_arg <- outer_cons_args.cc_linear_bits & used <- used_mask | used ]
	  new_cons_args =
	  			{ cc_size			= fun_arity
	  			, cc_args			= repeatn nr_of_lifted_vars cPassive ++ cc_args_from_outer_fun
	  			, cc_linear_bits	= repeatn nr_of_lifted_vars    False ++ cc_linear_bits_from_outer_fun
	  			, cc_producer		= False
	  			}
	  gf =
	  			{ gf_fun_def		= fun_def
	  			, gf_instance_info	= II_Empty
	  			, gf_cons_args		= new_cons_args
	  			, gf_fun_index		= fun_index
	  			}
	  ti_fun_heap = writePtr fun_info_ptr (FI_Function gf) ti.ti_fun_heap
	  ti =
	  			{ ti 
	  			& ti_new_functions	= [fun_info_ptr:ti.ti_new_functions]
	  			, ti_var_heap		= ti_var_heap
	  			, ti_fun_heap		= ti_fun_heap
	  			, ti_symbol_heap	= ti_symbol_heap
	  			, ti_type_heaps		= ti_type_heaps
	  			, ti_cleanup_info	= ti_cleanup_info 
	  			}
	  app_symb = { ro_fun & symb_kind = SK_GeneratedFunction fun_info_ptr fun_index}
	  app_args = map free_var_to_bound_var ro_fun_args
	= ( App {app_symb = app_symb, app_args = app_args, app_info_ptr = nilPtr}, ti)
where
	get_type_of_local_var {fv_info_ptr} var_heap
		# (EVI_VarType a_type, var_heap)	= readExtendedVarInfo fv_info_ptr var_heap
		= (a_type, var_heap)
	free_var_to_bound_var {fv_name, fv_info_ptr}
		= Var { var_name = fv_name, var_info_ptr = fv_info_ptr, var_expr_ptr = nilPtr}

removeNeverMatchingSubcases :: Expression -> Expression
removeNeverMatchingSubcases keesExpr=:(Case kees)
	// remove those case guards whose right hand side is a never matching case
	| is_never_matching_case keesExpr
		= keesExpr
	# {case_guards, case_default} = kees
	  filtered_default = get_filtered_default case_default
	= case case_guards of
		AlgebraicPatterns i alg_patterns
			| not (any (is_never_matching_case o get_alg_rhs) alg_patterns) && not (is_never_matching_default case_default)
				-> keesExpr // frequent case: all subexpressions can't fail
			# filtered_case_guards = filter (not o is_never_matching_case o get_alg_rhs) alg_patterns
			| has_become_never_matching filtered_default filtered_case_guards
				-> Case neverMatchingCase
			| is_default_only filtered_default filtered_case_guards
				-> fromYes case_default
			-> Case {kees & case_guards = AlgebraicPatterns i filtered_case_guards, case_default = filtered_default }
		BasicPatterns bt basic_patterns
			| not (any (is_never_matching_case o get_basic_rhs) basic_patterns) && not (is_never_matching_default case_default)
				-> keesExpr // frequent case: all subexpressions can't fail
			# filtered_case_guards = filter (not o is_never_matching_case o get_basic_rhs) basic_patterns
			| has_become_never_matching filtered_default filtered_case_guards
				-> Case neverMatchingCase
			| is_default_only filtered_default filtered_case_guards
				-> fromYes case_default
			-> Case {kees & case_guards = BasicPatterns bt filtered_case_guards, case_default = filtered_default }
		OverloadedListPatterns i decons_expr alg_patterns
			| not (any (is_never_matching_case o get_alg_rhs) alg_patterns) && not (is_never_matching_default case_default)
				-> keesExpr // frequent case: all subexpressions can't fail
			# filtered_case_guards = filter (not o is_never_matching_case o get_alg_rhs) alg_patterns
			| has_become_never_matching filtered_default filtered_case_guards
				-> Case neverMatchingCase
			| is_default_only filtered_default filtered_case_guards
				-> fromYes case_default
			-> Case {kees & case_guards = OverloadedListPatterns i decons_expr filtered_case_guards, case_default = filtered_default }
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
	is_never_matching_default No
		= False
	is_never_matching_default (Yes expr)
		= is_never_matching_case expr
removeNeverMatchingSubcases expr
	= expr

	
instance transform LetBind
where
	transform bind=:{lb_src} ro ti
		# (lb_src, ti) = transform lb_src ro ti
		= ({ bind & lb_src = lb_src }, ti)

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
	transform (OverloadedListPatterns type=:(OverloadedList _ _ _ _) decons_expr patterns) ro ti
		# (patterns, ti) = transform patterns ro ti
		# (decons_expr, ti) = transform decons_expr ro ti
		= (OverloadedListPatterns type decons_expr patterns, ti)
	transform (OverloadedListPatterns type decons_expr patterns) ro ti
		# (patterns, ti) = transform patterns ro ti
		# (decons_expr, ti) = transform decons_expr ro ti
		= (OverloadedListPatterns type decons_expr patterns, ti)

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

//@ tryToFindInstance: 

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
		compare_constructor_arguments (PR_Function _ _ index1) (PR_Function _ _ index2)
			= index1 =< index2
		compare_constructor_arguments (PR_GeneratedFunction _ _ index1) (PR_GeneratedFunction _ _ index2)
			= index1 =< index2
		compare_constructor_arguments 	(PR_Class app1 lifted_vars_with_types1 t1) 
										(PR_Class app2 lifted_vars_with_types2 t2) 
//			= app1.app_args =< app2.app_args
			# cmp = smallerOrEqual t1 t2
			| cmp<>Equal
				= cmp
			= compare_types lifted_vars_with_types1 lifted_vars_with_types2
		compare_constructor_arguments (PR_Curried symb_ident1 _) (PR_Curried symb_ident2 _)
			= symb_ident1 =< symb_ident2
		compare_constructor_arguments PR_Empty PR_Empty
			= Equal
		compare_constructor_arguments (PR_Constructor symb_ident1 _ _) (PR_Constructor symb_ident2 _ _)
			= symb_ident1 =< symb_ident2
			
		compare_types [(_, type1):types1] [(_, type2):types2]
			# cmp = smallerOrEqual type1 type2
			| cmp<>Equal
				= cmp
			= compare_types types1 types2
		compare_types [] [] = Equal
		compare_types [] _ = Smaller
		compare_types _ [] = Greater
		
/*
 *	UNIQUENESS STUFF...
 */

create_fresh_type_vars :: !Int !*TypeVarHeap -> (!{!TypeVar}, !*TypeVarHeap)
create_fresh_type_vars nr_of_all_type_vars th_vars
	# fresh_array = createArray  nr_of_all_type_vars {tv_name = {id_name="",id_info=nilPtr}, tv_info_ptr=nilPtr}
	= iFoldSt allocate_fresh_type_var 0 nr_of_all_type_vars (fresh_array,th_vars)
where
	allocate_fresh_type_var i (array, th_vars)
		# (new_tv_info_ptr, th_vars) = newPtr TVI_Empty th_vars
		  tv = { tv_name = { id_name = "a"+++toString i, id_info = nilPtr }, tv_info_ptr=new_tv_info_ptr }
		= ({array & [i] = tv}, th_vars)

create_fresh_attr_vars :: !{!CoercionTree} !Int !*AttrVarHeap -> (!{!TypeAttribute}, !.AttrVarHeap)
create_fresh_attr_vars demanded nr_of_attr_vars th_attrs
	# fresh_array = createArray nr_of_attr_vars TA_None
	= iFoldSt (allocate_fresh_attr_var demanded) 0 nr_of_attr_vars (fresh_array, th_attrs)
where
	allocate_fresh_attr_var demanded i (attr_var_array, th_attrs)
		= case demanded.[i] of
			CT_Unique
				-> ({ attr_var_array & [i] = TA_Unique}, th_attrs)
			CT_NonUnique
				-> ({ attr_var_array & [i] = TA_Multi}, th_attrs)
			_
				# (new_info_ptr, th_attrs) = newPtr AVI_Empty th_attrs
				-> ({ attr_var_array & [i] = TA_Var { av_name = NewAttrVarId i, av_info_ptr = new_info_ptr }}, th_attrs)

coercionsToAttrEnv :: !{!TypeAttribute} !Coercions -> [AttrInequality]
coercionsToAttrEnv attr_vars {coer_demanded, coer_offered}
	= flatten [ [ {ai_offered = toAttrVar attr_vars.[offered],
					ai_demanded = toAttrVar attr_vars.[demanded] }
				\\ offered <- fst (flattenCoercionTree offered_tree) ]
			  \\ offered_tree<-:coer_offered & demanded<-[0..] ]
  where
	toAttrVar (TA_Var av) = av

substitute_attr_inequality {ai_offered, ai_demanded} th_attrs
	#! ac_offered = pointer_to_int ai_offered th_attrs
	   ac_demanded = pointer_to_int ai_demanded th_attrs
	= ({ ac_offered = ac_offered, ac_demanded = ac_demanded }, th_attrs)
  where
	pointer_to_int {av_info_ptr} th_attrs
		# (AVI_Attr (TA_TempVar i)) = sreadPtr av_info_ptr th_attrs
		= i

new_inequality {ac_offered, ac_demanded} coercions
	= newInequality ac_offered ac_demanded coercions

:: UniquenessRequirement =
	{	ur_offered		:: !AType
	,	ur_demanded		:: !AType
	,	ur_attr_ineqs	:: ![AttrCoercion]
	}

readableCoercions {coer_demanded}
	= [ (i, readable coer_demanded.[i]) \\ i<-[0..size coer_demanded - 1] ]
  where
	readable CT_Unique
	 	= [TA_Unique]
	readable CT_NonUnique
	 	= [TA_Multi]
	readable ct
		# (vars, _) = flattenCoercionTree ct
		= map TA_TempVar vars

:: ATypesWithStrictness = {ats_types::![AType],ats_strictness::!StrictnessList};

compute_args_strictness new_arg_types_array = compute_args_strictness 0 0 NotStrict 0 new_arg_types_array
  	where
  		compute_args_strictness strictness_index strictness strictness_list array_index new_arg_types_array
  			| array_index==size new_arg_types_array
  				| strictness==0
  					= strictness_list
  					= append_strictness strictness strictness_list
  				# {ats_types,ats_strictness} = new_arg_types_array.[array_index]
  				# (strictness_index,strictness) = add_strictness_for_arguments ats_types 0 strictness_index strictness strictness_list
  					with
  						add_strictness_for_arguments [] ats_strictness_index strictness_index strictness strictness_list
  							= (strictness_index,strictness)
  						add_strictness_for_arguments [_:ats_types] ats_strictness_index strictness_index strictness strictness_list
  							| arg_is_strict ats_strictness_index ats_strictness
  								# (strictness_index,strictness,strictness_list) = add_next_strict strictness_index strictness strictness_list
  								= add_strictness_for_arguments ats_types (ats_strictness_index+1) strictness_index strictness strictness_list
  								# (strictness_index,strictness,strictness_list) = add_next_not_strict strictness_index strictness strictness_list
  								= add_strictness_for_arguments ats_types (ats_strictness_index+1) strictness_index strictness strictness_list
  				= compute_args_strictness strictness_index strictness strictness_list (array_index+1) new_arg_types_array
	
/*
 * GENERATE FUSED FUNCTION
 */

generateFunction :: !FunDef !ConsClasses !{! Producer} !FunctionInfoPtr !ReadOnlyTI !*TransformInfo -> (!Index, !Int, !*TransformInfo)
generateFunction fd=:{fun_body = TransformedBody {tb_args,tb_rhs},fun_info = {fi_group_index}} 
				 {cc_args,cc_linear_bits} prods fun_def_ptr ro
				 ti=:{ti_var_heap,ti_next_fun_nr,ti_new_functions,ti_fun_heap,ti_symbol_heap,ti_fun_defs,
				 		ti_type_heaps,ti_cons_args,ti_cleanup_info, ti_type_def_infos}
/*
	| False-!->("generating new function",fd.fun_symb.id_name,"->",ti_next_fun_nr)		= undef
	| False-!->("with type",fd.fun_type)												= undef
	| False-!->("producers:",II_Node prods nilPtr II_Empty II_Empty,("cc_args",cc_args,("cc_linear_bits",cc_linear_bits)))		= undef
//	| False-!->("body:",tb_args, tb_rhs)												= undef
*/
	#!(fi_group_index, ti_cons_args, ti_fun_defs, ti_fun_heap)
			= max_group_index 0 prods ro.ro_main_dcl_module_n fi_group_index ti_fun_defs ti_fun_heap ti_cons_args
	# opt_consumer_symbol_type 
			= fd.fun_type

	  (function_producer_types, ti_fun_defs, ti_fun_heap)
	  		= iFoldSt (accum_function_producer_type prods ro) 0 (size prods) 
	  				([], ti_fun_defs, ti_fun_heap)
	  (fresh_function_producer_types, ti_type_heaps)
	  		= mapSt copy_opt_symbol_type function_producer_types
	  				ti_type_heaps
	  ([opt_sound_consumer_symbol_type:opt_sound_function_producer_types], (ti_type_heaps, ti_type_def_infos))
	  		= mapSt (add_propagation_attributes ro.ro_common_defs) [opt_consumer_symbol_type: fresh_function_producer_types]
	  				(ti_type_heaps, ti_type_def_infos)

	  (Yes sound_consumer_symbol_type)
	  		= opt_sound_consumer_symbol_type

	  sound_function_producer_types
	  		= [x \\ Yes x <- opt_sound_function_producer_types]

	  ({st_attr_vars,st_args,st_args_strictness,st_result,st_attr_env})
	  		= sound_consumer_symbol_type

	  (class_types, ti_fun_defs, ti_fun_heap)
	  		= iFoldSt (accum_class_type prods ro) 0 (size prods) 
	  				([], ti_fun_defs, ti_fun_heap)
	  (type_vars_in_class_types, th_vars)
	  		= mapSt getTypeVars class_types ti_type_heaps.th_vars

	  all_involved_types
	  		= class_types ++ (flatten (map (\{st_args, st_result}-> [st_result:st_args]) 
					  					[sound_consumer_symbol_type:sound_function_producer_types]))
	  (propagating_cons_vars, th_vars)
	  		= collectPropagatingConsVars all_involved_types th_vars
	  all_type_vars
	  		=   flatten [st_vars \\ {st_vars} <- [sound_consumer_symbol_type:sound_function_producer_types]]
	  		  ++flatten type_vars_in_class_types
	| False -!-> ("all_type_vars",all_type_vars)	= undef
	# (nr_of_all_type_vars, th_vars)
	  		=  foldSt bind_to_temp_type_var all_type_vars (0, th_vars)
	  subst
	  		= createArray nr_of_all_type_vars TE
	  (next_attr_nr, th_attrs)
	  		= foldSt bind_to_temp_attr_var st_attr_vars (FirstAttrVar, ti_type_heaps.th_attrs)
	  ti_type_heaps
	  		= { ti_type_heaps & th_attrs = th_attrs, th_vars = th_vars }
	| False-!->("before substitute", st_args, "->", st_result)		= undef
	# (_, (st_args,st_result), ti_type_heaps)
	  		= substitute (st_args,st_result) ti_type_heaps
	| False-!->("after substitute", st_args, "->", st_result)		= undef
// determine args...
	# das =
			{ das_vars						= []
//			, das_arg_types					= { [el] \\ el <- st_args }
			, das_arg_types					= st_args_array st_args st_args_strictness
			, das_next_attr_nr				= next_attr_nr
			, das_new_linear_bits			= []
			, das_new_cons_args				= []
			, das_uniqueness_requirements	= []
			, das_subst						= subst
			, das_let_bindings				= ([],[],[],[])
			, das_type_heaps				= ti_type_heaps
			, das_symbol_heap				= ti_symbol_heap
			, das_fun_defs					= ti_fun_defs
			, das_fun_heap					= ti_fun_heap
			, das_var_heap					= ti_var_heap
			, das_cons_args					= ti_cons_args
			}
	# das		= determine_args cc_linear_bits cc_args 0 prods opt_sound_function_producer_types tb_args ro das
	  
	  new_fun_args				= das.das_vars
	  new_arg_types_array		= das.das_arg_types
	  next_attr_nr				= das.das_next_attr_nr
	  new_linear_bits			= das.das_new_linear_bits
	  new_cons_args				= das.das_new_cons_args
	  uniqueness_requirements	= das.das_uniqueness_requirements
	  subst						= das.das_subst
	  let_bindings				= das.das_let_bindings
	  ti_type_heaps				= das.das_type_heaps
	  ti_symbol_heap			= das.das_symbol_heap
	  ti_fun_defs				= das.das_fun_defs
	  ti_fun_heap				= das.das_fun_heap
	  ti_var_heap				= das.das_var_heap
	  ti_cons_args				= das.das_cons_args
	  
	  new_arg_types = flatten [ ats_types \\ {ats_types}<-:new_arg_types_array ]
	  
	  new_args_strictness = compute_args_strictness new_arg_types_array
	  	  	  
	  cons_vars
	  		= createArray (inc (BITINDEX nr_of_all_type_vars)) 0
	  (cons_vars, th_vars)
			= foldSt set_cons_var_bit propagating_cons_vars (cons_vars, ti_type_heaps.th_vars)
//	| False--->("subst before", [el\\el<-:subst], "cons_vars", [el\\el<-:cons_vars])		= undef
	# ti_type_heaps
			= { ti_type_heaps & th_vars = th_vars }

	# (subst, next_attr_nr, ti_type_heaps, ti_type_def_infos)
	  		= liftSubstitution subst ro.ro_common_defs cons_vars next_attr_nr ti_type_heaps ti_type_def_infos
//	| False--->("subst after lifting", [el\\el<-:subst])		= undef

	# (consumer_attr_inequalities, th_attrs)
			= mapSt substitute_attr_inequality st_attr_env ti_type_heaps.th_attrs
	  ti_type_heaps
	  		= { ti_type_heaps & th_attrs = th_attrs }
	  
	  coercions
	  		= { coer_offered	= {{ CT_Empty \\ i <- [0 .. next_attr_nr - 1] } & [AttrMulti] = CT_NonUnique }
	  		  , coer_demanded	= {{ CT_Empty \\ i <- [0 .. next_attr_nr - 1] } & [AttrUni] = CT_Unique } 
	  		  }
	  coercions 
	  		= foldSt new_inequality consumer_attr_inequalities coercions
	  coercions 
	  		= foldSt (\{ur_attr_ineqs} coercions -> foldSt new_inequality ur_attr_ineqs coercions)
		  			uniqueness_requirements coercions
	  (subst, coercions, ti_type_def_infos, ti_type_heaps)
	  		= foldSt (coerce_types ro.ro_common_defs cons_vars) uniqueness_requirements
	  				(subst, coercions, ti_type_def_infos, ti_type_heaps)
	# ([st_result:new_arg_types], (coercions, subst, ti_type_heaps, ti_type_def_infos))
	  		= mapSt (expand_type ro.ro_common_defs cons_vars) [st_result:new_arg_types]
	  				(coercions, subst, ti_type_heaps, ti_type_def_infos)
	| False-!->("unified type", new_arg_types, "->", st_result)		= undef
	| False-!->("coercions", readableCoercions coercions)			= undef

	# (fresh_type_vars_array,ti_type_heaps)
	  		= accTypeVarHeap (create_fresh_type_vars nr_of_all_type_vars) ti_type_heaps
	  (attr_partition, demanded) 
	  		= partitionateAttributes coercions.coer_offered coercions.coer_demanded
	  		// to eliminate circles in the attribute inequalities graph that was built during "det ermine_arg s"
	  (fresh_attr_vars, ti_type_heaps)
	  		= accAttrVarHeap (create_fresh_attr_vars demanded (size demanded)) ti_type_heaps
	  		// the attribute variables stored in the "demanded" graph are represented as integers: 
	  		// prepare to replace them by pointers
	  ((fresh_arg_types, fresh_result_type), used_attr_vars) 
	  		= replaceIntegers (new_arg_types, st_result) (fresh_type_vars_array, fresh_attr_vars, attr_partition)
	  				 (createArray (size demanded) False)
			// replace the integer-attribute-variables with pointer-attribute-variables or TA_Unique or TA_Multi
	  final_coercions 
	  		= removeUnusedAttrVars demanded [i \\ i<-[0..(size used_attr_vars)-1] | not used_attr_vars.[i]]
			// the attribute inequalities graph may have contained unused attribute variables.

 	  (all_attr_vars2, ti_type_heaps)
 	  		= accAttrVarHeap (getAttrVars (fresh_arg_types, fresh_result_type)) ti_type_heaps
	  all_attr_vars
	  		= [ attr_var \\ TA_Var attr_var
	  							<- [fresh_attr_vars.[i] \\ i<-[0..(size used_attr_vars)-1] | used_attr_vars.[i]]]
 	# (all_fresh_type_vars, ti_type_heaps)
 	  		= accTypeVarHeap (getTypeVars (fresh_arg_types, fresh_result_type)) ti_type_heaps
	  fun_arity
	  		= length new_fun_args
	  new_fun_type
	  		= Yes
	  			{ st_vars		= all_fresh_type_vars
	  			, st_args		= fresh_arg_types
	  			, st_args_strictness=new_args_strictness
	  			, st_arity		= fun_arity
	  			, st_result		= fresh_result_type
	  			, st_context	= []
	  			, st_attr_vars	= all_attr_vars
	  			, st_attr_env	= coercionsToAttrEnv fresh_attr_vars final_coercions 
	  			}
/* DvA... STRICT_LET
	  // DvA: moet hier rekening houden met strictness dwz alleen safe args expanderen en rest in stricte let genereren...
	  (tb_rhs,ti_symbol_heap,strict_free_vars) = case let_bindings of
	  			([],[],_,_)
	  				-> (tb_rhs,ti_symbol_heap,[])
	  			(s,l,st,lt)
					# let_type = st++lt
					# (new_info_ptr, ti_symbol_heap) = newPtr (EI_LetType let_type) ti_symbol_heap
	  				# new_expr = Let
	  						{ let_strict_binds	= s
	  						, let_lazy_binds	= l
	  						, let_expr			= tb_rhs
	  						, let_info_ptr		= new_info_ptr
	  						, let_expr_position	= NoPos
	  						}
	  				# strict_free_vars = [lb_dst \\ {lb_dst} <- s]
	  				-> (new_expr,ti_symbol_heap,strict_free_vars)
...DvA */
	  new_fd_expanding 
	  		= { fd & fun_body = Expanding new_fun_args, fun_arity = fun_arity,fun_type=new_fun_type, 
	  					fun_info.fi_group_index = fi_group_index
/* DvA... STRICT_LET
					,fun_info.fi_free_vars = strict_free_vars++fd.fun_info.fi_free_vars
...DvA */
	  					}
	  new_fd_cons_args
	  		= {cc_args = new_cons_args, cc_size = length new_cons_args, cc_linear_bits=new_linear_bits, cc_producer = False}
	  new_gen_fd
	  		= { gf_fun_def = new_fd_expanding,	gf_instance_info = II_Empty, gf_fun_index = ti_next_fun_nr,
				 gf_cons_args = new_fd_cons_args }
	  ti_fun_heap
	  		= ti_fun_heap <:= (fun_def_ptr, FI_Function new_gen_fd)
	  (subst, _)
	  		= iFoldSt (replace_integers_in_substitution (fresh_type_vars_array, fresh_attr_vars, attr_partition))
	  				0 nr_of_all_type_vars (subst, createArray (size demanded) False)
	  		// replace the integer-attribute-variables with pointer-attribute-variables or TA_Unique or TA_Multi in subst
	  (_, th_vars)
	  		= foldSt (\{tv_info_ptr} (i, th_vars) 
	  					-> case subst.[i] of
	  						TE
	  							-> (i+1, writePtr tv_info_ptr (TVI_Type (TV fresh_type_vars_array.[i])) th_vars)
	  						_
	  							-> (i+1, writePtr tv_info_ptr (TVI_Type subst.[i]) th_vars))
	  				all_type_vars (0, ti_type_heaps.th_vars)
	  us 	
	  		= { us_var_heap = ti_var_heap, us_symbol_heap = ti_symbol_heap,
	  			us_opt_type_heaps = Yes { ti_type_heaps & th_vars = th_vars },
				 us_cleanup_info=ti_cleanup_info,us_local_macro_functions=No }
 	  ui	
 	  		= {ui_handle_aci_free_vars = RemoveThem, ui_convert_module_n= -1,ui_conversion_table=No }
	  (tb_rhs, {us_var_heap,us_symbol_heap,us_opt_type_heaps=Yes ti_type_heaps, us_cleanup_info})
	  		= unfold tb_rhs ui us
//	| False -!-> ("unfolded:", tb_rhs) = undef
	# ro_fun= { symb_name = fd.fun_symb, symb_kind = SK_GeneratedFunction fun_def_ptr ti_next_fun_nr }
	# ro 	=	{ ro &	ro_root_case_mode = case tb_rhs of 
	  						Case _
	  							-> RootCase
	  						_	-> NotRootCase,
						ro_fun_root = ro_fun,
						ro_fun_case = ro_fun,
						ro_fun_args = new_fun_args
				}
	| False -!-> ("transforming new function:",tb_rhs)		= undef
	# ti
			= { ti & ti_var_heap = us_var_heap, ti_fun_heap = ti_fun_heap, ti_symbol_heap = us_symbol_heap,
	  			ti_next_fun_nr = inc ti_next_fun_nr, ti_type_def_infos = ti_type_def_infos,
	  			ti_new_functions = [fun_def_ptr : ti_new_functions], ti_fun_defs = ti_fun_defs,
	  			ti_type_heaps = ti_type_heaps, ti_cleanup_info = us_cleanup_info, 
	  			ti_cons_args = ti_cons_args }
	  (new_fun_rhs, ti)
			= transform tb_rhs ro ti
	  new_fd
	  		= { new_fd_expanding & fun_body = TransformedBody {tb_args = new_fun_args, tb_rhs = new_fun_rhs} }
	| False -!-> ("generated function", new_fd, new_cons_args)		= undef
// DvA...
	# fun_heap = ti.ti_fun_heap
	// producer requirements for generated function here...
	#! prs	=
		{ prs_group				= [dec ti_next_fun_nr]
		, prs_cons_args 		= ti.ti_cons_args
		, prs_main_dcl_module_n	= ro.ro_main_dcl_module_n
		, prs_fun_heap			= fun_heap
		}
	# (safe,prs)	= producerRequirements new_fun_rhs prs
	# fun_heap = prs.prs_fun_heap
// ...DvA
	# new_gen_fd = { new_gen_fd & gf_fun_def = new_fd, gf_cons_args = {new_fd_cons_args & cc_producer = safe}}
	# ti =
		{ ti
		& ti_fun_heap = fun_heap <:= (fun_def_ptr, FI_Function new_gen_fd)
		, ti_cons_args= prs.prs_cons_args
		}
	= (ti_next_fun_nr, fun_arity, ti)
where
	st_args_array :: ![AType] !StrictnessList -> .{#ATypesWithStrictness}
	st_args_array st_args args_strictness
		# strict1=Strict 1
		= { {ats_types=[el],ats_strictness=if (arg_is_strict i args_strictness) strict1 NotStrict} \\ i<-[0..] & el <- st_args }
		
	is_dictionary {at_type=TA {type_index} _} es_td_infos
		#! td_infos_of_module=es_td_infos.[type_index.glob_module]
		= type_index.glob_object>=size td_infos_of_module || td_infos_of_module.[type_index.glob_object].tdi_group_nr==(-1)
	is_dictionary _ es_td_infos
		= False

	set_cons_var_bit {tv_info_ptr} (cons_vars, th_vars)
		# (TVI_Type (TempV i), th_vars) = readPtr tv_info_ptr th_vars 
		= (set_bit i cons_vars, th_vars)

	copy_opt_symbol_type No ti_type_heaps
		= (No, ti_type_heaps)
	copy_opt_symbol_type (Yes symbol_type=:{st_vars, st_attr_vars, st_args, st_result, st_attr_env})
				ti_type_heaps=:{th_vars, th_attrs}
		# (fresh_st_vars, th_vars)
				= mapSt bind_to_fresh_type_variable st_vars th_vars
		  (fresh_st_attr_vars, th_attrs)
				= mapSt bind_to_fresh_attr_variable st_attr_vars th_attrs
		  (_, [fresh_st_result:fresh_st_args], ti_type_heaps)
		  		= substitute [st_result:st_args] { ti_type_heaps & th_vars = th_vars, th_attrs = th_attrs }
		  (_, fresh_st_attr_env, ti_type_heaps)
		  		= substitute st_attr_env ti_type_heaps
		= (Yes { symbol_type & st_vars = fresh_st_vars, st_attr_vars = fresh_st_attr_vars, st_args = fresh_st_args,
				st_result = fresh_st_result, st_attr_env = fresh_st_attr_env}, ti_type_heaps)

	add_propagation_attributes common_defs No state
		= (No, state)
	add_propagation_attributes common_defs (Yes st=:{st_args, st_result, st_attr_env, st_attr_vars})
				(type_heaps, type_def_infos)
		# ps	=
					{ prop_type_heaps	= type_heaps
					, prop_td_infos		= type_def_infos
					, prop_attr_vars	= st_attr_vars
					, prop_attr_env		= st_attr_env
					, prop_error		= No 
					}
		# ([sound_st_result:sound_st_args], ps)
//			  	= add_propagation_attributes_to_atypes common_defs [st_result:st_args] ps
			  	= mapSt (add_propagation_attributes_to_atype common_defs) [st_result:st_args] ps
		  sound_symbol_type = { st 
						  		& st_args		= sound_st_args
						  		, st_result		= sound_st_result
						  		, st_attr_env	= ps.prop_attr_env
						  		, st_attr_vars	= ps.prop_attr_vars
						  		}
		  state = (ps.prop_type_heaps, ps.prop_td_infos)
		= (Yes sound_symbol_type, state)

	add_propagation_attributes_to_atype modules type ps
		| is_dictionary type ps.prop_td_infos
			= (type, ps)
		# (type, prop_class, ps) = addPropagationAttributesToAType modules type ps
		= (type, ps)

//	add_propagation_attributes_to_atypes :: {#CommonDefs} ![AType] !*PropState -> (![AType],!*PropState)
//	add_propagation_attributes_to_atypes modules types ps
//		= mapSt (add_propagation_attributes_to_atype modules) types ps

	accum_class_type prods ro i (type_accu, ti_fun_defs, ti_fun_heap)
		= case prods.[i] of
			PR_Class _ _ class_type
				-> ([{empty_atype & at_type = class_type}  : type_accu ], ti_fun_defs, ti_fun_heap)
			_
				-> (type_accu, ti_fun_defs, ti_fun_heap)

	accum_function_producer_type prods ro i (type_accu, ti_fun_defs, ti_fun_heap)
		= case prods.[size prods-i-1] of
			PR_Empty
				-> ([No:type_accu], ti_fun_defs, ti_fun_heap)
			PR_Class _ _ class_type
				-> ([No:type_accu], ti_fun_defs, ti_fun_heap)
			producer
				# (symbol,_) = get_producer_symbol producer
				  (symbol_type, ti_fun_defs, ti_fun_heap)
						= get_producer_type symbol ro ti_fun_defs ti_fun_heap
				-> ([Yes symbol_type:type_accu], ti_fun_defs, ti_fun_heap)

// get_producer_type retrieves the type of symbol
	get_producer_type {symb_kind=SK_Function {glob_module, glob_object}} ro fun_defs fun_heap
		| glob_module == ro.ro_main_dcl_module_n
// Sjaak ...
			# ({fun_type=Yes symbol_type, fun_info={fi_properties}}, fun_defs) = fun_defs![glob_object]
			|  fi_properties bitand FI_HasTypeSpec <> 0
				# (_, symbol_type) = removeAnnotations symbol_type
				= (symbol_type, fun_defs, fun_heap)
				= (symbol_type, fun_defs, fun_heap)
			# {ft_type} = ro.ro_imported_funs.[glob_module].[glob_object]
			  (_, ft_type=:{st_args,st_args_strictness}) = removeAnnotations ft_type
			  new_st_args = addTypesOfDictionaries ro.ro_common_defs ft_type.st_context st_args
			  new_st_arity = length new_st_args
			  new_st_args_strictness = insert_n_strictness_values_at_beginning (new_st_arity-length st_args) st_args_strictness
			= ({ft_type & st_args = new_st_args, st_args_strictness = new_st_args_strictness, st_arity = new_st_arity, st_context = [] }, fun_defs, fun_heap)
// ... Sjaak
	get_producer_type {symb_kind=SK_LocalMacroFunction glob_object} ro fun_defs fun_heap
		# ({fun_type=Yes symbol_type}, fun_defs) = fun_defs![glob_object]
		= (symbol_type, fun_defs, fun_heap)
	get_producer_type {symb_kind=SK_GeneratedFunction fun_ptr _} ro fun_defs fun_heap
		# (FI_Function {gf_fun_def={fun_type=Yes symbol_type}}, fun_heap) = readPtr fun_ptr fun_heap
		= (symbol_type, fun_defs, fun_heap)
	get_producer_type {symb_kind=SK_Constructor {glob_module, glob_object}} ro fun_defs fun_heap
		# cons_defs = ro.ro_common_defs.[glob_module].com_cons_defs
		# {cons_type} = cons_defs.[glob_object]
		# (_,cons_type) = removeAnnotations cons_type	// necessary???
		= (cons_type, fun_defs, fun_heap)

	collectPropagatingConsVars type th_vars
		# th_vars
				= performOnTypeVars initializeToTVI_Empty type th_vars
		= performOnTypeVars collect_unencountered_cons_var type ([], th_vars)
	  where
		collect_unencountered_cons_var TA_MultiOfPropagatingConsVar tv=:{tv_info_ptr} (cons_var_accu, th_vars)
			# (tvi, th_vars) = readPtr tv_info_ptr th_vars
			= case tvi of
				TVI_Empty
					-> ([tv:cons_var_accu], writePtr tv_info_ptr TVI_Used th_vars)
				TVI_Used
					-> (cons_var_accu, th_vars)
		collect_unencountered_cons_var _ _ state
			= state

	replace_integers_in_substitution replace_input i (subst, used)
		# (subst_i, subst)
				= subst![i]
		  (subst_i, used)
		  		= replaceIntegers subst_i replace_input used
		= ({ subst & [i] = subst_i }, used)

	coerce_types common_defs cons_vars {ur_offered, ur_demanded} (subst, coercions, ti_type_def_infos, ti_type_heaps)
		# (opt_error_info, subst, coercions, ti_type_def_infos, ti_type_heaps)
				= determineAttributeCoercions ur_offered ur_demanded True
						subst coercions common_defs cons_vars ti_type_def_infos ti_type_heaps
		= case opt_error_info of
			Yes _
				-> abort "sanity check nr 5623 failed in module trans"
			No
				-> (subst, coercions, ti_type_def_infos, ti_type_heaps)

// expand_type converts 'pointer' type representation to 'integer' type representation
// inverse of class replaceIntegers
	expand_type ro_common_defs cons_vars atype (coercions, subst, ti_type_heaps, ti_type_def_infos)
		| is_dictionary atype ti_type_def_infos
			# (_, atype, subst) = arraySubst atype subst
			= (atype, (coercions, subst, ti_type_heaps, ti_type_def_infos))
		# es
	  			= { es_type_heaps = ti_type_heaps, es_td_infos = ti_type_def_infos }
		  (_, btype, (subst, es))
		  		= expandType ro_common_defs cons_vars atype (subst, es)
 		  { es_type_heaps = ti_type_heaps, es_td_infos = ti_type_def_infos }
				= es
		# cs
				= { crc_type_heaps = ti_type_heaps, crc_coercions = coercions, crc_td_infos = ti_type_def_infos }
		  (_, cs)
		  		= coerce PositiveSign ro_common_defs cons_vars [] btype btype cs
		  { crc_type_heaps = ti_type_heaps, crc_coercions = coercions, crc_td_infos = ti_type_def_infos }
		  		= cs
		= (btype, (coercions, subst, ti_type_heaps, ti_type_def_infos))

//@ determine_args
:: *DetermineArgsState =
	{ das_vars						:: ![FreeVar]
	, das_arg_types					:: !*{#ATypesWithStrictness}
	, das_next_attr_nr				:: !Int
	, das_new_linear_bits			:: ![Bool]
	, das_new_cons_args				:: ![ConsClass]
	, das_uniqueness_requirements	:: ![UniquenessRequirement]
	, das_subst						:: !*{!Type}
	, das_let_bindings				:: !(![LetBind],![LetBind],![AType],![AType])	// DvA: only used in strict_let variant
	, das_type_heaps				:: !*TypeHeaps
	, das_symbol_heap				:: !*ExpressionHeap					// unused...
	, das_fun_defs					:: !*{#FunDef}
	, das_fun_heap					:: !*FunctionHeap
	, das_var_heap					:: !*VarHeap
	, das_cons_args					:: !*{!ConsClasses}
	}

determine_args
	:: ![Bool] ![ConsClass] !Index !{!Producer} ![Optional SymbolType] ![FreeVar] !ReadOnlyTI !*DetermineArgsState
	-> !*DetermineArgsState
determine_args _ [] prod_index producers prod_atypes forms _ das=:{das_var_heap}
	# (vars, das_var_heap)	= new_variables forms das_var_heap
	= {das & das_vars = vars, das_var_heap = das_var_heap}
where
	new_variables [] var_heap
		= ([], var_heap)
	new_variables [form=:{fv_name,fv_info_ptr}:forms] var_heap
		# (vars, var_heap) = new_variables forms var_heap
		  (new_info_ptr, var_heap) = newPtr VI_Empty var_heap
		= ([{ form & fv_info_ptr = new_info_ptr } : vars], writeVarInfo fv_info_ptr (VI_Variable fv_name new_info_ptr) var_heap)

determine_args [linear_bit : linear_bits] [cons_arg : cons_args] prod_index producers [prod_atype:prod_atypes]
				[form : forms] input das
	# das = determine_args linear_bits cons_args (inc prod_index) producers prod_atypes forms input das
	# producer	= if (cons_arg == cActive) (producers.[prod_index]) PR_Empty
	= determine_arg producer prod_atype form prod_index ((linear_bit,cons_arg), input) das

determine_arg
	:: !Producer .(Optional SymbolType) !FreeVar .Int !(!(!Bool,!ConsClass),!ReadOnlyTI) !*DetermineArgsState
	-> !*DetermineArgsState

determine_arg PR_Empty _ form=:{fv_name,fv_info_ptr} _ ((linear_bit,cons_arg), _) das=:{das_var_heap}
	# (new_info_ptr, das_var_heap)	= newPtr VI_Empty das_var_heap
	# das_var_heap					= writeVarInfo fv_info_ptr (VI_Variable fv_name new_info_ptr) das_var_heap
	=	{ das 
		& das_vars				= [{ form & fv_info_ptr = new_info_ptr } : das.das_vars ]
		, das_new_linear_bits	= [ linear_bit : das.das_new_linear_bits ]
		, das_new_cons_args		= [ cons_arg : das.das_new_cons_args ]
		, das_var_heap			= das_var_heap
		}

determine_arg (PR_Class class_app free_vars_and_types class_type) _ {fv_info_ptr,fv_name} prod_index (_,ro)
			  das=:{das_arg_types, das_subst, das_type_heaps}
	# (ws_arg_type, das_arg_types)
			= das_arg_types![prod_index]
	# {ats_types=[arg_type:_]}
	  		= ws_arg_type
	  (_, int_class_type, das_type_heaps)
	  		= substitute class_type das_type_heaps
	  class_atype
	  		= { empty_atype & at_type = int_class_type }
	  type_input
	  		= { ti_common_defs = ro.ro_common_defs
	  		  , ti_functions = ro.ro_imported_funs
			  ,	ti_main_dcl_module_n = ro.ro_main_dcl_module_n
			  }
	// AA: Dummy generic dictionary does not unify with corresponding class dictionary.
	// Make it unify 			  		
	# (succ, das_subst, das_type_heaps)
	  		//AA: = unify class_atype arg_type type_input das_subst das_type_heaps
	  		= unify_dict class_atype arg_type type_input das_subst das_type_heaps
	  	with
	  		unify_dict class_atype=:{at_type=TA type_symb1 args1} arg_type=:{at_type=TA type_symb2 args2} 
	  			| type_symb1 == type_symb2 
	  				= unify class_atype arg_type
	  			// FIXME: check indexes, not names. Need predefs for that. 	
	  			| type_symb1.type_name.id_name == "GenericDict"
	  				= unify {class_atype & at_type = TA type_symb2 args1} arg_type	
	  			| type_symb2.type_name.id_name == "GenericDict"
	  				= unify class_atype {arg_type & at_type = TA type_symb1 args2} 	  				
	  		unify_dict class_atype arg_type 
	  			= unify class_atype arg_type	
	  			
	| not succ
		= abort ("sanity check nr 93 in module trans failed\n"--->(class_atype,"\n", arg_type))
	# (free_vars_and_types,das_type_heaps) = mapSt subFVT free_vars_and_types das_type_heaps
		with
			subFVT (fv,ty) th
				# (_,ty`,th`)		= substitute ty th
				= ((fv,ty`),th`)

	# ws_ats_types = [ { empty_atype & at_type = at_type } \\ (_, at_type) <- free_vars_and_types]
	# ws_arg_type` = {ats_types= ws_ats_types, ats_strictness = first_n_strict (length free_vars_and_types) }

	= {das
		& das_vars = mapAppend (\({var_info_ptr,var_name}, _)
						-> { fv_name = var_name, fv_info_ptr = var_info_ptr, fv_def_level = NotALevel, fv_count = 0 })
				  			  free_vars_and_types das.das_vars
		, das_arg_types			= {das_arg_types & [prod_index] = ws_arg_type` }
		, das_new_linear_bits	= mapAppend (\_ -> True) free_vars_and_types das.das_new_linear_bits
		, das_new_cons_args		= mapAppend (\_ -> cActive) free_vars_and_types das.das_new_cons_args
		, das_subst				= das_subst
		, das_type_heaps		= das_type_heaps
		, das_var_heap			= writeVarInfo fv_info_ptr (VI_Dictionary class_app.app_symb class_app.app_args class_type) das.das_var_heap
		}

determine_arg producer (Yes {st_args, st_args_strictness, st_result, st_attr_vars, st_context, st_attr_env, st_arity})
				{fv_info_ptr,fv_name} prod_index ((linear_bit, _),ro)
				das=:{das_subst,das_type_heaps,das_fun_defs,das_fun_heap,das_var_heap,das_cons_args}

	# {th_vars, th_attrs}		= das_type_heaps
	# (symbol,symbol_arity)		= get_producer_symbol producer
	  curried					= case producer of (PR_Curried _ _) -> True; _ -> False;
	#! size_fun_defs			= size das_fun_defs

	# ({cc_args, cc_linear_bits}, das_fun_heap, das_cons_args)
			= calc_cons_args curried symbol symbol_arity das_cons_args linear_bit size_fun_defs das_fun_heap

	  ({ats_types=[arg_type:_],ats_strictness}, das)
	  		= das!das_arg_types.[prod_index]

	  (das_next_attr_nr, th_attrs)
	  		= foldSt bind_to_temp_attr_var st_attr_vars (das.das_next_attr_nr, th_attrs)
	  		// prepare for substitute calls
	  (_, (st_args, st_result), das_type_heaps)
	  		= substitute (st_args, st_result) { das_type_heaps & th_vars = th_vars, th_attrs = th_attrs }
	  nr_of_applied_args
			= symbol_arity
	  application_type
	  		= build_application_type st_arity (length st_context) st_result st_args nr_of_applied_args
	  type_input
	  		= { ti_common_defs			= ro.ro_common_defs
	  		  , ti_functions			= ro.ro_imported_funs
			  ,	ti_main_dcl_module_n	= ro.ro_main_dcl_module_n
			  }
	  (succ, das_subst, das_type_heaps)
	  		= unify (skip_TFA application_type) (skip_TFA arg_type) type_input das_subst das_type_heaps
			with
				skip_TFA at=:{at_type = TFA vars type}
					= { at & at_type = type }
				skip_TFA at
					= at
	| not succ
		= abort ("sanity check nr 94 in module trans failed"--->(application_type, arg_type))
	# (attr_inequalities, das_type_heaps)
			= accAttrVarHeap (mapSt substitute_attr_inequality st_attr_env) das_type_heaps
	  new_uniqueness_requirement
	  		= { ur_offered		= application_type
	  		  , ur_demanded		= arg_type
	  		  , ur_attr_ineqs	= attr_inequalities 
	  		  }
	  (opt_body, var_names, das_fun_defs, das_fun_heap)
	  		= case producer of
	  			(PR_Constructor {symb_kind=SK_Constructor {glob_module}} arity _)
  					-> (NoBody, repeatn arity { id_name = "_x", id_info = nilPtr }, das_fun_defs, das_fun_heap)
	  			(PR_Curried {symb_kind=SK_Function {glob_module}} arity)
	  				| glob_module <> ro.ro_main_dcl_module_n
	  					// we do not have good names for the formal variables of that function: invent some
	  					-> (NoBody, repeatn arity { id_name = "_x", id_info = nilPtr }, das_fun_defs, das_fun_heap)
	  				// GOTO next alternative
	  			_
					# ({fun_body=fun_body=:TransformedBody tb}, das_fun_defs, das_fun_heap)
							= get_fun_def symbol.symb_kind ro.ro_main_dcl_module_n das_fun_defs das_fun_heap
					-> (fun_body, take nr_of_applied_args [ fv_name \\ {fv_name}<-tb.tb_args ], das_fun_defs, das_fun_heap)
	  (form_vars, act_vars, das_var_heap) 
	  		= build_var_args (reverse var_names) das.das_vars [] das_var_heap
	  (expr_to_unfold, das_var_heap)
			= case producer of
				(PR_Constructor symb _ expr)
					-> (VI_Expression (App { app_symb = symbol, app_args = act_vars, app_info_ptr = nilPtr }), das_var_heap)
				(PR_Curried _ _)
					-> (VI_Expression (App { app_symb = symbol, app_args = act_vars, app_info_ptr = nilPtr }), das_var_heap)
				_ // function or generated function
					# (TransformedBody tb) = opt_body
					-> (VI_Body symbol tb (take nr_of_applied_args form_vars), das_var_heap)
/* DvA... STRICT_LET
	  (expr_to_unfold, das_var_heap, let_bindings)
			= case arg_type.at_annotation of
				AN_Strict
					# (new_info_ptr_l, das_var_heap) = newPtr VI_Empty das_var_heap
	  				# free_var_l = { fv_name = { id_name = "free_l", id_info = nilPtr }, fv_info_ptr = new_info_ptr_l, fv_count = 0, fv_def_level = NotALevel }
			  		# act_var_l = Var { var_name = { id_name = "act_l", id_info = nilPtr }, var_info_ptr = new_info_ptr_l, var_expr_ptr = nilPtr }

					# bind = {lb_dst = fv, lb_src = act_var_l, lb_position = NoPos}

					# das_var_heap = writeVarInfo new_info_ptr_l expr_to_unfold das_var_heap

					# let_bindings = case let_bindings of
									(s,l,st,lt) -> ([bind:s],l,[arg_type:st],lt)
					-> (VI_Empty, das_var_heap, let_bindings)
				_	-> (expr_to_unfold,das_var_heap,let_bindings)
...DvA */
	=	{ das 
		& das_vars						= form_vars
		, das_arg_types.[prod_index]	= {ats_types=take nr_of_applied_args st_args,ats_strictness=st_args_strictness} 
		, das_next_attr_nr				= das_next_attr_nr
		, das_new_linear_bits			= cc_linear_bits ++ das.das_new_linear_bits
		, das_new_cons_args				= cc_args ++ das.das_new_cons_args
		, das_uniqueness_requirements	= [new_uniqueness_requirement:das.das_uniqueness_requirements]
		, das_subst						= das_subst
		, das_type_heaps				= das_type_heaps
		, das_fun_defs					= das_fun_defs
		, das_fun_heap					= das_fun_heap
		, das_var_heap					= writeVarInfo fv_info_ptr expr_to_unfold das_var_heap
		, das_cons_args					= das_cons_args
		}
where
	build_var_args [] form_vars act_vars var_heap
		= (form_vars, act_vars, var_heap)
	build_var_args [new_name:new_names] form_vars act_vars var_heap
		# (info_ptr, var_heap) = newPtr VI_Empty var_heap
		  form_var = { fv_name = new_name, fv_info_ptr = info_ptr, fv_count = 0, fv_def_level = NotALevel }
		  act_var = { var_name = new_name, var_info_ptr = info_ptr, var_expr_ptr = nilPtr }
		= build_var_args new_names [form_var : form_vars] [Var act_var : act_vars] var_heap

	calc_cons_args curried {symb_kind} symbol_arity ti_cons_args linear_bit size_fun_defs fun_heap
		# (cons_size, ti_cons_args) = usize ti_cons_args
		# (opt_cons_classes, fun_heap, ti_cons_args)
				= case symb_kind of
					SK_Function {glob_module, glob_object}
						| glob_module == ro.ro_main_dcl_module_n && glob_object < cons_size
							# (cons_args, ti_cons_args) = ti_cons_args![glob_object]
							-> (Yes cons_args, fun_heap, ti_cons_args)
						-> (No, fun_heap, ti_cons_args)
					SK_LocalMacroFunction glob_object
						| glob_object < cons_size
							# (cons_args, ti_cons_args) = ti_cons_args![glob_object]
							-> (Yes cons_args, fun_heap, ti_cons_args)
						-> (No, fun_heap, ti_cons_args)
					SK_GeneratedFunction fun_ptr fun_index
						| fun_index < cons_size
							# (cons_args, ti_cons_args) = ti_cons_args![fun_index]
							-> (Yes cons_args, fun_heap, ti_cons_args)
						| fun_index < size_fun_defs
							-> abort "sanity check failed in module trans"
						# (FI_Function {gf_cons_args}, fun_heap) = readPtr fun_ptr fun_heap
						-> (Yes gf_cons_args, fun_heap, ti_cons_args)
					SK_Constructor _
						-> (No, fun_heap, ti_cons_args)
		= case opt_cons_classes of
			Yes cons_classes
				-> ({ cc_size = symbol_arity, cc_args = take symbol_arity cons_classes.cc_args, 
		  				cc_linear_bits = if curried (repeatn symbol_arity linear_bit) 
		  									(take symbol_arity cons_classes.cc_linear_bits),
		  				cc_producer = False}
		  			, fun_heap, ti_cons_args)
			No
				-> ({cc_size = symbol_arity, cc_args = repeatn symbol_arity cPassive,
						cc_linear_bits = repeatn symbol_arity linear_bit,
						cc_producer = False}, fun_heap, ti_cons_args)


	build_application_type st_arity nr_context_args st_result st_args nr_of_applied_args
		| st_arity+nr_context_args==nr_of_applied_args
			= st_result
		| nr_of_applied_args<nr_context_args
			= abort "sanity check nr 234 failed in module trans"
		# (applied_args, unapplied_args) = splitAt (nr_of_applied_args-nr_context_args) st_args
		  attr_approx = if (any has_unique_attribute applied_args) TA_Unique TA_Multi
		= foldr (\atype1 atype2->{at_attribute=attr_approx, at_type=atype1-->atype2})
				st_result unapplied_args
	  where
		has_unique_attribute {at_attribute=TA_Unique} = True
		has_unique_attribute _ = False

//@ max_group_index

max_group_index
	:: !Int !{!Producer} Index Index *{#FunDef} *FunctionHeap *{!ConsClasses}
	-> (Index,*{!ConsClasses},*{#FunDef},*FunctionHeap)
max_group_index prod_index producers ro_main_dcl_module_n current_max fun_defs fun_heap cons_args
	| prod_index == size producers
		= (current_max, cons_args, fun_defs, fun_heap)
		# (current_max, cons_args, fun_defs, fun_heap)
			= max_group_index_of_producer producers.[prod_index] current_max fun_defs fun_heap cons_args
		= max_group_index (inc prod_index) producers ro_main_dcl_module_n current_max fun_defs fun_heap cons_args
where
	max_group_index_of_producer PR_Empty current_max fun_defs fun_heap cons_args
		= (current_max, cons_args, fun_defs, fun_heap)
	max_group_index_of_producer (PR_Class {app_args} _ _) current_max fun_defs fun_heap cons_args
		= foldSt (foldrExprSt max_group_index_of_member) app_args (current_max, cons_args, fun_defs, fun_heap)
	max_group_index_of_producer (PR_Curried {symb_kind=SK_Function {glob_object=fun_index, glob_module}} _) current_max fun_defs fun_heap cons_args
		| glob_module<>ro_main_dcl_module_n
			= (current_max, cons_args, fun_defs, fun_heap)
		# (current_max, fun_defs) = max_group_index_of_fun_with_fun_index fun_index current_max fun_defs
		= (current_max, cons_args, fun_defs, fun_heap)
	max_group_index_of_producer (PR_Curried {symb_kind=SK_LocalMacroFunction fun_index} _) current_max fun_defs fun_heap cons_args
		# (current_max, fun_defs) = max_group_index_of_fun_with_fun_index fun_index current_max fun_defs
		= (current_max, cons_args, fun_defs, fun_heap)
	max_group_index_of_producer (PR_Curried { symb_kind = SK_GeneratedFunction fun_ptr fun_index} _) current_max fun_defs fun_heap cons_args
		# (current_max, fun_defs, fun_heap) = max_group_index_of_fun_with_fun_index_and_ptr fun_ptr fun_index current_max fun_defs fun_heap
		= (current_max, cons_args, fun_defs, fun_heap)
	max_group_index_of_producer (PR_Function _ _ fun_index) current_max fun_defs fun_heap cons_args
		# (current_max, fun_defs) = max_group_index_of_fun_with_fun_index fun_index current_max fun_defs
		= (current_max, cons_args, fun_defs, fun_heap)
	max_group_index_of_producer (PR_GeneratedFunction { symb_kind = SK_GeneratedFunction fun_ptr fun_index} _ _)
								current_max fun_defs fun_heap cons_args
		# (current_max, fun_defs, fun_heap) = max_group_index_of_fun_with_fun_index_and_ptr fun_ptr fun_index current_max fun_defs fun_heap
		= (current_max, cons_args, fun_defs, fun_heap)
	max_group_index_of_producer (PR_Constructor symb _ args) current_max fun_defs fun_heap cons_args
		= (current_max, cons_args, fun_defs, fun_heap)	// DvA: not a clue what we're trying here...
	max_group_index_of_producer prod current_max fun_defs fun_heap cons_args
		= abort ("trans.icl: max_group_index_of_producer" ---> prod)

	max_group_index_of_member
				(App {app_symb = {symb_name, symb_kind = SK_Function { glob_object = fun_index, glob_module = mod_index}}}) 
				(current_max, cons_args, fun_defs, fun_heap)
		| mod_index == ro_main_dcl_module_n
			# (size_args, cons_args) = usize cons_args
			| fun_index < size_args
				# ({fun_info = {fi_group_index}},fun_defs) = fun_defs![fun_index]
				= (max fi_group_index current_max, cons_args, fun_defs, fun_heap)
			= (current_max, cons_args, fun_defs, fun_heap)
		= (current_max, cons_args, fun_defs, fun_heap)
	max_group_index_of_member
				(App {app_symb = {symb_name, symb_kind = SK_LocalMacroFunction fun_index}})
				(current_max, cons_args, fun_defs, fun_heap)
		# (size_args, cons_args) = usize cons_args
		| fun_index < size_args
			# ({fun_info = {fi_group_index}}, fun_defs) = fun_defs![fun_index]
			= (max fi_group_index current_max, cons_args, fun_defs, fun_heap)
		= (current_max, cons_args, fun_defs, fun_heap)
	max_group_index_of_member
				(App {app_symb = {symb_kind = SK_GeneratedFunction fun_ptr _}})
				(current_max, cons_args, fun_defs, fun_heap)
		# (FI_Function {gf_fun_def={fun_info = {fi_group_index}}}, fun_heap) = readPtr fun_ptr fun_heap
		= (max fi_group_index current_max, cons_args, fun_defs, fun_heap)
	max_group_index_of_member _ (current_max, cons_args, fun_defs, fun_heap)
		= (current_max, cons_args, fun_defs, fun_heap)

	max_group_index_of_fun_with_fun_index fun_index current_max fun_defs
		# (fun_def,fun_defs) = fun_defs![fun_index]
		= (max fun_def.fun_info.fi_group_index current_max, fun_defs)

	max_group_index_of_fun_with_fun_index_and_ptr fun_ptr fun_index current_max fun_defs fun_heap
		# (fun_size, fun_defs)	= usize fun_defs
		| fun_index < fun_size
			# ({fun_info},fun_defs) = fun_defs![fun_index] 
			= (max fun_info.fi_group_index current_max, fun_defs, fun_heap)
			# (FI_Function generated_function, fun_heap) = readPtr fun_ptr fun_heap
			= (max generated_function.gf_fun_def.fun_info.fi_group_index current_max, fun_defs, fun_heap)

//@ replaceIntegers

class replaceIntegers a :: !a !({!TypeVar}, !{!TypeAttribute}, !AttributePartition) !*{#Bool} -> (!a, !.{#Bool})
	// get rid of all those TempV and TA_Var things

instance replaceIntegers (a, b) | replaceIntegers a & replaceIntegers b where
	replaceIntegers (a, b) input used
		# (a, used) = replaceIntegers a input used
		  (b, used) = replaceIntegers b input used
		= ((a, b), used)

instance replaceIntegers [a] | replaceIntegers a where
	replaceIntegers [] input used
		= ([], used)
	replaceIntegers [h:t] input used
		# (h, used) = replaceIntegers h input used
		  (t, used) = replaceIntegers t input used
		= ([h:t], used)

instance replaceIntegers TypeAttribute where
	replaceIntegers (TA_TempVar i) (_, attributes, attr_partition) used
		# index = attr_partition.[i]
		  attribute = attributes.[index]
		= (attribute, { used & [index] = isAttrVar attribute })
	  where
		isAttrVar (TA_Var _) = True
		isAttrVar _ = False
	replaceIntegers ta _ used
		= (ta, used)

instance replaceIntegers Type where
	replaceIntegers (TA type_symb_ident args) input used
		# (args, used) = replaceIntegers args input used
		= (TA type_symb_ident args, used)
	replaceIntegers (TAS type_symb_ident args strictness) input used
		# (args, used) = replaceIntegers args input used
		= (TAS type_symb_ident args strictness, used)
	replaceIntegers (a --> b) input used
		# (a, used) = replaceIntegers a input used
		  (b, used) = replaceIntegers b input used
		= (a --> b, used)
	replaceIntegers (consvar :@: args) input=:(fresh_type_vars, _, _) used
		# (TempCV i) = consvar
		  (args, used) = replaceIntegers args input used
		= (CV fresh_type_vars.[i] :@: args, used)
	replaceIntegers (TempV i) (fresh_type_vars, _, _) used
		= (TV fresh_type_vars.[i], used)
	replaceIntegers type input used
		= (type, used)

instance replaceIntegers AType where
	replaceIntegers atype=:{at_attribute, at_type} input used
		# (at_attribute, used) = replaceIntegers at_attribute input used
		  (at_type, used) = replaceIntegers at_type input used
		= ({atype & at_attribute = at_attribute, at_type = at_type}, used)

// Variable binding...

bind_to_fresh_expr_var {fv_name, fv_info_ptr} var_heap
	# (new_info_ptr, var_heap) = newPtr VI_Empty var_heap
	  form_var = { fv_name = fv_name, fv_info_ptr = new_info_ptr, fv_count = undeff, fv_def_level = NotALevel }
	  act_var = { var_name = fv_name, var_info_ptr = new_info_ptr, var_expr_ptr = nilPtr }
	= (form_var, writeVarInfo fv_info_ptr (VI_Expression (Var act_var)) var_heap)

bind_to_fresh_type_variable {tv_name, tv_info_ptr} th_vars
	# (new_tv_info_ptr, th_vars) = newPtr TVI_Empty th_vars
	  tv = { tv_name=tv_name, tv_info_ptr=new_tv_info_ptr }
	= (tv, writePtr tv_info_ptr (TVI_Type (TV tv)) th_vars)

bind_to_fresh_attr_variable {av_name, av_info_ptr} th_attrs
	# (new_av_info_ptr, th_attrs) = newPtr AVI_Empty th_attrs
	  av = { av_name=av_name, av_info_ptr=new_av_info_ptr }
	= (av, writePtr av_info_ptr (AVI_Attr (TA_Var av)) th_attrs)

bind_to_temp_type_var {tv_info_ptr} (next_type_var_nr, th_vars)
	= (next_type_var_nr+1, writePtr tv_info_ptr (TVI_Type (TempV next_type_var_nr)) th_vars)

bind_to_temp_attr_var {av_info_ptr} (next_attr_var_nr, th_attrs)
	= (next_attr_var_nr+1, writePtr av_info_ptr (AVI_Attr (TA_TempVar next_attr_var_nr)) th_attrs)

//
transformFunctionApplication fun_def instances cc=:{cc_size, cc_args, cc_linear_bits} app=:{app_symb,app_args} extra_args ro ti
	# (app_args, extra_args) = complete_application fun_def.fun_arity app_args extra_args
	| False -!-> ("transformFunctionApplication",app_symb,app_args) = undef
	| cc_size > 0 && not_expanding_consumer
		| False-!->("determineProducers",(app_symb.symb_name, cc_linear_bits,cc_args,app_args))
			= undef
	  	# (producers, new_args, ti) = determineProducers (fun_def.fun_info.fi_properties bitand FI_IsMacroFun <> 0) cc_linear_bits cc_args app_args
														 0 (createArray cc_size PR_Empty) ro ti
	  	| False-!->("results in",II_Node producers nilPtr II_Empty II_Empty)
	  		= undef
	  	| containsProducer cc_size producers
	  		# (is_new, fun_def_ptr, instances, ti_fun_heap) = tryToFindInstance producers instances ti.ti_fun_heap
	  		| is_new
	  			# ti = update_instance_info app_symb.symb_kind instances { ti & ti_fun_heap = ti_fun_heap }
	  			# (fun_index, fun_arity, ti) = generateFunction fun_def cc producers fun_def_ptr ro ti
	  			  app_symb = { app_symb & symb_kind = SK_GeneratedFunction fun_def_ptr fun_index }
				# (app_args, extra_args) = complete_application fun_arity new_args extra_args
	  			= transformApplication { app & app_symb = app_symb, app_args = app_args } extra_args ro ti
	  			# (FI_Function {gf_fun_index, gf_fun_def}, ti_fun_heap) = readPtr fun_def_ptr ti_fun_heap
				  app_symb = { app_symb & symb_kind = SK_GeneratedFunction fun_def_ptr gf_fun_index }
				  (app_args, extra_args) = complete_application gf_fun_def.fun_arity new_args extra_args
	  			# ti = {ti & ti_fun_heap = ti_fun_heap }
	  			= transformApplication { app & app_symb = app_symb, app_args = app_args } extra_args ro ti
			= (build_application { app & app_symb = app_symb, app_args = app_args } extra_args, ti)
		= (build_application { app & app_symb = app_symb, app_args = app_args } extra_args, ti)
where
	not_expanding_consumer = case fun_def.fun_body of
								Expanding _	-> False
								_			-> True

	update_instance_info (SK_Function {glob_object}) instances ti=:{ti_instances}
		 = { ti & ti_instances = { ti_instances & [glob_object] = instances } }
	update_instance_info (SK_LocalMacroFunction glob_object) instances ti=:{ti_instances}
		 = { ti & ti_instances = { ti_instances & [glob_object] = instances } }
	update_instance_info (SK_GeneratedFunction fun_def_ptr fun_index) instances ti=:{ti_fun_heap, ti_instances}
		| fun_index < size ti_instances
			= { ti & ti_instances = { ti_instances & [fun_index] = instances } }
		# (FI_Function fun_info, ti_fun_heap) = readPtr fun_def_ptr ti_fun_heap
		= { ti & ti_fun_heap = ti_fun_heap <:= (fun_def_ptr, FI_Function { fun_info & gf_instance_info = instances })}

	complete_application form_arity args []
		= (args, [])
	complete_application form_arity args extra_args
		# arity_diff = min (form_arity - length args) (length extra_args)
		= (args ++ take arity_diff extra_args, drop arity_diff extra_args)

	build_application app []
		= App app
	build_application app extra_args
		= App app @ extra_args
		
is_cons_or_decons_of_UList_or_UTSList glob_object glob_module imported_funs
	:== let  type = imported_funs.[glob_module].[glob_object].ft_type;
		  in type.st_arity>0 && not (isEmpty type.st_context);

is_nil_cons_or_decons_of_UList_or_UTSList glob_object glob_module imported_funs
	:== not (isEmpty imported_funs.[glob_module].[glob_object].ft_type.st_context);

transformApplication :: !App ![Expression] !ReadOnlyTI !*TransformInfo -> *(!Expression,!*TransformInfo)
transformApplication app=:{app_symb=symb=:{symb_kind}, app_args} extra_args
			ro ti=:{ti_cons_args,ti_instances,ti_fun_defs}
	| is_SK_Function_or_SK_LocalMacroFunction symb_kind // otherwise GOTO next alternative	
		# { glob_module, glob_object }
			= case symb_kind of
				SK_Function global_index -> global_index
				SK_LocalMacroFunction index -> { glob_module = ro.ro_main_dcl_module_n, glob_object = index }
		| glob_module == ro.ro_main_dcl_module_n
			| glob_object < size ti_cons_args
				#! cons_class = ti_cons_args.[glob_object]
				   (instances, ti_instances) = ti_instances![glob_object]
				   (fun_def, ti_fun_defs) = ti_fun_defs![glob_object]
				   ti = { ti & ti_instances = ti_instances, ti_fun_defs = ti_fun_defs }
				= transformFunctionApplication fun_def instances cons_class app extra_args ro ti
			// It seems as if we have an array function 
				| isEmpty extra_args
					= (App app, ti)
					= (App { app & app_args = app_args ++ extra_args}, ti)

		| glob_module==ro.ro_stdStrictLists_module_n && is_cons_or_decons_of_UList_or_UTSList glob_object glob_module ro.ro_imported_funs && (not (isEmpty app_args))
//			&& trace_tn ("transformApplication "+++toString symb.symb_name)
			# {ft_type} = ro.ro_imported_funs.[glob_module].[glob_object] // type of cons instance of instance List [#] a | U(TS)List a
			# [{tc_class=TCClass {glob_module,glob_object={ds_index}}}:_] = ft_type.st_context			
			# member_n=find_member_n 0 symb.symb_name.id_name ro.ro_common_defs.[glob_module].com_class_defs.[ds_index].class_members
			# cons_u_member_index=ro.ro_common_defs.[glob_module].com_class_defs.[ds_index].class_members.[member_n].ds_index
			# {me_symb,me_offset}=ro.ro_common_defs.[glob_module].com_member_defs.[cons_u_member_index]
			# select_symb= {glob_module=glob_module,glob_object={ds_ident=me_symb,ds_index=cons_u_member_index,ds_arity=1}}
			# [first_arg:other_app_args] = app_args;
			# args=other_app_args++extra_args
			| isEmpty args
				= select_member first_arg select_symb me_offset ti
				# (expr,ti) = select_member first_arg select_symb me_offset ti
				= case expr of
					App app
						-> transformApplication app args ro ti
					_
						-> (expr @ args,ti)
		// This function is imported
			| isEmpty extra_args
				= (App app, ti)
				# {ft_arity,ft_type} = ro.ro_imported_funs.[glob_module].[glob_object]
				  form_arity = ft_arity + length ft_type.st_context
				  ar_diff = form_arity - length app_args
				  nr_of_extra_args = length extra_args
				| nr_of_extra_args <= ar_diff
					= (App {app  &  app_args = app_args ++ extra_args }, ti)
					= (App {app  &  app_args = app_args ++ take ar_diff extra_args } @ drop ar_diff extra_args, ti)
	where
		find_member_n i member_string a
			| i<size a
				| a.[i].ds_ident.id_name % (0,size member_string-1)==member_string
					= i
					= find_member_n (i+1) member_string a

		select_member (App {app_symb={symb_kind=SK_Constructor _},app_args,app_info_ptr}) select_symb me_offset ti
			| not (isNilPtr app_info_ptr) && (case (sreadPtr app_info_ptr ti.ti_symbol_heap) of (EI_DictionaryType _) -> True; _ -> False)
//			&& trace_tn ("select_member "+++toString select_symb.glob_object.ds_ident.id_name)
				= (app_args !! me_offset,ti)
		select_member exp select_symb me_offset ti
			= (Selection NormalSelector exp [RecordSelection select_symb me_offset],ti)

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

transformSelection :: SelectorKind [Selection] Expression *TransformInfo -> (!Expression,!*TransformInfo)
transformSelection NormalSelector s=:[RecordSelection _ field_index : selectors] 
					app=:(App {app_symb={symb_kind= SK_Constructor _ }, app_args, app_info_ptr})
					ti=:{ti_symbol_heap}
	| isNilPtr app_info_ptr
		= (Selection NormalSelector app s, ti)
	# (app_info, ti_symbol_heap) = readPtr app_info_ptr ti_symbol_heap
	  ti = { ti & ti_symbol_heap = ti_symbol_heap }
	= case app_info of
		EI_DictionaryType _
			-> transformSelection NormalSelector selectors (app_args !! field_index) ti
		_
			-> (Selection NormalSelector app s, ti)
transformSelection NormalSelector [] expr ti
	= (expr, ti)
transformSelection selector_kind selectors expr ti
	= (Selection selector_kind expr selectors, ti)

//@	determineProducers

// XXX store linear_bits and cc_args together ?

// determineProducers: finds all legal producers in the argument list.
determineProducers :: Bool [Bool] [Int] [Expression] Int *{!Producer} ReadOnlyTI *TransformInfo -> *(!*{!Producer},![Expression],!*TransformInfo);
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
			# (app_info, ti_symbol_heap) = readPtr app_info_ptr ti.ti_symbol_heap
			= determineProducer is_applied_to_macro_fun linear_bit app app_info new_args prod_index producers ro { ti & ti_symbol_heap = ti_symbol_heap }
	determine_producer _ _ arg new_args _ producers _ ti
		= (producers, [arg : new_args], ti)

determineProducer :: Bool Bool App ExprInfo [Expression] Int *{!Producer} ReadOnlyTI *TransformInfo -> *(!*{!Producer},![Expression],!*TransformInfo)
// XXX check for linear_bit also in case of a constructor ?
determineProducer _ _ app=:{app_symb = symb=:{symb_kind = SK_Constructor _}, app_args} (EI_DictionaryType type) new_args prod_index producers _ ti
	# (app_args, (new_vars_and_types, free_vars, ti_var_heap)) 
			= renewVariables app_args ti.ti_var_heap
	| False -!-> ("Produce0cc",symb.symb_name)
		= undef
	= ( { producers & [prod_index] = PR_Class { app & app_args = app_args } new_vars_and_types type}
	  , mapAppend Var free_vars new_args
	  , { ti & ti_var_heap = ti_var_heap }
	  )
determineProducer _ linear_bit app=:{app_symb = symb=:{symb_kind = SK_Constructor _, symb_name}, app_args} _ new_args prod_index producers ro ti
	| False -!-> ("ProduceXcc",symb_name)
		= undef
	| SwitchConstructorFusion (ro.ro_transform_fusion && linear_bit) False
		# producers = {producers & [prod_index] = PR_Constructor symb (length app_args) app_args }
		= (producers, app_args ++ new_args, ti)
	= ( producers, [App app : new_args ], ti)
determineProducer is_applied_to_macro_fun linear_bit app=:{app_symb = symb=:{ symb_kind = SK_GeneratedFunction fun_ptr fun_index}, app_args} _
				  new_args prod_index producers ro ti
	# (FI_Function {gf_cons_args={cc_producer},gf_fun_def={fun_body, fun_arity, fun_type=Yes symbol_type}}, ti_fun_heap) = readPtr fun_ptr ti.ti_fun_heap
	  ti = { ti & ti_fun_heap=ti_fun_heap }
	| length app_args<>fun_arity
		| is_applied_to_macro_fun 
			= ({ producers & [prod_index] = PR_Curried symb (length app_args)}, app_args ++ new_args, ti)
				-!-> ("Produce1cc_macro",symb.symb_name)
		| SwitchCurriedFusion ro.ro_transform_fusion False
			= ({ producers & [prod_index] = PR_Curried symb (length app_args)}, app_args ++ new_args, ti)
				-!-> ("Produce1cc_curried",symb.symb_name)
		= (producers, [App app : new_args ], ti)
	# is_good_producer
		= case fun_body of
			Expanding _
				-> False
			(TransformedBody {tb_rhs})
				-> SwitchGeneratedFusion (ro.ro_transform_fusion && linear_bit && is_sexy_body tb_rhs) False
	| cc_producer && is_good_producer
		= ({ producers & [prod_index] = (PR_GeneratedFunction symb (length app_args) fun_index)}, app_args ++ new_args, ti)
				-!-> ("Produce1cc",symb.symb_name)
	= (producers, [App app : new_args ], ti)
determineProducer is_applied_to_macro_fun linear_bit app=:{app_symb = symb=:{symb_kind}, app_args} _
				  new_args prod_index producers ro ti
	| is_SK_Function_or_SK_LocalMacroFunction symb_kind
		# { glob_module, glob_object }
			= case symb_kind of
				SK_Function global_index -> global_index
				SK_LocalMacroFunction index -> { glob_module = ro.ro_main_dcl_module_n, glob_object = index }
		# (fun_arity, ti) = get_fun_arity glob_module glob_object ro ti
		| length app_args<>fun_arity
			| is_applied_to_macro_fun
				= ({ producers & [prod_index] = PR_Curried symb (length app_args)}, app_args ++ new_args, ti)
					-!-> ("Produce2cc_macro",symb.symb_name)
			| SwitchCurriedFusion ro.ro_transform_fusion False
				= ({ producers & [prod_index] = PR_Curried symb (length app_args)}, app_args ++ new_args, ti)
					-!-> ("Produce2cc_curried",symb.symb_name)
			= (producers, [App app : new_args ], ti)
		#! max_index = size ti.ti_cons_args
		| glob_module <> ro.ro_main_dcl_module_n || glob_object >= max_index /* Sjaak, to skip array functions */
			= (producers, [App app : new_args ], ti)
					-!-> ("Produce2cc_array",symb.symb_name)
		# ({fun_body}, ti_fun_defs) = (ti.ti_fun_defs)![glob_object]
		  ti = { ti & ti_fun_defs=ti_fun_defs }
		  (TransformedBody {tb_rhs}) = fun_body
		  is_good_producer = SwitchFunctionFusion (ro.ro_transform_fusion && linear_bit && is_sexy_body tb_rhs) False
		  {cc_producer} = ti.ti_cons_args.[glob_object]
		| is_good_producer && cc_producer
			= ({ producers & [prod_index] = (PR_Function symb (length app_args) glob_object)}, app_args ++ new_args, ti)
					-!-> ("Produce2cc",symb.symb_name)
		= (producers, [App app : new_args ], ti)
	= (producers, [App app : new_args ], ti)
  where
	get_fun_arity glob_module glob_object ro ti
		| glob_module <> ro.ro_main_dcl_module_n
			# {st_arity, st_context} = ro.ro_imported_funs.[glob_module].[glob_object].ft_type
			= (st_arity+length st_context, ti)
		// for imported functions you have to add ft_arity and length st_context, but for unimported
		// functions fun_arity alone is sufficient
		# ({fun_arity}, ti_fun_defs) = (ti.ti_fun_defs)![glob_object]
		= (fun_arity, { ti & ti_fun_defs=ti_fun_defs })
	
// when two function bodies have fusion with each other this only leads into satisfaction if one body
// fulfills the following sexyness property
// DvA: now that we have producer requirements we can integrate this condition there...
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

:: *RenewState :== (![(BoundVar, Type)], ![BoundVar], !*VarHeap)
// DvA: should be in typesupport?
renewVariables :: ![Expression] !*VarHeap
				-> (![Expression], !RenewState)
renewVariables exprs var_heap
	# (exprs, (new_vars, free_vars, var_heap))
			= mapSt (mapExprSt map_expr preprocess_local_var postprocess_local_var)
					exprs ([], [], var_heap)
	  var_heap
	  		= foldSt (\{var_info_ptr} var_heap -> writeVarInfo var_info_ptr VI_Empty var_heap)
	  				free_vars var_heap
	= (exprs, (new_vars, free_vars, var_heap))
  where
	map_expr :: !Expression !RenewState -> (!Expression, !RenewState)
	map_expr (Var var=:{var_info_ptr, var_name}) (new_vars_accu, free_vars_accu, var_heap)
		# (var_info, var_heap)
				= readPtr var_info_ptr var_heap
		= case var_info of
			VI_Extended _ (VI_Forward new_var)
				-> ( Var new_var
				   , (new_vars_accu, free_vars_accu, var_heap))
			VI_Extended evi=:(EVI_VarType var_type) _
				# (new_var, var_heap)
						= allocate_and_bind_new_var var_name var_info_ptr evi var_heap
				-> ( Var new_var
				   , ( [(new_var, var_type.at_type) : new_vars_accu]
				     , [var:free_vars_accu]
				     , var_heap
				     )
				   )
	map_expr x st = (x, st)

	preprocess_local_var :: !FreeVar !RenewState -> (!FreeVar, !RenewState)
	preprocess_local_var fv=:{fv_name, fv_info_ptr} (new_vars_accu, free_vars_accu, var_heap)
//		# (VI_Extended evi _, var_heap)
//				= readPtr fv_info_ptr var_heap
		# (evi, var_heap)
				= readExtendedVarInfo fv_info_ptr var_heap
		  (new_var, var_heap)
				= allocate_and_bind_new_var fv_name fv_info_ptr evi var_heap
		= ( { fv & fv_info_ptr = new_var.var_info_ptr }
		  , (new_vars_accu, free_vars_accu, var_heap))
	allocate_and_bind_new_var var_name var_info_ptr evi var_heap
		# (new_info_ptr, var_heap)
				= newPtr (VI_Extended evi VI_Empty) var_heap
		  new_var
		  		= { var_name = var_name, var_info_ptr = new_info_ptr, var_expr_ptr = nilPtr }
		  var_heap
		  		= writeVarInfo var_info_ptr (VI_Forward new_var) var_heap
		= (new_var, var_heap)
	postprocess_local_var :: !FreeVar !RenewState -> RenewState
	postprocess_local_var {fv_info_ptr} (a, b, var_heap)
		= (a, b, writeVarInfo fv_info_ptr VI_Empty var_heap)
	
//@ ExprSt ops

mapExprSt f map_free_var postprocess_free_var expr st
	:== map_expr_st expr st
where
	map_expr_st expr=:(Var bound_var) st
		= f expr st
	map_expr_st (App app=:{app_args}) st
		# (app_args, st) = mapSt map_expr_st app_args st
		= f (App { app & app_args = app_args }) st
	map_expr_st (Let lad=:{let_lazy_binds, let_strict_binds, let_expr}) st
		# (lazy_free_vars, st)
				= mapSt (\{lb_dst} st -> map_free_var lb_dst st) let_lazy_binds st
		  (strict_free_vars, st)
				= mapSt (\{lb_dst} st -> map_free_var lb_dst st) let_strict_binds st
		  (lazy_rhss, st)
		  		= mapSt (\{lb_src} st -> map_expr_st lb_src st) let_lazy_binds st
		  (strict_rhss, st)
		  		= mapSt (\{lb_src} st -> map_expr_st lb_src st) let_strict_binds st
		  (let_expr, st)
		  		= map_expr_st let_expr st
		  st	= foldSt (\{lb_dst} st -> postprocess_free_var lb_dst st) let_lazy_binds st
		  st	= foldSt (\{lb_dst} st -> postprocess_free_var lb_dst st) let_strict_binds st
		  expr	= Let { lad
		  			& let_lazy_binds	= add_let_binds lazy_free_vars lazy_rhss let_lazy_binds
		  			, let_strict_binds	= add_let_binds strict_free_vars strict_rhss let_strict_binds
		  			, let_expr			= let_expr
					}
		= f expr st
	map_expr_st (Selection a expr b) st
		# (expr, st) = map_expr_st expr st
		= f (Selection a expr b) st

foldrExprSt f expr st :== foldr_expr_st expr st
  where
	foldr_expr_st expr=:(Var _) st
		= f expr st
	foldr_expr_st app=:(App {app_args}) st
		= f app (foldSt foldr_expr_st app_args st)
	foldr_expr_st lad=:(Let {let_lazy_binds, let_strict_binds, let_expr}) st
		# st
		  		= foldSt (\{lb_src} st -> foldr_expr_st lb_src st) let_lazy_binds st
		  st
		  		= foldSt (\{lb_src} st -> foldr_expr_st lb_src st) let_strict_binds st
		  st
		  		= f let_expr st
		= f lad st
	foldr_expr_st sel=:(Selection a expr b) st
		= f sel (foldr_expr_st expr st)

add_let_binds :: [FreeVar] [Expression] [LetBind] -> [LetBind]
add_let_binds free_vars rhss original_binds
	= [{ original_bind & lb_dst = lb_dst, lb_src = lb_src}
		\\ lb_dst <- free_vars & lb_src <- rhss & original_bind <- original_binds]

//@	transformGroups

::	ImportedConstructors	:== [Global Index]
::	ImportedFunctions		:== [Global Index]
::	ImportedTypes			:== {#{# CheckedTypeDef}}

transformGroups :: !CleanupInfo !Int !Int !*{! Group} !*{#FunDef} !*{!.ConsClasses} !{# CommonDefs}  !{# {# FunType} }
		!*ImportedTypes !ImportedConstructors !*TypeDefInfos !*VarHeap !*TypeHeaps !*ExpressionHeap !Bool
			-> (!*{! Group}, !*{#FunDef}, !*ImportedTypes, !ImportedConstructors, !*VarHeap, !*TypeHeaps, !*ExpressionHeap, !*{!ConsClasses})
transformGroups cleanup_info main_dcl_module_n stdStrictLists_module_n groups fun_defs cons_args common_defs imported_funs
		imported_types collected_imports type_def_infos var_heap type_heaps symbol_heap compile_with_fusion
	#! nr_of_funs = size fun_defs
	# initial_ti =
				{ ti_fun_defs		= fun_defs
				, ti_instances		= createArray nr_of_funs II_Empty
				, ti_cons_args		= cons_args
				, ti_new_functions	= []
				, ti_fun_heap		= newHeap
				, ti_var_heap		= var_heap
				, ti_symbol_heap	= symbol_heap
				, ti_type_heaps		= type_heaps
				, ti_type_def_infos	= type_def_infos
				, ti_next_fun_nr	= nr_of_funs
				, ti_cleanup_info	= cleanup_info
				, ti_recursion_introduced	= No
				}	
	# (groups, imported_types, collected_imports, ti)
		= transform_groups 0 groups common_defs imported_funs imported_types collected_imports initial_ti
//	  {ti_fun_defs,ti_new_functions,ti_var_heap,ti_symbol_heap,ti_fun_heap,ti_next_fun_nr,ti_type_heaps,ti_cleanup_info} = ti
	  (groups, new_fun_defs, imported_types, collected_imports, type_heaps, var_heap) 
	  		= foldSt (add_new_function_to_group common_defs ti.ti_fun_heap) ti.ti_new_functions
	  				(groups, [], imported_types, collected_imports, ti.ti_type_heaps, ti.ti_var_heap)
	  symbol_heap = foldSt cleanup_attributes ti.ti_cleanup_info ti.ti_symbol_heap
	  fun_defs = { fundef \\ fundef <- [ fundef \\ fundef <-: ti.ti_fun_defs ] ++ new_fun_defs }
	= (groups, fun_defs, imported_types, collected_imports,	var_heap, type_heaps, symbol_heap, ti.ti_cons_args)
  where
	transform_groups group_nr groups common_defs imported_funs imported_types collected_imports ti
		| group_nr < size groups
			# (group, groups) = groups![group_nr]
			# {group_members} = group
			# (ti_fun_defs, imported_types, collected_imports, ti_type_heaps, ti_var_heap) 
					= foldSt (convert_function_type common_defs) group_members
							(ti.ti_fun_defs, imported_types, collected_imports, ti.ti_type_heaps, ti.ti_var_heap)
			# ti = { ti & ti_fun_defs = ti_fun_defs, ti_type_heaps = ti_type_heaps, ti_var_heap = ti_var_heap }
			# ti = foldSt (transform_function common_defs imported_funs) group_members ti
			# ti = reannotate_producers (group_members -!-> ("reannotate_producers",group_nr)) ti
			= transform_groups (inc  group_nr) groups common_defs imported_funs imported_types collected_imports ti
			= (groups, imported_types, collected_imports, ti)

	transform_function common_defs imported_funs fun ti=:{ti_fun_defs, ti_var_heap}
		# (fun_def, ti_fun_defs) = ti_fun_defs![fun]
		  (Yes {st_args}) = fun_def.fun_type
		  {fun_body = TransformedBody tb} = fun_def
		  ti_var_heap = fold2St (\{fv_info_ptr} a_type ti_var_heap
									-> setExtendedVarInfo fv_info_ptr (EVI_VarType a_type) ti_var_heap)
								tb.tb_args st_args ti_var_heap
		  ro_fun = fun_def_to_symb_ident fun fun_def
		  ro =	{ ro_imported_funs				= imported_funs
				, ro_common_defs 				= common_defs
				, ro_root_case_mode				= get_root_case_mode tb
				, ro_fun_root					= ro_fun
				, ro_fun_case					= ro_fun
				, ro_fun_args					= tb.tb_args
				, ro_main_dcl_module_n			= main_dcl_module_n
				, ro_transform_fusion			= compile_with_fusion
				, ro_stdStrictLists_module_n	= stdStrictLists_module_n
				}
		  (fun_rhs, ti) = transform tb.tb_rhs ro { ti & ti_fun_defs = ti_fun_defs, ti_var_heap = ti_var_heap }
		= { ti & ti_fun_defs = {ti.ti_fun_defs & [fun] = { fun_def & fun_body = TransformedBody { tb & tb_rhs = fun_rhs }}}}
	  where
		fun_def_to_symb_ident fun_index {fun_symb}
			= { symb_name=fun_symb, symb_kind=SK_Function {glob_object=fun_index, glob_module=main_dcl_module_n } }

		get_root_case_mode {tb_rhs=Case _}	= RootCase
		get_root_case_mode _ 				= NotRootCase

	reannotate_producers group_members ti
		// determine if safe group
		# (safe,ti) = safe_producers group_members group_members ti
		| safe
			// if safe mark all members as safe
			= foldSt mark_producer_safe group_members ti
		= ti
	
	safe_producers group_members [] ti
		= (True,ti)
	safe_producers group_members [fun:funs] ti
		// look for occurrence of group_members in safe argument position of fun RHS
		// i.e. linearity ok && ...
		#! prs	=
			{ prs_group				= group_members
			, prs_cons_args 		= ti.ti_cons_args
			, prs_main_dcl_module_n	= main_dcl_module_n
			, prs_fun_heap			= ti.ti_fun_heap
			}
		# (fun_def, ti)	= ti!ti_fun_defs.[fun]
		  {fun_body		= TransformedBody tb} = fun_def
		  fun_body		= tb.tb_rhs
		# (safe,prs)	= producerRequirements fun_body prs
		// put back prs info into ti?
		| safe -!-> ("producerRequirements",fun_def.fun_symb,safe)
						= safe_producers group_members funs ti
		= (safe,ti)
	
	mark_producer_safe fun ti
		// update cc_prod for fun
		#!	ti_cons_args = {ti.ti_cons_args & [fun].cc_producer = pIsSafe}
			ti = {ti & ti_cons_args = ti_cons_args}
		= ti
// ... DvA		

	add_new_function_to_group ::  !{# CommonDefs} !FunctionHeap  !FunctionInfoPtr
				!(!*{! Group}, ![FunDef], !*ImportedTypes, !ImportedConstructors, !*TypeHeaps, !*VarHeap)
					-> (!*{! Group}, ![FunDef], !*ImportedTypes, !ImportedConstructors, !*TypeHeaps, !*VarHeap)
	add_new_function_to_group common_defs fun_heap fun_ptr (groups, fun_defs, imported_types, collected_imports, type_heaps, var_heap)
		# (FI_Function {gf_fun_def,gf_fun_index}) = sreadPtr fun_ptr fun_heap
		  {fun_type = Yes ft=:{st_args,st_result}, fun_info = {fi_group_index,fi_properties}} = gf_fun_def
		  (_,(st_result,st_args), {ets_type_defs, ets_collected_conses, ets_type_heaps, ets_var_heap})
		  		= expandSynTypes (fi_properties bitand FI_HasTypeSpec == 0) common_defs (st_result,st_args)
				  		{ ets_type_defs = imported_types, ets_collected_conses = collected_imports, ets_type_heaps = type_heaps, ets_var_heap = var_heap,
				  		  ets_main_dcl_module_n=main_dcl_module_n }
		# ft = { ft &  st_result = st_result, st_args = st_args }
		# (group, groups) = groups![fi_group_index]
		= ({ groups & [fi_group_index] = { group & group_members = [gf_fun_index : group.group_members]} },
				[ { gf_fun_def & fun_type = Yes ft} : fun_defs],
					ets_type_defs, ets_collected_conses, ets_type_heaps, ets_var_heap)
	
	convert_function_type common_defs fun_index (fun_defs, imported_types, collected_imports, type_heaps, var_heap)
		# (fun_def=:{fun_type = Yes fun_type, fun_info = {fi_properties}}, fun_defs)
					= fun_defs![fun_index]
		  rem_annot	= fi_properties bitand FI_HasTypeSpec == 0
		  (fun_type, imported_types, collected_imports, type_heaps, var_heap)
		  		= convertSymbolType rem_annot common_defs fun_type main_dcl_module_n imported_types collected_imports type_heaps var_heap
		  fun_def	= { fun_def & fun_type = Yes fun_type }
		  fun_defs	= { fun_defs & [fun_index] = fun_def }
		= (fun_defs, imported_types, collected_imports, type_heaps, var_heap)

//@ convertSymbolType

convertSymbolType :: !Bool !{# CommonDefs} !SymbolType !Int !*ImportedTypes !ImportedConstructors !*TypeHeaps !*VarHeap 
	-> (!SymbolType, !*ImportedTypes, !ImportedConstructors, !*TypeHeaps, !*VarHeap)
convertSymbolType  rem_annots common_defs st main_dcl_module_n imported_types collected_imports type_heaps var_heap
	# ets	=
				{ ets_type_defs			= imported_types
				, ets_collected_conses	= collected_imports
				, ets_type_heaps		= type_heaps
				, ets_var_heap			= var_heap
				, ets_main_dcl_module_n	= main_dcl_module_n 
				}	
	# {st_args,st_result,st_context,st_args_strictness}
										= st
//	# (st, {ets_type_defs, ets_collected_conses, ets_type_heaps, ets_var_heap})
//										= expandSynTypesInSymbolType rem_annots common_defs st ets
	# (_,(st_args,st_result), ets)		= expandSynTypes rem_annots common_defs (st_args,st_result) ets
	  new_st_args						= addTypesOfDictionaries common_defs st_context st_args
	  new_st_arity						= length new_st_args
	  st	=
	  			{ st
	  			& st_args				= new_st_args
	  			, st_result				= st_result
	  			, st_arity				= new_st_arity
	  			, st_args_strictness	= insert_n_strictness_values_at_beginning (new_st_arity-length st_args) st_args_strictness
	  			, st_context			= []
	  			}
	# {ets_type_defs, ets_collected_conses, ets_type_heaps, ets_var_heap}
										= ets
	= (st, ets_type_defs, ets_collected_conses, ets_type_heaps, ets_var_heap)

/*
expandSynTypesInSymbolType rem_annots common_defs st=:{st_args,st_args_strictness,st_result,st_context} ets
	# (_,(st_args,st_result), ets) = expandSynTypes rem_annots common_defs (st_args,st_result) ets
	  new_st_args = addTypesOfDictionaries common_defs st_context st_args
	  new_st_arity = length new_st_args
	  new_st_args_strictness = insert_n_strictness_values_at_beginning (new_st_arity-length st_args) st_args_strictness
	= ({st & st_args = new_st_args, st_args_strictness = new_st_args_strictness, st_result = st_result, st_arity = new_st_arity, st_context = [] }, ets)
*/	
::	ExpandTypeState =
	{	ets_type_defs			:: !.{#{#CheckedTypeDef}}
	,	ets_collected_conses	:: !ImportedConstructors
	,	ets_type_heaps			:: !.TypeHeaps
	,	ets_var_heap			:: !.VarHeap
	,	ets_main_dcl_module_n :: !Int
	}

//@	addTypesOfDictionaries

addTypesOfDictionaries :: !{#CommonDefs} ![TypeContext] ![AType] -> [AType]
addTypesOfDictionaries common_defs type_contexts type_args
	= mapAppend (add_types_of_dictionary common_defs) type_contexts type_args
where
	add_types_of_dictionary common_defs {tc_class = TCGeneric {gtc_dictionary={glob_module,glob_object={ds_ident,ds_index}}}, tc_types}

		/*
			AA HACK:
			Generic classes are always generated locally, 
			and therefore the their dictionaries are also generated localy. 
			Overloaded functions in DCL modules can have generic context restrictions, i.e. they will 
			get generic class dictionaries. 
			Problem: DCL function types refer to ICL type defs of dictionaries.
			Solution: plug a dummy dictinary type, defined in StdGeneric.
			It is possible because all generic class have one class argument and one member.
		*/  
		# dict_type_symb = MakeTypeSymbIdent { glob_object = ds_index, glob_module = glob_module } ds_ident 1
		# type_arg = { at_attribute = TA_Multi, at_type=hd tc_types }
		= {at_attribute = TA_Multi, at_type = TA dict_type_symb [type_arg]}

	add_types_of_dictionary common_defs {tc_class = TCClass {glob_module, glob_object={ds_index,ds_ident}}, tc_types}
		# {class_arity, class_dictionary={ds_ident,ds_index}, class_cons_vars}
				= common_defs.[glob_module].com_class_defs.[ds_index]
		# dict_type_symb
		  		= 	MakeTypeSymbIdent { glob_object = ds_index, glob_module = glob_module } ds_ident class_arity
		=  { at_attribute = TA_Multi, /* at_annotation = AN_Strict, */ at_type = TA dict_type_symb (
//				map (\type -> { at_attribute = TA_Multi, at_annotation = AN_None, at_type = type }) tc_types) }
				fst (mapSt 	(\type class_cons_vars
								-> let at_attribute = if (lowest_bit class_cons_vars) TA_MultiOfPropagatingConsVar TA_Multi
							   		in ( { at_attribute = at_attribute, at_type = type },
						   				class_cons_vars>>1)
						   	)
						  	tc_types
						  	class_cons_vars))}


lowest_bit int :== int bitand 1 <> 0

//@ expandSynTypes

class expandSynTypes a :: !Bool !{# CommonDefs} !a !*ExpandTypeState -> (!Bool,!a, !*ExpandTypeState)

instance expandSynTypes Type
where
	expandSynTypes rem_annots common_defs type=:(arg_type --> res_type) ets
		# (changed,(arg_type, res_type), ets) = expandSynTypes rem_annots common_defs (arg_type, res_type) ets
		| changed
			= (True,arg_type --> res_type, ets)
			= (False,type, ets)
	expandSynTypes rem_annots common_defs type=:(TB _) ets
		= (False,type, ets)
	expandSynTypes rem_annots common_defs type=:(cons_var :@: types) ets
		# (changed,types, ets) = expandSynTypes rem_annots common_defs types ets
		| changed
			= (True,cons_var :@: types, ets)
			= (False,type, ets)
	expandSynTypes rem_annots common_defs type=:(TA type_symb types) ets
		= expand_syn_types_in_TA rem_annots common_defs type TA_Multi ets
	expandSynTypes rem_annots common_defs type=:(TAS type_symb types _) ets
		= expand_syn_types_in_TA rem_annots common_defs type TA_Multi ets
// Sjaak 240801 ...
	expandSynTypes rem_annots common_defs tfa_type=:(TFA vars type) ets
		# (changed,type, ets) = expandSynTypes rem_annots common_defs type ets
		| changed
			= (True,TFA vars type, ets)
			= (False,tfa_type, ets)
	expandSynTypes rem_annots common_defs tfa_type=:(TST atvs st=:{st_args, st_result}) ets
		# (changed, (st_args, st_result), ets) = expandSynTypes rem_annots common_defs (st_args, st_result) ets	
		| changed
			= (True, TST atvs {st & st_args = st_args, st_result = st_result}, ets)
			= (False, tfa_type, ets)			
// ... Sjaak
	expandSynTypes rem_annots common_defs type ets
		= (False,type, ets)

instance expandSynTypes [a] | expandSynTypes a
where
	expandSynTypes rem_annots common_defs [] ets
		= (False,[],ets)
	expandSynTypes rem_annots common_defs t=:[type:types] ets
		# (changed_type,type,ets) = expandSynTypes rem_annots common_defs type ets
		# (changed_types,types,ets) = expandSynTypes rem_annots common_defs types ets
		| changed_type || changed_types
			= (True,[type:types],ets)
			= (False,t,ets)

instance expandSynTypes (a,b) | expandSynTypes a & expandSynTypes b
where
	expandSynTypes rem_annots common_defs (type1,type2) ets
		# (changed_type1,type1,ets) = expandSynTypes rem_annots common_defs type1 ets
		# (changed_type2,type2,ets) = expandSynTypes rem_annots common_defs type2 ets
		= (changed_type1 || changed_type2,(type1,type2),ets)

instance expandSynTypes AType
where
	expandSynTypes rem_annots common_defs atype ets
		= expand_syn_types_in_a_type rem_annots common_defs atype ets
	where
		expand_syn_types_in_a_type rem_annots common_defs atype=:{at_type = at_type=: TA type_symb types,at_attribute} ets
			# (changed,at_type, ets) = expand_syn_types_in_TA rem_annots common_defs at_type at_attribute ets
			| changed
				= (True,{ atype & at_type = at_type }, ets)
				= (False,atype,ets)
		expand_syn_types_in_a_type rem_annots common_defs atype=:{at_type = at_type=: TAS type_symb types _,at_attribute} ets
			# (changed,at_type, ets) = expand_syn_types_in_TA rem_annots common_defs at_type at_attribute ets
			| changed
				= (True,{ atype & at_type = at_type }, ets)
				= (False,atype,ets)
		expand_syn_types_in_a_type rem_annots common_defs atype ets
			# (changed,at_type, ets) = expandSynTypes rem_annots common_defs atype.at_type ets
			| changed
				= (True,{ atype & at_type = at_type }, ets)
				= (False,atype,ets)

expand_syn_types_in_TA rem_annots common_defs ta_type attribute ets=:{ets_type_defs}
	# (glob_object,glob_module,types)	= case ta_type of
		(TA type_symb=:{type_index={glob_object,glob_module},type_name} types)				-> (glob_object,glob_module,types)
		(TAS type_symb=:{type_index={glob_object,glob_module},type_name} types strictness)	-> (glob_object,glob_module,types)
	# ({td_rhs,td_name,td_args,td_attribute},ets_type_defs) = ets_type_defs![glob_module].[glob_object]
	  ets = { ets & ets_type_defs = ets_type_defs }
	= case td_rhs of
		SynType rhs_type
			# (type,ets_type_heaps) = bind_and_substitute_before_expand types td_args td_attribute rhs_type rem_annots attribute ets.ets_type_heaps
			# (_,type,ets) = expandSynTypes rem_annots common_defs type { ets & ets_type_heaps = ets_type_heaps }
			-> (True,type,ets)
		_
			# (changed,types, ets) = expandSynTypes rem_annots common_defs types ets
			# ta_type = if changed
							( case ta_type of
								TA  type_symb _				-> TA  type_symb types
								TAS type_symb _ strictness	-> TAS type_symb types strictness
							) ta_type
			| glob_module == ets.ets_main_dcl_module_n
				-> (changed,ta_type, ets)
				-> (changed,ta_type, collect_imported_constructors common_defs glob_module td_rhs ets)
/*
expand_syn_types_in_TA rem_annots common_defs ta_type attribute ets=:{ets_type_defs}
	# ({td_rhs,td_name,td_args,td_attribute},ets_type_defs) = ets_type_defs![glob_module].[glob_object]
	  ets = { ets & ets_type_defs = ets_type_defs }
	= case td_rhs of
		SynType rhs_type
			# (type,ets_type_heaps) = bind_and_substitute_before_expand types td_args td_attribute rhs_type rem_annots attribute ets.ets_type_heaps
			# (_,type,ets) = expandSynTypes rem_annots common_defs type { ets & ets_type_heaps = ets_type_heaps }
			-> (True,type,ets)
		_
			# (changed,types, ets) = expandSynTypes rem_annots common_defs types ets
			# ta_type = if changed (TAS type_symb types strictness) ta_type
			| glob_module == ets.ets_main_dcl_module_n
				-> (changed,ta_type, ets)
				-> (changed,ta_type, collect_imported_constructors common_defs glob_module td_rhs ets)
*/
where
	bind_and_substitute_before_expand types td_args td_attribute rhs_type rem_annots attribute ets_type_heaps
		# ets_type_heaps = bind_attr td_attribute attribute ets_type_heaps
		  ets_type_heaps = (fold2St bind_var_and_attr td_args types ets_type_heaps)
		  (_, type, ets_type_heaps) = substitute_rhs rem_annots rhs_type.at_type ets_type_heaps
		= (type, ets_type_heaps)
		where
			bind_var_and_attr {	atv_attribute = TA_Var {av_info_ptr},  atv_variable = {tv_info_ptr} } {at_attribute,at_type} type_heaps=:{th_vars,th_attrs}
				= { type_heaps & th_vars = th_vars <:= (tv_info_ptr, TVI_Type at_type), th_attrs = th_attrs <:= (av_info_ptr, AVI_Attr at_attribute) }
			bind_var_and_attr { atv_variable  = {tv_info_ptr}} {at_type} type_heaps=:{th_vars}
				= { type_heaps & th_vars = th_vars <:= (tv_info_ptr, TVI_Type at_type) }
	
			bind_attr (TA_Var {av_info_ptr}) attribute type_heaps=:{th_attrs}
				= { type_heaps & th_attrs = th_attrs <:= (av_info_ptr, AVI_Attr attribute) }
			bind_attr _ attribute type_heaps
				= type_heaps
	
			substitute_rhs rem_annots rhs_type type_heaps
				| rem_annots
					# (_, rhs_type) = removeAnnotations rhs_type
				  	= substitute rhs_type type_heaps
				  	= substitute rhs_type type_heaps

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
	where
		has_been_collected VI_Used				= True
		has_been_collected (VI_ExpandedType _)	= True
		has_been_collected _					= False

//@	freeVariables

::	FreeVarInfo =
	{	fvi_var_heap	:: !.VarHeap
	,	fvi_expr_heap	:: !.ExpressionHeap
	,	fvi_variables	:: ![BoundVar]
	,	fvi_expr_ptrs	:: ![ExprInfoPtr]
	}

class freeVariables expr ::  !expr !*FreeVarInfo -> *FreeVarInfo

instance freeVariables [a] | freeVariables a
where
	freeVariables list fvi
		= foldSt freeVariables list fvi

instance freeVariables LetBind
where
	freeVariables {lb_src} fvi
		= freeVariables lb_src fvi

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

//XXX
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
		  (fvi_variables, fvi_var_heap) = removeLocalVariables [lb_dst \\ {lb_dst} <- let_binds] fvi_variables [] fvi_var_heap		
		  (unbound_variables, fvi_var_heap) = determineGlobalVariables fvi_variables fvi_var_heap
		  (fvi_variables, fvi_var_heap) = restoreVariables removed_variables fvi_variables fvi_var_heap
		  (let_info, fvi_expr_heap) = readPtr let_info_ptr fvi_expr_heap
		= { fvi & fvi_variables = fvi_variables
		  , fvi_var_heap = fvi_var_heap
		  , fvi_expr_heap = fvi_expr_heap
		  , fvi_expr_ptrs = [let_info_ptr : fvi_expr_ptrs]
		  }
	freeVariables (Case kees) fvi
		= freeVariablesOfCase kees fvi
	where
		freeVariablesOfCase {case_expr,case_guards,case_default, case_info_ptr} fvi=:{fvi_variables, fvi_var_heap}
			# (removed_variables, fvi_var_heap) = removeVariables fvi_variables fvi_var_heap
			  fvi = free_variables_of_guards case_guards { fvi & fvi_variables = [], fvi_var_heap = fvi_var_heap }
			  {fvi_expr_heap, fvi_variables, fvi_var_heap, fvi_expr_ptrs} = freeVariables case_default fvi
			  (unbound_variables, fvi_var_heap) = determineGlobalVariables fvi_variables fvi_var_heap
			  (fvi_variables, fvi_var_heap) = restoreVariables removed_variables fvi_variables fvi_var_heap
			  (case_info, fvi_expr_heap) = readPtr case_info_ptr fvi_expr_heap
			= freeVariables case_expr { fvi & fvi_variables = fvi_variables, fvi_var_heap = fvi_var_heap,
					fvi_expr_heap = set_aci_free_vars_info_case unbound_variables case_info_ptr fvi_expr_heap,
					fvi_expr_ptrs = [case_info_ptr : fvi_expr_ptrs] }
		where
			free_variables_of_guards (AlgebraicPatterns _ alg_patterns) fvi
				= foldSt free_variables_of_alg_pattern alg_patterns fvi
			free_variables_of_guards (BasicPatterns _ basic_patterns) fvi
				= foldSt free_variables_of_basic_pattern basic_patterns fvi
			where
				free_variables_of_basic_pattern {bp_expr} fvi
					= freeVariables bp_expr fvi
			free_variables_of_guards (OverloadedListPatterns _ _ alg_patterns) fvi
				= foldSt free_variables_of_alg_pattern alg_patterns fvi
		
			free_variables_of_alg_pattern {ap_vars, ap_expr} fvi=:{fvi_variables}
				# fvi = freeVariables ap_expr { fvi & fvi_variables = [] }
				  (fvi_variables, fvi_var_heap) = removeLocalVariables ap_vars fvi.fvi_variables fvi_variables fvi.fvi_var_heap
				= { fvi & fvi_var_heap = fvi_var_heap, fvi_variables = fvi_variables }
		
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
	freeVariables (MatchExpr _ expr) fvi
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

determineGlobalVariables global_variables var_heap
	= foldSt determine_global_variable global_variables ([], var_heap)
where		
	determine_global_variable {var_info_ptr} (global_variables, var_heap)
		# (VI_UsedVar v_name, var_heap) = readVarInfo var_info_ptr var_heap
		= ([{var_name = v_name, var_info_ptr = var_info_ptr, var_expr_ptr = nilPtr} : global_variables], var_heap)

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

/*
isYes (Yes _) = True
isYes _ = False
*/

//@ producerRequirements

:: PRState =
	{ prs_group				:: ![Int]
	, prs_cons_args 		:: !.{!ConsClasses}
	, prs_main_dcl_module_n	:: !Int
	, prs_fun_heap			:: !.FunctionHeap
	}

class producerRequirements a
	:: !a !*PRState -> *(!Bool,!*PRState)

instance producerRequirements [a] | producerRequirements a where
	producerRequirements [] prs
		= (True,prs)
	producerRequirements [x:xs] prs
		# (safe,prs)	= producerRequirements x prs
		| safe			= producerRequirements xs prs
						= (safe,prs)

instance producerRequirements Expression where
	producerRequirements (Var var) prs
		= (True,prs)
	producerRequirements (App {app_symb={symb_kind=(SK_Constructor _)},app_args}) prs
		= producerRequirements app_args prs
	producerRequirements (App {app_symb,app_args}) prs
		// look up consumer class for app_symb args
		#! (maybe_ca,prs)	= retrieve_consumer_args app_symb prs
		// need to check for recursive call in safe arg...
		= case maybe_ca of
			No			// assuming that for functions that have no consumer info no unfolding will occur
						// note that this means that generated functions must be visible this way...
						-> (True,prs)
			Yes ca		// for each arg:
						// if safe && top of arg is App of group member...
						// else recurse into arg
						-> check_app_arguments ca.cc_args ca.cc_linear_bits app_args prs
	where
		check_app_arguments [cc_arg:cc_args] [cc_linear_bit:cc_bits] [app_arg:app_args] prs
			| cc_arg == cActive && cc_linear_bit
				# (rec,prs)	= is_recursive_app app_arg prs
				| rec		= (False,prs)
				# (safe,prs)= producerRequirements app_arg prs
				| safe		= check_app_arguments cc_args cc_bits app_args prs
							= (safe,prs)
			# (safe,prs)	= producerRequirements app_arg prs
			| safe			= check_app_arguments cc_args cc_bits app_args prs
							= (safe,prs)
		check_app_arguments _ _ _ prs
			= (True,prs)
		
		is_recursive_app (App {app_symb}) prs
			// check if app_symb member of prs_group
			# {symb_kind}	= app_symb
			| is_SK_Function_or_SK_LocalMacroFunction symb_kind
			#! main_dcl_module_n	= prs.prs_main_dcl_module_n
			# { glob_module, glob_object }
				= case symb_kind of
					SK_Function global_index -> global_index
					SK_LocalMacroFunction index -> { glob_module = main_dcl_module_n, glob_object = index }
			| glob_module <> main_dcl_module_n
				= (False,prs)
			#! rec = isMember glob_object prs.prs_group
			= (rec,prs)
		is_recursive_app _ prs
			= (False,prs)

	producerRequirements (fun_expr @ exprs) prs
		// recurse
		# (safe,prs)	= producerRequirements fun_expr prs
		| safe			= producerRequirements exprs prs
						= (safe,prs)
	producerRequirements (Let {let_strict_binds,let_lazy_binds,let_expr}) prs
		// watch out for function shadowing by 'let' binds
		// recurse into binding exprs
		// continue with 'in' body
		= (False,prs)
	producerRequirements (Case {case_expr,case_guards,case_default,case_ident}) prs
		// watch out for function shadowing by guards or case ident
		// check case_expr
		# (safe,prs)	= producerRequirements case_expr prs
		| not safe		= (safe,prs)
		// check case_guards
		# (safe,prs)	= producerRequirements case_guards prs
		| not safe		= (safe,prs)
		// check case_default
		# (safe,prs)	= producerRequirements case_default prs
		| not safe		= (safe,prs)
		= (True,prs)
	producerRequirements (Selection _ _ _) prs
		// ...
		= (False,prs)
	producerRequirements (Update _ _ _) prs
		// ...
		= (False,prs)
	producerRequirements (RecordUpdate _ expr exprs) prs
		// ...
		# (safe,prs)	= producerRequirements expr prs
		| safe			= producerFieldRequirements exprs prs
						= (safe,prs)
	where
		producerFieldRequirements [] prs
			= (True,prs)
		producerFieldRequirements [{bind_src}:fields] prs
			# (safe,prs)	= producerRequirements bind_src prs
			| safe			= producerFieldRequirements fields prs
							= (safe,prs)
	producerRequirements (TupleSelect _ _ expr) prs
		= producerRequirements expr prs
	producerRequirements (BasicExpr _) prs
		= (True,prs)
	producerRequirements (AnyCodeExpr _ _ _) prs
		= (False,prs)
	producerRequirements (ABCCodeExpr _ _) prs
		= (False,prs)
	producerRequirements (MatchExpr _ _) prs
		// what's this?
		= (False,prs)
	producerRequirements (DynamicExpr _) prs
		// what's this?
		= (False,prs)
	producerRequirements (TypeCodeExpression _) prs
		// what's this?
		= (False,prs)
	producerRequirements (EE) prs
		// what's this?
		= (False,prs)
	producerRequirements (NoBind var) prs
		// what's this?
		= (False,prs)
	producerRequirements expr prs
		= abort ("producerRequirements " ---> expr)

instance producerRequirements (Optional a) | producerRequirements a where
	producerRequirements (Yes x) prs
		= producerRequirements x prs
	producerRequirements No prs
		= (True,prs)

instance producerRequirements CasePatterns where
	producerRequirements (AlgebraicPatterns index patterns) prs
		// name shadowing...
		# (safe,prs)	= producerRequirements patterns prs
		= (safe,prs)
	producerRequirements (BasicPatterns type patterns) prs
		// name shadowing...
		# (safe,prs)	= producerRequirements patterns prs
		= (safe,prs)
	producerRequirements (OverloadedListPatterns _ _ _) prs
		//...disallow for now...
		= (False,prs)
	producerRequirements (DynamicPatterns patterns) prs
		//...disallow for now...
		= (False,prs)
	producerRequirements NoPattern prs
		= (True,prs)

instance producerRequirements AlgebraicPattern where
	producerRequirements {ap_expr} prs
		// name shadowing...
		= producerRequirements ap_expr prs

instance producerRequirements BasicPattern where
	producerRequirements {bp_expr} prs
		// name shadowing...
		= producerRequirements bp_expr prs

//@ fun_def & cons_arg getters...

get_fun_def :: !SymbKind !Int !u:{#FunDef} !*FunctionHeap -> (!FunDef, !u:{#FunDef}, !*FunctionHeap)
get_fun_def (SK_Function {glob_module, glob_object}) main_dcl_module_n fun_defs fun_heap
	| glob_module<>main_dcl_module_n
		= abort "sanity check 2 failed in module trans"
	# (fun_def, fun_defs) = fun_defs![glob_object]
	= (fun_def, fun_defs, fun_heap)
get_fun_def (SK_LocalMacroFunction glob_object) main_dcl_module_n fun_defs fun_heap
	# (fun_def, fun_defs) = fun_defs![glob_object]
	= (fun_def, fun_defs, fun_heap)
get_fun_def (SK_GeneratedFunction fun_ptr _) main_dcl_module_n fun_defs fun_heap
	# (FI_Function {gf_fun_def}, fun_heap) = readPtr fun_ptr fun_heap
	= (gf_fun_def, fun_defs, fun_heap)
		
get_fun_def_and_cons_args :: !SymbKind !v:{!ConsClasses} !u:{# FunDef} !*FunctionHeap -> (!FunDef, !ConsClasses, !w:{!ConsClasses}, !u:{# FunDef}, !*FunctionHeap), [v <= w]
get_fun_def_and_cons_args (SK_Function {glob_object}) cons_args fun_defs fun_heap
//	| glob_object >= size fun_defs
//		= abort "get_fun_def_and_cons_args:SK_Function"
	# (fun_def, fun_defs) = fun_defs![glob_object]
	# (fun_args, cons_args) = cons_args![glob_object]
	= (fun_def, fun_args, cons_args, fun_defs, fun_heap)
get_fun_def_and_cons_args (SK_LocalMacroFunction glob_object) cons_args fun_defs fun_heap
//	| glob_object >= size fun_defs
//		= abort "get_fun_def_and_cons_args:SK_LocalMacroFunction"
	# (fun_def, fun_defs) = fun_defs![glob_object]
	# (fun_args, cons_args) = cons_args![glob_object]
	= (fun_def, fun_args, cons_args, fun_defs, fun_heap)
get_fun_def_and_cons_args (SK_GeneratedFunction fun_info_ptr fun_index) cons_args fun_defs fun_heap
	| fun_index < size fun_defs
		# (fun_def, fun_defs) = fun_defs![fun_index]
//		| fun_index >= size cons_args
//			= abort "get_fun_def_and_cons_args:cons_args"
		# (fun_args, cons_args) = cons_args![fun_index]
		= (fun_def, fun_args, cons_args, fun_defs, fun_heap)
	# (FI_Function {gf_fun_def, gf_cons_args}, fun_heap) = readPtr fun_info_ptr fun_heap
	= (gf_fun_def, gf_cons_args, cons_args, fun_defs, fun_heap)

retrieve_consumer_args :: !SymbIdent !u:PRState -> (!Optional ConsClasses, !u:PRState)
retrieve_consumer_args si=:{symb_kind} prs=:{prs_cons_args, prs_main_dcl_module_n}
	# (prs_size, prs_cons_args) = usize prs_cons_args
	  prs = {prs & prs_cons_args = prs_cons_args}
	= case symb_kind of
		SK_Function {glob_module, glob_object}
			| glob_module == prs_main_dcl_module_n && glob_object < prs_size//size prs_cons_args
				# (cons_args,prs) = prs!prs_cons_args.[glob_object]
				-> (Yes cons_args,prs)
			-> (No,prs) -!-> ("r_c_a",si)
		SK_LocalMacroFunction glob_object
			| glob_object < prs_size//size prs_cons_args
				# (cons_args,prs) = prs!prs_cons_args.[glob_object]
				-> (Yes cons_args,prs)
			-> (No,prs) -!-> ("r_c_a",si)
		SK_GeneratedFunction fun_ptr fun_index
			| fun_index < prs_size//size prs_cons_args
				# (cons_args,prs) = prs!prs_cons_args.[fun_index]
				-> (Yes cons_args,prs)
			# (FI_Function {gf_cons_args}, fun_heap)	= readPtr fun_ptr prs.prs_fun_heap
			# prs										= {prs & prs_fun_heap = fun_heap}
			-> (Yes gf_cons_args,prs)
//		SK_Constructor cons_index
		sk -> (No -!-> ("Unexpected symbol kind: ", si, sk),prs)

//@ <<<

instance <<< RootCaseMode where
	(<<<) file mode = case mode of NotRootCase -> file <<< "NotRootCase"; RootCase -> file <<< "RootCase"; RootCaseOfZombie -> file <<< "RootCaseOfZombie";

/*
instance <<< InstanceInfo
where
	(<<<) file (II_Node prods _ left right) = file <<< left <<< prods <<< right 
	(<<<) file II_Empty = file 
*/	

// XXX	
instance <<< Producer
where
	(<<<) file (PR_Function symbol _ index)
		= file <<< "(F)" <<< symbol.symb_name
	(<<<) file (PR_GeneratedFunction symbol _ index)
		= file <<< "(G)" <<< symbol.symb_name <<< index
	(<<<) file PR_Empty = file <<< 'E'
	(<<<) file (PR_Class app vars type) = file <<< "(Class(" <<< App app<<<","<<< type <<< "))"
	(<<<) file (PR_Curried {symb_name, symb_kind} _) = file <<< "(Curried)" <<< symb_name <<< symb_kind
	(<<<) file _ = file

instance <<< SymbKind
where
	(<<<) file (SK_Function gi) = file <<< "(SK_Function)" <<< gi
	(<<<) file (SK_LocalMacroFunction gi) = file <<< gi
	(<<<) file (SK_OverloadedFunction gi) = file <<< "(SK_OverloadedFunction)" <<< gi
	(<<<) file (SK_Constructor gi) = file <<< gi
	(<<<) file (SK_DclMacro gi) = file <<< gi
	(<<<) file (SK_IclMacro gi) = file <<< gi
	(<<<) file (SK_GeneratedFunction _ gi) = file <<< "(SK_GeneratedFunction)" <<< gi
	(<<<) file _ = file
	
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

instance <<< SymbIdent
where
	(<<<) file symb=:{symb_kind = SK_Function symb_index }
		= file <<< symb.symb_name <<<  '@' <<< symb_index
	(<<<) file symb=:{symb_kind = SK_LocalMacroFunction symb_index }
		= file <<< symb.symb_name <<<  '@' <<< symb_index
	(<<<) file symb=:{symb_kind = SK_GeneratedFunction _ symb_index }
		= file <<< symb.symb_name <<<  '@' <<< symb_index
	(<<<) file symb=:{symb_kind = SK_OverloadedFunction symb_index }
		= file <<< symb.symb_name <<<  "[o]@" <<< symb_index
	(<<<) file symb
		= file <<< symb.symb_name 

instance <<< {!Type}
where
	(<<<) file subst
		= file <<< "{"<<<[s\\s<-:subst] <<< "}\n"
