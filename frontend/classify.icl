/*
	module owner: Diederik van Arkel
*/
implementation module classify

SwitchMultimatchClassification multi no_multi	:== multi

import syntax, checksupport, transform

::	CleanupInfo :== [ExprInfoPtr]

setExtendedExprInfo :: !ExprInfoPtr !ExtendedExprInfo !*ExpressionHeap -> *ExpressionHeap
setExtendedExprInfo expr_info_ptr extension expr_info_heap
	# (expr_info, expr_info_heap) = readPtr expr_info_ptr expr_info_heap
	= case expr_info of
		EI_Extended _ ei
			-> expr_info_heap <:= (expr_info_ptr, EI_Extended extension ei)
		ei	-> expr_info_heap <:= (expr_info_ptr, EI_Extended extension ei)
		
is_nil_cons_or_decons_of_UList_or_UTSList glob_object glob_module imported_funs
	:== not (isEmpty imported_funs.[glob_module].[glob_object].ft_type.st_context);

/*
 *	ANALYSIS: only determines consumerClass; producerClasses are determined after each group is transformed.
 */

IsAVariable cons_class	:== cons_class >= 0

combineClasses :: !ConsClass !ConsClass -> ConsClass
combineClasses cc1 cc2
	| IsAVariable cc1
		= CAccumulating
	| IsAVariable cc2
		= CAccumulating
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

determine_classification :: !ConsClasses !.ConsClassSubst -> ConsClasses
determine_classification cc class_subst
	# (cc_size, cc_args) = mapAndLength (skip_indirections class_subst) cc.cc_args
	= { cc & cc_size = cc_size, cc_args = cc_args }
where
	mapAndLength f [x : xs]
		#! x = f x
		   (length, xs) = mapAndLength f xs
		=  (inc length, [x : xs])
	mapAndLength f []
		= (0, [])
	
	skip_indirections subst cc
		| IsAVariable cc
			= skip_indirections subst subst.[cc]
			= cc

//@ Consumer Analysis datatypes...

:: RefCounts	:== {#Int}

::	*AnalyseInfo =
	{	ai_var_heap						:: !*VarHeap
	,	ai_cons_class					:: !*{!ConsClasses}
	,	ai_cur_ref_counts				:: !*RefCounts // for each variable 0,1 or 2
	,	ai_class_subst					:: !*ConsClassSubst
	,	ai_next_var						:: !Int
	,	ai_next_var_of_fun				:: !Int
	,	ai_cases_of_vars_for_function	:: ![Case]
	,	ai_fun_heap						:: !*FunctionHeap
	,	ai_def_ref_counts				:: !RefCounts
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

CUnused					:== -1
CPassive   				:== -2
CActive					:== -3
CAccumulating   		:== -4
CVarOfMultimatchCase	:== -5

/*
	NOTE: ordering of above values is relevant since unification
	is defined later as:
	
	combine_cons_constants :: !ConsClass !ConsClass -> ConsClass
	combine_cons_constants cc1 cc2
		= min cc1 cc2
*/

::	ConsClassSubst	:== {# ConsClass}

cNope			:== -1

/*
	The argument classification (i.e. 'accumulating', 'active' or 'passive') of consumers
	is represented by a negative integer value.
	Positive classifications are used to identify variables.
	Unification of classifications is done on-the-fly
*/

:: ConsumerAnalysisRO = ConsumerAnalysisRO !ConsumerAnalysisRORecord;

:: ConsumerAnalysisRORecord =
	{ common_defs				:: !{# CommonDefs}
	, imported_funs				:: !{#{#FunType}}
	, main_dcl_module_n			:: !Int
	, stdStrictLists_module_n	:: !Int
	}

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
				-> abort ("consumerRequirements [BoundVar] " ---> (var_name))

instance consumerRequirements Expression where
	consumerRequirements (Var var) common_defs ai
		= consumerRequirements var common_defs ai
	consumerRequirements (App app) common_defs ai
		= consumerRequirements app common_defs ai
	consumerRequirements (fun_expr @ exprs) common_defs ai
		# (cc_fun, _, ai)			= consumerRequirements fun_expr common_defs ai
		  ai						= aiUnifyClassifications CActive cc_fun ai
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
		= (CPassive, False, ai)
	consumerRequirements (MatchExpr _ expr) common_defs ai
		= consumerRequirements expr common_defs ai
	consumerRequirements (Selection _ expr selectors) common_defs ai
		# (cc, _, ai) = consumerRequirements expr common_defs ai
		  ai = aiUnifyClassifications CActive cc ai
		  ai = requirementsOfSelectors selectors common_defs ai
		= (CPassive, False, ai)
	consumerRequirements (Update expr1 selectors expr2) common_defs ai
		# (cc, _, ai) = consumerRequirements expr1 common_defs ai
		  ai = requirementsOfSelectors selectors common_defs ai
		  (cc, _, ai) = consumerRequirements expr2 common_defs ai
		= (CPassive, False, ai)
	consumerRequirements (RecordUpdate cons_symbol expression expressions) common_defs ai
		# (cc, _, ai) = consumerRequirements expression common_defs ai
		  (cc, _, ai) = consumerRequirements expressions common_defs ai
		= (CPassive, False, ai)
	consumerRequirements (TupleSelect tuple_symbol arg_nr expr) common_defs ai
		= consumerRequirements expr common_defs ai
	consumerRequirements (AnyCodeExpr _ _ _) _ ai=:{ai_cur_ref_counts}
		#! s							= size ai_cur_ref_counts
		   twos_array					= createArray s 2
		   ai							= { ai & ai_cur_ref_counts=twos_array }
		= (CPassive, False, ai)
	consumerRequirements (ABCCodeExpr _ _) _ ai=:{ai_cur_ref_counts}
		#! s							= size ai_cur_ref_counts
		   twos_array					= createArray s 2
		   ai							= { ai & ai_cur_ref_counts=twos_array }
		= (CPassive, False, ai)
	consumerRequirements (DynamicExpr dynamic_expr) common_defs ai
		= consumerRequirements dynamic_expr common_defs ai
	consumerRequirements (TypeCodeExpression _) _ ai
		= (CPassive, False, ai)
	consumerRequirements EE _ ai
		= (CPassive, False, ai)
	consumerRequirements (NoBind _) _ ai
		= (CPassive, False, ai)
	consumerRequirements expr _ ai
		= abort ("consumerRequirements [Expression]" ---> expr)

requirementsOfSelectors selectors common_defs ai
	= foldSt (reqs_of_selector common_defs) selectors ai
where
	reqs_of_selector common_defs (ArraySelection _ _ index_expr) ai
		# (_, _, ai) = consumerRequirements index_expr common_defs ai
		= ai
	reqs_of_selector common_defs (DictionarySelection dict_var _ _ index_expr) ai
		# (_, _, ai) = consumerRequirements index_expr common_defs ai
		  (cc_var, _, ai) = consumerRequirements dict_var common_defs ai
		= aiUnifyClassifications CActive cc_var ai
	// record selection missing?!
	reqs_of_selector _ _ ai
		= ai
			
instance consumerRequirements App where
	consumerRequirements {app_symb={symb_kind = SK_Function {glob_module,glob_object},symb_name}, app_args}
			common_defs=:(ConsumerAnalysisRO {main_dcl_module_n,stdStrictLists_module_n,imported_funs})
			ai=:{ai_cons_class}

		| glob_module == main_dcl_module_n
			| glob_object < size ai_cons_class
				#! fun_class = ai_cons_class.[glob_object]
				= reqs_of_args fun_class.cc_args app_args CPassive common_defs ai
				= consumerRequirements app_args common_defs ai

		| glob_module == stdStrictLists_module_n && (not (isEmpty app_args))
				&& is_nil_cons_or_decons_of_UList_or_UTSList glob_object glob_module imported_funs
			# [app_arg:app_args]=app_args;
			# (cc, _, ai) = consumerRequirements app_arg common_defs ai
			# ai = aiUnifyClassifications CActive cc ai
			= consumerRequirements app_args common_defs ai
// SPECIAL...
		# num_specials = case imported_funs.[glob_module].[glob_object].ft_specials of
			(SP_ContextTypes [sp:_])	-> length sp.spec_types
			_	-> 0
		| num_specials > 0 && num_specials <= length app_args
			= activeArgs num_specials app_args common_defs ai
			with
				activeArgs 0 app_args common_defs ai
					= consumerRequirements app_args common_defs ai			// treat remaining args normally...
				activeArgs n [app_arg:app_args] common_defs ai
					# (cc, _, ai)	= consumerRequirements app_arg common_defs ai
					# ai			= aiUnifyClassifications CActive cc ai	// make args for which specials exist active...
					= activeArgs (n-1) app_args common_defs ai
// ...SPECIAL
			= consumerRequirements app_args common_defs ai
	consumerRequirements {app_symb={symb_kind = SK_LocalMacroFunction glob_object,symb_name}, app_args}
			common_defs=:(ConsumerAnalysisRO {main_dcl_module_n})
			ai=:{ai_cons_class}
		| glob_object < size ai_cons_class
			#! fun_class = ai_cons_class.[glob_object]
			= reqs_of_args fun_class.cc_args app_args CPassive common_defs ai
			= consumerRequirements app_args common_defs ai
	
	// new alternative for generated function + reanalysis...
	consumerRequirements {app_symb={symb_kind = SK_GeneratedFunction fun_info_ptr index,symb_name}, app_args}
			common_defs
			ai
		# (FI_Function {gf_cons_args={cc_args,cc_linear_bits}}, ai_fun_heap)
			= readPtr fun_info_ptr ai.ai_fun_heap
		= reqs_of_args cc_args app_args CPassive common_defs {ai & ai_fun_heap = ai_fun_heap}
	
	consumerRequirements {app_args} common_defs ai
		=  not_an_unsafe_pattern (consumerRequirements app_args common_defs ai)


reqs_of_args :: ![ConsClass] !.[Expression] ConsClass ConsumerAnalysisRO !*AnalyseInfo -> *(!ConsClass,!.Bool,!*AnalyseInfo)
reqs_of_args _ [] cumm_arg_class _ ai
	= (cumm_arg_class, False, ai)
reqs_of_args [] _ cumm_arg_class _ ai
	= (cumm_arg_class, False, ai)
reqs_of_args [form_cc : ccs] [arg : args] cumm_arg_class common_defs ai
	# (act_cc, _, ai) = consumerRequirements arg common_defs ai
	  ai = aiUnifyClassifications form_cc act_cc ai
	= reqs_of_args ccs args (combineClasses act_cc cumm_arg_class) common_defs ai
reqs_of_args cc xp _ _ _ = abort "classify:reqs_of_args doesn't match" ---> (cc,xp)

showRefCount msg ai
	:== ai ---> (msg,rc)
where
	{ai_cur_ref_counts} = ai
	
	rc :: String
	rc = {show c \\ c <-: ai_cur_ref_counts}

	show 0 = '0'
	show 1 = '1'
	show 2 = '2'
	show _ = '?'

instance consumerRequirements Case where
	consumerRequirements kees=:{case_expr,case_guards,case_default,case_info_ptr,case_explicit}
				common_defs=:(ConsumerAnalysisRO {common_defs=common_defs_parameter}) ai
		# (cce, _, ai)					= consumerRequirements case_expr common_defs ai
		#! env_counts					= ai.ai_cur_ref_counts
		   (s,env_counts)				= usize env_counts
		   zero_array					= createArray s 0
		   ai							= {ai & ai_cur_ref_counts = zero_array}
		   (ccd, default_is_unsafe, ai)	= consumerRequirements case_default common_defs ai
		#! (context_counts,ai)			= case use_context_default of
											True
												-> ({},{ai & ai_cur_ref_counts = env_counts})
		   									False
		   										-> (ai.ai_def_ref_counts,{ai & ai_def_ref_counts = ai.ai_cur_ref_counts, ai_cur_ref_counts = env_counts})
		# (ccgs, unsafe_bits, ai)		= consumer_requirements_of_guards case_guards common_defs ai
		#  ai							= case use_context_default of
											True
												-> ai
											False
												-> {ai & ai_def_ref_counts = context_counts}
		# (every_constructor_appears_in_safe_pattern, may_be_active)
		  								= inspect_patterns common_defs_parameter has_default case_guards unsafe_bits
		  safe = case_explicit || (has_default && not default_is_unsafe) || every_constructor_appears_in_safe_pattern
		  ai = aiUnifyClassifications (SwitchMultimatchClassification
		  		(if may_be_active CActive CVarOfMultimatchCase) 
		  		CActive)
		  		cce ai
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
						# ai = aiUnifyClassifications CActive cc ai
						-> ai
					OverloadedListPatterns _ decons_expr _
						# (_,_,ai) = consumerRequirements decons_expr common_defs ai
						-> ai
					_
						-> ai
		= (combineClasses ccgs ccd, not safe, ai)
	  where
		has_default					= case case_default of
										  		Yes _ -> True
										  		_ -> False
		use_context_default			= not (case_explicit || has_default)
		
		inspect_patterns common_defs has_default (AlgebraicPatterns {glob_object, glob_module} algebraic_patterns) unsafe_bits
			# type_def						= common_defs.[glob_module].com_type_defs.[glob_object]
			  defined_symbols				= case type_def.td_rhs of
													AlgType defined_symbols		-> defined_symbols
													RecordType {rt_constructor}	-> [rt_constructor]
			  all_constructors				= [ ds_index \\ {ds_index}<-defined_symbols ]
			  pattern_constructors			= [ glob_object.ds_index \\ {ap_symbol={glob_object}}<-algebraic_patterns]	
			  sorted_pattern_constructors	= sort pattern_constructors unsafe_bits
			  all_sorted_constructors		= if (is_sorted all_constructors)
			  										all_constructors
			  										(sortBy (<) all_constructors)
			= ( appearance_loop all_sorted_constructors sorted_pattern_constructors
			  , not (multimatch_loop has_default sorted_pattern_constructors)
			  )
		inspect_patterns common_defs has_default (BasicPatterns BT_Bool basic_patterns) unsafe_bits
			# bools_indices					= [ if bool 1 0 \\ {bp_value=BVB bool}<-basic_patterns ]
			  sorted_pattern_constructors	= sort bools_indices unsafe_bits
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
	# pattern_exprs
			= [ ap_expr \\ {ap_expr}<-patterns]
	  pattern_vars
	  		= flatten [ ap_vars \\ {ap_vars}<-patterns]
	  (ai_next_var, ai_next_var_of_fun, ai_var_heap)
	  		= bindPatternVars pattern_vars ai.ai_next_var ai.ai_next_var_of_fun ai.ai_var_heap
	  ai	= { ai & ai_var_heap=ai_var_heap, ai_next_var=ai_next_var, ai_next_var_of_fun = ai_next_var_of_fun }
	= independentConsumerRequirements pattern_exprs common_defs ai
consumer_requirements_of_guards (BasicPatterns type patterns) common_defs ai
	# pattern_exprs
			= [ bp_expr \\ {bp_expr}<-patterns]
	= independentConsumerRequirements pattern_exprs common_defs ai
consumer_requirements_of_guards (OverloadedListPatterns type _ patterns) common_defs ai
	# pattern_exprs
			= [ ap_expr \\ {ap_expr}<-patterns]
	  pattern_vars
	  		= flatten [ ap_vars \\ {ap_vars}<-patterns]
	  (ai_next_var, ai_next_var_of_fun, ai_var_heap)
	  		= bindPatternVars pattern_vars ai.ai_next_var ai.ai_next_var_of_fun ai.ai_var_heap
	  ai	= { ai & ai_var_heap=ai_var_heap, ai_next_var=ai_next_var, ai_next_var_of_fun = ai_next_var_of_fun }
	= independentConsumerRequirements pattern_exprs common_defs ai
consumer_requirements_of_guards NoPattern common_defs ai
	= independentConsumerRequirements [] common_defs ai

bindPatternVars :: !.[FreeVar] !Int !Int !*VarHeap -> (!Int,!Int,!*VarHeap)
bindPatternVars [fv=:{fv_info_ptr,fv_count} : vars] next_var next_var_of_fun var_heap
	| fv_count > 0
		# var_heap	= writePtr fv_info_ptr (VI_AccVar next_var next_var_of_fun) var_heap
		= bindPatternVars vars (inc next_var) (inc next_var_of_fun) var_heap
	// otherwise
		# var_heap	= writePtr fv_info_ptr (VI_Count 0 False) var_heap
		= bindPatternVars vars next_var next_var_of_fun var_heap
bindPatternVars [] next_var next_var_of_fun var_heap
	= (next_var, next_var_of_fun, var_heap)

independentConsumerRequirements :: !.[Expression] ConsumerAnalysisRO !*AnalyseInfo -> (!Int,.[Bool],!*AnalyseInfo)
independentConsumerRequirements [] common_defs ai=:{ai_cur_ref_counts,ai_def_ref_counts}
	#! s							= size ai_cur_ref_counts
	   unified_ref_counts			= unify_with_default` s ai_cur_ref_counts ai_def_ref_counts
	   ai							= {ai & ai_cur_ref_counts = unified_ref_counts}
	= (CPassive,[],ai)
where
	unify_with_default` 0 accu env
		= accu
	unify_with_default` i accu env
		#! i1			= dec i
		   rca			= accu.[i1]
		   rce			= env.[i1]
		   accu			= { accu & [i1] = unify_counts rca rce }
		= unify_with_default` i1 accu env
	where
		unify_counts 0 x = x
		unify_counts 1 x = if (x==2) 2 (inc x)
		unify_counts 2 x = 2

independentConsumerRequirements [expr:exprs] common_defs ai=:{ai_cur_ref_counts,ai_def_ref_counts}
	#! s							= size ai_cur_ref_counts
	   zero_array					= createArray s 0
	   ai							= { ai & ai_cur_ref_counts=zero_array }

	   (cce, is_unsafe_case, ai)	= consumerRequirements expr common_defs ai
	   cc							= combineClasses cce CPassive
	   r_unsafe_bits				= [is_unsafe_case]

	   pat_counts					= case is_unsafe_case of
	   									True	-> combine_with_default s ai.ai_cur_ref_counts ai_def_ref_counts
	   									False	-> ai.ai_cur_ref_counts
	= case exprs of
		[]			//| size ai.ai_cur_ref_counts <> s || size ai_def_ref_counts <> s -> abort ("("+++toString s+++","+++ toString (size ai.ai_cur_ref_counts) +++","+++toString (size ai_def_ref_counts) +++")")
					#! unified_pat_counts				= unify_with_default s ai.ai_cur_ref_counts ai_def_ref_counts
					   unified_ref_counts				= unify_pattern_accu_with_env s unified_pat_counts ai_cur_ref_counts
					   ai								= { ai & ai_cur_ref_counts=unified_ref_counts }
					-> (cc, r_unsafe_bits, ai)
		_			#! zero_array						= createArray s 0
					   accu								= ai.ai_cur_ref_counts
					   ai								= { ai & ai_cur_ref_counts=zero_array }
					   (accu,cc,r_unsafe_bits,ai)		= foldSt (build_pattern_accu common_defs) exprs (accu,cc,r_unsafe_bits,ai)
					//| size ai.ai_cur_ref_counts <> s || size ai_def_ref_counts <> s -> abort "222"
					#! unified_pat_counts				= unify_with_default s accu ai_def_ref_counts
					   unified_ref_counts				= unify_pattern_accu_with_env s unified_pat_counts ai_cur_ref_counts
					   ai								= { ai & ai_cur_ref_counts=unified_ref_counts }
					-> (cc, reverse r_unsafe_bits, ai)
where
	build_pattern_accu common_defs expr (ref_counts_accu,cc,unsafe_bits_accu,ai)
		# (s,ai) = getSize ai
		#! (cce, is_unsafe_case, ai)	= consumerRequirements expr common_defs ai
		   cc							= combineClasses cce cc
		   unsafe_bits_accu				= [is_unsafe_case:unsafe_bits_accu]

		#! ai_cur_ref_counts`			= ai.ai_cur_ref_counts
		   pat_counts					= case is_unsafe_case of
		   									True	-> combine_with_default s ai_cur_ref_counts` ai_def_ref_counts
		   									False	-> ai_cur_ref_counts`

		   (ref_counts_accu,zero_array)	= unify_pattern_accu_with_pat s ref_counts_accu pat_counts
		   ai							= { ai & ai_cur_ref_counts=zero_array }
		= (ref_counts_accu,cc,unsafe_bits_accu,ai)
	where
		getSize :: !*AnalyseInfo -> (!Int,!*AnalyseInfo)
		getSize ai=:{ai_cur_ref_counts}
			# (s,ai_cur_ref_counts) = usize ai_cur_ref_counts
			= (s,{ ai & ai_cur_ref_counts = ai_cur_ref_counts})

	
	unify_with_default :: !Int !*RefCounts !RefCounts -> *RefCounts
	unify_with_default 0 accu env
		= accu
	unify_with_default i accu env
		#! i1			= dec i
		   rca			= accu.[i1]
		   rce			= env.[i1]
		   accu			= { accu & [i1] = unify_counts rce rca }
		= unify_with_default i1 accu env
	where
		unify_counts 0 x = x
		unify_counts 1 x = if (x==0) 1 x
		unify_counts 2 x = 2

	combine_with_default 0 accu env
		= accu
	combine_with_default i accu env
		#! i1			= dec i
		   rca			= accu.[i1]
		   rce			= env.[i1]
		   accu			= { accu & [i1] = unify_counts rca rce }
		= combine_with_default i1 accu env
	where
		unify_counts 0 x = x
		unify_counts 1 x = if (x==2) 2 (inc x)
		unify_counts 2 x = 2

	unify_pattern_accu_with_env 0 accu env
		= env
	unify_pattern_accu_with_env i accu env
		#! i1			= dec i
		   rca			= accu.[i1]
		   rce			= env.[i1]
		   env			= { env & [i1] = unify_counts rca rce }
		= unify_pattern_accu_with_env i1 accu env
	where
		unify_counts 0 x = x
		unify_counts 1 x = if (x==2) 2 (inc x)
		unify_counts 2 x = 2

	unify_pattern_accu_with_pat :: !Int !*RefCounts !*RefCounts -> (!*RefCounts,!*RefCounts)
	unify_pattern_accu_with_pat 0 accu pat
		= (accu,pat)
	unify_pattern_accu_with_pat i accu pat
		#! i1			= dec i
		   rca			= accu.[i1]
		   rcp			= pat.[i1]
		   accu			= { accu & [i1] = unify_counts rcp rca }
		   pat			= { pat & [i1] = 0 }
		= unify_pattern_accu_with_pat i1 accu pat
	where
		unify_counts 0 x = x
		unify_counts 1 x = if (x==0) 1 x
		unify_counts 2 x = 2

/* old WRONG version...
independentConsumerRequirements exprs common_defs ai=:{ai_cur_ref_counts}
// reference counting happens independently for each pattern expression
	#! s							= size ai_cur_ref_counts
	   zero_array					= createArray s 0
	   (_, cc, r_unsafe_bits ,ai)	= foldSt (independent_consumer_requirements common_defs) exprs (zero_array, CPassive, [], ai)
	= (cc, reverse r_unsafe_bits, ai)
where	
	independent_consumer_requirements common_defs expr (zero_array, cc, unsafe_bits_accu, ai=:{ai_cur_ref_counts})
		#! s							= size ai_cur_ref_counts
		   ai							= { ai & ai_cur_ref_counts=zero_array }
		   (cce, is_unsafe_case, ai)	= consumerRequirements expr common_defs ai
		   (unused, unified_ref_counts)	= unify_ref_count_arrays s ai_cur_ref_counts ai.ai_cur_ref_counts
		   ai							= { ai & ai_cur_ref_counts=unified_ref_counts }
		= ({ unused & [i]=0 \\ i<-[0..s-1]}, combineClasses cce cc, [is_unsafe_case:unsafe_bits_accu], ai)
	unify_ref_count_arrays 0 src1 src2_dest
		= (src1, src2_dest)
	unify_ref_count_arrays i src1 src2_dest
		#! i1			= dec i
		   rc1			= src1.[i1]
		   rc2			= src2_dest.[i1]
		   src2_dest	= { src2_dest & [i1] = unify_ref_counts rc1 rc2 }
		= unify_ref_count_arrays i1 src1 src2_dest

	// unify_ref_counts outer_ref_count ref_count_in_pattern
	unify_ref_counts 0 x = if (x==2) 2 0
	unify_ref_counts 1 x = if (x==0) 1 2
	unify_ref_counts 2 _ = 2
*/
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
		= (CPassive, False, ai)

instance consumerRequirements (!a,!b) | consumerRequirements a & consumerRequirements b where
	consumerRequirements (x, y) common_defs ai
		# (ccx, _, ai) = consumerRequirements x common_defs ai
		  (ccy, _, ai) = consumerRequirements y common_defs ai
		= (combineClasses ccx ccy, False, ai)
		
instance consumerRequirements [a] | consumerRequirements a where
	consumerRequirements [x : xs] common_defs ai
		# (ccx,  _, ai) = consumerRequirements x  common_defs ai
		  (ccxs, _, ai) = consumerRequirements xs common_defs ai
		= (combineClasses ccx ccxs, False, ai)
	consumerRequirements [] _ ai
		= (CPassive, False, ai)

instance consumerRequirements (Bind a b) | consumerRequirements a where
	consumerRequirements {bind_src} common_defs ai
		= consumerRequirements bind_src common_defs ai

//@ Analysis

// determine consumerRequirements for functions
analyseGroups	:: !{# CommonDefs} !{#{#FunType}} !IndexRange !Int !Int !*{! Group} !*{#FunDef} !*VarHeap !*ExpressionHeap 
				-> (!CleanupInfo, !*{! ConsClasses}, !*{! Group}, !*{#FunDef}, !*VarHeap, !*ExpressionHeap)
analyseGroups common_defs imported_funs {ir_from, ir_to} main_dcl_module_n stdStrictLists_module_n groups fun_defs var_heap expr_heap
	#! nr_of_funs	= size fun_defs + ir_from - ir_to /* Sjaak */
	   nr_of_groups	= size groups
	# consumerAnalysisRO=ConsumerAnalysisRO
		{ common_defs				= common_defs
		, imported_funs				= imported_funs
		, main_dcl_module_n			= main_dcl_module_n
		, stdStrictLists_module_n	= stdStrictLists_module_n
		}
	# class_env = createArray nr_of_funs { cc_size = 0, cc_args = [], cc_linear_bits = [], cc_producer=False}
	= iFoldSt (analyse_group consumerAnalysisRO) 0 nr_of_groups
				([], class_env, groups, fun_defs, var_heap, expr_heap)
where	
	analyse_group common_defs group_nr (cleanup_info, class_env, groups, fun_defs, var_heap, expr_heap)
		# ({group_members}, groups)
				= groups![group_nr]

		# (next_var, nr_of_local_vars, var_heap, class_env, fun_defs)
				= foldSt initial_cons_class group_members (0, 0, var_heap, class_env, fun_defs)

		# ai =
						{	ai_var_heap						= var_heap
						, 	ai_cons_class					= class_env
						,	ai_cur_ref_counts				= {}
						,	ai_class_subst					= createArray (next_var + nr_of_local_vars) CPassive
						,	ai_next_var						= next_var
						,	ai_next_var_of_fun				= 0
						,	ai_cases_of_vars_for_function	= []
						,	ai_fun_heap						= newHeap
						,	ai_def_ref_counts				= {}
						}

		# (ai_cases_of_vars_for_group, ai, fun_defs)
				= foldSt (analyse_functions common_defs) group_members ([], ai, fun_defs)

		  class_env
		  		= ai.ai_cons_class
		  class_env
		  		= foldSt (collect_classifications ai.ai_class_subst) group_members class_env
		  (cleanup_info, class_env, fun_defs, var_heap, expr_heap)
				= foldSt set_case_expr_info (flatten ai_cases_of_vars_for_group)
					(cleanup_info, class_env, fun_defs, ai.ai_var_heap, expr_heap)
		= (cleanup_info, class_env, groups, fun_defs, var_heap, expr_heap)
	  where
//initial classification...
		initial_cons_class fun (next_var, nr_of_local_vars, var_heap, class_env, fun_defs)
			# (fun_def, fun_defs)					= fun_defs![fun]
			  (TransformedBody {tb_args})			= fun_def.fun_body
			  
			  nr_of_locals							= length fun_def.fun_info.fi_local_vars
			  nr_of_local_vars						= nr_of_local_vars + nr_of_locals
			  
			# (fresh_vars, next_var, var_heap)
			   										= fresh_variables tb_args 0 next_var var_heap
			# fun_class								= { cc_size = 0, cc_args = fresh_vars, cc_linear_bits=[], cc_producer=False}
			  class_env								= { class_env & [fun] = fun_class}
			= (next_var, nr_of_local_vars, var_heap, class_env, fun_defs)
//determine classification...
		analyse_functions common_defs fun (cfvog_accu, ai, fun_defs)
			#  (fun_def, fun_defs)					= fun_defs![fun]
	 		   (TransformedBody {tb_args, tb_rhs})	= fun_def.fun_body

	 		   nr_of_locals							= length fun_def.fun_info.fi_local_vars
			   nr_of_args							= length tb_args

			   ai = { ai
			   		& ai_cur_ref_counts				= createArray (nr_of_args + nr_of_locals) 0
			   		, ai_def_ref_counts				= createArray (nr_of_args + nr_of_locals) 0
			   		, ai_next_var_of_fun			= nr_of_args 
			   		}
			// classify
			   (_, _, ai)							= consumerRequirements tb_rhs common_defs ai
			// set linearity info based on cur_ref_counts
			#  ai_cur_ref_counts					= ai.ai_cur_ref_counts
			   ai_cons_class						= ai.ai_cons_class
			   (fun_cons_class,ai_cons_class)		= ai_cons_class![fun]
			   linear_bits							= [ ref_count<2 \\ ref_count <-: ai_cur_ref_counts ]
			   fun_cons_class						= { fun_cons_class & cc_linear_bits=linear_bits }
			   cc_args								= add_unused_args fun_cons_class.cc_args ai_cur_ref_counts
			   fun_cons_class						= { fun_cons_class & cc_args = cc_args }
			   ai_cons_class						= {ai_cons_class & [fun] = fun_cons_class}
			   cases_of_vars_for_function			= [(a,fun) \\ a <- ai.ai_cases_of_vars_for_function ]
			   cfvog_accu							= [cases_of_vars_for_function:cfvog_accu]

			   ai = { ai
			   		& ai_cons_class					= ai_cons_class
			   		, ai_cases_of_vars_for_function	= [] 
			   		, ai_cur_ref_counts				= {}
			   		}
			= (cfvog_accu, ai, fun_defs)
//final classification...
		collect_classifications class_subst fun class_env
			# (fun_class, class_env)	= class_env![fun]
			  fun_class					= determine_classification fun_class class_subst
	 		= { class_env & [fun] = fun_class

		set_case_expr_info ({case_expr=case_expr=:(Var {var_info_ptr}), case_guards, case_info_ptr},fun_index)
				(cleanup_acc, class_env, fun_defs, var_heap, expr_heap)
			# (VI_AccVar _ arg_position, var_heap)				= readPtr var_info_ptr var_heap
			  ({cc_size, cc_args, cc_linear_bits},class_env)	= class_env![fun_index]
			  (aci_linearity_of_patterns, var_heap)				= get_linearity_info cc_linear_bits case_guards var_heap
			| arg_position<cc_size && (arg_position>=cc_size || cc_args!!arg_position==CActive) && cc_linear_bits!!arg_position
				// mark non multimatch cases whose case_expr is an active linear function argument
				# aci =
					{ aci_params				= []
					, aci_opt_unfolder			= No
					, aci_free_vars				= No
					, aci_linearity_of_patterns = aci_linearity_of_patterns
					}
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

reanalyseGroups	:: !{# CommonDefs} !{#{#FunType}} !Int !Int ![FunctionInfoPtr]  ![Group] !*{#FunDef} !*VarHeap !*ExpressionHeap !*FunctionHeap !*{!ConsClasses}
				-> (!CleanupInfo, !*{#FunDef}, !*VarHeap, !*ExpressionHeap, !*FunctionHeap, !*{!ConsClasses})
reanalyseGroups common_defs imported_funs main_dcl_module_n stdStrictLists_module_n new_functions
	groups fun_defs var_heap expr_heap fun_heap class_env
	#! nr_of_groups	= size groups
	# consumerAnalysisRO=ConsumerAnalysisRO
		{ common_defs				= common_defs
		, imported_funs				= imported_funs
		, main_dcl_module_n			= main_dcl_module_n
		, stdStrictLists_module_n	= stdStrictLists_module_n
		}
	= foldSt (analyse_group consumerAnalysisRO) groups
				([], fun_defs, var_heap, expr_heap, fun_heap, class_env)
where	
	analyse_group common_defs group (cleanup_info, fun_defs, var_heap, expr_heap, fun_heap, class_env)
		# {group_members}	= group

		# (next_var, nr_of_local_vars, var_heap, class_env, fun_defs, fun_heap)
				= foldSt initial_cons_class group_members (0, 0, var_heap, class_env, fun_defs, fun_heap)

		# ai =
						{	ai_var_heap						= var_heap
						, 	ai_cons_class					= class_env
						,	ai_cur_ref_counts				= {}
						,	ai_class_subst					= createArray (next_var + nr_of_local_vars) CPassive
						,	ai_next_var						= next_var
						,	ai_next_var_of_fun				= 0
						,	ai_cases_of_vars_for_function	= []
						,	ai_fun_heap						= fun_heap
						,	ai_def_ref_counts				= {}
						}

		# (ai_cases_of_vars_for_group, ai, fun_defs)
				= foldSt (analyse_functions common_defs) group_members ([], ai, fun_defs)

		  class_env
		  		= ai.ai_cons_class
		  fun_heap
		  		= ai.ai_fun_heap
		  (class_env,fun_heap)
		  		= foldSt (collect_classifications ai.ai_class_subst) group_members (class_env,fun_heap)
		  (cleanup_info, class_env, fun_defs, var_heap, expr_heap, fun_heap)
				= foldSt set_case_expr_info (flatten ai_cases_of_vars_for_group)
					(cleanup_info, class_env, fun_defs, ai.ai_var_heap, expr_heap, fun_heap)
		= (cleanup_info, fun_defs, var_heap, expr_heap, fun_heap, class_env)
	  where
//initial classification...
		initial_cons_class fun (next_var, nr_of_local_vars, var_heap, class_env, fun_defs, fun_heap)
			# (fun_def, fun_defs, fun_heap)			= get_fun_def fun fun_defs fun_heap
			# (TransformedBody {tb_args,tb_rhs})	= fun_def.fun_body
			  
			  nr_of_locals							= count_locals tb_rhs 0
			  nr_of_local_vars						= nr_of_local_vars + nr_of_locals
			  
			# (fresh_vars, next_var, var_heap)
			   										= fresh_variables tb_args 0 next_var var_heap
			# fun_class								= { cc_size = 0, cc_args = fresh_vars, cc_linear_bits=[], cc_producer=False}
			# (fun_heap,class_env)					= set_fun_class fun fun_class fun_heap class_env
			= (next_var, nr_of_local_vars, var_heap, class_env, fun_defs, fun_heap)


		set_fun_class fun fun_class fun_heap class_env
			| fun < size class_env
				# class_env							= { class_env & [fun] = fun_class}
				= (fun_heap,class_env)

			# (fun_def_ptr,fun_heap)				= lookup_ptr fun new_functions fun_heap
				with
					lookup_ptr fun [] ti_fun_heap = abort "drat"
					lookup_ptr fun [fun_def_ptr:new_functions] ti_fun_heap
						# (FI_Function {gf_fun_index}, ti_fun_heap)
								= readPtr fun_def_ptr ti_fun_heap
						| gf_fun_index == fun
							= (fun_def_ptr, ti_fun_heap)
							= lookup_ptr fun new_functions ti_fun_heap
			# (FI_Function gf, fun_heap)			= readPtr fun_def_ptr fun_heap
			# fun_heap								= writePtr fun_def_ptr (FI_Function {gf & gf_cons_args = fun_class}) fun_heap
			= (fun_heap,class_env)

//determine classification...
		analyse_functions common_defs fun (cfvog_accu, ai, fun_defs)
			#  (fun_def, fun_defs, fun_heap)		= get_fun_def fun fun_defs ai.ai_fun_heap
	 		   ai									= {ai & ai_fun_heap = fun_heap}
	 		   (TransformedBody {tb_args, tb_rhs})	= fun_def.fun_body

			   nr_of_locals							= count_locals tb_rhs 0
			   nr_of_args							= length tb_args

			   ai = { ai
			   		& ai_cur_ref_counts				= createArray (nr_of_args + nr_of_locals) 0
			   		, ai_def_ref_counts				= createArray (nr_of_args + nr_of_locals) 0
			   		, ai_next_var_of_fun			= nr_of_args 
			   		}
			// classify
			   (_, _, ai)							= consumerRequirements tb_rhs common_defs ai
			// set linearity info based on cur_ref_counts
			#  ai_cur_ref_counts					= ai.ai_cur_ref_counts
			   ai_cons_class						= ai.ai_cons_class

			#  fun_heap								= ai.ai_fun_heap
			#  (fun_cons_class,fun_heap,ai_cons_class)	= get_fun_class fun fun_heap ai_cons_class

			   linear_bits							= [ ref_count<2 \\ ref_count <-: ai_cur_ref_counts ]
			   fun_cons_class						= { fun_cons_class & cc_linear_bits=linear_bits }
			   cc_args								= add_unused_args fun_cons_class.cc_args ai_cur_ref_counts
			   fun_cons_class						= { fun_cons_class & cc_args = cc_args }
			#  (fun_heap,ai_cons_class)				= set_fun_class fun fun_cons_class fun_heap ai_cons_class
			   cases_of_vars_for_function			= [(a,fun) \\ a <- ai.ai_cases_of_vars_for_function ]
			   cfvog_accu							= [cases_of_vars_for_function:cfvog_accu]

			   ai = { ai
			   		& ai_cons_class					= ai_cons_class
			   		, ai_cases_of_vars_for_function	= [] 
			   		, ai_cur_ref_counts				= {}
			   		, ai_fun_heap					= fun_heap
			   		}
			= (cfvog_accu, ai, fun_defs)
//final classification...
		collect_classifications class_subst fun (class_env,fun_heap)
			# (fun_class,fun_heap,class_env)	= get_fun_class fun fun_heap class_env
			  fun_class					= determine_classification fun_class class_subst
			# (fun_heap,class_env)		= set_fun_class fun fun_class fun_heap class_env
	 		= (class_env,fun_heap)

		set_case_expr_info ({case_expr=case_expr=:(Var {var_info_ptr}), case_guards, case_info_ptr},fun_index)
				(cleanup_acc, class_env, fun_defs, var_heap, expr_heap, fun_heap)
			# (VI_AccVar _ arg_position, var_heap)				= readPtr var_info_ptr var_heap
			  ({cc_size, cc_args, cc_linear_bits},fun_heap,class_env)	= get_fun_class fun_index fun_heap class_env
			  (aci_linearity_of_patterns, var_heap)				= get_linearity_info cc_linear_bits case_guards var_heap
			| arg_position<cc_size && (arg_position>=cc_size || cc_args!!arg_position==CActive) && cc_linear_bits!!arg_position
				// mark non multimatch cases whose case_expr is an active linear function argument
				# aci =
					{ aci_params				= []
					, aci_opt_unfolder			= No
					, aci_free_vars				= No
					, aci_linearity_of_patterns = aci_linearity_of_patterns
					}
				= ([case_info_ptr:cleanup_acc], class_env, fun_defs, var_heap, 
					setExtendedExprInfo case_info_ptr (EEI_ActiveCase aci) expr_heap, fun_heap)
			= (cleanup_acc, class_env, fun_defs, var_heap, expr_heap, fun_heap)

		get_fun_class fun fun_heap class_env
			| fun < size class_env
				# (fun_cons_class,class_env)		= class_env![fun]
				= (fun_cons_class,fun_heap,class_env)
			# (fun_def_ptr,fun_heap)				= lookup_ptr fun new_functions fun_heap
														with
															lookup_ptr fun [] ti_fun_heap = abort "drat"
															lookup_ptr fun [fun_def_ptr:new_functions] ti_fun_heap
																# (FI_Function {gf_fun_index}, ti_fun_heap)
																		= readPtr fun_def_ptr ti_fun_heap
																| gf_fun_index == fun
																	= (fun_def_ptr, ti_fun_heap)
																	= lookup_ptr fun new_functions ti_fun_heap
			# (FI_Function {gf_cons_args}, fun_heap)		= readPtr fun_def_ptr fun_heap
			= (gf_cons_args, fun_heap, class_env)

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

		get_fun_def fun fun_defs fun_heap
			| fun < size fun_defs
				# (fun_def, fun_defs)						= fun_defs![fun]
				= (fun_def, fun_defs, fun_heap)
			# (fun_def_ptr, fun_heap)			= lookup_ptr fun new_functions fun_heap
				with
					lookup_ptr fun [] ti_fun_heap = abort "drat"
					lookup_ptr fun [fun_def_ptr:new_functions] ti_fun_heap
						# (FI_Function {gf_fun_index}, ti_fun_heap)
								= readPtr fun_def_ptr ti_fun_heap
						| gf_fun_index == fun
							= (fun_def_ptr, ti_fun_heap)
							= lookup_ptr fun new_functions ti_fun_heap
			# (FI_Function {gf_fun_def}, fun_heap)
												= readPtr fun_def_ptr fun_heap
			= (gf_fun_def, fun_defs, fun_heap)

reanalyseFunction
	:: !Int !FunctionInfoPtr !{# CommonDefs} !{#{#FunType}} !Int !Int !*{#FunDef} !*VarHeap !*FunctionHeap !*{!ConsClasses}
	-> *(!ConsClasses,!*{#FunDef},!*VarHeap,!*FunctionHeap,!*{!ConsClasses})
reanalyseFunction fun fun_info_ptr common_defs imported_funs main_dcl_module_n stdStrictLists_module_n fun_defs var_heap fun_heap class_env
	# consumerAnalysisRO=ConsumerAnalysisRO
		{ common_defs				= common_defs
		, imported_funs				= imported_funs
		, main_dcl_module_n			= main_dcl_module_n
		, stdStrictLists_module_n	= stdStrictLists_module_n
		}

	#  (fifun, fun_heap)					= readPtr fun_info_ptr fun_heap
	   fun_def								= case fifun of
												FI_Function {gf_fun_def}	-> gf_fun_def
												FI_Empty					-> abort "unexpected FI_Empty.\n"

	   ({tb_args, tb_rhs})					= case fun_def.fun_body of
	   											TransformedBody body		-> body
	   											body						-> abort "unexpected non-Transformed body?\n"

	   nr_of_locals							= count_locals tb_rhs 0
	   nr_of_args							= length tb_args

	# (fresh_vars, next_var, var_heap)
	   										= fresh_variables tb_args 0 0 var_heap
	# fun_class								= { cc_size = 0, cc_args = fresh_vars, cc_linear_bits=[], cc_producer=False}

	# (fun_info, fun_heap)					= readPtr fun_info_ptr fun_heap
	# fun_info								= case fun_info of
												FI_Function gf
													-> FI_Function {gf & gf_cons_args = fun_class}
	# fun_heap								= writePtr fun_info_ptr fun_info fun_heap

	# ai =
					{	ai_var_heap						= var_heap
					, 	ai_cons_class					= class_env
					,	ai_cur_ref_counts				= createArray (nr_of_args + nr_of_locals) 0
					,	ai_class_subst					= createArray (nr_of_args + nr_of_locals) CPassive
					,	ai_next_var						= next_var
					,	ai_next_var_of_fun				= nr_of_args
					,	ai_cases_of_vars_for_function	= []
					,	ai_fun_heap						= fun_heap
					,	ai_def_ref_counts				= createArray (nr_of_args + nr_of_locals) 0
					}

	// classify
	#  (_, _, ai)							= consumerRequirements tb_rhs consumerAnalysisRO ai
	// set linearity info based on cur_ref_counts?
	   ai_cur_ref_counts					= ai.ai_cur_ref_counts
	   ai_cons_class						= ai.ai_cons_class
	   fun_cons_class						= determine_classification fun_class ai.ai_class_subst
	   linear_bits							= [ ref_count<2 \\ ref_count <-: ai_cur_ref_counts ]
	   fun_cons_class						= { fun_cons_class & cc_linear_bits=linear_bits }
	   cc_args								= add_unused_args fun_cons_class.cc_args ai_cur_ref_counts
	   fun_cons_class						= { fun_cons_class & cc_args = cc_args }
	   cases_of_vars_for_function			= [(a,fun) \\ a <- ai.ai_cases_of_vars_for_function ]
	// set_case_expr_info cases_of_vars_for_function
	= (fun_cons_class,fun_defs,ai.ai_var_heap,ai.ai_fun_heap,ai_cons_class)

			
fresh_variables [{fv_info_ptr} : vars] arg_position next_var_number var_heap
	# (fresh_vars, last_var_number, var_heap)
			= fresh_variables vars (inc arg_position) (inc next_var_number) var_heap
	  var_heap
	  		= writePtr fv_info_ptr (VI_AccVar next_var_number arg_position) var_heap
	= ([next_var_number : fresh_vars], last_var_number, var_heap)
fresh_variables [] _ next_var_number var_heap
	= ([], next_var_number, var_heap)

// count_locals determines number of local variables...

count_locals (Var _) n
	= n
count_locals (App {app_args}) n
	= foldSt count_locals app_args n
count_locals (fun_expr @ exprs) n
	= foldSt count_locals exprs (count_locals fun_expr n)
count_locals (Let {let_strict_binds,let_lazy_binds,let_expr}) n
	# let_binds	= let_strict_binds ++ let_lazy_binds
	= count_let_bind_locals let_binds (count_locals let_expr n)
count_locals (Case {case_expr,case_guards,case_default}) n
	= count_case_locals case_guards (count_locals case_expr (count_optional_locals case_default n))
count_locals (BasicExpr _) n
	= n
count_locals (MatchExpr _ expr) n
	= count_locals expr n
count_locals (Selection _ expr selectors) n
	= count_selector_locals selectors (count_locals expr n)
count_locals (Update expr1 selectors expr2) n
	# n = count_locals expr1 n
	# n = count_locals expr2 n
	# n = count_selector_locals selectors n
	= n
count_locals (RecordUpdate _ expr exprs) n
	= foldSt count_bind_locals exprs (count_locals expr n)
count_locals (TupleSelect _ _ expr) n
	= count_locals expr n
count_locals (AnyCodeExpr _ _ _) n
	= n
count_locals (ABCCodeExpr _ _) n
	= n
count_locals (DynamicExpr {dyn_expr}) n
	= count_locals dyn_expr n
count_locals (TypeCodeExpression _) n
	= n
count_locals EE n
	= n
count_locals (NoBind _) n
	= n

count_optional_locals (Yes e) n
	= count_locals e n
count_optional_locals No n
	= n

count_bind_locals {bind_src} n
	= count_locals bind_src n

count_let_bind_locals binds n
	= foldSt count_let_bind_locals binds n
where
	count_let_bind_locals {lb_src,lb_dst} n
		| lb_dst.fv_count > 0
			= count_locals lb_src (inc n)
			= n

count_case_locals (AlgebraicPatterns _ patterns) n
	# pattern_exprs		= [ ap_expr \\ {ap_expr} <- patterns ]
	  pattern_vars		= flatten [ ap_vars \\ {ap_vars} <- patterns ]
	= foldSt count_locals pattern_exprs (foldSt count_case_guard_locals pattern_vars n)
count_case_locals (BasicPatterns _ patterns) n
	# pattern_exprs		= [ bp_expr \\ {bp_expr} <- patterns ]
	= foldSt count_locals pattern_exprs n
count_case_locals (OverloadedListPatterns _ _ patterns) n
	# pattern_exprs		= [ ap_expr \\ {ap_expr} <- patterns ]
	  pattern_vars		= flatten [ ap_vars \\ {ap_vars} <- patterns ]
	= foldSt count_locals pattern_exprs (foldSt count_case_guard_locals pattern_vars n)
count_case_locals NoPattern n
	= n

count_case_guard_locals {fv_count} n
	| fv_count > 0
		= inc n
		= n

count_selector_locals selectors n
	= foldSt count_selector_locals selectors n
where
	count_selector_locals (ArraySelection _ _ index_expr) n
		= count_locals index_expr n
	count_selector_locals (DictionarySelection _ _ _ index_expr) n
		= count_locals index_expr n
	// record selection missing?!
	count_selector_locals _ n
		= n

add_unused_args args ref_counts
	= [if (ref_count > 0) arg CUnused \\ arg <- args & ref_count <-: ref_counts]
