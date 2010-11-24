/*
	module owner: Diederik van Arkel
*/
implementation module classify

SwitchMultimatchClassification multi no_multi	:== multi
SwitchNewOld new old							:== new

import syntax, transform
import StdStrictLists

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

:: RefCounts
//	:== {#RefCount}
	:== {RefCount}

:: RefCount	
//	:== Int
//	= RC !Int
//	= RC !Int [[(!FunIndex,!ArgIndex)]]  // (fun_index,arg_index)
	= Par !Int !.[!.RefCount!]
	| Seq !Int !.[!.RefCount!]
	| Dep !FunIndex !ArgIndex

:: FunIndex	:== Int
:: ArgIndex :== Int

replace_global_idx_by_group_idx table rcs
	= {{replace rc \\ rc <-: frcs} \\ frcs <-: rcs}
where
	replace rc
		= case rc of
			Par i d		-> Par i [|replace rc \\ rc <|- d]//(map replace d)
			Seq i d		-> Seq i [|replace rc \\ rc <|- d]//(map replace d)
			Dep f a		-> Dep (get_index f 0 table) a

	get_index f x [] = abort "classify:get_index: no index for function\n"
	get_index f x [t:ts]
		| t == f
			= x
			= get_index f (x+1) ts

Max a m [|]
	= a + m
Max a m [|d:ds]
	| a + m >= 2
		= 2
	# s = score d
	| s > m
		= Max a s ds
		= Max a m ds

Sum a [|]
	= a
Sum a [|d:ds]
	| a >= 2
		= 2
		= Sum (a + score d) ds

score (Par i d)		= Max i 0 d
score (Seq i d)		= Sum i d
score (Dep f a)		= 0

Max` a m [|]
	= a + m
Max` a m [|d:ds]
	| a + m >= 2
		= 2
	# s = score` d
	| s > m
		= Max` a s ds
		= Max` a m ds

Sum` a [|]
	= a
Sum` a [|d:ds]
	| a >= 2
		= 2
		= Sum` (a + score` d) ds

score` (Par i d)	= Max` i 0 d
score` (Seq i d)	= Sum` i d
score` (Dep f a)	= 1

substitute_dep :: ![(!FunIndex,!ArgIndex)] !u:RefCount -> u:RefCount
substitute_dep subs (Par i d)
	= Par i [|substitute_dep subs rc \\ rc <|- d]
substitute_dep subs (Seq i d)
	= Seq i [|substitute_dep subs rc \\ rc <|- d]
substitute_dep subs rc=:(Dep f a)
	| isMember (f,a) subs
		= Seq 1 [|]
		= Dep f a

n_zero_counts n
	:== createArray n (Seq 0 [|])
n_twos_counts n
	:== createArray n (Seq 2 [|])

inc_ref_count :: !RefCount -> RefCount
//inc_ref_count (RC ref_count deps)
//	:== RC (min (ref_count+1) 2) deps
inc_ref_count rc
	= case rc of
		Par i d	-> if (i > 0) (Seq 2 [|]) (Par (i+1) d)
		Seq i d -> if (i > 0) (Seq 2 [|]) (Seq (i+1) d)
		_ -> abort "classify:inc_ref_count: unexpected Dep\n"

add_dep_count :: !(!Int,!Int) !RefCount -> RefCount
//add_dep_count dep (RC ref_count deps)
//	:== RC ref_count (map (\l->[dep:l]) deps)
add_dep_count (fi,ai) rc
	= case rc of
		Par i d	-> Par i [|Dep fi ai:d]
		Seq i d -> Seq i [|Dep fi ai:d]
		_ -> abort "classify:add_dep_count: unexpected Dep\n"

combine_counts :: !RefCounts !RefCounts -> .RefCounts
combine_counts c1 c2
	= {combine rc1 rc2 \\ rc1 <-: c1 & rc2 <-: c2}
where
	combine (Seq 0 [|]) rc2 = rc2
	combine rc1 (Seq 0 [|]) = rc1
	combine (Seq i1 [|]) (Seq i2 l) = Seq (i1+i2) l
	combine (Seq i1 l) (Seq i2 [|]) = Seq (i1+i2) l
	combine rc1 rc2 = Seq 0 [|rc1,rc2]

unify_counts :: !RefCounts !RefCounts -> RefCounts
unify_counts c1 c2
	= {unify rc1 rc2 \\ rc1 <-: c1 & rc2 <-: c2}
where
	unify (Seq 0 [|]) rc2 = rc2
	unify rc1 (Seq 0 [|]) = rc1
	unify rc1 rc2 = Par 0 [|rc1,rc2]

show_counts group_members group_counts
	# (_,group_counts) = foldSt show group_members (0,group_counts)
	= group_counts
where
	show fun (fun_index,group_counts)
		# (fun_counts,group_counts) = group_counts![fun_index]
		= (fun_index+1,group_counts) 
			--->	( fun_index,fun
					, [score rc \\ rc <-: fun_counts]
					, [score` rc \\ rc <-: fun_counts]
					, [is_non_zero rc \\ rc <-: fun_counts]
					, fun_counts
					)

instance <<< [!a!] | <<< a
where
	(<<<) s a = s <<< [e \\ e <|- a]
	
instance <<< {a} | <<< a
where
	(<<<) s a = s <<< [e \\ e <-: a]
	
::	*AnalyseInfo =
	{	ai_var_heap						:: !*VarHeap
	,	ai_cons_class					:: !*{!ConsClasses}
	,	ai_cur_ref_counts				:: !*RefCounts // for each variable 0,1 or 2
	,	ai_class_subst					:: !*ConsClassSubst
	,	ai_next_var						:: !Int
	,	ai_next_var_of_fun				:: !Int
	,	ai_cases_of_vars_for_function	:: ![(!Bool,!Case)]
	,	ai_fun_heap						:: !*FunctionHeap
	,	ai_fun_defs						:: !*{#FunDef}

	,	ai_group_members				:: ![Int]
	,	ai_group_counts					:: !*{!RefCounts}
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

CUnusedLazy				:== -1
CUnusedStrict			:== -2
CPassive   				:== -3
CActive					:== -4
CAccumulating   		:== -5
CVarOfMultimatchCase	:== -6

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
	consumerRequirements {var_ident,var_info_ptr} _ ai=:{ai_var_heap}
		# (var_info, ai_var_heap)	= readPtr var_info_ptr ai_var_heap
		  ai						= {ai & ai_var_heap=ai_var_heap}
		= case var_info of
			VI_AccVar temp_var arg_position
				#! (ref_count,ai)	= ai!ai_cur_ref_counts.[arg_position] 
				   ai				= {ai & ai_cur_ref_counts.[arg_position] = inc_ref_count ref_count}
				-> (temp_var, False, ai)
			_
				-> abort ("consumerRequirements [BoundVar] " ---> (var_ident,var_info_ptr))

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
		# ai						= {ai & ai_next_var = new_next_var, ai_next_var_of_fun = new_ai_next_var_of_fun, ai_var_heap = ai_var_heap}
		# ai						= acc_requirements_of_let_binds let_binds ai_next_var common_defs ai
		= consumerRequirements let_expr common_defs ai
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
		   twos_array					= n_twos_counts s
		   ai							= { ai & ai_cur_ref_counts=twos_array }
		= (CPassive, False, ai)
	consumerRequirements (ABCCodeExpr _ _) _ ai=:{ai_cur_ref_counts}
		#! s							= size ai_cur_ref_counts
		   twos_array					= n_twos_counts s
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
	consumerRequirements (FailExpr _) _ ai
		= (CPassive, False, ai)
	consumerRequirements (DictionariesFunction dictionaries expr expr_type) common_defs ai
		# (new_next_var,new_next_var_of_fun,ai_var_heap) = init_variables dictionaries ai.ai_next_var ai.ai_next_var_of_fun ai.ai_var_heap
		# ai = {ai & ai_next_var=new_next_var,ai_next_var_of_fun=new_next_var_of_fun,ai_var_heap=ai_var_heap}
		= consumerRequirements expr common_defs ai
		where
			init_variables [({fv_info_ptr},_):dictionaries] ai_next_var ai_next_var_of_fun ai_var_heap
				# ai_var_heap = writePtr fv_info_ptr (VI_AccVar ai_next_var ai_next_var_of_fun) ai_var_heap
				= init_variables dictionaries (inc ai_next_var) (inc ai_next_var_of_fun) ai_var_heap
			init_variables [] ai_next_var ai_next_var_of_fun ai_var_heap
				= (ai_next_var,ai_next_var_of_fun,ai_var_heap)
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
	reqs_of_selector common_defs (RecordSelection _ _) ai
		= ai

instance consumerRequirements App where
	consumerRequirements {app_symb={symb_kind = SK_Function {glob_module,glob_object},symb_ident}, app_args}
			common_defs=:(ConsumerAnalysisRO {main_dcl_module_n,stdStrictLists_module_n,imported_funs})
			ai=:{ai_cons_class,ai_group_members}

		| glob_module == main_dcl_module_n
			| glob_object < size ai_cons_class
				# (fun_class, ai) = ai!ai_cons_class.[glob_object]
				| isMember glob_object ai_group_members
					= reqs_of_args glob_object 0 fun_class.cc_args app_args CPassive common_defs ai
				= reqs_of_args (-1) 0 fun_class.cc_args app_args CPassive common_defs ai
			= consumerRequirements app_args common_defs ai

		| glob_module == stdStrictLists_module_n && (not (isEmpty app_args))
				&& is_nil_cons_or_decons_of_UList_or_UTSList glob_object glob_module imported_funs
			# [app_arg:app_args]=app_args
			# (cc, _, ai) = consumerRequirements app_arg common_defs ai
			# ai = aiUnifyClassifications CActive cc ai
			= consumerRequirements app_args common_defs ai
/*
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
*/
// ACTIVATE DICTIONARIES... [SUBSUMES SPECIAL]
		# num_dicts = length imported_funs.[glob_module].[glob_object].ft_type.st_context

		# num_specials = case imported_funs.[glob_module].[glob_object].ft_specials of
			(SP_ContextTypes [sp:_])	-> length sp.spec_types
			_	-> 0
//		# num_dicts = num_dicts ---> ("NUM_DICTS",num_dicts,num_specials)

		| num_dicts > 0 && num_dicts <= length app_args
			= reqs_of_args (-1) 0 (repeatn num_dicts CActive ++ repeatn (imported_funs.[glob_module].[glob_object].ft_arity) CPassive) app_args CPassive common_defs ai
/* wrong version...
			= activeArgs num_dicts app_args common_defs ai
			with
				activeArgs 0 app_args common_defs ai
					= consumerRequirements app_args common_defs ai
				activeArgs n [app_arg:app_args] common_defs ai
					# (cc, _, ai)	= consumerRequirements app_arg common_defs ai
					# ai			= aiUnifyClassifications CActive cc ai
					= activeArgs (n-1) app_args common_defs ai
...*/
// ...ACTIVATE DICTIONARIES
		= consumerRequirements app_args common_defs ai
	consumerRequirements {app_symb={symb_kind = SK_LocalMacroFunction glob_object,symb_ident}, app_args}
			common_defs=:(ConsumerAnalysisRO {main_dcl_module_n})
			ai=:{ai_cons_class,ai_group_members}
		| glob_object < size ai_cons_class
			# (fun_class, ai) = ai!ai_cons_class.[glob_object]
			| isMember glob_object ai_group_members
				= reqs_of_args glob_object 0 fun_class.cc_args app_args CPassive common_defs ai
			= reqs_of_args (-1) 0 fun_class.cc_args app_args CPassive common_defs ai
		= consumerRequirements app_args common_defs ai
	
	// new alternative for generated function + reanalysis...
	consumerRequirements {app_symb={symb_kind = SK_GeneratedFunction fun_info_ptr index,symb_ident}, app_args}
			common_defs
			ai=:{ai_group_members}
		# (FI_Function {gf_cons_args={cc_args,cc_linear_bits},gf_fun_def}, ai_fun_heap)
			= readPtr fun_info_ptr ai.ai_fun_heap
		# ai = {ai & ai_fun_heap = ai_fun_heap}
		| isMember index ai_group_members
			= reqs_of_args index 0 cc_args app_args CPassive common_defs ai
		= reqs_of_args (-1) 0 cc_args app_args CPassive common_defs ai

	consumerRequirements {app_args} common_defs ai
		=  not_an_unsafe_pattern (consumerRequirements app_args common_defs ai)

instance <<< TypeContext
where
	(<<<) file co = file <<< co.tc_class <<< " " <<< co.tc_types <<< " <" <<< co.tc_var <<< '>'

instance <<< (Ptr a)
where
	(<<<) file p = file <<< ptrToInt p

reqs_of_args :: !Int !Int ![ConsClass] !.[Expression] ConsClass ConsumerAnalysisRO !*AnalyseInfo -> *(!ConsClass,!.Bool,!*AnalyseInfo)
reqs_of_args _ _ _ [] cumm_arg_class _ ai
	= (cumm_arg_class, False, ai)
reqs_of_args _ _ [] _ cumm_arg_class _ ai
	= (cumm_arg_class, False, ai)
reqs_of_args fun_idx arg_idx [form_cc : ccs] [Var arg : args] cumm_arg_class common_defs ai
	| fun_idx >= 0
		# (act_cc, _, ai) = consumerRequirements` arg common_defs ai
		  ai = aiUnifyClassifications form_cc act_cc ai
		= reqs_of_args fun_idx (inc arg_idx) ccs args (combineClasses act_cc cumm_arg_class) common_defs ai
where
	consumerRequirements` {var_info_ptr,var_ident} _ ai
		# (var_info, ai_var_heap)	= readPtr var_info_ptr ai.ai_var_heap
		  ai						= { ai & ai_var_heap=ai_var_heap }
		= case var_info of
			VI_AccVar temp_var arg_position
				#! (ref_count,ai)	= ai!ai_cur_ref_counts.[arg_position]
				   ai				= { ai & ai_cur_ref_counts.[arg_position] = add_dep_count (fun_idx,arg_idx) ref_count }
				-> (temp_var, False, ai)
			_
				-> abort ("reqs_of_args [BoundVar] " ---> (var_ident))

reqs_of_args fun_idx arg_idx [form_cc : ccs] [arg : args] cumm_arg_class common_defs ai
	# (act_cc, _, ai) = consumerRequirements arg common_defs ai
	  ai = aiUnifyClassifications form_cc act_cc ai
	= reqs_of_args fun_idx (inc arg_idx) ccs args (combineClasses act_cc cumm_arg_class) common_defs ai
reqs_of_args _ _ cc xp _ _ _ = abort "classify:reqs_of_args doesn't match" ---> (cc,xp)

instance consumerRequirements Case where
	consumerRequirements kees=:{case_expr,case_guards,case_default,case_info_ptr,case_explicit}
				ro=:(ConsumerAnalysisRO {common_defs=common_defs_parameter}) ai=:{ai_cur_ref_counts}
		#  (cce, _, ai)					= consumerRequirements case_expr ro ai
		#! env_counts					= ai.ai_cur_ref_counts
		   (s,env_counts)				= usize env_counts
		   zero_array					= n_zero_counts s
		   ai							= {ai & ai_cur_ref_counts = zero_array}
		   (ccd, default_is_unsafe, ai)	= consumerRequirements case_default ro ai
		# (ccgs, unsafe_bits, guard_counts, ai)
										= consumer_requirements_of_guards case_guards ro ai
		# default_counts				= ai.ai_cur_ref_counts
		# (every_constructor_appears_in_safe_pattern, may_be_active)
		  								= inspect_patterns common_defs_parameter has_default case_guards unsafe_bits
		  ref_counts = combine_pattern_counts has_default case_guards unsafe_bits guard_counts default_counts
		  ref_counts = combine_counts ref_counts env_counts
		  ai = {ai & ai_cur_ref_counts = ref_counts }
		  safe = case_explicit || (has_default && not default_is_unsafe) || every_constructor_appears_in_safe_pattern
		  ai = aiUnifyClassifications (SwitchMultimatchClassification
		  		(if may_be_active CActive CVarOfMultimatchCase) 
		  		CActive)
		  		cce ai
		  ai = case case_expr of
				Var {var_info_ptr}
					| SwitchMultimatchClassification may_be_active True
						-> { ai & ai_cases_of_vars_for_function=[(safe,kees):ai.ai_cases_of_vars_for_function] }
						-> ai
// N-WAY...
//				_	-> ai
				_
					| SwitchMultimatchClassification may_be_active True
						-> { ai & ai_cases_of_vars_for_function=[(safe,kees):ai.ai_cases_of_vars_for_function] }
						-> ai
// ...N-WAY
/*		# ai = case case_guards of
					OverloadedListPatterns (OverloadedList _ _ _ _) decons_expr=:(App {app_symb={symb_kind=SK_Function _},app_args=[app_arg]}) patterns
						// decons_expr will be optimized to a decons_u Selector in transform
						# (cc, _, ai)	= consumerRequirements app_arg ro ai
						# ai = aiUnifyClassifications CActive cc ai
						-> ai
					OverloadedListPatterns _ decons_expr _
						# (_,_,ai) = consumerRequirements decons_expr ro ai
						-> ai
					_
						-> ai
*/
		# ai = handle_overloaded_list_patterns case_guards ai
		= (combineClasses ccgs ccd, not safe, ai)
	  where
		handle_overloaded_list_patterns
					(OverloadedListPatterns (OverloadedList _ _ _ _) decons_expr=:(App {app_symb={symb_kind=SK_Function _},app_args=[app_arg]}) patterns)
					ai
						// decons_expr will be optimized to a decons_u Selector in transform
						# (cc, _, ai)	= consumerRequirements app_arg ro ai
						# ai = aiUnifyClassifications CActive cc ai
						= ai
		handle_overloaded_list_patterns
					(OverloadedListPatterns _ decons_expr _) ai
						# (_,_,ai) = consumerRequirements decons_expr ro ai
						= ai
		handle_overloaded_list_patterns
					_ ai
						= ai
		
		has_default					= case case_default of
										  		Yes _ -> True
										  		_ -> False

		inspect_patterns :: !{#.CommonDefs} !.Bool !.CasePatterns ![.Bool] -> (!.Bool,!Bool)
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

combine_pattern_counts :: !.Bool !.CasePatterns ![.Bool] ![RefCounts] !RefCounts -> *RefCounts
combine_pattern_counts has_default patterns unsafe_bits guard_counts default_counts
	| not ok_pattern_type
		= n_twos_counts (size default_counts)
	# sorted_pattern_constructors`	= sort3 pattern_constructors unsafe_bits guard_counts
	# initial_count					= case has_default of
	  										True	-> default_counts
	  										_		-> zero_array
	= count_loop default_counts initial_count sorted_pattern_constructors`
	
where
	ok_pattern_type = case patterns of
		(AlgebraicPatterns _ _)
			-> True
		(BasicPatterns BT_Bool _)
			-> True
		(BasicPatterns BT_Int _)
			-> True
//		(BasicPatterns (BT_String _) basic_patterns)
//			-> [ string \\ {bp_value=BVS string}<-basic_patterns ] ---> ("BasicPatterns String")
		(OverloadedListPatterns overloaded_list _ algebraic_patterns)
			-> True
		_ -> False //---> ("not ok_pattern_type",patterns)
	pattern_constructors = case patterns of
		(AlgebraicPatterns {glob_object, glob_module} algebraic_patterns)
			-> [ glob_object.ds_index \\ {ap_symbol={glob_object}}<-algebraic_patterns] //---> ("AlgebraicPatterns")
		(BasicPatterns BT_Bool basic_patterns)
			-> [ if bool 1 0 \\ {bp_value=BVB bool}<-basic_patterns ] //---> ("BasicPatterns Bool")
		(BasicPatterns BT_Int basic_patterns)
			-> [ int \\ {bp_value=BVInt int}<-basic_patterns ] //---> ("BasicPatterns Int")
//		(BasicPatterns (BT_String _) basic_patterns)
//			-> [ string \\ {bp_value=BVS string}<-basic_patterns ] ---> ("BasicPatterns String")
		(OverloadedListPatterns overloaded_list _ algebraic_patterns)
			-> [ glob_object.ds_index \\ {ap_symbol={glob_object}}<-algebraic_patterns] //---> ("OverloadedListPatterns")
		_ -> abort "unsupported?!" ---> ("pattern_constructors",patterns) //[]	// ???

	count_size					= size default_counts
	zero_array					= n_zero_counts count_size

	sort3 :: !.[Int] !.[a] !.[b] -> .[(!Int,!Int,!a,!b)]
	sort3 constr_indices unsafe_bits counts
		= sortBy smaller (zip4 constr_indices [0..] unsafe_bits counts)
	  where
		smaller (i1,si1,_,_) (i2,si2,_,_)
			| i1<i2		= True
			| i1>i2		= False
						= si1<si2
		zip4 [h1:t1] [h2:t2] [h3:t3] [h4:t4]
			= [(h1,h2,h3,h4):zip4 t1 t2 t3 t4]
		zip4 _ _ _ _
			= []

	count_loop :: !RefCounts !RefCounts ![(!Int,!Int,!Bool,!RefCounts)] -> *RefCounts
	count_loop default_counts unified_counts []
		= {e \\ e <-: unified_counts}
	count_loop default_counts unified_counts [(c_index,p_index,unsafe,counts):patterns]
		# (same,next)	= splitWhile (\(ds_index,_,_,_)->ds_index==c_index) patterns
		# ccount= case unsafe of
					True 	-> count_constructor default_counts counts same
					_		-> counts
		= count_loop default_counts (unify_counts ccount unified_counts) next
	where
		splitWhile :: !(a -> .Bool) !u:[a] -> (!.[a],!v:[a]), [u <= v];
		splitWhile f []
			= ([],[])
		splitWhile f cons=:[a:x]
			| f a
				# (t,d)	= splitWhile f x
				= ([a:t],d)
				= ([],cons)
	
	count_constructor :: !RefCounts !RefCounts ![(!Int,!Int,!Bool,!RefCounts)] -> RefCounts
	count_constructor default_counts combined_counts []
		= combine_counts combined_counts default_counts
	count_constructor default_counts combined_counts [(_,_,unsafe,counts):patterns]
		| unsafe
			= count_constructor default_counts (combine_counts combined_counts counts) patterns
			= combine_counts combined_counts counts

//consumer_requirements_of_guards :: !CasePatterns ConsumerAnalysisRO !*AnalyseInfo -> (!Int,.[Bool],!*AnalyseInfo)
consumer_requirements_of_guards :: !.CasePatterns !.ConsumerAnalysisRO !*AnalyseInfo -> *(!Int,!.[Bool],![RefCounts],!*AnalyseInfo)
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

independentConsumerRequirements :: !.[Expression] !ConsumerAnalysisRO !*AnalyseInfo -> (!ConsClass,!.[Bool],![RefCounts],!*AnalyseInfo)
independentConsumerRequirements exprs info ai
	# ref_counts					= ai.ai_cur_ref_counts
	# (count_size,ref_counts)		= usize ref_counts
	# zero_array					= n_zero_counts count_size
	# (counts_unsafe,(cc,ai))		= mapSt cons_reqs exprs (CPassive,{ ai & ai_cur_ref_counts = zero_array})
	# (counts,unsafe)				= unzip counts_unsafe
	= (cc,unsafe,counts,{ ai & ai_cur_ref_counts = ref_counts})
where
	cons_reqs :: !Expression !*(!.Int,!*AnalyseInfo) -> *(!.(!RefCounts,!Bool),!*(!Int,!*AnalyseInfo))
	cons_reqs expr (cc,ai)
		# (cce, unsafe, ai)		= consumerRequirements expr info ai
		# cc					= combineClasses cce cc
		# ref_counts			= ai.ai_cur_ref_counts
		# count_size			= size ref_counts
		# zero_array			= n_zero_counts count_size
		= ((ref_counts,unsafe),(cc, { ai & ai_cur_ref_counts=zero_array }))

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
						,	ai_fun_defs						= fun_defs
						,	ai_group_members				= group_members
						,	ai_group_counts					= createArray (length group_members) {}
//						,	ai_def_ref_counts				= {}
						}

		# (_,ai_cases_of_vars_for_group, rev_strictness_for_group, ai)
				= foldSt (analyse_functions common_defs) group_members (0, [], [], ai)
		  ai_group_counts = ai.ai_group_counts
		  ai_group_counts = replace_global_idx_by_group_idx group_members ai_group_counts
		#!
		  ai_group_counts = substitute_dep_counts group_members ai_group_counts
		  ai	= { ai & ai_group_counts =  ai_group_counts}

		# (_,_,ai)
		  		= foldSt set_linearity_info_for_group group_members (0,reverse rev_strictness_for_group,ai)
		  class_env = ai.ai_cons_class
		  class_env
		  		= foldSt (collect_classifications ai.ai_class_subst) group_members class_env
		  (cleanup_info, class_env, fun_defs, var_heap, expr_heap)
				= foldSt (set_case_expr_info ai.ai_class_subst) (flatten ai_cases_of_vars_for_group)
					(cleanup_info, class_env, ai.ai_fun_defs, ai.ai_var_heap, expr_heap)
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
		analyse_functions common_defs fun (fun_index, cfvog_accu, strictness_accu, ai)
			#  (fun_def, ai)						= ai!ai_fun_defs.[fun]
	 		   (TransformedBody {tb_args, tb_rhs})	= fun_def.fun_body

	 		   nr_of_locals							= length fun_def.fun_info.fi_local_vars
			   nr_of_args							= length tb_args

			   ai = { ai
			   		& ai_cur_ref_counts				= n_zero_counts (nr_of_args + nr_of_locals)
			   		, ai_next_var_of_fun			= nr_of_args 
			   		}
//	 		   												---> ("analyse",fun_def)
			// classify
			   (_, _, ai)							= consumerRequirements tb_rhs common_defs ai
			#  ai_cur_ref_counts					= ai.ai_cur_ref_counts
			#  cases_of_vars_for_function			= [(a,fun) \\ a <- ai.ai_cases_of_vars_for_function ]
			   cfvog_accu							= [cases_of_vars_for_function:cfvog_accu]
			   strictness_accu						= [get_strictness_list fun_def:strictness_accu]
			   											with
			   												get_strictness_list {fun_type = Yes {st_args_strictness}}
			   													= st_args_strictness

			   ai = { ai
			   		& ai_cases_of_vars_for_function	= [] 
			   		, ai_cur_ref_counts				= {}
			   		, ai_group_counts				= {ai.ai_group_counts & [fun_index] = ai_cur_ref_counts}
			   		}
			= (fun_index + 1, cfvog_accu, strictness_accu, ai)
		set_linearity_info_for_group fun (fun_index,group_strictness,ai=:{ai_cons_class,ai_group_counts})
			#  (fun_cons_class,ai_cons_class)		= ai_cons_class![fun]
			   (fun_ref_counts,ai_group_counts)		= ai_group_counts![fun_index]
			   fun_cons_class						= set_linearity_info fun fun_index fun_cons_class fun_ref_counts group_strictness
			   ai_cons_class						= {ai_cons_class & [fun] = fun_cons_class}
			   ai									= {ai & ai_cons_class = ai_cons_class, ai_group_counts = ai_group_counts}
			= (fun_index+1,group_strictness,ai)
		set_linearity_info fun fun_index fun_cons_class fun_ref_counts group_strictness
			#  linear_bits							= determine_linear_bits fun_ref_counts
			   fun_cons_class						= { fun_cons_class & cc_linear_bits=linear_bits }
			   cc_args								= add_unused_args fun fun_index fun_cons_class.cc_args fun_ref_counts group_strictness
			   fun_cons_class						= { fun_cons_class & cc_args = cc_args }
			= fun_cons_class
//final classification...
		collect_classifications class_subst fun class_env
			# (fun_class, class_env)	= class_env![fun]
			  fun_class					= determine_classification fun_class class_subst
	 		= { class_env & [fun] = fun_class }

		set_case_expr_info class_subst ((safe,{case_expr=(Var {var_info_ptr}), case_guards, case_info_ptr}),fun_index)
				(cleanup_acc, class_env, fun_defs, var_heap, expr_heap)
			# (VI_AccVar cc arg_position, var_heap)				= readPtr var_info_ptr var_heap
			  ({cc_size, cc_args, cc_linear_bits},class_env)	= class_env![fun_index]
			  (aci_linearity_of_patterns, var_heap)				= get_linearity_info cc_linear_bits case_guards var_heap
			| ((arg_position>=cc_size && CActive==skip_indirections class_subst cc) || (arg_position<cc_size && cc_args!!arg_position==CActive)) && cc_linear_bits!!arg_position
				# aci =
					{ aci_params				= []
					, aci_opt_unfolder			= No
					, aci_free_vars				= No
					, aci_linearity_of_patterns = aci_linearity_of_patterns
					, aci_safe					= safe
					}
				= ([case_info_ptr:cleanup_acc], class_env, fun_defs, var_heap, 
					setExtendedExprInfo case_info_ptr (EEI_ActiveCase aci) expr_heap)
			= (cleanup_acc, class_env, fun_defs, var_heap, expr_heap)
				  where
					skip_indirections subst cc
						| IsAVariable cc
							= skip_indirections subst subst.[cc]
							= cc

// N-WAY...
		set_case_expr_info class_subst ((safe,{case_expr=(App _), case_guards, case_info_ptr}),fun_index)
				(cleanup_acc, class_env, fun_defs, var_heap, expr_heap)
			# ({cc_size, cc_args, cc_linear_bits},class_env)	= class_env![fun_index]
			  (aci_linearity_of_patterns, var_heap)				= get_linearity_info cc_linear_bits case_guards var_heap
			# aci =
				{ aci_params				= []
				, aci_opt_unfolder			= No
				, aci_free_vars				= No
				, aci_linearity_of_patterns = aci_linearity_of_patterns
				, aci_safe					= safe
				}
			= ([case_info_ptr:cleanup_acc], class_env, fun_defs, var_heap, 
				setExtendedExprInfo case_info_ptr (EEI_ActiveCase aci) expr_heap)
		set_case_expr_info class_subst ((safe,{case_expr=(_ @ _), case_guards, case_info_ptr}),fun_index)
				(cleanup_acc, class_env, fun_defs, var_heap, expr_heap)
			# ({cc_size, cc_args, cc_linear_bits},class_env)	= class_env![fun_index]
			  (aci_linearity_of_patterns, var_heap)				= get_linearity_info cc_linear_bits case_guards var_heap
			# aci =
				{ aci_params				= []
				, aci_opt_unfolder			= No
				, aci_free_vars				= No
				, aci_linearity_of_patterns = aci_linearity_of_patterns
				, aci_safe					= safe
				}
			= ([case_info_ptr:cleanup_acc], class_env, fun_defs, var_heap, 
				setExtendedExprInfo case_info_ptr (EEI_ActiveCase aci) expr_heap)
		set_case_expr_info _ _ s = s
// ...N-WAY
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
				-> (!CleanupInfo, !*{#FunDef}, !*VarHeap, !*ExpressionHeap, !*FunctionHeap, !*{!ConsClasses}, !Bool)
reanalyseGroups common_defs imported_funs main_dcl_module_n stdStrictLists_module_n new_functions
	groups fun_defs var_heap expr_heap fun_heap class_env
	# consumerAnalysisRO=ConsumerAnalysisRO
		{ common_defs				= common_defs
		, imported_funs				= imported_funs
		, main_dcl_module_n			= main_dcl_module_n
		, stdStrictLists_module_n	= stdStrictLists_module_n
		}
	= foldSt (analyse_group consumerAnalysisRO) groups
				([], fun_defs, var_heap, expr_heap, fun_heap, class_env, True)
where	
	analyse_group common_defs group (cleanup_info, fun_defs, var_heap, expr_heap, fun_heap, class_env, same)
		# {group_members}	= group

		# (next_var, nr_of_local_vars, var_heap, class_env, fun_defs, fun_heap, old_cons_class)
				= foldSt initial_cons_class group_members (0, 0, var_heap, class_env, fun_defs, fun_heap, [])

		# ai =
						{	ai_var_heap						= var_heap
						, 	ai_cons_class					= class_env
						,	ai_cur_ref_counts				= {}
						,	ai_class_subst					= createArray (next_var + nr_of_local_vars) CPassive
						,	ai_next_var						= next_var
						,	ai_next_var_of_fun				= 0
						,	ai_cases_of_vars_for_function	= []
						,	ai_fun_heap						= fun_heap
						,	ai_fun_defs						= fun_defs
						,	ai_group_members				= group_members
						,	ai_group_counts					= createArray (length group_members) {}
						}

		# (_, ai_cases_of_vars_for_group, rev_strictness_for_group, ai)
				= foldSt (analyse_functions common_defs) group_members (0, [], [], ai)
		  ai_group_counts
		  		= ai.ai_group_counts
		  ai_group_counts
		  		= replace_global_idx_by_group_idx group_members ai_group_counts
		#!
		  ai_group_counts
		  		= substitute_dep_counts group_members ai_group_counts
		  ai	= { ai & ai_group_counts =  ai_group_counts}
		  
		# (_,_,ai)
		  		= foldSt set_linearity_info_for_group group_members (0,reverse rev_strictness_for_group,ai)

		  class_env
		  		= ai.ai_cons_class
		  fun_heap
		  		= ai.ai_fun_heap
		  (class_env,fun_heap,same,_)
		  		= foldSt (collect_classifications ai.ai_class_subst) group_members (class_env,fun_heap,same,reverse old_cons_class)
		  (cleanup_info, class_env, fun_defs, var_heap, expr_heap, fun_heap)
				= foldSt set_case_expr_info (flatten ai_cases_of_vars_for_group)
					(cleanup_info, class_env, ai.ai_fun_defs, ai.ai_var_heap, expr_heap, fun_heap)
		= (cleanup_info, fun_defs, var_heap, expr_heap, fun_heap, class_env, same)
	  where
//initial classification...
		initial_cons_class fun (next_var, nr_of_local_vars, var_heap, class_env, fun_defs, fun_heap, old_acc)
			# (fun_def, fun_defs, fun_heap)			= get_fun_def fun fun_defs fun_heap
			# (TransformedBody {tb_args,tb_rhs})	= fun_def.fun_body
			  
			  nr_of_locals							= count_locals tb_rhs 0
			  nr_of_local_vars						= nr_of_local_vars + nr_of_locals
			  
			# (fresh_vars, next_var, var_heap)
			   										= fresh_variables tb_args 0 next_var var_heap
			# fun_class								= { cc_size = 0, cc_args = fresh_vars, cc_linear_bits=[], cc_producer=False}
			# (fun_heap,class_env,old_class)		= set_fun_class` fun fun_class fun_heap class_env
			= (next_var, nr_of_local_vars, var_heap, class_env, fun_defs, fun_heap, [old_class:old_acc])


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
			# gf									= {gf & gf_cons_args = fun_class}
			# fun_heap								= writePtr fun_def_ptr (FI_Function gf) fun_heap
			= (fun_heap,class_env)

		set_fun_class` fun fun_class fun_heap class_env
			| fun < size class_env
				# (old,class_env)					= replace class_env fun fun_class
				= (fun_heap,class_env,old)

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
			# (old,gf)								= (gf.gf_cons_args, {gf & gf_cons_args = fun_class})
			# fun_heap								= writePtr fun_def_ptr (FI_Function gf) fun_heap
			= (fun_heap,class_env,old)

//determine classification...
		analyse_functions common_defs fun (fun_index, cfvog_accu, strictness_accu, ai)
			#  (fun_def, fun_defs, fun_heap)		= get_fun_def fun ai.ai_fun_defs ai.ai_fun_heap
	 		   ai									= {ai
	 		   											& ai_fun_heap = fun_heap
	 		   											, ai_fun_defs = fun_defs
	 		   											}
//	 		   												---> ("reanalyse",fun_def)
	 		   (TransformedBody {tb_args, tb_rhs})	= fun_def.fun_body

			   nr_of_locals							= count_locals tb_rhs 0
			   nr_of_args							= length tb_args

			   ai = { ai
			   		& ai_cur_ref_counts				= n_zero_counts (nr_of_args + nr_of_locals)
			   		, ai_next_var_of_fun			= nr_of_args 
			   		}
			// classify
			   (_, _, ai)							= consumerRequirements tb_rhs common_defs ai
			#  ai_cur_ref_counts					= ai.ai_cur_ref_counts
			   cases_of_vars_for_function			= [(a,fun) \\ a <- ai.ai_cases_of_vars_for_function ]
			   cfvog_accu							= [cases_of_vars_for_function:cfvog_accu]
			   strictness_accu						= [get_strictness_list fun_def:strictness_accu]
			   											with
			   												get_strictness_list {fun_type = Yes {st_args_strictness}}
			   													= st_args_strictness

			   ai = { ai
			   		& ai_cases_of_vars_for_function	= [] 
			   		, ai_cur_ref_counts				= {}
			   		, ai_group_counts				= {ai.ai_group_counts & [fun_index] = ai_cur_ref_counts}
			   		}
			= (fun_index + 1, cfvog_accu, strictness_accu, ai)
		set_linearity_info_for_group fun (fun_index,group_strictness,ai=:{ai_cons_class,ai_group_counts,ai_fun_heap})
			#  (fun_cons_class,ai_fun_heap,ai_cons_class)
													= get_fun_class fun ai_fun_heap ai_cons_class
			   (fun_ref_counts,ai_group_counts)		= ai_group_counts![fun_index]
			   fun_cons_class						= set_linearity_info fun fun_index fun_cons_class fun_ref_counts group_strictness
			   (ai_fun_heap,ai_cons_class)			= set_fun_class fun fun_cons_class ai_fun_heap ai_cons_class
			   ai									= {ai & ai_cons_class = ai_cons_class, ai_group_counts = ai_group_counts, ai_fun_heap = ai_fun_heap}
			= (fun_index+1,group_strictness,ai)
		set_linearity_info fun fun_index fun_cons_class fun_ref_counts group_strictness
			#  linear_bits							= determine_linear_bits fun_ref_counts
			   fun_cons_class						= { fun_cons_class & cc_linear_bits=linear_bits }
			   cc_args								= add_unused_args fun fun_index fun_cons_class.cc_args fun_ref_counts group_strictness
			   fun_cons_class						= { fun_cons_class & cc_args = cc_args }
			= fun_cons_class
//final classification...
		collect_classifications :: !.{#Int} !Int !*(!*{!ConsClasses},!*FunctionHeap,!Bool,!u:[w:ConsClasses]) -> *(!*{!ConsClasses},!*FunctionHeap,!Bool,!v:[x:ConsClasses]), [w <= x, u <= v];
		collect_classifications class_subst fun (class_env,fun_heap,same,[old_class:old_acc])
			# (fun_class,fun_heap,class_env)	= get_fun_class fun fun_heap class_env
			  fun_class					= determine_classification fun_class class_subst
			# (fun_heap,class_env)		= set_fun_class fun fun_class fun_heap class_env
	 		= (class_env,fun_heap,same && equalCCs fun_class old_class,old_acc)

		equalCCs l r
			= equalCCArgs l.cc_args r.cc_args && equalCCBits l.cc_size l.cc_linear_bits r.cc_linear_bits
		equalCCArgs [] [] = True
		equalCCArgs [l:ls] [r:rs] = equalCC l r && equalCCArgs ls rs
		equalCC l r = l == r
		equalCCBits 0 _ _ = True
		equalCCBits n [l:ls] [r:rs] = l == r && equalCCBits (dec n) ls rs
		
		set_case_expr_info ((safe,{case_expr=case_expr=:(Var {var_info_ptr}), case_guards, case_info_ptr}),fun_index)
				(cleanup_acc, class_env, fun_defs, var_heap, expr_heap, fun_heap)
			# (VI_AccVar _ arg_position, var_heap)				= readPtr var_info_ptr var_heap
			  ({cc_size, cc_args, cc_linear_bits},fun_heap,class_env)	= get_fun_class fun_index fun_heap class_env
			  (aci_linearity_of_patterns, var_heap)				= get_linearity_info cc_linear_bits case_guards var_heap
			| arg_position<cc_size && (arg_position>=cc_size || cc_args!!arg_position==CActive) && cc_linear_bits!!arg_position
				# aci =
					{ aci_params				= []
					, aci_opt_unfolder			= No
					, aci_free_vars				= No
					, aci_linearity_of_patterns = aci_linearity_of_patterns
					, aci_safe					= safe
					}
				= ([case_info_ptr:cleanup_acc], class_env, fun_defs, var_heap, 
					setExtendedExprInfo case_info_ptr (EEI_ActiveCase aci) expr_heap, fun_heap)
			= (cleanup_acc, class_env, fun_defs, var_heap, expr_heap, fun_heap)
// N-WAY...
		set_case_expr_info ((safe,{case_expr=(App _), case_guards, case_info_ptr}),fun_index)
				(cleanup_acc, class_env, fun_defs, var_heap, expr_heap, fun_heap)
			# ({cc_size, cc_args, cc_linear_bits},fun_heap,class_env)	= get_fun_class fun_index fun_heap class_env
			  (aci_linearity_of_patterns, var_heap)				= get_linearity_info cc_linear_bits case_guards var_heap
			# aci =
				{ aci_params				= []
				, aci_opt_unfolder			= No
				, aci_free_vars				= No
				, aci_linearity_of_patterns = aci_linearity_of_patterns
				, aci_safe					= safe
				}
			= ([case_info_ptr:cleanup_acc], class_env, fun_defs, var_heap, 
				setExtendedExprInfo case_info_ptr (EEI_ActiveCase aci) expr_heap, fun_heap)
		set_case_expr_info _ s = s
// ...N-WAY

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
			= (gf_fun_def, fun_defs, fun_heap) // ---> ("read",fun_def_ptr,gf_fun_def)
			
fresh_variables :: ![.FreeVar] !Int !Int !*(Heap VarInfo) -> *(!.[Int],!Int,!*(Heap VarInfo))
fresh_variables [{fv_info_ptr} : vars] arg_position next_var_number var_heap
	# var_heap
	  		= writePtr fv_info_ptr (VI_AccVar next_var_number arg_position) var_heap
	# (fresh_vars, last_var_number, var_heap)
			= fresh_variables vars (inc arg_position) (inc next_var_number) var_heap
	= ([next_var_number : fresh_vars], last_var_number, var_heap)
fresh_variables [] _ next_var_number var_heap
	= ([], next_var_number, var_heap)

// count_locals determines number of local variables...

count_locals :: !Expression !Int -> Int
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
count_locals (FailExpr _) n = n
count_locals (NoBind _) n
	= n
count_locals (DictionariesFunction dictionaries expr expr_type) n
	= count_locals expr (foldSt count_local_dictionary dictionaries n)
	where
		count_local_dictionary ({fv_count},_) n
			| fv_count > 0
				= n+1
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
	count_selector_locals (RecordSelection _ _) n
		= n

add_unused_args fun fun_index args ref_counts group_strictness
	= SwitchNewOld
		[if (is_non_zero  rc)
			arg
			(unused2class (collect_deps (if (arg_strictness fun_index idx group_strictness) UStrict ULazy) [!rc!]) )
		\\ arg <- args & rc <-: ref_counts & idx <- [0..]]	// new
		[if (is_non_zero` rc) arg CUnusedStrict \\ arg <- args & rc <-: ref_counts]	// old
where
	unused2class :: !UnusedStatus -> ConsClass
	unused2class u = case u of
		UStrict	-> CUnusedStrict
		ULazy	-> CUnusedLazy
		UMixed	-> CUnusedStrict
	
	collect_deps :: !UnusedStatus ![!RefCount!] -> UnusedStatus
	collect_deps s [|]
		= s
	collect_deps s [|(Par _ d):ds]
		# s = collect_deps s d
		| isMixed s = s
		= collect_deps s ds
	collect_deps s [|(Seq _ d):ds]
		# s = collect_deps s d
		| isMixed s = s
		= collect_deps s ds
	collect_deps s [|(Dep f a):ds]
		# s = case arg_strictness f a group_strictness of
				True/*Strict*/	-> case s of
					UStrict	-> UStrict
					_		-> UMixed
				_/*Lazy*/	-> case s of
					ULazy	-> ULazy
					_		-> UMixed
		| isMixed s = s
		= collect_deps s ds
	
	isMixed UMixed = True
	isMixed _ = False
	
	arg_strictness f a group_strictness
		= arg_is_strict a (group_strictness!!f)
	
:: UnusedStatus = UEmpty | ULazy | UStrict | UMixed

determine_linear_bits ref_counts
	= [ score` rc < 2 \\ rc <-: ref_counts]

substitute_dep_counts group_members ai_group_counts
	#!	am						= size ai_group_counts.[0]
		(known,ai_group_counts)	= build_known ai_group_counts
	    ai_group_counts			= subst_non_zero [] 0 0 (length group_members) am known ai_group_counts
	= ai_group_counts
where
	build_known :: !*{!RefCounts} -> (!*{*{#Bool}},!*{!RefCounts})
	build_known t
		= arrayAndElementsCopy {} (\e->(createArray (size e) False,e)) t

	subst_non_zero :: ![(!FunIndex,!ArgIndex)] !FunIndex !ArgIndex !FunIndex !ArgIndex !*{*{#Bool}} !*{!RefCounts}-> *{!RefCounts}
	subst_non_zero iter fi ai fm am known rcs
		| ai >= am
			# fi = fi + 1
			# ai = 0
			| fi >= fm
				| not (isEmpty iter)
					# rcs = {{fix iter rc \\ rc <-: frcs} \\ frcs <-: rcs}
					#!	fi = 0
						am	= size rcs.[fi]
					= subst_non_zero [] fi ai fm am known rcs
				= rcs
			#!	am	= size rcs.[fi]
			= subst_non_zero iter fi ai fm am known rcs
		| known.[fi,ai]
			= subst_non_zero iter fi (ai + 1) fm am known rcs
		| SwitchNewOld (is_non_zero rcs.[fi,ai]) (is_non_zero` rcs.[fi,ai])
			# known = {known & [fi,ai] = True}
			= subst_non_zero [(fi,ai):iter] fi (ai + 1) fm am known rcs
		= subst_non_zero iter fi (ai + 1) fm am known rcs

	fix :: ![(!FunIndex,!ArgIndex)] !RefCount -> RefCount
	fix subs rc
		# rc = 	substitute_dep subs rc
//					 ---> ("substitute",fi,ai)
		| score rc == 2
			= Seq 2 [|]
			= rc

is_non_zero :: !RefCount -> Bool
is_non_zero rc = score rc > 0

is_non_zero` :: !RefCount -> Bool
is_non_zero` rc = score` rc > 0

//@ producerRequirements

:: *PRState =
	{ prs_group				:: ![Int]
	, prs_cons_args 		:: !*{!ConsClasses}
	, prs_main_dcl_module_n	:: !Int
	, prs_fun_heap			:: !*FunctionHeap
	, prs_fun_defs			:: !*{#FunDef}
	, prs_group_index		:: !Int
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
	producerRequirements app=:(App {app_symb,app_args}) prs
/*
		# (rec,prs)			= is_recursive_app app prs
		| not rec
			= producerRequirements app_args prs
*/
		// look up consumer class for app_symb args
		#! (maybe_ca,prs)	= retrieve_consumer_args app_symb prs
		// need to check for recursive call in safe arg...
		= case maybe_ca of
			No			// assuming that for functions that have no consumer info no unfolding will occur
						// note that this means that generated functions must be visible this way...
//						# prs = prs  ---> ("No cons info for",app_symb)
						-> (True,prs)
			Yes ca		// for each arg:
						// if safe && top of arg is App of group member...
						// else recurse into arg
//						# prs = prs  ---> ("Yes cons info for",app_symb,ca.cc_args,ca.cc_linear_bits)
						-> check_app_arguments ca.cc_args ca.cc_linear_bits app_args prs
	where
		check_app_arguments [cc_arg:cc_args] [cc_linear_bit:cc_bits] [app_arg:app_args] prs
			| cc_arg == CActive && cc_linear_bit
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
			#! main_dcl_module_n	= prs.prs_main_dcl_module_n
			# { glob_module, glob_object }
				= case symb_kind of
					SK_Function global_index -> global_index
					SK_LocalMacroFunction index -> { glob_module = main_dcl_module_n, glob_object = index }
					SK_GeneratedFunction info_ptr index -> { glob_module = main_dcl_module_n, glob_object = index }
					_ -> {glob_module = -1, glob_object = -1}
			| glob_module <> main_dcl_module_n
				= (False,prs)
			#! (fun_def,fun_defs,fun_heap)	= get_fun_def symb_kind prs.prs_main_dcl_module_n prs.prs_fun_defs prs.prs_fun_heap
			   prs = {prs & prs_fun_defs = fun_defs, prs_fun_heap = fun_heap}
			   rec = fun_def.fun_info.fi_group_index == prs.prs_group_index
			= (rec,prs)
		where
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
		# (safe,prs)	= producerRequirements let_lazy_binds prs
		| not safe		= (safe,prs)
		# (safe,prs)	= producerRequirements let_strict_binds prs
		| not safe		= (safe,prs)
		# (safe,prs)	= producerRequirements let_expr prs
		| not safe		= (safe,prs)
		= (safe,prs)
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
	producerRequirements (Selection _ expr sels) prs
		# (safe,prs)	= producerRequirements expr prs
		| safe			= producerRequirements sels prs
						= (safe,prs)
	producerRequirements (Update expr1 sels expr2) prs
		# (safe,prs)	= producerRequirements expr1 prs
		| not safe		= (safe,prs)
		# (safe,prs)	= producerRequirements expr2 prs
		| not safe		= (safe,prs)
		# (safe,prs)	= producerRequirements sels prs
		| not safe		= (safe,prs)
		= (True,prs)
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
	producerRequirements (MatchExpr _ expr) prs
		= producerRequirements expr prs
	producerRequirements (DynamicExpr _) prs
		= (False,prs)
	producerRequirements (TypeCodeExpression _) prs
		= (False,prs)
	producerRequirements (EE) prs
		= (False,prs)
	producerRequirements (NoBind var) prs
		= (True,prs)
	producerRequirements (FailExpr _) prs
		= (True,prs)
	producerRequirements expr prs
		= abort ("producerRequirements " ---> expr)

instance producerRequirements (Optional a) | producerRequirements a where
	producerRequirements (Yes x) prs
		= producerRequirements x prs
	producerRequirements No prs
		= (True,prs)

instance producerRequirements CasePatterns where
	producerRequirements (AlgebraicPatterns index patterns) prs
		= producerRequirements patterns prs
	producerRequirements (BasicPatterns type patterns) prs
		= producerRequirements patterns prs
	producerRequirements (OverloadedListPatterns _ _ patterns) prs
		= producerRequirements patterns prs
	producerRequirements (DynamicPatterns patterns) prs
		//...disallow for now...
		= (False,prs)
	producerRequirements NoPattern prs
		= (True,prs)

instance producerRequirements AlgebraicPattern where
	producerRequirements {ap_expr} prs
		= producerRequirements ap_expr prs

instance producerRequirements BasicPattern where
	producerRequirements {bp_expr} prs
		= producerRequirements bp_expr prs

instance producerRequirements LetBind where
	producerRequirements {lb_src} prs
		= producerRequirements lb_src prs

instance producerRequirements Selection where
	producerRequirements (RecordSelection _ _) prs
		= (True,prs)
	producerRequirements (ArraySelection _ _ expr) prs
		= producerRequirements expr prs
	producerRequirements (DictionarySelection _ sels _ expr) prs
		# (safe,prs)	= producerRequirements expr prs
		| safe			= producerRequirements sels prs
						= (safe,prs)

retrieve_consumer_args :: !SymbIdent !*PRState -> (!Optional ConsClasses, !*PRState)
retrieve_consumer_args si=:{symb_kind} prs=:{prs_cons_args, prs_main_dcl_module_n}
	# (prs_size, prs_cons_args) = usize prs_cons_args
	  prs = {prs & prs_cons_args = prs_cons_args}
	= case symb_kind of
		SK_Function {glob_module, glob_object}
			| glob_module == prs_main_dcl_module_n && glob_object < prs_size
				# (cons_args,prs) = prs!prs_cons_args.[glob_object]
				-> (Yes cons_args,prs)
			-> (No,prs)
		SK_LocalMacroFunction glob_object
			| glob_object < prs_size
				# (cons_args,prs) = prs!prs_cons_args.[glob_object]
				-> (Yes cons_args,prs)
			-> (No,prs)
		SK_GeneratedFunction fun_ptr fun_index
			| fun_index < prs_size
				# (cons_args,prs) = prs!prs_cons_args.[fun_index]
				-> (Yes cons_args,prs)
			# (FI_Function {gf_cons_args}, fun_heap)	= readPtr fun_ptr prs.prs_fun_heap
			# prs										= {prs & prs_fun_heap = fun_heap}
			-> (Yes gf_cons_args,prs)
//		SK_Constructor cons_index
		sk -> (No,prs)
