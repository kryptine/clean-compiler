/*
	module owner: Diederik van Arkel
*/
implementation module trans

import StdEnv

import syntax, transform, checksupport, StdCompare, check, utilities, unitype, typesupport, type
import classify, partition

SwitchCaseFusion			fuse dont_fuse :== fuse
SwitchGeneratedFusion		fuse dont_fuse :== fuse
SwitchFunctionFusion		fuse dont_fuse :== fuse
SwitchConstructorFusion		fuse dont_fuse :== dont_fuse
SwitchRnfConstructorFusion  rnf  linear	   :== rnf
SwitchCurriedFusion			fuse xtra dont_fuse :== fuse 
SwitchExtraCurriedFusion	fuse macro :== (fuse && macro)//fuse
SwitchTrivialFusion			fuse dont_fuse :== fuse
SwitchUnusedFusion			fuse dont_fuse :== fuse
SwitchReanalyseFunction		rean dont_rean :== dont_rean
SwitchTransformConstants	tran dont_tran :== tran
SwitchSpecialFusion			fuse dont_fuse :== fuse
SwitchArityChecks			check dont_check :== check
SwitchNWayFusion			fuse dont_fuse :== dont_fuse
SwitchDirectConsumerUnfold	unfold dont    :== dont
SwitchAutoFoldCaseInCase	fold dont	   :== fold
SwitchAutoFoldAppInCase		fold dont	   :== fold
SwitchAlwaysIntroduceCaseFunction yes no   :== no//yes
SwitchNonRecFusion			fuse dont_fuse :== dont_fuse
SwitchHOFusion				fuse dont_fuse :== fuse
SwitchHOFusion`				fuse dont_fuse :== fuse

//import RWSDebug

(-!->) infix
(-!->) a b :== a  // ---> b
(<-!-) infix
(<-!-) a b :== a  // <--- b

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
		_							-> abort "sanity check 'readExtendedVarInfo' failed in module trans.\n"

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

/*
 *	TRANSFORM
 */

::	*TransformInfo =
	{	ti_fun_defs				:: !*{# FunDef}
	,	ti_instances 			:: !*{! InstanceInfo }
	,	ti_cons_args 			:: !*{! ConsClasses}
	,	ti_new_functions 		:: ![FunctionInfoPtr]
	,	ti_fun_heap				:: !*FunctionHeap
	,	ti_var_heap				:: !*VarHeap
	,	ti_symbol_heap			:: !*ExpressionHeap
	,	ti_type_heaps			:: !*TypeHeaps
	,	ti_type_def_infos		:: !*TypeDefInfos
	,	ti_next_fun_nr			:: !Index
	,	ti_cleanup_info			:: !CleanupInfo
	,	ti_recursion_introduced	:: !Optional Index
//	,	ti_trace				:: !Bool // XXX just for tracing
	,	ti_error_file			:: !*File
	,	ti_predef_symbols		:: !*PredefinedSymbols
	}

::	ReadOnlyTI = 
	{	ro_imported_funs	:: !{# {# FunType} }
	,	ro_common_defs		:: !{# CommonDefs }
// the following four are used when possibly generating functions for cases...
	,	ro_root_case_mode		:: !RootCaseMode
	,	ro_fun_root				:: !SymbIdent		// original function
	,	ro_fun_case				:: !SymbIdent		// original function or possibly generated case
	,	ro_fun_args				:: ![FreeVar]		// args of above
	,	ro_fun_geni				:: !(!Int,!Int)
	,	ro_fun_orig				:: !SymbIdent		// original consumer

	,	ro_main_dcl_module_n 	:: !Int

	,	ro_transform_fusion		:: !Bool			// fusion switch

	,	ro_stdStrictLists_module_n :: !Int
	}

::	RootCaseMode = NotRootCase | RootCase | RootCaseOfZombie

neverMatchingCase (Yes ident)
	# ident = ident -!-> ("neverMatchingCase",ident)
	= FailExpr ident
neverMatchingCase _ 
	# ident = {id_name = "neverMatchingCase", id_info = nilPtr}  -!-> "neverMatchingCase without ident\n"
	= FailExpr ident
/*
	= Case { case_expr = EE, case_guards = NoPattern, case_default = No, case_ident = ident, case_info_ptr = nilPtr, 
// RWS ...
						case_explicit = False,
				//		case_explicit = True,	// DvA better?
// ... RWS
						case_default_pos = NoPos }
*/
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
		  lad = { lad & let_lazy_binds = let_lazy_binds, let_strict_binds = let_strict_binds, let_expr = let_expr}
//		  ti = check_type_info lad ti
		= (Let lad, ti)
	  where
		store_type_info_of_bindings_in_heap {let_strict_binds, let_lazy_binds,let_info_ptr} ti
			# let_binds = let_strict_binds ++ let_lazy_binds
			# (EI_LetType var_types, ti_symbol_heap) = readExprInfo let_info_ptr ti.ti_symbol_heap
			  ti_var_heap								= foldSt store_type_info_let_bind
								   (zip2 var_types let_binds) ti.ti_var_heap
								   //  ---> ("store_type_info_of_bindings_in_heap",let_strict_binds,let_lazy_binds,var_types)
			= { ti & ti_symbol_heap = ti_symbol_heap, ti_var_heap = ti_var_heap }
		store_type_info_let_bind (var_type, {lb_dst={fv_info_ptr}}) var_heap
			= setExtendedVarInfo fv_info_ptr (EVI_VarType var_type) var_heap
		check_type_info {let_strict_binds,let_lazy_binds,let_info_ptr} ti
			# (EI_LetType var_types, ti_symbol_heap) = readExprInfo let_info_ptr ti.ti_symbol_heap
			= { ti & ti_symbol_heap = ti_symbol_heap }
				//  ---> ("check_type_info_of_bindings_in_heap",let_strict_binds,let_lazy_binds,var_types)

	transform (Case kees) ro ti
		# ti = store_type_info_of_patterns_in_heap kees ti
		= transformCase kees ro ti
	  where
		store_type_info_of_patterns_in_heap {case_guards,case_info_ptr} ti
			= case case_guards of
				AlgebraicPatterns _ patterns
					# (EI_CaseType {ct_cons_types},ti_symbol_heap)
										= readExprInfo case_info_ptr ti.ti_symbol_heap
					  ti_var_heap = foldSt store_type_info_of_alg_pattern (zip2 ct_cons_types patterns) ti.ti_var_heap
					-> { ti & ti_symbol_heap = ti_symbol_heap, ti_var_heap = ti_var_heap }
				BasicPatterns _ _
					-> ti // no variables occur
				OverloadedListPatterns _ _ patterns
					# (EI_CaseType {ct_cons_types},ti_symbol_heap)
										= readExprInfo case_info_ptr ti.ti_symbol_heap
					  ti_var_heap = foldSt store_type_info_of_alg_pattern (zip2 ct_cons_types patterns) ti.ti_var_heap
					-> { ti & ti_symbol_heap = ti_symbol_heap, ti_var_heap = ti_var_heap }
				NoPattern
					-> ti
		store_type_info_of_alg_pattern (var_types,{ap_vars}) var_heap
			= foldSt store_type_info_of_pattern_var (zip2 var_types ap_vars) var_heap
		store_type_info_of_pattern_var (var_type, {fv_info_ptr}) var_heap
			= setExtendedVarInfo fv_info_ptr (EVI_VarType var_type) var_heap

	transform (Selection opt_type expr selectors) ro ti
		# (expr, ti) = transform expr ro ti
		= transformSelection opt_type selectors expr ro ti
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
	| SwitchCaseFusion (not ro.ro_transform_fusion) True
		= skip_over this_case ro ti
	| isNilPtr case_info_ptr			// encountered neverMatchingCase?!
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
	= (removeNeverMatchingSubcases result_expr ro, ti)
where
	is_variable (Var _) = True
	is_variable _ 		= False

skip_over this_case=:{case_expr,case_guards,case_default} ro ti
	# ro_lost_root = { ro & ro_root_case_mode = NotRootCase }
	  (new_case_expr, ti) = transform case_expr ro_lost_root ti
	  (new_case_guards, ti) = transform case_guards ro_lost_root ti
	  (new_case_default, ti) = transform case_default ro_lost_root ti
	= (Case { this_case & case_expr=new_case_expr, case_guards=new_case_guards, case_default=new_case_default }, ti)

transCase is_active opt_aci this_case=:{case_expr = Case case_in_case} ro ti
	| is_active
		= lift_case case_in_case this_case ro ti
		= skip_over this_case ro ti
where
	lift_case nested_case=:{case_guards,case_default} outer_case ro ti
		| isNilPtr nested_case.case_info_ptr	// neverMatchingCase ?!
			= skip_over outer_case ro ti
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
	lift_patterns _ _ _ _ _
		= abort "lift_patterns does not match"

	lift_patterns_2 False [guard_expr] outer_case ro ti
		// if no default pattern exists, then the outer case expression does not have to be copied for the last pattern
		# (guard_expr, ti)						= possiblyFoldOuterCase True guard_expr outer_case ro ti
		= ([guard_expr], ti)
	lift_patterns_2 default_exists [guard_expr : guard_exprs] outer_case ro ti
		# (guard_expr, ti)						= possiblyFoldOuterCase False guard_expr outer_case ro ti
		  (guard_exprs, ti) = lift_patterns_2 default_exists guard_exprs outer_case ro ti
		= ([guard_expr : guard_exprs], ti)
	lift_patterns_2 _ [] _ _ ti
		= ([], ti)
		
	lift_default (Yes default_expr) outer_case ro ti
		# (default_expr, ti)					= possiblyFoldOuterCase True default_expr outer_case ro ti
		= (Yes default_expr, ti)
	lift_default No _ _ ti
		= (No, ti)

	possiblyFoldOuterCase final guard_expr outer_case ro ti
		| SwitchAutoFoldCaseInCase (isFoldExpression guard_expr) False // otherwise GOTO next alternative
			| False -!-> ("possiblyFoldOuterCase","Case",bef < 0 || act < 0,ro.ro_fun_args,aci.aci_params) = undef
			| bef < 0 || act < 0
				= possiblyFoldOuterCase` final guard_expr outer_case ro ti	//abort "possiblyFoldOuterCase: unexpected!\n"
			= transformApplication { app_symb = folder, app_args = folder_args, app_info_ptr = nilPtr } [] ro ti
		= possiblyFoldOuterCase` final guard_expr outer_case ro ti
	where
		(bef,act)	= ro.ro_fun_geni
		new_f_a_before	= take bef ro.ro_fun_args
		new_f_a_after	= drop (bef+act) ro.ro_fun_args
		
		f_a_before	= new_f_a_before	//| new_f_a_before <> old_f_a_before	= abort "!!!"
		f_a_after	= new_f_a_after

//			= transformApplication { app_symb = folder, app_args = folder_args, app_info_ptr = nilPtr } [] ro ti
//	where
		isFoldExpression (App app)	= isFoldSymbol app.app_symb.symb_kind
		isFoldExpression (Var _)	= True
//		isFoldExpression (Case _)	= True
		isFoldExpression _			= False
		
		isFoldSymbol (SK_Function _)			= True
		isFoldSymbol (SK_LocalMacroFunction _)	= True
		isFoldSymbol (SK_GeneratedFunction _ _)	= True
		isFoldSymbol _							= False
		
		folder		= ro.ro_fun_orig
		folder_args = f_a_before` ++ [guard_expr:f_a_after`]
		old_f_a_before	= takeWhile (\e -> not (isMember e aci.aci_params)) ro.ro_fun_args
		old_f_a_help	= dropWhile (\e -> not (isMember e aci.aci_params)) ro.ro_fun_args
		old_f_a_after	= dropWhile (\e -> isMember e aci.aci_params) old_f_a_help
		f_a_before`	= [Var {var_name = fv_name, var_info_ptr = fv_info_ptr, var_expr_ptr = nilPtr} \\ {fv_name,fv_info_ptr} <- f_a_before]
		f_a_after`	= [Var {var_name = fv_name, var_info_ptr = fv_info_ptr, var_expr_ptr = nilPtr} \\ {fv_name,fv_info_ptr} <- f_a_after]
		(Yes aci)	= opt_aci

		isMember x [hd:tl] = hd.fv_info_ptr==x.fv_info_ptr || isMember x tl
		isMember x []	= False

	possiblyFoldOuterCase` final guard_expr outer_case ro ti
		| final
			= transformCase {outer_case & case_expr = guard_expr} ro ti
		# us = { us_var_heap = ti.ti_var_heap, us_symbol_heap = ti.ti_symbol_heap, us_opt_type_heaps = No
				,us_cleanup_info=ti.ti_cleanup_info, us_local_macro_functions = No }
		  ui									= {ui_handle_aci_free_vars = LeaveThem }
		  (outer_guards, us=:{us_cleanup_info})	= unfold outer_case.case_guards ui us
		  (expr_info, ti_symbol_heap)			= readPtr outer_case.case_info_ptr us.us_symbol_heap
		  (new_info_ptr, ti_symbol_heap)		= newPtr expr_info ti_symbol_heap
		  new_cleanup_info 						= case expr_info of 
		  		EI_Extended _ _
		  			-> [new_info_ptr:us_cleanup_info]
		  		_ 	-> us_cleanup_info
		  ti = { ti & ti_var_heap = us.us_var_heap, ti_symbol_heap = ti_symbol_heap, ti_cleanup_info=new_cleanup_info }
		  new_case								= { outer_case & case_expr = guard_expr, case_guards=outer_guards, case_info_ptr=new_info_ptr }
		= transformCase new_case ro ti
	
transCase is_active opt_aci this_case=:{case_expr = case_expr=:(App app=:{app_symb,app_args}),case_guards,case_default,case_explicit} ro ti
	= case app_symb.symb_kind of
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
					-> (neverMatchingCase never_ident, ti) <-!- ("transCase:App:neverMatchingCase",never_ident)
					with
						never_ident = case ro.ro_root_case_mode of
							NotRootCase -> this_case.case_ident
							_ -> Yes ro.ro_fun_case.symb_name
		// otherwise it's a function application
		_	-> case opt_aci of
				Yes aci=:{ aci_params, aci_opt_unfolder }
					-> case aci_opt_unfolder of
						No	-> skip_over this_case ro ti									-!-> ("transCase","No opt unfolder")
						Yes unfolder
							| not (equal app_symb.symb_kind unfolder.symb_kind)
								// in this case a third function could be fused in
								-> possiblyFoldOuterCase this_case ro ti					-!-> ("transCase","Diff opt unfolder",unfolder,app_symb)
							# variables = [ Var {var_name=fv_name, var_info_ptr=fv_info_ptr, var_expr_ptr=nilPtr}
											\\ {fv_name, fv_info_ptr} <- ro.ro_fun_args ]
							  (ti_next_fun_nr, ti) = ti!ti_next_fun_nr						-!-> ("transCase","Yes opt unfolder",unfolder)
							  (new_next_fun_nr, app_symb)
								= case ro.ro_root_case_mode of
										RootCaseOfZombie
											# (ro_fun=:{symb_kind=SK_GeneratedFunction fun_info_ptr _}) = ro.ro_fun_case
											-> (inc ti_next_fun_nr,
											    { ro_fun & symb_kind=SK_GeneratedFunction fun_info_ptr ti_next_fun_nr })
												-!-> ("Recursion","RootCaseOfZombie",ti_next_fun_nr,ti.ti_recursion_introduced)
										RootCase
											-> (ti_next_fun_nr, ro.ro_fun_root)
												-!-> ("Recursion","RootCase",ti_next_fun_nr,ro.ro_fun_root,ti.ti_recursion_introduced)
							  ti = case ro.ro_root_case_mode of
										RootCaseOfZombie
											-> { ti & ti_next_fun_nr = new_next_fun_nr, ti_recursion_introduced = Yes ti_next_fun_nr }
										RootCase
											-> { ti & ti_next_fun_nr = new_next_fun_nr, ti_recursion_introduced = No }
							  app_args1 = replace_arg [ fv_info_ptr \\ {fv_info_ptr}<-aci_params ] app_args variables
							  (app_args2, ti) = transform app_args1 { ro & ro_root_case_mode = NotRootCase } ti
							-> (App {app_symb=app_symb, app_args=app_args2, app_info_ptr=nilPtr}, ti)
				No	-> skip_over this_case ro ti
where
	possiblyFoldOuterCase outer_case ro ti
		| SwitchAutoFoldAppInCase True False
			| False -!-> ("possiblyFoldOuterCase","App",bef < 0 || act < 0,ro.ro_fun_args,aci.aci_params) = undef
			| bef < 0 || act < 0	= skip_over this_case ro ti	//abort "possiblyFoldOuterCase: unexpected!\n"
			= transformApplication { app_symb = folder, app_args = folder_args, app_info_ptr = nilPtr } [] ro ti
		= skip_over this_case ro ti
	where
		(bef,act)	= ro.ro_fun_geni
		new_f_a_before	= take bef ro.ro_fun_args
		new_f_a_after	= drop (bef+act) ro.ro_fun_args
		
		f_a_before	= new_f_a_before
		f_a_after	= new_f_a_after

		folder		= ro.ro_fun_orig
		folder_args = f_a_before` ++ [case_expr:f_a_after`]
		old_f_a_before	= takeWhile (\e -> not (isMember e aci.aci_params)) ro.ro_fun_args
		old_f_a_help	= dropWhile (\e -> not (isMember e aci.aci_params)) ro.ro_fun_args
		old_f_a_after	= dropWhile (\e -> isMember e aci.aci_params) old_f_a_help
		f_a_before`	= [Var {var_name = fv_name, var_info_ptr = fv_info_ptr, var_expr_ptr = nilPtr} \\ {fv_name,fv_info_ptr} <- f_a_before]
		f_a_after`	= [Var {var_name = fv_name, var_info_ptr = fv_info_ptr, var_expr_ptr = nilPtr} \\ {fv_name,fv_info_ptr} <- f_a_after]
		(Yes aci)	= opt_aci

		isMember x [hd:tl] = hd.fv_info_ptr==x.fv_info_ptr || isMember x tl
		isMember x []	= False

	equal (SK_Function glob_index1) (SK_Function glob_index2)
		= glob_index1==glob_index2
	equal (SK_LocalMacroFunction glob_index1) (SK_LocalMacroFunction glob_index2)
		= glob_index1==glob_index2
	equal (SK_GeneratedFunction _ index1) (SK_GeneratedFunction _ index2)
		= index1==index2
	equal _ _
		= False

	replace_arg [] _ f
		= f
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

	match_and_instantiate [linearity:linearities] cons_index app_args 
							[{ap_symbol={glob_module,glob_object={ds_index}}, ap_vars, ap_expr} : guards] 
							case_default ro ti
		| cons_index.glob_module == glob_module && cons_index.glob_object == ds_index
			# zipped = zip2 ap_vars app_args
			  {cons_type} = ro.ro_common_defs.[glob_module].com_cons_defs.[ds_index]
			  unfoldables = [ ((not (arg_is_strict i cons_type.st_args_strictness)) && linear) || in_normal_form app_arg \\ linear <- linearity & app_arg <- app_args & i <- [0..]]
			  unfoldable_args = filterWith unfoldables zipped
			  not_unfoldable = map not unfoldables
			  non_unfoldable_args = filterWith not_unfoldable zipped
			  ti_var_heap = foldSt (\({fv_info_ptr}, arg) -> writeVarInfo fv_info_ptr (VI_Expression arg)) unfoldable_args ti.ti_var_heap
			  (new_expr, ti_symbol_heap) = possibly_add_let non_unfoldable_args ap_expr not_unfoldable cons_type ro ti.ti_symbol_heap
			  unfold_state = { us_var_heap = ti_var_heap, us_symbol_heap = ti_symbol_heap, us_opt_type_heaps = No,us_cleanup_info=ti.ti_cleanup_info,
			  				   us_local_macro_functions = No }
			  ui= {ui_handle_aci_free_vars = LeaveThem }
			  (unfolded_expr, unfold_state) = unfold new_expr ui unfold_state
			  (final_expr, ti) = transform unfolded_expr
			  						{ ro & ro_root_case_mode = NotRootCase }
			  						{ ti & ti_var_heap = unfold_state.us_var_heap, ti_symbol_heap = unfold_state.us_symbol_heap,ti_cleanup_info=unfold_state.us_cleanup_info }
			= (Yes final_expr, ti)
		= match_and_instantiate linearities cons_index app_args guards case_default ro ti
	match_and_instantiate [linearity:linearities] cons_index app_args [guard : guards] case_default ro ti
		= match_and_instantiate linearities cons_index app_args guards case_default ro ti
	match_and_instantiate _ cons_index app_args [] default_expr ro ti
		= transform default_expr { ro & ro_root_case_mode = NotRootCase } ti

transCase is_active opt_aci this_case=:{case_expr = (BasicExpr basic_value),case_guards,case_default} ro ti
	| not is_active
		= skip_over this_case ro ti // XXX currently only active cases are matched at runtime (multimatch problem)
	# basicPatterns = getBasicPatterns case_guards
	  may_be_match_pattern = dropWhile (\{bp_value} -> bp_value<>basic_value) basicPatterns
	| isEmpty may_be_match_pattern
		= case case_default of
			Yes default_expr-> transform default_expr { ro & ro_root_case_mode = NotRootCase } ti
			No				-> (neverMatchingCase never_ident, ti) <-!- ("transCase:BasicExpr:neverMatchingCase",never_ident)
					with
						never_ident = case ro.ro_root_case_mode of
							NotRootCase -> this_case.case_ident
							_ -> Yes ro.ro_fun_case.symb_name
	= transform (hd may_be_match_pattern).bp_expr { ro & ro_root_case_mode = NotRootCase } ti
where
	getBasicPatterns (BasicPatterns _ basicPatterns)
		= basicPatterns

transCase is_active opt_aci this_case=:{case_expr = (Let lad)} ro ti
	| not is_active
		= skip_over this_case ro ti
	# ro_not_root = { ro & ro_root_case_mode = NotRootCase }
	  (new_let_strict_binds, ti) = transform lad.let_strict_binds ro_not_root ti
	  (new_let_lazy_binds, ti) = transform lad.let_lazy_binds ro_not_root ti
	  (new_let_expr, ti) = transform (Case { this_case & case_expr = lad.let_expr }) ro ti
	= (Let { lad & let_expr = new_let_expr, let_strict_binds = new_let_strict_binds, let_lazy_binds = new_let_lazy_binds }, ti)

transCase is_active opt_aci this_case ro ti
	= skip_over this_case ro ti
	
in_normal_form (Var _)			= True
in_normal_form (BasicExpr _)	= True
in_normal_form _				= False

filterWith [True:t2] [h1:t1]
	= [h1:filterWith t2 t1]
filterWith [False:t2] [h1:t1]
	= filterWith t2 t1
filterWith _ _
	= []

possibly_add_let [] ap_expr _ _ _ ti_symbol_heap
	= (ap_expr, ti_symbol_heap)
possibly_add_let non_unfoldable_args ap_expr not_unfoldable cons_type ro ti_symbol_heap
	# let_type = filterWith not_unfoldable cons_type.st_args
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

possibly_generate_case_function :: !Case !ActiveCaseInfo !ReadOnlyTI !*TransformInfo -> *(!Expression, !*TransformInfo)
possibly_generate_case_function kees=:{case_info_ptr} aci=:{aci_free_vars} ro ti=:{ti_recursion_introduced=old_ti_recursion_introduced}
//	| False -!-> ("possibly_generate_case_function",ro.ro_fun_root.symb_name.id_name,ro.ro_fun_case.symb_name.id_name,ro.ro_root_case_mode)
//		= undef
	| not aci.aci_safe
		= skip_over kees ro ti
	// determine free variables
	# ti_var_heap = clearVariables (Case kees) ti.ti_var_heap
	  fvi	= { fvi_var_heap = ti_var_heap, fvi_expr_heap = ti.ti_symbol_heap, fvi_variables = [],
			  fvi_expr_ptrs = ti.ti_cleanup_info }
	  {fvi_var_heap, fvi_expr_heap, fvi_variables, fvi_expr_ptrs}
	  		= freeVariables (Case kees) fvi
	  ti	= { ti & ti_var_heap = fvi_var_heap, ti_symbol_heap = fvi_expr_heap, ti_cleanup_info = fvi_expr_ptrs }
	  free_vars	= fvi_variables
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
	| SwitchArityChecks (length all_args > 32) False
		# ti
		  		= { ti & ti_cons_args = ti_cons_args, ti_fun_defs = ti_fun_defs, ti_fun_heap = ti_fun_heap, ti_recursion_introduced = No }
		| ro.ro_transform_fusion
			#  ti	= { ti & ti_error_file = ti.ti_error_file <<< "Possibly missed fusion oppurtunity: Case Arity > 32 " <<< ro.ro_fun_root.symb_name.id_name <<< "\n"}
			= skip_over kees ro ti
		= skip_over kees ro ti
	# (fun_info_ptr, ti_fun_heap)
	  		= newPtr FI_Empty ti_fun_heap
	  fun_ident
	  		= { id_name = ro.ro_fun_root.symb_name.id_name+++"_case", id_info = nilPtr }
	  fun_symb
	  		= { symb_name = fun_ident, symb_kind=SK_GeneratedFunction fun_info_ptr undeff }
	  			<-!- ("<<<transformCaseFunction",fun_ident)
	| SwitchAlwaysIntroduceCaseFunction True False
		# ti
	  		= { ti & ti_cons_args = ti_cons_args, ti_fun_defs = ti_fun_defs, ti_fun_heap = ti_fun_heap }
	  	# fun_index
	  		= ti.ti_next_fun_nr
	  	# ti
	  		= { ti & ti_next_fun_nr = fun_index + 1 }
		# new_ro
	  		= { ro & ro_root_case_mode = RootCaseOfZombie , ro_fun_case = fun_symb, ro_fun_args = all_args }
	  	= generate_case_function fun_index case_info_ptr (Case kees) outer_fun_def outer_cons_args used_mask new_ro ti
	# new_ro
	  		= { ro & ro_root_case_mode = RootCaseOfZombie , ro_fun_case = fun_symb, ro_fun_args = all_args, ro_fun_geni = (-1,-1) }
	  ti
	  		= { ti & ti_cons_args = ti_cons_args, ti_fun_defs = ti_fun_defs, ti_fun_heap = ti_fun_heap, ti_recursion_introduced = No }
	  (new_expr, ti)
	  		= transformCase kees new_ro ti
	  (ti_recursion_introduced, ti)
	  		= ti!ti_recursion_introduced
	  			<-!- ("transformCaseFunction>>>",fun_ident)
	  ti	= { ti & ti_recursion_introduced = old_ti_recursion_introduced }
	= case ti_recursion_introduced of
		Yes fun_index
			-> generate_case_function fun_index case_info_ptr new_expr outer_fun_def outer_cons_args used_mask new_ro ti
		No	-> (new_expr, ti)

generate_case_function :: !Int !ExprInfoPtr !Expression FunDef .ConsClasses [.Bool] !.ReadOnlyTI !*TransformInfo -> (!Expression,!*TransformInfo)
generate_case_function fun_index case_info_ptr new_expr outer_fun_def outer_cons_args used_mask
					{ro_fun_case=ro_fun=:{symb_kind=SK_GeneratedFunction fun_info_ptr _}, ro_fun_args} ti
//	| False -!-> ("generate_case_function",ro_fun.symb_name)		= undef
	# fun_arity								= length ro_fun_args
	# ti = arity_warning "generate_case_function" ro_fun.symb_name fun_index fun_arity ti
	  (Yes {st_vars,st_args,st_attr_env})	= outer_fun_def.fun_type
	  types_from_outer_fun					= [ st_arg \\ st_arg <- st_args & used <- used_mask | used ]
	  nr_of_lifted_vars						= fun_arity-(length types_from_outer_fun)
	  (lifted_types, ti_var_heap)			= mapSt get_type_of_local_var (take nr_of_lifted_vars ro_fun_args) ti.ti_var_heap
	  (EI_CaseType {ct_result_type}, ti_symbol_heap) = readExprInfo case_info_ptr ti.ti_symbol_heap
	  (form_vars, ti_var_heap)				= mapSt bind_to_fresh_expr_var ro_fun_args ti_var_heap

	  arg_types								= lifted_types++types_from_outer_fun

	# ti = {ti & ti_var_heap = ti_var_heap, ti_symbol_heap = ti_symbol_heap}
	# (fun_type,ti)							= determine_case_function_type fun_arity ct_result_type arg_types st_attr_env ti

	  // unfold...
	  us =		{ us_var_heap				= ti.ti_var_heap
	  			, us_symbol_heap			= ti.ti_symbol_heap
	  			, us_opt_type_heaps			= Yes ti.ti_type_heaps
	  			, us_cleanup_info			= ti.ti_cleanup_info
	  			, us_local_macro_functions	= No 
	  			}
	  ui =
	  			{ ui_handle_aci_free_vars	= SubstituteThem
	  			}
	  (copied_expr, us)
			= unfold new_expr ui us
	  {us_var_heap=ti_var_heap, us_symbol_heap=ti_symbol_heap, us_cleanup_info=ti_cleanup_info, us_opt_type_heaps = Yes ti_type_heaps}
	  		= us
	  // generated function...
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
	  			, cc_args			= repeatn nr_of_lifted_vars CPassive ++ cc_args_from_outer_fun
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
	determine_case_function_type fun_arity ct_result_type arg_types st_attr_env ti
		# {ti_type_heaps}						= ti
		  {th_vars}								= ti_type_heaps
		  (type_variables, th_vars)				= getTypeVars [ct_result_type:arg_types] th_vars
		  (fresh_type_vars, th_vars)			= mapSt bind_to_fresh_type_variable type_variables th_vars
		  ti_type_heaps							= { ti_type_heaps & th_vars = th_vars }
		  (_, fresh_arg_types, ti_type_heaps)	= substitute arg_types ti_type_heaps
		  (_, fresh_result_type, ti_type_heaps)	= substitute ct_result_type ti_type_heaps
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
		  ti									= { ti & ti_type_heaps = ti_type_heaps }
		= (fun_type,ti)

removeNeverMatchingSubcases :: Expression !.ReadOnlyTI -> Expression
removeNeverMatchingSubcases keesExpr=:(Case kees) ro
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
				-> neverMatchingCase never_ident <-!- ("removeNeverMatchingSubcases:AlgebraicPatterns:neverMatchingCase",never_ident)
			| is_default_only filtered_default filtered_case_guards
				-> fromYes case_default
			-> Case {kees & case_guards = AlgebraicPatterns i filtered_case_guards, case_default = filtered_default }
		BasicPatterns bt basic_patterns
			| not (any (is_never_matching_case o get_basic_rhs) basic_patterns) && not (is_never_matching_default case_default)
				-> keesExpr // frequent case: all subexpressions can't fail
			# filtered_case_guards = filter (not o is_never_matching_case o get_basic_rhs) basic_patterns
			| has_become_never_matching filtered_default filtered_case_guards
				-> neverMatchingCase never_ident <-!- ("removeNeverMatchingSubcases:BasicPatterns:neverMatchingCase",never_ident)
			| is_default_only filtered_default filtered_case_guards
				-> fromYes case_default
			-> Case {kees & case_guards = BasicPatterns bt filtered_case_guards, case_default = filtered_default }
		OverloadedListPatterns i decons_expr alg_patterns
			| not (any (is_never_matching_case o get_alg_rhs) alg_patterns) && not (is_never_matching_default case_default)
				-> keesExpr // frequent case: all subexpressions can't fail
			# filtered_case_guards = filter (not o is_never_matching_case o get_alg_rhs) alg_patterns
			| has_become_never_matching filtered_default filtered_case_guards
				-> neverMatchingCase never_ident <-!- ("removeNeverMatchingSubcases:OverloadedListPatterns:neverMatchingCase",never_ident)
			| is_default_only filtered_default filtered_case_guards
				-> fromYes case_default
			-> Case {kees & case_guards = OverloadedListPatterns i decons_expr filtered_case_guards, case_default = filtered_default }
		_	-> abort "removeNeverMatchingSubcases does not match"
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
	never_ident = case ro.ro_root_case_mode of
		NotRootCase -> kees.case_ident
		_ -> Yes ro.ro_fun_case.symb_name
removeNeverMatchingSubcases expr ro
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
	transform NoPattern ro ti
		= (NoPattern, ti)
	transform _ ro ti
		= abort "transform CasePatterns does not match"

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

tryToFindInstance :: !{! Producer} !InstanceInfo !*(Heap FunctionInfo) -> *(!Bool, !FunctionInfoPtr, !InstanceInfo, !.FunctionHeap)
tryToFindInstance new_prods II_Empty fun_heap
	# (fun_def_ptr, fun_heap) = newPtr FI_Empty fun_heap
	= (cIsANewFunction, fun_def_ptr, II_Node new_prods fun_def_ptr II_Empty II_Empty, fun_heap)
tryToFindInstance new_prods instances=:(II_Node prods fun_def_ptr left right) fun_heap
	| size new_prods > size prods
		# (is_new, new_fun_def_ptr, right, fun_heap) = tryToFindInstance new_prods right fun_heap
		= (is_new, new_fun_def_ptr, II_Node prods fun_def_ptr left right, fun_heap)
	| size new_prods < size prods
		# (is_new, new_fun_def_ptr, left, fun_heap) = tryToFindInstance new_prods left fun_heap
		= (is_new, new_fun_def_ptr, II_Node prods fun_def_ptr left right, fun_heap)
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
		compare_constructor_arguments PR_Unused PR_Unused
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

generateFunction :: !SymbIdent !FunDef ![ConsClass] ![Bool] !{! Producer} !FunctionInfoPtr !ReadOnlyTI !*TransformInfo -> (!Index, !Int, !*TransformInfo)
generateFunction app_symb fd=:{fun_body = TransformedBody {tb_args,tb_rhs},fun_info = {fi_group_index}} 
				 cc_args cc_linear_bits prods fun_def_ptr ro
				 ti=:{ti_var_heap,ti_next_fun_nr,ti_new_functions,ti_fun_heap,ti_symbol_heap,ti_fun_defs,
				 		ti_type_heaps,ti_cons_args,ti_cleanup_info, ti_type_def_infos}
/*
	| False-!->("generating new function",fd.fun_symb.id_name,"->",ti_next_fun_nr)		= undef
	| False-!->("with type",fd.fun_type)												= undef
	| False-!->("producers:",II_Node prods nilPtr II_Empty II_Empty,("cc_args",cc_args,("cc_linear_bits",cc_linear_bits)))		= undef
	| False-!->("body:",tb_args, tb_rhs)												= undef
*/
	#!(fi_group_index, ti_cons_args, ti_fun_defs, ti_fun_heap)
			= max_group_index 0 prods ro.ro_main_dcl_module_n fi_group_index ti_fun_defs ti_fun_heap ti_cons_args

	# (Yes consumer_symbol_type)
			= fd.fun_type
	  (function_producer_types, ti_fun_defs, ti_fun_heap)
	  		= iFoldSt (accum_function_producer_type prods ro) 0 (size prods) 
	  				([], ti_fun_defs, ti_fun_heap)
	  consumer_symbol_type		= strip_universal_quantor consumer_symbol_type
	  function_producer_types	= mapOpt strip_universal_quantor function_producer_types
	  (sound_consumer_symbol_type, (ti_type_heaps, ti_type_def_infos))
	  		= add_propagation_attributes` ro.ro_common_defs consumer_symbol_type (ti_type_heaps, ti_type_def_infos)
	  (opt_sound_function_producer_types, (ti_type_heaps, ti_type_def_infos))
	  		= mapSt (add_propagation_attributes ro.ro_common_defs) function_producer_types (ti_type_heaps, ti_type_def_infos)
	  (opt_sound_function_producer_types, ti_type_heaps)
	  		= mapSt copy_opt_symbol_type opt_sound_function_producer_types
	  				ti_type_heaps

	  sound_function_producer_types		// nog even voor determine args....
	  		= [x \\ Yes x <- opt_sound_function_producer_types]

	# ({st_attr_vars,st_args,st_args_strictness,st_result,st_attr_env})
	  		= sound_consumer_symbol_type

	  (class_types, ti_fun_defs, ti_fun_heap)
	  		= iFoldSt (accum_class_type prods ro) 0 (size prods) 
	  				([], ti_fun_defs, ti_fun_heap)
	  (type_vars_in_class_types, th_vars)
	  		= mapSt getTypeVars class_types ti_type_heaps.th_vars

	  all_involved_types
	  		= class_types ++ (flatten (map (\{st_args, st_result}-> [st_result:st_args]) 
					  					[sound_consumer_symbol_type:sound_function_producer_types]))
//	| False ---> ("all_involved_types",app_symb,all_involved_types)	= undef
	# (propagating_cons_vars, th_vars)
	  		= collectPropagatingConsVars all_involved_types th_vars
	  all_type_vars
	  		=   flatten [st_vars \\ {st_vars} <- [sound_consumer_symbol_type:sound_function_producer_types]]
	  		  ++flatten type_vars_in_class_types
//	| False -!-> ("all_type_vars",all_type_vars)	= undef
	# (nr_of_all_type_vars, th_vars)
	  		=  foldSt bind_to_temp_type_var all_type_vars (0, th_vars)
	  subst
	  		= createArray nr_of_all_type_vars TE
	  (next_attr_nr, th_attrs)
	  		= foldSt bind_to_temp_attr_var st_attr_vars (FirstAttrVar, ti_type_heaps.th_attrs)
	  ti_type_heaps
	  		= { ti_type_heaps & th_attrs = th_attrs, th_vars = th_vars }
//	| False-!->("before substitute", st_args, "->", st_result)		= undef
	# (_, (st_args,st_result), ti_type_heaps)
	  		= substitute (st_args,st_result) ti_type_heaps
//	| False-!->("after substitute", st_args, "->", st_result)		= undef
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
			, das_predef					= ti.ti_predef_symbols
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
	  ti_predef_symbols			= das.das_predef
	  
	  new_fun_arity
	  		= length new_fun_args
	| SwitchArityChecks (new_fun_arity > 32) False
		# new_gen_fd =
			{	gf_fun_def			= fd
			,	gf_instance_info	= II_Empty
			,	gf_cons_args		= {cc_args = [], cc_size = 0, cc_linear_bits=[], cc_producer = False}
			,	gf_fun_index		= -1
			}
		# ti_fun_heap 	= ti_fun_heap <:= (fun_def_ptr, FI_Function new_gen_fd)
		# ti = { ti & ti_type_heaps = ti_type_heaps, ti_symbol_heap = ti_symbol_heap, ti_fun_defs = ti_fun_defs
				, ti_fun_heap = ti_fun_heap, ti_var_heap = ti_var_heap, ti_cons_args = ti_cons_args, ti_type_def_infos = ti_type_def_infos
				, ti_predef_symbols = ti_predef_symbols }
		| ro.ro_transform_fusion
			#  ti = { ti & ti_error_file = ti.ti_error_file <<< "Possibly missed fusion oppurtunity: Function Arity > 32 " <<< ro.ro_fun_root.symb_name.id_name <<< "\n"}
			= (-1,new_fun_arity,ti)
		= (-1,new_fun_arity,ti)
	# new_arg_types = flatten [ ats_types \\ {ats_types}<-:new_arg_types_array ]
	  
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
//	| False-!->("unified type", new_arg_types, "->", st_result)		= undef
//	| False-!->("coercions", readableCoercions coercions)			= undef

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
	  new_fun_type
	  		= Yes
	  			{ st_vars		= all_fresh_type_vars
	  			, st_args		= fresh_arg_types
	  			, st_args_strictness=new_args_strictness
	  			, st_arity		= new_fun_arity
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
	  		= { fd & fun_body = Expanding new_fun_args, fun_arity = new_fun_arity,fun_type=new_fun_type, 
	  					fun_info.fi_group_index = fi_group_index
/* DvA... STRICT_LET
					,fun_info.fi_free_vars = strict_free_vars++fd.fun_info.fi_free_vars
...DvA */
	  					}
	  new_fd_cons_args
//	  		= {cc_args = new_cons_args, cc_size = length new_cons_args, cc_linear_bits=new_linear_bits, cc_producer = False}
	  		= {cc_args = repeatn (length new_cons_args) CPassive, cc_size = length new_cons_args, cc_linear_bits=new_linear_bits, cc_producer = False}
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
	  us 	=	{ us_var_heap				= ti_var_heap
	  			, us_symbol_heap			= ti_symbol_heap
	  			, us_opt_type_heaps			= Yes { ti_type_heaps & th_vars = th_vars }
	  			, us_cleanup_info			= ti_cleanup_info
	  			, us_local_macro_functions	= No 
	  			}
 	  ui	=	{ ui_handle_aci_free_vars	= RemoveThem
 	  			}
//	| False ---> ("before unfold:", tb_rhs) = undef
	# (tb_rhs, {us_var_heap,us_symbol_heap,us_opt_type_heaps=Yes ti_type_heaps, us_cleanup_info})
	  		= unfold tb_rhs ui us
//	| False ---> ("unfolded:", tb_rhs) = undef
//*999
	# us_var_heap						= fold2St store_arg_type_info new_fun_args fresh_arg_types us_var_heap
		with
			store_arg_type_info {fv_info_ptr} a_type ti_var_heap
				= setExtendedVarInfo fv_info_ptr (EVI_VarType a_type) ti_var_heap
//*/
	# ro_fun= { symb_name = fd.fun_symb, symb_kind = SK_GeneratedFunction fun_def_ptr ti_next_fun_nr }
	# ro_root_case_mode = case tb_rhs of 
	  						Case _
	  							-> RootCase
	  						_	-> NotRootCase
	
	# (args1,resto,restn,us_var_heap) = take1 tb_args new_fun_args us_var_heap
		with
			take1 [o:os] [n:ns] us_var_heap
				# (vi,us_var_heap) = readVarInfo o.fv_info_ptr us_var_heap
				# eq = case vi of
					VI_Variable _ fip	-> fip == n.fv_info_ptr
					_					-> False
				| eq
					# (ts,os,ns,us_var_heap)	= take1 os ns us_var_heap
					= ([o:ts],os,ns,us_var_heap)
					= ([],[o:os],[n:ns],us_var_heap)
			take1 os ns us_var_heap = ([],os,ns,us_var_heap)
	# (args2o,args2n,resto,restn,us_var_heap) = take2 resto restn us_var_heap
		with
			take2 [] [] us_var_heap = ([],[],[],[],us_var_heap)
			take2 os ns us_var_heap
				# (os`,us_var_heap) = extend os us_var_heap 
				# os`` = map fst os`
				# ns`` = map (\{fv_info_ptr}->fv_info_ptr) ns
				# condO = \(o,_) -> not (isMember o ns``)
				# condN = \{fv_info_ptr} -> not (isMember fv_info_ptr os``)
				# (ao`,ro`) = (takeWhile condO os`, dropWhile condO os`)
				# (an,rn) = (takeWhile condN ns, dropWhile condN ns)
				# ao = shrink ao`
				# ro = shrink ro`
				= (ao,an,ro,rn,us_var_heap)
			where
				extend os uvh	= seqList (map ext os) uvh
				ext o uvh
					# (vi,uvh) = readVarInfo o.fv_info_ptr uvh
					= case vi of
						VI_Variable _ fip	-> ((fip,o),uvh)
						_					-> ((nilPtr,o),uvh)
				shrink as = map snd as

				isMember x [hd:tl]
					| isNilPtr x	= False
					| isNilPtr hd	= isMember x tl
					= hd==x || isMember x tl
				isMember x []	= False

	# (args3,resto,restn,us_var_heap) = take1 resto restn us_var_heap
		with
			take1 [o:os] [n:ns] us_var_heap
				# (vi,us_var_heap) = readVarInfo o.fv_info_ptr us_var_heap
				# eq = case vi of
					VI_Variable _ fip	-> fip == n.fv_info_ptr
					_					-> False
				| eq
					# (ts,os,ns,us_var_heap)	= take1 os ns us_var_heap
					= ([o:ts],os,ns,us_var_heap)
					= ([],[o:os],[n:ns],us_var_heap)
			take1 os ns us_var_heap = ([],os,ns,us_var_heap)
/*			take1 [] [] = ([],[],[])
			take1 [o:os] [n:ns]
				| o.fv_info_ptr == n.fv_info_ptr
					# (ts,os,ns)	= take1 os ns
					= ([o:ts],os,ns)
					= ([],[o:os],[n:ns])
*/
	| False -!-> ("genFun",(tb_args,new_fun_args),args1,(args2o,args2n),args3,(resto,restn)) = undef
	| not (isEmpty resto)	= abort "genFun:resto"
	| not (isEmpty restn)	= abort "genFun:restn"
	# ro 	=	{ ro &	ro_root_case_mode = ro_root_case_mode,
						ro_fun_root = ro_fun,
						ro_fun_case = ro_fun,
						ro_fun_orig = app_symb,
						ro_fun_args = new_fun_args,
						ro_fun_geni = (length args1,length args2n)
				}
//	| False ---> ("transform generated function:",ti_next_fun_nr,ro_root_case_mode)		= undef
//	| False -!-> ("transforming new function:",ti_next_fun_nr)		= undef
//	| False -!-> ("transforming new function:",tb_rhs)		= undef
	# ti
			= { ti & ti_var_heap = us_var_heap, ti_fun_heap = ti_fun_heap, ti_symbol_heap = us_symbol_heap,
	  			ti_next_fun_nr = inc ti_next_fun_nr, ti_type_def_infos = ti_type_def_infos,
	  			ti_new_functions = [fun_def_ptr : ti_new_functions], ti_fun_defs = ti_fun_defs,
	  			ti_type_heaps = ti_type_heaps, ti_cleanup_info = us_cleanup_info, 
	  			ti_cons_args = ti_cons_args,
	  			ti_predef_symbols = ti_predef_symbols }
	# ti = arity_warning "generateFunction" fd.fun_symb.id_name ti_next_fun_nr new_fun_arity ti

	  (new_fun_rhs, ti)
			= transform tb_rhs ro ti
	  new_fd
	  		= { new_fd_expanding & fun_body = TransformedBody {tb_args = new_fun_args, tb_rhs = new_fun_rhs} }
//	| False -!-> ("generated function", new_fd, new_cons_args)		= undef

	# new_gen_fd = { new_gen_fd & gf_fun_def = new_fd, gf_cons_args = new_fd_cons_args}
	# (new_gen_fd,fun_defs,var_heap,fun_heap,cons_args)
		= SwitchReanalyseFunction
					(reanalyse_function new_gen_fd ti_next_fun_nr ti.ti_cons_args ti.ti_fun_heap ti.ti_fun_defs ti.ti_var_heap fi_group_index new_fun_rhs
					)
					(new_gen_fd,ti.ti_fun_defs,ti.ti_var_heap,ti.ti_fun_heap,ti.ti_cons_args)

	# ti =
		{ ti
		& ti_fun_heap 	= fun_heap <:= (fun_def_ptr, FI_Function new_gen_fd)
		, ti_cons_args	= cons_args
		, ti_fun_defs	= fun_defs
		, ti_var_heap	= var_heap
		}
	= (ti_next_fun_nr, new_fun_arity, ti)
where
	reanalyse_function new_gen_fd ti_next_fun_nr ti_cons_args ti_fun_heap ti_fun_defs ti_var_heap fi_group_index new_fun_rhs
		# prs	=
			{ prs_group				= [dec ti_next_fun_nr]
			, prs_cons_args 		= ti_cons_args
			, prs_main_dcl_module_n	= ro.ro_main_dcl_module_n
			, prs_fun_heap			= ti_fun_heap
			, prs_fun_defs			= ti_fun_defs
			, prs_group_index		= fi_group_index
			}
		# (safe,prs)	= producerRequirements new_fun_rhs prs
		# (new_fd_cons_args`,fun_defs,var_heap,fun_heap,cons_args) = reanalyseFunction
					ti_next_fun_nr
					fun_def_ptr
					ro.ro_common_defs
					ro.ro_imported_funs
					ro.ro_main_dcl_module_n
					ro.ro_stdStrictLists_module_n
					prs.prs_fun_defs
					ti_var_heap
					(prs.prs_fun_heap <:= (fun_def_ptr, FI_Function new_gen_fd))
					prs.prs_cons_args
		# new_gen_fd = { new_gen_fd & gf_cons_args = {new_fd_cons_args` & cc_producer = safe}}
		= (new_gen_fd,fun_defs,var_heap,fun_heap,cons_args)

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
	add_propagation_attributes common_defs (Yes st) state
		# (st, state)	= add_propagation_attributes` common_defs st state
		= (Yes st, state)

	add_propagation_attributes` common_defs st=:{st_args, st_result, st_attr_env, st_attr_vars}
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
		= (sound_symbol_type, state)

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
			PR_Unused
				-> ([No:type_accu], ti_fun_defs, ti_fun_heap)
			producer
				# (symbol,_) = get_producer_symbol producer
				  (symbol_type, ti_fun_defs, ti_fun_heap)
						= get_producer_type symbol ro ti_fun_defs ti_fun_heap
				-> ([Yes symbol_type:type_accu], ti_fun_defs, ti_fun_heap)

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

// get_producer_type retrieves the type of symbol
get_producer_type :: !SymbIdent !.ReadOnlyTI !*{#FunDef} !*FunctionHeap -> (!SymbolType,!*{#FunDef},!*FunctionHeap)
get_producer_type {symb_kind=SK_Function {glob_module, glob_object}} ro fun_defs fun_heap
	| glob_module == ro.ro_main_dcl_module_n
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
	, das_predef					:: !*PredefinedSymbols
	}

determine_args
	:: ![Bool] ![ConsClass] !Index !{!Producer} ![Optional SymbolType] ![FreeVar] !ReadOnlyTI !*DetermineArgsState
	-> *DetermineArgsState
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
//	# producer	= if (cons_arg == CActive) (producers.[prod_index]) PR_Empty
	# producer	= case cons_arg of
					CActive		-> producers.[prod_index]
					CUnused		-> producers.[prod_index]
					_			-> PR_Empty
	= determine_arg producer prod_atype form prod_index ((linear_bit,cons_arg), input) das

determine_arg
	:: !Producer .(Optional SymbolType) !FreeVar .Int !(!(!Bool,!ConsClass),!ReadOnlyTI) !*DetermineArgsState
	-> *DetermineArgsState

determine_arg PR_Empty _ form=:{fv_name,fv_info_ptr} _ ((linear_bit,cons_arg), _) das=:{das_var_heap}
	# (new_info_ptr, das_var_heap)	= newPtr VI_Empty das_var_heap
	# das_var_heap					= writeVarInfo fv_info_ptr (VI_Variable fv_name new_info_ptr) das_var_heap
	=	{ das 
		& das_vars				= [{ form & fv_info_ptr = new_info_ptr } : das.das_vars ]
		, das_new_linear_bits	= [ linear_bit : das.das_new_linear_bits ]
		, das_new_cons_args		= [ cons_arg : das.das_new_cons_args ]
		, das_var_heap			= das_var_heap
		}

determine_arg PR_Unused _ form=:{fv_name,fv_info_ptr} prod_index (_,ro) das=:{das_var_heap}
	# no_arg_type				= { ats_types= [], ats_strictness = NotStrict }
	=	{ das
		& das_arg_types.[prod_index] = no_arg_type
		}

determine_arg (PR_Class class_app free_vars_and_types class_type) _ {fv_info_ptr,fv_name} prod_index (_,ro)
			  das=:{das_arg_types, das_subst, das_type_heaps, das_predef}
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
	# ({pds_module,pds_def},das_predef) = das_predef![PD_TypeGenericDict]
	# genericGlobalIndex	= {glob_module = pds_module, glob_object = pds_def}
	# (succ, das_subst, das_type_heaps)
		//AA: = unify class_atype arg_type type_input das_subst das_type_heaps
		= unify_dict class_atype arg_type type_input das_subst das_type_heaps
		with
			unify_dict class_atype=:{at_type=TA type_symb1 args1} arg_type=:{at_type=TA type_symb2 args2} 
				| type_symb1 == type_symb2 
					= unify class_atype arg_type
				// FIXME: check indexes, not names. Need predefs for that. 	
//				| type_symb1.type_name.id_name == "GenericDict"
				| type_symb1.type_index == genericGlobalIndex
					= unify {class_atype & at_type = TA type_symb2 args1} arg_type	
//				| type_symb2.type_name.id_name == "GenericDict"
				| type_symb2.type_index == genericGlobalIndex
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
		, das_new_cons_args		= mapAppend (\_ -> CActive) free_vars_and_types das.das_new_cons_args
		, das_subst				= das_subst
		, das_type_heaps		= das_type_heaps
		, das_var_heap			= writeVarInfo fv_info_ptr (VI_Dictionary class_app.app_symb class_app.app_args class_type) das.das_var_heap
		, das_predef			= das_predef
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
	  (application_type, attr_env, das_next_attr_nr)
	  		= build_application_type st_arity (length st_context) st_result st_args nr_of_applied_args [] das_next_attr_nr
	  type_input
	  		= { ti_common_defs			= ro.ro_common_defs
	  		  , ti_functions			= ro.ro_imported_funs
			  ,	ti_main_dcl_module_n	= ro.ro_main_dcl_module_n
			  }
	# (succ, das_subst, das_type_heaps)
	  		= unify application_type arg_type type_input das_subst das_type_heaps
	| not succ
		= abort "sanity check nr 94 in module trans failed\n"
	# (attr_inequalities, das_type_heaps)
			= accAttrVarHeap (mapSt substitute_attr_inequality st_attr_env) das_type_heaps
	  new_uniqueness_requirement
	  		= { ur_offered		= application_type
	  		  , ur_demanded		= arg_type
//	  		  , ur_attr_ineqs	= attr_inequalities 
	  		  , ur_attr_ineqs	= attr_inequalities ++ attr_env
	  		  }
	  (opt_body, var_names, das_fun_defs, das_fun_heap)
	  		= case producer of
	  			(PR_Constructor {symb_kind=SK_Constructor {glob_module}} arity _)
  					-> (NoBody, repeatn arity { id_name = "_x", id_info = nilPtr }, das_fun_defs, das_fun_heap)
	  			(PR_Curried {symb_kind=SK_Function {glob_module}} arity)
	  				| glob_module <> ro.ro_main_dcl_module_n
	  					// we do not have good names for the formal variables of that function: invent some
	  					-> (NoBody, repeatn arity { id_name = "_x", id_info = nilPtr }, das_fun_defs, das_fun_heap)
	  			(PR_Curried _ arity)
					# ({fun_body}, das_fun_defs, das_fun_heap)
							= get_fun_def symbol.symb_kind ro.ro_main_dcl_module_n das_fun_defs das_fun_heap
					-> case fun_body of
						(TransformedBody tb)
							-> (NoBody, take nr_of_applied_args [ fv_name \\ {fv_name}<-tb.tb_args ], das_fun_defs, das_fun_heap)
						_
							-> (NoBody, repeatn arity { id_name = "_x", id_info = nilPtr }, das_fun_defs, das_fun_heap)
	  			_
					# ({fun_body}, das_fun_defs, das_fun_heap)
							= get_fun_def symbol.symb_kind ro.ro_main_dcl_module_n das_fun_defs das_fun_heap
					-> case fun_body of
						(TransformedBody tb)
							-> (fun_body, take nr_of_applied_args [ fv_name \\ {fv_name}<-tb.tb_args ], das_fun_defs, das_fun_heap)
						_
							-> abort ("determine_args:not a Transformed Body:"--->("producer",producer))
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
				# cc_args = copy_classes symbol_arity cons_classes.cc_args
				-> ({ cc_size			= symbol_arity
					, cc_args			= cc_args
					, cc_linear_bits	= if curried
											(repeatn symbol_arity linear_bit)
											(take symbol_arity cons_classes.cc_linear_bits)
					, cc_producer		= False
					}
		  			, fun_heap, ti_cons_args)
			No
				-> ({ cc_size			= symbol_arity
					, cc_args			= repeatn symbol_arity CPassive
					, cc_linear_bits	= repeatn symbol_arity linear_bit
					, cc_producer		= False
					}
					, fun_heap, ti_cons_args)

	copy_classes 0 _ = []
	copy_classes n [cc:ccs]
		= case cc of
			CUnused		-> [CActive:copy_classes (dec n) ccs]
			cc			-> [cc:copy_classes (dec n) ccs]

/*
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
*/
	build_application_type st_arity nr_context_args st_result st_args nr_of_applied_args attr_env attr_store
		| st_arity+nr_context_args==nr_of_applied_args
			= (st_result, attr_env, attr_store)
		| nr_of_applied_args<nr_context_args
			= abort "sanity check nr 234 failed in module trans"
		# req_arity	= nr_of_applied_args - nr_context_args

		= currySymbolType st_args st_arity st_result attr_env req_arity attr_store
/*
		# (type`,attr_env`,attr_store`)
			= currySymbolType st_args st_arity st_result attr_env req_arity attr_store
		# (applied_args, unapplied_args) = splitAt req_arity st_args
		  attr_approx = if (any has_unique_attribute applied_args) TA_Unique TA_Multi			// DvA: should be var instead of multi...
		# type = foldr (\atype1 atype2->{at_attribute=attr_approx, at_type=atype1-->atype2})
				st_result unapplied_args
		| False ---> ("build",type,type`) = undef
//		= (type, attr_env, attr_store)
		= (type`, attr_env`, attr_store`)
	  where
		has_unique_attribute {at_attribute=TA_Unique} = True
		has_unique_attribute _ = False
*/
// DvA: from type.icl...
currySymbolType tst_args tst_arity tst_result tst_attr_env req_arity ts_attr_store
	| tst_arity == req_arity
		= (tst_result, tst_attr_env, ts_attr_store)
	# (tst_args, rest_args, is_unique)			= split_args req_arity tst_args 
	| is_unique
		# (type, _, _)							= buildCurriedType rest_args tst_result TA_Unique [] 0
		= (type, tst_attr_env, ts_attr_store)
		# tst_attr_env							= build_attr_env ts_attr_store tst_args tst_attr_env
		# (type, tst_attr_env, ts_attr_store)	= buildCurriedType rest_args tst_result (TA_TempVar ts_attr_store)
		  												tst_attr_env (inc ts_attr_store)
		= (type, tst_attr_env, ts_attr_store)
where
	split_args 0 args = ([], args, False)
	split_args n [atype=:{at_attribute} : args]
		# (left, right, is_unique) = split_args (dec n) args
		= ([ atype : left ], right, is_unique || attr_is_unique at_attribute)
	
	attr_is_unique TA_Unique = True
	attr_is_unique _ = False
	
	build_attr_env cum_attr_var [] attr_env
		= attr_env
	build_attr_env cum_attr_var [{at_attribute=(TA_TempVar attr_var)} : args] attr_env
		# attr_env = [{ ac_demanded = attr_var, ac_offered = cum_attr_var } : attr_env]
		= build_attr_env cum_attr_var args attr_env
	build_attr_env cum_attr_var [_ : args] attr_env
		= build_attr_env cum_attr_var args attr_env

buildCurriedType [] type cum_attr attr_env attr_store
	= (type, attr_env, attr_store)
buildCurriedType [at=:{at_attribute}:ats] type cum_attr attr_env attr_store
	# (next_cum_attr, attr_env, attr_store) = combine_attributes at_attribute cum_attr attr_env attr_store
	  (res_type, attr_env, attr_store) = buildCurriedType ats type next_cum_attr attr_env attr_store
	= ({at_attribute = cum_attr , at_type = at --> res_type }, attr_env, attr_store)
where
	combine_attributes TA_Unique cum_attr attr_env attr_store
		= (TA_Unique, attr_env, attr_store)
	combine_attributes (TA_TempVar attr_var) (TA_TempVar cum_attr_var) attr_env attr_store
		# attr_env =
			[{ ac_demanded = cum_attr_var,ac_offered = attr_store }
			,{ ac_demanded = attr_var,ac_offered = attr_store }
			:attr_env]
		= (TA_TempVar attr_store, attr_env, inc attr_store)
	combine_attributes (TA_TempVar _) cum_attr attr_env attr_store
		= (cum_attr, attr_env, attr_store)
	combine_attributes _ (TA_TempVar cum_attr_var) attr_env attr_store
		# attr_env = [{ ac_demanded = cum_attr_var,ac_offered = attr_store }:attr_env]
		= (TA_TempVar attr_store, attr_env, inc attr_store)
	combine_attributes _ cum_attr attr_env attr_store
		= (cum_attr, attr_env, attr_store)

freshAttrVar attr_var th_attrs
	# (new_info_ptr, th_attrs) = newPtr AVI_Empty th_attrs
	= ({ av_name = NewAttrVarId attr_var, av_info_ptr = new_info_ptr }, th_attrs)


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
	max_group_index_of_producer PR_Unused current_max fun_defs fun_heap cons_args
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

transformFunctionApplication :: FunDef InstanceInfo !ConsClasses !App [Expression] ReadOnlyTI !*TransformInfo -> *(Expression,!*TransformInfo)
transformFunctionApplication fun_def instances cc=:{cc_size, cc_args, cc_linear_bits} app=:{app_symb,app_args} extra_args ro ti
	# (app_args, extra_args) = complete_application fun_def.fun_arity app_args extra_args
//	| False -!-> ("transformFunctionApplication",app_symb,app_args,extra_args,fun_def.fun_arity,cc_size) = undef
	| expanding_consumer
	 	= (build_application { app & app_args = app_args } extra_args, ti)
	| cc_size == 0
		# {fun_body=fun_body=:TransformedBody {tb_rhs}, fun_kind} = fun_def
		| SwitchTransformConstants (ro.ro_transform_fusion && is_not_caf fun_kind && is_sexy_body tb_rhs) False
			= transform_trivial_function app app_args extra_args ro ti
		= (build_application { app & app_args = app_args } extra_args, ti)
	| cc_size >= 0
		# is_applied_to_macro_fun = fun_def.fun_info.fi_properties bitand FI_IsMacroFun <> 0
	  	# consumer_is_curried = cc_size <> length app_args
		# non_rec_consumer
			= (fun_def.fun_info.fi_properties bitand FI_IsNonRecursive) <> 0 with FI_IsNonRecursive = 4
		# safe_args
			= isEmpty [arg \\ arg <- app_args & cc_arg <- cc_args | unsafe cc_arg && non_var arg]
						with
							unsafe CAccumulating			= True
							unsafe CVarOfMultimatchCase		= True
							unsafe _						= False
							
							non_var (Var _)					= False
							non_var _						= True
	  	# ok_non_rec_consumer	= non_rec_consumer && safe_args
	  	# (producers, new_args, ti)
	  		= determineProducers is_applied_to_macro_fun consumer_is_curried ok_non_rec_consumer fun_def.fun_type cc_linear_bits cc_args app_args 0 (createArray cc_size PR_Empty) ro ti
		# (arity_changed,new_args,extra_args,producers,cc_args,cc_linear_bits,fun_def,ti)
			= determineCurriedProducersInExtraArgs new_args extra_args is_applied_to_macro_fun producers cc_args cc_linear_bits fun_def ro ti
	  	| containsProducer cc_size producers || arity_changed
	  		# (is_new, fun_def_ptr, instances, ti_fun_heap) = tryToFindInstance producers instances ti.ti_fun_heap
	  		| is_new
	  			# ti							= update_instance_info app_symb.symb_kind instances { ti & ti_fun_heap = ti_fun_heap }
	  			# (fun_index, fun_arity, ti)	= generateFunction app_symb fun_def cc_args cc_linear_bits producers fun_def_ptr ro ti
				| fun_index == (-1)
					= (build_application { app & app_args = app_args } extra_args, ti)
	  			# app_symb = { app_symb & symb_kind = SK_GeneratedFunction fun_def_ptr fun_index }
				# (app_args, extra_args) = complete_application fun_arity new_args extra_args
	  			= transformApplication { app & app_symb = app_symb, app_args = app_args } extra_args ro ti
  			# (FI_Function {gf_fun_index, gf_fun_def}, ti_fun_heap) = readPtr fun_def_ptr ti_fun_heap
			| gf_fun_index == (-1)
				= (build_application { app & app_args = app_args } extra_args, ti)
			# app_symb` = { app_symb & symb_kind = SK_GeneratedFunction fun_def_ptr gf_fun_index }
			  (app_args, extra_args) = complete_application gf_fun_def.fun_arity new_args extra_args
  			# ti = {ti & ti_fun_heap = ti_fun_heap }
  			= transformApplication { app & app_symb = app_symb`, app_args = app_args } extra_args ro ti
		| SwitchTrivialFusion ro.ro_transform_fusion False
			= transform_trivial_function app app_args extra_args ro ti
		= (build_application { app & app_args = app_args } extra_args, ti)
	= (build_application { app & app_args = app_args } extra_args, ti)
where
	expanding_consumer = case fun_def.fun_body of
								Expanding _	-> True
								_			-> False

	is_not_caf FK_Caf	= False
	is_not_caf _		= True

	transform_trivial_function app=:{app_symb} app_args extra_args ro ti
		# (fun_def,ti_fun_defs,ti_fun_heap)		= get_fun_def app_symb.symb_kind ro.ro_main_dcl_module_n ti.ti_fun_defs ti.ti_fun_heap
		# {fun_body=fun_body=:TransformedBody {tb_args,tb_rhs},fun_type} = fun_def
		# (opt_expr, ti_fun_defs, ti_fun_heap, ti_type_heaps, ti_cons_args)
												= is_trivial_body tb_args tb_rhs app_args fun_type ro ti_fun_defs ti_fun_heap ti.ti_type_heaps ti.ti_cons_args
		# ti									= { ti & ti_fun_defs = ti_fun_defs, ti_fun_heap = ti_fun_heap, ti_type_heaps = ti_type_heaps, ti_cons_args = ti_cons_args }
		= case opt_expr of
			No		
					-> (build_application { app & app_symb = app_symb, app_args = app_args } extra_args, ti)
			(Yes tb_rhs)
				| isEmpty extra_args
					-> (tb_rhs, ti)
					-> (tb_rhs @ extra_args, ti)

	update_instance_info (SK_Function {glob_object}) instances ti=:{ti_instances}
		 = { ti & ti_instances = { ti_instances & [glob_object] = instances } }
	update_instance_info (SK_LocalMacroFunction glob_object) instances ti=:{ti_instances}
		 = { ti & ti_instances = { ti_instances & [glob_object] = instances } }
	update_instance_info (SK_GeneratedFunction fun_def_ptr fun_index) instances ti=:{ti_fun_heap, ti_instances}
		| fun_index < size ti_instances
			= { ti & ti_instances = { ti_instances & [fun_index] = instances } }
		# (FI_Function fun_info, ti_fun_heap) = readPtr fun_def_ptr ti_fun_heap
		= { ti & ti_fun_heap = ti_fun_heap <:= (fun_def_ptr, FI_Function { fun_info & gf_instance_info = instances })}

	complete_application form_arity args extra_args
		= (take form_arity all_args,drop form_arity all_args)
	where
		all_args = args ++ extra_args

	build_application app []
		= App app
	build_application app extra_args
		= App app @ extra_args
		
is_cons_or_decons_of_UList_or_UTSList glob_object glob_module imported_funs
	:== let  type = imported_funs.[glob_module].[glob_object].ft_type;
		  in type.st_arity>0 && not (isEmpty type.st_context);

determineCurriedProducersInExtraArgs new_args [] is_applied_to_macro_fun producers cc_args cc_linear_bits fun_def ro ti
	= (False,new_args,[],producers,cc_args,cc_linear_bits,fun_def,ti)
determineCurriedProducersInExtraArgs new_args extra_args is_applied_to_macro_fun producers cc_args cc_linear_bits fun_def ro ti
	| not (SwitchExtraCurriedFusion ro.ro_transform_fusion is_applied_to_macro_fun)
		= (False,new_args,extra_args,producers,cc_args,cc_linear_bits,fun_def,ti)
	# n_extra_args													= length extra_args
	# {fun_type = Yes symbol_type=:{st_args,st_result,st_arity}}	= fun_def
	# (ok,new_args_types,new_result_type)							= get_new_args_types_from_result_type st_result n_extra_args
	| not ok
		= (False,new_args,extra_args,producers,cc_args,cc_linear_bits,fun_def,ti)
	# symbol_type	= {symbol_type & st_result=new_result_type,st_args=st_args++new_args_types,st_arity=st_arity+n_extra_args}
	# fun_def							= {fun_def & fun_type=Yes symbol_type}
	# (form_args,act_args,var_heap)		= create_new_args n_extra_args ti.ti_var_heap
	# ti								= {ti & ti_var_heap=var_heap}
	# (fun_body,ti)						= add_args_to_fun_body form_args act_args new_result_type fun_def.fun_body ro ti
	# fun_def							= {fun_def & fun_body=fun_body}
	# new_producers						= arrayPlusList producers [PR_Empty \\ i<-[0..n_extra_args-1]]
	# new_cc_args						= cc_args ++ [CPassive \\ i<-[0..n_extra_args-1]]
	# new_cc_linear_bits				= cc_linear_bits ++ [True \\ i<-[0..n_extra_args-1]]
	= (True,new_args++extra_args,[],new_producers,new_cc_args,new_cc_linear_bits,fun_def,ti)
where
	get_new_args_types_from_result_type type 0
		= (True,[],type)
	get_new_args_types_from_result_type {at_type=a-->b} n
		# (ok,args_types,result_type) = get_new_args_types_from_result_type b (n-1)
		= (ok,[a:args_types],result_type)
	get_new_args_types_from_result_type type _
		= (False,[],type)

	create_new_args n_new_args var_heap
		| n_new_args==0
			= ([], [], var_heap)            
		# new_name				= { id_name = "_a", id_info = nilPtr }
		  (info_ptr, var_heap)	= newPtr VI_Empty var_heap
		  form_var				= { fv_name = new_name, fv_info_ptr = info_ptr, fv_count = 0, fv_def_level = NotALevel }
		  act_var				= { var_name = new_name, var_info_ptr = info_ptr, var_expr_ptr = nilPtr }
		  (form_vars,act_vars,var_heap)
		  						= create_new_args (n_new_args-1) var_heap
		= ([form_var : form_vars],[Var act_var : act_vars],var_heap)

	add_args_to_fun_body form_args act_args new_result_type (TransformedBody {tb_args,tb_rhs}) ro ti
		# tb_args		= tb_args ++ form_args
		# (tb_rhs,ti)	= add_arguments tb_rhs act_args new_result_type ro ti
		= (TransformedBody {tb_args=tb_args,tb_rhs=tb_rhs},ti)

	add_arguments (App app=:{app_symb,app_args}) extra_args new_result_type ro ti
		# (form_arity,fun_defs,fun_heap) = get_arity app_symb ro ti.ti_fun_defs ti.ti_fun_heap
		# ti = {ti & ti_fun_defs=fun_defs,ti_fun_heap=fun_heap}
		# ar_diff = form_arity - length app_args
		| length extra_args <= ar_diff
			= (App {app & app_args = app_args ++ extra_args }, ti)
			= (App {app & app_args = app_args ++ take ar_diff extra_args } @ drop ar_diff extra_args, ti)
	add_arguments (Case kees=:{case_guards,case_default,case_info_ptr}) extra_args new_result_type ro ti
		# (case_default, ti)	= add_arguments_opt case_default extra_args new_result_type ro ti
		# (case_guards, ti)		= add_arguments_guards case_guards extra_args new_result_type ro ti
		# ti_symbol_heap		= overwrite_result_type case_info_ptr new_result_type ti.ti_symbol_heap
		# ti					= {ti & ti_symbol_heap = ti_symbol_heap}
		= (Case {kees & case_guards = case_guards, case_default = case_default}, ti)
	where
		overwrite_result_type case_info_ptr new_result_type ti_symbol_heap
			#! (EI_CaseType case_type, ti_symbol_heap)	= readExprInfo case_info_ptr ti_symbol_heap
			= writeExprInfo case_info_ptr (EI_CaseType { case_type & ct_result_type = new_result_type}) ti_symbol_heap
	add_arguments (Let lad=:{let_expr}) extra_args new_result_type ro ti
		# (let_expr, ti)		= add_arguments let_expr extra_args new_result_type ro ti
		= (Let {lad & let_expr = let_expr}, ti)
	add_arguments (expr1 @ expr2) extra_args _ ro ti
		= (expr1 @ (expr2++extra_args),ti)
	add_arguments expr extra_args _ ro ti
		= (expr @ extra_args,ti)
	
	add_arguments_opt No _ _ ro ti = (No,ti)
	add_arguments_opt (Yes expr) extra_args new_result_type ro ti
		# (expr, ti)	= add_arguments expr extra_args new_result_type ro ti
		= (Yes expr,ti)
	
	add_arguments_guards (AlgebraicPatterns gindex apats) extra_args new_result_type ro ti
		# (apats, ti)	= add_arguments_apats apats extra_args new_result_type ro ti
		= (AlgebraicPatterns gindex apats, ti)
	add_arguments_guards (BasicPatterns btype bpats) extra_args new_result_type ro ti
		# (bpats, ti)	= add_arguments_bpats bpats extra_args new_result_type ro ti
		= (BasicPatterns btype bpats, ti)
	add_arguments_guards (DynamicPatterns dpats) extra_args new_result_type ro ti
		# (dpats, ti)	= add_arguments_dpats dpats extra_args new_result_type ro ti
		= (DynamicPatterns dpats, ti)
	add_arguments_guards (OverloadedListPatterns type decons_expr apats) extra_args new_result_type ro ti
		# (apats, ti)	= add_arguments_apats apats extra_args new_result_type ro ti
		= (OverloadedListPatterns type decons_expr apats, ti)
	add_arguments_guards NoPattern extra_args _ ro ti
		= (NoPattern, ti)
	
	add_arguments_apats [] extra_args _ ro ti = ([],ti)
	add_arguments_apats [ap=:{ap_expr}:aps] extra_args new_result_type ro ti
		# (ap_expr, ti)	= add_arguments ap_expr extra_args new_result_type ro ti
		# (aps, ti)	= add_arguments_apats aps extra_args new_result_type ro ti
		= ([{ap & ap_expr = ap_expr}:aps],ti)

	add_arguments_bpats [] extra_args _ ro ti = ([],ti)
	add_arguments_bpats [bp=:{bp_expr}:bps] extra_args new_result_type ro ti
		# (bp_expr, ti)	= add_arguments bp_expr extra_args new_result_type ro ti
		# (bps, ti)	= add_arguments_bpats bps extra_args new_result_type ro ti
		= ([{bp & bp_expr = bp_expr}:bps],ti)

	add_arguments_dpats [] extra_args _ ro ti = ([],ti)
	add_arguments_dpats [dp=:{dp_rhs}:dps] extra_args new_result_type ro ti
		# (dp_rhs, ti)	= add_arguments dp_rhs extra_args new_result_type ro ti
		# (dps, ti)	= add_arguments_dpats dps extra_args new_result_type ro ti
		= ([{dp & dp_rhs = dp_rhs}:dps],ti)

	get_arity {symb_kind=SK_Function {glob_module, glob_object}} ro fun_defs fun_heap
		| glob_module == ro.ro_main_dcl_module_n
			# (fun_arity, fun_defs) = fun_defs![glob_object].fun_arity
			= (fun_arity, fun_defs, fun_heap)
		# {ft_arity,ft_type} = ro.ro_imported_funs.[glob_module].[glob_object]
		= (ft_arity + length ft_type.st_context, fun_defs, fun_heap)
	get_arity {symb_kind=SK_LocalMacroFunction glob_object} ro fun_defs fun_heap
		# (fun_arity, fun_defs) = fun_defs![glob_object].fun_arity
		= (fun_arity, fun_defs, fun_heap)
	get_arity {symb_kind=SK_GeneratedFunction fun_ptr _} ro fun_defs fun_heap
		# (FI_Function {gf_fun_def={fun_arity}}, fun_heap) = readPtr fun_ptr fun_heap
		= (fun_arity, fun_defs, fun_heap)
	get_arity {symb_kind=SK_Constructor {glob_module, glob_object}} ro fun_defs fun_heap
		# arity = ro.ro_common_defs.[glob_module].com_cons_defs.[glob_object].cons_type.st_arity
		= (arity, fun_defs, fun_heap)

//@ is_trivial_body

:: *MatchState =
	{ tvar_map			:: ![(TypeVar,TypeVar)]
	, ms_type_heaps		:: !*TypeHeaps
	, ms_common_defs	:: !{# CommonDefs}
	}

is_trivial_body :: ![FreeVar] !Expression ![Expression] !(Optional SymbolType) !.ReadOnlyTI !*{#FunDef} !*FunctionHeap !*TypeHeaps !*{!ConsClasses}
	-> (!Optional Expression,!*{#FunDef},!*FunctionHeap,!*TypeHeaps,!*{!ConsClasses})
is_trivial_body [fv] (Var bv) [arg] type ro fun_defs fun_heap type_heaps cons_args
	= if (fv.fv_info_ptr == bv.var_info_ptr)
			(Yes arg, fun_defs, fun_heap, type_heaps, cons_args)
			(No, fun_defs, fun_heap, type_heaps , cons_args)
is_trivial_body args (App app) f_args type ro fun_defs fun_heap type_heaps cons_args
	# (safe_producer, fun_heap, cons_args) = get_producer_class app.app_symb.symb_kind ro fun_heap cons_args
	| not safe_producer
		= (No,fun_defs,fun_heap,type_heaps,cons_args)
	# (type`,fun_defs,fun_heap)	= get_producer_type app.app_symb ro fun_defs fun_heap
	# match = match_args (length f_args) info args app.app_args []
	= case match of
		Yes perm
			# (match, type_heaps) = match_types type type` perm ro.ro_common_defs type_heaps
			| match
				# f_args = permute_args f_args (take (length f_args) perm)
				-> (Yes (App {app & app_args = f_args}),fun_defs,fun_heap,type_heaps,cons_args)
				-> (No,fun_defs,fun_heap,type_heaps,cons_args)
		_	-> (No,fun_defs,fun_heap,type_heaps,cons_args)
where
	info :: {!VarInfoPtr}
	info = {v.fv_info_ptr \\ v <- args}
	
	match_args 0 _ [] [] accu
		= Yes (reverse accu)
	match_args 0 info [fv:fvs] [Var bv:bvs] accu
		| fv.fv_info_ptr == bv.var_info_ptr 
			# index = lookup bv.var_info_ptr info
			= match_args 0 info fvs bvs [index:accu]
			= No
	match_args n info [fv:fvs] [Var bv:bvs] accu
		# index = lookup bv.var_info_ptr info
		= match_args (dec n) info fvs bvs [index:accu]
	match_args _ _ _ _ _ = No
	
	lookup x d = lookup 0 x d
	where
		lookup i x d
			| d.[i] == x
				= i
				= lookup (inc i) x d
	
	permute_args args perm = [args!!p \\ p <- perm]
		
	match_types type type` perm common_defs type_heaps
		| not_ok_perm perm
			= (False,type_heaps)
		= case type of
			No			-> (True,type_heaps)
			Yes type	-> match_types type type` perm common_defs type_heaps
	where
		not_ok_perm perm = length perm <> size info
		
		match_types type type` perm common_defs type_heaps
			| not (match_strictness` (dec type.st_arity) type.st_args_strictness type`.st_args_strictness perm)
				= (False,type_heaps)
			= (True,type_heaps)
/*			# (ok,args,res)	= make_args (type`.st_arity) type.st_args type.st_result
			| not ok = (False,type_heaps)
			# args` = permute_args args perm
			# ms = {tvar_map=[], ms_type_heaps = type_heaps,ms_common_defs=common_defs}
			# (match_ok,ms)	= match_arg_types args type`.st_args ms
			| not match_ok = (False,ms.ms_type_heaps)
			# (match_ok,ms)	= match_res_type res type`.st_result ms
			| not match_ok = (False,ms.ms_type_heaps)
			| type.st_context <> [] || type`.st_context <> []
				= (False,ms.ms_type_heaps)
			= (True,ms.ms_type_heaps)

		where
			make_args n as r
				# l = length as
				| n < l		= (False,as,r)
				| n == l	= (True,as,r)
				= move_args (n-l) as r []
			move_args 0 as r accu	= (True,as++(reverse accu),r)
			move_args n as {at_type = a-->r} accu = move_args (dec n) as r [a:accu]
			move_args _ as r accu = (False,as,r)
*/
		match_strictness` i s1 s2 p
			| i < 0 = True
			= arg_is_strict (p!!i) s1 == arg_is_strict i s2 && match_strictness (dec i) s1 s2

	match_strictness i s1 s2
		| i < 0 = True
		= arg_is_strict i s1 == arg_is_strict i s2 && match_strictness (dec i) s1 s2
	
	match_arg_types [] [] ms
		= (True,ms)
	match_arg_types [arg:args] [arg`:args`] ms
		# (type_ok,ms)	= match_type arg.at_type arg.at_attribute arg`.at_type arg`.at_attribute ms
		| not type_ok = (False,ms)
		= match_arg_types args args` ms
	match_arg_types _ _ ms
		= (False,ms)
	
	match_res_type res res` ms
		= match_type res.at_type res.at_attribute res`.at_type res`.at_attribute ms

	match_type (TA tsid types) _ (TA tsid` types`) _ ms
		| tsid == tsid`
			= match_arg_types types types` ms
	match_type (TAS tsid types strictl) _ (TAS tsid` types` strictl`) _ ms
		| tsid == tsid`
			| not (match_strictness (dec (length types)) strictl strictl`) = (False,ms)
			= match_arg_types types types` ms
	match_type (arg --> res) _ (arg` --> res`) _ ms
		# (type_ok,ms)	= match_type arg.at_type arg.at_attribute arg`.at_type arg`.at_attribute ms
		| not type_ok = (False,ms)
		= match_type res.at_type res.at_attribute res`.at_type res`.at_attribute ms
	match_type (TB bt) _ (TB bt`) _ ms
		= (bt==bt`,ms)
	match_type (TV tv) _ (TV tv`) _ ms
		= match_tvar tv tv` ms
	match_type t1 a1 t2 a2 ms
		# type_heaps	= ms.ms_type_heaps
		# (succ1,t1,type_heaps)	= tryToExpand t1 a1 ms.ms_common_defs type_heaps
		# (succ2,t2,type_heaps)	= tryToExpand t2 a2 ms.ms_common_defs type_heaps
		# ms = { ms & ms_type_heaps = type_heaps }
		| succ1 || succ2 = match_type t1 a1 t2 a2 ms
		= (False,ms)

	match_tvar x y ms
		# (r,tvar_map)	= match_tvar x y ms.tvar_map
		= (r, {ms & tvar_map = tvar_map})
	where
		match_tvar x y [] = (True,[(x,y)])
		match_tvar x y ms=:[(x`,y`):t]
			| x == x`	= (y==y`, ms)
			# (res,t)	= match_tvar x y t
			= (res,[(x`,y`):t])
	
is_trivial_body args rhs f_args type ro fun_defs fun_heap type_heaps cons_args
	= (No,fun_defs,fun_heap,type_heaps,cons_args)

get_producer_class (SK_GeneratedFunction fun_ptr _) ro fun_heap cons_args
	# (FI_Function {gf_cons_args={cc_producer}}, fun_heap) = readPtr fun_ptr fun_heap
	= (cc_producer, fun_heap, cons_args)
get_producer_class (SK_LocalMacroFunction glob_object) ro fun_heap cons_args
	# ({cc_producer},cons_args) = cons_args![glob_object]
	= (cc_producer, fun_heap, cons_args)
get_producer_class (SK_Function { glob_module, glob_object }) ro fun_heap cons_args
	# (max_index,cons_args)			= usize cons_args
	| glob_module <> ro.ro_main_dcl_module_n || glob_object >= max_index
		= (False, fun_heap, cons_args)
	# ({cc_producer},cons_args) = cons_args![glob_object]
	= (cc_producer, fun_heap, cons_args)
get_producer_class (SK_Constructor {glob_module, glob_object}) ro fun_heap cons_args
	= (SwitchConstructorFusion True False, fun_heap, cons_args)

//@ transformApplication
transformApplication :: !App ![Expression] !ReadOnlyTI !*TransformInfo -> *(!Expression,!*TransformInfo)
transformApplication app=:{app_symb=symb=:{symb_kind}, app_args} extra_args
			ro ti=:{ti_cons_args,ti_instances,ti_fun_defs}
	| is_SK_Function_or_SK_LocalMacroFunction symb_kind // otherwise GOTO next alternative	
		# gi
			= case symb_kind of
				SK_Function global_index -> global_index
				SK_LocalMacroFunction index -> { glob_module = ro.ro_main_dcl_module_n, glob_object = index }
		# { glob_module, glob_object } = gi
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
//			&& True ---> ("transformApplication "+++toString symb.symb_name)
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
		| SwitchSpecialFusion
				(not (isEmpty app_args) )
				False
			// Check imported overloaded function application for specials...
			# {ft_specials}						= ro.ro_imported_funs.[glob_module].[glob_object]
			# specials							= case ft_specials of
													(SP_ContextTypes s)	-> s
													_	-> []
			| not (isEmpty specials)
				# (ei,ti_symbol_heap)			= mapSt readAppInfo app_args ti.ti_symbol_heap
					with
						readAppInfo (App {app_info_ptr}) heap
							| isNilPtr app_info_ptr
								= (EI_Empty,heap)
							= readPtr app_info_ptr heap
						readAppInfo _ heap = (EI_Empty,heap)
				# ti							= {ti & ti_symbol_heap = ti_symbol_heap}
				# context						= ro.ro_imported_funs.[glob_module].[glob_object].ft_type.st_context
				# insts							= resolveContext context ei
				# (num_special_args,special_gi)	= findInstInSpecials insts specials
				| foundSpecial special_gi
					= build_application {app & app_symb.symb_kind = SK_Function special_gi} (drop num_special_args app_args) extra_args special_gi ti
				= build_application app app_args extra_args gi ti
			= build_application app app_args extra_args gi ti
		= build_application app app_args extra_args gi ti
	where
		build_application app app_args extra_args {glob_module,glob_object} ti
			| isEmpty extra_args
				= (App {app & app_args = app_args}, ti)
			# {ft_arity,ft_type}	= ro.ro_imported_funs.[glob_module].[glob_object]
			  form_arity			= ft_arity + length ft_type.st_context
			  ar_diff				= form_arity - length app_args
			  nr_of_extra_args		= length extra_args
			| nr_of_extra_args <= ar_diff
				= (App {app  &  app_args = app_args ++ extra_args }, ti)
				= (App {app  &  app_args = app_args ++ take ar_diff extra_args } @ drop ar_diff extra_args, ti)
		
		build_special_application app app_args extra_args {glob_module,glob_object} ro ti
			| isEmpty extra_args
				= (App {app & app_args = app_args}, ti)
			# {ft_arity,ft_type} = ro.ro_imported_funs.[glob_module].[glob_object]
			  form_arity = ft_arity + length ft_type.st_context
			  ar_diff = form_arity - length app_args
			  nr_of_extra_args = length extra_args
			| nr_of_extra_args <= ar_diff
				= (App {app  &  app_args = app_args ++ extra_args }, ti)
				= (App {app  &  app_args = app_args ++ take ar_diff extra_args } @ drop ar_diff extra_args, ti)

		find_member_n i member_string a
			| i<size a
				| a.[i].ds_ident.id_name % (0,size member_string-1)==member_string
					= i
					= find_member_n (i+1) member_string a

		select_member exp=:(App {app_symb={symb_kind=SK_Constructor _},app_args,app_info_ptr}) select_symb me_offset ti=:{ti_symbol_heap}
			| not (isNilPtr app_info_ptr) 
				# (ei,ti_symbol_heap)	= readPtr app_info_ptr ti_symbol_heap
				# ti = {ti & ti_symbol_heap = ti_symbol_heap}
				= case ei of
					(EI_DictionaryType _)	-> (app_args !! me_offset,ti)
					_						-> (Selection NormalSelector exp [RecordSelection select_symb me_offset],ti)
		select_member exp select_symb me_offset ti
			= (Selection NormalSelector exp [RecordSelection select_symb me_offset],ti)

// XXX linear_bits field has to be added for generated functions
transformApplication app=:{app_symb={symb_name,symb_kind = SK_GeneratedFunction fun_def_ptr fun_index}} extra_args
			ro ti=:{ti_cons_args,ti_instances,ti_fun_defs,ti_fun_heap}
	| fun_index < size ti_cons_args
		#! cons_class = ti_cons_args.[fun_index]
		   (instances, ti_instances) = ti_instances![fun_index]
		   (fun_def, ti_fun_defs) = ti_fun_defs![fun_index]
		   ti = { ti & ti_instances = ti_instances, ti_fun_defs = ti_fun_defs }
		= transformFunctionApplication fun_def instances cons_class app extra_args ro ti
	# (FI_Function {gf_fun_def,gf_instance_info,gf_cons_args}, ti_fun_heap) = readPtr fun_def_ptr ti_fun_heap
	  ti = { ti & ti_fun_heap = ti_fun_heap }
	= transformFunctionApplication gf_fun_def gf_instance_info gf_cons_args app extra_args ro ti
transformApplication app [] ro ti
	= (App app, ti)
transformApplication app=:{app_symb={symb_name,symb_kind = SK_Constructor cons_index},app_args} extra_args
			ro ti=:{ti_cons_args,ti_instances,ti_fun_defs,ti_fun_heap}
	# {cons_type}			= ro.ro_common_defs.[cons_index.glob_module].com_cons_defs.[cons_index.glob_object]
	# (app_args,extra_args)	= complete_application cons_type.st_arity app_args extra_args
	= (build_application { app & app_args = app_args } extra_args, ti)
where
	complete_application form_arity args []
		= (args, [])
	complete_application form_arity args extra_args
		# arity_diff = min (form_arity - length args) (length extra_args)
		= (args ++ take arity_diff extra_args, drop arity_diff extra_args)

	build_application app []
		= App app
	build_application app extra_args
		= App app @ extra_args
transformApplication app extra_args ro ti
	= (App app @ extra_args, ti)

transformSelection :: SelectorKind [Selection] Expression ReadOnlyTI *TransformInfo -> (!Expression,!*TransformInfo)
transformSelection NormalSelector s=:[RecordSelection _ field_index : selectors] 
					app=:(App appi=:{app_symb={symb_kind= SK_Constructor _ }, app_args, app_info_ptr})
					ro ti=:{ti_symbol_heap}
	| isNilPtr app_info_ptr
		// urgh: now reevaluates cnf for each nested strict selector :-(
		| cnf_app_args appi ro
			= transformSelection NormalSelector selectors (app_args !! field_index) ro ti
		= (Selection NormalSelector app s, ti)
	# (app_info, ti_symbol_heap) = readPtr app_info_ptr ti_symbol_heap
	  ti = { ti & ti_symbol_heap = ti_symbol_heap }
	= case app_info of
		EI_DictionaryType _
			-> transformSelection NormalSelector selectors (app_args !! field_index) ro ti
		_
			// urgh: now reevaluates cnf for each nested strict selector :-(
			| cnf_app_args appi ro
				-> transformSelection NormalSelector selectors (app_args !! field_index) ro ti
			-> (Selection NormalSelector app s, ti)
where
	cnf_args [] index strictness ro = True
	cnf_args [arg:args] index strictness ro
		| arg_is_strict index strictness
			= case arg of
				BasicExpr _	-> cnf_args args (inc index) strictness ro
				App app		-> cnf_app_args app ro
				_			-> False
		= cnf_args args (inc index) strictness ro
	
	cnf_app_args {app_symb=symb=:{symb_kind = SK_Constructor cons_index, symb_name}, app_args} ro
		# {cons_type}		= ro.ro_common_defs.[cons_index.glob_module].com_cons_defs.[cons_index.glob_object]
		= cnf_args app_args 0 cons_type.st_args_strictness ro
	cnf_app_args {app_symb=symb=:{symb_kind}, app_args} ro
		= False
transformSelection NormalSelector s=:[RecordSelection _ field_index : selectors] 
					app=:(App appi=:{app_symb=app_symb=:{symb_kind}, app_args, app_info_ptr})
					ro ti
	| isOKSymbol symb_kind && isEmpty app_args
		# (fun_def,ti_fun_defs,ti_fun_heap)		= get_fun_def symb_kind ro.ro_main_dcl_module_n ti.ti_fun_defs ti.ti_fun_heap
		# ti = {ti & ti_fun_defs = ti_fun_defs, ti_fun_heap = ti_fun_heap}
		# {fun_body,fun_type,fun_kind}			= fun_def
		| is_not_caf fun_kind
			= case fun_body of
				TransformedBody {tb_rhs}	-> case tb_rhs of
					App app						-> transformSelection NormalSelector s tb_rhs ro ti
					_							-> (Selection NormalSelector app s, ti)
			= (Selection NormalSelector app s, ti)
where
	isOKSymbol (SK_Function {glob_module})	= glob_module == ro.ro_main_dcl_module_n
	isOKSymbol (SK_LocalMacroFunction _)	= True
	isOKSymbol (SK_GeneratedFunction _ _)	= True
	isOKSymbol _							= False
	
	is_not_caf FK_Caf	= False
	is_not_caf _		= True
transformSelection NormalSelector [] expr ro ti
	= (expr, ti)
transformSelection selector_kind selectors expr ro ti
	= (Selection selector_kind expr selectors, ti)

//@	determineProducers: finds all legal producers in the argument list.
// This version finds FIRST legal producer in argument list...

// XXX store linear_bits and cc_args together ?

determineProducers :: Bool Bool Bool (Optional SymbolType) [Bool] [Int] [Expression] Int *{!Producer} ReadOnlyTI *TransformInfo -> *(!*{!Producer},![Expression],!*TransformInfo);
determineProducers _ _ _ _ _ _ [] _ producers _ ti
	= (producers, [], ti)
determineProducers is_applied_to_macro_fun consumer_is_curried ok_non_rec_consumer fun_type [linear_bit : linear_bits] [ cons_arg : cons_args ] [ arg : args ] prod_index producers ro ti
 	| cons_arg == CActive
		# (producers, new_arg, ti) = determine_producer is_applied_to_macro_fun consumer_is_curried ok_non_rec_consumer linear_bit arg [] prod_index producers ro ti
		| isProducer producers.[prod_index]
			= (producers, new_arg++args, ti)
		# (producers, new_args, ti) = determineProducers is_applied_to_macro_fun consumer_is_curried ok_non_rec_consumer fun_type linear_bits cons_args args (inc prod_index) producers ro ti
		= (producers, new_arg++new_args, ti)
	| SwitchUnusedFusion (ro.ro_transform_fusion && cons_arg == CUnused && isLazyArg fun_type prod_index) False
		# producers = { producers & [prod_index] = PR_Unused }
		= (producers, args, ti)
	# (producers, new_args, ti) = determineProducers is_applied_to_macro_fun consumer_is_curried ok_non_rec_consumer fun_type linear_bits cons_args args (inc prod_index) producers ro ti
	= (producers, [arg : new_args], ti)
where
	isProducer PR_Empty	= False
	isProducer _		= True
	
	isLazyArg No _ = True
	isLazyArg (Yes {st_args_strictness}) index = not (arg_is_strict (inc index) st_args_strictness)
	
	determine_producer is_applied_to_macro_fun consumer_is_curried ok_non_rec_consumer linear_bit arg=:(App app=:{app_info_ptr}) new_args prod_index producers ro ti
		| isNilPtr app_info_ptr
			= determineProducer is_applied_to_macro_fun consumer_is_curried ok_non_rec_consumer linear_bit app EI_Empty new_args prod_index producers ro ti
		# (app_info, ti_symbol_heap) = readPtr app_info_ptr ti.ti_symbol_heap
		# ti = { ti & ti_symbol_heap = ti_symbol_heap }
		= determineProducer is_applied_to_macro_fun consumer_is_curried ok_non_rec_consumer linear_bit app app_info new_args prod_index producers ro ti
	determine_producer _ _ _ _ arg new_args _ producers _ ti
		= (producers, [arg : new_args], ti)

NoDictionaryElimination	:== False

determineProducer :: Bool Bool Bool Bool App ExprInfo [Expression] Int *{!Producer} ReadOnlyTI *TransformInfo -> *(!*{!Producer},![Expression],!*TransformInfo)
// XXX check for linear_bit also in case of a constructor ?
determineProducer _ _ _ _ app=:{app_symb = symb=:{symb_kind = SK_Constructor _}, app_args} (EI_DictionaryType type)
				  new_args prod_index producers _ ti
	| NoDictionaryElimination
		= (producers, [App app : new_args ], ti)
	# (app_args, (new_vars_and_types, free_vars, ti_var_heap)) 
			= renewVariables app_args ti.ti_var_heap
	# prod	= PR_Class { app & app_args = app_args } new_vars_and_types type
	= ( { producers & [prod_index] = prod }
	  , mapAppend Var free_vars new_args
	  , { ti & ti_var_heap = ti_var_heap }
	  )

determineProducer _ _ _ linear_bit app=:{app_symb = symb=:{symb_kind = SK_Constructor cons_index, symb_name}, app_args} _
				  new_args prod_index producers ro ti
	# {cons_type}								= ro.ro_common_defs.[cons_index.glob_module].com_cons_defs.[cons_index.glob_object]
	  rnf										= rnf_args app_args 0 cons_type.st_args_strictness ro	//---> ("rnf_args",symb_name)
	| SwitchConstructorFusion
		(ro.ro_transform_fusion && SwitchRnfConstructorFusion (linear_bit || rnf) linear_bit)
		False
		# producers = {producers & [prod_index] = PR_Constructor symb (length app_args) app_args }
		= (producers, app_args ++ new_args, ti)
	= ( producers, [App app : new_args ], ti)
where
	rnf_args [] index strictness ro = True
	rnf_args [arg:args] index strictness ro
		| arg_is_strict index strictness
			= case arg of
				BasicExpr _	-> rnf_args args (inc index) strictness ro			//---> ("rnf_arg","Basic")
				App app		-> rnf_app_args app args index strictness ro		//---> ("rnf_arg","App")
				_			-> False											//---> ("rnf_arg","Other")
		= rnf_args args (inc index) strictness ro								//---> ("rnf_arg","Lazy")
	
	rnf_app_args {app_symb=symb=:{symb_kind = SK_Constructor cons_index, symb_name}, app_args} args index strictness ro
		# {cons_type}		= ro.ro_common_defs.[cons_index.glob_module].com_cons_defs.[cons_index.glob_object]
		| rnf_args app_args 0 cons_type.st_args_strictness ro					//---> ("rnf_args",symb_name)
			= rnf_args args (inc index) strictness ro
			= False
	// what else is rnf => curried apps
	rnf_app_args {app_symb=symb=:{symb_kind}, app_args} args index strictness ro
		= False

determineProducer is_applied_to_macro_fun consumer_is_curried ok_non_rec_consumer linear_bit
				  app=:{app_symb = symb=:{ symb_kind = SK_GeneratedFunction fun_ptr fun_index}, app_args} _
				  new_args prod_index producers ro ti
	# (FI_Function {gf_cons_args={cc_producer},gf_fun_def={fun_body, fun_arity, fun_type, fun_info}}, ti_fun_heap)
					= readPtr fun_ptr ti.ti_fun_heap
	  ti = { ti & ti_fun_heap=ti_fun_heap }
	| length app_args<>fun_arity
		| is_applied_to_macro_fun
			= ({ producers & [prod_index] = PR_Curried symb (length app_args)}, app_args ++ new_args, ti)
				-!-> ("Produce1cc_macro",symb.symb_name)
		| SwitchCurriedFusion ro.ro_transform_fusion cc_producer False
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
    # not_expanding_producer
		= case fun_body of
			Expanding _
				-> False
			_
				-> True
//				-> cc_producer
    | SwitchHOFusion
    	((not consumer_is_curried && not_expanding_producer) && is_applied_to_macro_fun && linear_bit && is_higher_order_function fun_type)
    	False
		= ({ producers & [prod_index] = PR_Curried symb (length app_args)}, app_args ++ new_args, ti)
				-!-> ("Produce1cc_ho",symb.symb_name)
    | SwitchHOFusion`
    	((not consumer_is_curried && not_expanding_producer) && ok_non_rec_consumer && linear_bit && is_higher_order_function fun_type)
    	False
		= ({ producers & [prod_index] = PR_Curried symb (length app_args)}, app_args ++ new_args, ti)
				-!-> ("Produce1cc_hnr",symb.symb_name)
// NON-REC...
	# non_rec_producer
		= (fun_info.fi_properties bitand FI_IsNonRecursive) <> 0 with FI_IsNonRecursive = 4
	# ok_non_rec
		= case fun_body of
			Expanding _
				-> False
			(TransformedBody {tb_rhs})
				-> ro.ro_transform_fusion && not_expanding_producer && is_sexy_body tb_rhs && ok_non_rec_consumer && non_rec_producer//is_good_producer
	| SwitchNonRecFusion ok_non_rec False
		= ({ producers & [prod_index] = (PR_GeneratedFunction symb (length app_args) fun_index)}, app_args ++ new_args, ti)
				-!-> ("Produce1nr",symb.symb_name)
// ...NON-REC
	= (producers, [App app : new_args ], ti)
				-!-> ("Produce1--",symb.symb_name)

determineProducer is_applied_to_macro_fun consumer_is_curried ok_non_rec_consumer linear_bit app=:{app_symb = symb=:{symb_kind}, app_args} _
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
			# ({cc_producer},ti) = ti!ti_cons_args.[glob_object]
			| SwitchCurriedFusion ro.ro_transform_fusion cc_producer False
				= ({ producers & [prod_index] = PR_Curried symb (length app_args)}, app_args ++ new_args, ti)
					-!-> ("Produce2cc_curried",symb.symb_name)
			= (producers, [App app : new_args ], ti)
		#! max_index = size ti.ti_cons_args
		| glob_module <> ro.ro_main_dcl_module_n || glob_object >= max_index /* Sjaak, to skip array functions */
			= (producers, [App app : new_args ], ti)
					-!-> ("Produce2cc_array",symb.symb_name,if (glob_module <> ro.ro_main_dcl_module_n) "foreign" "array")
		# ({fun_body,fun_type,fun_info}, ti) = ti!ti_fun_defs.[glob_object]
		  (TransformedBody {tb_rhs}) = fun_body
		  is_good_producer = SwitchFunctionFusion (ro.ro_transform_fusion && linear_bit && is_sexy_body tb_rhs) False
		  {cc_producer} = ti.ti_cons_args.[glob_object]
		| is_good_producer && cc_producer && not consumer_is_curried
			= ({ producers & [prod_index] = (PR_Function symb (length app_args) glob_object)}, app_args ++ new_args, ti)
					-!-> ("Produce2cc",symb.symb_name)
	    # not_expanding_producer
			= case fun_body of
				Expanding _
					-> False
				_
					-> True
//					-> cc_producer
		| (not consumer_is_curried && not_expanding_producer) && is_applied_to_macro_fun && linear_bit && is_higher_order_function fun_type
			= ({ producers & [prod_index] = PR_Curried symb (length app_args)}, app_args ++ new_args, ti)
					-!-> ("Produce2cc_ho",symb.symb_name)
// NON-REC...
		# non_rec_producer
			= (fun_info.fi_properties bitand FI_IsNonRecursive) <> 0 with FI_IsNonRecursive = 4
		# ok_non_rec
			= case fun_body of
				Expanding _
					-> False
				(TransformedBody {tb_rhs})
					-> ro.ro_transform_fusion && not_expanding_producer && is_sexy_body tb_rhs && ok_non_rec_consumer && non_rec_producer//&& is_good_producer
		| SwitchNonRecFusion ok_non_rec False
			= ({ producers & [prod_index] = (PR_Function symb (length app_args) glob_object)}, app_args ++ new_args, ti)
					-!-> ("Produce2nr",symb.symb_name)
// ...NON-REC
		= (producers, [App app : new_args ], ti)
					-!-> ("Produce2-1",symb.symb_name)
	= (producers, [App app : new_args ], ti)
					-!-> ("Produce2-2",symb.symb_name)
where
	get_max_index ti=:{ti_cons_args}
		#! (max_index, ti_cons_args)	= usize ti_cons_args
		= (max_index, {ti & ti_cons_args = ti_cons_args})
	get_fun_arity glob_module glob_object ro ti
		| glob_module <> ro.ro_main_dcl_module_n
			# {st_arity, st_context} = ro.ro_imported_funs.[glob_module].[glob_object].ft_type
			= (st_arity+length st_context, ti)
		// for imported functions you have to add ft_arity and length st_context, but for unimported
		// functions fun_arity alone is sufficient
		= ti!ti_fun_defs.[glob_object].fun_arity
	
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

is_higher_order_function (Yes {st_result={at_type=_ --> _}})
        = True
is_higher_order_function _
        = False

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
			_	-> abort "map_expr in module trans does not match\n"// <<- ("map_expr",var,var_info)
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

	// AA:
	map_expr_st expr=:(BasicExpr _) st 
		= f expr st
	map_expr_st (expr @ exprs) st 
		= abort "trans.icl: map_expr_st (expr @ exprs) not implemented\n"
	map_expr_st (TupleSelect ds n expr) st 
		= abort "trans.icl: map_expr_st (TupleSelect ds n expr) not implemented\n"
	map_expr_st (DynamicExpr dyn_expr) st 
		= abort "trans.icl: map_expr_st (DynamicExpr dyn_expr) not implemented\n"
	map_expr_st _ st = abort "trans.icl: map_expr_st does not match !!!!!!!!!!!!\n"


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
		
	// AA:	
	foldr_expr_st expr=:(BasicExpr _) st 
		= f expr st

add_let_binds :: [FreeVar] [Expression] [LetBind] -> [LetBind]
add_let_binds free_vars rhss original_binds
	= [{ original_bind & lb_dst = lb_dst, lb_src = lb_src}
		\\ lb_dst <- free_vars & lb_src <- rhss & original_bind <- original_binds]

//@	transformGroups

transformGroups :: !CleanupInfo !Int !Int !Int !Int !*{!Group} !*{#FunDef} !*{!.ConsClasses} !{# CommonDefs}  !{# {# FunType} }
		!*ImportedTypes !ImportedConstructors !*TypeDefInfos !*VarHeap !*TypeHeaps !*ExpressionHeap !Bool !*File !*PredefinedSymbols
			-> (!*{!Group}, !*{#FunDef}, !*ImportedTypes, !ImportedConstructors, !*VarHeap, !*TypeHeaps, !*ExpressionHeap, !*{!ConsClasses}, !*File, !*PredefinedSymbols)
transformGroups cleanup_info main_dcl_module_n stdStrictLists_module_n def_min def_max groups fun_defs cons_args common_defs imported_funs
		imported_types collected_imports type_def_infos var_heap type_heaps symbol_heap compile_with_fusion error predef_symbols
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
				, ti_error_file		= error
				, ti_predef_symbols	= predef_symbols
				}
	# groups = [group \\ group <-: groups]
	# (groups, imported_types, collected_imports, fun_indices_with_abs_syn_types, ti)
		= transform_groups 0 groups [] common_defs imported_funs imported_types collected_imports [] initial_ti
	# groups = {group \\ group <- reverse groups}

	  {ti_fun_defs,ti_new_functions,ti_var_heap,ti_symbol_heap,ti_fun_heap,ti_next_fun_nr,ti_type_heaps,ti_cleanup_info} = ti
	# (fun_defs, imported_types, collected_imports, type_heaps, var_heap) 
			= foldSt (expand_abstract_syn_types_in_function_type common_defs) (reverse fun_indices_with_abs_syn_types)
					(ti_fun_defs, imported_types, collected_imports, ti_type_heaps, ti_var_heap)

	  (groups, new_fun_defs, new_cons_classes, imported_types, collected_imports, type_heaps, var_heap) 
	  		= foldSt (add_new_function_to_group common_defs ti_fun_heap) ti_new_functions
	  				(groups, [], [], imported_types, collected_imports, type_heaps, var_heap)
	  symbol_heap = foldSt cleanup_attributes ti.ti_cleanup_info ti.ti_symbol_heap
	  fun_defs = { fundef \\ fundef <- [ fundef \\ fundef <-: fun_defs ] ++ new_fun_defs }
	  cons_args	= { consarg \\ consarg <- [ consarg \\ consarg <-: ti.ti_cons_args ] ++ new_cons_classes }
	= (groups, fun_defs, imported_types, collected_imports,	var_heap, type_heaps, symbol_heap, cons_args, ti.ti_error_file, ti.ti_predef_symbols)
where
	transform_groups group_nr [] acc_groups common_defs imported_funs imported_types collected_imports fun_indices_with_abs_syn_types ti
		= (acc_groups, imported_types, collected_imports, fun_indices_with_abs_syn_types, ti)
	transform_groups group_nr [group:groups] acc_groups common_defs imported_funs imported_types collected_imports fun_indices_with_abs_syn_types ti
			# {group_members} = group
			# (ti_fun_defs, imported_types, collected_imports, fun_indices_with_abs_syn_types, ti_type_heaps, ti_var_heap) 
					= foldSt (convert_function_type common_defs) group_members
							(ti.ti_fun_defs, imported_types, collected_imports, fun_indices_with_abs_syn_types, ti.ti_type_heaps, ti.ti_var_heap)
			# ti = { ti & ti_fun_defs = ti_fun_defs, ti_type_heaps = ti_type_heaps, ti_var_heap = ti_var_heap }
			# (group_nr,acc_groups,ti) = transform_group common_defs imported_funs group_nr group_members acc_groups ti
			= transform_groups group_nr groups acc_groups common_defs imported_funs imported_types collected_imports fun_indices_with_abs_syn_types ti

	transform_groups` common_defs imported_funs group_nr [] acc_groups ti
			= (group_nr, acc_groups, ti)
	transform_groups` common_defs imported_funs group_nr [{group_members}:groups] acc_groups ti
			# (group_nr,acc_groups,ti) = transform_group common_defs imported_funs group_nr group_members acc_groups ti
			= transform_groups` common_defs imported_funs group_nr groups acc_groups ti
	
	transform_group common_defs imported_funs group_nr group_members acc_groups ti
			// assign group_nr to group_members
			# ti = ti <-!- ("transform_group",group_nr)
			# ti = foldSt (assign_group group_nr) group_members ti
			// store old consumer classification			
			# (before,ti) = ti!ti_next_fun_nr
			// transform group_members
			# ti = foldSt (transform_function common_defs imported_funs) group_members ti
			// partitionate group: need to know added functions for this...
			# (after,ti) = ti!ti_next_fun_nr
			# (new_groups,ti) = partition_group group_nr (group_members++[before..after-1]) ti
			// reanalyse consumers
			# (cleanup,ti_fun_defs,ti_var_heap,ti_symbol_heap,ti_fun_heap,ti_cons_args,same)
					= reanalyseGroups common_defs imported_funs main_dcl_module_n stdStrictLists_module_n ti.ti_new_functions
						new_groups
						ti.ti_fun_defs ti.ti_var_heap ti.ti_symbol_heap ti.ti_fun_heap ti.ti_cons_args
			# ti = {ti 
					& ti_cleanup_info = cleanup ++ ti.ti_cleanup_info
					, ti_fun_defs = ti_fun_defs
					, ti_var_heap = ti_var_heap
					, ti_symbol_heap = ti_symbol_heap
					, ti_fun_heap = ti_fun_heap
					, ti_cons_args = ti_cons_args
					}
			// if wanted reapply transform_group to all found groups
			| (after>before) || (length new_groups > 1) || not same
				= transform_groups` common_defs imported_funs group_nr new_groups acc_groups ti
			// producer annotation for finished components!
			# ti = reannotate_producers group_nr group_members ti
			= (inc group_nr,(reverse new_groups)++acc_groups,ti)
	
	changed_group_classification [] ti
		= (False,ti)
	changed_group_classification [fun:funs] ti
		= (False,ti)
	
	assign_group group_number fun ti
		# (fd,ti)		= get_fun_def fun ti
		# fd			= { fd & fun_info.fi_group_index = group_number }
		# ti			= set_fun_def fun fd ti
		= ti
	
	get_fun_def fun ti=:{ti_fun_defs}
		| fun < size ti_fun_defs
			# (fun_def, ti)						= ti!ti_fun_defs.[fun]
			= (fun_def,ti)
		# (fun_def_ptr,ti_fun_heap)			= lookup_ptr fun ti.ti_new_functions ti.ti_fun_heap
			with
				lookup_ptr fun [] ti_fun_heap = abort "drat"
				lookup_ptr fun [fun_def_ptr:new_functions] ti_fun_heap
					# (FI_Function {gf_fun_index}, ti_fun_heap)
							= readPtr fun_def_ptr ti_fun_heap
					| gf_fun_index == fun
						= (fun_def_ptr, ti_fun_heap)
						= lookup_ptr fun new_functions ti_fun_heap
		# (FI_Function {gf_fun_def}, ti_fun_heap)
											= readPtr fun_def_ptr ti_fun_heap
		  ti								= { ti & ti_fun_heap = ti_fun_heap }
		= (gf_fun_def,ti)

	set_fun_def fun fun_def ti=:{ti_fun_defs}
		| fun < size ti_fun_defs
			= {ti & ti_fun_defs.[fun] = fun_def}
		# (fun_def_ptr,ti_fun_heap)			= lookup_ptr fun ti.ti_new_functions ti.ti_fun_heap
			with
				lookup_ptr fun [] ti_fun_heap = abort "drat"
				lookup_ptr fun [fun_def_ptr:new_functions] ti_fun_heap
					# (FI_Function {gf_fun_index}, ti_fun_heap)
							= readPtr fun_def_ptr ti_fun_heap
					| gf_fun_index == fun
						= (fun_def_ptr, ti_fun_heap)
						= lookup_ptr fun new_functions ti_fun_heap
		# (FI_Function gf, ti_fun_heap)
											= readPtr fun_def_ptr ti_fun_heap
		# ti_fun_heap						= writePtr fun_def_ptr (FI_Function {gf & gf_fun_def = fun_def}) ti_fun_heap
		  ti								= { ti & ti_fun_heap = ti_fun_heap }
		= ti
	
	partition_group group_nr group_members ti
		# fun_defs = ti.ti_fun_defs
		# fun_heap = ti.ti_fun_heap
		# max_fun_nr = ti.ti_next_fun_nr
		# new_functions = ti.ti_new_functions
		# main_dcl_module_n = main_dcl_module_n
		# next_group = group_nr
		# predef_symbols = ti.ti_predef_symbols
		# var_heap = ti.ti_var_heap
		# expression_heap = ti.ti_symbol_heap
		# error_admin = {ea_file = ti.ti_error_file, ea_loc = [], ea_ok = True }
		# (_,groups,fun_defs,fun_heap,predef_symbols,var_heap,expression_heap,error_admin)
			= partitionateFunctions`` max_fun_nr next_group new_functions fun_defs group_members main_dcl_module_n def_min def_max fun_heap predef_symbols var_heap expression_heap error_admin
		# ti = 
			{ ti
			& ti_fun_defs		= fun_defs
			, ti_fun_heap		= fun_heap
			, ti_predef_symbols	= predef_symbols
			, ti_var_heap		= var_heap
			, ti_symbol_heap	= expression_heap
			, ti_error_file		= error_admin.ea_file
			}
		= (groups,ti)
		
	transform_function common_defs imported_funs fun ti
		# (fun_def, ro_fun, ti)	= get_fun_def_and_symb_ident fun ti
		# ti = ti <-!- ("transform_function",fun,ro_fun,fun_def)
		# (Yes {st_args})					= fun_def.fun_type
		  {fun_body = TransformedBody tb} = fun_def
		  ti_var_heap						= fold2St store_arg_type_info tb.tb_args st_args ti.ti_var_heap
		  ro =	{ ro_imported_funs				= imported_funs
				, ro_common_defs 				= common_defs
				, ro_root_case_mode				= get_root_case_mode tb
				, ro_fun_root					= ro_fun
				, ro_fun_case					= ro_fun
				, ro_fun_orig					= ro_fun
				, ro_fun_args					= tb.tb_args
				, ro_fun_geni					= (-1,-1)
				, ro_main_dcl_module_n			= main_dcl_module_n
				, ro_transform_fusion			= compile_with_fusion
				, ro_stdStrictLists_module_n	= stdStrictLists_module_n
				}
		  ti								= { ti & ti_var_heap = ti_var_heap } <-!- ("transform_function",fun,ro.ro_root_case_mode)
		  (fun_rhs, ti)						= transform tb.tb_rhs ro ti
		  fun_def							= { fun_def & fun_body = TransformedBody { tb & tb_rhs = fun_rhs }}
		# ti			= set_fun_def fun fun_def ti
		= ti
	  where
		store_arg_type_info {fv_info_ptr} a_type ti_var_heap
			= setExtendedVarInfo fv_info_ptr (EVI_VarType a_type) ti_var_heap
		
		fun_def_to_symb_ident fun_index fsize {fun_symb}
			| fun_index < fsize
			= { symb_name=fun_symb, symb_kind=SK_Function {glob_object=fun_index, glob_module=main_dcl_module_n } }

		get_root_case_mode {tb_rhs=Case _}	= RootCase
		get_root_case_mode _ 				= NotRootCase

		get_fun_def_and_symb_ident fun ti=:{ti_fun_defs}
			| fun < size ti_fun_defs
				# (fun_def, ti)						= ti!ti_fun_defs.[fun]
				# si = { symb_name=fun_def.fun_symb, symb_kind=SK_Function {glob_object=fun, glob_module=main_dcl_module_n } }
				= (fun_def,si,ti)
			# (fun_def_ptr,ti_fun_heap)			= lookup_ptr fun ti.ti_new_functions ti.ti_fun_heap
				with
					lookup_ptr fun [] ti_fun_heap = abort "drat"
					lookup_ptr fun [fun_def_ptr:new_functions] ti_fun_heap
						# (FI_Function {gf_fun_index}, ti_fun_heap)
								= readPtr fun_def_ptr ti_fun_heap
						| gf_fun_index == fun
							= (fun_def_ptr, ti_fun_heap)
							= lookup_ptr fun new_functions ti_fun_heap
			# (FI_Function {gf_fun_def}, ti_fun_heap)
											= readPtr fun_def_ptr ti_fun_heap
			# si = { symb_name=gf_fun_def.fun_symb, symb_kind=SK_GeneratedFunction fun_def_ptr fun }
			  ti								= { ti & ti_fun_heap = ti_fun_heap }
			= (gf_fun_def,si,ti)

	reannotate_producers group_nr group_members ti
		// determine if safe group
		# (safe,ti) = safe_producers group_nr group_members group_members ti
		| safe
			// if safe mark all members as safe
			= foldSt mark_producer_safe group_members ti
		= ti

	safe_producers group_nr group_members [] ti
		= (True,ti)
	safe_producers group_nr group_members [fun:funs] ti
		// look for occurrence of group_members in safe argument position of fun RHS
		// i.e. linearity ok && ...
		#! (fun_def, ti)	= get_fun_def fun ti
		   {fun_body = TransformedBody tb}
		   					= fun_def
		   fun_body			= tb.tb_rhs

		#! prs	=
			{ prs_group				= group_members
			, prs_cons_args 		= ti.ti_cons_args
			, prs_main_dcl_module_n	= main_dcl_module_n
			, prs_fun_heap			= ti.ti_fun_heap
			, prs_fun_defs			= ti.ti_fun_defs
			, prs_group_index		= group_nr
			}
		# (safe,prs)	= producerRequirements fun_body prs
		#! ti = {ti & ti_fun_defs = prs.prs_fun_defs, ti_fun_heap = prs.prs_fun_heap, ti_cons_args = prs.prs_cons_args}
		// put back prs info into ti?
		| safe //-!-> ("producerRequirements",fun_def.fun_symb,safe)
						= safe_producers group_nr group_members funs ti
		= (safe,ti)
	
	mark_producer_safe fun ti=:{ti_fun_defs}
		// update cc_prod for fun
		| fun < size ti_fun_defs
			= {ti & ti_cons_args.[fun].cc_producer = pIsSafe}
		# (fun_def_ptr,ti_fun_heap)			= lookup_ptr fun ti.ti_new_functions ti.ti_fun_heap
			with
				lookup_ptr fun [] ti_fun_heap = abort "drat"
				lookup_ptr fun [fun_def_ptr:new_functions] ti_fun_heap
					# (FI_Function {gf_fun_index}, ti_fun_heap)
							= readPtr fun_def_ptr ti_fun_heap
					| gf_fun_index == fun
						= (fun_def_ptr, ti_fun_heap)
						= lookup_ptr fun new_functions ti_fun_heap
		# (FI_Function gf, ti_fun_heap)
											= readPtr fun_def_ptr ti_fun_heap
		# ti_fun_heap						= writePtr fun_def_ptr (FI_Function {gf & gf_cons_args.cc_producer = pIsSafe}) ti_fun_heap
		  ti								= { ti & ti_fun_heap = ti_fun_heap }
		= ti
// ... DvA		

	add_new_function_to_group ::  !{# CommonDefs} !FunctionHeap  !FunctionInfoPtr
				!(!*{!Group}, ![FunDef], ![ConsClasses], !*ImportedTypes, !ImportedConstructors, !*TypeHeaps, !*VarHeap)
					-> (!*{!Group}, ![FunDef], ![ConsClasses], !*ImportedTypes, !ImportedConstructors, !*TypeHeaps, !*VarHeap)
	add_new_function_to_group common_defs fun_heap fun_ptr (groups, fun_defs, cons_classes, imported_types, collected_imports, type_heaps, var_heap)
		# (FI_Function {gf_fun_def,gf_fun_index,gf_cons_args}) = sreadPtr fun_ptr fun_heap
		  {fun_type = Yes ft=:{st_args,st_result}, fun_info = {fi_group_index,fi_properties}} = gf_fun_def
		  ets =
		  	{ ets_type_defs							= imported_types
		  	, ets_collected_conses					= collected_imports
		  	, ets_type_heaps						= type_heaps
		  	, ets_var_heap							= var_heap
		  	, ets_main_dcl_module_n					= main_dcl_module_n
		  	, ets_contains_unexpanded_abs_syn_type	= False
		  	}
		  (_,(st_result,st_args), {ets_type_defs, ets_collected_conses, ets_type_heaps, ets_var_heap})
		  		= expandSynTypes (if (fi_properties bitand FI_HasTypeSpec == 0) (RemoveAnnotationsMask bitor ExpandAbstractSynTypesMask) ExpandAbstractSynTypesMask) common_defs (st_result,st_args) ets
		# ft = { ft &  st_result = st_result, st_args = st_args }
		| fi_group_index >= size groups
			= abort ("add_new_function_to_group "+++ toString fi_group_index+++ "," +++ toString (size groups) +++ "," +++ toString gf_fun_index)
				  		
		# (group, groups) = groups![fi_group_index]
		| not (isMember gf_fun_index group.group_members)
			= abort ("add_new_function_to_group INSANE!\n" +++ toString gf_fun_index +++ "," +++ toString fi_group_index)
		# groups = {groups & [fi_group_index] = group}

		= (groups,
				[ { gf_fun_def & fun_type = Yes ft} : fun_defs], [gf_cons_args:cons_classes],
					ets_type_defs, ets_collected_conses, ets_type_heaps, ets_var_heap)
	
	convert_function_type common_defs fun_index (fun_defs, imported_types, collected_imports, fun_indices_with_abs_syn_types, type_heaps, var_heap)
		# (fun_def=:{fun_type = Yes fun_type, fun_info = {fi_properties}}, fun_defs)
					= fun_defs![fun_index]
		  rem_annot	= fi_properties bitand FI_HasTypeSpec == 0
		  (fun_type,contains_unexpanded_abs_syn_type,imported_types, collected_imports, type_heaps, var_heap)
		  		= convertSymbolType_ (if rem_annot RemoveAnnotationsMask 0) common_defs fun_type main_dcl_module_n imported_types collected_imports type_heaps var_heap
		# fun_def	= { fun_def & fun_type = Yes fun_type }
		  fun_defs	= { fun_defs & [fun_index] = fun_def }
		| contains_unexpanded_abs_syn_type
			= (fun_defs, imported_types, collected_imports, [fun_index : fun_indices_with_abs_syn_types], type_heaps, var_heap)
			= (fun_defs, imported_types, collected_imports, fun_indices_with_abs_syn_types, type_heaps, var_heap)

	expand_abstract_syn_types_in_function_type common_defs fun_index (fun_defs, imported_types, collected_imports, type_heaps, var_heap)
		# (fun_def=:{fun_type = Yes fun_type, fun_info = {fi_properties}}, fun_defs)
					= fun_defs![fun_index]
		  rem_annot	= fi_properties bitand FI_HasTypeSpec == 0
		  (fun_type,contains_unexpanded_abs_syn_type,imported_types, collected_imports, type_heaps, var_heap)
	  		= convertSymbolType_ (if rem_annot (RemoveAnnotationsMask bitor ExpandAbstractSynTypesMask) ExpandAbstractSynTypesMask) common_defs fun_type main_dcl_module_n imported_types collected_imports type_heaps var_heap
	  	  fun_def = { fun_def & fun_type = Yes fun_type}
	  	  fun_defs = { fun_defs & [fun_index] = fun_def }
		= (fun_defs, imported_types, collected_imports, type_heaps, var_heap)

//@ convertSymbolType

RemoveAnnotationsMask:==1
ExpandAbstractSynTypesMask:==2
		
convertSymbolType :: !Bool !{# CommonDefs} !SymbolType !Int !*ImportedTypes !ImportedConstructors !*TypeHeaps !*VarHeap 
	-> (!SymbolType, !*ImportedTypes, !ImportedConstructors, !*TypeHeaps, !*VarHeap)
convertSymbolType rem_annots common_defs st main_dcl_module_n imported_types collected_imports type_heaps var_heap
	# (st, ets_contains_unexpanded_abs_syn_type,ets_type_defs, ets_collected_conses, ets_type_heaps, ets_var_heap)
		= convertSymbolType_  (if rem_annots (RemoveAnnotationsMask bitor ExpandAbstractSynTypesMask) ExpandAbstractSynTypesMask) common_defs st main_dcl_module_n imported_types collected_imports type_heaps var_heap
	= (st, ets_type_defs, ets_collected_conses, ets_type_heaps, ets_var_heap)

convertSymbolType_ :: !Int !{# CommonDefs} !SymbolType !Int !*ImportedTypes !ImportedConstructors !*TypeHeaps !*VarHeap 
	-> (!SymbolType, !Bool,!*ImportedTypes, !ImportedConstructors, !*TypeHeaps, !*VarHeap)
convertSymbolType_  rem_annots common_defs st main_dcl_module_n imported_types collected_imports type_heaps var_heap
	# ets	=
				{ ets_type_defs			= imported_types
				, ets_collected_conses	= collected_imports
				, ets_type_heaps		= type_heaps
				, ets_var_heap			= var_heap
				, ets_main_dcl_module_n	= main_dcl_module_n 
				, ets_contains_unexpanded_abs_syn_type = False
				}	
	# {st_args,st_result,st_context,st_args_strictness}
										= st
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
	# {ets_type_defs, ets_collected_conses, ets_type_heaps, ets_var_heap,ets_contains_unexpanded_abs_syn_type}
										= ets
	= (st, ets_contains_unexpanded_abs_syn_type, ets_type_defs, ets_collected_conses, ets_type_heaps, ets_var_heap)

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

::	ExpandTypeState =
	{	ets_type_defs			:: !.{#{#CheckedTypeDef}}
	,	ets_collected_conses	:: !ImportedConstructors
	,	ets_type_heaps			:: !.TypeHeaps
	,	ets_var_heap			:: !.VarHeap
	,	ets_main_dcl_module_n :: !Int
	,	ets_contains_unexpanded_abs_syn_type :: !Bool
	}

class expandSynTypes a :: !Int !{# CommonDefs} !a !*ExpandTypeState -> (!Bool,!a, !*ExpandTypeState)

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
	expandSynTypes rem_annots common_defs tfa_type=:(TFA vars type) ets
		# (changed,type, ets) = expandSynTypes rem_annots common_defs type ets
		| changed
			= (True,TFA vars type, ets)
			= (False,tfa_type, ets)
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
		AbstractSynType _ rhs_type
			| (rem_annots bitand ExpandAbstractSynTypesMask)<>0
				# (type,ets_type_heaps) = bind_and_substitute_before_expand types td_args td_attribute rhs_type rem_annots attribute ets.ets_type_heaps
				# (_,type,ets) = expandSynTypes rem_annots common_defs type { ets & ets_type_heaps = ets_type_heaps }
				-> (True,type,ets)

				# ets = {ets & ets_contains_unexpanded_abs_syn_type=True }
				# (changed,types, ets) = expandSynTypes rem_annots common_defs types ets
				# ta_type = if changed
								( case ta_type of
									TA  type_symb _				-> TA  type_symb types
									TAS type_symb _ strictness	-> TAS type_symb types strictness
								) ta_type
				| glob_module == ets.ets_main_dcl_module_n
					-> (changed,ta_type, ets)
					-> (changed,ta_type, collect_imported_constructors common_defs glob_module td_rhs ets)
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
				| (rem_annots bitand RemoveAnnotationsMask)<>0
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

class clearVariables expr :: !expr !*VarHeap -> *VarHeap

instance clearVariables [a] | clearVariables a
where
	clearVariables list fvi
		= foldSt clearVariables list fvi

instance clearVariables LetBind
where
	clearVariables {lb_src} fvi
		= clearVariables lb_src fvi

instance clearVariables (Bind a b) | clearVariables a
where
	clearVariables {bind_src} fvi
		= clearVariables bind_src fvi

instance clearVariables (Optional a) | clearVariables a
where
	clearVariables (Yes x) fvi
		= clearVariables x fvi
	clearVariables No fvi
		= fvi

//XXX
instance clearVariables BoundVar
where
	clearVariables bound_var=:{var_info_ptr} var_heap
		# (var_info, var_heap) = readVarInfo var_info_ptr var_heap
		= case var_info of
			(VI_UsedVar _)	-> writeVarInfo var_info_ptr VI_Empty var_heap
			VI_LocalVar		-> writeVarInfo var_info_ptr VI_Empty var_heap
			VI_Empty		-> var_heap
			VI_Count _ _			-> abort "VI_Count"
			VI_Expression _			-> writeVarInfo var_info_ptr VI_Empty var_heap	//abort "VI_Expression"
			VI_Body _ _ _			-> abort "VI_Body"
			VI_Dictionary _ _ _		-> writeVarInfo var_info_ptr VI_Empty var_heap	//abort "VI_Dictionary"
			VI_Occurrence _			-> abort "VI_Occurrence"
			VI_Variable _ _			-> writeVarInfo var_info_ptr VI_Empty var_heap	//abort "VI_Variable"
			VI_AccVar _ _			-> writeVarInfo var_info_ptr VI_Empty var_heap	//abort "VI_AccVar"
			VI_Used					-> abort "VI_Used"
			VI_ExpandedType _		-> abort "VI_ExpandedType"
			v				-> abort "unexpected VI type in clearVariables\n"

instance clearVariables Expression
where
	clearVariables (Var var) fvi
		= clearVariables var fvi
	clearVariables (App {app_args}) fvi
		= clearVariables app_args fvi
	clearVariables (fun @ args) fvi
		= clearVariables args (clearVariables fun fvi)
	clearVariables (Let {let_strict_binds,let_lazy_binds,let_expr}) fvi
		# fvi = clearVariables let_strict_binds fvi
		  fvi = clearVariables let_lazy_binds fvi
		  fvi = clearVariables let_expr fvi
		= fvi
	clearVariables (Case {case_expr,case_guards,case_default}) fvi
		# fvi = clearVariables case_expr fvi
		  fvi = clearVariables case_guards fvi
		  fvi = clearVariables case_default fvi
		= fvi

	clearVariables (Selection _ expr selectors) fvi
		= clearVariables expr (clearVariables selectors fvi)
	clearVariables (Update expr1 selectors expr2) fvi
		= clearVariables expr2 (clearVariables selectors (clearVariables expr1 fvi))
	clearVariables (RecordUpdate cons_symbol expression expressions) fvi
		= clearVariables expression (clearVariables expressions fvi)
	clearVariables (TupleSelect _ arg_nr expr) fvi
		= clearVariables expr fvi
	clearVariables (MatchExpr _ expr) fvi
		= clearVariables expr fvi
	clearVariables EE fvi
		= fvi
	clearVariables _ fvi
		= fvi

instance clearVariables CasePatterns
where
	clearVariables (AlgebraicPatterns _ alg_patterns) fvi
		= foldSt clearVariables alg_patterns fvi
	clearVariables (BasicPatterns _ basic_patterns) fvi
		= foldSt clearVariables basic_patterns fvi
	clearVariables (OverloadedListPatterns _ _ alg_patterns) fvi
		= foldSt clearVariables alg_patterns fvi

instance clearVariables BasicPattern
where
	clearVariables {bp_expr} fvi
		= clearVariables bp_expr fvi

instance clearVariables AlgebraicPattern
where
	clearVariables {ap_vars, ap_expr} fvi
		= clearVariables ap_expr fvi
		
instance clearVariables Selection
where
	clearVariables (RecordSelection _ _) fvi
		= fvi
	clearVariables (ArraySelection _ _ expr) fvi
		= clearVariables expr fvi
	clearVariables (DictionarySelection dict_var selections _ expr) fvi
		= clearVariables dict_var (clearVariables selections (clearVariables expr fvi))
	
////////////////

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
		= freeVariables selectors (freeVariables expr fvi)
	freeVariables (Update expr1 selectors expr2) fvi
		= freeVariables expr2 (freeVariables selectors (freeVariables expr1 fvi))
	freeVariables (RecordUpdate cons_symbol expression expressions) fvi
		= freeVariables expressions (freeVariables expression fvi)
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
		# (rec,prs)			= is_recursive_app app prs
		| not rec
			= producerRequirements app_args prs
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

retrieve_consumer_args :: !SymbIdent !*PRState -> (!Optional ConsClasses, !*PRState)
retrieve_consumer_args si=:{symb_kind} prs=:{prs_cons_args, prs_main_dcl_module_n}
	# (prs_size, prs_cons_args) = usize prs_cons_args
	  prs = {prs & prs_cons_args = prs_cons_args}
	= case symb_kind of
		SK_Function {glob_module, glob_object}
			| glob_module == prs_main_dcl_module_n && glob_object < prs_size
				# (cons_args,prs) = prs!prs_cons_args.[glob_object]
				-> (Yes cons_args,prs)
			-> (No,prs) -!-> ("r_c_a",si)
		SK_LocalMacroFunction glob_object
			| glob_object < prs_size
				# (cons_args,prs) = prs!prs_cons_args.[glob_object]
				-> (Yes cons_args,prs)
			-> (No,prs) -!-> ("r_c_a",si)
		SK_GeneratedFunction fun_ptr fun_index
			| fun_index < prs_size
				# (cons_args,prs) = prs!prs_cons_args.[fun_index]
				-> (Yes cons_args,prs)
			# (FI_Function {gf_cons_args}, fun_heap)	= readPtr fun_ptr prs.prs_fun_heap
			# prs										= {prs & prs_fun_heap = fun_heap}
			-> (Yes gf_cons_args,prs)
//		SK_Constructor cons_index
		sk -> (No -!-> ("Unexpected symbol kind: ", si, sk),prs)

//@ <<<

instance <<< Group where
	(<<<) file {group_members}
	 = file <<< "Group: " <<< group_members
	
instance <<< RootCaseMode where
	(<<<) file mode = case mode of NotRootCase -> file <<< "NotRootCase"; RootCase -> file <<< "RootCase"; RootCaseOfZombie -> file <<< "RootCaseOfZombie";

/*
instance <<< InstanceInfo
where
	(<<<) file (II_Node prods _ left right) = file <<< left <<< prods <<< right 
	(<<<) file II_Empty = file 
*/	

// XXX	
/*
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
*/
/*
instance <<< {!Producer}
where
	(<<<) file array
		# file = file <<< "{"
		= showBody 0 (size array) array file
	where
		showBody i m a f
			| i >= m	= f <<< "}"
						= showBody (inc i) m a (f <<< a.[i] <<< ", ")
*/
instance <<< Producer where
	(<<<) file PR_Empty
		= file <<< "(E)"
	(<<<) file PR_Unused
		= file <<< "(U)"
	(<<<) file (PR_Function ident int index)
		= file <<< "(F:" <<< ident <<< ")"
	(<<<) file (PR_Class app binds type)
		= file <<< "(O::" <<< app.app_symb <<< ")"
	(<<<) file (PR_Constructor ident int exprl)
		= file <<< "(C:" <<< ident <<< ")"
	(<<<) file (PR_GeneratedFunction ident int index)
		= file <<< "(G:" <<< ident <<< ")"
	(<<<) file (PR_Curried ident int)
		= file <<< "(P:" <<< ident <<< ")"

instance <<< SymbKind
where
	(<<<) file SK_Unknown = file <<< "(SK_Unknown)"
	(<<<) file (SK_Function gi) = file <<< "(SK_Function)" <<< gi
	(<<<) file (SK_IclMacro gi) = file <<< "(SK_IclMacro)" <<< gi
	(<<<) file (SK_LocalMacroFunction gi) = file <<< "(SK_LocalMacroFunction)" <<< gi
	(<<<) file (SK_DclMacro gi) = file <<< "(SK_DclMacro)" <<< gi
	(<<<) file (SK_LocalDclMacroFunction gi) = file <<< "(SK_LocalDclMacroFunction)" <<< gi
	(<<<) file (SK_OverloadedFunction gi) = file <<< "(SK_OverloadedFunction)" <<< gi
	(<<<) file (SK_GeneratedFunction _ gi) = file <<< "(SK_GeneratedFunction)" <<< gi
	(<<<) file (SK_Constructor gi) = file <<< "(SK_Constructor)" <<< gi
	(<<<) file (SK_Generic gi tk) = file <<< "(SK_Constructor)" <<< gi
	(<<<) file SK_TypeCode = file <<< "(SK_TypeCode)"
	(<<<) file _ = file <<< "(SK_UNKNOWN)"
	
instance <<< ConsClasses
where
	(<<<) file {cc_args,cc_linear_bits,cc_producer} = file <<< cc_args <<< cc_linear_bits <<< cc_producer
	
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

// SPECIAL...
instance <<< Specials
where
	(<<<) file spec = case spec of
		(SP_ParsedSubstitutions 	_)	-> file <<< "SP_ParsedSubstitutions"
		(SP_Substitutions 		 	_)	-> file <<< "SP_Substitutions"
		(SP_ContextTypes			l)	-> file <<< "(SP_ContextTypes: " <<< l <<< ")"
		(SP_FunIndex				i)	-> file <<< "(SP_FunIndex: " <<< i <<< ")"
		(SP_TypeOffset				_)	-> file <<< "SP_TypeOffset"
		SP_None							-> file <<< "SP_None"

instance <<< Special
where
	(<<<) file {spec_index,spec_types,spec_vars,spec_attrs}
		= file <<< "spec_index" <<< spec_index <<< "spec_types" <<< spec_types <<< "spec_vars" <<< spec_vars <<< "spec_attrs" <<< spec_attrs

instance <<< ExprInfo
where
	(<<<) file EI_Empty = file <<< "EI_Empty"
	(<<<) file (EI_DictionaryType t) = file <<< "<EI_DictionaryType: " <<< t <<< ">"
//	(<<<) file (EI_Instance symb exprs) = file <<< symb <<< exprs
//	(<<<) file (EI_Selection sels var_ptr exprs) = file <<< sels <<< var_ptr <<< exprs
//	(<<<) file (EI_Context exprs) = file <<< exprs
	(<<<) file _ = file <<< "EI_Other"

instance <<< TypeContext
where
	(<<<) file co = file <<< co.tc_class <<< " " <<< co.tc_types <<< " <" <<< co.tc_var <<< '>'

resolveContext :: [TypeContext] [ExprInfo] -> [[Type]]
resolveContext [tc:tcs] [EI_DictionaryType t:eis]
	= minimiseContext tc t ++ resolveContext tcs eis
resolveContext _ _ = []

minimiseContext {tc_class = TCClass gds} (TA ti ts)
	# tc_index = {glob_module = gds.glob_module, glob_object = gds.glob_object.ds_index}
	| tc_index == ti.type_index
		= [[at_type \\ {at_type} <- ts]]
		= []
minimiseContext _ _ = []

findInstInSpecials insts []
	= (0,{glob_object= -1,glob_module = -1})
findInstInSpecials insts [{spec_types,spec_index}:specials]
	| matchTypes insts spec_types
		= (length spec_types, spec_index)
	= findInstInSpecials insts specials

matchTypes [] [] = True
matchTypes [l:ls] [r:rs]
	= l == r && matchTypes ls rs
matchTypes _ _ = False

foundSpecial {glob_object= -1,glob_module = -1}	= False
foundSpecial _ = True	

// ...SPECIAL

arity_warning msg symb_name fun_index fun_arity ti
	| fun_arity <= 32
		= ti
	= {ti & ti_error_file = ti.ti_error_file <<< "Warning: Arity > 32 " <<< msg <<< " " <<< fun_arity <<< " " <<< symb_name <<< "@" <<< fun_index <<< "\n"}
	
strip_universal_quantor :: SymbolType -> SymbolType
strip_universal_quantor st=:{st_vars,st_args,st_result}
	# (st_result,st_vars)	= strip st_result st_vars
	# (st_args,st_vars)		= mapSt strip st_args st_vars
	= {st & st_vars = st_vars, st_args = st_args, st_result = st_result}
where
	strip :: AType [TypeVar] -> (AType,[TypeVar])
	strip atype=:{at_type = TFA vars type} tvs
		= ({atype & at_type = type}, map (\{atv_variable}->atv_variable) vars ++ tvs)
	strip atype tvs
		= (atype,tvs)

mapOpt f [Yes a:x]	= [Yes (f a):mapOpt f x]
mapOpt f [No:x]		= [No:mapOpt f x]
mapOpt f [] 		= []
