/*
	module owner: Ronny Wichers Schreur
*/
implementation module convertDynamics

import syntax, transform, utilities, convertcases, compilerSwitches
// import RWSDebug

from type_io_common import PredefinedModuleName
// Optional
extended_unify_and_coerce no yes :== no;	// change also _unify and _coerce in StdDynamic

import type_io;
//import pp;

/*2.0
from type_io_common import class toString (..),instance toString GlobalTCType;
0.2*/

::	*ConversionState =
	{	ci_predef_symb		:: !*PredefinedSymbols
	,	ci_var_heap			:: !*VarHeap
	,	ci_expr_heap		:: !*ExpressionHeap
	,	ci_new_variables 	:: ![FreeVar]

	,	ci_type_pattern_var_count	:: !Int	
	//	data needed to generate coercions
	,	ci_module_id_symbol						:: Expression
	,	ci_module_id_var						:: Optional LetBind
	,	ci_type_constructor_used_in_dynamic_patterns	:: !*{#Bool}
	}

:: DynamicRepresentation =
	{	dr_type_ident		:: SymbIdent
	,	dr_dynamic_type		:: Global Index
	,	dr_dynamic_symbol	:: Global DefinedSymbol
	}

::	ConversionInput =
	{	cinp_glob_type_inst	:: !{! GlobalTCType} 
	,	cinp_dynamic_representation	:: DynamicRepresentation
	,	cinp_st_args		:: ![FreeVar]
	,	cinp_subst_var		:: !BoundVar
	}

F :: !a .b -> .b
F a b = b


//write_tcl_file :: !Int {#DclModule} CommonDefs !*File [String] -> (.Bool,.File)
//write_tcl_file :: !Int {#DclModule} CommonDefs !*File [String] _ _ !*TypeHeaps !*PredefinedSymbols -> (.Bool,.File,!*TypeHeaps,!*PredefinedSymbols)
// write_tcl_file ({#},{!},{#},[{#Char}],CommonDefs,{#}) :: !.Int !{#y:DclModule} CommonDefs !*File [{#Char}] !{!x:GlobalTCType} {#w:Bool} !*TypeHeaps !{#v:PredefinedSymbol} -> (.Bool,.File,.TypeHeaps,{#PredefinedSymbol}), [u <= 
write_tcl_file main_dcl_module_n dcl_mods=:{[main_dcl_module_n] = main_dcl_module} common_defs tcl_file directly_imported_dcl_modules global_type_instances ci_type_constructor_used_in_dynamic_patterns type_heaps predefined_symbols
	# (pre_mod, predefined_symbols) = predefined_symbols![PD_PredefinedModule]
	# write_type_info_state2
		= { WriteTypeInfoState |
			wtis_type_heaps				= type_heaps
		,	wtis_n_type_vars			= 0
		,	wtis_predefined_module_def	= pre_mod.pds_module
		};
	# (j,tcl_file)
		= fposition tcl_file

	#! (tcl_file,write_type_info_state)
		= write_type_info common_defs tcl_file write_type_info_state2
	#! (tcl_file,write_type_info_state)
		= write_type_info directly_imported_dcl_modules tcl_file write_type_info_state

	// dynamic pattern matches
	#! type_constructors_in_dynamic_patterns
		= collect_type_constructors_in_dynamic_patterns 0 (size global_type_instances) []
	#! (tcl_file,write_type_info_state)
		= write_type_info type_constructors_in_dynamic_patterns tcl_file write_type_info_state

	#! (tcl_file,write_type_info_state)
		= write_type_info (help_20_compiler { dcl_name.id_name\\ {dcl_name} <-: dcl_mods }) tcl_file write_type_info_state
			with 
				help_20_compiler :: {#{#Char}} -> {#{#Char}}
				help_20_compiler l = l
		
	#! (type_heaps,_)
		= f write_type_info_state;	
		
	#! tcl_file
		= fwritei (size main_dcl_module.dcl_common.com_type_defs) tcl_file
	#! tcl_file
		= fwritei (size main_dcl_module.dcl_common.com_cons_defs) tcl_file
				
	= (True,tcl_file,type_heaps,predefined_symbols) 
where
	collect_type_constructors_in_dynamic_patterns :: !Int !Int [TypeSymbIdent] -> [TypeSymbIdent]
	collect_type_constructors_in_dynamic_patterns i limit type_constructors_in_dynamic_patterns
		| i == limit
			= type_constructors_in_dynamic_patterns
			
			| isGTT_Constructor global_type_instances.[i]
				# (GTT_Constructor type_name=:{type_name={id_name}} module_name used_in_application_of_type_dependent_function)
					= global_type_instances.[i]
				| used_in_application_of_type_dependent_function || ci_type_constructor_used_in_dynamic_patterns.[i]
					= collect_type_constructors_in_dynamic_patterns (inc i) limit [type_name:type_constructors_in_dynamic_patterns]
					= collect_type_constructors_in_dynamic_patterns (inc i) limit type_constructors_in_dynamic_patterns
				= collect_type_constructors_in_dynamic_patterns (inc i) limit type_constructors_in_dynamic_patterns
	where
		isGTT_Constructor (GTT_Constructor _ _ _)	= True
		isGTT_Constructor _							= False
		
	f write_type_info_state=:{wtis_type_heaps}
		= (wtis_type_heaps,{write_type_info_state & wtis_type_heaps = abort "convertDynamics.icl"});

/*2.0
f (Yes tcl_file)
	= tcl_file;
0.2*/
			
convertDynamicPatternsIntoUnifyAppls :: {! GlobalTCType} !{# CommonDefs} !Int !*{! Group} !*{#FunDef} !*PredefinedSymbols !*VarHeap !*TypeHeaps !*ExpressionHeap (Optional *File) {# DclModule} !IclModule [String]
			-> (!*{! Group}, !*{#FunDef}, !*PredefinedSymbols, !*{#{# CheckedTypeDef}}, !ImportedConstructors, !*VarHeap, !*TypeHeaps, !*ExpressionHeap, (Optional *File))
convertDynamicPatternsIntoUnifyAppls global_type_instances common_defs main_dcl_module_n groups fun_defs predefined_symbols var_heap type_heaps expr_heap tcl_file dcl_mods icl_mod directly_imported_dcl_modules
	#! (dynamic_representation,predefined_symbols)
		=	create_dynamic_and_selector_idents common_defs predefined_symbols
/*
	# (module_symb,module_id,predefined_symbols)
		= get_module_id_app predefined_symbols
	# ({pds_module=pds_type_id_module, pds_def=pds_type_id_def} , predefined_symbols) = predefined_symbols![PD_TypeID]
	# type_id
		=	{	type_name	= common_defs.[pds_type_id_module].com_type_defs.[pds_type_id_def].td_name
			,	type_arity	= 0
			,	type_index	= { glob_object = pds_type_id_def, glob_module = pds_type_id_module}
			,	type_prop	= { tsp_sign = BottomSignClass, tsp_propagation = NoPropClass, tsp_coercible = True }
			}
*/
	# type_id = undef
	# (module_symb,module_id,predefined_symbols)
		= get_module_id_app predefined_symbols

	#! nr_of_funs = size fun_defs
	#! s_global_type_instances = size global_type_instances
	# imported_types = {com_type_defs \\ {com_type_defs} <-: common_defs }
	# (groups, (fun_defs, {ci_predef_symb, ci_var_heap, ci_expr_heap, ci_type_constructor_used_in_dynamic_patterns}))
			= convert_groups 0 groups global_type_instances type_id module_id dynamic_representation (fun_defs, {	
							ci_predef_symb = predefined_symbols, ci_var_heap = var_heap, ci_expr_heap = expr_heap,
							ci_new_variables = [],
							ci_type_pattern_var_count = 0,
							ci_module_id_symbol = App module_symb,
							ci_module_id_var  = No,
							ci_type_constructor_used_in_dynamic_patterns	= createArray s_global_type_instances False
							})
			
	// store type info			
	# (tcl_file,type_heaps,ci_predef_symb)
		= case tcl_file of
			No
				-> (No,type_heaps,ci_predef_symb)
			_ 
				# tcl_file = f tcl_file;
				# (ok,tcl_file,type_heaps,ci_predef_symb)
					= write_tcl_file main_dcl_module_n dcl_mods icl_mod.icl_common tcl_file directly_imported_dcl_modules global_type_instances ci_type_constructor_used_in_dynamic_patterns type_heaps ci_predef_symb
				| not ok
					-> abort "convertDynamicPatternsIntoUnifyAppls: error writing tcl file"
					-> (Yes tcl_file,type_heaps,ci_predef_symb)

	= (groups, fun_defs, ci_predef_symb, imported_types, [], ci_var_heap, type_heaps, ci_expr_heap, tcl_file)
where
	convert_groups group_nr groups global_type_instances type_id module_id dynamic_representation fun_defs_and_ci
		| group_nr == size groups
			= (groups, fun_defs_and_ci)
			# (group, groups) = groups![group_nr]
			= convert_groups (inc group_nr) groups global_type_instances type_id module_id dynamic_representation (foldSt (convert_function group_nr global_type_instances type_id module_id dynamic_representation) group.group_members fun_defs_and_ci)

	convert_function group_nr global_type_instances type_id module_id dynamic_representation fun (fun_defs, ci)
		# (fun_def, fun_defs) = fun_defs![fun]
		  {fun_body, fun_type, fun_info} = fun_def
		| isEmpty fun_info.fi_dynamics
			= (fun_defs, ci)
			
			// For each function which uses dynamics, a module id is constructed regardless
			// of its use. In some very specific cases, the let generated here is superfluous.
			# (TransformedBody fun_body=:{tb_rhs})
				= fun_body
			# (tb_rhs, ci)
				= share_module_identification tb_rhs module_id ci
			# fun_body
				= {fun_body & tb_rhs = tb_rhs}
			# fun_body
				= TransformedBody fun_body
			
			# (unify_subst_var, ci)
			  	=	newVariable "unify_subst" VI_Empty ci
			# ci
				= {ci & ci_type_pattern_var_count = 0}

			# (fun_body, ci) = convertDynamics {cinp_st_args = [], cinp_dynamic_representation = dynamic_representation,
					cinp_glob_type_inst = global_type_instances,
					cinp_subst_var = unify_subst_var} fun_body ci

			= ({fun_defs & [fun] = { fun_def & fun_body = fun_body, fun_info = { fun_info & fi_local_vars = ci.ci_new_variables ++ fun_info.fi_local_vars }}},
				{ ci & ci_new_variables = [] })
		where
			share_module_identification rhs module_id ci
				# (dst=:{var_info_ptr},ci)
					= newVariable "module_id" VI_Empty ci
				# dst_fv
					= varToFreeVar dst 1
				# let_bind
					= { lb_src = module_id
					,	lb_dst = dst_fv
					,	lb_position = NoPos
					}

				# ci
					= { ci & 
						ci_new_variables	= [ dst_fv : ci.ci_new_variables ]
					,	ci_module_id_var		= Yes let_bind
					}

				# (let_info_ptr,  ci)	= let_ptr2 [toAType TE] ci
				# rhs
					= Let {	let_strict_binds	= [],
							let_lazy_binds		= [let_bind],
							let_expr			= rhs,
							let_info_ptr		= let_info_ptr,
							let_expr_position	= NoPos
					}
				=	(rhs, ci)


class convertDynamics a :: !ConversionInput !a !*ConversionState -> (!a, !*ConversionState)

instance convertDynamics [a] | convertDynamics a where
	convertDynamics cinp xs ci
		=	mapSt (convertDynamics cinp) xs ci

instance convertDynamics (Optional a) | convertDynamics a where
	convertDynamics cinp (Yes x) ci
		# (x, ci)
			=	convertDynamics cinp x ci
		=	(Yes x, ci)
	convertDynamics _ No ci
		=	(No, ci)

instance convertDynamics FunctionBody where
	convertDynamics cinp (TransformedBody body) ci
		# (body, ci)
			=	convertDynamics cinp body ci
		=	(TransformedBody body, ci)

instance convertDynamics TransformedBody where
	convertDynamics cinp body=:{tb_args,tb_rhs} ci=:{ci_var_heap}
		// this actually marks all arguments as type terms (also the regular arguments
		// and dictionaries)
		# ci_var_heap
			=	foldSt mark_var tb_args ci_var_heap
		# (tb_rhs, ci)
			=	convertDynamics cinp tb_rhs {ci & ci_var_heap = ci_var_heap}
		# (global_tpvs, subst, ci)
			=	foldSt collect_global_type_pattern_var tb_args ([], cinp.cinp_subst_var, ci)
		# (tb_rhs, ci)
			=	share_init_subst subst global_tpvs tb_rhs ci
		=	({body & tb_rhs = tb_rhs}, ci)
		where
			mark_var :: FreeVar *VarHeap -> *VarHeap
			mark_var {fv_info_ptr} var_heap
				=	writePtr fv_info_ptr (VI_TypeCodeVariable TCI_TypeTerm) var_heap

			collect_global_type_pattern_var :: FreeVar ([LetBind], BoundVar, *ConversionState) -> ([LetBind], BoundVar, *ConversionState)
			collect_global_type_pattern_var {fv_info_ptr} (l, subst, ci)
				# (var_info, ci_var_heap)
					=	readPtr fv_info_ptr ci.ci_var_heap
				# ci
					=	{ci & ci_var_heap = ci_var_heap}
				=	case var_info of
						VI_TypeCodeVariable (TCI_TypeVar tpv)
							# (bind_global_tpv_symb, ci) 
								=	getSymbol PD_Dyn_bind_global_type_pattern_var SK_Function 3 ci
							# type_code
								=	{var_name = a_ij_var_name, var_info_ptr = fv_info_ptr, var_expr_ptr = nilPtr}
							# (unify_subst_var, ci)
							  	=	newVariable "gtpv_subst" VI_Empty ci
							  unify_subst_fv
							  	=	varToFreeVar unify_subst_var 1
							# let_bind
								= { lb_src = App {	app_symb		= bind_global_tpv_symb,
													app_args 		= [tpv, Var type_code, Var unify_subst_var],
													app_info_ptr	= nilPtr }
								,	lb_dst =  varToFreeVar subst 1
								,	lb_position = NoPos
								}
							->	([let_bind:l], unify_subst_var, ci)
						_
							->	(l, subst, ci)

			share_init_subst :: BoundVar [LetBind] Expression *ConversionState
					-> (Expression, *ConversionState)
			share_init_subst subst global_tpv_binds rhs ci=:{ci_type_pattern_var_count}
				#  (initial_unifier_symb, ci) 
					=	getSymbol PD_Dyn_initial_unifier SK_Function 1 ci

				# let_bind_initial_subst
					= { lb_src = App {	app_symb		= initial_unifier_symb,
										app_args 		= [BasicExpr (BVInt ci_type_pattern_var_count)],
										app_info_ptr	= nilPtr }
					,	lb_dst =  varToFreeVar subst 1
					,	lb_position = NoPos
					}

				# let_binds
					=	[let_bind_initial_subst : global_tpv_binds]
				# (let_info_ptr,  ci)	= let_ptr (length let_binds) ci
				# ci
					= { ci & 
						ci_new_variables	= [lb_dst  \\ {lb_dst} <- let_binds] ++ ci.ci_new_variables
					}
				# rhs
					= Let {	let_strict_binds	= [],
							let_lazy_binds		= let_binds,
							let_expr			= rhs,
							let_info_ptr		= let_info_ptr,
							let_expr_position	= NoPos
					}
				=	(rhs, ci)

instance convertDynamics LetBind where
	convertDynamics cinp binding=:{lb_src} ci
		# (lb_src, ci)
			=	convertDynamics cinp lb_src ci
		=	({binding &  lb_src = lb_src}, ci)

instance convertDynamics (Bind a b) | convertDynamics a where
	convertDynamics cinp binding=:{bind_src} ci
		# (bind_src, ci)
			=	convertDynamics cinp bind_src ci
		=	({binding &  bind_src = bind_src}, ci)

instance convertDynamics Expression where
	convertDynamics cinp (TypeCodeExpression tce) ci
		# (type_code, ci)
			=	convertExprTypeCode cinp tce ci
		# (normalise_symb, ci) 
			=	getSymbol PD_Dyn_normalise SK_Function 2 ci
		# normalise_call
			=	App { app_symb = normalise_symb,  app_args = [ Var cinp.cinp_subst_var, type_code],  app_info_ptr = nilPtr }
		=	(normalise_call, ci)
	convertDynamics cinp (Var var) ci
		# (info, ci_var_heap)
			=	readPtr var.var_info_ptr ci.ci_var_heap
		# ci
			=	{ci & ci_var_heap = ci_var_heap}
		=	case (info, ci) of
				(VI_DynamicValueAlias value_var, ci)
					->	(Var value_var, ci)
				(_, ci)
					->	(Var var, ci)
	convertDynamics cinp (App app) ci
		# (app, ci)
			= convertDynamics cinp app ci
		=	(App app, ci)
	convertDynamics cinp (expr @ exprs) ci
		# (expr, ci)
			=	convertDynamics cinp expr  ci
		  (exprs, ci)
		  	=	convertDynamics cinp exprs ci
		=	(expr @ exprs, ci)
	convertDynamics cinp (Let letje) ci
		# (letje, ci)
			=	convertDynamics cinp letje  ci
		=	(Let letje, ci)
	convertDynamics cinp (Case kees) ci
		# (kees,  ci)
			=	convertDynamics cinp kees  ci
		=	(Case kees, ci)
	convertDynamics cinp (Selection opt_symb expression selections) ci
		# (expression,ci)
			=	convertDynamics cinp expression ci
		# (selections,ci)
			=	convertDynamics cinp selections ci
		=	(Selection opt_symb expression selections, ci)
	convertDynamics cinp (Update expression1 selections expression2) ci
		# (expression1, ci)
			=	convertDynamics cinp expression1 ci
		# (selections, ci)
			=	convertDynamics cinp selections ci
		# (expression2, ci)
			=	convertDynamics cinp expression2 ci
		=	(Update expression1 selections expression2, ci)
	convertDynamics cinp (RecordUpdate cons_symbol expression expressions) ci
		# (expression, ci)
			=	convertDynamics cinp expression ci
		# (expressions, ci)
			=	convertDynamics cinp expressions ci
		=	(RecordUpdate cons_symbol expression expressions, ci)
	convertDynamics cinp (TupleSelect definedSymbol int expression) ci
		# (expression, ci)
			=	convertDynamics cinp expression ci
		=	(TupleSelect definedSymbol int expression, ci)
	convertDynamics _ be=:(BasicExpr _) ci
		=	(be, ci)
	convertDynamics _ code_expr=:(AnyCodeExpr _ _ _) ci
		=	(code_expr, ci)
	convertDynamics _ code_expr=:(ABCCodeExpr _ _) ci
		=	(code_expr, ci)
	convertDynamics cinp (MatchExpr symb expression) ci
		# (expression, ci)
			=	convertDynamics cinp expression ci
		=	(MatchExpr symb expression, ci)
	convertDynamics cinp (DynamicExpr dyno) ci
		=	convertDynamic cinp dyno ci
	convertDynamics cinp EE ci
		=	(EE, ci)
	convertDynamics cinp expr=:(NoBind _) ci
		=	(expr,ci)

instance convertDynamics App where
	convertDynamics cinp app=:{app_args} ci
		# (app_args,ci)
			=	convertDynamics cinp app_args ci
		=	({app & app_args = app_args}, ci)

instance convertDynamics Let where
	convertDynamics cinp letje=:{let_strict_binds, let_lazy_binds,
											let_expr, let_info_ptr} ci
		# (let_strict_binds, ci)
		  	=	convertDynamics cinp let_strict_binds ci
		  (let_lazy_binds, ci)
		  	=	convertDynamics cinp let_lazy_binds ci
		  (let_expr,  ci)
		   	=	convertDynamics cinp let_expr  ci
		  letje
		  	=	{ letje &  let_strict_binds = let_strict_binds,
		  			let_lazy_binds = let_lazy_binds, let_expr = let_expr}
		= (letje, ci)

instance convertDynamics Case where
	convertDynamics cinp kees=:{case_expr, case_guards, case_default} ci
		# (case_expr, ci)
			=	convertDynamics cinp case_expr ci
		# (case_default, ci)
			=	convertDynamics cinp case_default ci
		# kees
			=	{kees & case_expr=case_expr, case_default=case_default}
		= case case_guards of
			DynamicPatterns alts
				->	convertDynamicCase cinp kees ci
			_
				# (case_guards, ci)
					=	convertDynamics cinp case_guards ci
				# kees
					=	{kees & case_explicit=False, case_guards=case_guards}
				->	(kees, ci)

instance convertDynamics CasePatterns where
	convertDynamics cinp (BasicPatterns type alts) ci
		# (alts, ci)
			=	convertDynamics cinp alts ci
		=	(BasicPatterns type alts, ci)
	convertDynamics cinp (AlgebraicPatterns type alts) ci
		# (alts, ci)
			=	convertDynamics cinp alts ci
		=	(AlgebraicPatterns type alts, ci)
	convertDynamics cinp (OverloadedListPatterns type decons alts) ci
		# (alts, ci)
			=	convertDynamics cinp alts ci
		=	(OverloadedListPatterns type decons alts, ci)

convertDynamic cinp=:{cinp_dynamic_representation={dr_type_ident}}
					{dyn_expr, dyn_type_code} ci
	# (dyn_expr, ci)
		=	convertDynamics cinp dyn_expr ci
	# (dyn_type_code, ci)
		=	convertExprTypeCode cinp dyn_type_code ci

	#  (normalise_symb, ci) 
		=	getSymbol PD_Dyn_normalise SK_Function 2 ci

	# normalise_call
		=	App { app_symb = normalise_symb,  app_args = [ Var cinp.cinp_subst_var, dyn_type_code],  app_info_ptr = nilPtr }

	=	(App {	app_symb		= dr_type_ident,
				app_args 		= [dyn_expr, normalise_call],
				app_info_ptr	= nilPtr }, ci)

convertDynamicCase cinp=:{cinp_dynamic_representation={dr_dynamic_symbol, dr_dynamic_type}}
			kees=:{case_guards=DynamicPatterns alts, case_info_ptr, case_default} ci
	# (value_var, ci)
		=	newVariable "value" VI_Empty ci
	# (type_var, ci)
		=	newVariable "type" VI_Empty ci
	# ci
		=	{ci & ci_new_variables	= [varToFreeVar value_var 1, varToFreeVar type_var 1 : ci.ci_new_variables ]}

	# (result_type, ci)
		=	getResultType case_info_ptr ci
	# (matches, ci)
		=	case convertDynamicAlts cinp kees type_var value_var result_type case_default alts ci of
				(Yes matches, ci) -> (matches, ci)
				_ -> abort "where are those converted dynamics?"
	# match =
		{	ap_symbol	= dr_dynamic_symbol
		,	ap_vars		= [varToFreeVar value_var 1, varToFreeVar type_var 1]
		,	ap_expr		= matches
		,	ap_position	= position alts
		}
	# (case_info_ptr, ci)
		=	dummy_case_ptr result_type ci
	# kees
		=	{kees & case_explicit=False, case_guards=AlgebraicPatterns dr_dynamic_type [match],
								case_default=No, case_info_ptr = case_info_ptr}
	=	(kees, ci)

convertDynamicAlts _ _ _ _ _ defoult [] ci
	=	(defoult, ci)
convertDynamicAlts cinp kees type_var value_var result_type defoult [{dp_rhs, dp_position, dp_type_code, dp_var}:alts] ci
	# (type_code, binds, ci)
		=	convertPatternTypeCode cinp dp_type_code ci

	#  (unify_symb, ci) 
		=	getSymbol PD_Dyn_unify SK_Function (extended_unify_and_coerce 3 4) /*3 was 2 */ ci

	# unify_call
		=	App { app_symb = unify_symb,  app_args = [ Var cinp.cinp_subst_var, Var type_var, type_code],  app_info_ptr = nilPtr }

	// FIXME, more precise types (not all TEs)
	# (let_info_ptr, ci)
		=	let_ptr (/* 4 */ 3+length binds) ci

	  (unify_result_var, ci)
	  	=	newVariable "result" VI_Empty ci
	  unify_result_fv
	  	=	varToFreeVar unify_result_var 1
	  (unify_bool_var, ci)
	  	=	newVariable "unify_bool" VI_Empty ci
	  unify_bool_fv
	  	=	varToFreeVar unify_bool_var 1

	  (unify_subst_var, ci)
	  	=	newVariable "unify_subst" VI_Empty ci
	  unify_subst_fv
	  	=	varToFreeVar unify_subst_var 1

	# ci_var_heap = writePtr dp_var.fv_info_ptr (VI_DynamicValueAlias value_var) ci.ci_var_heap
	# ci = {ci & ci_var_heap = ci_var_heap}

	# (dp_rhs, ci)
		=	convertDynamics {cinp & cinp_subst_var=unify_subst_var} dp_rhs ci

	# (case_info_ptr, ci)
		=	bool_case_ptr result_type ci
	# case_guards
		=	BasicPatterns BT_Bool
				[{bp_value = BVB True, bp_expr = dp_rhs, bp_position = dp_position}]
	# (case_default, ci)
		=	convertDynamicAlts cinp
				kees type_var value_var result_type defoult alts ci

	# kees
		=	{kees & case_info_ptr=case_info_ptr, case_guards=case_guards,
						case_default=case_default, case_explicit=False, case_expr=Var unify_bool_var}

	# ci
		=	{ci & ci_new_variables	= [unify_result_fv, unify_bool_fv, unify_subst_fv : ci.ci_new_variables ]}

	  (twotuple, ci)
	  	=	getTupleSymbol 2 ci

	  letje
		=	{	let_strict_binds = [{ lb_src =  unify_call,
		  							   lb_dst = unify_result_fv, lb_position = NoPos },
		  							{ lb_src =  TupleSelect twotuple 0 (Var unify_result_var),
		  							   lb_dst = unify_bool_fv, lb_position = NoPos }]
		  	,	let_lazy_binds = [ // { lb_src = Var value_var, lb_dst = dp_var, lb_position = NoPos },
		  	{ lb_src = TupleSelect twotuple 1 (Var unify_result_var),
		  							   lb_dst = unify_subst_fv, lb_position = NoPos }] ++ binds
			,	let_info_ptr = let_info_ptr
			,	let_expr = Case kees
			,	let_expr_position = NoPos // FIXME, add correct position
			} 

	=	(Yes (Let letje), ci)


class position a :: a -> Position

instance position [a] | position a where
	position []
		=	NoPos
	position [h:_]
		=	position h

instance position DynamicPattern where
	position {dp_position}
		=	dp_position

instance convertDynamics BasicPattern where
	convertDynamics cinp alt=:{bp_expr} ci
		# (bp_expr, ci)
			=	convertDynamics cinp bp_expr ci
		= ({alt & bp_expr=bp_expr}, ci)

instance convertDynamics AlgebraicPattern where
	convertDynamics cinp alt=:{ap_expr} ci
		# (ap_expr, ci)
			=	convertDynamics cinp ap_expr ci
		=	({alt & ap_expr=ap_expr}, ci)

instance convertDynamics Selection where
	convertDynamics cinp selection=:(RecordSelection _ _) ci
		=	(selection, ci)
	convertDynamics cinp (ArraySelection selector expr_ptr expr) ci
		# (expr, ci)
			=	convertDynamics cinp expr ci
		=	(ArraySelection selector expr_ptr expr, ci)
	convertDynamics cinp (DictionarySelection var selectors expr_ptr expr) ci
		# (expr, ci)
			=	convertDynamics cinp expr ci
		=	(DictionarySelection var selectors expr_ptr expr, ci)

convertExprTypeCode
	::	!ConversionInput !TypeCodeExpression !*ConversionState
	->	(!Expression, !*ConversionState)
convertExprTypeCode cinp tce ci
	# (expr, binds, ci)
		=	convertTypeCode cinp tce [] ci
	// sanity check ...
	| not (isEmpty binds)
		=	abort "unexpected binds in expression type code"
	// ... sanity check	
	=	(expr, ci)

convertPatternTypeCode :: !ConversionInput !TypeCodeExpression !*ConversionState
										-> (!Expression, ![LetBind], !*ConversionState)
convertPatternTypeCode cinp tce ci
	=	convertTypeCode cinp tce [] ci

convertTypeCode :: !ConversionInput !TypeCodeExpression ![LetBind] !*ConversionState
										-> (!Expression, ![LetBind], !*ConversionState)
convertTypeCode _ (TCE_Var var_info_ptr) binds ci=:{ci_var_heap}
	# (var_info, ci_var_heap)
		=	readPtr var_info_ptr ci_var_heap
	  ci
	  	=	{ci & ci_var_heap = ci_var_heap}
	=	case var_info of
			// sanity check ...
			VI_TypeCodeVariable TCI_TypeTerm
				->	abort "unexpected type term"
			// ... sanity check
			VI_TypeCodeVariable (TCI_TypeVar expr)
				->	(expr, binds, ci) 
			_
				# (expr, ci)
					=	createTypePatternVariable ci
				# ci
					=	{ci & ci_var_heap
						=	writePtr var_info_ptr (VI_TypeCodeVariable (TCI_TypeVar expr)) ci.ci_var_heap}
				->	(expr, binds, ci)
convertTypeCode _ (TCE_TypeTerm var_info_ptr) binds ci=:{ci_var_heap}
	// sanity check ...
	# (var_info, ci_var_heap)
		=	readPtr var_info_ptr ci_var_heap
	  ci
	  	=	{ci & ci_var_heap = ci_var_heap}
//	# ci
	=	case var_info of
				VI_TypeCodeVariable TCI_TypeTerm
					# (expr, ci)
						=	createTypePatternVariable ci
					# ci
						=	{ci & ci_var_heap
							=	writePtr var_info_ptr (VI_TypeCodeVariable (TCI_TypeVar expr)) ci.ci_var_heap}
					->	(expr, binds, ci)
				VI_TypeCodeVariable (TCI_TypeVar expr)
					->	(expr, binds, ci)
				info
					->	abort "type term expected instead of unknown"
/*
	// ... sanity check
	# var
		// FIXME, share vars & proper name
		=	{var_name = a_ij_var_name, var_info_ptr = var_info_ptr,
															var_expr_ptr = nilPtr}
	=	(Var var, binds, ci)
*/
convertTypeCode cinp (TCE_Constructor index typecode_exprs) binds ci
	# (typeapp_symb, ci)
		=	getSymbol PD_Dyn_TypeApp SK_Constructor 2 ci
	# (constructor, ci)
		=	get_constructor cinp.cinp_glob_type_inst index ci
	  (module_id, ci)
		=	get_module_id ci
	  (typecode_exprs, binds, ci)
	  	=	convertTypeCodes cinp typecode_exprs binds ci
	= (App {app_symb		= typeapp_symb,
			app_args 		= [constructor, module_id, typecode_exprs],
			app_info_ptr	= nilPtr}, binds, ci)
where
	get_module_id ci=:{ci_module_id_var=Yes {lb_dst}}
		=	(Var (freeVarToVar lb_dst),ci)
		
	get_constructor :: !{!GlobalTCType} Index !*ConversionState -> (Expression,!*ConversionState)
	get_constructor glob_type_inst index ci=:{ci_type_constructor_used_in_dynamic_patterns}
		# cons_string
			=	BasicExpr (BVS ("\"" +++ toString  glob_type_inst.[index] +++ "\""))
		=	(cons_string, ci)

	convertTypeCodes _ [] binds ci
		# (nil_symb, ci) = getSymbol PD_NilSymbol SK_Constructor 0 ci
		= (App {	app_symb		= nil_symb,
					app_args 		= [],
					app_info_ptr	= nilPtr},binds, ci)
	
	convertTypeCodes cinp [typecode_expr : typecode_exprs] binds ci
		# (cons_symb, ci)
			=	getSymbol PD_ConsSymbol SK_Constructor 2 ci
		# (expr, binds, ci)
			=	convertTypeCode cinp typecode_expr  binds ci
		# (exprs, binds, ci)
			=	convertTypeCodes cinp typecode_exprs binds ci
		= (App {	app_symb		= cons_symb,
					app_args 		= [expr , exprs],
					app_info_ptr	= nilPtr}, binds, ci)
convertTypeCode cinp (TCE_UniType uni_vars type_code) binds ci
		# (type_scheme_sym, ci)
			=	getSymbol PD_Dyn_TypeScheme SK_Constructor 2 ci
		# (tv_symb, ci)
			=	getSymbol PD_Dyn_TypeVar SK_Constructor 1 ci
		// assign unique numbers for all type variables in the module (for testing)
		# init_count = ci.ci_type_pattern_var_count
		# (count, ci_var_heap)
			=	foldSt (mark_uni_var (build_tv tv_symb)) uni_vars (init_count, ci.ci_var_heap)
		# ci
			=	{ci & ci_type_pattern_var_count = count, ci_var_heap = ci_var_heap}
//		  (type_code_expr, binds, ci)
	  	=	convertTypeCode cinp type_code binds ci
/*		=	(App {	app_symb = type_scheme_sym,
					app_args = [BasicExpr (BVInt (count - init_count)), type_code_expr],
					app_info_ptr = nilPtr }, binds, ci)
*/		where
			mark_uni_var :: (Int -> Expression) VarInfoPtr (Int, *VarHeap) -> (Int, *VarHeap)
			mark_uni_var build_var_code var_info_ptr (count, var_heap)
				# var_info
					=	VI_TypeCodeVariable (TCI_TypeVar (build_var_code count))
				=	(count+1, writePtr var_info_ptr var_info var_heap)

			build_tv :: SymbIdent Int -> Expression
			build_tv tv_symb number
				=	App {	app_symb = tv_symb,
							app_args = [BasicExpr (BVInt number)],
							app_info_ptr = nilPtr }

convertTypeCode cinp (TCE_Selector selections var_info_ptr) binds ci
	# (var, binds, ci)		
		=	convertTypeCode cinp (TCE_Var var_info_ptr) binds ci
	=	(Selection NormalSelector var selections, binds, ci)

createTypePatternVariable :: !*ConversionState -> (!Expression, !*ConversionState)
createTypePatternVariable ci
	# (tpv_symb, ci)
		=	getSymbol PD_Dyn_TypePatternVar SK_Constructor 1 ci
	=	(App {	app_symb = tpv_symb,
						app_args = [BasicExpr (BVInt ci.ci_type_pattern_var_count)],
						app_info_ptr = nilPtr },
		{ci & ci_type_pattern_var_count = ci.ci_type_pattern_var_count + 1})

/**************************************************************************************************/

newVariable :: String !VarInfo !*ConversionState -> *(!BoundVar,!*ConversionState)
newVariable var_name var_info ci=:{ci_var_heap}
	# (var_info_ptr, ci_var_heap) = newPtr var_info ci_var_heap
	= ( { var_name = {id_name = var_name, id_info = nilPtr},  var_info_ptr = var_info_ptr, var_expr_ptr = nilPtr},
	    { ci & ci_var_heap = ci_var_heap })	

varToFreeVar :: BoundVar Int -> FreeVar
varToFreeVar {var_name, var_info_ptr} count
	= {fv_def_level = NotALevel, fv_name = var_name, fv_info_ptr = var_info_ptr, fv_count = count}

freeVarToVar ::  FreeVar -> BoundVar
freeVarToVar {fv_name, fv_info_ptr}
	= { var_name = fv_name,  var_info_ptr = fv_info_ptr, var_expr_ptr = nilPtr}


getResultType :: ExprInfoPtr !*ConversionState -> (!AType, !*ConversionState)
getResultType case_info_ptr ci=:{ci_expr_heap}
	# (EI_CaseType {ct_result_type}, ci_expr_heap) = readPtr case_info_ptr ci_expr_heap
	= (ct_result_type, {ci & ci_expr_heap = ci_expr_heap})

getSymbol :: Index ((Global Index) -> SymbKind) Int !*ConversionState -> (SymbIdent, !*ConversionState)
getSymbol index symb_kind arity ci=:{ci_predef_symb}
	# ({pds_module, pds_def}, ci_predef_symb) = ci_predef_symb![index]
	# pds_ident = predefined_idents.[index]
	  ci = {ci & ci_predef_symb = ci_predef_symb}
	  symbol = { symb_name = pds_ident, symb_kind = symb_kind { glob_module = pds_module, glob_object = pds_def} }
	= (symbol, ci)

getTupleSymbol arity ci=:{ci_predef_symb}
	# ({pds_def}, ci_predef_symb) = ci_predef_symb![GetTupleConsIndex arity]
	# pds_ident = predefined_idents.[GetTupleConsIndex arity]
    = ( {ds_ident = pds_ident, ds_arity = arity, ds_index = pds_def}, {ci & ci_predef_symb = ci_predef_symb })

a_ij_var_name :== { id_name = "a_ij", id_info = nilPtr }

bool_case_ptr :: !AType !*ConversionState -> (ExprInfoPtr, !*ConversionState)
bool_case_ptr result_type ci=:{ci_expr_heap}
	# (expr_info_ptr, ci_expr_heap) = newPtr (EI_CaseType {	ct_pattern_type = toAType (TB BT_Bool),
															ct_result_type = result_type, //empty_attributed_type,
															ct_cons_types = [[toAType (TB BT_Bool)]]}) ci_expr_heap
	= (expr_info_ptr, {ci &  ci_expr_heap = ci_expr_heap})

dummy_case_ptr :: !AType !*ConversionState -> (ExprInfoPtr, !*ConversionState)
dummy_case_ptr result_type ci=:{ci_expr_heap}
	# (expr_info_ptr, ci_expr_heap) = newPtr (EI_CaseType {	ct_pattern_type = toAType (TB BT_Bool),
															ct_result_type = result_type, //empty_attributed_type,
															ct_cons_types = [[empty_attributed_type, empty_attributed_type]]}) ci_expr_heap
	= (expr_info_ptr, {ci &  ci_expr_heap = ci_expr_heap})


let_ptr :: !Int !*ConversionState -> (ExprInfoPtr, !*ConversionState)
let_ptr nr_of_binds ci=:{ci_expr_heap}
	= let_ptr2 (repeatn nr_of_binds empty_attributed_type) ci

typed_let_ptr :: TypeSymbIdent !*ConversionState -> (ExprInfoPtr, !*ConversionState)
typed_let_ptr type_id ci=:{ci_expr_heap}
	= let_ptr2 [toAType (TA type_id [])] ci

let_ptr2 :: [AType] !*ConversionState -> (ExprInfoPtr, !*ConversionState)
let_ptr2 let_types ci=:{ci_expr_heap}
	# (expr_info_ptr, ci_expr_heap) = newPtr (EI_LetType let_types) ci_expr_heap
	= (expr_info_ptr, {ci &  ci_expr_heap = ci_expr_heap})

toAType :: Type -> AType
toAType type = { at_attribute = TA_Multi, at_type = type }

empty_attributed_type :: AType
empty_attributed_type = toAType TE

instance <<< (Ptr a)
where
	(<<<) file ptr = file <<< ptrToInt ptr  


create_dynamic_and_selector_idents common_defs predefined_symbols 
	| predefined_symbols.[PD_StdDynamic].pds_module == NoIndex
		=	({	dr_type_ident		= undef
			,	dr_dynamic_type		= undef
			,	dr_dynamic_symbol	= undef
			},predefined_symbols)
	// otherwise	
		# ({pds_module=pds_module1, pds_def=pds_def1} , predefined_symbols) = predefined_symbols![PD_Dyn_DynamicTemp]
		# {td_rhs=RecordType {rt_constructor,rt_fields}} = common_defs.[pds_module1].com_type_defs.[pds_def1]
	
		# dynamic_defined_symbol
			= {glob_module = pds_module1, glob_object = rt_constructor}
		# dynamic_type = {glob_module = pds_module1, glob_object = pds_def1}

		# dynamic_temp_symb_ident
			= { SymbIdent |
				symb_name	= rt_constructor.ds_ident
			,	symb_kind 	= SK_Constructor {glob_module = pds_module1, glob_object = rt_constructor.ds_index} 
			}
		= ({	dr_type_ident		= dynamic_temp_symb_ident
			,	dr_dynamic_type		= dynamic_type
			,	dr_dynamic_symbol	= dynamic_defined_symbol
			}, predefined_symbols)

get_module_id_app :: !*PredefinedSymbols -> (App,Expression,!*PredefinedSymbols)
get_module_id_app predef_symbols
	// get module id symbol
	# ({pds_module, pds_def}, predef_symbols)	= predef_symbols![PD_ModuleConsSymbol]
	# pds_ident = predefined_idents.[PD_ModuleConsSymbol]
	# module_symb = 
		{	app_symb 		= { symb_name = pds_ident, symb_kind = SK_Constructor { glob_module = pds_module, glob_object = pds_def} }
		,	app_args 		= []
		,	app_info_ptr	= nilPtr
		}

	# ({pds_module, pds_def}, predef_symbols)	= predef_symbols![PD_Dyn_ModuleID]
	# pds_ident = predefined_idents.[PD_Dyn_ModuleID]
	# module_id_symb = 
		{	app_symb 		= { symb_name = pds_ident, symb_kind = SK_Constructor { glob_module = pds_module, glob_object = pds_def} }
		,	app_args 		= [App module_symb]
		,	app_info_ptr	= nilPtr
		}

	= (module_symb,App module_id_symb,predef_symbols)
