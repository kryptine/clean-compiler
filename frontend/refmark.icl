implementation module refmark

import StdEnv
import syntax, Heap, typesupport, check, overloading, unitype, utilities //, RWSDebug


NotASelector :== -1

class refMark expr ::  ![[FreeVar]] !Int !(Optional [CountedFreeVar]) !expr !*VarHeap -> *VarHeap

instance refMark [a] | refMark a
where
	refMark free_vars sel _ list var_heap
		= foldSt (refMark free_vars sel No) list var_heap

collectAllSelections [] cum_sels
	= cum_sels
collectAllSelections [{su_multiply,su_uniquely} : sels ] cum_sels
	= collectAllSelections sels (su_uniquely ++ su_multiply ++ cum_sels)

addSelection var_expr_ptr sel []
	= [ { su_field = sel, su_multiply = [], su_uniquely = [var_expr_ptr]  } ]
addSelection var_expr_ptr sel sels=:[selection=:{ su_field,su_multiply,su_uniquely } : selections]
	| sel == su_field
		= [ { selection & su_multiply = su_multiply ++ [var_expr_ptr : su_uniquely], su_uniquely = [] } : selections ]
	| sel < su_field
		= [ { su_field = sel, su_multiply = [], su_uniquely = [var_expr_ptr]  } : sels ]
		= [ selection : addSelection var_expr_ptr sel selections ]

/*
saveOccurrencesWhenNeeded pattern_nr free_vars var_heap
	| pattern_nr == 0
		= var_heap
		= saveOccurrences free_vars var_heap
*/
		
saveOccurrences free_vars var_heap
	= foldSt (foldSt save_occurrence)  free_vars var_heap // (free_vars ---> ("saveOccurrences", free_vars)) var_heap
where
	save_occurrence {fv_name,fv_info_ptr} var_heap
		# (VI_Occurrence old_occ=:{occ_ref_count,occ_previous}, var_heap) = readPtr fv_info_ptr var_heap
		= var_heap <:= (fv_info_ptr, VI_Occurrence {old_occ & occ_ref_count = RC_Unused, occ_previous = [occ_ref_count : occ_previous] } )
// 			---> ("save_occurrence", fv_name, occ_ref_count, length occ_previous)
restoreOccurrences free_vars var_heap
	= foldSt (foldSt restore_occurrence) (free_vars /* ---> ("restoreOccurrences", free_vars) */) ([], var_heap)
where
	restore_occurrence fv=:{fv_name,fv_info_ptr} (occurrences, var_heap)
		# (VI_Occurrence old_occ=:{occ_ref_count,occ_previous = [prev_ref_count : occ_previous]}, var_heap) = readPtr fv_info_ptr var_heap
		  var_heap = var_heap <:= (fv_info_ptr, VI_Occurrence {old_occ & occ_ref_count = prev_ref_count, occ_previous = occ_previous })
		= case occ_ref_count of // ---> ("restore_occurrence", fv_name, prev_ref_count, occ_previous) of
			RC_Unused
				-> (occurrences, var_heap)
			_
				-> ([{cfv_var = fv,cfv_count = occ_ref_count} : occurrences ], var_heap)

adjustRefCount sel RC_Unused var_expr_ptr
	| sel == NotASelector
		= RC_Used {rcu_multiply = [], rcu_selectively = [], rcu_uniquely = [var_expr_ptr] }
		# sel_ref = { su_field = sel, su_multiply = [], su_uniquely = [var_expr_ptr] }
		= RC_Used {rcu_multiply = [], rcu_selectively = [{ su_field = sel, su_multiply = [], su_uniquely = [var_expr_ptr] }], rcu_uniquely = [] }
adjustRefCount sel (RC_Used {rcu_multiply,rcu_uniquely,rcu_selectively}) var_expr_ptr
	| sel == NotASelector
		# rcu_multiply = collectAllSelections rcu_selectively (rcu_uniquely ++ [var_expr_ptr : rcu_multiply])
		= RC_Used {rcu_multiply = rcu_multiply, rcu_uniquely = [], rcu_selectively = [] }
		# rcu_selectively = addSelection var_expr_ptr sel rcu_selectively
		  rcu_multiply = rcu_uniquely ++ rcu_multiply
		= RC_Used {rcu_multiply = rcu_multiply, rcu_uniquely = [], rcu_selectively = rcu_selectively }

markPatternVariables sel list_of_used_pattern_vars var_heap
	= foldSt (mark_pattern_variables sel) list_of_used_pattern_vars var_heap
where
	mark_pattern_variables sel used_pattern_vars var_heap
		| sel == NotASelector
			= foldSt mark_variable used_pattern_vars var_heap
			= mark_selected_variable sel used_pattern_vars var_heap

	mark_selected_variable sel [] var_heap
		= var_heap
	mark_selected_variable sel [pv=:{pv_var, pv_arg_nr} : pvs ] var_heap
		| sel == pv_arg_nr
			= mark_variable pv var_heap
			= mark_selected_variable sel pvs var_heap
		
	mark_variable {pv_var={fv_info_ptr}} var_heap
		# (VI_Occurrence old_occ=:{occ_ref_count}, var_heap) = readPtr fv_info_ptr var_heap
		= case occ_ref_count of
			RC_Unused
				# occ_ref_count = RC_Used {rcu_multiply = [], rcu_selectively = [], rcu_uniquely = [nilPtr] }
				-> var_heap <:= (fv_info_ptr, VI_Occurrence {old_occ & occ_ref_count = occ_ref_count } )
			RC_Used {rcu_multiply,rcu_uniquely,rcu_selectively}
				# occ_ref_count = RC_Used { rcu_multiply = collectAllSelections rcu_selectively (rcu_uniquely ++ rcu_multiply),
							 rcu_selectively = [], rcu_uniquely = [] }
				-> var_heap <:= (fv_info_ptr, VI_Occurrence {old_occ & occ_ref_count = occ_ref_count } )

closeAndMarkBinding free_vars var_info_ptr occ_ref_count var_occ let_expr=:(Either expr) var_heap
	# var_heap = var_heap <:= (var_info_ptr, VI_Occurrence { var_occ & occ_ref_count = occ_ref_count, occ_bind = OB_LockedLet let_expr })
	= refMark free_vars NotASelector No expr var_heap
closeAndMarkBinding free_vars var_info_ptr occ_ref_count var_occ let_expr=:(Or ref_counts) var_heap
	# var_heap = var_heap <:= (var_info_ptr, VI_Occurrence { var_occ & occ_ref_count = occ_ref_count, occ_bind = OB_LockedLet let_expr })
	= addRefCounts ref_counts var_heap

refMarkOfVariable free_vars sel (VI_Occurrence var_occ) var_name var_info_ptr var_expr_ptr var_heap
	# occ_ref_count = adjustRefCount sel var_occ.occ_ref_count var_expr_ptr
	  var_heap		= markPatternVariables sel var_occ.occ_pattern_vars var_heap
	= ref_count_of_bindings free_vars var_info_ptr occ_ref_count var_occ var_heap
where
	ref_count_of_bindings free_vars var_info_ptr occ_ref_count var_occ=:{occ_bind = OB_OpenLet let_expr} var_heap
		= closeAndMarkBinding free_vars var_info_ptr occ_ref_count var_occ let_expr var_heap
	ref_count_of_bindings free_vars var_info_ptr occ_ref_count var_occ var_heap
		= var_heap <:= (var_info_ptr, VI_Occurrence { var_occ & occ_ref_count = occ_ref_count })	
		
addRefCounts ref_counts var_heap
	= foldSt set_occurrence ref_counts var_heap
where
	set_occurrence {cfv_var = {fv_name,fv_info_ptr}, cfv_count} var_heap
		# (VI_Occurrence occ=:{occ_ref_count}, var_heap) = readPtr fv_info_ptr var_heap
		  comb_ref_count = parCombineRefCount occ_ref_count cfv_count
		= var_heap <:= (fv_info_ptr, VI_Occurrence { occ & occ_ref_count = comb_ref_count})

instance refMark BoundVar
where
	refMark free_vars sel _ {var_name,var_expr_ptr,var_info_ptr} var_heap
		# (var_occ, var_heap) = readPtr var_info_ptr var_heap
		= refMarkOfVariable free_vars sel var_occ var_name var_info_ptr var_expr_ptr var_heap

combineDefaults outer_default No explicit
	| explicit
		= No
		= outer_default
combineDefaults outer_default this_default explicit
	= this_default
			
instance refMark Expression
where
	refMark free_vars sel _ (Var var) var_heap
		= refMark free_vars sel No var var_heap
	refMark free_vars sel _ (App {app_args}) var_heap
		= refMark free_vars NotASelector No app_args var_heap
	refMark free_vars sel _ (fun @ args) var_heap
		= refMark free_vars NotASelector No args (refMark free_vars NotASelector No fun var_heap)
	refMark free_vars sel def (Let {let_strict_binds,let_lazy_binds,let_expr}) var_heap
		| isEmpty let_lazy_binds
			# new_free_vars = [ [ lb_dst \\ {lb_dst} <- let_strict_binds ] : free_vars]
			# (observing, var_heap) = binds_are_observing let_strict_binds var_heap
			| observing
				# var_heap = saveOccurrences free_vars var_heap
				  var_heap = refMark new_free_vars NotASelector No let_strict_binds var_heap
				  var_heap = saveOccurrences new_free_vars var_heap
				  var_heap = refMark new_free_vars sel def let_expr var_heap
				= let_combine free_vars var_heap
				= refMark new_free_vars sel def let_expr (refMark new_free_vars NotASelector No let_strict_binds var_heap)
			# all_binds						= let_strict_binds ++ let_lazy_binds
			  local_let_vars				= [ lb_dst \\ {lb_dst} <- all_binds ]
			  new_free_vars					= [ local_let_vars : free_vars]
//			  (global_let_vars, var_heap)	= collectOpenLetVars free_vars var_heap
			  var_heap						= init_let_binds all_binds var_heap
//			  (let_occurrences, var_heap)	= ref_mark_of_lets new_free_vars local_let_vars global_let_vars all_binds var_heap
//			  var_heap						= finish_let_binds let_occurrences var_heap
			= refMark new_free_vars sel def let_expr var_heap

		where
		    binds_are_observing binds var_heap
		    	= foldr bind_is_observing (True, var_heap) binds
			where
				bind_is_observing {lb_dst={fv_info_ptr}} (observe, var_heap) 
					# (VI_Occurrence {occ_observing}, var_heap) = readPtr fv_info_ptr var_heap
					= (occ_observing && observe, var_heap)
			
			let_combine free_vars var_heap
				= foldSt (foldSt let_combine_ref_count) free_vars var_heap
			where
				let_combine_ref_count {fv_info_ptr} var_heap
					# (VI_Occurrence old_occ=:{occ_ref_count,occ_previous=[prev_ref_count, pre_pref_recount:occ_previouses]}, var_heap)
							= readPtr fv_info_ptr var_heap
					  comb_ref_count = parCombineRefCount (seqCombineRefCount occ_ref_count prev_ref_count) pre_pref_recount
					= var_heap <:= (fv_info_ptr, VI_Occurrence { old_occ & occ_ref_count = comb_ref_count, occ_previous = occ_previouses })

			init_let_binds let_binds var_heap
				= foldSt bind_variable let_binds var_heap
			where
				bind_variable {lb_src,lb_dst={fv_info_ptr}} var_heap
					# (VI_Occurrence occ, var_heap) = readPtr fv_info_ptr var_heap
					= var_heap <:= (fv_info_ptr, VI_Occurrence { occ & occ_ref_count = RC_Unused, occ_bind = OB_OpenLet (Either lb_src) })

			finish_let_binds let_binds var_heap
				= foldSt finish_let_bind let_binds var_heap
			where				
				finish_let_bind (let_var_ptr, occurrences) var_heap
					# (VI_Occurrence occ, var_heap) = readPtr let_var_ptr var_heap
					= var_heap <:= (let_var_ptr, VI_Occurrence { occ & occ_bind = OB_OpenLet (Or occurrences) })

			ref_mark_of_lets free_vars local_let_vars global_let_vars let_binds var_heap
				= foldSt (ref_mark_of_let free_vars local_let_vars global_let_vars) let_binds ([], var_heap)

			ref_mark_of_let free_vars local_let_vars global_let_vars {lb_src,lb_dst={fv_info_ptr}} (all_occurrences, var_heap)
				# (VI_Occurrence occ, var_heap) = readPtr fv_info_ptr var_heap
				  var_heap = var_heap <:= (fv_info_ptr, VI_Occurrence { occ & occ_bind = OB_LockedLet (Either lb_src) })
				  var_heap = saveOccurrences free_vars var_heap
				  var_heap = refMark free_vars NotASelector No lb_src var_heap
				  var_heap = open_locked_lets local_let_vars var_heap
				  (_, var_heap) = collectUsedLetVars global_let_vars ([], var_heap)
				  (occurrences, var_heap) = restoreOccurrences free_vars var_heap
				= ([(fv_info_ptr, occurrences) : all_occurrences], var_heap)
			where
				open_locked_lets let_vars var_heap
					= foldSt open_locked_let let_vars var_heap
				where
					open_locked_let fv=:{fv_name,fv_info_ptr} var_heap
						# (VI_Occurrence var_occ, var_heap) = readPtr fv_info_ptr var_heap
						= case var_occ.occ_bind of
							OB_LockedLet expr
								-> 	var_heap <:= (fv_info_ptr, VI_Occurrence { var_occ & occ_bind = OB_OpenLet expr })
							_
								-> var_heap
	
	refMark free_vars sel def (Case kees) var_heap
		= refMarkOfCase free_vars sel def kees var_heap
	refMark free_vars sel _ (Selection _ expr selectors) var_heap
		= refMark free_vars (field_number selectors) No expr var_heap
	where
		field_number [ RecordSelection _ field_nr : _ ]
			= field_nr	
		field_number _
			= NotASelector	
	refMark free_vars sel _ (Update expr1 selectors expr2) var_heap
		# var_heap = refMark free_vars NotASelector No expr1 var_heap
		  var_heap = refMark free_vars NotASelector No selectors var_heap
		= refMark free_vars NotASelector No expr2 var_heap
	refMark free_vars sel _ (RecordUpdate cons_symbol expression expressions) var_heap
		= ref_mark_of_record_expression free_vars expression expressions var_heap
	where
		ref_mark_of_record_expression free_vars (Var var) fields var_heap
			= ref_mark_of_fields 0 free_vars fields var var_heap
		ref_mark_of_record_expression free_vars expression fields var_heap
			# var_heap = refMark free_vars NotASelector No expression var_heap
			= foldSt (ref_mark_of_field free_vars) fields var_heap
	
		ref_mark_of_fields field_nr free_vars [] var var_heap
			= var_heap
		ref_mark_of_fields field_nr free_vars [{bind_src = NoBind expr_ptr} : fields] var=:{var_name,var_info_ptr} var_heap
			# (var_occ, var_heap) = readPtr var_info_ptr var_heap
			  var_heap = refMarkOfVariable free_vars field_nr var_occ var_name var_info_ptr expr_ptr var_heap
			= ref_mark_of_fields (inc field_nr) free_vars fields var var_heap
		ref_mark_of_fields field_nr free_vars [{bind_src} : fields] var var_heap
			# var_heap = refMark free_vars NotASelector No bind_src var_heap
			= ref_mark_of_fields (inc field_nr) free_vars fields var var_heap

		ref_mark_of_field free_vars {bind_src} var_heap
			= refMark free_vars NotASelector No bind_src var_heap

	refMark free_vars sel _ (TupleSelect _ arg_nr expr) var_heap
		= refMark free_vars arg_nr No expr var_heap
	refMark free_vars sel _ (MatchExpr _ expr) var_heap
		= refMark free_vars sel No expr var_heap
	refMark free_vars sel _ EE var_heap
		= var_heap
	refMark _ _ _ _ var_heap
		= var_heap


isUsed RC_Unused	= False				
isUsed _			= True				

instance refMark LetBind
where
	refMark free_vars sel _ {lb_src} var_heap
		= refMark free_vars NotASelector No lb_src var_heap


instance refMark Selection
where
	refMark free_vars _ _ (ArraySelection _ _ index_expr) var_heap
		= refMark free_vars NotASelector No index_expr var_heap
	refMark free_vars _ _ _ var_heap
		= var_heap

collectUsedFreeVariables free_vars var_heap
	= foldSt collectUsedVariables free_vars ([], var_heap)

collectUsedVariables free_vars (collected_vars, var_heap)
	= foldSt collect_used_var free_vars (collected_vars, var_heap)
where
	collect_used_var fv=:{fv_info_ptr} (collected_vars, var_heap)
		# (VI_Occurrence occ=:{occ_ref_count}, var_heap) = readPtr fv_info_ptr var_heap
		| isUsed occ_ref_count
			= ([ fv : collected_vars ], var_heap)
			= (collected_vars, var_heap)

collectPatternsVariables pattern_vars
	= collect_used_vars pattern_vars 0 []
where
	collect_used_vars [ fv=:{fv_count} : pattern_vars ] arg_nr collected_vars
		| fv_count > 0
			= collect_used_vars pattern_vars (inc arg_nr) [ {pv_var = fv, pv_arg_nr = arg_nr} : collected_vars ]
			= collect_used_vars pattern_vars (inc arg_nr) collected_vars
	collect_used_vars [] arg_nr collected_vars
		= collected_vars

collectOpenLetVars free_vars var_heap
	= foldSt (foldSt collect_open_let_var) free_vars ([], var_heap)
where
	collect_open_let_var fv=:{fv_info_ptr} (collected_vars, var_heap)
		# (VI_Occurrence var_occ, var_heap) = readPtr fv_info_ptr var_heap
		= case var_occ.occ_bind of
			OB_OpenLet _
				-> ([ fv_info_ptr : collected_vars], var_heap)
			_
				-> (collected_vars, var_heap)
		
collectUsedLetVars local_vars (used_vars, var_heap)
	= foldSt collect_local_let_var local_vars (used_vars, var_heap)
where
	collect_local_let_var fv_info_ptr (used_vars, var_heap)
		# (VI_Occurrence var_occ, var_heap) = readPtr fv_info_ptr var_heap
		= case var_occ.occ_bind of
			OB_LockedLet ref_counts
				-> ([ fv_info_ptr : used_vars], var_heap <:= (fv_info_ptr, VI_Occurrence { var_occ & occ_bind = OB_OpenLet ref_counts }))
			_
				-> (used_vars, var_heap)

setUsedLetVars used_vars var_heap
	= foldSt set_used_let_var used_vars var_heap
where
	set_used_let_var fv_info_ptr var_heap
		# (VI_Occurrence var_occ, var_heap) = readPtr fv_info_ptr var_heap
		= case var_occ.occ_bind of
			OB_OpenLet ref_counts
				-> var_heap <:= (fv_info_ptr, VI_Occurrence { var_occ & occ_bind = OB_LockedLet ref_counts })
			_
				-> var_heap

refMarkOfCase free_vars sel def {case_expr, case_guards=AlgebraicPatterns type patterns, case_explicit, case_default} var_heap
	= refMarkOfAlgebraicOrOverloadedListCase free_vars sel def case_expr patterns case_explicit case_default var_heap

refMarkOfCase free_vars sel def {case_expr,case_guards=BasicPatterns type patterns,case_default,case_explicit} var_heap
	# (local_lets, var_heap) = collectOpenLetVars free_vars var_heap
	  (def, used_lets, var_heap) = refMarkOfDefault case_explicit free_vars sel def case_default local_lets var_heap
	  (pattern_depth, used_lets, var_heap) = foldSt (ref_mark_of_basic_pattern free_vars sel local_lets def) patterns (0, used_lets, var_heap)
	  var_heap = addRefMarkOfDefault  pattern_depth free_vars def used_lets var_heap
	  var_heap = saveOccurrences free_vars var_heap
	  var_heap = refMark free_vars NotASelector No case_expr var_heap
	= caseCombine False free_vars var_heap	  
where
	ref_mark_of_basic_pattern free_vars sel local_lets def {bp_expr} (pattern_depth, used_lets, var_heap)
//		# var_heap = saveOccurrencesWhenNeeded pattern_depth free_vars var_heap
		# var_heap = saveOccurrences free_vars var_heap
		  var_heap = refMark free_vars sel def bp_expr var_heap
		  (used_lets, var_heap) = collectUsedLetVars local_lets (used_lets, var_heap)
		= (inc pattern_depth, used_lets, var_heap)

refMarkOfCase free_vars sel def {case_expr, case_guards=OverloadedListPatterns type _ patterns, case_explicit, case_default} var_heap
	= refMarkOfAlgebraicOrOverloadedListCase free_vars sel def case_expr patterns case_explicit case_default var_heap

refMarkOfCase free_vars sel def {case_expr,case_guards=DynamicPatterns patterns,case_default,case_explicit} var_heap
//	 (used_free_vars, var_heap) = collectUsedFreeVariables free_vars var_heap
//	  var_heap = parCombine free_vars var_heap
	# (local_lets, var_heap) = collectOpenLetVars free_vars var_heap
	  (def, used_lets, var_heap) = refMarkOfDefault case_explicit free_vars sel def case_default local_lets var_heap
	  (pattern_depth, used_lets, var_heap) = foldSt (ref_mark_of_dynamic_pattern free_vars sel local_lets def) patterns (0, used_lets, var_heap)
	  var_heap = addRefMarkOfDefault pattern_depth free_vars def used_lets var_heap
	  var_heap = saveOccurrences free_vars var_heap
	  var_heap = refMark free_vars NotASelector No case_expr var_heap
	= caseCombine True free_vars var_heap	  
where
	ref_mark_of_dynamic_pattern free_vars sel local_lets def {dp_var, dp_rhs} (pattern_depth, used_lets, var_heap)
//		# var_heap = saveOccurrencesWhenNeeded pattern_depth free_vars var_heap
		# var_heap = saveOccurrences free_vars var_heap
		  used_pattern_vars = collectPatternsVariables [dp_var]
		  var_heap = refMark [ [ pv_var \\ {pv_var} <- used_pattern_vars ] : free_vars ] sel def dp_rhs var_heap
		  (used_lets, var_heap) = collectUsedLetVars local_lets (used_lets, var_heap)
		= (inc pattern_depth, used_lets, var_heap)

refMarkOfAlgebraicOrOverloadedListCase free_vars sel def case_expr alternatives case_explicit case_default var_heap
	# (with_pattern_bindings, var_heap) = ref_mark_of_alternatives free_vars sel def (is_variable_pattern case_expr) alternatives case_explicit case_default var_heap
	= ref_mark_of_pattern free_vars with_pattern_bindings case_expr var_heap
where
	is_variable_pattern (Var {var_info_ptr})	= Yes var_info_ptr
	is_variable_pattern _						= No

	ref_mark_of_pattern free_vars with_pattern_bindings (Var {var_name,var_info_ptr,var_expr_ptr}) var_heap
		# (VI_Occurrence var_occ_in_alts, var_heap) = readPtr var_info_ptr var_heap
		  var_heap	= adjust_ref_count_of_variable_pattern var_occ_in_alts var_info_ptr var_expr_ptr var_heap
		  var_heap	= saveOccurrences free_vars var_heap 
		  var_heap	= ref_mark_of_variable_pattern free_vars var_info_ptr var_occ_in_alts var_heap
//		  var_heap	= markPatternVariables NotASelector var_occ_in_alts.occ_pattern_vars var_heap
		  var_heap	= caseCombine with_pattern_bindings free_vars var_heap
		= var_heap
	where
		adjust_ref_count_of_variable_pattern var_occ_in_alts=:{occ_ref_count = RC_Unused} var_info_ptr var_expr_ptr var_heap
			= var_heap <:= (var_info_ptr, VI_Occurrence { var_occ_in_alts &
							occ_ref_count = RC_Used { rcu_multiply = [], rcu_uniquely = [var_expr_ptr], rcu_selectively = [] }})
		adjust_ref_count_of_variable_pattern var_occ_in_alts=:{occ_ref_count = RC_Used rcu} var_info_ptr var_expr_ptr var_heap
			= var_heap  <:= (var_info_ptr, VI_Occurrence { var_occ_in_alts &
							occ_ref_count = RC_Used { rcu & rcu_uniquely = [var_expr_ptr : rcu.rcu_uniquely] }})

		ref_mark_of_variable_pattern free_vars var_info_ptr var_occ=:{occ_bind = OB_OpenLet let_expr} var_heap
			# (VI_Occurrence empty_var_occ, var_heap) = readPtr var_info_ptr var_heap
			= closeAndMarkBinding free_vars var_info_ptr empty_var_occ.occ_ref_count empty_var_occ let_expr var_heap
		ref_mark_of_variable_pattern _ _ _ var_heap
			= var_heap
			
	ref_mark_of_pattern free_vars with_pattern_bindings expr var_heap
		# var_heap	= saveOccurrences free_vars var_heap
		  var_heap	= refMark free_vars NotASelector No expr var_heap
		  var_heap	= caseCombine with_pattern_bindings free_vars var_heap
		= var_heap  

	ref_mark_of_alternatives free_vars sel def opt_pattern_var patterns case_explicit case_default var_heap
		# (local_lets, var_heap) = collectOpenLetVars free_vars var_heap
		  (def, used_lets, var_heap) = refMarkOfDefault case_explicit free_vars sel def case_default local_lets var_heap
		  (with_pattern_bindings, pattern_depth, used_lets, var_heap)
			= foldSt (ref_mark_of_algebraic_pattern free_vars sel opt_pattern_var local_lets def) patterns (False, 0, used_lets, var_heap)		
		  var_heap = addRefMarkOfDefault pattern_depth free_vars def used_lets var_heap
		= (with_pattern_bindings, var_heap)
		
	ref_mark_of_algebraic_pattern free_vars sel opt_pattern_var local_lets def {ap_vars,ap_expr}
					(with_pattern_bindings, pattern_depth, used_lets, var_heap) 
//		# var_heap = saveOccurrencesWhenNeeded pattern_depth free_vars var_heap
		# var_heap = saveOccurrences free_vars var_heap
		  used_pattern_vars = collectPatternsVariables ap_vars
		  var_heap = bind_optional_pattern_variable opt_pattern_var used_pattern_vars var_heap
		  var_heap = refMark [ [ pv_var \\ {pv_var} <- used_pattern_vars ] : free_vars ] sel def ap_expr var_heap
		  var_heap = restore_binding_of_pattern_variable opt_pattern_var used_pattern_vars var_heap
		  (used_lets, var_heap) = collectUsedLetVars local_lets (used_lets, var_heap)
		= (with_pattern_bindings || not (isEmpty used_pattern_vars), inc pattern_depth, used_lets, var_heap)	

	bind_optional_pattern_variable _ [] var_heap
		= var_heap
	bind_optional_pattern_variable (Yes var_info_ptr) used_pattern_vars var_heap
		# (VI_Occurrence var_occ, var_heap) = readPtr var_info_ptr var_heap
		= var_heap <:= (var_info_ptr, VI_Occurrence { var_occ & occ_pattern_vars = [ used_pattern_vars : var_occ.occ_pattern_vars ] })
	bind_optional_pattern_variable _ used_pattern_vars var_heap
		= var_heap

	restore_binding_of_pattern_variable _ [] var_heap
		= var_heap
	restore_binding_of_pattern_variable (Yes var_info_ptr) used_pattern_vars var_heap
		# (VI_Occurrence var_occ, var_heap) = readPtr var_info_ptr var_heap
		= var_heap <:= (var_info_ptr, VI_Occurrence { var_occ & occ_pattern_vars = tl var_occ.occ_pattern_vars })
	restore_binding_of_pattern_variable _ used_pattern_vars var_heap
		= var_heap

refMarkOfDefault case_explicit free_vars sel def (Yes expr) local_lets var_heap
	# var_heap = saveOccurrences free_vars var_heap
	  var_heap = refMark free_vars sel No expr var_heap
	  (used_lets, var_heap) = collectUsedLetVars local_lets ([], var_heap)
	  (occurrences, var_heap) = restoreOccurrences free_vars var_heap
	= (Yes occurrences, used_lets, var_heap)
refMarkOfDefault case_explicit free_vars sel def No local_lets var_heap
	| case_explicit
		= (No, [], var_heap)
		= (def, [], var_heap)

addRefMarkOfDefault pattern_depth free_vars (Yes occurrences) used_lets var_heap
//	# var_heap = saveOccurrencesWhenNeeded pattern_depth free_vars var_heap
	# var_heap = saveOccurrences  free_vars var_heap
	  var_heap = foldSt set_occurrence occurrences var_heap
	  var_heap = setUsedLetVars used_lets var_heap
	= altCombine (inc pattern_depth) free_vars var_heap
where
	set_occurrence {cfv_var={fv_name,fv_info_ptr}, cfv_count} var_heap
		# (VI_Occurrence old_occ, var_heap) = readPtr fv_info_ptr var_heap
		= var_heap <:= (fv_info_ptr, VI_Occurrence {old_occ & occ_ref_count = cfv_count } )
addRefMarkOfDefault pattern_depth free_vars No used_lets var_heap
	# var_heap = setUsedLetVars used_lets var_heap
	= altCombine pattern_depth free_vars var_heap 


/*
parCombine free_vars var_heap
	= foldSt (foldSt (par_combine)) free_vars var_heap
where
	par_combine {fv_info_ptr} var_heap
		# (VI_Occurrence old_occ=:{occ_ref_count,occ_previous=[prev_ref_count:prev_counts]}, var_heap) = readPtr fv_info_ptr var_heap
		= var_heap <:= (fv_info_ptr, VI_Occurrence { old_occ &
				occ_ref_count = parCombineRefCount occ_ref_count prev_ref_count , occ_previous = prev_counts })
*/

caseCombine do_par_combine free_vars var_heap
	= foldSt (foldSt (case_combine do_par_combine)) free_vars var_heap // (var_heap ---> ("caseCombine", free_vars))
where
	case_combine do_par_combine {fv_name,fv_info_ptr} var_heap
		# (VI_Occurrence old_occ, var_heap) = readPtr fv_info_ptr var_heap
		= case old_occ.occ_previous of // ---> ("case_combine", fv_name, old_occ.occ_ref_count, length old_occ.occ_previous) of
			[ref_count_in_alt , glob_ref_count : occ_previous]
				# comb_ref_count = case_combine_ref_counts do_par_combine old_occ.occ_ref_count ref_count_in_alt
				# comb_ref_count = parCombineRefCount comb_ref_count glob_ref_count
				-> var_heap <:= (fv_info_ptr, VI_Occurrence { old_occ & occ_ref_count = comb_ref_count , occ_previous = occ_previous })
			_
				-> abort ("inconsistent reference count administration" ---> fv_name)

	case_combine_ref_counts do_par_combine ref_count_in_pattern ref_count_in_alt
		| do_par_combine
			= parCombineRefCount ref_count_in_pattern	ref_count_in_alt
			= seqCombineRefCount ref_count_in_alt		ref_count_in_pattern

altCombine depth free_vars var_heap
	= foldSt (foldSt (alt_combine depth)) free_vars var_heap // (var_heap ---> ("altCombine", free_vars))
where
	alt_combine depth {fv_name,fv_info_ptr} var_heap
		# (VI_Occurrence old_occ=:{occ_ref_count,occ_previous}, var_heap) = readPtr fv_info_ptr var_heap
		  (occ_ref_count, occ_previous) = alt_combine_ref_counts occ_ref_count occ_previous ((dec depth)) // ---> ("alt_combine", fv_name, occ_ref_count, length occ_previous, depth))
		= var_heap <:= (fv_info_ptr, VI_Occurrence { old_occ & occ_ref_count = occ_ref_count , occ_previous = occ_previous })
				
	alt_combine_ref_counts comb_ref_count ref_counts 0
		= (comb_ref_count, ref_counts)
	alt_combine_ref_counts comb_ref_count [occ_ref_count:occ_previous] depth
		# new_comb_ref_count = alt_combine_ref_count comb_ref_count occ_ref_count
		= alt_combine_ref_counts new_comb_ref_count occ_previous (dec depth)
//				---> ("alt_combine_ref_count", comb_ref_count, occ_ref_count, new_comb_ref_count)

	alt_combine_ref_count RC_Unused ref_count
		= ref_count
	alt_combine_ref_count ref_count RC_Unused
		= ref_count
	alt_combine_ref_count (RC_Used {rcu_multiply,rcu_selectively,rcu_uniquely}) (RC_Used ref_count2)
		= RC_Used { rcu_uniquely = rcu_uniquely ++ ref_count2.rcu_uniquely, rcu_multiply = rcu_multiply ++ ref_count2.rcu_multiply,
					rcu_selectively = alt_combine_of_selections rcu_selectively ref_count2.rcu_selectively }
	where
		alt_combine_of_selections [] sels
			= sels
		alt_combine_of_selections sels []
			= sels
		alt_combine_of_selections sl1=:[sel1=:{ su_field, su_multiply, su_uniquely } : sels1] sl2=:[sel2 : sels2]
			| su_field == sel2.su_field
				# sel1 = { sel1 & su_multiply = sel2.su_multiply ++ su_multiply, su_uniquely =  sel2.su_uniquely ++ su_uniquely }
				= [ sel1 : alt_combine_of_selections sels1 sels2 ]
			| su_field < sel2.su_field
				= [sel1 : alt_combine_of_selections sels1 sl2 ]
				= [sel2 : alt_combine_of_selections sl1 sels2 ]

parCombineRefCount RC_Unused ref_count
	= ref_count
parCombineRefCount ref_count RC_Unused
	= ref_count
parCombineRefCount (RC_Used {rcu_multiply,rcu_selectively,rcu_uniquely}) (RC_Used ref_count2)
	# rcu_multiply = ref_count2.rcu_uniquely ++ ref_count2.rcu_multiply ++ rcu_uniquely ++ rcu_multiply
	| isEmpty rcu_multiply
		=  RC_Used { rcu_multiply = [], rcu_uniquely = [], rcu_selectively = par_combine_selections rcu_selectively ref_count2.rcu_selectively }
		# rcu_multiply = collectAllSelections ref_count2.rcu_selectively (collectAllSelections rcu_selectively rcu_multiply)
		= RC_Used { rcu_multiply = rcu_multiply, rcu_uniquely = [], rcu_selectively = [] }
where	
	par_combine_selections [] sels
		= sels
	par_combine_selections sels []
		= sels
	par_combine_selections sl1=:[sel1=:{ su_field, su_multiply, su_uniquely } : sels1] sl2=:[sel2 : sels2]
		| su_field == sel2.su_field
			# sel1 = { sel1 & su_multiply = sel2.su_multiply ++ su_multiply ++ sel2.su_uniquely ++ su_uniquely, su_uniquely = [] }
			= [ sel1 : par_combine_selections sels1 sels2 ]
		| su_field < sel2.su_field
			= [sel1 : par_combine_selections sels1 sl2 ]
			= [sel2 : par_combine_selections sl1 sels2 ]

seqCombineRefCount RC_Unused ref_count
	= ref_count
seqCombineRefCount ref_count RC_Unused
	= ref_count
seqCombineRefCount (RC_Used sec_ref) (RC_Used prim_ref)
	# rcu_multiply = prim_ref.rcu_uniquely ++ prim_ref.rcu_multiply ++ sec_ref.rcu_multiply
	| isEmpty rcu_multiply
		| isEmpty sec_ref.rcu_uniquely /* so sec_ref contains selections only */
			# rcu_selectively = seq_combine_selections sec_ref.rcu_selectively prim_ref.rcu_selectively /* rcu_selectively can't be empty */
			= RC_Used { rcu_uniquely = [], rcu_multiply = [], rcu_selectively = rcu_selectively }
			# prim_selections = make_primary_selections_on_unique prim_ref.rcu_selectively
			  rcu_selectively = seq_combine_selections sec_ref.rcu_selectively prim_selections
			= RC_Used { sec_ref & rcu_selectively = rcu_selectively }
		= RC_Used { sec_ref & rcu_multiply = collectAllSelections prim_ref.rcu_selectively rcu_multiply }
	where	
		seq_combine_selections [] sels
			= sels
		seq_combine_selections sels []
			= sels
		seq_combine_selections sl1=:[sel1=:{ su_field, su_multiply, su_uniquely } : sels1] sl2=:[sel2 : sels2]
			| su_field == sel2.su_field
				# sel1 = { sel1 & su_multiply = sel2.su_multiply ++ sel2.su_uniquely ++ su_multiply }
				= [ sel1 : seq_combine_selections sels1 sels2 ]
			| su_field < sel2.su_field
				= [sel1 : seq_combine_selections sels1 sl2 ]
				= [sel2 : seq_combine_selections sl1 sels2 ]

		make_primary_selections_on_unique [sel=:{su_multiply, su_uniquely } : sels]
			= [ { sel & su_multiply = su_uniquely ++ su_multiply, su_uniquely = [] } : make_primary_selections_on_unique sels ]
		make_primary_selections_on_unique []
			= []

emptyOccurrence observing =
		{	occ_ref_count		= RC_Unused
		,	occ_previous		= []
		,	occ_observing		= observing
		,	occ_bind			= OB_Empty
		, 	occ_pattern_vars	= []
		}

emptyObservingOccurrence	=: VI_Occurrence (emptyOccurrence True)
emptyNonObservingOccurrence =: VI_Occurrence (emptyOccurrence False)
																	
makeSharedReferencesNonUnique :: ![Int] !u:{# FunDef} !*Coercions !w:{! Type} !v:TypeDefInfos !*VarHeap !*ExpressionHeap !*ErrorAdmin
	-> (!u:{# FunDef}, !*Coercions, !w:{! Type},  !v:TypeDefInfos, !*VarHeap, !*ExpressionHeap, !*ErrorAdmin)
makeSharedReferencesNonUnique [] fun_defs coercion_env subst type_def_infos var_heap expr_heap  error
	= (fun_defs, coercion_env, subst, type_def_infos, var_heap, expr_heap, error)
makeSharedReferencesNonUnique [fun : funs] fun_defs coercion_env subst type_def_infos var_heap expr_heap error
	# (fun_def, fun_defs) = fun_defs![fun] 
	# (coercion_env, subst, type_def_infos, var_heap, expr_heap, error)
		= make_shared_references_of_funcion_non_unique fun_def coercion_env subst type_def_infos var_heap expr_heap error
	= makeSharedReferencesNonUnique funs fun_defs coercion_env subst type_def_infos var_heap expr_heap error
where
	make_shared_references_of_funcion_non_unique {fun_symb, fun_pos, fun_body = TransformedBody {tb_args,tb_rhs},fun_info={fi_local_vars}}
			coercion_env subst type_def_infos var_heap expr_heap error
	# variables = tb_args ++ fi_local_vars
	  (subst, type_def_infos, var_heap, expr_heap) = clear_occurrences variables subst type_def_infos var_heap expr_heap
	  var_heap = refMark [tb_args] NotASelector No tb_rhs var_heap // (tb_rhs ---> ("makeSharedReferencesNonUnique", fun_symb, tb_rhs)) var_heap
	  position = newPosition fun_symb fun_pos
	  (coercion_env, var_heap, expr_heap, error) = make_shared_vars_non_unique variables coercion_env var_heap expr_heap
	  		(setErrorAdmin position error)
	= (coercion_env, subst, type_def_infos, var_heap, expr_heap, error)
	
	where
		clear_occurrences vars subst type_def_infos var_heap expr_heap
			= foldSt initial_occurrence vars (subst, type_def_infos, var_heap, expr_heap)
		where
			initial_occurrence {fv_name,fv_info_ptr} (subst, type_def_infos, var_heap, expr_heap) 
				# (var_info, var_heap) = readPtr fv_info_ptr var_heap
				| has_observing_base_type var_info type_def_infos subst
					= (subst, type_def_infos, var_heap <:= (fv_info_ptr, emptyObservingOccurrence), expr_heap)
					= (subst, type_def_infos, var_heap <:= (fv_info_ptr, emptyNonObservingOccurrence), expr_heap)
				
		has_observing_base_type (VI_Type {at_type} _) type_def_infos subst
			= has_observing_type at_type type_def_infos subst
		has_observing_base_type (VI_FAType _ {at_type} _) type_def_infos subst
			= has_observing_type at_type type_def_infos subst
		has_observing_base_type _ type_def_infos subst
			= abort "has_observing_base_type (refmark.icl)"

		make_shared_vars_non_unique vars coercion_env var_heap expr_heap error
			= foldl make_shared_var_non_unique (coercion_env, var_heap, expr_heap, error) vars

		make_shared_var_non_unique (coercion_env, var_heap, expr_heap, error)  fv=:{fv_name,fv_info_ptr}
			# (VI_Occurrence occ, var_heap) = readPtr fv_info_ptr var_heap
			= case occ.occ_ref_count of
				RC_Used {rcu_multiply,rcu_selectively}
					# (coercion_env, expr_heap, error) = make_shared_occurrences_non_unique fv rcu_multiply (coercion_env, expr_heap, error)
					  (coercion_env, expr_heap, error) = foldSt (make_selection_non_unique fv) rcu_selectively (coercion_env, expr_heap, error)  
					-> (coercion_env, var_heap, expr_heap, error)
				_
					-> (coercion_env, var_heap, expr_heap, error)
//						---> ("make_shared_var_non_unique", fv_name)

		make_shared_occurrences_non_unique fv multiply (coercion_env, expr_heap, error)
			= foldSt (make_shared_occurrence_non_unique fv) multiply (coercion_env, expr_heap, error) 
		
		make_shared_occurrence_non_unique free_var var_expr_ptr (coercion_env, expr_heap, error) 
			| isNilPtr var_expr_ptr
				= (coercion_env, expr_heap, error)
				# (expr_info, expr_heap) = readPtr var_expr_ptr expr_heap
				= case expr_info of
					EI_Attribute sa_attr_nr
						# (succ, coercion_env) = tryToMakeNonUnique sa_attr_nr coercion_env
						| succ
//								 ---> ("make_shared_occurrence_non_unique", free_var, var_expr_ptr, sa_attr_nr)
							-> (coercion_env, expr_heap, error)
							-> (coercion_env, expr_heap, uniquenessError (CP_Expression (FreeVar free_var)) " demanded attribute cannot be offered by shared object" error)
					_
						-> abort ("make_shared_occurrence_non_unique" ---> ((free_var, var_expr_ptr) )) // <<- expr_info))

		make_selection_non_unique fv {su_multiply} cee
			= make_shared_occurrences_non_unique fv su_multiply cee

/*
	has_observing_type type_def_infos TE
		= True
	has_observing_type type_def_infos (TB basic_type)
		= True
*/
	has_observing_type (TB basic_type) type_def_infos subst
		= True
	has_observing_type (TempV var_number) type_def_infos subst
		= case subst.[var_number] of
			TE
				-> True
			subst_type
				-> 	has_observing_type subst_type type_def_infos subst
	has_observing_type (TA {type_index = {glob_object,glob_module}} type_args) type_def_infos subst
		# {tdi_properties} = type_def_infos.[glob_module].[glob_object]
		= foldSt (\ {at_type} ok -> ok && has_observing_type at_type type_def_infos subst) type_args (tdi_properties bitand cIsHyperStrict <> 0)
	has_observing_type type type_def_infos subst
		= False
					
instance <<< ReferenceCount
where
	(<<<) file RC_Unused = file
	(<<<) file (RC_Used {rcu_multiply,rcu_uniquely,rcu_selectively}) = file <<< '\n' <<< "M:" <<< rcu_multiply <<< " U:" <<< rcu_uniquely <<< " S:" <<< rcu_selectively

instance <<< SelectiveUse
where
	(<<<) file {su_field,su_multiply,su_uniquely} = file <<< su_field <<< " M:" <<< su_multiply <<< " U:" <<< su_uniquely



instance <<< (Ptr v)
where
	(<<<) file ptr = file <<< '[' <<< ptrToInt ptr <<< ']'


