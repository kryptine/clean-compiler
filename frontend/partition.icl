/*
	module owner: Diederik van Arkel
*/
implementation module partition

import syntax, transform

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
					= abort ("visit_functions "+++toString fd.fun_ident+++" "+++toString module_index+++" "+++toString fc_index)
				
				visit_functions [DclFunCall module_index fc_index:funs] min_dep max_fun_nr fun_defs pi
					= visit_functions funs min_dep max_fun_nr fun_defs pi

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
				= close_group False False fun_index pi_deps pi_marks [] max_fun_nr pi_next_group fun_defs
			  pi = { pi & pi_deps = pi_deps, pi_marks = pi_marks, pi_next_group = inc pi_next_group,  pi_groups = [group : pi_groups] }
			= (max_fun_nr, fun_defs, pi)
			= (min_dep, fun_defs, pi)
	where
		close_group :: !Bool !Bool !Int ![Int] !*{# Int} ![Int] !Int !Int !*{# FunDef} -> (![Int], !*{# Int}, ![Int], !*{# FunDef})
		close_group n_r_known non_recursive fun_index [d:ds] marks group max_fun_nr group_number fun_defs
			# marks = { marks & [d] = max_fun_nr }
			# (fd,fun_defs) = fun_defs![d]
			# non_recursive = case n_r_known of
								True	-> non_recursive
								_		-> case fun_index == d of
									True	-> isEmpty [fc \\ fc <- fd.fun_info.fi_calls | case fc of FunCall idx _ -> idx == d; _ -> False]
									_		-> False
			# fd = { fd & fun_info.fi_group_index = group_number, fun_info.fi_properties = set_rec_prop non_recursive fd.fun_info.fi_properties}
			# fun_defs = { fun_defs & [d] = fd}
			| d == fun_index
				= (ds, marks, [d : group], fun_defs)
				= close_group True non_recursive fun_index ds marks [d : group] max_fun_nr group_number fun_defs


::	PartitioningInfo` = 
	{	pi_marks` :: 		!.{# Int}
	,	pi_next_num` ::		!Int
	,	pi_next_group` ::	!Int
	,	pi_groups` ::		![[Int]]
	,	pi_deps` ::			![Int]
	
//	,	pi_predef` ::		!PredefSymbolsForTransform
	,	pi_collect` ::		!.CollectState
	}

stripStrictLets :: !*{# FunDef} !*PredefinedSymbols !*VarHeap !*ExpressionHeap !*ErrorAdmin -> (!*{# FunDef}, !*PredefinedSymbols, !*VarHeap, !*ExpressionHeap, !*ErrorAdmin)
stripStrictLets fun_defs predef_symbols var_heap sym_heap error_admin
	# (cs_predef,predef_symbols) = get_predef_symbols_for_transform predef_symbols
	# collect_state =
		{ cos_predef_symbols_for_transform	= cs_predef
		, cos_var_heap						= var_heap
		, cos_symbol_heap					= sym_heap
		, cos_error							= error_admin
		}
	# (fun_defs,collect_state) = aMapSt ref_null fun_defs collect_state
	= (fun_defs,predef_symbols,collect_state.cos_var_heap, collect_state.cos_symbol_heap, collect_state.cos_error)
where
	aMapSt f a s
		# (l,s)	= mapSt f [e \\ e <-: a] s
		= ({e \\ e <- l},s)

partitionateFunctions` :: !*{# FunDef} ![IndexRange] !Index !Int !Int !*PredefinedSymbols !*VarHeap !*ExpressionHeap !*ErrorAdmin -> (!*{! Group}, !*{# FunDef}, !*PredefinedSymbols, !*VarHeap, !*ExpressionHeap, !*ErrorAdmin)
partitionateFunctions` fun_defs ranges main_dcl_module_n def_min def_max predef_symbols var_heap sym_heap error_admin
	#! max_fun_nr = size fun_defs
	# (cs_predef,predef_symbols) = get_predef_symbols_for_transform predef_symbols
	# collect_state =
		{ cos_predef_symbols_for_transform	= cs_predef
		, cos_var_heap						= var_heap
		, cos_symbol_heap					= sym_heap
		, cos_error							= error_admin
		}
	# partitioning_info =
		{ pi_collect` = collect_state
		, pi_marks` = createArray max_fun_nr NotChecked
		, pi_deps` = []
		, pi_next_num` = 0
		, pi_next_group` = 0
		, pi_groups` = [] 
		}
	  (fun_defs, {pi_groups`,pi_next_group`,pi_collect`}) = 
	  		foldSt (partitionate_functions max_fun_nr) ranges (fun_defs, partitioning_info)
	  groups = { {group_members = group} \\ group <- reverse pi_groups` }
	= (groups, fun_defs, predef_symbols, pi_collect`.cos_var_heap, pi_collect`.cos_symbol_heap, pi_collect`.cos_error)
where
	partitionate_functions :: !Index !IndexRange !(!*{# FunDef}, !*PartitioningInfo`) -> (!*{# FunDef}, !*PartitioningInfo`)
	partitionate_functions max_fun_nr ir=:{ir_from,ir_to} (fun_defs, pi=:{pi_marks`})
		| ir_from == ir_to
			= (fun_defs, pi)
		| pi_marks`.[ir_from] == NotChecked
			# (_, fun_defs, pi) = partitionate_function ir_from max_fun_nr fun_defs pi
			= partitionate_functions max_fun_nr { ir & ir_from = inc ir_from } (fun_defs, pi)
			= partitionate_functions max_fun_nr { ir & ir_from = inc ir_from } (fun_defs, pi)

	partitionate_function :: !Int !Int !*{# FunDef} !*PartitioningInfo` -> *(!Int, !*{# FunDef}, !*PartitioningInfo`)
	partitionate_function fun_index max_fun_nr fun_defs pi=:{pi_next_num`,pi_collect`}
		# (fd, fun_defs) = fun_defs![fun_index]
//		# {fi_calls} = fd.fun_info
		# (fd,pi_collect`) = ref_null fd pi_collect`
		# pi = {pi & pi_collect` = pi_collect`}
		# fc_state = find_calls
						{ main_dcl_module_n=main_dcl_module_n
						, def_min=def_min
						, def_max=def_max
						, fun_index=fun_index
						} fd.fun_body {fun_calls = []}
		  fi_calls = fc_state.fun_calls
		  fd = {fd & fun_info.fi_calls = fi_calls}
		# fun_defs = {fun_defs & [fun_index] = fd}

		  pi = push_on_dep_stack fun_index pi
		  (min_dep, fun_defs, pi) = visit_functions fi_calls max_fun_nr max_fun_nr fun_defs pi
			with
				visit_functions :: ![FunCall] !Int !Int !*{# FunDef} !*PartitioningInfo` -> *(!Int, !*{# FunDef}, !*PartitioningInfo`)
				visit_functions [FunCall fc_index _:funs] min_dep max_fun_nr fun_defs pi=:{pi_marks`} 
					#! mark = pi_marks`.[fc_index]
					| mark == NotChecked
						# (mark, fun_defs, pi) = partitionate_function fc_index max_fun_nr fun_defs  pi
						= visit_functions funs (min min_dep mark) max_fun_nr fun_defs pi
						= visit_functions funs (min min_dep mark) max_fun_nr fun_defs pi
				
				visit_functions [MacroCall module_index fc_index _:funs] min_dep max_fun_nr fun_defs pi
					= abort ("visit_functions "+++toString fd.fun_ident+++" "+++toString module_index+++" "+++toString fc_index)
				
				visit_functions [DclFunCall module_index fc_index:funs] min_dep max_fun_nr fun_defs pi
					= visit_functions funs min_dep max_fun_nr fun_defs pi

				visit_functions [] min_dep max_fun_nr fun_defs pi
					= (min_dep, fun_defs, pi)
		= try_to_close_group fun_index pi_next_num` min_dep max_fun_nr fun_defs pi

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
	push_on_dep_stack :: !Int !*PartitioningInfo` -> *PartitioningInfo`;
	push_on_dep_stack fun_index pi=:{pi_deps`,pi_marks`,pi_next_num`}
		= { pi & pi_deps` = [fun_index : pi_deps`], pi_marks` = { pi_marks` & [fun_index] = pi_next_num`}, pi_next_num` = inc pi_next_num`}


	try_to_close_group :: !Int !Int !Int !Int !*{# FunDef} !*PartitioningInfo` -> *(!Int, !*{# FunDef}, !*PartitioningInfo`)
	try_to_close_group fun_index fun_nr min_dep max_fun_nr fun_defs pi=:{pi_marks`, pi_deps`, pi_groups`, pi_next_group`}
		| fun_nr <= min_dep
			# (pi_deps`, pi_marks`, group, fun_defs)
				= close_group False False fun_index pi_deps` pi_marks` [] max_fun_nr pi_next_group` fun_defs
			  pi = { pi & pi_deps` = pi_deps`, pi_marks` = pi_marks`, pi_next_group` = inc pi_next_group`,  pi_groups` = [group : pi_groups`] }
			= (max_fun_nr, fun_defs, pi)
			= (min_dep, fun_defs, pi)
	where
		close_group :: !Bool !Bool !Int ![Int] !*{# Int} ![Int] !Int !Int !*{# FunDef} -> (![Int], !*{# Int}, ![Int], !*{# FunDef})
		close_group n_r_known non_recursive fun_index [d:ds] marks group max_fun_nr group_number fun_defs
			# marks = { marks & [d] = max_fun_nr }
			# (fd,fun_defs) = fun_defs![d]
			# non_recursive = case n_r_known of
								True	-> non_recursive
								_		-> case fun_index == d of
									True	-> isEmpty [fc \\ fc <- fd.fun_info.fi_calls | case fc of FunCall idx _ -> idx == d; _ -> False]
									_		-> False
			# fd = { fd & fun_info.fi_group_index = group_number, fun_info.fi_properties = set_rec_prop non_recursive fd.fun_info.fi_properties}
			# fun_defs = { fun_defs & [d] = fd}
			| d == fun_index
				= (ds, marks, [d : group], fun_defs)
				= close_group True non_recursive fun_index ds marks [d : group] max_fun_nr group_number fun_defs

::	PartitioningInfo`` = 
	{ pi_marks``			:: !.Marks
	, pi_next_num``			:: !Int
	, pi_next_group``		:: !Int
	, pi_groups``			:: ![[Int]]
	, pi_deps``				:: ![Int]
	, pi_collect``			:: !.CollectState
	}

//:: Marks	:== {# Int}
:: Marks	:== {# Mark}
:: Mark		= { m_fun :: !Int, m_mark :: !Int}

create_marks max_fun_nr functions
//	# marks				= createArray max_fun_nr max_fun_nr
//	# marks				= {marks & [i] = NotChecked \\ i <- functions}
//	= marks
	= {{m_fun = fun, m_mark = NotChecked} \\ fun <- functions}
get_mark max_fun_nr marks fun
//	:== marks.[fun]
	:== case [m_mark \\ {m_fun,m_mark} <-: marks | m_fun == fun] of
		[]		-> max_fun_nr
		[m:_]	-> m
set_mark marks fun val
//	:== { marks & [fun] = val}
//	:== { if (m_fun==fun) {m & m_mark = val} m \\ m=:{m_fun=m_fun} <-: marks}
	:== { if (m.m_fun==fun) {m & m_mark = val} m \\ m <-: marks}
	
partitionateFunctions`` :: !Int !Int ![FunctionInfoPtr] !*{# FunDef} ![Int] !Index !Int !Int !*FunctionHeap !*PredefinedSymbols !*VarHeap !*ExpressionHeap !*ErrorAdmin
	-> (!Int, ![Group], !*{# FunDef}, !*FunctionHeap, !*PredefinedSymbols, !*VarHeap, !*ExpressionHeap, !*ErrorAdmin)
partitionateFunctions`` max_fun_nr next_group new_functions fun_defs functions main_dcl_module_n def_min def_max fun_heap predef_symbols var_heap sym_heap error_admin
	# marks					= create_marks max_fun_nr functions
	# (cs_predef,predef_symbols) = get_predef_symbols_for_transform predef_symbols
	# collect_state =
		{ cos_predef_symbols_for_transform	= cs_predef
		, cos_var_heap						= var_heap
		, cos_symbol_heap					= sym_heap
		, cos_error							= error_admin
		}
	# partitioning_info =
		{ pi_marks``		= marks
		, pi_deps``			= []
		, pi_next_num``		= 0
		, pi_next_group``	= next_group
		, pi_groups``		= [] 
		, pi_collect``		= collect_state
		}
	  (fun_defs, fun_heap, {pi_groups``,pi_next_group``,pi_collect``}) = 
	  		foldSt (partitionate_functions max_fun_nr) functions (fun_defs, fun_heap, partitioning_info)
	  groups = [ {group_members = group} \\ group <- reverse pi_groups`` ]
	= (pi_next_group``,groups, fun_defs, fun_heap, predef_symbols, pi_collect``.cos_var_heap, pi_collect``.cos_symbol_heap, pi_collect``.cos_error)
where
	partitionate_functions :: !Index !Int !(!*{# FunDef}, !*FunctionHeap, !*PartitioningInfo``) -> (!*{# FunDef}, !*FunctionHeap, !*PartitioningInfo``)
	partitionate_functions max_fun_nr fun (fun_defs, fun_heap, pi=:{pi_marks``})
		| get_mark max_fun_nr pi_marks`` fun == NotChecked
			# (_, fun_defs, fun_heap, pi) = partitionate_function fun max_fun_nr fun_defs fun_heap pi
			= (fun_defs, fun_heap, pi)
			= (fun_defs, fun_heap, pi)

	partitionate_function :: !Int !Int !*{# FunDef} !*FunctionHeap !*PartitioningInfo`` -> *(!Int, !*{# FunDef}, !*FunctionHeap, !*PartitioningInfo``)
	partitionate_function fun_index max_fun_nr fun_defs fun_heap pi=:{pi_next_num``,pi_collect``}
//		# (fd, fun_defs) = fun_defs![fun_index]
		# (fd, fun_defs, fun_heap)	= get_fun_def fun_index new_functions fun_defs fun_heap
		# (fd,pi_collect``) = ref_null fd pi_collect``
		# pi = {pi & pi_collect`` = pi_collect``}
		# fc_state = find_calls
						{ main_dcl_module_n=main_dcl_module_n
						, def_min=def_min
						, def_max=def_max
						, fun_index=fun_index
						} fd.fun_body {fun_calls = []}
		  fi_calls = fc_state.fun_calls
		  fd = {fd & fun_info.fi_calls = fi_calls}
		# (fun_defs, fun_heap) = set_fun_def fun_index fd new_functions fun_defs fun_heap
		  pi = push_on_dep_stack fun_index pi
		  (min_dep, fun_defs, fun_heap, pi) = visit_functions fi_calls max_fun_nr max_fun_nr fun_defs fun_heap pi
			with
				visit_functions :: ![FunCall] !Int !Int !*{# FunDef} !*FunctionHeap !*PartitioningInfo`` -> *(!Int, !*{# FunDef}, !*FunctionHeap, !*PartitioningInfo``)
				visit_functions [FunCall fc_index _:funs] min_dep max_fun_nr fun_defs fun_heap pi=:{pi_marks``} 
					#! mark = get_mark max_fun_nr pi_marks`` fc_index
					| mark == NotChecked
						# (mark, fun_defs, fun_heap, pi) = partitionate_function fc_index max_fun_nr fun_defs fun_heap pi
						= visit_functions funs (min min_dep mark) max_fun_nr fun_defs fun_heap pi
						= visit_functions funs (min min_dep mark) max_fun_nr fun_defs fun_heap pi
				
				visit_functions [MacroCall module_index fc_index _:funs] min_dep max_fun_nr fun_defs fun_heap pi
					= abort ("visit_functions "+++toString fd.fun_ident+++" "+++toString module_index+++" "+++toString fc_index)
				
				visit_functions [DclFunCall module_index fc_index:funs] min_dep max_fun_nr fun_defs fun_heap pi
					= visit_functions funs min_dep max_fun_nr fun_defs fun_heap pi

				visit_functions [] min_dep max_fun_nr fun_defs fun_heap pi
					= (min_dep, fun_defs, fun_heap, pi)
		= try_to_close_group fun_index pi_next_num`` min_dep max_fun_nr fun_defs fun_heap pi

	push_on_dep_stack :: !Int !*PartitioningInfo`` -> *PartitioningInfo``;
	push_on_dep_stack fun_index pi=:{pi_deps``,pi_marks``,pi_next_num``} =
		{ pi 
		& pi_deps`` = [fun_index : pi_deps``]
		, pi_marks`` = set_mark pi_marks`` fun_index pi_next_num``
		, pi_next_num`` = inc pi_next_num``
		}


	try_to_close_group :: !Int !Int !Int !Int !*{# FunDef} !*FunctionHeap !*PartitioningInfo`` -> *(!Int, !*{# FunDef}, !*FunctionHeap, !*PartitioningInfo``)
	try_to_close_group fun_index fun_nr min_dep max_fun_nr fun_defs fun_heap pi=:{pi_marks``, pi_deps``, pi_groups``, pi_next_group``}
		| fun_nr <= min_dep
			# (pi_deps``, pi_marks``, group, fun_defs, fun_heap)
				= close_group False False fun_index pi_deps`` pi_marks`` [] max_fun_nr pi_next_group`` fun_defs fun_heap
			  pi = { pi & pi_deps`` = pi_deps``, pi_marks`` = pi_marks``, pi_next_group`` = inc pi_next_group``,  pi_groups`` = [group : pi_groups``] }
			= (max_fun_nr, fun_defs, fun_heap, pi)
			= (min_dep, fun_defs, fun_heap, pi)
	where
		close_group :: !Bool !Bool !Int ![Int] !*Marks ![Int] !Int !Int !*{# FunDef} !*FunctionHeap -> (![Int], !*Marks, ![Int], !*{# FunDef}, !*FunctionHeap)
		close_group n_r_known non_recursive fun_index [d:ds] marks group max_fun_nr group_number fun_defs fun_heap
			# marks = set_mark marks d max_fun_nr
			# (fd, fun_defs, fun_heap) = get_fun_def d new_functions fun_defs fun_heap
			# non_recursive = case n_r_known of
								True	-> non_recursive
								_		-> case fun_index == d of
									True	-> isEmpty [fc \\ fc <- fd.fun_info.fi_calls | case fc of FunCall idx _ -> idx == d; _ -> False]
									_		-> False
			# fd = { fd & fun_info.fi_group_index = group_number, fun_info.fi_properties = set_rec_prop non_recursive fd.fun_info.fi_properties}
			# (fun_defs, fun_heap) = set_fun_def d fd new_functions fun_defs fun_heap
			| d == fun_index
				= (ds, marks, [d : group], fun_defs, fun_heap)
				= close_group True non_recursive fun_index ds marks [d : group] max_fun_nr group_number fun_defs fun_heap

	get_fun_def fun new_functions fun_defs fun_heap
		| fun < size fun_defs
			# (fun_def, fun_defs)			= fun_defs![fun]
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
	
	set_fun_def fun fun_def new_functions fun_defs fun_heap
		| fun < size fun_defs
			= ({fun_defs & [fun] = fun_def}, fun_heap)
		# (fun_def_ptr, fun_heap)			= lookup_ptr fun new_functions fun_heap
			with
				lookup_ptr fun [] ti_fun_heap = abort "drat"
				lookup_ptr fun [fun_def_ptr:new_functions] ti_fun_heap
					# (FI_Function {gf_fun_index}, ti_fun_heap)
							= readPtr fun_def_ptr ti_fun_heap
					| gf_fun_index == fun
						= (fun_def_ptr, ti_fun_heap)
						= lookup_ptr fun new_functions ti_fun_heap
		# (FI_Function gf, fun_heap)
											= readPtr fun_def_ptr fun_heap
		# fun_heap							= writePtr fun_def_ptr (FI_Function {gf & gf_fun_def = fun_def}) fun_heap
		= (fun_defs, fun_heap)

//~~~~~~~~~~~~~~

:: FindCallsInfo =
	{ main_dcl_module_n	:: !Index
	, def_min			:: !Int
	, def_max			:: !Int
	, fun_index			:: !Int
	}

:: FindCallsState =
	{ fun_calls			:: ![FunCall]
//	, ref_added			:: !Bool
//	, ref_used_vars		:: !
	}

class find_calls a :: !FindCallsInfo !a !FindCallsState -> FindCallsState

instance find_calls [a] | find_calls a
where
	find_calls fc_info els fc_state = foldSt (find_calls fc_info) els fc_state

instance find_calls (Optional a) | find_calls a
where
	find_calls fc_info (Yes e) fc_state = find_calls fc_info e fc_state
	find_calls fc_info No fc_state = fc_state

instance find_calls FunctionBody
where
	find_calls fc_info (TransformedBody tb) fc_state
		= find_calls fc_info tb fc_state
//	find_calls fc_info NoBody fc_state = fc_state
	find_calls fc_info _ fc_state = abort ("Undefined pattern in FunctionBody: "+++toString fc_info.fun_index+++ "?" +++ toString fc_info.def_min+++ "?" +++ toString fc_info.def_max +++ "\n")

instance find_calls TransformedBody
where
	find_calls fc_info {tb_rhs} fc_state = find_calls fc_info tb_rhs fc_state

instance find_calls Expression
where
	find_calls fc_info (Var _)					fc_state = fc_state
	find_calls fc_info (App app)				fc_state = find_calls fc_info app fc_state
	find_calls fc_info (exp @ exps)				fc_state = find_calls fc_info exps (find_calls fc_info exp fc_state)
	find_calls fc_info (Let lete)				fc_state = find_calls fc_info lete fc_state
	find_calls fc_info (Case kees)				fc_state = find_calls fc_info kees fc_state
	find_calls fc_info (Selection _ exp sells)	fc_state = find_calls fc_info sells (find_calls fc_info exp fc_state)
	find_calls fc_info (Update e1 sl e2)		fc_state
		#! fc_state	= find_calls fc_info e1 fc_state
		   fc_state	= find_calls fc_info sl fc_state
		= find_calls fc_info e2 fc_state
	find_calls fc_info (RecordUpdate _ expr bexps) fc_state
		#! fc_state	= find_calls fc_info expr fc_state
		= find_calls fc_info (map (\{bind_src} -> bind_src) bexps) fc_state
	find_calls fc_info (TupleSelect _ _ expr) fc_state
		= find_calls fc_info expr fc_state
	find_calls fc_info (BasicExpr _) fc_state
		= fc_state
	find_calls fc_info (Conditional _) fc_state
		= abort "Conditional"
	find_calls fc_info (AnyCodeExpr _ _ _) fc_state
		= fc_state
	find_calls fc_info (ABCCodeExpr _ _) fc_state
		= fc_state
	find_calls fc_info (MatchExpr _ expr) fc_state
		= find_calls fc_info expr fc_state
	find_calls fc_info (FreeVar _) fc_state
		= abort "FreeVar"
	find_calls fc_info (Constant _ _ _) fc_state
		= abort "Constant"
	find_calls fc_info (ClassVariable _) fc_state
		= abort "ClassVariable"
	find_calls fc_info (DynamicExpr _) fc_state
		= abort "DynamicExpr"
	find_calls fc_info (TypeCodeExpression _) fc_state
		= abort "TypeCodeExpression"
	find_calls fc_info EE fc_state
		= fc_state	//abort "EE"
	find_calls fc_info (NoBind _) fc_state
		= fc_state
	find_calls fc_info (FailExpr _) fc_state
		= fc_state
	find_calls fc_info (DictionariesFunction dictionaries expr expr_type) fc_state
		= find_calls fc_info expr fc_state
	find_calls _ u _
		= abort ("find_calls : Undefined pattern in Expression\n")

instance find_calls App
where
	find_calls fc_info {app_symb,app_args} fc_state
		#! fc_state = get_index app_symb.symb_kind fc_state
		= find_calls fc_info app_args fc_state
	where
		get_index (SK_Function {glob_object,glob_module}) fc_state
			| fc_info.main_dcl_module_n == glob_module && (glob_object < fc_info.def_max || glob_object >= fc_info.def_min)
				= {fc_state & fun_calls = [FunCall glob_object 0: fc_state.fun_calls]}
				= {fc_state & fun_calls = [DclFunCall glob_module glob_object: fc_state.fun_calls]}
		get_index (SK_Constructor idx) fc_state
				= fc_state
		get_index (SK_Unknown) fc_state
				= abort "SK_Unknown"
		get_index (SK_IclMacro _) fc_state
				= abort "SK_IclMacro"
		get_index (SK_LocalMacroFunction idx) fc_state
				= {fc_state & fun_calls = [FunCall idx 0: fc_state.fun_calls]}
//				= fc_state
		get_index (SK_DclMacro _) fc_state
				= abort "SK_DclMacro"
		get_index (SK_LocalDclMacroFunction _) fc_state
				= abort "SK_LocalDclMacroFunction"
		get_index (SK_OverloadedFunction _) fc_state
				= abort "SK_OverloadedFunction"
		get_index (SK_GeneratedFunction _ idx) fc_state
				= {fc_state & fun_calls = [FunCall idx 0: fc_state.fun_calls]}
//				= fc_state
//		get_index (SK_GeneratedCaseFunction _ idx) fc_state
//				= {fc_state & fun_calls = [FunCall idx 0: fc_state.fun_calls]}
		get_index (SK_Generic _ _) fc_state
				= abort "SK_Generic"
		get_index (SK_TypeCode) fc_state
				= abort "SK_TypeCode"
		get_index u _ = abort "Undefined pattern in get_index\n"

instance find_calls Let
where
	find_calls fc_info {let_strict_binds,let_lazy_binds,let_expr} fc_state
		= find_calls fc_info (let_strict_binds++let_lazy_binds) (find_calls fc_info let_expr fc_state)

instance find_calls Case
where
	find_calls fc_info {case_expr,case_guards,case_default} fc_state
		#! fc_state	= find_calls fc_info case_expr fc_state
		   fc_state	= find_calls fc_info case_default fc_state
		= find_calls fc_info case_guards fc_state

instance find_calls Selection
where
	find_calls fc_info (RecordSelection _ _) fc_state
		= fc_state
	find_calls fc_info (ArraySelection _ _ expr) fc_state
		= find_calls fc_info expr fc_state
	find_calls fc_info (DictionarySelection _ sells _ expr) fc_state
		= find_calls fc_info expr (find_calls fc_info sells fc_state)
	find_calls _ u _ = abort "Undefined pattern in Selection\n"

instance find_calls LetBind
where
	find_calls fc_info {lb_src} fc_state
		= find_calls fc_info lb_src fc_state

instance find_calls CasePatterns
where
	find_calls fc_info (AlgebraicPatterns _ pats) fc_state
		= find_calls fc_info pats fc_state
	find_calls fc_info (BasicPatterns _ pats) fc_state
		= find_calls fc_info pats fc_state
	find_calls fc_info (DynamicPatterns pats) fc_state
		= find_calls fc_info pats fc_state
	find_calls fc_info (OverloadedListPatterns _ expr pats) fc_state
		= find_calls fc_info pats (find_calls fc_info expr fc_state)
	find_calls fc_info (NoPattern) fc_state
		= fc_state
	find_calls _ u _ = abort "Undefined pattern in CasePatterns\n"

instance find_calls AlgebraicPattern
where
	find_calls fc_info {ap_expr} fc_state
		= find_calls fc_info ap_expr fc_state

instance find_calls BasicPattern
where
	find_calls fc_info {bp_expr} fc_state
		= find_calls fc_info bp_expr fc_state

instance find_calls DynamicPattern
where
	find_calls fc_info {dp_rhs} fc_state
		= find_calls fc_info dp_rhs fc_state

////////////////////////
import StdDebug

ref_null fd=:{fun_body=TransformedBody {tb_args,tb_rhs}} pi_collect
//	| not (fst (ferror (stderr <<< fd)))
	
//	# tb_args = tb_args ---> ("ref_null",fd.fun_ident,tb_args,tb_rhs)
	# (new_rhs, new_args, _, _, pi_collect) = determineVariablesAndRefCounts tb_args tb_rhs pi_collect
	# fd = {fd & fun_body=TransformedBody {tb_args=new_args,tb_rhs=new_rhs}}
	= (fd,pi_collect)
ref_null fd pi_collect
	= (fd, pi_collect)

/////////////// from check.icl ////////////////////

get_predef_symbols_for_transform :: *PredefinedSymbols -> (!PredefSymbolsForTransform,!.PredefinedSymbols)
// clean 2.0 does not allow this, clean 1.3 does:
// get_predef_symbols_for_transform cs_predef_symbols=:{[PD_DummyForStrictAliasFun]=predef_alias_dummy,[PD_AndOp]=predef_and,[PD_OrOp]=predef_or}
get_predef_symbols_for_transform cs_predef_symbols
	# (predef_alias_dummy,cs_predef_symbols) = cs_predef_symbols![PD_DummyForStrictAliasFun]
	# (predef_and,cs_predef_symbols) = cs_predef_symbols![PD_AndOp]
	# (predef_or,cs_predef_symbols) = cs_predef_symbols![PD_OrOp]
	= ({predef_alias_dummy=predef_alias_dummy,predef_and=predef_and,predef_or=predef_or},cs_predef_symbols)

dummy_predef_symbol =
	{ pds_module	= 0
	, pds_def		= 0
	}

dummy_predef_symbols =
	{ predef_alias_dummy	= dummy_predef_symbol
	, predef_and			= dummy_predef_symbol
	, predef_or				= dummy_predef_symbol
	}

set_rec_prop non_recursive fi_properties
	= case non_recursive of
		True	-> fi_properties bitor FI_IsNonRecursive
		_		-> fi_properties bitand (bitnot FI_IsNonRecursive)
