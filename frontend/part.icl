module part

import StdEnv

import syntax, transform, checksupport, StdCompare, check, utilities

::	PartitioningInfo = 
	{	pi_marks :: 		!.{# Int}
	,	pi_next_num ::		!Int
	,	pi_next_group ::	!Int
	,	pi_groups ::		![[Int]]
	,	pi_deps ::			![Int]
	}

NotChecked :== -1	

Start = 3

partitionateFunctions :: !*{# FunDef} !*{# FunDef} -> (!{! Group}, !*{# FunDef}, !*{# FunDef})
partitionateFunctions fun_defs inst_defs
	#! nr_of_functions = size fun_defs
	   nr_of_instances = size inst_defs
	#! max_fun_nr = nr_of_functions + nr_of_instances
	# partitioning_info = { pi_marks = createArray max_fun_nr NotChecked, pi_deps = [], pi_next_num = 0, pi_next_group = 0, pi_groups = [] }
	  (fun_defs, inst_defs, {pi_groups,pi_next_group}) = partitionate_functions 0 max_fun_nr nr_of_functions fun_defs inst_defs partitioning_info
	  groups = { {group_members = group} \\ group <- reverse pi_groups }
	= (groups, fun_defs, inst_defs)
where
	partitionate_functions :: !Int !Int !Int !*{# FunDef} !*{# FunDef} !*PartitioningInfo -> (!*{# FunDef}, !*{# FunDef}, !*PartitioningInfo)
	partitionate_functions from_index max_fun_nr nr_of_functions fun_defs inst_defs pi=:{pi_marks}
		| from_index == max_fun_nr
			= (fun_defs, inst_defs, pi)
		| pi_marks.[from_index] == NotChecked
			# (_, fun_defs, inst_defs, pi) = partitionate_function from_index max_fun_nr nr_of_functions fun_defs inst_defs pi
			= partitionate_functions (inc from_index) max_fun_nr nr_of_functions fun_defs inst_defs pi
			= partitionate_functions (inc from_index) max_fun_nr nr_of_functions fun_defs inst_defs pi

	partitionate_function :: !Int !Int !Int !*{# FunDef} !*{# FunDef} !*PartitioningInfo -> *(!Int, !*{# FunDef}, !*{# FunDef}, !*PartitioningInfo)
	partitionate_function fun_index max_fun_nr nr_of_functions fun_defs inst_defs pi=:{pi_next_num}
		| fun_index < nr_of_functions
			#! fd = fun_defs.[fun_index]
			| fd.fun_kind
				# {fi_calls,fi_instance_calls} = fd.fun_info
				  (min_dep, fun_defs, inst_defs, pi) = visit_functions fi_calls max_fun_nr max_fun_nr nr_of_functions fun_defs inst_defs (push_on_dep_stack fun_index pi)
				  (min_dep, fun_defs, inst_defs, pi) = visit_functions fi_calls min_dep max_fun_nr nr_of_functions fun_defs inst_defs pi
				= try_to_close_group fun_index pi_next_num min_dep max_fun_nr nr_of_functions fun_defs inst_defs pi
			#! fd = inst_defs.[fun_index-nr_of_functions]
			# {fi_calls,fi_instance_calls} = fd.fun_info
			  (min_dep, fun_defs, inst_defs, pi) = visit_functions fi_calls max_fun_nr max_fun_nr nr_of_functions fun_defs inst_defs (push_on_dep_stack fun_index pi)
			  (min_dep, fun_defs, inst_defs, pi) = visit_functions fi_calls min_dep max_fun_nr nr_of_functions fun_defs inst_defs pi
			= try_to_close_group fun_index pi_next_num min_dep max_fun_nr nr_of_functions fun_defs inst_defs pi
				  
	push_on_dep_stack :: !Int !*PartitioningInfo -> *PartitioningInfo;
	push_on_dep_stack fun_index pi=:{pi_deps,pi_marks,pi_next_num}
		= { pi & pi_deps = [fun_index : pi_deps], pi_marks = { pi_marks & [fun_index] = pi_next_num}, pi_next_num = inc pi_next_num}

	visit_functions :: ![FunCall] !Int !Int !Int !*{# FunDef} !*{# FunDef} !*PartitioningInfo -> *(!Int, !*{# FunDef}, !*{# FunDef}, !*PartitioningInfo)
	visit_functions [{fc_index}:funs] min_dep max_fun_nr nr_of_functions fun_defs inst_defs pi=:{pi_marks} 
		#! mark = pi_marks.[fc_index]
		| mark == NotChecked
			# (mark, fun_defs, inst_defs, pi) = partitionate_function fc_index max_fun_nr nr_of_functions fun_defs inst_defs  pi
			= visit_functions funs (min min_dep mark) max_fun_nr nr_of_functions fun_defs inst_defs pi
			= visit_functions funs (min min_dep mark) max_fun_nr nr_of_functions fun_defs inst_defs pi
	visit_functions [] min_dep max_fun_nr nr_of_functions fun_defs inst_defs pi
		= (min_dep, fun_defs, inst_defs, pi)
		

	try_to_close_group :: !Int !Int !Int !Int !Int !*{# FunDef} !*{# FunDef} !*PartitioningInfo -> *(!Int, !*{# FunDef}, !*{# FunDef}, !*PartitioningInfo)
	try_to_close_group fun_index fun_nr min_dep max_fun_nr nr_of_functions fun_defs inst_defs pi=:{pi_marks, pi_deps, pi_groups, pi_next_group}
		| fun_nr <= min_dep
			# (pi_deps, pi_marks, group, fun_defs, inst_defs)
				= close_group fun_index pi_deps pi_marks [] max_fun_nr nr_of_functions pi_next_group fun_defs inst_defs
				
			  pi = { pi & pi_deps = pi_deps, pi_marks = pi_marks, pi_next_group = inc pi_next_group,  pi_groups = [group : pi_groups] }
			= (max_fun_nr, fun_defs, inst_defs, pi)
			= (min_dep, fun_defs, inst_defs, pi)
	where
		close_group :: !Int ![Int] !*{# Int} ![Int] !Int !Int !Index !*{# FunDef} !*{# FunDef} -> (![Int], !*{# Int}, ![Int], !*{# FunDef}, !*{# FunDef})
		close_group fun_index [d:ds] marks group max_fun_nr nr_of_functions group_number fun_defs inst_defs
			#! fd = fun_defs.[d]
			# marks = { marks & [d] = max_fun_nr }
			| d < nr_of_functions
				#! fd = fun_defs.[d]
				# fun_defs = { fun_defs & [d] = { fd & fun_info.fi_group_index = group_number }}
				| d == fun_index
					= (ds, marks, [d : group], fun_defs, inst_defs)
					= close_group fun_index ds marks group max_fun_nr nr_of_functions group_number fun_defs inst_defs
				#! fd = inst_defs.[d-nr_of_functions]
				# inst_defs = { inst_defs & [d] = { fd & fun_info.fi_group_index = group_number }}
				| d == fun_index
					= (ds, marks, [d : group], fun_defs, inst_defs)
					= close_group fun_index ds marks group max_fun_nr nr_of_functions group_number fun_defs inst_defs
