implementation module checkKindCorrectness

import StdEnv
import syntax, containers, checksupport, utilities

// import RWSDebug

checkKindCorrectness :: !NumberSet !Index IndexRange !{#CommonDefs} !{#DclModule} !u:{# FunDef} !*TypeVarHeap !*TypeDefInfos !*ErrorAdmin
					-> (!u:{# FunDef}, !*TypeVarHeap, !*TypeDefInfos, !*ErrorAdmin)
checkKindCorrectness icl_used_module_numbers main_dcl_module_n icl_instances common_defs dcl_mods
			fun_defs th_vars td_infos error_admin
	#! n_fun_defs = size fun_defs
	# (th_vars, td_infos, error_admin)
			= iFoldSt (\mod_index state
						-> if (inNumberSet mod_index icl_used_module_numbers)
								(check_kind_correctness_of_classes common_defs common_defs.[mod_index] state)
								state)
					0 (size dcl_mods) (th_vars, td_infos, error_admin)
	  th_vars = th_vars
	  (th_vars, td_infos, error_admin)
			= iFoldSt (\mod_index state
						-> if (inNumberSet mod_index icl_used_module_numbers)
								(check_kind_correctness_of_instances_and_class_and_member_contexts
										common_defs common_defs.[mod_index] state)
								state)
					0 (size dcl_mods) (th_vars, td_infos, error_admin)
	  // check_kind_correctness_of_icl_function: don't check the types that were generated for instances
	  th_vars = th_vars
	  state
			= iFoldSt check_kind_correctness_of_icl_function 0 icl_instances.ir_from
					(fun_defs, th_vars, td_infos, error_admin)
	  (fun_defs, th_vars, td_infos, error_admin)
			= iFoldSt check_kind_correctness_of_icl_function icl_instances.ir_to n_fun_defs state
	  th_vars = th_vars
	  (th_vars, td_infos, error_admin)
			= iFoldSt (\mod_index state
						-> if (inNumberSet mod_index icl_used_module_numbers && mod_index<>main_dcl_module_n)
						   	  (check_kind_correctness_of_dcl_functions common_defs dcl_mods.[mod_index] 
						   	  		state)
			    		      state)
			  0 (size dcl_mods)
			  (th_vars, td_infos, error_admin)
	  th_vars = th_vars
	= (fun_defs, th_vars, td_infos, error_admin)
  where
	check_kind_correctness_of_classes common_defs {com_class_defs, com_member_defs} state 
		= foldlArraySt (check_kind_correctness_of_class common_defs com_member_defs) com_class_defs state
	check_kind_correctness_of_class common_defs com_member_defs {class_name, class_args, class_members}
			(th_vars, td_infos, error_admin)
		# th_vars
				= foldSt init_type_var class_args th_vars
		= foldlArraySt (\{ds_index} state
							-> check_kind_correctness_of_member_without_context common_defs class_args 
									com_member_defs.[ds_index] state)
					class_members (th_vars, td_infos, error_admin)
	check_kind_correctness_of_member_without_context common_defs class_args 
				{me_symb, me_pos, me_class_vars, me_type=me_type=:{st_vars, st_args, st_result}}
				(th_vars, td_infos, error_admin)
		# error_admin
				= setErrorAdmin (newPosition me_symb me_pos) error_admin
		  th_vars
				= foldSt init_type_var st_vars th_vars
		  th_vars
		  		= fold2St copy_TVI class_args me_class_vars th_vars
		  (th_vars, td_infos, error_admin)
		  		= unsafeFold2St (check_kind_correctness_of_atype KindConst) 
		  				[0..] [st_result:st_args] (th_vars, td_infos, error_admin)
		  th_vars
		  		= fold2St copy_TVI me_class_vars class_args th_vars
		= (th_vars, td_infos, error_admin)
	  where
		copy_TVI src dst th_vars
			# (tvi, th_vars)
					= readPtr src.tv_info_ptr th_vars
			= writePtr dst.tv_info_ptr tvi th_vars
	check_kind_correctness_of_instances_and_class_and_member_contexts common_defs 
			{com_instance_defs, com_class_defs, com_member_defs} state
		# state
				= foldlArraySt (check_kind_correctness_of_instance common_defs) com_instance_defs state
		  state
				= foldlArraySt 
					(check_kind_correctness_of_class_context_and_member_contexts common_defs com_member_defs)
					com_class_defs state
		= state
	check_kind_correctness_of_instance common_defs {ins_class, ins_ident, ins_pos, ins_type}
				(th_vars, td_infos, error_admin)
		# {class_args}
				= common_defs.[ins_class.glob_module].com_class_defs.[ins_class.glob_object.ds_index]
		  (expected_kinds, th_vars)
		  		= mapSt get_tvi class_args th_vars
		  error_admin
		  		= setErrorAdmin (newPosition ins_ident ins_pos) error_admin
		  th_vars
		  		= foldSt init_type_var ins_type.it_vars th_vars
		  state
		  		= unsafeFold3St possibly_check_kind_correctness_of_type expected_kinds [1..] 
		  				ins_type.it_types (th_vars, td_infos, error_admin)
		  state
		  		= foldSt (check_kind_correctness_of_context common_defs) ins_type.it_context state
		= state
	possibly_check_kind_correctness_of_type TVI_Empty _ _ state
		// This can happen for stooopid classes like StdClass::Ord, where the member type is ignored at all
		= state
	possibly_check_kind_correctness_of_type (TVI_Kind expected_kind) arg_nr type state
		= check_kind_correctness_of_type expected_kind arg_nr type state
	check_kind_correctness_of_class_context_and_member_contexts common_defs com_member_defs
				{class_name, class_pos, class_context, class_members} (th_vars, td_infos, error_admin)
		# error_admin
				= setErrorAdmin (newPosition class_name class_pos) error_admin
		  state
				= foldSt (check_kind_correctness_of_context common_defs) class_context
						(th_vars, td_infos, error_admin)
		  state
		  		= foldlArraySt (check_kind_correctness_of_member_context common_defs com_member_defs)
		  				class_members state
		= state
	check_kind_correctness_of_member_context common_defs com_member_defs {ds_index}
				(th_vars, td_infos, error_admin)
		# {me_symb, me_pos, me_type}
				= com_member_defs.[ds_index]
		  error_admin
		  		= setErrorAdmin (newPosition me_symb me_pos) error_admin
		= foldSt (check_kind_correctness_of_context common_defs) me_type.st_context 
				(th_vars, td_infos, error_admin)
	get_tvi {tv_info_ptr} th_vars
		= readPtr tv_info_ptr th_vars
	check_kind_correctness_of_icl_function fun_n (fun_defs, th_vars, td_infos, error_admin)
		# (fun_def, fun_defs) = fun_defs![fun_n]
		= case fun_def.fun_type of
			No
				-> (fun_defs, th_vars, td_infos, error_admin)
			Yes st
				# (th_vars, td_infos, error_admin)
						= check_kind_correctness_of_symbol_type common_defs fun_def.fun_symb fun_def.fun_pos
								st (th_vars, td_infos, error_admin)
				-> (fun_defs, th_vars, td_infos, error_admin)
	check_kind_correctness_of_dcl_functions common_defs {dcl_functions, dcl_instances, dcl_macros} state
		= iFoldSt (\i state
					-> if (in_index_range i dcl_instances || in_index_range i dcl_macros) // yawn
						  state
						  (let ({ft_symb, ft_pos, ft_type}) = dcl_functions.[i]
						    in check_kind_correctness_of_symbol_type common_defs ft_symb ft_pos ft_type 
						    		state))
					0 (size dcl_functions) state
	check_kind_correctness_of_symbol_type common_defs fun_symb fun_pos 
			st=:{st_vars, st_args, st_result, st_context} (th_vars, td_infos, error_admin)
		# error_admin
				= setErrorAdmin (newPosition fun_symb fun_pos) error_admin
		  th_vars
				= foldSt init_type_var st_vars th_vars
		  (th_vars, td_infos, error_admin)
		  		= unsafeFold2St (check_kind_correctness_of_atype KindConst) 
		  				[0..] [st_result:st_args] (th_vars, td_infos, error_admin)
		  (th_vars, td_infos, error_admin)
		  		= foldSt (check_kind_correctness_of_context common_defs) st_context (th_vars, td_infos, error_admin)
		= (th_vars, td_infos, error_admin)
	check_kind_correctness_of_atype expected_kind arg_nr {at_type} state
		= check_kind_correctness_of_type expected_kind arg_nr at_type state
	check_kind_correctness_of_type expected_kind arg_nr (TA {type_name,type_index} args)
					(th_vars, td_infos, error_admin)
		# ({tdi_kinds}, td_infos)
				= td_infos![type_index.glob_module,type_index.glob_object]
		  (th_vars, td_infos, error_admin)
		  		= unsafeFold2St (flip check_kind_correctness_of_atype arg_nr) tdi_kinds args
		  				(th_vars, td_infos, error_admin)
		  n_args
		  		= length args
		  kind_of_application
		  		= if (n_args==length tdi_kinds) 
		  			KindConst
		  			(KindArrow (drop n_args tdi_kinds))
		  error_admin
		  		= check_equality_of_kinds arg_nr expected_kind kind_of_application error_admin
		= (th_vars, td_infos, error_admin)
	check_kind_correctness_of_type expected_kind _ (TV tv) (th_vars, td_infos, error_admin)
		# (th_vars, error_admin)
		  		= unify_var_kinds expected_kind tv th_vars error_admin
		= (th_vars, td_infos, error_admin)
	check_kind_correctness_of_type expected_kind _ (GTV tv) (th_vars, td_infos, error_admin)
		# (th_vars, error_admin)
		  		= unify_var_kinds expected_kind tv th_vars error_admin
		= (th_vars, td_infos, error_admin)
	check_kind_correctness_of_type expected_kind arg_nr (l --> r) state
		# state
				= check_kind_correctness_of_atype KindConst arg_nr l state
		  (th_vars, td_infos, error_admin)
				= check_kind_correctness_of_atype KindConst arg_nr r state
		  error_admin
		  		= check_equality_of_kinds arg_nr expected_kind KindConst error_admin
		= (th_vars, td_infos, error_admin)
	check_kind_correctness_of_type expected_kind arg_nr ((CV tv) :@: args) state
		# (th_vars, td_infos, error_admin)
				= foldSt (check_kind_correctness_of_atype KindConst arg_nr) args state
		  expected_kind_of_cons_var
		  		= KindArrow (repeatn (length args) KindConst)
		  (th_vars, error_admin)
		  		= unify_var_kinds expected_kind_of_cons_var tv th_vars error_admin
		  error_admin
		  		= check_equality_of_kinds arg_nr expected_kind KindConst error_admin
		= (th_vars, td_infos, error_admin)
	check_kind_correctness_of_type expected_kind arg_nr (TB _) (th_vars, td_infos, error_admin)
		# error_admin
		  		= check_equality_of_kinds arg_nr expected_kind KindConst error_admin
		= (th_vars, td_infos, error_admin)
	
	check_kind_correctness_of_context common_defs {tc_class, tc_types} (th_vars, td_infos, error_admin)
		# {class_args}
				= common_defs.[tc_class.glob_module].com_class_defs.[tc_class.glob_object.ds_index]
		  (expected_kinds, th_vars)
		  		= mapSt get_tvi class_args th_vars
		  state
		  		= unsafeFold3St possibly_check_kind_correctness_of_type expected_kinds (descending (-1))
		  				tc_types (th_vars, td_infos, error_admin)
		= state
	  where
		descending i = [i:descending (i-1)]
		  
	init_type_var {tv_info_ptr} th_vars
		= writePtr tv_info_ptr TVI_Empty th_vars
		
	unify_var_kinds expected_kind {tv_name, tv_info_ptr} th_vars error_admin
		# (tvi, th_vars)
				= readPtr tv_info_ptr th_vars
		= case tvi of
			TVI_Empty
				-> (writePtr tv_info_ptr (TVI_Kind expected_kind) th_vars, error_admin)
			TVI_Kind kind
				| expected_kind==kind
					-> (th_vars, error_admin)
				-> (th_vars, checkError "cannot consistently assign a kind to type variable"
										tv_name.id_name error_admin)
	check_equality_of_kinds arg_nr expected_kind kind error_admin
		| expected_kind==kind
			= error_admin
		= checkError "inconsistent kind in " (arg_nr_to_string arg_nr) error_admin

	arg_nr_to_string 0 = "result type"
	arg_nr_to_string i
		| i >0
			= "type of argument nr "+++toString i
		= "type context nr "+++toString (~i)
		

in_index_range test ir :== test>=ir.ir_from && test < ir.ir_to
