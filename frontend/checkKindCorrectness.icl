implementation module checkKindCorrectness

import StdEnv
import syntax, containers, checksupport, utilities

// import RWSDebug

checkKindCorrectness :: !Index IndexRange !u:{# FunDef} !{#CommonDefs} !*{#DclModule} !*TypeVarHeap !*TypeDefInfos !*ErrorAdmin
					-> (!u:{# FunDef}, !*{#DclModule}, !*TypeVarHeap, !*TypeDefInfos, !*ErrorAdmin)
checkKindCorrectness main_dcl_module_n icl_instances fun_defs common_defs 
			dcl_mods th_vars td_infos error_admin
	#! n_fun_defs
			= size fun_defs
	   size_dcl_mods
	   		= size dcl_mods
	# (bv_cashed_modules, dcl_mods)
			= iFoldSt mark_cashed_module
					0 size_dcl_mods (bitvectCreate size_dcl_mods, dcl_mods)
	  (dcl_mods, th_vars, td_infos, error_admin)
			= iFoldSt (\mod_index state
						-> if (bitvectSelect mod_index bv_cashed_modules)
								state
								(check_classes mod_index state))
					0 size_dcl_mods (dcl_mods, th_vars, td_infos, error_admin)
	  icl_common_defs
	  		= common_defs.[main_dcl_module_n]
	  (_, th_vars, td_infos, error_admin)
	  		= foldrArraySt (check_class icl_common_defs.com_member_defs)
	  				icl_common_defs.com_class_defs
					([], th_vars, td_infos, error_admin)
	  bv_uninitialized_mods
	  		= {el\\el<-:bv_cashed_modules}
	  (bv_uninitialized_mods, th_vars, td_infos, error_admin)
			= iFoldSt (\mod_index state
						-> if (bitvectSelect mod_index bv_cashed_modules)
								state
								(check_instances_and_class_and_member_contexts
										common_defs common_defs.[mod_index] state))
					0 size_dcl_mods (bv_uninitialized_mods, th_vars, td_infos, error_admin)
	  // check_icl_function: don't check the types that were generated for instances
	  state
			= iFoldSt (check_icl_function common_defs) 0 icl_instances.ir_from
					(fun_defs, bv_uninitialized_mods, th_vars, td_infos, error_admin)
	  (fun_defs, bv_uninitialized_mods, th_vars, td_infos, error_admin)
			= iFoldSt (check_icl_function common_defs) icl_instances.ir_to n_fun_defs state
	  (dcl_mods, bv_uninitialized_mods, th_vars, td_infos, error_admin)
			= iFoldSt (\mod_index state
						-> if (bitvectSelect mod_index bv_cashed_modules || mod_index==main_dcl_module_n)
			    		      state
						   	  (check_dcl_functions common_defs mod_index state))
			  0 size_dcl_mods
			  (dcl_mods, bv_uninitialized_mods, th_vars, td_infos, error_admin)
	= (fun_defs, dcl_mods, th_vars, td_infos, error_admin)
  where
	mark_cashed_module mod_index (bitvect, dcl_mods)
		| dcl_mods.[mod_index].dcl_is_cashed
			= (bitvectSet mod_index bitvect, dcl_mods)
		= (bitvect, dcl_mods)

	check_classes mod_index (dcl_mods, th_vars, td_infos, error_admin)
		# (dcl_mod, dcl_mods)
				= dcl_mods![mod_index]
		  {com_class_defs, com_member_defs}
		  		= dcl_mod.dcl_common
		  (class_defs_with_cacheable_kind_info, th_vars, td_infos, error_admin)
		  		= foldrArraySt (check_class com_member_defs) com_class_defs
						([], th_vars, td_infos, error_admin)
		  dcl_mods
		  		= { dcl_mods & [mod_index].dcl_common.com_class_defs 
		  				= { el \\ el <- class_defs_with_cacheable_kind_info }}
		= (dcl_mods, th_vars, td_infos, error_admin)
	check_class com_member_defs class_def=:{class_name, class_args, class_members}
			(class_defs_accu, th_vars, td_infos, error_admin)
		# th_vars
				= foldSt init_type_var class_args th_vars
		  (th_vars, td_infos, error_admin)
		  		= foldlArraySt (\{ds_index} state
									-> check_member_without_context class_args 
											com_member_defs.[ds_index] state)
							class_members (th_vars, td_infos, error_admin)
		  (derived_kinds, th_vars)
		  		= mapFilterYesSt get_opt_kind class_args th_vars
		= ([{ class_def & class_arg_kinds = derived_kinds }:class_defs_accu], th_vars, td_infos, error_admin)
	check_member_without_context class_args
				{me_symb, me_pos, me_class_vars, me_type=me_type=:{st_vars, st_args, st_result}}
				(th_vars, td_infos, error_admin)
		# error_admin
				= setErrorAdmin (newPosition me_symb me_pos) error_admin
		  th_vars
				= foldSt init_type_var st_vars th_vars
		  th_vars
		  		= fold2St copy_TVI class_args me_class_vars th_vars
		  (th_vars, td_infos, error_admin)
		  		= unsafeFold2St (check_atype KindConst) 
		  				[0..] [st_result:st_args] (th_vars, td_infos, error_admin)
		  th_vars
		  		= fold2St copy_TVI me_class_vars class_args th_vars
		= (th_vars, td_infos, error_admin)
	  where
		copy_TVI src dst th_vars
			# (tvi, th_vars)
					= readPtr src.tv_info_ptr th_vars
			= writePtr dst.tv_info_ptr tvi th_vars
	check_instances_and_class_and_member_contexts common_defs 
			{com_instance_defs, com_class_defs, com_member_defs} state
		# state
				= foldlArraySt (check_instance common_defs) com_instance_defs state
		  state
				= foldlArraySt 
					(check_class_context_and_member_contexts common_defs com_member_defs)
					com_class_defs state
		= state
	check_instance common_defs {ins_is_generic, ins_class, ins_ident, ins_pos, ins_type}
				(bv_uninitialized_mods, th_vars, td_infos, error_admin)
		| ins_is_generic
			// kind correctness of user supplied generic instances
			// is checked during generic phase
			= (bv_uninitialized_mods, th_vars, td_infos, error_admin)
		# (expected_kinds, bv_uninitialized_mods, th_vars)
				= get_expected_kinds ins_class common_defs bv_uninitialized_mods th_vars
		  error_admin
		  		= setErrorAdmin (newPosition ins_ident ins_pos) error_admin
		  th_vars
		  		= foldSt init_type_var ins_type.it_vars th_vars
		  (th_vars, td_infos, error_admin)
		  		= unsafeFold3St possibly_check_type expected_kinds [1..] 
		  				ins_type.it_types (th_vars, td_infos, error_admin)
		  state
		  		= foldSt (check_context common_defs) ins_type.it_context
		  				(bv_uninitialized_mods, th_vars, td_infos, error_admin)
		= state

	get_expected_kinds class_index=:{glob_module, glob_object} common_defs bv_uninitialized_mods th_vars
		| bitvectSelect glob_module bv_uninitialized_mods
			/* the desired class is defined in a module which is a cached one 
				=> check_classes has not been called for all the classes
				   within that module
				=> the kind information for the class args is not in the heap
				=> put it in the heap now
			*/
			# th_vars
					= foldlArraySt write_kind_info common_defs.[glob_module].com_class_defs th_vars
			= get_expected_kinds class_index common_defs (bitvectReset glob_module bv_uninitialized_mods)
					th_vars
		# {class_args, class_arg_kinds}
				= common_defs.[glob_module].com_class_defs.[glob_object.ds_index]
		  (expected_kinds, th_vars)
		  		= mapSt get_tvi class_args th_vars
		= (expected_kinds, bv_uninitialized_mods, th_vars)

	write_kind_info {class_name, class_args, class_arg_kinds} th_vars
		= write_ki class_args class_arg_kinds th_vars

	write_ki [{tv_info_ptr}:class_args] [class_arg_kind:class_arg_kinds] th_vars
		= write_ki class_args class_arg_kinds (writePtr tv_info_ptr (TVI_Kind class_arg_kind) th_vars)
	write_ki [{tv_info_ptr}:class_args] [] th_vars
		= write_ki class_args [] (writePtr tv_info_ptr TVI_Empty th_vars)
	write_ki [] [] th_vars
		= th_vars

	possibly_check_type TVI_Empty _ _ state
		// This can happen for stooopid classes like StdClass::Ord, where the member type is ignored at all
		= state
	possibly_check_type (TVI_Kind expected_kind) arg_nr type state
		= check_type expected_kind arg_nr type state
	check_class_context_and_member_contexts common_defs com_member_defs
				{class_name, class_pos, class_context, class_members, class_args} 
				(bv_uninitialized_mods, th_vars, td_infos, error_admin)
		# error_admin
				= setErrorAdmin (newPosition class_name class_pos) error_admin
		  state
				= foldSt (check_context common_defs) class_context
						(bv_uninitialized_mods, th_vars, td_infos, error_admin)
		  state
		  		= foldlArraySt (check_member_context common_defs com_member_defs)
		  				class_members state
		= state
	check_member_context common_defs com_member_defs {ds_index}
				(bv_uninitialized_mods, th_vars, td_infos, error_admin)
		# {me_symb, me_pos, me_type}
				= com_member_defs.[ds_index]
		  error_admin
		  		= setErrorAdmin (newPosition me_symb me_pos) error_admin
		= foldSt (check_context common_defs) me_type.st_context 
				(bv_uninitialized_mods, th_vars, td_infos, error_admin)
	get_tvi {tv_info_ptr} th_vars
		= readPtr tv_info_ptr th_vars
	get_opt_kind {tv_info_ptr} th_vars
		# (tvi, th_vars)
				= readPtr tv_info_ptr th_vars
		#! opt_kind
				= case tvi of
					TVI_Kind kind -> Yes kind
					_ -> No
		= (opt_kind, th_vars)
	check_icl_function common_defs fun_n 
				(fun_defs, bv_uninitialized_mods, th_vars, td_infos, error_admin)
		# (fun_def, fun_defs) = fun_defs![fun_n]
		= case fun_def.fun_type of
			No
				-> (fun_defs, bv_uninitialized_mods, th_vars, td_infos, error_admin)
			Yes st
				# (bv_uninitialized_mods, th_vars, td_infos, error_admin)
						= check_symbol_type common_defs fun_def.fun_symb fun_def.fun_pos
								st (bv_uninitialized_mods, th_vars, td_infos, error_admin)
				-> (fun_defs, bv_uninitialized_mods, th_vars, td_infos, error_admin)
	check_dcl_functions common_defs mod_index
			(dcl_mods, bv_uninitialized_mods, th_vars, td_infos, error_admin)
		# ({dcl_functions, dcl_instances, dcl_macros}, dcl_mods)
				= dcl_mods![mod_index]
		  (bv_uninitialized_mods, th_vars, td_infos, error_admin)
		  		= iFoldSt (\i state
							-> if (in_index_range i dcl_instances || in_index_range i dcl_macros) // yawn
								  state
								  (let ({ft_symb, ft_pos, ft_type}) = dcl_functions.[i]
								    in check_symbol_type common_defs ft_symb ft_pos ft_type 
								    		state))
							0 (size dcl_functions) (bv_uninitialized_mods, th_vars, td_infos, error_admin)
		= (dcl_mods, bv_uninitialized_mods, th_vars, td_infos, error_admin)
	check_symbol_type common_defs fun_symb fun_pos
			st=:{st_vars, st_args, st_result, st_context}
			(bv_uninitialized_mods, th_vars, td_infos, error_admin)
		# error_admin
				= setErrorAdmin (newPosition fun_symb fun_pos) error_admin
		  th_vars
				= foldSt init_type_var st_vars th_vars
		  (th_vars, td_infos, error_admin)
		  		= unsafeFold2St (check_atype KindConst) 
		  				[0..] [st_result:st_args] (th_vars, td_infos, error_admin)
		  (bv_uninitialized_mods, th_vars, td_infos, error_admin)
		  		= foldSt (check_context common_defs) st_context 
		  				(bv_uninitialized_mods, th_vars, td_infos, error_admin)
		= (bv_uninitialized_mods, th_vars, td_infos, error_admin)
	check_atype expected_kind arg_nr {at_type} state
		= check_type expected_kind arg_nr at_type state
	check_type expected_kind arg_nr (TA {type_name,type_index} args)
					(th_vars, td_infos, error_admin)
		# ({tdi_kinds}, td_infos)
				= td_infos![type_index.glob_module,type_index.glob_object]
		  (th_vars, td_infos, error_admin)
		  		= unsafeFold2St (flip check_atype arg_nr) tdi_kinds args
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
	check_type expected_kind _ (TV tv) (th_vars, td_infos, error_admin)
		# (th_vars, error_admin)
		  		= unify_var_kinds expected_kind tv th_vars error_admin
		= (th_vars, td_infos, error_admin)
	check_type expected_kind _ (GTV tv) (th_vars, td_infos, error_admin)
		# (th_vars, error_admin)
		  		= unify_var_kinds expected_kind tv th_vars error_admin
		= (th_vars, td_infos, error_admin)
	check_type expected_kind arg_nr (l --> r) state
		# state
				= check_atype KindConst arg_nr l state
		  (th_vars, td_infos, error_admin)
				= check_atype KindConst arg_nr r state
		  error_admin
		  		= check_equality_of_kinds arg_nr expected_kind KindConst error_admin
		= (th_vars, td_infos, error_admin)
	check_type expected_kind arg_nr ((CV tv) :@: args) state
		# (th_vars, td_infos, error_admin)
				= foldSt (check_atype KindConst arg_nr) args state
		  expected_kind_of_cons_var
		  		= KindArrow (repeatn (length args) KindConst)
		  (th_vars, error_admin)
		  		= unify_var_kinds expected_kind_of_cons_var tv th_vars error_admin
		  error_admin
		  		= check_equality_of_kinds arg_nr expected_kind KindConst error_admin
		= (th_vars, td_infos, error_admin)
	check_type expected_kind arg_nr (TB _) (th_vars, td_infos, error_admin)
		# error_admin
		  		= check_equality_of_kinds arg_nr expected_kind KindConst error_admin
		= (th_vars, td_infos, error_admin)
	
	check_context common_defs {tc_class, tc_types} 
			(bv_uninitialized_mods, th_vars, td_infos, error_admin)
		# (expected_kinds, bv_uninitialized_mods, th_vars)
		  		= get_expected_kinds tc_class common_defs bv_uninitialized_mods th_vars
		  (th_vars, td_infos, error_admin)
		  		= unsafeFold3St possibly_check_type expected_kinds (descending (-1))
		  				tc_types (th_vars, td_infos, error_admin)
		= (bv_uninitialized_mods, th_vars, td_infos, error_admin)
	  where
		descending i = [i:descending (i-1)]
		  
	init_type_var {tv_info_ptr} th_vars
		= writePtr tv_info_ptr TVI_Empty th_vars
		
	unify_var_kinds expected_kind tv=:{tv_name, tv_info_ptr} th_vars error_admin
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
		= checkError "inconsistent kind in" (arg_nr_to_string arg_nr) error_admin

	arg_nr_to_string 0 = "result type"
	arg_nr_to_string i
		| i >0
			= "type of argument nr "+++toString i
		= "type context nr "+++toString (~i)
		
	get_common_defs dcl_mods
		#! size = size dcl_mods
		# ({dcl_common=arbitrary_value_for_initializing}, dcl_mods) = dcl_mods![0]
		= loop 0 (createArray size arbitrary_value_for_initializing) dcl_mods
	  where
		loop :: !Int !*{#CommonDefs} !u:{#DclModule} -> (!*{#CommonDefs}, !u:{#DclModule})
		loop i common_defs dcl_mods
			| i==size dcl_mods
				= (common_defs, dcl_mods)
			# ({dcl_common}, dcl_mods) = dcl_mods![i]
			= loop (i+1) { common_defs & [i] = dcl_common } dcl_mods

in_index_range test ir :== test>=ir.ir_from && test < ir.ir_to

