implementation module check

import StdEnv

import syntax, typesupport, parse, checksupport, utilities, checktypes, transform, predef
import explicitimports, comparedefimp, checkFunctionBodies, containers, compilerSwitches
import genericsupport
import typereify
// import RWSDebug

cUndef :== (-1)
cDummyArray :== {}

isMainModule :: ModuleKind -> Bool
isMainModule MK_Main	= True
isMainModule _ 			= False

// AA: new implementation of generics ...
checkGenericDefs :: !Index !(Optional (CopiedDefinitions, Int)) !*{#GenericDef} !*{#CheckedTypeDef} !*{#ClassDef} !*{#DclModule} !*Heaps !*CheckState
	-> (!*{#GenericDef}, !*{#CheckedTypeDef}, !*{#ClassDef}, !*{#DclModule}, !*Heaps, !*CheckState)
checkGenericDefs mod_index opt_icl_info gen_defs type_defs class_defs modules heaps cs 	
	= check_generics 0 mod_index opt_icl_info gen_defs type_defs class_defs modules heaps cs
where
	check_generics index mod_index opt_icl_info gen_defs type_defs class_defs modules heaps cs
		# (n_generics, gen_defs) = usize gen_defs
		| index == n_generics 
			= (gen_defs, type_defs, class_defs, modules, heaps, cs)
			# (gen_defs, type_defs, class_defs, modules, heaps, cs) 
				= check_generic_def index mod_index opt_icl_info gen_defs type_defs class_defs modules heaps cs
			= check_generics (inc index) mod_index opt_icl_info gen_defs type_defs class_defs modules heaps cs		

	check_generic_def index mod_index opt_icl_info gen_defs type_defs class_defs modules heaps cs
		| has_to_be_checked mod_index index opt_icl_info 	
			= check_generic index mod_index gen_defs type_defs class_defs modules heaps cs		
				//---> ("check_generic", mod_index, index)
			= (gen_defs, type_defs, class_defs, modules, heaps, cs)
				//---> ("skipped check_generic", mod_index, index)

	has_to_be_checked module_index generic_index No 
		= True
	has_to_be_checked module_index generic_index (Yes ({copied_generic_defs}, n_cached_dcl_mods))
		= not (module_index < n_cached_dcl_mods && generic_index < size copied_generic_defs && copied_generic_defs.[generic_index])
			
	check_generic index mod_index gen_defs type_defs class_defs modules heaps cs		

		#(gen_def=:{gen_ident, gen_pos}, gen_defs) = gen_defs ! [index]
		# cs = pushErrorAdmin (newPosition gen_ident gen_pos) cs

		# (gen_def, heaps) = alloc_gen_info gen_def heaps

		# (gen_def, type_defs, class_defs, modules, heaps, cs)
			= check_generic_type gen_def mod_index type_defs class_defs modules heaps cs

		//# (heaps, cs) = check_generic_vars gen_def heaps cs

		# gen_defs = {gen_defs & [index] = gen_def} 
		# (cs=:{cs_x}) = popErrorAdmin cs
		#! cs = { cs & cs_x = {cs_x & x_needed_modules = cs_x.x_needed_modules bitor cNeedStdGeneric}}			
		= (gen_defs, type_defs, class_defs, modules, heaps, cs)
				//---> ("check_generic", gen_ident, gen_def.gen_vars, gen_def.gen_type)

	alloc_gen_info gen_def heaps=:{hp_generic_heap}
		# initial_info = 
			{ gen_classes = createArray 32 []
			, gen_cases = []
			, gen_var_kinds = []
			, gen_star_case = {gi_module=NoIndex, gi_index=NoIndex}
			}
		# (gen_info_ptr, hp_generic_heap) = newPtr initial_info hp_generic_heap 
		= (	{gen_def & gen_info_ptr = gen_info_ptr}, 
			{heaps & hp_generic_heap = hp_generic_heap})

	check_generic_vars {gen_vars,gen_type} heaps=:{hp_type_heaps=hp_type_heaps=:{th_vars}} cs	
		#! types = [gen_type.st_result:gen_type.st_args]
		#! th_vars = performOnTypeVars mark_var types th_vars
		#! (th_vars,cs) = foldSt check_var_marked gen_vars (th_vars,cs)
		#! th_vars = performOnTypeVars initializeToTVI_Empty types th_vars
		= ({heaps & hp_type_heaps={hp_type_heaps&th_vars=th_vars}}, cs)
	where
		mark_var _ {tv_ident,tv_info_ptr} th_vars
			= writePtr tv_info_ptr TVI_Used th_vars
		check_var_marked {tv_ident,tv_info_ptr} (th_vars,cs=:{cs_error})
			#! (tv_info, th_vars) = readPtr tv_info_ptr th_vars
			#! cs_error = case tv_info of  
				TVI_Empty -> checkError tv_ident "generic variable not used" cs_error
				TVI_Used -> cs_error
			= (th_vars, {cs & cs_error = cs_error})	

	check_generic_type gen_def=:{gen_type, gen_vars, gen_ident, gen_pos} module_index type_defs class_defs modules heaps=:{hp_type_heaps} cs

		#! (checked_gen_type, _, type_defs, class_defs, modules, hp_type_heaps, cs) =
			checkFunctionType module_index gen_type SP_None type_defs class_defs modules hp_type_heaps cs
		
		#! (checked_gen_vars, cs) = check_generic_vars gen_vars checked_gen_type.st_vars cs		
		#! checked_gen_type = { checked_gen_type & st_vars = move_gen_vars checked_gen_vars checked_gen_type.st_vars}
				
		#! (hp_type_heaps, cs) = check_no_generic_vars_in_contexts checked_gen_type checked_gen_vars hp_type_heaps cs
		= 	( {gen_def & gen_type = checked_gen_type, gen_vars = checked_gen_vars}
			, type_defs
			, class_defs
			, modules
			, {heaps & hp_type_heaps = hp_type_heaps}
			, cs
			)
			//---> ("check_genric_type", gen_vars, checked_gen_vars, checked_gen_type)
	where
		check_generic_vars gen_vars st_vars cs=:{cs_error}
			# (gen_vars, _, cs_error) = foldSt check_generic_var gen_vars ([], st_vars, cs_error)
			= (reverse gen_vars, {cs & cs_error = cs_error})
	
		// make sure generic variables are first
		move_gen_vars gen_vars st_vars
			= gen_vars ++ (removeMembers st_vars gen_vars)
				
		check_generic_var gv (acc_gvs, [], error)
			= (acc_gvs, [], checkError gv.tv_ident "generic variable not used" error) 
		check_generic_var gv (acc_gvs, [tv:tvs], error)
			| gv.tv_ident.id_name == tv.tv_ident.id_name
				= ([tv:acc_gvs], tvs, error)
				# (acc_gvs, tvs, error) = check_generic_var gv (acc_gvs, tvs, error)
				= (acc_gvs, [tv:tvs], error)
									
	// returns reversed variable list		
	add_vars_to_symbol_table gen_vars type_heaps=:{th_vars} cs=:{cs_error, cs_symbol_table}
		#! (rev_gen_vars,cs_symbol_table,th_vars, cs_error) 
			= foldSt add_var_to_symbol_table gen_vars ([],cs.cs_symbol_table,th_vars, cs_error)
		= (	rev_gen_vars,
			{type_heaps & th_vars = th_vars}, 
			{cs & cs_error = cs_error, cs_symbol_table = cs_symbol_table})			
	
	add_var_to_symbol_table :: !TypeVar !(![TypeVar], !*SymbolTable, !*TypeVarHeap, !*ErrorAdmin)
		-> (![TypeVar],!*SymbolTable,!*TypeVarHeap,!*ErrorAdmin)
	add_var_to_symbol_table tv=:{tv_ident={id_name,id_info}} (rev_class_args, symbol_table, th_vars, error)
	  	#! (entry, symbol_table) = readPtr id_info symbol_table
		| entry.ste_kind == STE_Empty || entry.ste_def_level < cGlobalScope
			# (new_var_ptr, th_vars) = newPtr TVI_Empty th_vars
			# symbol_table = NewEntry symbol_table id_info (STE_TypeVariable new_var_ptr) NoIndex cGlobalScope entry
			= ([{ tv & tv_info_ptr = new_var_ptr} : rev_class_args], symbol_table, th_vars, error)
			= (rev_class_args, symbol_table, th_vars, checkError id_name "generic variable already defined" error)
	
	// also reverses variable list (but does not make coffe)
	remove_vars_from_symbol_table rev_gen_vars cs=:{cs_symbol_table}
		#! (gen_vars, cs_symbol_table) = foldSt remove_var_from_symbol_table rev_gen_vars ([], cs_symbol_table)
		= (gen_vars, { cs & cs_symbol_table = cs_symbol_table})
	remove_var_from_symbol_table tv=:{tv_ident={id_name,id_info}} (gen_vars, symbol_table)
	  	#! (entry, symbol_table) = readPtr id_info symbol_table
		#! symbol_table = writePtr id_info entry.ste_previous symbol_table
		=([tv:gen_vars], symbol_table)

	check_no_generic_vars_in_contexts :: !SymbolType ![TypeVar] !*TypeHeaps !*CheckState -> (!*TypeHeaps, !*CheckState)
	check_no_generic_vars_in_contexts gen_type gen_vars th=:{th_vars} cs=:{cs_error}
		#! th_vars = clear_type_vars gen_type.st_vars th_vars
		#! th_vars = mark_type_vars_used gen_vars th_vars
		#! (th_vars, cs_error) = check_type_vars_not_used gen_type.st_context th_vars cs_error
		#! th_vars = clear_type_vars gen_type.st_vars th_vars
	
		= ({th & th_vars = th_vars}, {cs & cs_error = cs_error})
	where
		mark_type_vars_used gen_vars th_vars
			= foldSt (write_type_var_info TVI_Used) gen_vars th_vars
		clear_type_vars gen_vars th_vars
			= foldSt (write_type_var_info TVI_Empty) gen_vars th_vars
		write_type_var_info tvi {tv_ident, tv_info_ptr} th_vars 
			= writePtr tv_info_ptr tvi th_vars
		
		check_type_vars_not_used :: ![TypeContext] !*TypeVarHeap !*ErrorAdmin -> (!*TypeVarHeap, !*ErrorAdmin) 
		check_type_vars_not_used contexts th_vars cs_error
			# types	= flatten [tc_types \\ {tc_types} <- contexts]		
			# atypes = [{at_type=t,at_attribute=TA_None} \\ t <- types]
			= performOnTypeVars check_type_var_not_used atypes (th_vars, cs_error)
		check_type_var_not_used attr tv=:{tv_ident, tv_info_ptr} (th_vars, cs_error)
			#! (tv_info, th_vars) = readPtr tv_info_ptr th_vars
			= case tv_info of
				TVI_Empty  
					-> (th_vars, cs_error)
				TVI_Used
					#! cs_error = checkError tv_ident "context restrictions on generic variables are not allowed" cs_error 
					-> (th_vars, cs_error)
				_	-> abort ("check_no_generic_vars_in_contexts: wrong TVI" ---> (tv, tv_info))	
						
checkGenericCaseDefs :: !Index !*{#GenericCaseDef} !*{#GenericDef} !u:{#CheckedTypeDef} !*{#DclModule} !*Heaps !*CheckState
	-> (!*{#GenericCaseDef}, !*{#GenericDef}, !u:{#CheckedTypeDef}, !*{#DclModule},!.Heaps,!.CheckState)
checkGenericCaseDefs mod_index gen_case_defs generic_defs type_defs modules heaps cs
	= check_instances 0 mod_index gen_case_defs generic_defs type_defs modules heaps cs
where
	check_instances index mod_index gen_case_defs generic_defs type_defs modules heaps cs
		# (n_gc, gen_inst_defs) = usize gen_case_defs
		| index == n_gc  
			= (gen_case_defs, generic_defs, type_defs, modules, heaps, cs)	
			# (gen_case_defs, generic_defs, type_defs, modules, heaps, cs) 
				= check_instance index mod_index gen_case_defs generic_defs type_defs modules heaps cs
			= check_instances (inc index)  mod_index gen_case_defs generic_defs type_defs modules heaps cs			

	check_instance index mod_index gen_case_defs generic_defs type_defs modules heaps cs

		#! (case_def=:{gc_ident,gc_gident,gc_pos,gc_type}, gen_case_defs) = gen_case_defs ! [index]

		#! cs = pushErrorAdmin (newPosition gc_ident gc_pos) cs

		#! (gc_type, gc_type_cons, type_defs, modules, heaps, cs)
		 	= check_instance_type mod_index gc_type type_defs modules heaps cs 

		#! (generic_gi, cs) = get_generic_index gc_gident mod_index cs 
		| not cs.cs_error.ea_ok
			# cs = popErrorAdmin cs
			= (gen_case_defs, generic_defs, type_defs, modules, heaps, cs)
				 
		#! case_def = 
			{ case_def 
			& gc_generic = generic_gi
			, gc_type = gc_type
			, gc_type_cons = gc_type_cons
			}
		#! gen_case_defs = { gen_case_defs & [index] = case_def }
				
		#! (generic_def, generic_defs, modules) = get_generic_def generic_gi mod_index generic_defs modules
		#! gindex = {gi_module=mod_index,gi_index=index}
		#! heaps = add_case_to_generic generic_def gindex heaps 		
	
		#! (heaps, cs) = check_star_case gc_type_cons generic_def gindex heaps cs 
			
		#! (cs=:{cs_x}) = popErrorAdmin cs	
		#! cs = { cs & cs_x = {cs_x & x_needed_modules = cs_x.x_needed_modules bitor cNeedStdGeneric}}			
		= (gen_case_defs, generic_defs, type_defs, modules, heaps, cs)
			//---> ("check_generic_case", gc_ident, gc_type_cons)

	check_instance_type module_index (TA type_cons []) type_defs modules heaps=:{hp_type_heaps} cs 

		# (entry, cs_symbol_table) = readPtr type_cons.type_ident.id_info cs.cs_symbol_table
		# cs = {cs & cs_symbol_table = cs_symbol_table}
	  	# (type_index, type_module) = retrieveGlobalDefinition entry STE_Type module_index
		| type_index == NotFound
			# cs_error = checkError type_cons.type_ident "generic argument type undefined" cs.cs_error
 			= (TA type_cons [], TypeConsSymb type_cons, type_defs, modules,{heaps&hp_type_heaps = hp_type_heaps}, {cs&cs_error=cs_error})
		# (type_def, type_defs, modules) 
			= getTypeDef module_index {glob_module=type_module, glob_object=type_index} type_defs modules		
		# type_cons = { type_cons & type_index = { glob_object = type_index, glob_module = type_module }}
		= (TA type_cons [], TypeConsSymb type_cons, type_defs, modules,{heaps&hp_type_heaps = hp_type_heaps}, cs)
	check_instance_type module_index (TB b) type_defs modules heaps cs
		= (TB b, TypeConsBasic b, type_defs, modules,heaps, cs) 
	check_instance_type module_index TArrow type_defs modules heaps cs
		= (TArrow, TypeConsArrow, type_defs, modules, heaps , cs) 		
// General instance ..
	check_instance_type module_index (TV tv) type_defs modules heaps=:{hp_type_heaps} cs
		# (tv_info_ptr, th_vars) = newPtr TVI_Empty hp_type_heaps.th_vars
		# tv = {tv & tv_info_ptr = tv_info_ptr}		
		= 	( TV tv, TypeConsVar tv, type_defs, modules
			, {heaps& hp_type_heaps = {hp_type_heaps & th_vars = th_vars}}, cs) 
	
// .. General instance
	check_instance_type module_index ins_type type_defs modules heaps cs=:{cs_error}
		# cs_error = checkError {id_name="<>",id_info=nilPtr} "invalid generic type argument" cs_error
		= (ins_type, TypeConsArrow, type_defs, modules, heaps, {cs & cs_error=cs_error})

	get_generic_index :: !Ident !Index !*CheckState -> (!GlobalIndex, !*CheckState)
	get_generic_index {id_name,id_info} mod_index cs=:{cs_symbol_table}
 		# (ste, cs_symbol_table) = readPtr id_info cs_symbol_table
 		# cs = {cs & cs_symbol_table = cs_symbol_table}
 		= case ste.ste_kind of
			STE_Generic
				-> ({gi_module=mod_index,gi_index = ste.ste_index}, cs) 
			STE_Imported STE_Generic imported_generic_module
				-> ({gi_module=imported_generic_module,gi_index = ste.ste_index}, cs)
			_	->	//abort "--------------" ---> ("STE_Kind", ste.ste_kind)			
					( {gi_module=NoIndex,gi_index = NoIndex}
					, {cs & cs_error = checkError id_name "generic undefined" cs.cs_error})

	get_generic_def :: !GlobalIndex !Int !u:{#GenericDef} !v:{#DclModule} -> (!GenericDef,!u:{#GenericDef},!v:{#DclModule})
	get_generic_def {gi_module, gi_index} mod_index generic_defs modules
		| gi_module == mod_index
			# (generic_def, generic_defs) = generic_defs![gi_index]
			= (generic_def, generic_defs, modules)
			# (dcl_mod, modules) = modules![gi_module]
			= (dcl_mod.dcl_common.com_generic_defs.[gi_index], generic_defs, modules)

	add_case_to_generic :: !GenericDef !GlobalIndex !*Heaps -> *Heaps
	add_case_to_generic {gen_info_ptr} index heaps=:{hp_generic_heap} 
		# (info=:{gen_cases}, hp_generic_heap) = readPtr gen_info_ptr hp_generic_heap
		# info = { info & gen_cases = [index:gen_cases]}
		= { heaps & hp_generic_heap = writePtr gen_info_ptr info hp_generic_heap} 
								
	check_star_case :: !TypeCons !GenericDef !GlobalIndex !*Heaps !*CheckState -> (!*Heaps, !*CheckState)
	check_star_case (TypeConsVar _) {gen_ident, gen_info_ptr} index heaps=:{hp_generic_heap} cs=:{cs_error} 
		# (info=:{gen_star_case}, hp_generic_heap) = readPtr gen_info_ptr hp_generic_heap
		| gen_star_case.gi_module <> NoIndex
			# cs_error = checkError gen_ident "general kind-* case is already defined" cs_error 
			= ({ heaps & hp_generic_heap = hp_generic_heap}, {cs & cs_error = cs_error})   
			# info = { info & gen_star_case = index }
			# hp_generic_heap = writePtr gen_info_ptr info hp_generic_heap	
			= ({ heaps & hp_generic_heap = hp_generic_heap}, {cs & cs_error = cs_error}) 
	check_star_case _ _ _ heaps cs 
		= (heaps, cs)
				
								
// ... AA: new implementation of generics

				
checkTypeClasses :: !Index !(Optional (CopiedDefinitions, Int)) !*{#ClassDef} !*{#MemberDef} !*{#CheckedTypeDef} !*{#DclModule} !*Heaps !*CheckState
	-> (!*{#ClassDef}, !*{#MemberDef}, !*{#CheckedTypeDef}, !*{#DclModule}, !*Heaps, !*CheckState)
checkTypeClasses module_index opt_icl_info class_defs member_defs type_defs modules heaps=:{hp_type_heaps} cs
	#! n_classes = size class_defs
	# (class_defs,member_defs,type_defs,modules,hp_type_heaps,cs) 
		= iFoldSt (check_type_class module_index opt_icl_info) 0 n_classes (class_defs, member_defs, type_defs, modules, hp_type_heaps, cs)
	= (class_defs,member_defs,type_defs,modules,{heaps & hp_type_heaps = hp_type_heaps},cs)
where
	check_type_class module_index opt_icl_info class_index (class_defs, member_defs, type_defs, modules, type_heaps, cs=:{cs_symbol_table,cs_error})
		| has_to_be_checked module_index opt_icl_info class_index
			# (class_def=:{class_ident,class_pos,class_args,class_context,class_members}, class_defs) = class_defs![class_index]
			  cs = {cs & cs_error = setErrorAdmin (newPosition class_ident class_pos) cs_error }
			  (class_args, class_context, type_defs, class_defs, modules, type_heaps, cs)
			  		= checkSuperClasses class_args class_context module_index type_defs class_defs modules type_heaps cs
			  class_defs = { class_defs & [class_index] = { class_def & class_context = class_context, class_args = class_args }}
			  member_defs = set_classes_in_member_defs 0 class_members {glob_object = class_index, glob_module = module_index} member_defs 
			= (class_defs, member_defs, type_defs, modules, type_heaps, cs)
			= (class_defs, member_defs, type_defs, modules, type_heaps, cs)

	has_to_be_checked module_index No class_index
		= True
	has_to_be_checked module_index (Yes ({copied_class_defs}, n_cached_dcl_mods)) class_index
		= not (module_index < n_cached_dcl_mods && class_index < size copied_class_defs && copied_class_defs.[class_index])

	set_classes_in_member_defs mem_offset class_members glob_class_index member_defs
		| mem_offset == size class_members
			= member_defs
			# {ds_index} = class_members.[mem_offset]
			# (member_def, member_defs) = member_defs![ds_index]
			= set_classes_in_member_defs (inc mem_offset) class_members glob_class_index { member_defs & [ds_index] = { member_def & me_class = glob_class_index }}

checkSpecial :: !Index !FunType !Index !SpecialSubstitution !(!Index, ![FunType], !*Heaps,!*PredefinedSymbols,!*ErrorAdmin)
	-> (!Special, !(!Index, ![FunType], !*Heaps,!*PredefinedSymbols, !*ErrorAdmin))
checkSpecial mod_index fun_type=:{ft_type} fun_index subst (next_inst_index, special_types, heaps, predef_symbols,error)
	# (special_type, hp_type_heaps, error) = substitute_type ft_type subst heaps.hp_type_heaps error
	  (spec_types, predef_symbols, error) = checkAndCollectTypesOfContextsOfSpecials special_type.st_context predef_symbols error
	  ft_type = { special_type & st_context = [] }
	  (new_info_ptr, hp_var_heap) = newPtr VI_Empty heaps.hp_var_heap
	= ( { spec_index = { glob_module = mod_index, glob_object = next_inst_index }, spec_types = spec_types, spec_vars = subst.ss_vars, spec_attrs = subst.ss_attrs },
			((inc next_inst_index), [{ fun_type & ft_type = ft_type, ft_specials = SP_FunIndex fun_index, ft_type_ptr = new_info_ptr} : special_types ],
					{ heaps & hp_type_heaps = hp_type_heaps, hp_var_heap = hp_var_heap }, predef_symbols, error))
where	
	substitute_type st=:{st_vars,st_attr_vars,st_args,st_result,st_context,st_attr_env} environment type_heaps error
		# (st_vars, st_attr_vars, [st_result : st_args], st_context, st_attr_env, _, type_heaps, error)
			= instantiateTypes st_vars st_attr_vars [ st_result : st_args ] st_context st_attr_env environment [] type_heaps error
		= ({st & st_vars = st_vars, st_args = st_args, st_result = st_result, st_attr_vars = st_attr_vars,
			st_context = st_context, st_attr_env = st_attr_env }, type_heaps, error)

checkDclFunctions :: !Index !Index ![FunType] !v:{#CheckedTypeDef} !x:{#ClassDef} !v:{#.DclModule} !*Heaps !*CheckState
	-> (!Index, ![FunType], ![FunType], !v:{#CheckedTypeDef}, !x:{#ClassDef}, !v:{#DclModule}, !*Heaps, !*CheckState)
checkDclFunctions module_index first_inst_index fun_types type_defs class_defs modules heaps cs
	= check_dcl_functions module_index fun_types 0 first_inst_index [] [] type_defs class_defs modules heaps cs
where
	check_dcl_functions ::  !Index ![FunType]   !Index  !Index ![FunType] ![FunType] !v:{#CheckedTypeDef} !x:{#ClassDef} !v:{#DclModule} !*Heaps !*CheckState
		 -> (!Index, ![FunType], ![FunType],!v:{#CheckedTypeDef}, !x:{#ClassDef}, !v:{#DclModule}, !*Heaps, !*CheckState)
	check_dcl_functions module_index [] fun_index next_inst_index collected_funtypes collected_instances type_defs class_defs modules heaps cs
		= (next_inst_index, collected_funtypes, collected_instances, type_defs, class_defs, modules, heaps, cs)
	check_dcl_functions module_index [fun_type=:{ft_ident,ft_type,ft_pos,ft_specials} : fun_types] fun_index
			next_inst_index collected_funtypes collected_instances type_defs class_defs modules heaps cs
		# position = newPosition ft_ident ft_pos
		  cs = { cs & cs_error = setErrorAdmin position cs.cs_error }
		  (ft_type, ft_specials, type_defs,  class_defs, modules, hp_type_heaps, cs)
		  		= checkFunctionType module_index ft_type ft_specials type_defs class_defs modules heaps.hp_type_heaps cs
		  (spec_types, next_inst_index, collected_instances, heaps, cs_predef_symbols,cs_error)
		  		= check_specials module_index { fun_type & ft_type = ft_type } fun_index ft_specials next_inst_index collected_instances
		  				{ heaps & hp_type_heaps = hp_type_heaps } cs.cs_predef_symbols cs.cs_error
		  (new_info_ptr, hp_var_heap) = newPtr VI_Empty heaps.hp_var_heap
		= check_dcl_functions module_index fun_types (inc fun_index) next_inst_index [
				{ fun_type & ft_type = ft_type, ft_specials = spec_types, ft_type_ptr = new_info_ptr } : collected_funtypes]
					collected_instances type_defs class_defs modules { heaps & hp_var_heap = hp_var_heap } { cs & cs_predef_symbols=cs_predef_symbols,cs_error = cs_error }

	check_specials :: !Index !FunType !Index !Specials !Index ![FunType] !*Heaps !*PredefinedSymbols !*ErrorAdmin
		-> (!Specials, !Index, ![FunType], !*Heaps, !*PredefinedSymbols, !*ErrorAdmin)
	check_specials mod_index fun_type fun_index (SP_Substitutions substs) next_inst_index all_instances heaps predef_symbols error
		# (list_of_specials, (next_inst_index, all_instances, heaps, cs_predef_symbols,cs_error))
				= mapSt (checkSpecial mod_index fun_type fun_index) substs (next_inst_index, all_instances, heaps, predef_symbols,error)
		= (SP_ContextTypes list_of_specials, next_inst_index, all_instances, heaps, cs_predef_symbols,cs_error)
	check_specials mod_index fun_type fun_index SP_None next_inst_index all_instances heaps predef_symbols error
		= (SP_None, next_inst_index, all_instances, heaps, predef_symbols,error)

checkSpecialsOfInstances :: !Index !Index ![ClassInstance] !Index ![ClassInstance] ![FunType] {# FunType} *{! [Special] } !*Heaps !*PredefinedSymbols !*ErrorAdmin
		-> (!Index, ![ClassInstance], ![FunType], !*{! [Special]}, !*Heaps, !*PredefinedSymbols,!*ErrorAdmin)
checkSpecialsOfInstances mod_index first_mem_index [class_inst=:{ins_members,ins_specials} : class_insts] next_inst_index all_class_instances all_specials
		new_inst_defs all_spec_types heaps predef_symbols error
	= case ins_specials of
		SP_TypeOffset type_offset
			# (next_inst_index, rev_mem_specials, all_specials, all_spec_types, heaps,predef_symbols, error)
				= check_and_build_members mod_index first_mem_index 0 ins_members type_offset next_inst_index [] all_specials new_inst_defs all_spec_types heaps predef_symbols error
			  class_inst = { class_inst & ins_members = { mem \\ mem <- reverse rev_mem_specials } }
			-> checkSpecialsOfInstances mod_index first_mem_index class_insts next_inst_index [class_inst : all_class_instances]
					all_specials new_inst_defs all_spec_types heaps predef_symbols error
		SP_None
			-> checkSpecialsOfInstances mod_index first_mem_index class_insts next_inst_index [class_inst : all_class_instances]
					all_specials new_inst_defs all_spec_types heaps predef_symbols error
where
	check_and_build_members :: !Index !Index !Int {# DefinedSymbol} !Int !Index ![DefinedSymbol] ![FunType] !{#FunType} !*{! [Special]} !*Heaps !*PredefinedSymbols !*ErrorAdmin
		-> (!Index, ![DefinedSymbol], ![FunType], !*{! [Special]}, !*Heaps, !*PredefinedSymbols,!*ErrorAdmin)
	check_and_build_members mod_index first_mem_index member_offset ins_members type_offset next_inst_index rev_mem_specials all_specials inst_spec_defs
			all_spec_types heaps predef_symbols error
		| member_offset < size ins_members
			# member = ins_members.[member_offset]
			  member_index = member.ds_index
			  spec_member_index = member_index - first_mem_index
		 	# (spec_types, all_spec_types) = all_spec_types![spec_member_index]
		 	# mem_inst = inst_spec_defs.[spec_member_index]
		 	  (SP_Substitutions specials) = mem_inst.ft_specials
		 	  env = specials !! type_offset
			  member = { member & ds_index = next_inst_index }
			  (spec_type, (next_inst_index, all_specials, heaps, predef_symbols,error))
			  		= checkSpecial mod_index mem_inst member_index env (next_inst_index, all_specials, heaps, predef_symbols,error)
			  all_spec_types = { all_spec_types & [spec_member_index] = [ spec_type : spec_types] }
			= check_and_build_members mod_index first_mem_index (inc member_offset) ins_members type_offset next_inst_index [ member : rev_mem_specials ]
					all_specials inst_spec_defs all_spec_types heaps predef_symbols error
			= (next_inst_index, rev_mem_specials, all_specials, all_spec_types, heaps, predef_symbols,error)
checkSpecialsOfInstances mod_index first_mem_index [] next_inst_index all_class_instances all_specials inst_spec_defs all_spec_types heaps predef_symbols error
	= (next_inst_index, all_class_instances, all_specials, all_spec_types, heaps, predef_symbols,error)

checkMemberTypes :: !Index !(Optional (CopiedDefinitions, Int)) !*{#MemberDef} !*{#CheckedTypeDef} !*{#ClassDef} !*{#DclModule} !*Heaps !*CheckState
	-> (!*{#MemberDef}, !*{#CheckedTypeDef}, !*{#ClassDef}, !*{#DclModule}, !*Heaps, !*CheckState)
checkMemberTypes module_index opt_icl_info member_defs type_defs class_defs modules heaps=:{hp_type_heaps,hp_var_heap} cs
	#! nr_of_members = size member_defs
	# (mds,tds,cds,modules,hp_type_heaps,hp_var_heap,cs) 
		= iFoldSt (check_class_member module_index opt_icl_info) 0 nr_of_members (member_defs, type_defs, class_defs, modules, hp_type_heaps, hp_var_heap, cs)
	= (mds,tds,cds,modules,{heaps & hp_type_heaps = hp_type_heaps,hp_var_heap = hp_var_heap},cs) 
where
	check_class_member module_index opt_icl_info member_index (member_defs, type_defs, class_defs, modules, type_heaps, var_heap, cs)
		# (member_def=:{me_ident,me_type,me_pos,me_class}, member_defs) = member_defs![member_index]
		| has_to_be_checked opt_icl_info me_class
			# position = newPosition me_ident me_pos
			  cs = { cs & cs_error = setErrorAdmin position cs.cs_error }
			  (me_type, type_defs, class_defs, modules, type_heaps, cs)
			   		= checkMemberType module_index me_type type_defs class_defs modules type_heaps cs
			  me_class_vars = [ type_var \\ (TV type_var) <- (hd me_type.st_context).tc_types ]
			  (me_type_ptr, var_heap) = newPtr VI_Empty var_heap		   
			= ({ member_defs & [member_index] = { member_def & me_type = me_type, me_class_vars = me_class_vars, me_type_ptr = me_type_ptr }},
					type_defs, class_defs, modules, type_heaps, var_heap, cs)
			= (member_defs, type_defs, class_defs, modules, type_heaps, var_heap, cs)

	has_to_be_checked No glob_class_index
		= True
	has_to_be_checked (Yes ({copied_class_defs}, n_cached_dcl_mods)) {glob_module,glob_object}
		= not (glob_module < n_cached_dcl_mods && glob_object < size copied_class_defs && copied_class_defs.[glob_object])

::	InstanceSymbols =
	{	is_type_defs		:: !.{# CheckedTypeDef}
	,	is_class_defs		:: !.{# ClassDef}
	,	is_member_defs		:: !.{# MemberDef}
	,	is_modules			:: !.{# DclModule}
	}

// AA..
checkInstanceDefs :: !Index !*{#ClassInstance} !u:{#CheckedTypeDef} !u:{#ClassDef} !u:{#MemberDef} !u:{#DclModule} !*Heaps !*CheckState
	-> (!.{#ClassInstance},!u:{#CheckedTypeDef},!u:{#ClassDef},!u:{#MemberDef}, !u:{#DclModule},!.Heaps,!.CheckState)
checkInstanceDefs mod_index instance_defs type_defs class_defs member_defs modules heaps=:{hp_type_heaps} cs
	# is = { is_type_defs = type_defs, is_class_defs = class_defs, is_member_defs = member_defs, is_modules = modules }
	  (instance_defs, is, hp_type_heaps, cs) = check_instance_defs 0 mod_index instance_defs is hp_type_heaps cs
	= (instance_defs, is.is_type_defs, is.is_class_defs, is.is_member_defs, is.is_modules, {heaps & hp_type_heaps = hp_type_heaps}, cs)
where
	check_instance_defs :: !Index !Index !*{# ClassInstance} !u:InstanceSymbols !*TypeHeaps !*CheckState
		-> (!*{# ClassInstance},!u:InstanceSymbols,!*TypeHeaps,!*CheckState)
	check_instance_defs inst_index mod_index instance_defs is type_heaps cs
		| inst_index < size instance_defs
			# (instance_def, instance_defs) = instance_defs![inst_index]
			  (instance_def, is, type_heaps, cs) = check_instance mod_index instance_def is type_heaps cs
			= check_instance_defs (inc inst_index) mod_index { instance_defs & [inst_index] = instance_def } is type_heaps cs
			= (instance_defs, is, type_heaps, cs)

	check_instance :: !Index !ClassInstance !u:InstanceSymbols !*TypeHeaps !*CheckState -> (!ClassInstance, !u:InstanceSymbols, !*TypeHeaps, !*CheckState)
	check_instance module_index
			ins=:{ins_members,ins_class={glob_object = class_ident =: {ds_ident = {id_name,id_info},ds_arity}},ins_type,ins_specials,ins_pos,ins_ident}
			is=:{is_class_defs,is_modules} type_heaps cs=:{cs_symbol_table}
		#  	(entry, cs_symbol_table) = readPtr id_info cs_symbol_table
		# 	cs = pushErrorAdmin (newPosition ins_ident ins_pos) { cs & cs_symbol_table = cs_symbol_table }
		#   (ins, is, type_heaps, cs) = case entry.ste_kind of
				STE_Class				
					# (class_def, is) = class_by_index entry.ste_index is
					-> check_class_instance	class_def module_index entry.ste_index module_index ins is type_heaps cs 
				STE_Imported STE_Class decl_index	
					# (class_def, is) = class_by_module_index decl_index entry.ste_index is
					-> check_class_instance class_def module_index entry.ste_index decl_index ins is type_heaps cs
				ste -> (ins, is, type_heaps, { cs & cs_error = checkError id_name "class undefined" cs.cs_error })
		= (ins, is, type_heaps, popErrorAdmin cs)

	where
			class_by_index class_index is=:{is_class_defs}
				#	(class_def, is_class_defs) = is_class_defs![class_index]
 				= (class_def, {is & is_class_defs = is_class_defs})
			class_by_module_index decl_index class_index is=:{is_modules}
 				# 	(dcl_mod, is_modules) = is_modules![decl_index]
					class_def = dcl_mod.dcl_common.com_class_defs.[class_index]
				= (class_def, {is & is_modules = is_modules })

	check_class_instance :: ClassDef !Index !Index !Index !ClassInstance !u:InstanceSymbols !*TypeHeaps !*CheckState 
		-> (!ClassInstance, !u:InstanceSymbols, !*TypeHeaps, !*CheckState)
	check_class_instance class_def module_index class_index class_mod_index
			ins=:{ins_members,ins_class={glob_object = class_ident =: {ds_ident = {id_name,id_info},ds_arity}},ins_type,ins_specials,ins_pos,ins_ident}
			is=:{is_class_defs,is_modules} type_heaps cs=:{cs_symbol_table}	
		| class_def.class_arity == ds_arity
			# ins_class = { glob_object = { class_ident & ds_index = class_index }, glob_module = class_mod_index}
			  (ins_type, ins_specials, is_type_defs, is_class_defs, is_modules, type_heaps, cs)
			  		= checkInstanceType module_index ins_class ins_type ins_specials
							is.is_type_defs is.is_class_defs is.is_modules type_heaps cs
			  is = { is & is_type_defs = is_type_defs, is_class_defs = is_class_defs, is_modules = is_modules }
			= ({ins & ins_class = ins_class, ins_type = ins_type, ins_specials = ins_specials}, is, type_heaps, cs)
		// otherwise
			= ( ins, is, type_heaps
			  , { cs & cs_error = checkError id_name ("wrong arity: expected "+++toString class_def.class_arity+++" found "+++toString ds_arity) cs.cs_error }
			  )

checkInstances :: !Index !*CommonDefs !u:{# DclModule} !*VarHeap !*TypeHeaps !*CheckState
	-> (![(Index,SymbolType)], !*CommonDefs, !u:{# DclModule}, !*VarHeap , !*TypeHeaps, !*CheckState)
checkInstances mod_index icl_common=:{com_instance_defs,com_class_defs,com_member_defs,com_generic_defs,com_type_defs} modules var_heap type_heaps cs=:{cs_error}
	| cs_error.ea_ok
		# (instance_types, com_instance_defs, com_class_defs, com_member_defs, com_generic_defs, com_type_defs, modules, var_heap, type_heaps, cs)
				= check_instances 0 mod_index [] com_instance_defs com_class_defs com_member_defs /*AA*/com_generic_defs com_type_defs modules var_heap type_heaps cs
		= (instance_types, { icl_common & com_instance_defs = com_instance_defs,com_class_defs = com_class_defs,com_member_defs = com_member_defs, /*AA*/com_generic_defs = com_generic_defs, com_type_defs = com_type_defs },
			 	modules, var_heap, type_heaps, cs)
		= ([], icl_common, modules, var_heap, type_heaps, cs)
where
	check_instances :: !Index !Index ![(Index,SymbolType)] !x:{# ClassInstance} !w:{# ClassDef} !v:{# MemberDef} /*AA*/!w:{# GenericDef} !nerd:{# CheckedTypeDef} !u:{# DclModule}
		!*VarHeap !*TypeHeaps !*CheckState
			-> (![(Index,SymbolType)], !x:{# ClassInstance}, !w:{# ClassDef}, !v:{# MemberDef}, /*AA*/!w:{# GenericDef}, !nerd:{# CheckedTypeDef}, !u:{# DclModule}, !*VarHeap, !*TypeHeaps, !*CheckState)
	check_instances inst_index mod_index instance_types instance_defs class_defs member_defs generic_defs type_defs modules var_heap type_heaps cs
		| inst_index < size instance_defs
			# (instance_def=:{ins_ident, ins_pos}, instance_defs) = instance_defs![inst_index]
			# (instance_types, class_defs, member_defs, generic_defs, type_defs, modules, var_heap, type_heaps, cs) =
					check_class_instance instance_def mod_index instance_types class_defs member_defs generic_defs type_defs modules var_heap type_heaps cs				 
			= check_instances (inc inst_index) mod_index instance_types instance_defs class_defs member_defs generic_defs type_defs modules var_heap type_heaps cs 
		// otherwise
			= (instance_types, instance_defs, class_defs, member_defs, generic_defs, type_defs, modules, var_heap, type_heaps, cs)

	check_class_instance {ins_pos,ins_class,ins_members,ins_type} mod_index instance_types class_defs member_defs generic_defs type_defs modules var_heap type_heaps cs
			# ({class_members,class_ident}, class_defs, modules) = getClassDef ins_class mod_index class_defs modules
			  class_size = size class_members
			| class_size == size ins_members
				# (instance_types, member_defs, type_defs, modules, var_heap, type_heaps, cs) 
						= check_member_instances mod_index ins_class.glob_module
			  	        	 0 class_size ins_members class_members class_ident ins_pos ins_type instance_types member_defs type_defs modules var_heap type_heaps cs
				= (instance_types, class_defs, member_defs, generic_defs, type_defs, modules, var_heap, type_heaps, cs)
			// otherwise
				# cs = { cs & cs_error = checkErrorWithIdentPos (newPosition class_ident ins_pos) "different number of members specified" cs.cs_error }
				= (instance_types, class_defs, member_defs, generic_defs, type_defs, modules, var_heap, type_heaps, cs)

/*
	check_generic_instance {ins_class, ins_members, ins_generate} mod_index instance_types class_defs member_defs generic_defs type_defs modules var_heap type_heaps cs
			# ({gen_ident, gen_member_ident}, generic_defs, modules) = getGenericDef ins_class mod_index generic_defs modules		
			//| ins_generate 
			//	= (instance_types, class_defs, member_defs, generic_defs, type_defs, modules, var_heap, type_heaps, cs)
			| size ins_members <> 1 				
				# cs = { cs & cs_error = checkError gen_ident "generic instance must have one member" cs.cs_error }
				= (instance_types, class_defs, member_defs, generic_defs, type_defs, modules, var_heap, type_heaps, cs)
			# member_name = ins_members.[0].ds_ident
			| member_name <> gen_member_ident
				# cs = { cs & cs_error = checkError member_name "wrong member name" cs.cs_error }
				= (instance_types, class_defs, member_defs, generic_defs, type_defs, modules, var_heap, type_heaps, cs)				
			// otherwise
				= (instance_types, class_defs, member_defs, generic_defs, type_defs, modules, var_heap, type_heaps, cs)
*/
	check_member_instances :: !Index !Index !Int !Int !{#DefinedSymbol} !{#DefinedSymbol} Ident !Position !InstanceType ![(Index,SymbolType)]
		!v:{# MemberDef} !blah:{# CheckedTypeDef} !u:{# DclModule} !*VarHeap !*TypeHeaps !*CheckState
			-> (![(Index,SymbolType)], !v:{# MemberDef}, !blah:{# CheckedTypeDef}, !u:{# DclModule},!*VarHeap, !*TypeHeaps, !*CheckState)

	check_member_instances module_index member_mod_index mem_offset class_size ins_members class_members
				class_ident ins_pos ins_type instance_types member_defs type_defs modules var_heap type_heaps cs=:{cs_x={x_main_dcl_module_n}}
		| mem_offset == class_size
			= (instance_types, member_defs, type_defs, modules, var_heap, type_heaps, cs)
			# ins_member = ins_members.[mem_offset]
			  class_member = class_members.[mem_offset]
			  cs = setErrorAdmin (newPosition class_ident ins_pos) cs
			| ins_member.ds_ident <> class_member.ds_ident
				= check_member_instances module_index member_mod_index (inc mem_offset) class_size ins_members class_members class_ident ins_pos ins_type 
						instance_types member_defs type_defs modules var_heap type_heaps
							{ cs & cs_error = checkError class_member.ds_ident "instance of class member expected" cs.cs_error}
			| ins_member.ds_arity <> class_member.ds_arity
				= check_member_instances module_index member_mod_index (inc mem_offset) class_size ins_members class_members class_ident ins_pos ins_type
						instance_types member_defs type_defs modules var_heap type_heaps
							{ cs & cs_error = checkError class_member.ds_ident "used with wrong arity" cs.cs_error}
				# ({me_ident, me_type,me_class_vars,me_pos}, member_defs, modules) = getMemberDef member_mod_index class_member.ds_index module_index member_defs modules
				  (instance_type, _, type_heaps, Yes (modules, type_defs), cs_error)
				  		= determineTypeOfMemberInstance me_type me_class_vars ins_type SP_None type_heaps (Yes (modules, type_defs, x_main_dcl_module_n)) cs.cs_error
				  (st_context, var_heap) = initializeContextVariables instance_type.st_context var_heap
				= check_member_instances module_index member_mod_index (inc mem_offset) class_size ins_members class_members class_ident ins_pos ins_type
						[ (ins_member.ds_index, { instance_type & st_context = st_context }) : instance_types ] member_defs type_defs modules var_heap type_heaps { cs & cs_error = cs_error }


getClassDef :: !(Global DefinedSymbol) !Int !u:{#ClassDef} !v:{#DclModule} -> (!ClassDef,!u:{#ClassDef},!v:{#DclModule})
getClassDef {glob_module, glob_object={ds_ident, ds_index}} mod_index class_defs modules
	| glob_module == mod_index
		# (class_def, class_defs) = class_defs![ds_index]
		= (class_def, class_defs, modules)
		# (dcl_mod, modules) = modules![glob_module]
		= (dcl_mod.dcl_common.com_class_defs.[ds_index], class_defs, modules)
		
getMemberDef :: !Int Int !Int !u:{#MemberDef} !v:{#DclModule} -> (!MemberDef,!u:{#MemberDef},!v:{#DclModule})
getMemberDef mem_mod mem_index mod_index member_defs modules
	| mem_mod == mod_index
		# (member_def,member_defs) = member_defs![mem_index]
		= (member_def, member_defs, modules)
		# (dcl_mod,modules) = modules![mem_mod]
		= (dcl_mod.dcl_common.com_member_defs.[mem_index], member_defs, modules)

getGenericDef :: !(Global DefinedSymbol) !Int !u:{#GenericDef} !v:{#DclModule} -> (!GenericDef,!u:{#GenericDef},!v:{#DclModule})
getGenericDef {glob_module, glob_object={ds_ident, ds_index}} mod_index generic_defs modules
	| glob_module == mod_index
		# (generic_def, generic_defs) = generic_defs![ds_index]
		= (generic_def, generic_defs, modules)
		# (dcl_mod, modules) = modules![glob_module]
		= (dcl_mod.dcl_common.com_generic_defs.[ds_index], generic_defs, modules)

instantiateTypes :: ![TypeVar] ![AttributeVar] ![AType] ![TypeContext] ![AttrInequality] !SpecialSubstitution ![SpecialSubstitution] !*TypeHeaps !*ErrorAdmin
	-> (![TypeVar], ![AttributeVar], ![AType], ![TypeContext], ![AttrInequality], ![SpecialSubstitution], !*TypeHeaps, !*ErrorAdmin)
instantiateTypes old_type_vars old_attr_vars types type_contexts attr_env {ss_environ, ss_vars, ss_attrs, ss_context} special_subst_list type_heaps=:{th_vars, th_attrs} error
	# th_vars = clear_vars old_type_vars th_vars

	  (new_type_vars, th_vars) = foldSt build_var_subst ss_vars ([], th_vars)
	  (new_attr_vars, th_attrs) = foldSt build_attr_var_subst ss_attrs ([], th_attrs)

	  type_heaps = foldSt build_type_subst ss_environ { type_heaps & th_vars = th_vars, th_attrs = th_attrs }
	  (new_ss_context, type_heaps) = substitute ss_context type_heaps

	  (inst_vars, th_vars)			= foldSt determine_free_var old_type_vars (new_type_vars, type_heaps.th_vars) 
	  (inst_attr_vars, th_attrs)	= foldSt build_attr_var_subst old_attr_vars (new_attr_vars, type_heaps.th_attrs)

	  (inst_types, (ok2, type_heaps))	= mapSt substitue_arg_type types (True, { type_heaps & th_vars = th_vars, th_attrs = th_attrs })
//	  (ok2, inst_types, type_heaps)		= substitute types { type_heaps & th_vars = th_vars, th_attrs = th_attrs }
	  (inst_contexts, type_heaps)	= substitute type_contexts type_heaps
	  (inst_attr_env, type_heaps)	= substitute attr_env type_heaps
	  (special_subst_list, th_vars) 	= mapSt adjust_special_subst special_subst_list type_heaps.th_vars
	= (inst_vars, inst_attr_vars, inst_types, new_ss_context ++ inst_contexts, inst_attr_env, special_subst_list, { type_heaps & th_vars = th_vars }, error)
where
	clear_vars type_vars type_var_heap = foldSt (\tv -> writePtr tv.tv_info_ptr TVI_Empty) type_vars type_var_heap
	
	determine_free_var tv=:{tv_info_ptr} (free_vars, type_var_heap)
		# (type_var_info, type_var_heap) = readPtr tv_info_ptr type_var_heap
		= case type_var_info of
			TVI_Empty
				-> build_var_subst tv (free_vars, type_var_heap)
			_
				-> (free_vars, type_var_heap)

	build_type_subst {bind_src,bind_dst} type_heaps
		# (bind_src, type_heaps) = substitute bind_src type_heaps
// RWS ...
/*
	FIXME: this is a patch for the following incorrect function type (in a dcl module)


    f :: a | c a b special
        a=[], b = Int
        a=T, b = Char

   The type variable b doesn't occur in f's type, but this is checked in a later
   phase. Probably it's a better solution to change the order of checking.

*/
		| isNilPtr bind_dst.tv_info_ptr
			= type_heaps
// ... RWS
		= { type_heaps & th_vars = writePtr bind_dst.tv_info_ptr (TVI_Type bind_src) type_heaps.th_vars}

	substitue_arg_type at=:{at_type = TFA type_vars type} (was_ok, type_heaps)
		# (fresh_type_vars, type_heaps) = foldSt build_avar_subst type_vars ([], type_heaps)
		  (new_at, type_heaps) = substitute {at & at_type = type} type_heaps
		= ({ new_at & at_type = TFA fresh_type_vars new_at.at_type}, (was_ok, type_heaps))
	substitue_arg_type type (was_ok, type_heaps)
		# (type, type_heaps) = substitute type type_heaps
		= (type, (was_ok, type_heaps))
		
	build_var_subst var (free_vars, type_var_heap)
		# (new_info_ptr, type_var_heap) = newPtr TVI_Empty type_var_heap
		  new_fv = { var & tv_info_ptr = new_info_ptr}
	  	= ([ new_fv : free_vars ], writePtr var.tv_info_ptr (TVI_Type (TV new_fv)) type_var_heap)

	build_avar_subst atv=:{atv_variable,atv_attribute} (free_vars, type_heaps)
		# (new_info_ptr, th_vars) = newPtr TVI_Empty type_heaps.th_vars
		  new_fv = { atv_variable & tv_info_ptr = new_info_ptr}
		  th_vars = th_vars <:= (atv_variable.tv_info_ptr, TVI_Type (TV new_fv))
		  (new_attr, th_attrs) = build_attr_subst atv_attribute type_heaps.th_attrs
		= ([ { atv & atv_variable = new_fv, atv_attribute = new_attr } : free_vars], { type_heaps & th_vars = th_vars, th_attrs = th_attrs })
	where		  
		 build_attr_subst (TA_Var avar) attr_var_heap
			# (new_info_ptr, attr_var_heap) = newPtr AVI_Empty attr_var_heap
			  new_attr = { avar & av_info_ptr = new_info_ptr}
			= (TA_Var new_attr, attr_var_heap <:= (avar.av_info_ptr, AVI_Attr (TA_Var new_attr)))
		 build_attr_subst attr attr_var_heap
			= (attr, attr_var_heap)

	build_attr_var_subst attr (free_attrs, attr_var_heap)
		# (new_info_ptr, attr_var_heap) = newPtr AVI_Empty attr_var_heap
		  new_attr = { attr & av_info_ptr = new_info_ptr}
		= ([new_attr : free_attrs], writePtr attr.av_info_ptr (AVI_Attr (TA_Var new_attr)) attr_var_heap)
	
	adjust_special_subst special_subst=:{ss_environ} type_var_heap
		# (ss_environ, type_var_heap) = mapSt adjust_special_bind ss_environ type_var_heap
		= ({ special_subst & ss_environ = ss_environ }, type_var_heap)
		
	adjust_special_bind bind=:{bind_dst={tv_info_ptr}} type_var_heap
		# (TVI_Type (TV new_tv), type_var_heap) = readPtr tv_info_ptr type_var_heap
		= ({ bind & bind_dst = new_tv }, type_var_heap)

determineTypeOfMemberInstance :: !SymbolType ![TypeVar] !InstanceType !Specials !*TypeHeaps !u:(Optional (v:{#DclModule}, w:{#CheckedTypeDef}, Index)) !*ErrorAdmin
		-> (!SymbolType, !Specials, !*TypeHeaps, !u:Optional (v:{#DclModule}, w:{#CheckedTypeDef}), !*ErrorAdmin)
determineTypeOfMemberInstance mem_st class_vars {it_types,it_vars,it_attr_vars,it_context} specials type_heaps opt_modules error
	# env = { ss_environ = foldl2 (\binds var type -> [ {bind_src = type, bind_dst = var} : binds]) [] class_vars it_types,
			  ss_context = it_context, ss_vars = it_vars, ss_attrs = it_attr_vars} 
	  (st, specials, type_heaps, error)
	  		= determine_type_of_member_instance mem_st env specials type_heaps error
	  (type_heaps, opt_modules, error)
	  		= check_attribution_consistency mem_st type_heaps opt_modules error
	= (st, specials, type_heaps, opt_modules, error)
where
	determine_type_of_member_instance mem_st=:{st_context} env (SP_Substitutions substs) type_heaps error
		# (mem_st, substs, type_heaps, error) 
				= substitute_symbol_type { mem_st &  st_context = tl st_context } env substs type_heaps error
		= (mem_st, SP_Substitutions substs, type_heaps, error) 
	determine_type_of_member_instance mem_st=:{st_context} env SP_None type_heaps error
		# (mem_st, _, type_heaps, error)
				= substitute_symbol_type { mem_st &  st_context = tl st_context } env [] type_heaps error
		= (mem_st, SP_None, type_heaps, error)

	substitute_symbol_type st=:{st_vars,st_attr_vars,st_args,st_result,st_context,st_attr_env} environment specials type_heaps error
		# (st_vars, st_attr_vars, [st_result : st_args], st_context, st_attr_env, specials, type_heaps, error)
			= instantiateTypes st_vars st_attr_vars [ st_result : st_args ] st_context st_attr_env environment specials type_heaps error
		= ({st & st_vars = st_vars, st_args = st_args, st_result = st_result, st_attr_vars = st_attr_vars,
			st_context = st_context, st_attr_env = st_attr_env }, specials, type_heaps, error)

	check_attribution_consistency {st_args, st_result} type_heaps No error
		= (type_heaps, No, error)
	check_attribution_consistency {st_args, st_result} type_heaps=:{th_vars} (Yes (modules, type_defs, x_main_dcl_module_n)) error
		// it is assumed that all type vars bindings done in instantiateTypes are still valid
		# (_, th_vars, modules, type_defs, error)
				= foldSt (foldATypeSt (check_it x_main_dcl_module_n) (\_ st -> st))
						[st_result:st_args]
						(False, th_vars, modules, type_defs, error)
		= ({ type_heaps & th_vars = th_vars }, Yes (modules, type_defs), error)
	
	check_it _ {at_attribute} (error_already_given, th_vars, modules, type_defs, error)
		| at_attribute==TA_Unique || error_already_given
			= (error_already_given, th_vars, modules, type_defs, error)
		// otherwise GOTO next alternative
	check_it x_main_dcl_module_n {at_type=TV tv} (_, th_vars, modules, type_defs, error)
  		= must_not_be_essentially_unique x_main_dcl_module_n tv th_vars modules type_defs error
	check_it x_main_dcl_module_n {at_type= (CV tv) :@: _} (_, th_vars, modules, type_defs, error)
  		= must_not_be_essentially_unique x_main_dcl_module_n tv th_vars modules type_defs error
	check_it _ _ state
		= state
		
	must_not_be_essentially_unique x_main_dcl_module_n {tv_ident, tv_info_ptr} th_vars modules type_defs error
		# (TVI_Type type, th_vars) = readPtr tv_info_ptr th_vars
		= case type of
			TA {type_ident, type_index} _
				-> must_not_be_essentially_unique_for_TA type_ident type_index th_vars
			TAS {type_ident, type_index} _ _
				-> must_not_be_essentially_unique_for_TA type_ident type_index th_vars
			_
				-> (False, th_vars, modules, type_defs, error)
		where
			must_not_be_essentially_unique_for_TA type_ident type_index th_vars
				# (type_def, type_defs, modules)
						= getTypeDef x_main_dcl_module_n type_index type_defs modules
				= case type_def.td_attribute of
					TA_Unique
						-> (True, th_vars, modules, type_defs,
							checkError type_ident 
								(   "is unique but instanciates class variable "
								 +++tv_ident.id_name
								 +++" that is non uniquely used in a member type"
								) error
						   )
					_
						-> (False, th_vars, modules, type_defs, error)
		
getTypeDef :: !Index !(Global Index) !v:{#CheckedTypeDef} !w:{#DclModule}
		-> (!CheckedTypeDef, !v:{#CheckedTypeDef}, !w:{#DclModule})
getTypeDef x_main_dcl_module_n {glob_module,glob_object} type_defs modules
	| glob_module==x_main_dcl_module_n
		# (type_def, type_defs)
				= type_defs![glob_object]
		= (type_def, type_defs, modules)
	# (type_def, modules)
			= modules![glob_module].dcl_common.com_type_defs.[glob_object]
	= (type_def, type_defs, modules)
		
determineTypesOfInstances :: !Index !Index !*{#ClassInstance} !*{# ClassDef} !*{# MemberDef} 
							 !*{#DclModule} !*TypeHeaps !*VarHeap !*CheckState
	-> (![FunType], !Index, ![ClassInstance], !*{#ClassInstance}, !*{# ClassDef}, !*{# MemberDef}, !*{#DclModule}, !*TypeHeaps, !*VarHeap, !*CheckState)
determineTypesOfInstances first_memb_inst_index mod_index com_instance_defs com_class_defs com_member_defs
		modules type_heaps var_heap cs=:{cs_error,cs_predef_symbols,cs_x={x_main_dcl_module_n}}
	| cs_error.ea_ok
		#! nr_of_class_instances = size com_instance_defs
		# (memb_inst_defs, next_mem_inst_index, all_class_specials, com_class_defs, com_member_defs, modules, com_instance_defs, type_heaps, var_heap, cs_predef_symbols,cs_error)
				= determine_types_of_instances x_main_dcl_module_n 0 nr_of_class_instances first_memb_inst_index mod_index [] com_class_defs com_member_defs 
						modules com_instance_defs type_heaps var_heap cs_predef_symbols cs_error
		= (memb_inst_defs, next_mem_inst_index, all_class_specials, com_instance_defs, com_class_defs,
		   com_member_defs, modules, type_heaps, var_heap, { cs & cs_predef_symbols=cs_predef_symbols,cs_error = cs_error })
		= ([], first_memb_inst_index, [], com_instance_defs, com_class_defs, com_member_defs, modules, type_heaps, var_heap, cs)
where
	determine_types_of_instances :: !Index !Index !Index !Index !Index ![ClassInstance] !v:{#ClassDef} !w:{#MemberDef}
		!x:{#DclModule} !*{#ClassInstance} !*TypeHeaps !*VarHeap !*PredefinedSymbols !*ErrorAdmin
			-> (![FunType], !Index, ![ClassInstance], !v:{#ClassDef}, !w:{#MemberDef}, !x:{#DclModule}, !*{#ClassInstance}, !*TypeHeaps, !*VarHeap, !*PredefinedSymbols,!*ErrorAdmin)
	determine_types_of_instances x_main_dcl_module_n inst_index next_class_inst_index next_mem_inst_index mod_index all_class_specials
			class_defs member_defs modules instance_defs type_heaps var_heap predef_symbols error
		| inst_index < size instance_defs
			# (instance_def=:{ins_class,ins_pos,ins_type,ins_specials}, instance_defs) = instance_defs![inst_index]
			# ({class_ident, class_members}, class_defs, modules) = getClassDef ins_class mod_index class_defs modules
			  class_size = size class_members
			  (ins_members, memb_inst_defs1, member_defs, modules, type_heaps, var_heap, error)
			  		= determine_instance_symbols_and_types x_main_dcl_module_n next_mem_inst_index 0 mod_index ins_class.glob_module class_size class_members
			  				ins_type ins_specials class_ident ins_pos member_defs modules type_heaps var_heap error
			  instance_def = { instance_def & ins_members = { member \\ member <- ins_members }}
			  (ins_specials, next_class_inst_index, all_class_specials, type_heaps, predef_symbols,error)
					= check_instance_specials mod_index instance_def inst_index ins_specials next_class_inst_index all_class_specials type_heaps predef_symbols error
			  (memb_inst_defs2, next_mem_inst_index, all_class_specials, class_defs, member_defs, modules, instance_defs, type_heaps, var_heap, predef_symbols,error)
			  		= determine_types_of_instances x_main_dcl_module_n (inc inst_index) next_class_inst_index (next_mem_inst_index + class_size) mod_index all_class_specials
			  				class_defs member_defs modules { instance_defs & [inst_index] = { instance_def & ins_specials = ins_specials }} type_heaps var_heap predef_symbols error

			= (memb_inst_defs1 ++ memb_inst_defs2, next_mem_inst_index, all_class_specials, class_defs, member_defs, modules, instance_defs, type_heaps, var_heap, predef_symbols,error)
			= ([], next_mem_inst_index, all_class_specials, class_defs, member_defs, modules, instance_defs, type_heaps, var_heap, predef_symbols,error)

	determine_instance_symbols_and_types :: !Index !Index !Index !Index !Index !Int !{#DefinedSymbol} !InstanceType !Specials Ident !Position
			!w:{#MemberDef} !u:{#DclModule} !*TypeHeaps !*VarHeap !*ErrorAdmin
					-> (![DefinedSymbol], ![FunType], !w:{#MemberDef}, !u:{#DclModule}, !*TypeHeaps, !*VarHeap, !.ErrorAdmin)
	determine_instance_symbols_and_types x_main_dcl_module_n first_inst_index mem_offset module_index member_mod_index class_size class_members
			ins_type ins_specials class_ident ins_pos member_defs modules type_heaps var_heap cs_error
		| mem_offset == class_size
			=  ([], [], member_defs, modules, type_heaps, var_heap, cs_error)
			# class_member = class_members.[mem_offset]
			  ({me_ident,me_type,me_priority,me_class_vars}, member_defs, modules) = getMemberDef member_mod_index class_member.ds_index module_index member_defs modules
			  cs_error
			  		= pushErrorAdmin (newPosition class_ident ins_pos) cs_error
			  (instance_type, new_ins_specials, type_heaps, Yes (modules, _), cs_error)
			  		= determineTypeOfMemberInstance me_type me_class_vars ins_type ins_specials type_heaps (Yes (modules, {}, cUndef)) cs_error
			  cs_error
			  		= popErrorAdmin cs_error
			  (new_info_ptr, var_heap) = newPtr VI_Empty var_heap
			  inst_def = MakeNewFunctionType me_ident me_type.st_arity me_priority instance_type ins_pos new_ins_specials new_info_ptr
			  (inst_symbols, memb_inst_defs, member_defs, modules, type_heaps, var_heap, cs_error)
			  		= determine_instance_symbols_and_types x_main_dcl_module_n first_inst_index (inc mem_offset) module_index member_mod_index
			  				class_size class_members ins_type ins_specials class_ident ins_pos member_defs modules type_heaps var_heap cs_error
			= ([{ class_member & ds_index = first_inst_index +  mem_offset } : inst_symbols], [inst_def : memb_inst_defs], member_defs, modules, type_heaps, var_heap, cs_error)

	check_instance_specials :: !Index !ClassInstance !Index !Specials !Index ![ClassInstance] !*TypeHeaps !*PredefinedSymbols !*ErrorAdmin
		-> (!Specials, !Index, ![ClassInstance], !*TypeHeaps, !*PredefinedSymbols,!*ErrorAdmin)
	check_instance_specials mod_index inst_type inst_index (SP_Substitutions substs) next_inst_index all_instances type_heaps predef_symbols error
		# (list_of_specials, next_inst_index, all_instances, type_heaps, predef_symbols,error)
			= check_specials mod_index inst_type 0 substs [] next_inst_index all_instances type_heaps predef_symbols error
		= (SP_ContextTypes list_of_specials, next_inst_index, all_instances, type_heaps, predef_symbols, error)
	where
		check_specials mod_index inst=:{ins_type} type_offset [ subst : substs ] list_of_specials next_inst_index all_instances type_heaps predef_symbols error
			# (special_type, type_heaps, error) = substitute_instance_type ins_type subst type_heaps error
			  (spec_types, predef_symbols,error) = checkAndCollectTypesOfContextsOfSpecials special_type.it_context predef_symbols error
			  special = { spec_index = { glob_module = mod_index, glob_object = next_inst_index }, spec_types = spec_types,
			  				spec_vars = subst.ss_vars, spec_attrs = subst.ss_attrs }
			= check_specials mod_index inst (inc type_offset) substs [ special : list_of_specials ] (inc next_inst_index)
					[{ inst & ins_type = { special_type & it_context = [] }, ins_specials = SP_TypeOffset type_offset} : all_instances ] type_heaps predef_symbols error
		where
			substitute_instance_type :: !InstanceType !SpecialSubstitution !*TypeHeaps !*ErrorAdmin -> (!InstanceType,!*TypeHeaps,!.ErrorAdmin)
			substitute_instance_type it=:{it_vars,it_attr_vars,it_types,it_context} environment type_heaps cs_error
				# (it_vars, it_attr_vars, it_atypes, it_context, _, _, type_heaps, cs_error)	
					= instantiateTypes it_vars it_attr_vars [MakeAttributedType type \\ type <- it_types] it_context [] environment [] type_heaps cs_error
				= ({it & it_vars = it_vars, it_types = [ at_type \\ {at_type} <- it_atypes ], it_attr_vars = it_attr_vars, it_context = it_context }, type_heaps, cs_error)			
		check_specials mod_index inst=:{ins_type} type_offset [] list_of_specials next_inst_index all_instances type_heaps predef_symbols error
			= (list_of_specials,  next_inst_index, all_instances, type_heaps, predef_symbols, error)
	check_instance_specials mod_index fun_type fun_index SP_None next_inst_index all_instances type_heaps predef_symbols error
		= (SP_None, next_inst_index, all_instances, type_heaps, predef_symbols,error)

mapSt2 f l s1 s2 :== map_st2 l s1 s2
where
	map_st2 [x : xs] s1 s2
	 	# (x, s1,s2) = f x s1 s2
		  (xs, s1,s2) = map_st2 xs s1 s2
		#! s1 = s1
		#! s2 = s2
		= ([x : xs], s1,s2)
	map_st2 [] s1 s2
	 	= ([], s1,s2)
	
checkAndCollectTypesOfContextsOfSpecials :: [TypeContext] *PredefinedSymbols *ErrorAdmin -> (![[Type]],!*PredefinedSymbols,!*ErrorAdmin);
checkAndCollectTypesOfContextsOfSpecials type_contexts predef_symbols error
	= mapSt2 check_and_collect_context_types_of_special type_contexts predef_symbols error
where	
	check_and_collect_context_types_of_special {tc_class=TCClass {glob_object={ds_ident,ds_index},glob_module},tc_types} predef_symbols error
		| hasNoTypeVariables tc_types
			= (tc_types, predef_symbols,error)
		# {pds_def,pds_module} = predef_symbols.[PD_ArrayClass]
		| glob_module==pds_module && ds_index==pds_def && is_lazy_or_strict_array tc_types predef_symbols
			= (tc_types, predef_symbols,error)
		# {pds_def,pds_module} = predef_symbols.[PD_ListClass]
		| glob_module==pds_module && ds_index==pds_def && is_lazy_or_strict_list tc_types predef_symbols
			= (tc_types, predef_symbols,error)
			= (tc_types, predef_symbols,checkError ds_ident.id_name "illegal specialization" error)
	check_and_collect_context_types_of_special {tc_class=TCGeneric {gtc_generic},tc_types} predef_symbols error
		= (tc_types, predef_symbols,checkError gtc_generic.glob_object.ds_ident.id_name "genenric specials are illegal" error) 

	hasNoTypeVariables []
		= True
	hasNoTypeVariables [TV tvar : types]
		= False
	hasNoTypeVariables [ _ : types]
		= hasNoTypeVariables types
	
	is_lazy_or_strict_array [TA {type_index={glob_module,glob_object}} [],TV var] predef_symbols
		# {pds_def,pds_module} = predef_symbols.[PD_LazyArrayType]
		| glob_module==pds_module && glob_object==pds_def
			= True
		# {pds_def,pds_module} = predef_symbols.[PD_StrictArrayType]
		| glob_module==pds_module && glob_object==pds_def
			= True
			= False
	is_lazy_or_strict_array _ predef_symbols
		= False

	is_lazy_or_strict_list [TA {type_index={glob_module,glob_object}} [],TV var] predef_symbols
		# {pds_def,pds_module} = predef_symbols.[PD_ListType]
		| glob_module==pds_module && glob_object==pds_def
			= True
		# {pds_def,pds_module} = predef_symbols.[PD_StrictListType]
		| glob_module==pds_module && glob_object==pds_def
			= True
		# {pds_def,pds_module} = predef_symbols.[PD_TailStrictListType]
		| glob_module==pds_module && glob_object==pds_def
			= True
		# {pds_def,pds_module} = predef_symbols.[PD_StrictTailStrictListType]
		| glob_module==pds_module && glob_object==pds_def
			= True
			= False
	is_lazy_or_strict_list _ predef_symbols
		= False

initializeContextVariables :: ![TypeContext] !*VarHeap ->  (![TypeContext], !*VarHeap)
initializeContextVariables contexts var_heap
	= mapSt add_variable_to_context contexts var_heap
where
	add_variable_to_context context var_heap
		# (new_info_ptr, var_heap) = newPtr VI_Empty var_heap
		= ({ context & tc_var = new_info_ptr}, var_heap)

ident_for_errors_from_fun_symb_and_fun_kind :: Ident FunKind -> Ident;
ident_for_errors_from_fun_symb_and_fun_kind {id_name} (FK_Function fun_name_is_location_dependent)
	| fun_name_is_location_dependent && size id_name>0
		# beautiful_name = if (id_name.[0]==backslash) "lambda" "comprehension"
		= { id_name=beautiful_name, id_info=nilPtr }
ident_for_errors_from_fun_symb_and_fun_kind fun_ident _
	= fun_ident

// check that there are no strict lets, mark top-level cases as explicit
class checkMacro a :: !Bool !a !*ErrorAdmin -> (!a, !*ErrorAdmin)

instance checkMacro [a] | checkMacro a where
	checkMacro topLevel l ea
		=	mapSt (checkMacro topLevel) l ea

instance checkMacro FunctionBody where
	checkMacro topLevel (CheckedBody body) ea
		# (body, ea)
			=	checkMacro topLevel body ea
		= (CheckedBody body, ea)

instance checkMacro CheckedBody where
	checkMacro topLevel body=:{cb_rhs} ea
		# (cb_rhs, ea)
			=	checkMacro topLevel cb_rhs ea
		= ({body & cb_rhs = cb_rhs}, ea)

instance checkMacro CheckedAlternative where
	checkMacro topLevel alt=:{ca_rhs} ea
		# (ca_rhs, ea)
			=	checkMacro topLevel ca_rhs ea
		= ({alt & ca_rhs = ca_rhs}, ea)

instance checkMacro Expression where
	checkMacro topLevel (Let lad) ea
		# (lad, ea)
			=	checkMacro topLevel lad ea
		=	(Let lad, ea)
	checkMacro topLevel (Case kees) ea
		# (kees, ea)
			=	checkMacro topLevel kees ea
		=	(Case kees, ea)
	checkMacro _ expr ea
		=	(expr, ea)

instance checkMacro Let where
	checkMacro topLevel lad=:{let_strict_binds, let_expr} ea
		# ea
			=	check_strict_binds let_strict_binds ea
		# (let_expr, ea)
			=	checkMacro topLevel let_expr ea
		= ({lad & let_expr = let_expr}, ea)
		where
			check_strict_binds [] ea
				=	ea
			check_strict_binds _ ea
				=	checkError "#! not allowed in macros" "" ea

instance checkMacro Case where
	checkMacro topLevel kees=:{case_guards, case_explicit} ea
		# (case_guards, ea)
			=	checkMacro False case_guards ea
		= ({kees & case_guards = case_guards,case_explicit = topLevel || case_explicit}, ea)

instance checkMacro CasePatterns where
	checkMacro topLevel (AlgebraicPatterns type patterns) ea
		# (patterns, ea)
			=	checkMacro topLevel patterns ea	
		=	(AlgebraicPatterns type patterns, ea)
	checkMacro topLevel (BasicPatterns type patterns) ea
		# (patterns, ea)
			=	checkMacro topLevel patterns ea	
		=	(BasicPatterns type patterns, ea)
	checkMacro topLevel (DynamicPatterns patterns) ea
		# (patterns, ea)
			=	checkMacro topLevel patterns ea	
		=	(DynamicPatterns patterns, ea)
	checkMacro topLevel (OverloadedListPatterns type decons patterns) ea
		# (patterns, ea)
			=	checkMacro topLevel patterns ea	
		=	(OverloadedListPatterns type decons patterns, ea)
	checkMacro _ NoPattern ea
		=	(NoPattern, ea)

instance checkMacro AlgebraicPattern where
	checkMacro topLevel pattern=:{ap_expr} ea
		# (ap_expr, ea)
			=	checkMacro topLevel ap_expr ea	
		=	({pattern & ap_expr = ap_expr}, ea)

instance checkMacro BasicPattern where
	checkMacro topLevel pattern=:{bp_expr} ea
		# (bp_expr, ea)
			=	checkMacro topLevel bp_expr ea	
		=	({pattern & bp_expr = bp_expr}, ea)

instance checkMacro DynamicPattern where
	checkMacro topLevel pattern=:{dp_rhs} ea
		# (dp_rhs, ea)
			=	checkMacro topLevel dp_rhs ea	
		=	({pattern & dp_rhs = dp_rhs}, ea)

checkFunctionBodyIfMacro :: !FunKind !FunctionBody !*ErrorAdmin -> (!FunctionBody, !*ErrorAdmin)
checkFunctionBodyIfMacro FK_Macro def ea
	=	checkMacro True def ea
checkFunctionBodyIfMacro _ def ea
	=	(def, ea)

checkFunction :: !FunDef !Index !FunctionOrMacroIndex !Level !Int !*{#FunDef} !*ExpressionInfo !*Heaps !*CheckState
													  -> (!FunDef,!*{#FunDef},!*ExpressionInfo,!*Heaps,!*CheckState);
checkFunction fun_def=:{fun_ident,fun_pos,fun_body,fun_type,fun_kind} mod_index fun_index def_level local_functions_index_offset
			fun_defs e_info=:{ef_type_defs,ef_modules,ef_class_defs,ef_is_macro_fun} heaps=:{hp_var_heap,hp_expression_heap,hp_type_heaps,hp_generic_heap} cs=:{cs_error}			
	# function_ident_for_errors = ident_for_errors_from_fun_symb_and_fun_kind fun_ident fun_kind
	# cs = {cs & cs_error = pushErrorAdmin (newPosition function_ident_for_errors fun_pos) cs_error}

	  (fun_type, ef_type_defs, ef_class_defs, ef_modules, hp_var_heap, hp_type_heaps, cs)
			= check_function_type fun_type mod_index (fun_kind == FK_Caf) ef_type_defs ef_class_defs ef_modules hp_var_heap hp_type_heaps cs
	  e_info  = { e_info & ef_type_defs = ef_type_defs, ef_class_defs = ef_class_defs, ef_modules = ef_modules }
	  e_state = {   es_var_heap = hp_var_heap, es_expr_heap = hp_expression_heap, es_type_heaps = hp_type_heaps,es_generic_heap=hp_generic_heap,
	  				es_dynamics = [], es_calls = [], es_fun_defs = fun_defs}
	  e_input = { ei_expr_level = inc def_level, ei_fun_index = fun_index, ei_fun_level = inc def_level, ei_mod_index = mod_index, ei_local_functions_index_offset=local_functions_index_offset }
	  (fun_body, free_vars, e_state, e_info, cs) = checkFunctionBodies fun_body function_ident_for_errors e_input e_state e_info cs

	# {es_fun_defs,es_calls,es_var_heap,es_expr_heap,es_type_heaps,es_generic_heap,es_dynamics} = e_state
	  (ef_type_defs, ef_modules, es_type_heaps, es_expr_heap, cs) = 
	  	checkDynamicTypes mod_index es_dynamics fun_type e_info.ef_type_defs e_info.ef_modules es_type_heaps es_expr_heap cs
	  (fun_body, cs_error) = checkFunctionBodyIfMacro fun_kind fun_body cs.cs_error
	  cs = { cs & cs_error = popErrorAdmin cs_error }
	  fi_properties = (if ef_is_macro_fun FI_IsMacroFun 0) bitor (has_type fun_type)
	  fun_info = { fun_def.fun_info & fi_calls = es_calls, fi_def_level = def_level, fi_free_vars = free_vars, fi_dynamics = es_dynamics,
	  								  fi_properties = fi_properties }
  
	  fun_def = { fun_def & fun_body = fun_body, fun_info = fun_info, fun_type = fun_type}
	  (fun_defs,macro_defs,cs_symbol_table) = remove_calls_from_symbol_table fun_index def_level es_calls e_state.es_fun_defs e_info.ef_macro_defs cs.cs_symbol_table
	= (fun_def,fun_defs,
			{ e_info & ef_type_defs = ef_type_defs, ef_modules = ef_modules,ef_macro_defs=macro_defs },
			{ heaps & hp_var_heap = es_var_heap, hp_expression_heap = es_expr_heap, hp_type_heaps = es_type_heaps,hp_generic_heap=es_generic_heap }, 
			{ cs & cs_symbol_table = cs_symbol_table })

where
	has_type (Yes _) 	= FI_HasTypeSpec
	has_type no 		= 0
	
	check_function_type (Yes ft) module_index is_caf type_defs class_defs modules var_heap type_heaps cs
		# (ft, _, type_defs, class_defs, modules, type_heaps, cs) = checkFunctionType module_index ft SP_None type_defs class_defs modules type_heaps cs
		  cs = (if is_caf (check_caf_uniqueness ft.st_result.at_attribute) id) cs
		  (st_context, var_heap) = initializeContextVariables ft.st_context var_heap
		= (Yes { ft & st_context = st_context } , type_defs,  class_defs, modules, var_heap, type_heaps, cs)
		where
			check_caf_uniqueness TA_None cs
				=	cs
			check_caf_uniqueness TA_Multi cs
				=	cs
			check_caf_uniqueness _ cs
				= {cs & cs_error = checkError "result type of CAF must be non-unique " "" cs.cs_error}
	check_function_type No module_index _ type_defs class_defs modules var_heap type_heaps cs
		= (No, type_defs,  class_defs, modules, var_heap, type_heaps, cs)

	remove_calls_from_symbol_table fun_index fun_level [FunCall fc_index fc_level : fun_calls] fun_defs macro_defs symbol_table
		| fc_level <= fun_level
			# (id_info, fun_defs) = fun_defs![fc_index].fun_ident.id_info
			# (entry, symbol_table) = readPtr id_info symbol_table
			# symbol_table = remove_call entry.ste_kind fun_index entry id_info symbol_table
			= remove_calls_from_symbol_table fun_index fun_level fun_calls fun_defs macro_defs symbol_table
			= remove_calls_from_symbol_table fun_index fun_level fun_calls fun_defs macro_defs symbol_table
	remove_calls_from_symbol_table fun_index fun_level [MacroCall module_index fc_index fc_level : fun_calls] fun_defs macro_defs symbol_table
		| fc_level <= fun_level
			# (id_info, macro_defs) = macro_defs![module_index,fc_index].fun_ident.id_info
			# (entry, symbol_table) = readPtr id_info symbol_table
			# symbol_table = remove_call entry.ste_kind fun_index entry id_info symbol_table
			= remove_calls_from_symbol_table fun_index fun_level fun_calls fun_defs macro_defs symbol_table
			= remove_calls_from_symbol_table fun_index fun_level fun_calls fun_defs macro_defs symbol_table
	remove_calls_from_symbol_table fun_index fun_level [DclFunCall _ _ : fun_calls] fun_defs macro_defs symbol_table
		= remove_calls_from_symbol_table fun_index fun_level fun_calls fun_defs macro_defs symbol_table

	remove_calls_from_symbol_table fun_index fun_level [] fun_defs macro_defs symbol_table
		= (fun_defs,macro_defs,symbol_table)

	remove_call (STE_FunctionOrMacro [x:xs]) fun_index entry id_info symbol_table
		| fun_index==x
			= symbol_table <:= (id_info,{ entry & ste_kind = STE_FunctionOrMacro xs})
	remove_call (STE_DclMacroOrLocalMacroFunction [x:xs]) fun_index entry id_info symbol_table
		| fun_index==x
			= symbol_table <:= (id_info,{ entry & ste_kind = STE_DclMacroOrLocalMacroFunction xs})
	remove_call (STE_Imported (STE_DclMacroOrLocalMacroFunction [x:xs]) mod_index) fun_index entry id_info symbol_table
		| fun_index==x
			= symbol_table <:= (id_info,{ entry & ste_kind = (STE_Imported (STE_DclMacroOrLocalMacroFunction xs) mod_index)})

checkGlobalFunctionsInRanges:: ![IndexRange] !Index !Int !*{#FunDef} !*ExpressionInfo !*Heaps !*CheckState
													 -> (!*{#FunDef},!*ExpressionInfo,!*Heaps,!*CheckState)
checkGlobalFunctionsInRanges [{ir_from,ir_to}:ranges] mod_index local_functions_index_offset fun_defs e_info heaps cs
	# (fun_defs, e_info, heaps, cs)
		= checkFunctions mod_index cGlobalScope ir_from ir_to local_functions_index_offset fun_defs e_info heaps cs;
	= checkGlobalFunctionsInRanges ranges mod_index local_functions_index_offset fun_defs e_info heaps cs;
checkGlobalFunctionsInRanges [] mod_index local_functions_index_offset fun_defs e_info heaps cs
	= (fun_defs, e_info, heaps, cs)

checkFunctions :: !Index !Level !Index !Index !Int !*{#FunDef} !*ExpressionInfo !*Heaps !*CheckState
											   -> (!*{#FunDef},!*ExpressionInfo,!*Heaps,!*CheckState)
checkFunctions mod_index level fun_index to_index local_functions_index_offset fun_defs e_info heaps cs
	| fun_index == to_index
		= (fun_defs, e_info, heaps, cs)
		# (fun_def,fun_defs) = fun_defs![fun_index]
		# (fun_def,fun_defs, e_info, heaps, cs) = checkFunction fun_def mod_index (FunctionOrIclMacroIndex fun_index) level local_functions_index_offset fun_defs e_info heaps cs
		# fun_defs = { fun_defs & [fun_index] = fun_def }
		= checkFunctions mod_index level (inc fun_index) to_index local_functions_index_offset fun_defs e_info heaps cs

checkDclMacros :: !Index !Level !Index !Index !*{#FunDef} !*ExpressionInfo !*Heaps !*CheckState
										  -> (!*{#FunDef},!*ExpressionInfo,!*Heaps,!*CheckState)
checkDclMacros mod_index level fun_index to_index fun_defs e_info heaps cs
	| fun_index == to_index
		= (fun_defs, e_info, heaps, cs)
		# (macro_def,e_info) = e_info!ef_macro_defs.[mod_index,fun_index]
		# (macro_def,fun_defs, e_info, heaps, cs) = checkFunction macro_def mod_index (DclMacroIndex mod_index fun_index) level 0 fun_defs e_info heaps cs
		# e_info = { e_info & ef_macro_defs.[mod_index,fun_index] = macro_def }
		= checkDclMacros mod_index level (inc fun_index) to_index fun_defs e_info heaps cs

get_predef_symbols_for_transform :: *PredefinedSymbols -> (!PredefSymbolsForTransform,!.PredefinedSymbols)
// clean 2.0 does not allow this, clean 1.3 does:
// get_predef_symbols_for_transform cs_predef_symbols=:{[PD_DummyForStrictAliasFun]=predef_alias_dummy,[PD_AndOp]=predef_and,[PD_OrOp]=predef_or}
get_predef_symbols_for_transform cs_predef_symbols
	# (predef_alias_dummy,cs_predef_symbols) = cs_predef_symbols![PD_DummyForStrictAliasFun]
	# (predef_and,cs_predef_symbols) = cs_predef_symbols![PD_AndOp]
	# (predef_or,cs_predef_symbols) = cs_predef_symbols![PD_OrOp]
	= ({predef_alias_dummy=predef_alias_dummy,predef_and=predef_and,predef_or=predef_or},cs_predef_symbols)

checkAndPartitionateDclMacros ::  !Index !IndexRange !*{#FunDef} !*ExpressionInfo !*Heaps !*CheckState
												 -> (!*{#FunDef},!*ExpressionInfo,!*Heaps,!*CheckState);
checkAndPartitionateDclMacros mod_index range fun_defs e_info=:{ef_is_macro_fun=ef_is_macro_fun_old} heaps cs
	# (fun_defs, e_info, heaps=:{hp_var_heap, hp_expression_heap}, cs=:{cs_symbol_table, cs_predef_symbols, cs_error})
			= checkDclMacros mod_index cGlobalScope range.ir_from range.ir_to fun_defs { e_info & ef_is_macro_fun=True } heaps cs
	  (e_info=:{ef_macro_defs}) = { e_info & ef_is_macro_fun=ef_is_macro_fun_old }
	# (predef_symbols_for_transform, cs_predef_symbols) = get_predef_symbols_for_transform cs_predef_symbols
	  (fun_defs, macro_defs, hp_var_heap, hp_expression_heap, cs_symbol_table, cs_error)
	  		= partitionateDclMacros range mod_index predef_symbols_for_transform fun_defs ef_macro_defs hp_var_heap hp_expression_heap cs_symbol_table cs_error
	= (fun_defs, { e_info & ef_macro_defs=macro_defs }, {heaps &  hp_var_heap = hp_var_heap, hp_expression_heap = hp_expression_heap},
			{ cs & cs_symbol_table = cs_symbol_table, cs_predef_symbols = cs_predef_symbols, cs_error = cs_error })

checkAndPartitionateIclMacros ::  !Index !IndexRange !Int !*{#FunDef} !*ExpressionInfo !*Heaps !*CheckState
													  -> (!*{#FunDef},!*ExpressionInfo,!*Heaps,!*CheckState);
checkAndPartitionateIclMacros mod_index range local_functions_index_offset fun_defs e_info=:{ef_is_macro_fun=ef_is_macro_fun_old} heaps cs
	# (fun_defs, e_info, heaps=:{hp_var_heap, hp_expression_heap}, cs=:{cs_symbol_table, cs_predef_symbols, cs_error})
			= checkFunctions mod_index cGlobalScope range.ir_from range.ir_to local_functions_index_offset fun_defs { e_info & ef_is_macro_fun=True } heaps cs
	  (e_info=:{ef_macro_defs}) = { e_info & ef_is_macro_fun=ef_is_macro_fun_old }
	# (predef_symbols_for_transform, cs_predef_symbols) = get_predef_symbols_for_transform cs_predef_symbols
	  (fun_defs, macro_defs, hp_var_heap, hp_expression_heap, cs_symbol_table, cs_error)
	  		= partitionateIclMacros range mod_index predef_symbols_for_transform fun_defs ef_macro_defs hp_var_heap hp_expression_heap cs_symbol_table cs_error
	= (fun_defs, { e_info & ef_macro_defs=macro_defs }, {heaps &  hp_var_heap = hp_var_heap, hp_expression_heap = hp_expression_heap},
			{ cs & cs_symbol_table = cs_symbol_table, cs_predef_symbols = cs_predef_symbols, cs_error = cs_error })

checkInstanceBodies :: ![IndexRange] !Int !*{#FunDef} !*ExpressionInfo !*Heaps !*CheckState
									  -> (!*{#FunDef},!*ExpressionInfo,!*Heaps, !*CheckState);
checkInstanceBodies icl_instances_ranges local_functions_index_offset fun_defs e_info heaps cs=:{cs_x}
	= checkGlobalFunctionsInRanges icl_instances_ranges cs_x.x_main_dcl_module_n local_functions_index_offset fun_defs e_info heaps cs

instance < FunDef 
where
	(<) fd1 fd2 = fd1.fun_ident.id_name < fd2.fun_ident.id_name

createCommonDefinitions :: (CollectedDefinitions ClassInstance a) -> .CommonDefs;
createCommonDefinitions {def_types,def_constructors,def_selectors,def_classes,def_members,def_instances, def_generics,def_generic_cases}
	=	{	com_type_defs		= { type \\ type <- def_types }
		,	com_cons_defs		= { cons \\ cons <- def_constructors }
		,	com_selector_defs	= { sel \\ sel <- def_selectors }
		,	com_class_defs		= { class_def \\ class_def <- def_classes }
		,	com_member_defs		= { member \\ member <- def_members }
		,	com_instance_defs	= { next_instance \\ next_instance <- def_instances }
		,	com_generic_defs	= { gen \\ gen <- def_generics }
		, 	com_gencase_defs    = { gi \\ gi <- def_generic_cases}		
		}

array_plus_list a [] = a
array_plus_list a l = arrayPlusList a l

checkCommonDefinitions :: !(Optional (CopiedDefinitions, Int)) !Index !*CommonDefs !*{# DclModule} !*Heaps !*CheckState
												  -> (!DictionaryInfo,!*CommonDefs,!*{# DclModule},!*Heaps, !*CheckState)
checkCommonDefinitions opt_icl_info module_index common modules heaps cs
	# (com_type_defs, com_cons_defs, com_selector_defs, modules, heaps, cs)
			= checkTypeDefs module_index opt_icl_info
					common.com_type_defs common.com_cons_defs common.com_selector_defs modules heaps cs
	  (com_class_defs, com_member_defs, com_type_defs, modules, heaps, cs)
	  		= checkTypeClasses module_index opt_icl_info common.com_class_defs common.com_member_defs com_type_defs modules heaps cs
	  (com_member_defs, com_type_defs, com_class_defs, modules, heaps, cs)
	  		= checkMemberTypes module_index opt_icl_info com_member_defs com_type_defs com_class_defs modules heaps cs
	  (com_instance_defs, com_type_defs, com_class_defs, com_member_defs, modules, heaps, cs)
	  		= checkInstanceDefs module_index common.com_instance_defs com_type_defs com_class_defs com_member_defs modules heaps cs
	  (com_generic_defs, com_type_defs, com_class_defs, modules, heaps, cs)
			= checkGenericDefs module_index opt_icl_info common.com_generic_defs com_type_defs com_class_defs modules heaps cs
	  (com_gencase_defs, com_generic_defs, com_type_defs, modules, heaps, cs)
			= checkGenericCaseDefs module_index common.com_gencase_defs com_generic_defs com_type_defs modules heaps cs	  
 	| cs.cs_error.ea_ok
		# (size_com_type_defs,com_type_defs) = usize com_type_defs
	 	  (size_com_selector_defs,com_selector_defs) = usize com_selector_defs
	      (size_com_cons_defs,com_cons_defs) = usize com_cons_defs
		  {hp_var_heap, hp_type_heaps=hp_type_heaps=:{th_vars} } = heaps
		  is_dcl = case opt_icl_info of No -> True ; Yes _ -> False
		  (new_type_defs, new_selector_defs, new_cons_defs,dictionary_info,com_type_defs,com_selector_defs, com_cons_defs, com_class_defs, modules, th_vars, hp_var_heap, cs_symbol_table)
		  	= createClassDictionaries is_dcl module_index size_com_type_defs size_com_selector_defs size_com_cons_defs
								  			com_type_defs com_selector_defs com_cons_defs com_class_defs modules th_vars hp_var_heap cs.cs_symbol_table
	
		  com_type_defs = array_plus_list com_type_defs new_type_defs
		  com_selector_defs = array_plus_list com_selector_defs new_selector_defs
		  com_cons_defs = array_plus_list com_cons_defs new_cons_defs
		  
		  common = {common & com_type_defs = com_type_defs, com_cons_defs = com_cons_defs, com_selector_defs = com_selector_defs, com_class_defs = com_class_defs,
							 com_member_defs = com_member_defs,  com_instance_defs = com_instance_defs, 
							 com_generic_defs = com_generic_defs, com_gencase_defs = com_gencase_defs}
		  heaps = {heaps & hp_var_heap=hp_var_heap,hp_type_heaps={hp_type_heaps & th_vars=th_vars}}
		= (dictionary_info,common, modules,	heaps, { cs & cs_symbol_table = cs_symbol_table })

		# dictionary_info = { n_dictionary_types=0, n_dictionary_constructors=0, n_dictionary_selectors=0 }
		  common = {common & com_type_defs = com_type_defs, com_cons_defs = com_cons_defs, com_selector_defs = com_selector_defs, com_class_defs = com_class_defs,
							 com_member_defs = com_member_defs,  com_instance_defs = com_instance_defs, 
							 com_generic_defs = com_generic_defs, com_gencase_defs = com_gencase_defs}	
		= (dictionary_info,common, modules,	heaps, cs)
		
collectCommonfinitions :: !(CollectedDefinitions ClassInstance a) -> (!*{# Int}, ![Declaration])
collectCommonfinitions {def_types,def_constructors,def_selectors,def_classes,def_members,def_instances, def_generic_cases, def_generics} 
	// MW: the order in which the declarations appear in the returned list is essential (explicit imports)
	# sizes = createArray cConversionTableSize 0
	  (size, defs) = foldSt cons_def_to_dcl def_constructors (0, [])
	  sizes = { sizes & [cConstructorDefs] = size }
	  (size, defs) = foldSt selector_def_to_dcl def_selectors (0, defs)
	  sizes = { sizes & [cSelectorDefs] = size }
	  (size, defs) = foldSt type_def_to_dcl def_types (0, defs)
	  sizes = { sizes & [cTypeDefs] = size }
	  (size, defs) = foldSt member_def_to_dcl def_members (0, defs)
	  sizes = { sizes & [cMemberDefs] = size }
	  (size, defs) = foldSt class_def_to_dcl def_classes (0, defs)
	  sizes = { sizes & [cClassDefs] = size }
	  (size, defs) = foldSt instance_def_to_dcl def_instances (0, defs)
	  sizes = { sizes & [cInstanceDefs] = size }
	  (size, defs) = foldSt generic_def_to_dcl def_generics (0, defs)
	  sizes = { sizes & [cGenericDefs] = size }
	  (size, defs) = foldSt gen_case_def_to_dcl def_generic_cases (0, defs)
	  sizes = { sizes & [cGenericCaseDefs] = size }
	= (sizes, defs)
where
	type_def_to_dcl {td_ident, td_pos} (decl_index, decls)
		= (inc decl_index, [Declaration { decl_ident = td_ident, decl_pos = td_pos, decl_kind = STE_Type, decl_index = decl_index } : decls]) 
	cons_def_to_dcl {cons_ident, cons_pos} (decl_index, decls)
		= (inc decl_index, [Declaration { decl_ident = cons_ident, decl_pos = cons_pos, decl_kind = STE_Constructor, decl_index = decl_index } : decls]) 
	selector_def_to_dcl {sd_ident, sd_field, sd_pos} (decl_index, decls)
		= (inc decl_index, [Declaration { decl_ident = sd_field, decl_pos = sd_pos, decl_kind = STE_Field sd_ident, decl_index = decl_index } : decls]) 
	class_def_to_dcl {class_ident, class_pos} (decl_index, decls)
		= (inc decl_index, [Declaration { decl_ident = class_ident, decl_pos = class_pos, decl_kind = STE_Class, decl_index = decl_index } : decls]) 
	member_def_to_dcl {me_ident, me_pos} (decl_index, decls)
		= (inc decl_index, [Declaration { decl_ident = me_ident, decl_pos = me_pos, decl_kind = STE_Member, decl_index = decl_index } : decls]) 
	instance_def_to_dcl {ins_ident, ins_pos} (decl_index, decls)
		= (inc decl_index, [Declaration { decl_ident = ins_ident, decl_pos = ins_pos, decl_kind = STE_Instance, decl_index = decl_index } : decls])
	generic_def_to_dcl {gen_ident, gen_member_ident, gen_type, gen_pos} (decl_index, decls)
		# generic_decl = Declaration { decl_ident = gen_ident, decl_pos = gen_pos, decl_kind = STE_Generic, decl_index = decl_index }
		# member_decl = Declaration { decl_ident = gen_member_ident, decl_pos = gen_pos, decl_kind = STE_Generic, decl_index = decl_index }
		= (inc decl_index, [generic_decl, member_decl : decls]) 
	gen_case_def_to_dcl {gc_ident, gc_pos} (decl_index, decls)
		= (inc decl_index, [Declaration { decl_ident = gc_ident, decl_pos = gc_pos, decl_kind = STE_GenericCase, decl_index = decl_index } : decls]) 

collectMacros {ir_from,ir_to} macro_defs sizes_defs
	= collectGlobalFunctions cMacroDefs ir_from ir_to macro_defs sizes_defs

collectFunctionTypes fun_types (sizes, defs)
	# (size, defs) = foldSt fun_type_to_dcl fun_types (0, defs)
	= ({ sizes & [cFunctionDefs] = size }, defs)
where
	fun_type_to_dcl {ft_ident, ft_pos} (decl_index, decls) 
		= (inc decl_index, [Declaration { decl_ident = ft_ident, decl_pos = ft_pos, decl_kind = STE_DclFunction, decl_index = decl_index } : decls]) 

collectGlobalFunctions def_index from_index to_index fun_defs (sizes, defs)
	# (defs, fun_defs) = iFoldSt fun_def_to_decl from_index to_index (defs, fun_defs)  
	= (fun_defs, ({ sizes & [def_index] = to_index - from_index }, defs))
where
	fun_def_to_decl decl_index (defs, fun_defs)
		# ({fun_ident, fun_pos}, fun_defs) = fun_defs![decl_index]
		= ([Declaration { decl_ident = fun_ident, decl_pos = fun_pos, decl_kind = STE_FunctionOrMacro [], decl_index = decl_index } : defs], fun_defs)

collectDclMacros {ir_from=from_index,ir_to=to_index} fun_defs (sizes, defs)
	# (defs, fun_defs) = iFoldSt macro_def_to_dcl from_index to_index (defs, fun_defs)  
	= (fun_defs, ({ sizes & [cMacroDefs] = to_index - from_index }, defs))
where
	macro_def_to_dcl decl_index (defs, fun_defs)
		# ({fun_ident, fun_pos}, fun_defs) = fun_defs![decl_index]
		= ([Declaration { decl_ident = fun_ident, decl_pos = fun_pos, decl_kind = STE_DclMacroOrLocalMacroFunction [], decl_index = decl_index } : defs], fun_defs)

gimme_a_lazy_array_type :: !u:{.a} -> v:{.a}, [u<=v]
gimme_a_lazy_array_type a = a

gimme_a_strict_array_type :: !u:{!.a} -> v:{!.a}, [u<=v]
gimme_a_strict_array_type a = a

create_icl_to_dcl_index_table :: !ModuleKind !{#Int} !Int !(Optional {#{#Int}}) !*{#DclModule} !*{#FunDef}
																  -> (!Optional {#{#Int}},!Optional {#{#Int}},  !.{#DclModule},!*{#FunDef})
create_icl_to_dcl_index_table MK_Main icl_sizes main_dcl_module_n dcl_conversions modules fun_defs
	= (No,No,modules,fun_defs)
create_icl_to_dcl_index_table _ icl_sizes main_dcl_module_n old_conversions modules fun_defs
	#! (size_icl_functions,fun_defs) = usize fun_defs
	#! icl_sizes = make_icl_sizes
		with
			make_icl_sizes :: *{#Int}
			make_icl_sizes => {{icl_sizes.[i] \\ i<-[0..cMacroDefs-1]} & [cFunctionDefs]=size_icl_functions}
	#! (dcl_mod,modules) = modules![main_dcl_module_n]
	#! dictionary_info=dcl_mod.dcl_dictionary_info	
	# (Yes conversion_table) = old_conversions
	#! icl_to_dcl_index_table = {create_icl_to_dcl_index_table_for_kind table_size dcl_to_icl_table table_kind dictionary_info \\ table_kind<-[0..] & table_size <-: icl_sizes & dcl_to_icl_table <-: conversion_table }
	#! modules = {modules & [main_dcl_module_n].dcl_macro_conversions=Yes conversion_table.[cMacroDefs]}
	= (Yes icl_to_dcl_index_table,old_conversions,modules,fun_defs)

recompute_icl_to_dcl_index_table_for_functions No dcl_icl_conversions n_functions
	= No
recompute_icl_to_dcl_index_table_for_functions (Yes icl_to_dcl_index_table) (Yes dcl_icl_conversions) n_functions
	# icl_to_dcl_index_table_for_functions = create_icl_to_dcl_index_table_for_kind n_functions dcl_icl_conversions cFunctionDefs {n_dictionary_types=0, n_dictionary_constructors=0, n_dictionary_selectors=0}
	# icl_to_dcl_index_table = {{t\\t<-:icl_to_dcl_index_table} & [cFunctionDefs] = icl_to_dcl_index_table_for_functions}
	= Yes icl_to_dcl_index_table

create_icl_to_dcl_index_table_for_kind :: !Int !{#Int} Int DictionaryInfo -> {#Int}
create_icl_to_dcl_index_table_for_kind table_size dcl_to_icl_table table_kind dcl_dictionary_info
	# icl_to_dcl_index_table_for_kind = {createArray table_size NoIndex & [dcl_to_icl_table.[decl_index]]=decl_index \\ decl_index<- [0..size dcl_to_icl_table-1]}
	#! max_index=size icl_to_dcl_index_table_for_kind-1
	# free_position_index =  if (table_kind==cTypeDefs) (max_index+dcl_dictionary_info.n_dictionary_types)
							(if (table_kind==cSelectorDefs) (max_index+dcl_dictionary_info.n_dictionary_selectors)
							(if (table_kind==cConstructorDefs) (max_index+dcl_dictionary_info.n_dictionary_constructors)
							 max_index))
	# icl_to_dcl_index_table_for_kind = number_NoIndex_elements max_index free_position_index icl_to_dcl_index_table_for_kind
		with
			number_NoIndex_elements :: Int Int *{#Int} -> .{#Int};
			number_NoIndex_elements index free_position_index icl_to_dcl_index_table_for_kind
				| index>=0
					| icl_to_dcl_index_table_for_kind.[index]==NoIndex
						= number_NoIndex_elements (index-1) (free_position_index-1) {icl_to_dcl_index_table_for_kind & [index]=free_position_index}
						= number_NoIndex_elements (index-1) free_position_index icl_to_dcl_index_table_for_kind
					= icl_to_dcl_index_table_for_kind
	= icl_to_dcl_index_table_for_kind

renumber_member_indexes_of_class_instances No class_instances
	= class_instances
renumber_member_indexes_of_class_instances (Yes icl_to_dcl_index_table) class_instances
	= renumber_member_indexes_of_class_instances 0 class_instances
	where
		function_conversion_table = icl_to_dcl_index_table.[cFunctionDefs]

		renumber_member_indexes_of_class_instances class_inst_index class_instances
			| class_inst_index < size class_instances
				# (class_instance,class_instances) = class_instances![class_inst_index]
				# new_members = {{icl_member & ds_index=function_conversion_table.[icl_member.ds_index]} \\ icl_member<-:class_instance.ins_members}
				# class_instances = {class_instances & [class_inst_index]={class_instance & ins_members=new_members}}
				= renumber_member_indexes_of_class_instances (class_inst_index+1) class_instances
				= class_instances

renumber_members_of_gencases No gencases
	= gencases
renumber_members_of_gencases (Yes icl_to_dcl_index_table) gencases
	= renumber 0 gencases
where
	function_conversion_table = icl_to_dcl_index_table.[cFunctionDefs]
	
	renumber gencase_index gencases
		| gencase_index < size gencases
			# (gencase=:{gc_body = GCB_FunIndex icl_index}, gencases) = gencases ! [gencase_index]
			# dcl_index = function_conversion_table.[icl_index] 
			# gencase = { gencase & gc_body = GCB_FunIndex dcl_index }
			# gencases = { gencases & [gencase_index] = gencase } 
			= renumber (inc gencase_index) gencases
			= gencases	


renumber_type_fun_indices :: (Optional {{#Int}}) *{#CheckedTypeDef} -> *{#CheckedTypeDef}
renumber_type_fun_indices No type_defs
	=	type_defs
renumber_type_fun_indices (Yes conversion_table) type_defs
	# (n, type_defs) = usize type_defs
	= renumber 0 n conversion_table.[cFunctionDefs] type_defs
where
	renumber :: Int Int {# Int} *{#CheckedTypeDef} -> *{#CheckedTypeDef}
	renumber i n conversion type_defs
		| i < n
			# (type_def, type_defs) = type_defs![i]
			# icl_index = type_def.td_fun_index
			| icl_index <> NoIndex && icl_index < size conversion
				# dcl_index = conversion.[icl_index] 
				# type_def = { type_def & td_fun_index = dcl_index }
				# type_defs = { type_defs & [i] = type_def } 
				= renumber (inc i) n conversion type_defs
			// otherwise
				= renumber (inc i) n conversion type_defs
		// otherwise
			= type_defs	 

renumber_icl_definitions_as_dcl_definitions :: !(Optional {{#Int}}) !{#Int} IndexRange !Int ![Declaration] !*{#DclModule} !*CommonDefs !*{#FunDef}
																					 	-> (![Declaration],!.{#DclModule},!.CommonDefs,!*{#FunDef})
renumber_icl_definitions_as_dcl_definitions No icl_sizes icl_global_function_range main_dcl_module_n icl_decl_symbols modules cdefs fun_defs
	= (icl_decl_symbols,modules,cdefs,fun_defs)
renumber_icl_definitions_as_dcl_definitions (Yes icl_to_dcl_index_table) icl_sizes icl_global_function_range main_dcl_module_n icl_decl_symbols modules cdefs fun_defs
	# (size_icl_functions,fun_defs) = usize fun_defs
	# icl_sizes = {{icl_sizes.[i] \\ i<-[0..cMacroDefs-1]} & [cFunctionDefs]=size_icl_functions}
	# (icl_decl_symbols,cdefs) = renumber_icl_decl_symbols icl_decl_symbols cdefs
		with
			renumber_icl_decl_symbols [] cdefs
				= ([],cdefs)
			renumber_icl_decl_symbols [icl_decl_symbol : icl_decl_symbols] cdefs
				# (icl_decl_symbol,cdefs) = renumber_icl_decl_symbol icl_decl_symbol cdefs
				# (icl_decl_symbols,cdefs) = renumber_icl_decl_symbols icl_decl_symbols cdefs
				= ([icl_decl_symbol : icl_decl_symbols],cdefs)
				where
					renumber_icl_decl_symbol (Declaration icl_decl_symbol=:{decl_kind = STE_Type, decl_index}) cdefs
						# (type_def,cdefs) = cdefs!com_type_defs.[decl_index]
						# type_def = renumber_type_def type_def
						# cdefs={cdefs & com_type_defs.[decl_index]=type_def}
						= (Declaration {icl_decl_symbol & decl_index=icl_to_dcl_index_table.[cTypeDefs,decl_index]},cdefs)
						where
							renumber_type_def td=:{td_rhs = AlgType conses}
								# conses = [{cons & ds_index=icl_to_dcl_index_table.[cConstructorDefs,cons.ds_index]} \\ cons <- conses]
								= { td & td_rhs = AlgType conses}
							renumber_type_def td=:{td_rhs = RecordType rt=:{rt_constructor,rt_fields,rt_is_boxed_record}}
								# rt_constructor = {rt_constructor & ds_index=icl_to_dcl_index_table.[cConstructorDefs,rt_constructor.ds_index]}
								# rt_fields = {{field & fs_index=icl_to_dcl_index_table.[cSelectorDefs,field.fs_index]} \\ field <-: rt_fields}
								= {td & td_rhs=RecordType {rt_constructor=rt_constructor,rt_fields=rt_fields,rt_is_boxed_record=rt_is_boxed_record}}
							renumber_type_def td
								= td
					renumber_icl_decl_symbol (Declaration icl_decl_symbol=:{decl_kind = STE_Constructor, decl_index}) cdefs
						= (Declaration {icl_decl_symbol & decl_index=icl_to_dcl_index_table.[cConstructorDefs,decl_index]},cdefs)
					renumber_icl_decl_symbol (Declaration icl_decl_symbol=:{decl_kind = STE_Field _, decl_index}) cdefs
						= (Declaration {icl_decl_symbol & decl_index=icl_to_dcl_index_table.[cSelectorDefs,decl_index]},cdefs)
					renumber_icl_decl_symbol (Declaration icl_decl_symbol=:{decl_kind = STE_Member, decl_index}) cdefs
						= (Declaration {icl_decl_symbol & decl_index=icl_to_dcl_index_table.[cMemberDefs,decl_index]},cdefs)
					renumber_icl_decl_symbol (Declaration icl_decl_symbol=:{decl_kind = STE_Class, decl_index}) cdefs
						# (class_def,cdefs) = cdefs!com_class_defs.[decl_index]
						# class_members = {{class_member & ds_index=icl_to_dcl_index_table.[cMemberDefs,class_member.ds_index]} \\ class_member <-: class_def.class_members}
						# class_def = {class_def & class_members=class_members}
						# cdefs = {cdefs & com_class_defs.[decl_index] =class_def}
						= (Declaration {icl_decl_symbol & decl_index=icl_to_dcl_index_table.[cClassDefs,decl_index]},cdefs)
					renumber_icl_decl_symbol (Declaration icl_decl_symbol=:{decl_kind = STE_Instance, decl_index}) cdefs
						= (Declaration {icl_decl_symbol & decl_index=icl_to_dcl_index_table.[cInstanceDefs,decl_index]},cdefs)
					renumber_icl_decl_symbol (Declaration icl_decl_symbol=:{decl_kind = STE_Generic, decl_index}) cdefs
						= (Declaration {icl_decl_symbol & decl_index=icl_to_dcl_index_table.[cGenericDefs,decl_index]},cdefs)
					renumber_icl_decl_symbol (Declaration icl_decl_symbol=:{decl_kind = STE_GenericCase, decl_index}) cdefs
						= (Declaration {icl_decl_symbol & decl_index=icl_to_dcl_index_table.[cGenericCaseDefs,decl_index]},cdefs)
							//---> ("renumber generic case", icl_decl_symbol.decl_ident, decl_index, icl_to_dcl_index_table.[cGenericCaseDefs,decl_index])		
					renumber_icl_decl_symbol icl_decl=:(Declaration icl_decl_symbol=:{decl_kind=STE_FunctionOrMacro _, decl_index}) cdefs
//						| decl_index>=icl_global_function_range.ir_from && decl_index<icl_global_function_range.ir_to
							= (Declaration {icl_decl_symbol & decl_index=icl_to_dcl_index_table.[cFunctionDefs,decl_index]},cdefs)	
//							= (icl_decl,cdefs)
					renumber_icl_decl_symbol icl_decl_symbol cdefs
						= (icl_decl_symbol,cdefs)
	# (dcl_mod,modules) = modules![main_dcl_module_n]
	# {n_dictionary_types,n_dictionary_selectors,n_dictionary_constructors}=dcl_mod.dcl_dictionary_info
	# cdefs=reorder_common_definitions cdefs
		with
			reorder_common_definitions {com_type_defs,com_cons_defs,com_selector_defs,com_class_defs,com_member_defs,com_instance_defs,com_generic_defs,com_gencase_defs}
				# dummy_ident = {id_name="",id_info=nilPtr}
				# com_type_defs=reorder_and_enlarge_array com_type_defs n_dictionary_types icl_to_dcl_index_table.[cTypeDefs]
									{td_ident=dummy_ident,td_index= -1,td_arity=0,td_args=[],td_attrs=[],td_context=[],td_rhs=UnknownType,td_attribute=TA_None,td_pos=NoPos,td_used_types=[],
									 td_fun_index = NoIndex}
				# dummy_symbol_type={st_vars=[],st_args=[],st_args_strictness=NotStrict,st_arity=0,st_result={at_attribute=TA_None,at_type=TE},st_context=[],st_attr_vars=[],st_attr_env=[]}
				# com_selector_defs=reorder_and_enlarge_array com_selector_defs n_dictionary_selectors icl_to_dcl_index_table.[cSelectorDefs]
					 				{sd_ident=dummy_ident,sd_field=dummy_ident,sd_type=dummy_symbol_type,sd_exi_vars=[],sd_field_nr=0,sd_type_index=0,sd_type_ptr=nilPtr,sd_pos=NoPos}
				# com_cons_defs=reorder_and_enlarge_array com_cons_defs n_dictionary_constructors icl_to_dcl_index_table.[cConstructorDefs]
									{cons_ident=dummy_ident,cons_type=dummy_symbol_type,cons_arg_vars=[],cons_priority=NoPrio,cons_index= -1,cons_type_index= -1,cons_exi_vars=[],cons_type_ptr=nilPtr,cons_pos=NoPos}					
				# com_class_defs=reorder_array com_class_defs icl_to_dcl_index_table.[cClassDefs]
				# com_member_defs=reorder_array com_member_defs icl_to_dcl_index_table.[cMemberDefs]
				# com_instance_defs=reorder_array com_instance_defs icl_to_dcl_index_table.[cInstanceDefs]
				# com_generic_defs=reorder_array com_generic_defs icl_to_dcl_index_table.[cGenericDefs]
				# com_gencase_defs=reorder_array com_gencase_defs icl_to_dcl_index_table.[cGenericCaseDefs]				
				= {
					com_type_defs=com_type_defs,com_cons_defs=com_cons_defs,com_selector_defs=com_selector_defs,
					com_class_defs=com_class_defs,com_member_defs=com_member_defs,com_instance_defs=com_instance_defs,
					com_generic_defs=com_generic_defs,com_gencase_defs=com_gencase_defs
				  }
	# fun_defs = reorder_array fun_defs icl_to_dcl_index_table.[cFunctionDefs]
	= (icl_decl_symbols,modules,cdefs,fun_defs)
	where
		reorder_array array index_array
			# new_array={e\\e<-:array}
			= {new_array & [index_array.[i]]=e \\ e<-:array & i<-[0..]}

		reorder_and_enlarge_array array n_extra_elements index_array dummy_element
			# new_array=createArray (size array+n_extra_elements) dummy_element
			= {new_array & [index_array.[i]] = e \\ e<-:array & i<-[0..]}

combineDclAndIclModule ::			 ModuleKind *{#DclModule}  [Declaration] (CollectedDefinitions a b)  *{#Int}   *CheckState
	-> (!CopiedDefinitions,!Optional {#{#Int}},!*{#DclModule},![Declaration],!CollectedDefinitions a b, !*{#Int}, !*CheckState);
combineDclAndIclModule MK_Main modules icl_decl_symbols icl_definitions icl_sizes cs
	= ({ copied_type_defs = {}, copied_class_defs = {}, copied_generic_defs = {}}, No, modules, icl_decl_symbols, icl_definitions, icl_sizes, cs)
combineDclAndIclModule _ modules icl_decl_symbols icl_definitions icl_sizes cs
	#! main_dcl_module_n=cs.cs_x.x_main_dcl_module_n
	# (dcl_mod=:{dcl_declared={dcls_local},dcl_macros, dcl_sizes, dcl_common}, modules) =  modules![main_dcl_module_n]

	  cs = addGlobalDefinitionsToSymbolTable icl_decl_symbols cs

	  (moved_dcl_defs,dcl_cons_and_member_defs,conversion_table, icl_sizes, icl_decl_symbols, cs)
			= foldSt (add_to_conversion_table dcl_macros.ir_from dcl_common) dcls_local ([],[],{ createArray size NoIndex \\ size <-: dcl_sizes }, icl_sizes, icl_decl_symbols, cs)
	  (new_type_defs, new_class_defs, new_cons_defs, new_selector_defs, new_member_defs, new_generic_defs, (cop_td_indexes, cop_cd_indexes, cop_gd_indexes), conversion_table, icl_sizes, icl_decl_symbols, cs)
			= foldSt (add_dcl_definition dcl_common) moved_dcl_defs ([], [], [], [], [], [], ([], [],[]), conversion_table, icl_sizes, icl_decl_symbols, cs)
	  (new_cons_defs,new_member_defs,conversion_table,icl_sizes,icl_decl_symbols,symbol_table,errors)
	  		= foldSt (add_all_dcl_cons_and_members_to_conversion_table dcl_common) dcl_cons_and_member_defs (new_cons_defs,new_member_defs,conversion_table,icl_sizes,icl_decl_symbols,cs.cs_symbol_table,cs.cs_error)

	  new_cons_defs = reverse new_cons_defs
	  new_member_defs = reverse new_member_defs

	  symbol_table = removeDeclarationsFromSymbolTable icl_decl_symbols cGlobalScope symbol_table

	# n_dcl_classes		= dcl_sizes.[cClassDefs]
	# n_dcl_types		= dcl_sizes.[cTypeDefs]
	# n_dcl_generics 	= dcl_sizes.[cGenericDefs]
	# copied_type_defs	= mark_copied_definitions n_dcl_types	cop_td_indexes
	# copied_class_defs	= mark_copied_definitions n_dcl_classes	cop_cd_indexes
	# copied_generic_defs	= mark_copied_definitions n_dcl_generics cop_gd_indexes
	=	( 	{ copied_type_defs = copied_type_defs
			, copied_class_defs = copied_class_defs
			, copied_generic_defs = copied_generic_defs 
			}
		, Yes conversion_table
		, { modules & [main_dcl_module_n] = { dcl_mod & dcl_macro_conversions = Yes conversion_table.[cMacroDefs] }}
		, icl_decl_symbols
		, { icl_definitions
				& def_types			= my_append icl_definitions.def_types new_type_defs
				, def_constructors	= my_append icl_definitions.def_constructors new_cons_defs
				, def_selectors		= my_append icl_definitions.def_selectors new_selector_defs
				, def_classes		= my_append icl_definitions.def_classes new_class_defs
				, def_members		= my_append icl_definitions.def_members new_member_defs
				, def_generics		= my_append icl_definitions.def_generics new_generic_defs
		  }
		,  icl_sizes
		, { cs & cs_symbol_table = symbol_table, cs_error=errors }
		)
where

	mark_copied_definitions :: !Int ![Index] -> *{# Bool}
	mark_copied_definitions nr_of_defs not_to_be_checked
		# marks = createArray nr_of_defs False
		= foldSt mark_def not_to_be_checked marks
	where
		mark_def index marks = { marks & [index] = True }

	add_to_conversion_table first_macro_index dcl_common decl=:(Declaration {decl_ident=decl_ident=:{id_info},decl_kind,decl_index,decl_pos})
			(moved_dcl_defs,dcl_cons_and_member_defs, conversion_table, icl_sizes, icl_defs, cs)
		# (entry=:{ste_kind,ste_index,ste_def_level}, cs_symbol_table) = readPtr id_info cs.cs_symbol_table
		| ste_kind == STE_Empty
			# def_index = toInt decl_kind
			| def_index == cConstructorDefs || def_index == cMemberDefs
				= (moved_dcl_defs,[decl:dcl_cons_and_member_defs],conversion_table, icl_sizes, icl_defs, { cs & cs_symbol_table = cs_symbol_table })
 			| can_be_only_in_dcl def_index && not (def_index==cTypeDefs && is_abstract_type dcl_common.com_type_defs decl_index)
				# (conversion_table, icl_sizes, icl_defs, cs_symbol_table)
					= add_dcl_declaration id_info entry decl def_index decl_index (conversion_table, icl_sizes, icl_defs, cs_symbol_table)
				= ([ decl : moved_dcl_defs ],dcl_cons_and_member_defs,conversion_table, icl_sizes, icl_defs, { cs & cs_symbol_table = cs_symbol_table })
			| def_index == cMacroDefs
				# (conversion_table, icl_defs, cs_symbol_table)
					= add_macro_declaration id_info entry decl (decl_index - first_macro_index) /*decl_index*/ (conversion_table, icl_defs, cs_symbol_table)
				= (moved_dcl_defs /* [ decl : moved_dcl_defs ] */,dcl_cons_and_member_defs,conversion_table, icl_sizes, icl_defs, { cs & cs_symbol_table = cs_symbol_table })
				# cs_error = checkError "undefined in implementation module" "" (setErrorAdmin (newPosition decl_ident decl_pos) cs.cs_error)
				= (moved_dcl_defs,dcl_cons_and_member_defs,conversion_table, icl_sizes, icl_defs, { cs & cs_error = cs_error, cs_symbol_table = cs_symbol_table })
		| ste_def_level == cGlobalScope && ste_kind == decl_kind
			# def_index = toInt decl_kind
			# decl_index = if (def_index == cMacroDefs) (decl_index - first_macro_index) decl_index
			= (moved_dcl_defs,dcl_cons_and_member_defs,{ conversion_table & [def_index].[decl_index] = ste_index },  icl_sizes, icl_defs, { cs & cs_symbol_table = cs_symbol_table })
			# cs_error = checkError "conflicting definition in implementation module" "" (setErrorAdmin (newPosition decl_ident decl_pos) cs.cs_error)
			= (moved_dcl_defs,dcl_cons_and_member_defs,conversion_table, icl_sizes, icl_defs, { cs & cs_error = cs_error, cs_symbol_table = cs_symbol_table })

	can_be_only_in_dcl def_kind
		= def_kind == cTypeDefs || def_kind == cSelectorDefs || def_kind == cClassDefs || def_kind == cGenericDefs 

 	is_abstract_type com_type_defs decl_index
 		= case com_type_defs.[decl_index].td_rhs of (AbstractType _) -> True ; (AbstractSynType _ _) -> True ; _ -> False
 
	add_dcl_declaration info_ptr entry (Declaration dcl) def_index decl_index (conversion_table, icl_sizes, icl_defs, symbol_table)
		# (icl_index, icl_sizes) = icl_sizes![def_index]
		=	(	{ conversion_table & [def_index].[decl_index] = icl_index }
			,	{ icl_sizes & [def_index] = inc icl_index }
			,	[ Declaration { dcl & decl_index = icl_index } : icl_defs ]
			,	NewEntry symbol_table info_ptr dcl.decl_kind icl_index cGlobalScope entry
			)

	add_macro_declaration info_ptr entry decl=:(Declaration dcl) decl_index /*icl_index*/ (conversion_table, icl_defs, symbol_table)
		=	(	{ conversion_table & [cMacroDefs].[decl_index] = -1 /*icl_index*/ }
			,	[ decl /* Declaration { dcl & decl_index = icl_index } */ : icl_defs ]
			,	NewEntry symbol_table info_ptr dcl.decl_kind dcl.decl_index /*icl_index*/ cGlobalScope entry
			)

	add_dcl_definition {com_type_defs,com_cons_defs} dcl=:(Declaration {decl_kind = STE_Type, decl_index})
			(new_type_defs, new_class_defs, new_cons_defs, new_selector_defs, new_member_defs, new_generic_defs, (cop_td_indexes, cop_cd_indexes, cop_gd_indexes), conversion_table, icl_sizes, icl_decl_symbols, cs)
		# type_def = com_type_defs.[decl_index]
		  (new_type_defs,new_cons_defs,new_selector_defs,conversion_table,icl_sizes,icl_decl_symbols,cs) = add_type_def type_def new_type_defs new_cons_defs new_selector_defs conversion_table icl_sizes icl_decl_symbols cs
		  cop_td_indexes = [decl_index : cop_td_indexes] 
		= (new_type_defs, new_class_defs, new_cons_defs, new_selector_defs, new_member_defs, new_generic_defs, (cop_td_indexes, cop_cd_indexes, cop_gd_indexes), conversion_table, icl_sizes, icl_decl_symbols, cs)
	where
		add_type_def td=:{td_pos, td_rhs = AlgType conses} new_type_defs new_cons_defs new_selector_defs conversion_table icl_sizes icl_decl_symbols cs		
			# (conses,(new_cons_defs,conversion_table,icl_sizes,icl_decl_symbols,cs)) = copy_and_redirect_cons_symbols com_cons_defs td_pos conses (new_cons_defs,conversion_table,icl_sizes,icl_decl_symbols,cs)
			= ([ { td & td_rhs = AlgType conses} : new_type_defs ],new_cons_defs,new_selector_defs,conversion_table,icl_sizes,icl_decl_symbols,cs)
			where
				copy_and_redirect_cons_symbols com_cons_defs td_pos [cons:conses] (new_cons_defs,conversion_table,icl_sizes,icl_decl_symbols,cs)
					# (dcl_cons_index,cons,(conversion_table,icl_sizes,icl_decl_symbols,cs)) = copy_and_redirect_symbol STE_Constructor td_pos cons (conversion_table,icl_sizes,icl_decl_symbols,cs)
					# new_cons_defs = if (dcl_cons_index==(-1)) new_cons_defs [ com_cons_defs.[dcl_cons_index] : new_cons_defs ]
					# (conses,st) = copy_and_redirect_cons_symbols com_cons_defs td_pos conses (new_cons_defs,conversion_table,icl_sizes,icl_decl_symbols,cs)
					= ([cons:conses],st)
				copy_and_redirect_cons_symbols com_cons_defs td_pos [] (new_cons_defs,conversion_table,icl_sizes,icl_decl_symbols,cs)
					= ([],(new_cons_defs,conversion_table,icl_sizes,icl_decl_symbols,cs))
		add_type_def td=:{td_pos, td_rhs = RecordType rt=:{rt_constructor,rt_fields}} new_type_defs new_cons_defs new_selector_defs conversion_table icl_sizes icl_decl_symbols cs
			# (dcl_cons_index,rt_constructor,(conversion_table,icl_sizes,icl_decl_symbols,cs)) = copy_and_redirect_symbol STE_Constructor td_pos rt_constructor (conversion_table,icl_sizes,icl_decl_symbols,cs)
			# new_cons_defs = if (dcl_cons_index==(-1)) new_cons_defs [ com_cons_defs.[dcl_cons_index] : new_cons_defs ]
			# (rt_fields, cs) = redirect_field_symbols td_pos rt_fields cs
			= ([ { td & td_rhs =  RecordType { rt & rt_constructor = rt_constructor, rt_fields = rt_fields }} : new_type_defs ],new_cons_defs,new_selector_defs,conversion_table,icl_sizes,icl_decl_symbols,cs)
		add_type_def td=:{td_ident, td_pos, td_rhs = AbstractType _} new_type_defs new_cons_defs new_selector_defs conversion_table icl_sizes icl_decl_symbols cs
			# cs_error = checkError "abstract type not defined in implementation module" ""
					(setErrorAdmin (newPosition td_ident td_pos) cs.cs_error)
			= (new_type_defs,new_cons_defs,new_selector_defs,conversion_table,icl_sizes,icl_decl_symbols,{ cs & cs_error = cs_error })
		add_type_def td=:{td_ident, td_pos, td_rhs = AbstractSynType _ _} new_type_defs new_cons_defs new_selector_defs conversion_table icl_sizes icl_decl_symbols cs
			# cs_error = checkError "abstract type not defined in implementation module" ""
					(setErrorAdmin (newPosition td_ident td_pos) cs.cs_error)
			= (new_type_defs,new_cons_defs,new_selector_defs,conversion_table,icl_sizes,icl_decl_symbols,{ cs & cs_error = cs_error })
		add_type_def td new_type_defs new_cons_defs new_selector_defs conversion_table icl_sizes icl_decl_symbols cs
			= ([td : new_type_defs],new_cons_defs,new_selector_defs,conversion_table,icl_sizes,icl_decl_symbols,cs) 

		redirect_field_symbols pos fields cs
			# new_fields = { field \\ field <-: fields }
			= iFoldSt (redirect_field_symbol pos fields) 0 (size fields) (new_fields, cs)
		where
			redirect_field_symbol pos fields field_nr (new_fields, cs)
				# field = fields.[field_nr]
				  ({ste_kind,ste_index}, cs_symbol_table) = readPtr field.fs_ident.id_info cs.cs_symbol_table
				| is_field ste_kind
					= ({ new_fields & [field_nr] = { field & fs_index = ste_index }}, { cs & cs_symbol_table = cs_symbol_table })
					# cs_error = checkError "conflicting definition in implementation module" "" (setErrorAdmin (newPosition field.fs_ident pos) cs.cs_error)
					= (new_fields, { cs & cs_error = cs_error, cs_symbol_table = cs_symbol_table })

			is_field (STE_Field _)	= True
			is_field _				= False
	add_dcl_definition {com_selector_defs} dcl=:(Declaration {decl_kind = STE_Field _, decl_index})
			(new_type_defs, new_class_defs, new_cons_defs, new_selector_defs, new_member_defs, new_generic_defs, copied_defs, conversion_table, icl_sizes, icl_decl_symbols, cs)
		= (new_type_defs, new_class_defs, new_cons_defs, [ com_selector_defs.[decl_index] : new_selector_defs ], new_member_defs, new_generic_defs, copied_defs, conversion_table, icl_sizes, icl_decl_symbols, cs)
	add_dcl_definition {com_class_defs,com_member_defs} dcl=:(Declaration {decl_kind = STE_Class, decl_index, decl_pos})
			(new_type_defs, new_class_defs, new_cons_defs, new_selector_defs, new_member_defs, new_generic_defs, (cop_td_indexes, cop_cd_indexes, cop_gd_indexes), conversion_table, icl_sizes, icl_decl_symbols, cs)
		# class_def = com_class_defs.[decl_index]
		  cop_cd_indexes = [decl_index : cop_cd_indexes] 
		  (new_class_defs,new_member_defs,conversion_table,icl_sizes,icl_decl_symbols,cs) = add_class_def decl_pos class_def new_class_defs new_member_defs conversion_table icl_sizes icl_decl_symbols cs
		= (new_type_defs, new_class_defs, new_cons_defs, new_selector_defs, new_member_defs, new_generic_defs, (cop_td_indexes, cop_cd_indexes, cop_gd_indexes), conversion_table, icl_sizes, icl_decl_symbols, cs)
	  where
		add_class_def decl_pos cd=:{class_members} new_class_defs new_member_defs conversion_table icl_sizes icl_decl_symbols cs
			# (new_class_members,(new_member_defs,conversion_table,icl_sizes,icl_decl_symbols,cs)) = copy_and_redirect_member_symbols 0 com_member_defs decl_pos (new_member_defs,conversion_table,icl_sizes,icl_decl_symbols,cs)
			= ([{cd & class_members={cm \\ cm<-new_class_members}}:new_class_defs],new_member_defs,conversion_table,icl_sizes,icl_decl_symbols,cs)
			where
				copy_and_redirect_member_symbols member_index com_member_defs td_pos (new_member_defs,conversion_table,icl_sizes,icl_decl_symbols,cs)
					| member_index<size class_members
						# member=class_members.[member_index]
						# (dcl_member_index,member,(conversion_table,icl_sizes,icl_decl_symbols,cs)) = copy_and_redirect_symbol STE_Member td_pos member (conversion_table,icl_sizes,icl_decl_symbols,cs)
						# new_member_defs = if (dcl_member_index==(-1)) new_member_defs [ com_member_defs.[dcl_member_index] : new_member_defs ]
						# (members,st) = copy_and_redirect_member_symbols (member_index+1) com_member_defs td_pos (new_member_defs,conversion_table,icl_sizes,icl_decl_symbols,cs)
						= ([member:members],st)
						= ([],(new_member_defs,conversion_table,icl_sizes,icl_decl_symbols,cs))
	add_dcl_definition {com_generic_defs} dcl=:(Declaration {decl_kind = STE_Generic, decl_index, decl_pos}) 
			(new_type_defs, new_class_defs, new_cons_defs, new_selector_defs, new_member_defs, new_generic_defs, copied_defs, conversion_table, icl_sizes, icl_decl_symbols, cs)
		# generic_def = com_generic_defs.[decl_index]
		# (cop_td_indexes, cop_cd_indexes, cop_gd_indexes) = copied_defs
		# copied_defs = (cop_td_indexes, cop_cd_indexes, [decl_index:cop_gd_indexes])
		= (new_type_defs, new_class_defs, new_cons_defs, new_selector_defs, new_member_defs, [generic_def:new_generic_defs], copied_defs, conversion_table, icl_sizes, icl_decl_symbols, cs)	
	add_dcl_definition _ _ result = result

	copy_and_redirect_symbol req_kind pos ds=:{ds_ident=ds_ident=:{id_info},ds_index} (conversion_table,icl_sizes,icl_defs,cs)
		# (entry=:{ste_kind,ste_index}, cs_symbol_table) = readPtr id_info cs.cs_symbol_table
		| ste_kind == STE_Empty
			# def_index = toInt req_kind
			# (icl_index, icl_sizes) = icl_sizes![def_index]
			# conversion_table = { conversion_table & [def_index].[ds_index] = icl_index }
			# icl_sizes = { icl_sizes & [def_index] = inc icl_index }
			# icl_defs = [ Declaration { decl_ident=ds_ident,decl_index=icl_index,decl_kind=req_kind,decl_pos=pos} : icl_defs ]
			# cs_symbol_table = NewEntry cs_symbol_table id_info req_kind icl_index cGlobalScope entry
			= (ds_index,{ ds & ds_index = icl_index }, (conversion_table,icl_sizes,icl_defs,{ cs & cs_symbol_table = cs_symbol_table }))
			# cs_error = checkError "conflicting definition in implementation module" "" (setErrorAdmin (newPosition ds_ident pos) cs.cs_error)
			= (-1,{ ds & ds_index = ste_index }, (conversion_table,icl_sizes,icl_defs,{ cs & cs_error = cs_error, cs_symbol_table = cs_symbol_table }))

	add_all_dcl_cons_and_members_to_conversion_table dcl_common decl=:(Declaration {decl_ident=decl_ident=:{id_info},decl_kind=STE_Constructor,decl_index,decl_pos}) (new_cons_defs,new_member_defs,conversion_table,icl_sizes,icl_defs,symbol_table,errors)
		| conversion_table.[cConstructorDefs].[decl_index]>=0
			= (new_cons_defs,new_member_defs,conversion_table,icl_sizes,icl_defs,symbol_table,errors)
		# (entry=:{ste_kind,ste_index}, symbol_table) = readPtr id_info symbol_table
		| ste_kind == STE_Empty
			# (conversion_table,icl_sizes,icl_defs,symbol_table)
				= add_dcl_declaration id_info entry decl cConstructorDefs decl_index (conversion_table,icl_sizes,icl_defs,symbol_table)
			= ([dcl_common.com_cons_defs.[decl_index] : new_cons_defs],new_member_defs,conversion_table,icl_sizes,icl_defs,symbol_table,errors)
			# errors = checkErrorWithIdentPos (newPosition decl_ident decl_pos) " constructor already defined" errors
			= (new_cons_defs,new_member_defs,conversion_table,icl_sizes,icl_defs,symbol_table,errors)
	add_all_dcl_cons_and_members_to_conversion_table dcl_common decl=:(Declaration {decl_ident=decl_ident=:{id_info},decl_kind=STE_Member,decl_index,decl_pos}) (new_cons_defs,new_member_defs,conversion_table,icl_sizes,icl_defs,symbol_table,errors)
		| conversion_table.[cMemberDefs].[decl_index]>=0
			= (new_cons_defs,new_member_defs,conversion_table,icl_sizes,icl_defs,symbol_table,errors)
		# (entry=:{ste_kind,ste_index}, symbol_table) = readPtr id_info symbol_table
		| ste_kind == STE_Empty
			# (conversion_table,icl_sizes,icl_defs,symbol_table)
				= add_dcl_declaration id_info entry decl cMemberDefs decl_index (conversion_table,icl_sizes,icl_defs,symbol_table)
			= (new_cons_defs,[dcl_common.com_member_defs.[decl_index] :  new_member_defs],conversion_table,icl_sizes,icl_defs,symbol_table,errors)
			# errors = checkErrorWithIdentPos (newPosition decl_ident decl_pos) " member already defined" errors
			= (new_cons_defs,new_member_defs,conversion_table,icl_sizes,icl_defs,symbol_table,errors)

	my_append front []
		= front
	my_append front back
		= front ++ back

replace_icl_macros_by_dcl_macros :: ModuleKind IndexRange [Declaration] *{#DclModule} *CheckState -> (![Declaration],!*{#DclModule},!*CheckState);
replace_icl_macros_by_dcl_macros MK_Main icl_macro_index_range decls dcl_modules cs 
	= (decls,dcl_modules,cs)
replace_icl_macros_by_dcl_macros _ {ir_from=first_icl_macro_index,ir_to=end_icl_macro_index} decls dcl_modules cs
	#! main_dcl_module_n=cs.cs_x.x_main_dcl_module_n
	#  ({dcl_macros={ir_from=first_macro_n},dcl_macro_conversions},dcl_modules) = dcl_modules![main_dcl_module_n]
	| case dcl_macro_conversions of No -> True ; _ -> False
		= (decls,dcl_modules,cs)
	# (Yes dcl_to_icl_table) = dcl_macro_conversions
	# macro_renumber_table = create_icl_to_dcl_index_table_for_macros dcl_to_icl_table
		with
			create_icl_to_dcl_index_table_for_macros :: !{#Int} -> {#Int}
			create_icl_to_dcl_index_table_for_macros dcl_to_icl_table
				# macro_renumber_table = createArray (end_icl_macro_index-first_icl_macro_index) NoIndex
				# size_dcl_to_icl_table = size dcl_to_icl_table
				# macro_renumber_table = fill_macro_renumber_table 0 macro_renumber_table
					with
					fill_macro_renumber_table decl_index macro_renumber_table
						| decl_index<size_dcl_to_icl_table
							# i=dcl_to_icl_table.[decl_index]
							| i>=first_icl_macro_index && i<end_icl_macro_index
								= fill_macro_renumber_table (decl_index+1) {macro_renumber_table & [i-first_icl_macro_index]=decl_index}
								= fill_macro_renumber_table (decl_index+1) macro_renumber_table // for a macro that only occurs in the dcl module and not in the icl module
							= macro_renumber_table
				= macro_renumber_table

	# decls = replace_icl_macros_by_dcl_macros decls
		with
		replace_icl_macros_by_dcl_macros [decl=:(Declaration decl_record=:{decl_kind=STE_FunctionOrMacro _,decl_index}):decls]
			# dcl_n=macro_renumber_table.[decl_index-first_icl_macro_index]
			# decls = replace_icl_macros_by_dcl_macros decls;
			| decl_index>=first_icl_macro_index && decl_index<end_icl_macro_index && dcl_n<>NoIndex
//				| trace_tn ("replace_icl_macros_by_dcl_macros "+++toString decl_record.decl_ident+++" "+++toString decl_index+++" "+++toString (first_macro_n+dcl_n))
				= [Declaration {decl_record & decl_kind=STE_DclMacroOrLocalMacroFunction [], decl_index=first_macro_n+dcl_n} : decls]
				= [decl : decls]
		replace_icl_macros_by_dcl_macros [decl:decls]
			= [decl : replace_icl_macros_by_dcl_macros decls]
		replace_icl_macros_by_dcl_macros []
			= []
	= (decls,dcl_modules,cs)

(<=<) infixl 
(<=<) state fun :== fun state 

checkDclModules imports_of_icl_mod dcl_modules icl_functions macro_defs heaps cs=:{cs_symbol_table}
	#! nr_of_dcl_modules
			= size dcl_modules
	# (bitvect, dependencies, dcl_modules, cs_symbol_table)
			= iFoldSt add_dependencies 0 nr_of_dcl_modules
					(bitvectCreate (nr_of_dcl_modules+1), gimme_a_strict_array_type (createArray (nr_of_dcl_modules+1) []),
						dcl_modules, cs_symbol_table)
	  index_of_icl_module
	  		= nr_of_dcl_modules
	  (dependencies_of_icl_mod, (_, cs_symbol_table))
			= mapFilterYesSt get_opt_dependency imports_of_icl_mod (bitvect, cs_symbol_table)
	  (directly_imported_dcl_modules,dcl_modules)
			= mapSt (\mod_index dcl_modules -> dcl_modules![mod_index].dcl_name.id_name)
					dependencies_of_icl_mod dcl_modules
	  dependencies
	  		= { dependencies & [index_of_icl_module] = dependencies_of_icl_mod }
	  module_dag
	  		= { dag_nr_of_nodes = nr_of_dcl_modules+1, dag_get_children = select dependencies }
	  components
	  		= partitionateDAG module_dag [cs.cs_x.x_main_dcl_module_n,index_of_icl_module]
//	| False--->("biggest component:", m axList (map length components))
//		= undef
	# (nr_of_components, component_numbers)
	  		= getComponentNumbers components module_dag.dag_nr_of_nodes
	  reversed_dag1
	  		= reverseDAG module_dag
	  reversed_dag
			= { module_dag & dag_get_children = select reversed_dag1 }
	  super_components
	  		= groupify reversed_dag component_numbers nr_of_components
	  		// module i is imported by components with _component_ numbers super_components.[i]
	  components_array
	  		= gimme_a_strict_array_type { component \\ component <- components }
	  (expl_imp_symbols_and_indices_in_components, (dcl_modules, cs_symbol_table))
	   		= mapSt (get_expl_imp_symbols_of_component imports_of_icl_mod) components (dcl_modules, cs_symbol_table)
	  (expl_imp_symbols_in_components, expl_imp_indices)
	  		= unzip expl_imp_symbols_and_indices_in_components
	  expl_imp_infos
	  		= { { ExplImpInfo expl_imp_symbol ikhEmpty
	  			  \\ expl_imp_symbol <- expl_imp_symbols_in_component
	  			}
	  			\\ expl_imp_symbols_in_component<-expl_imp_symbols_in_components }
	  		// eii_declaring_modules will be updated later
	  cs
	  		= { cs & cs_symbol_table = cs_symbol_table }
	  nr_of_icl_component
	  		= component_numbers.[index_of_icl_module]
	  (_, expl_imp_infos, dcl_modules, icl_functions, macro_defs, heaps, cs)
	  		= unsafeFold2St (checkDclComponent components_array super_components) (reverse expl_imp_indices) (reverse components)
					(nr_of_components-1, expl_imp_infos, dcl_modules, icl_functions, macro_defs, heaps, cs)
//	# cs = cs--->"------------------------------------"
	= (nr_of_icl_component, hd expl_imp_indices!!nr_of_icl_component, directly_imported_dcl_modules,
		expl_imp_infos, dcl_modules, icl_functions, macro_defs, heaps, cs)
  where
	add_dependencies mod_index (bitvect, dependencies, dcl_modules, cs_symbol_table)
		// all i: not bitvect.[i]
		| mod_index==cPredefinedModuleIndex
			= (bitvect, dependencies, dcl_modules, cs_symbol_table)
		# ({dcl_name}, dcl_modules)
				= dcl_modules![mod_index]
		  ({ste_kind, ste_index}, cs_symbol_table)
				= readPtr dcl_name.id_info cs_symbol_table
		= case ste_kind of
			STE_Module {mod_imports}
				# (dependencies_of_mod, (bitvect, cs_symbol_table))
						= mapFilterYesSt get_opt_dependency mod_imports (bitvect, cs_symbol_table)
				  (bitvect, cs_symbol_table)
				  		= foldSt set_to_false mod_imports (bitvect, cs_symbol_table)
				-> (bitvect, { dependencies & [mod_index] = dependencies_of_mod }, dcl_modules, cs_symbol_table)
			STE_ClosedModule
				-> (bitvect, { dependencies & [mod_index] = [] }, dcl_modules, cs_symbol_table)

	get_opt_dependency {import_module} (already_visited, cs_symbol_table)
		# ({ste_index}, cs_symbol_table)
				= readPtr import_module.id_info cs_symbol_table
		| bitvectSelect ste_index already_visited
			= (No, (already_visited, cs_symbol_table))
		= (Yes ste_index, (bitvectSet ste_index already_visited, cs_symbol_table))

	set_to_false :: (Import x) !(!*LargeBitvect, !u:SymbolTable) -> (!.LargeBitvect, !u:SymbolTable)
	set_to_false {import_module} (bitvect, cs_symbol_table)
		#! ste_index
				= (sreadPtr import_module.id_info cs_symbol_table).ste_index
		= (bitvectReset ste_index bitvect, cs_symbol_table)

	get_expl_imp_symbols_of_component imports_of_icl_mod component (dcl_modules, cs_symbol_table)
		# (expl_imp_symbols, _, expl_imp_indices, dcl_modules, cs_symbol_table)
				= foldSt (get_expl_imp_symbols_of_module imports_of_icl_mod) component ([], 0, [], dcl_modules, cs_symbol_table)
		  cs_symbol_table
				= foldSt restoreHeap expl_imp_symbols cs_symbol_table
		= ((reverse expl_imp_symbols, reverse expl_imp_indices), (dcl_modules, cs_symbol_table))
		
	get_expl_imp_symbols_of_module imports_of_icl_mod mod_index (expl_imp_symbols_accu, nr_of_expl_imp_symbols, expl_imp_indices_accu, dcl_modules, cs_symbol_table)
		#! siz = size dcl_modules
		# (mod_imports, dcl_modules, cs_symbol_table)
				= get_mod_imports (mod_index==siz) imports_of_icl_mod dcl_modules cs_symbol_table
		  (expl_imp_symbols_accu, nr_of_expl_imp_symbols, expl_imp_indices, cs_symbol_table)
				= foldSt get_expl_imp_symbols mod_imports (expl_imp_symbols_accu, nr_of_expl_imp_symbols, [], cs_symbol_table)
		= (expl_imp_symbols_accu, nr_of_expl_imp_symbols, [expl_imp_indices:expl_imp_indices_accu],dcl_modules, cs_symbol_table)
	  where
		get_mod_imports is_icl_mod=:False _ dcl_modules cs_symbol_table
			# ({dcl_name}, dcl_modules) =  dcl_modules![mod_index]
			  ({ste_kind}, cs_symbol_table) = readPtr dcl_name.id_info cs_symbol_table
			= case ste_kind of
				STE_Module {mod_imports}
					-> (mod_imports, dcl_modules, cs_symbol_table)
				STE_ClosedModule
					-> ([], dcl_modules, cs_symbol_table)
		get_mod_imports _ imports_of_icl_mod dcl_modules cs_symbol_table
		 	= (imports_of_icl_mod, dcl_modules, cs_symbol_table)

	get_expl_imp_symbols {import_module, import_symbols, import_file_position} (expl_imp_symbols_accu, nr_of_expl_imp_symbols, expl_imp_indices_accu, cs_symbol_table)
		# (expl_imp_symbols_accu, nr_of_expl_imp_symbols, expl_imp_indices, cs_symbol_table)
				= foldSt get_expl_imp_symbol import_symbols (expl_imp_symbols_accu, nr_of_expl_imp_symbols, [], cs_symbol_table)
		  ({ste_index}, cs_symbol_table) = readPtr import_module.id_info cs_symbol_table
		= (expl_imp_symbols_accu, nr_of_expl_imp_symbols, [(ste_index, import_file_position, expl_imp_indices):expl_imp_indices_accu], cs_symbol_table)

	get_expl_imp_symbol imp_decl state
		= get_symbol imp_decl (get_ident imp_decl) state
	where
		get_ident :: !ImportDeclaration -> Ident
		get_ident (ID_Function {ii_ident})						= ii_ident
		get_ident (ID_Class {ii_ident} _)						= ii_ident
		get_ident (ID_Type {ii_ident} _)						= ii_ident
		get_ident (ID_Record {ii_ident} _)						= ii_ident
		get_ident (ID_Instance class_ident instance_ident _)	= instance_ident

	get_symbol imp_decl ident=:{id_info} (expl_imp_symbols_accu, nr_of_expl_imp_symbols, expl_imp_indices_accu, cs_symbol_table)
		# (ste, cs_symbol_table) = readPtr id_info cs_symbol_table
		= case ste.ste_kind of
			STE_ExplImpSymbol expl_imp_symbols_nr
				# ini = { ini_symbol_nr = expl_imp_symbols_nr, ini_imp_decl = imp_decl }
				-> (expl_imp_symbols_accu, nr_of_expl_imp_symbols, [ini:expl_imp_indices_accu], cs_symbol_table)
			STE_Empty
				# cs_symbol_table = writePtr id_info { ste & ste_kind = STE_ExplImpSymbol nr_of_expl_imp_symbols, ste_previous = ste } cs_symbol_table
				  ini = { ini_symbol_nr = nr_of_expl_imp_symbols, ini_imp_decl = imp_decl }
				-> ([ident:expl_imp_symbols_accu], nr_of_expl_imp_symbols+1,[ini:expl_imp_indices_accu], cs_symbol_table)				

checkDclComponent :: !{![Int]} !{![Int]} ![[(Index, Position, [ImportNrAndIdents])]] ![Int] 
				!(!Int, !*ExplImpInfos, !*{# DclModule},!*{# FunDef},!*{#*{#FunDef}},!*Heaps,!*CheckState)
			->   (!Int, !*ExplImpInfos, !.{# DclModule},!.{# FunDef},!*{#*{#FunDef}},!.Heaps,!.CheckState)
checkDclComponent components_array super_components expl_imp_indices mod_indices
		(component_nr, expl_imp_infos, dcl_modules, icl_functions, macro_defs, heaps, cs=:{cs_x})
	| not cs.cs_error.ea_ok || hd mod_indices==size dcl_modules // the icl module!
		= (component_nr-1, expl_imp_infos, dcl_modules, icl_functions, macro_defs, heaps, cs)
//	| False--->("checkDclComponent", mod_indices, size dcl_modules) = undef	
	# ({dcl_name=dcl_name_of_first_mod_in_component}, dcl_modules)
			= dcl_modules![hd mod_indices]
	  ({ste_kind}, cs_symbol_table)
			= readPtr dcl_name_of_first_mod_in_component.id_info cs.cs_symbol_table
	  cs
	  		= { cs & cs_symbol_table = cs_symbol_table }
	= case ste_kind of
		STE_ClosedModule
			// this component has been already checked during the previous icl module's compilation
			# (expl_imp_infos, dcl_modules, cs_symbol_table)
					= foldSt (just_update_expl_imp_info components_array super_components) mod_indices (expl_imp_infos, dcl_modules, cs.cs_symbol_table)
 			-> (component_nr-1, expl_imp_infos, dcl_modules, icl_functions, macro_defs, heaps,
 				{ cs & cs_symbol_table = cs_symbol_table })
		STE_Module _
			# is_on_cycle
					= case mod_indices of
						[_]	-> False
						_	-> True
			  cs_error
			  		= fold2St check_whether_module_imports_itself expl_imp_indices mod_indices cs.cs_error
			  cs = { cs & cs_error = cs_error }
			| not cs.cs_error.ea_ok
				-> (component_nr-1, expl_imp_infos, dcl_modules, icl_functions, macro_defs, heaps, cs)
			# (expl_imp_infos, dcl_modules, cs)
			  		= case is_on_cycle of
			  			True
			  				-> collect_expl_imp_info component_nr mod_indices (expl_imp_infos, dcl_modules, cs)
			  			False
			  				-> (expl_imp_infos, dcl_modules, cs)
			#! nr_of_modules
					= size dcl_modules
			# modules_in_component_set = foldSt bitvectSet mod_indices (bitvectCreate nr_of_modules)
			  (dcl_imported_module_numbers, dcl_modules)
			  		= foldSt (\imports_per_module state
					  			-> foldSt compute_used_module_nrs imports_per_module state)
					  		expl_imp_indices
			  				(foldSt addNr mod_indices EndNumbers, dcl_modules)
			  expl_imp_indices_ikh
					= fold2St (ikhInsert` False) mod_indices expl_imp_indices ikhEmpty
			  (expl_imp_info, expl_imp_infos)
			  		= replace expl_imp_infos component_nr cDummyArray
			  (imports, (dcl_modules, _, expl_imp_info, cs))
					= mapSt (solveExplicitImports expl_imp_indices_ikh modules_in_component_set) mod_indices
							(dcl_modules, bitvectCreate nr_of_modules, expl_imp_info, cs)
			| not cs.cs_error.ea_ok
				-> (component_nr-1, expl_imp_infos, dcl_modules, icl_functions, macro_defs, heaps, cs)
			# imports_ikh
			  		= fold2St (ikhInsert` False) mod_indices imports ikhEmpty
			  		// maps the module indices of all modules in the actual component to all explicit
			  		// imports of that module
		
			  (dcls_common_defs, (dcl_modules, cs))
				= mapSt (createCommonDefinitionsWithinComponent is_on_cycle) mod_indices (dcl_modules, cs)

			  (afterwards_info, (expl_imp_infos, dcl_modules, icl_functions, macro_defs, heaps, cs))
				= map2St (checkDclModuleWithinComponent dcl_imported_module_numbers component_nr is_on_cycle modules_in_component_set super_components imports_ikh)
								mod_indices dcls_common_defs (expl_imp_infos, dcl_modules, icl_functions, macro_defs, heaps, cs)

			| not cs.cs_error.ea_ok
				-> (component_nr-1, expl_imp_infos, dcl_modules, icl_functions, macro_defs, heaps, cs)

			# (dcl_modules, icl_functions,macro_defs,heaps, cs)
					= case is_on_cycle of
						False
							-> (dcl_modules, icl_functions, macro_defs,heaps, cs)
						True
							# (dcl_modules, icl_functions, macro_defs,hp_expression_heap, cs)
									= fold2St check_expl_imp_completeness_of_dcl_mod_within_non_trivial_component
											mod_indices imports
											(dcl_modules, icl_functions,macro_defs,heaps.hp_expression_heap, cs)
							-> (dcl_modules, icl_functions, macro_defs,{ heaps & hp_expression_heap = hp_expression_heap }, cs)	
			  (dcl_modules, heaps, cs)
			   		= fold2St checkInstancesOfDclModule mod_indices afterwards_info (dcl_modules, heaps, cs)
			-> (component_nr-1, expl_imp_infos, dcl_modules, icl_functions, macro_defs, heaps, cs)
  where
	check_whether_module_imports_itself expl_imp_indices_for_module mod_index cs_error
		= foldSt (check_that mod_index) expl_imp_indices_for_module cs_error
	  where
		check_that mod_index (imported_mod_index, position, _) cs_error
			| mod_index==imported_mod_index
				= checkErrorWithIdentPos (newPosition import_ident position)
						"a dcl module cannot import from itself" cs_error
			= cs_error
	
	collect_expl_imp_info component_nr mod_indices (expl_imp_infos, dcl_modules, cs)
		# (changed_symbols, (expl_imp_infos, cs_symbol_table))
				= markExplImpSymbols component_nr (expl_imp_infos, cs.cs_symbol_table)
		  (expl_imp_infos, dcl_modules, cs_symbol_table)
		  		= foldSt collect_expl_imp_info_per_module mod_indices (expl_imp_infos, dcl_modules, cs_symbol_table)
		  cs_symbol_table
		  		= foldSt restoreHeap changed_symbols cs_symbol_table
		= (expl_imp_infos, dcl_modules, { cs & cs_symbol_table = cs_symbol_table })

	collect_expl_imp_info_per_module mod_index (expl_imp_infos, dcl_modules, cs_symbol_table)
		# (dcls_local_for_import, dcl_modules)
				= dcl_modules![mod_index].dcl_declared.dcls_local_for_import
		  (dcl_modules, expl_imp_infos, cs_symbol_table)
				= foldlArraySt (update_expl_imp_for_marked_local_symbol mod_index)
						dcls_local_for_import (dcl_modules, expl_imp_infos, cs_symbol_table)
		= (expl_imp_infos, dcl_modules, cs_symbol_table)
	
	just_update_expl_imp_info components_array super_components mod_index (expl_imp_infos, dcl_modules, cs_symbol_table)
		# ({dcls_local_for_import, dcls_import}, dcl_modules) = dcl_modules![mod_index].dcl_declared
		= updateExplImpInfoForCachedModule super_components.[mod_index] mod_index dcls_import dcls_local_for_import expl_imp_infos dcl_modules cs_symbol_table

	check_expl_imp_completeness_of_dcl_mod_within_non_trivial_component mod_index {si_explicit} (dcl_modules, icl_functions,macro_defs,hp_expression_heap, cs)
		# ({dcl_declared}, dcl_modules) = dcl_modules![mod_index]
		  ({dcls_local_for_import, dcls_import}) = dcl_declared
		  cs = addDeclarationsOfDclModToSymbolTable mod_index dcls_local_for_import dcls_import cs
		  (dcl_modules, icl_functions,macro_defs,hp_expression_heap, cs=:{cs_symbol_table})
		  		= checkExplicitImportCompleteness si_explicit dcl_modules icl_functions macro_defs hp_expression_heap cs
		  cs_symbol_table
		  		= removeImportsAndLocalsOfModuleFromSymbolTable dcl_declared cs.cs_symbol_table
		= (dcl_modules, icl_functions,macro_defs,hp_expression_heap, { cs & cs_symbol_table = cs_symbol_table })
	
compute_used_module_nrs (mod_index, _, _) (mod_nr_accu, dcl_modules)
	| inNumberSet mod_index mod_nr_accu
		= (mod_nr_accu, dcl_modules)
	# ({dcl_imported_module_numbers}, dcl_modules)
			= dcl_modules![mod_index]
	= (addNr mod_index (numberSetUnion dcl_imported_module_numbers mod_nr_accu),
		 dcl_modules)

createCommonDefinitionsWithinComponent is_on_cycle mod_index (dcl_modules, cs=:{cs_symbol_table})
	# (dcl_mod=:{dcl_name}, dcl_modules) = dcl_modules![mod_index]
	  (mod_entry, cs_symbol_table) = readPtr dcl_name.id_info cs_symbol_table
	  ({ ste_kind = STE_Module mod, ste_index }) = mod_entry
	  cs = { cs & cs_symbol_table = cs_symbol_table}
	# dcl_common = createCommonDefinitions mod.mod_defs
	#! first_type_index = size dcl_common.com_type_defs		
	# dcl_common = {dcl_common & com_class_defs = number_class_dictionaries 0 dcl_common.com_class_defs first_type_index}
		with
			number_class_dictionaries class_index class_defs index_type
				| class_index < size class_defs
					# class_defs = { class_defs & [class_index].class_dictionary.ds_index = index_type }
					= number_class_dictionaries (inc class_index) class_defs (inc index_type)
					= class_defs
	| not is_on_cycle
		= (dcl_common, (dcl_modules, cs))
		# (dcl_common,dcl_common2) = copy_common_defs dcl_common
		# dcl_modules = {dcl_modules & [mod_index].dcl_common=dcl_common2}
		= (dcl_common, (dcl_modules, cs))
		with
			copy_common_defs :: !*CommonDefs -> (!*CommonDefs,!*CommonDefs)
			copy_common_defs {com_type_defs,com_cons_defs,com_selector_defs,com_class_defs,com_member_defs,com_instance_defs,com_generic_defs,com_gencase_defs}
				# (type_defs1,type_defs2) = arrayCopy com_type_defs
				# (cons_defs1,cons_defs2) = arrayCopy com_cons_defs
				# (selector_defs1,selector_defs2) = arrayCopy com_selector_defs
				# (class_defs1,class_defs2) = arrayCopy com_class_defs
				# (member_defs1,member_defs2) = arrayCopy com_member_defs
				# (instance_defs1,instance_defs2) = arrayCopy com_instance_defs
				# (generic_defs1,generic_defs2) = arrayCopy com_generic_defs
				# (gencase_defs1,gencase_defs2) = arrayCopy com_gencase_defs
				= ({com_type_defs=type_defs1,com_cons_defs=cons_defs1,com_selector_defs=selector_defs1,com_class_defs=class_defs1,com_member_defs=member_defs1,com_instance_defs=instance_defs1,com_generic_defs=generic_defs1,com_gencase_defs=gencase_defs1},
				   {com_type_defs=type_defs2,com_cons_defs=cons_defs2,com_selector_defs=selector_defs2,com_class_defs=class_defs2,com_member_defs=member_defs2,com_instance_defs=instance_defs2,com_generic_defs=generic_defs2,com_gencase_defs=gencase_defs2})

checkDclModuleWithinComponent dcl_imported_module_numbers component_nr is_on_cycle modules_in_component_set super_components imports_ikh
		mod_index dcl_common
		(expl_imp_infos, dcl_modules, icl_functions, macro_defs, heaps, cs=:{cs_symbol_table})
	# ({dcl_name}, dcl_modules) = dcl_modules![mod_index]
	  (mod_entry, cs_symbol_table) = readPtr dcl_name.id_info cs_symbol_table
	  ({ ste_kind = STE_Module mod, ste_index }) = mod_entry
	  cs = { cs & cs_symbol_table = writePtr dcl_name.id_info { mod_entry & ste_kind = STE_ClosedModule } cs_symbol_table}
	# {mod_ident,mod_defs={def_macro_indices,def_funtypes}} = mod
	= checkDclModule2 dcl_imported_module_numbers super_components.[mod_index] imports_ikh component_nr is_on_cycle modules_in_component_set
		 mod_ident dcl_common def_macro_indices def_funtypes ste_index expl_imp_infos dcl_modules icl_functions macro_defs heaps cs

renumber_icl_module :: ModuleKind IndexRange IndexRange IndexRange IndexRange Index Int {#Int} (Optional {#{#Int}}) IndexRange  *{#FunDef}  *CommonDefs  [Declaration]  *{#DclModule} *ErrorAdmin
												 -> (![IndexRange],![IndexRange],![IndexRange], ![IndexRange], !Int,!Index,!IndexRange,!*{#FunDef},!*CommonDefs,![Declaration],!*{#DclModule}, *ErrorAdmin);
renumber_icl_module mod_type icl_global_function_range icl_instance_range icl_generic_range icl_type_fun_range nr_of_functions main_dcl_module_n icl_sizes dcl_conversions def_macro_indices icl_functions icl_common local_defs dcl_modules error
	# (optional_icl_to_dcl_index_table,optional_old_conversion_table,dcl_modules,icl_functions)
		= create_icl_to_dcl_index_table mod_type icl_sizes main_dcl_module_n dcl_conversions dcl_modules icl_functions
	# (dcl_mod, dcl_modules) = dcl_modules![main_dcl_module_n]
	# icl_functions = add_dummy_specialized_functions mod_type dcl_mod icl_functions
	# class_instances = icl_common.com_instance_defs
	# gencase_defs = icl_common.com_gencase_defs
	# type_defs = icl_common.com_type_defs
	# (dcl_icl_conversions, class_instances, gencase_defs, type_defs, error)
		= add_dcl_instances_to_conversion_table 
			optional_old_conversion_table nr_of_functions dcl_mod class_instances gencase_defs type_defs error
	| not error.ea_ok
		= ([],[],[],[], 0,0,def_macro_indices,icl_functions,
			{icl_common & com_instance_defs=class_instances, com_gencase_defs=gencase_defs,
			 com_type_defs=type_defs},
			local_defs,dcl_modules,error)
	# (n_functions,icl_functions) = usize icl_functions
	# optional_icl_to_dcl_index_table = recompute_icl_to_dcl_index_table_for_functions optional_icl_to_dcl_index_table dcl_icl_conversions n_functions
	# class_instances = renumber_member_indexes_of_class_instances optional_icl_to_dcl_index_table class_instances
	# gencase_defs = renumber_members_of_gencases optional_icl_to_dcl_index_table gencase_defs
	# type_defs = renumber_type_fun_indices optional_icl_to_dcl_index_table type_defs

	# icl_common = 
		{ icl_common 
		& com_instance_defs = class_instances
		, com_gencase_defs = gencase_defs
		, com_type_defs = type_defs
		}

	# (local_defs,dcl_modules,icl_common,icl_functions)
		= renumber_icl_definitions_as_dcl_definitions optional_icl_to_dcl_index_table icl_sizes icl_global_function_range main_dcl_module_n local_defs dcl_modules icl_common icl_functions
	# (dcl_mod, dcl_modules) = dcl_modules![main_dcl_module_n]

	#! dcl_instances = dcl_mod.dcl_instances
	#! n_exported_global_functions=dcl_mod.dcl_sizes.[cFunctionDefs]
	#! first_not_exported_global_function_index = size dcl_mod.dcl_functions

	# n_dcl_instances = dcl_instances.ir_to-dcl_instances.ir_from
	#! dcl_specials = dcl_mod.dcl_specials
	# n_dcl_specials = dcl_specials.ir_to-dcl_specials.ir_from

	# dcl_gencases = dcl_mod.dcl_gencases
	# n_dcl_gencases = dcl_gencases.ir_to-dcl_gencases.ir_from

	# dcl_type_funs = dcl_mod.dcl_type_funs
	# n_dcl_type_funs = dcl_type_funs.ir_to-dcl_type_funs.ir_from

	# local_functions_index_offset = n_dcl_instances + n_dcl_gencases + n_dcl_specials + n_dcl_type_funs

	# dcl_mod = case dcl_mod of
			dcl_mod=:{dcl_macro_conversions=Yes conversion_table}
				# new_macro_conversions = {if (old_icl_macro_index==(-1)) old_icl_macro_index (old_icl_macro_index+local_functions_index_offset) \\ old_icl_macro_index<-:conversion_table}
				-> {dcl_mod & dcl_macro_conversions=Yes new_macro_conversions}
			dcl_mod
				-> dcl_mod
	# dcl_modules = {dcl_modules & [main_dcl_module_n]=dcl_mod}

	# n_global_functions=icl_global_function_range.ir_to
	# n_not_exported_global_functions=n_global_functions-n_exported_global_functions
	# end_not_exported_global_functions_range=first_not_exported_global_function_index+n_not_exported_global_functions
	# icl_global_functions_ranges = [{ir_from=icl_global_function_range.ir_from,ir_to=n_exported_global_functions},
									 {ir_from=first_not_exported_global_function_index,ir_to=end_not_exported_global_functions_range}
									 ]
	# first_macro_index = def_macro_indices.ir_from+local_functions_index_offset
	# end_macro_indexes = def_macro_indices.ir_to+local_functions_index_offset
	# def_macro_indices={ir_from=first_macro_index,ir_to=end_macro_indexes}	

	# n_dcl_specials_and_gencases = n_dcl_specials + n_dcl_gencases
	# not_exported_instance_range = 
		{ ir_from=icl_instance_range.ir_from + n_dcl_instances + n_dcl_specials_and_gencases + n_dcl_type_funs
		, ir_to = icl_instance_range.ir_to + n_dcl_specials_and_gencases + n_dcl_type_funs
		}
	# icl_instances_ranges = [dcl_instances, not_exported_instance_range]	

	# not_exported_generic_range = 
		{ ir_from =icl_generic_range.ir_from + n_dcl_specials_and_gencases + n_dcl_type_funs
		, ir_to = icl_generic_range.ir_to + n_dcl_specials + n_dcl_type_funs
		}
	# icl_generic_ranges = [dcl_gencases, not_exported_generic_range]

	# n_not_exported_type_funs
		=	(icl_type_fun_range.ir_to - icl_type_fun_range.ir_from) - n_dcl_type_funs
	# not_exported_type_fun_range = 
		{ ir_from = not_exported_generic_range.ir_to
		, ir_to = not_exported_generic_range.ir_to + n_not_exported_type_funs
		}

	# icl_type_fun_ranges = [dcl_type_funs, not_exported_type_fun_range]

	# dcl_global = {ir_from=icl_global_function_range.ir_from,ir_to=n_exported_global_functions}
	# dcl_ranges = 
		[dcl_global, dcl_instances, dcl_gencases, dcl_type_funs, dcl_specials]
	# icl_global = {ir_from=first_not_exported_global_function_index,ir_to=end_not_exported_global_functions_range}
	# icl_ranges = 
		[icl_global, not_exported_instance_range, not_exported_generic_range]

	= (icl_global_functions_ranges, icl_instances_ranges, icl_generic_ranges, icl_type_fun_ranges, n_exported_global_functions,local_functions_index_offset,def_macro_indices,icl_functions,icl_common,local_defs,dcl_modules, error)
	where
		add_dummy_specialized_functions MK_Main dcl_mod icl_functions
			= icl_functions
		add_dummy_specialized_functions _ {dcl_specials={ir_from,ir_to}} icl_functions
			# n_specials = ir_to-ir_from
			| n_specials==0
				= icl_functions
				# dummy_function = {fun_ident={id_name="",id_info=nilPtr},fun_arity= -1,fun_priority=NoPrio,fun_body=NoBody,fun_type=No,fun_pos=NoPos,fun_kind=FK_Unknown,fun_lifted=0,fun_info=EmptyFunInfo}
				= arrayPlusList icl_functions [dummy_function \\ i<-[0..n_specials-1]]

		add_dcl_instances_to_conversion_table :: (Optional {#{#Int}}) !Index !DclModule !*{# ClassInstance} !*{# GenericCaseDef} !*{# CheckedTypeDef} *ErrorAdmin
			-> (!*Optional *{#Index},!*{# ClassInstance}, !*{# GenericCaseDef}, !*{# CheckedTypeDef},*ErrorAdmin)
 		add_dcl_instances_to_conversion_table optional_old_conversion_table first_free_index
 				dcl_mod=:{dcl_specials,dcl_functions,dcl_common,dcl_macro_conversions,dcl_type_funs}
 												icl_instances icl_gencases icl_type_defs error
			= case dcl_macro_conversions of
				Yes _
					# (new_conversion_table, icl_instances, icl_gencases, icl_type_defs, error)
					  		= build_conversion_table_for_instances_of_dcl_mod dcl_specials first_free_index optional_old_conversion_table
					  				dcl_functions dcl_common.com_instance_defs icl_instances dcl_common.com_gencase_defs icl_gencases
					  				dcl_common.com_type_defs icl_type_defs error
					-> (Yes new_conversion_table,icl_instances, icl_gencases, icl_type_defs, error)
				No
					-> (No, icl_instances, icl_gencases, icl_type_defs, error)
		where
			build_conversion_table_for_instances_of_dcl_mod dcl_specials=:{ir_from,ir_to} first_free_index optional_old_conversion_table dcl_functions
					dcl_instances icl_instances dcl_gencases icl_gencases dcl_types icl_type_defs error
				#! nr_of_dcl_functions = size dcl_functions
				# (Yes old_conversion_table) = optional_old_conversion_table
				#! dcl_instances_table = old_conversion_table.[cInstanceDefs]
				#! dcl_gencase_table = old_conversion_table.[cGenericCaseDefs]
				#! dcl_function_table = old_conversion_table.[cFunctionDefs]
				#! dcl_type_table =  old_conversion_table.[cTypeDefs]
				#! new_table = { createArray nr_of_dcl_functions NoIndex & [i] = icl_index \\ icl_index <-: dcl_function_table & i <- [0..] }
				#! index_diff = first_free_index - ir_from
				#! new_table = { new_table & [i] = i + index_diff \\ i <- [ir_from .. ir_to - 1] }
				#! (new_table, icl_instances, error) 
					= build_conversion_table_for_instances 0 dcl_instances dcl_instances_table icl_instances new_table error
				#! (new_table, icl_gencases, error) 
					= build_conversion_table_for_generic_cases 0 dcl_gencases dcl_gencase_table icl_gencases new_table error
				#! (new_table, icl_type_defs)
					= fill_conversion_table_for_type_funs 0 dcl_types icl_type_defs dcl_type_table new_table
				= (new_table, icl_instances, icl_gencases, icl_type_defs, error)

			build_conversion_table_for_generic_cases dcl_index dcl_gencases gencase_table icl_gencases new_table error
				| dcl_index < size gencase_table
					#! (new_table, icl_gencases, error)
						= build_conversion_table_for_generic_case dcl_index dcl_gencases gencase_table icl_gencases new_table error
					= build_conversion_table_for_generic_cases (inc dcl_index) dcl_gencases gencase_table icl_gencases new_table error
					= (new_table, icl_gencases, error)					
			build_conversion_table_for_generic_case dcl_index dcl_gencases gencase_table icl_gencases new_table error
				#! icl_index = gencase_table.[dcl_index]	
				#! (icl_gencase, icl_gencases) = icl_gencases ! [icl_index]
				#! dcl_gencase = dcl_gencases.[dcl_index]
				# (GCB_FunIndex icl_fun) = icl_gencase.gc_body 				
				# (GCB_FunIndex dcl_fun) = dcl_gencase.gc_body
				#! new_table = { new_table & [dcl_fun] = icl_fun } 								
				= (new_table, icl_gencases, error)	

			build_conversion_table_for_instances dcl_class_inst_index dcl_instances class_instances_table icl_instances new_table error
				| dcl_class_inst_index < size class_instances_table
					# icl_index = class_instances_table.[dcl_class_inst_index]				
					# (icl_instance, icl_instances) = icl_instances![icl_index]
					  dcl_members = dcl_instances.[dcl_class_inst_index].ins_members
					  icl_members = icl_instance.ins_members
					| size dcl_members == size icl_members
						# new_table = build_conversion_table_for_instances_of_members 0 dcl_members icl_members new_table
						= build_conversion_table_for_instances (inc dcl_class_inst_index) dcl_instances class_instances_table icl_instances new_table error
						# error = checkErrorWithIdentPos (newPosition icl_instance.ins_ident icl_instance.ins_pos) "incorrect number of members specified" error
						= build_conversion_table_for_instances (inc dcl_class_inst_index) dcl_instances class_instances_table icl_instances new_table error
					= (new_table, icl_instances,error)
			
			build_conversion_table_for_instances_of_members mem_index dcl_members icl_members new_table
				| mem_index < size dcl_members
					# dcl_member = dcl_members.[mem_index]
					# icl_member = icl_members.[mem_index]
					# new_table = {new_table & [dcl_member.ds_index] = icl_member.ds_index}
					= build_conversion_table_for_instances_of_members (inc mem_index) dcl_members icl_members new_table
					= new_table

			fill_conversion_table_for_type_funs dcl_type_index dcl_types icl_type_defs type_conversions new_table
				| dcl_type_index >= size dcl_types
					= (new_table, icl_type_defs)
				# dcl_type_fun_index = dcl_types.[dcl_type_index].td_fun_index
				| dcl_type_fun_index == NoIndex || dcl_types.[dcl_type_index].td_fun_index == NoIndex
					= fill_conversion_table_for_type_funs (inc dcl_type_index) dcl_types icl_type_defs type_conversions new_table
				// sanity check ...
				| dcl_type_index < 0 // == NoIndex
					=	abort ("check, fill_conversion_table_for_type_funs: too small dcl conversion "
									+++ dcl_types.[dcl_type_index].td_ident.id_name)
				| dcl_type_index >= size type_conversions
					=	abort ("check, fill_conversion_table_for_type_funs: too large dcl conversion "
									+++ dcl_types.[dcl_type_index].td_ident.id_name)
				# icl_type_index = type_conversions.[dcl_type_index]
				// sanity check ...
				| icl_type_index < 0 // == NoIndex
					=	abort ("check, fill_conversion_table_for_type_funs: no icl type index "
									+++ dcl_types.[dcl_type_index].td_ident.id_name)
				| icl_type_index >= size icl_type_defs
					=	abort ("check, fill_conversion_table_for_type_funs: too large icl type index "
									+++ dcl_types.[dcl_type_index].td_ident.id_name)
				// ... sanity check
				# (icl_type_fun_index,icl_type_defs) = icl_type_defs![icl_type_index].td_fun_index
				| dcl_type_fun_index == NoIndex
					// sanity check ...
					| icl_type_fun_index <> NoIndex
						=	abort ("check, fill_conversion_table_for_type_funs: indices mismatch icl ")
									//	+++ icl_types.[icl_type_index].td_ident.id_name)
					// ... sanity check
					= fill_conversion_table_for_type_funs (inc dcl_type_index) dcl_types icl_type_defs type_conversions new_table
				// otherwise
					// sanity check ...
					| icl_type_fun_index == NoIndex
						=	abort ("check, fill_conversion_table_for_type_funs: indices mismatch dcl ")
									//	+++ dcl_types.[dcl_type_index].td_ident.id_name)
					| new_table.[dcl_type_fun_index] <> NoIndex
						=	abort ("check, fill_conversion_table_for_type_funs: entry already occupied ")
									//	+++ dcl_types.[dcl_type_index].td_ident.id_name)
					/// ... sanity check
					# new_table = {new_table & [dcl_type_fun_index] = icl_type_fun_index}
					= fill_conversion_table_for_type_funs (inc dcl_type_index) dcl_types icl_type_defs type_conversions new_table

checkModule :: !Bool !ScannedModule !IndexRange ![FunDef] !Int !(Optional ScannedModule) ![ScannedModule] !{#DclModule} !*{#*{#FunDef}} !*PredefinedSymbols !*SymbolTable !*File !*Heaps
	-> (!Bool, *IclModule, *{#DclModule}, *{!Group}, !*{#*{#FunDef}},!Int, !*Heaps, !*PredefinedSymbols, !*SymbolTable, *File, [String])

checkModule support_dynamics {mod_defs,mod_ident,mod_type,mod_imports,mod_imported_objects,mod_foreign_exports,mod_modification_time} icl_global_function_range fun_defs dcl_module_n_in_cache 
	optional_dcl_mod scanned_modules dcl_modules cached_dcl_macros predef_symbols symbol_table err_file heaps
	# nr_of_cached_modules = size dcl_modules
	# (optional_pre_def_mod,predef_symbols)
		= case nr_of_cached_modules of
			0	# (predef_mod,predef_symbols) = buildPredefinedModule predef_symbols
				-> (Yes predef_mod,predef_symbols)
			_	-> (No,predef_symbols)
	# (nr_of_functions,first_inst_index,first_gen_inst_index, local_defs,icl_functions,macro_defs,init_dcl_modules,main_dcl_module_n,cdefs,sizes,cs)
		= check_module1 mod_defs icl_global_function_range fun_defs optional_dcl_mod optional_pre_def_mod scanned_modules dcl_modules cached_dcl_macros dcl_module_n_in_cache predef_symbols symbol_table err_file
	# icl_instance_range = {ir_from = first_inst_index, ir_to = first_gen_inst_index}
	# icl_generic_range = {ir_from = first_gen_inst_index, ir_to = nr_of_functions}
	= check_module2 mod_ident mod_modification_time mod_imported_objects mod_imports mod_foreign_exports mod_type icl_global_function_range icl_instance_range icl_generic_range nr_of_cached_modules optional_pre_def_mod local_defs support_dynamics icl_functions macro_defs init_dcl_modules cdefs sizes heaps cs

check_module1 cdefs icl_global_function_range fun_defs optional_dcl_mod optional_pre_def_mod scanned_modules dcl_modules cached_dcl_macros dcl_module_n_in_cache predef_symbols symbol_table err_file
	# error = {ea_file = err_file, ea_loc = [], ea_ok = True }

	  first_inst_index = length fun_defs
	  (inst_fun_defs, def_instances) = convert_class_instances cdefs.def_instances first_inst_index	  

	  first_gen_inst_index = first_inst_index + length inst_fun_defs
	  (gen_inst_fun_defs, def_generic_cases) = convert_generic_instances cdefs.def_generic_cases first_gen_inst_index

	  icl_functions = { next_fun \\ next_fun <- fun_defs ++ inst_fun_defs ++ gen_inst_fun_defs}

	  cdefs = { cdefs & def_instances = def_instances, def_generic_cases = def_generic_cases }
	#! nr_of_functions = size icl_functions

	# sizes_and_local_defs = collectCommonfinitions cdefs
	  (icl_functions, sizes_and_local_defs) = collectGlobalFunctions cFunctionDefs icl_global_function_range.ir_from icl_global_function_range.ir_to icl_functions sizes_and_local_defs

	  (icl_functions, (sizes, local_defs)) = collectMacros cdefs.def_macro_indices icl_functions sizes_and_local_defs

	# nr_of_cached_modules = size dcl_modules

	  main_dcl_module_n = if (dcl_module_n_in_cache<>NoIndex) dcl_module_n_in_cache nr_of_cached_modules

	  cs = { cs_symbol_table = symbol_table, cs_predef_symbols = predef_symbols, cs_error = error, cs_x= {x_needed_modules=0,x_main_dcl_module_n=main_dcl_module_n, x_check_dynamic_types = False}}
	  
	  (scanned_modules,macro_defs,cs) = add_dcl_module_predef_module_and_modules_to_symbol_table optional_dcl_mod optional_pre_def_mod scanned_modules nr_of_cached_modules cs
	  macro_defs = make_macro_def_array cached_dcl_macros macro_defs

	  init_new_dcl_modules = gimme_a_strict_array_type { initialDclModule scanned_module module_n \\ scanned_module <- scanned_modules & module_n<-[nr_of_cached_modules..]}

	  init_dcl_modules = {	if (i<size dcl_modules) 
	  							dcl_modules.[i]
		  						init_new_dcl_modules.[i-size dcl_modules] 
	  						\\ i<-[0..size dcl_modules+size init_new_dcl_modules-1]}
	= (nr_of_functions,first_inst_index,first_gen_inst_index,local_defs,icl_functions,macro_defs,init_dcl_modules,main_dcl_module_n,cdefs,sizes,cs)

	where
		add_dcl_module_predef_module_and_modules_to_symbol_table (Yes dcl_mod) optional_predef_mod modules mod_index cs
			# (mod_sizes_and_defs,dcl_macro_defs,cs) = add_module_to_symbol_table dcl_mod mod_index cs
			  (mods, macro_defs, cs) = add_predef_module_and_modules_to_symbol_table optional_predef_mod modules (inc mod_index) cs
			= ([mod_sizes_and_defs:mods], [dcl_macro_defs:macro_defs], cs)
		add_dcl_module_predef_module_and_modules_to_symbol_table No optional_predef_mod modules mod_index cs
			= add_predef_module_and_modules_to_symbol_table optional_predef_mod modules mod_index cs
		
		add_predef_module_and_modules_to_symbol_table (Yes predef_mod) modules mod_index cs
			# (mod_sizes_and_defs,dcl_macro_defs,cs) = add_module_to_symbol_table predef_mod mod_index cs
			  (mods, macro_defs, cs) = add_modules_to_symbol_table modules (inc mod_index) cs
			= ([mod_sizes_and_defs:mods],[dcl_macro_defs:macro_defs], cs)
		add_predef_module_and_modules_to_symbol_table No modules mod_index cs
			= add_modules_to_symbol_table modules mod_index cs
	
		add_modules_to_symbol_table [] mod_index cs=:{cs_predef_symbols,cs_symbol_table,cs_x}
			# (cs_predef_symbols, cs_symbol_table) = (cs_predef_symbols, cs_symbol_table) 
					<=< adjust_predefined_module_symbol PD_StdArray
					<=< adjust_predefined_module_symbol PD_StdEnum
					<=< adjust_predefined_module_symbol PD_StdBool
					<=< adjust_predefined_module_symbol PD_StdStrictLists
					<=< adjust_predefined_module_symbol PD_StdDynamic
					<=< adjust_predefined_module_symbol PD_StdGeneric
					<=< adjust_predefined_module_symbol PD_CleanTypes
					<=< adjust_predefined_module_symbol PD_StdMisc										
					<=< adjust_predefined_module_symbol PD_PredefinedModule
			= ([], [], { cs & cs_predef_symbols = cs_predef_symbols, cs_symbol_table = cs_symbol_table})
		where
			adjust_predefined_module_symbol :: !Index !(!*PredefinedSymbols, !*SymbolTable) -> (!*PredefinedSymbols, !*SymbolTable)
			adjust_predefined_module_symbol predef_index (pre_def_symbols, symbol_table)
				# (mod_symb, pre_def_symbols) = pre_def_symbols![predef_index]
				# (mod_entry, symbol_table) = readPtr predefined_idents.[predef_index].id_info symbol_table
				= case mod_entry.ste_kind of
					STE_Module _
						-> ({ pre_def_symbols & [predef_index] = { mod_symb & pds_module = cs_x.x_main_dcl_module_n, pds_def =  mod_entry.ste_index }}, symbol_table)
					_
						-> (pre_def_symbols, symbol_table)

		add_modules_to_symbol_table [mod : mods] mod_index cs
			# (mod_sizes_and_defs,dcl_macro_defs,cs) = add_module_to_symbol_table mod mod_index cs
			  (mods, macro_defs, cs) = add_modules_to_symbol_table mods (inc mod_index) cs
			= ([mod_sizes_and_defs:mods],[dcl_macro_defs:macro_defs], cs)

		add_module_to_symbol_table mod=:{mod_defs} mod_index cs=:{cs_symbol_table, cs_error}
			# def_instances	= convert_class_instances mod_defs.def_instances
			# def_generic_cases = convert_generic_instances mod_defs.def_generic_cases
			  mod_defs = { mod_defs & def_instances = def_instances, def_generic_cases = def_generic_cases }
			  sizes_and_defs = collectFunctionTypes mod_defs.def_funtypes (collectCommonfinitions mod_defs)
			  
			  dcl_macro_defs={macro_def \\ macro_def<-mod_defs.def_macros}
			  (dcl_macro_defs, (sizes, defs)) = collectDclMacros mod_defs.def_macro_indices dcl_macro_defs sizes_and_defs
			  
  			  mod = { mod & mod_defs = mod_defs }
		   	  (cs_symbol_table, cs_error) = addDefToSymbolTable cGlobalScope mod_index mod.mod_ident (STE_Module mod) cs_symbol_table cs_error
		   	= ((mod,sizes,defs),dcl_macro_defs,{ cs & cs_symbol_table = cs_symbol_table, cs_error = cs_error })
		where
			convert_class_instances :: ![ParsedInstance a] -> [ClassInstance]
			convert_class_instances [pi : pins]
				= [ParsedInstanceToClassInstance pi {} : convert_class_instances pins]
			convert_class_instances []
				= []
				
			convert_generic_instances :: ![GenericCaseDef] -> [GenericCaseDef]	
			convert_generic_instances gcs 
				// TODO: check what to do here
				= gcs //[{ gc & gc_body = gc.gc_body } \\ gc <- gcs]

		convert_class_instances :: .[ParsedInstance FunDef] Int -> (!.[FunDef],!.[ClassInstance]);
		convert_class_instances [pi=:{pi_members} : pins] next_fun_index
			# ins_members = sort pi_members
			  (member_symbols, next_fun_index) = determine_indexes_of_members ins_members next_fun_index
			  (next_fun_defs, cins) =  convert_class_instances pins next_fun_index
			= (ins_members ++ next_fun_defs, [ParsedInstanceToClassInstance pi { member \\ member <- member_symbols} : cins])
		convert_class_instances [] next_fun_index
			= ([], [])

		convert_generic_instances :: !.[GenericCaseDef] !Int -> (!.[FunDef], !.[GenericCaseDef])
		convert_generic_instances [gc=:{gc_ident, gc_body=GCB_FunDef fun_def} : gcs] next_fun_index
			# (fun_defs, gcs) =  convert_generic_instances gcs (inc next_fun_index)
			# gc = { gc & gc_body = GCB_FunIndex next_fun_index } 
			= ([fun_def : fun_defs], [gc:gcs])
				//---> ("convert generic case: user defined function", gc.gc_ident, gc.gc_type_cons, next_fun_index)
		convert_generic_instances [gc=:{gc_ident,gc_pos, gc_type_cons, gc_body=GCB_None} : gcs] next_fun_index
			# (fun_defs, gcs) =  convert_generic_instances gcs (inc next_fun_index)
			# fun_def = 
 				{ fun_ident = genericIdentToFunIdent gc_ident gc_type_cons
 				, fun_arity = 0
 				, fun_priority = NoPrio
 				, fun_body = GeneratedBody
 				, fun_type = No
 				, fun_pos = gc_pos
 				, fun_kind = FK_Unknown
 				, fun_lifted = 0
 				, fun_info = EmptyFunInfo
 				}
			# gc = { gc & gc_body = GCB_FunIndex next_fun_index } 
			= ([fun_def:fun_defs], [gc:gcs])
				//---> ("convert generic case: function to derive ", gc.gc_ident, gc.gc_type_cons, next_fun_index)
		convert_generic_instances [] next_fun_index 
			= ([], [])
			
		determine_indexes_of_members [{fun_ident,fun_arity}:members] next_fun_index
			#! (member_symbols, last_fun_index) = determine_indexes_of_members members (inc next_fun_index)
			= ([{ds_ident = fun_ident, ds_index = next_fun_index, ds_arity = fun_arity} : member_symbols], last_fun_index)
		determine_indexes_of_members [] next_fun_index
			= ([], next_fun_index)

  		make_macro_def_array :: *{#*{#FunDef}} *[*{#FunDef}] -> *{#*{#FunDef}}
  		make_macro_def_array cached_dcl_macros macro_defs
  			#! size_cached_dcl_macros=size cached_dcl_macros
  			#! n_modules=length macro_defs+size_cached_dcl_macros
  			# a={{} \\ i<-[0..n_modules-1]}
  			# a=move_cached_macros_to_macro_def_array 0 size_cached_dcl_macros {} cached_dcl_macros a
  			= fill_macro_def_array size_cached_dcl_macros macro_defs a
		where
	  		move_cached_macros_to_macro_def_array :: Int Int !*{#FunDef} !*{#*{#FunDef}} !*{#*{#FunDef}} -> *{#*{#FunDef}}
	  		move_cached_macros_to_macro_def_array i size_cached_dcl_macros empty_array cached_dcl_macros a
	  			| i==size_cached_dcl_macros
	  				= a
	  				# (cached_macros,cached_dcl_macros) = replace cached_dcl_macros i empty_array
	  				# (empty_array,a) = replace a i cached_macros
	  				= move_cached_macros_to_macro_def_array (i+1) size_cached_dcl_macros empty_array cached_dcl_macros a
	  				
	  		fill_macro_def_array i [] a
	  			= a
	  		fill_macro_def_array i [dcl_macro_defs:macro_defs] a
	  			= fill_macro_def_array (i+1) macro_defs {a & [i]=dcl_macro_defs}

check_module2 :: Ident {#Char} [.ImportedObject] .[Import ImportDeclaration] [ParsedForeignExport] .ModuleKind !.IndexRange !.IndexRange !.IndexRange !Int 
				(Optional (Module a)) [Declaration] Bool *{#FunDef} *{#*{#FunDef}} *{#DclModule} (CollectedDefinitions ClassInstance IndexRange)
				*{#.Int} *Heaps *CheckState
			-> (!Bool,.IclModule,!.{#DclModule},.{!Group},!*{#*{#FunDef}},!Int,!.Heaps,!.{#PredefinedSymbol},!.Heap SymbolTableEntry,!.File,[String]);
check_module2 mod_ident mod_modification_time mod_imported_objects mod_imports mod_foreign_exports mod_type icl_global_function_range icl_instance_range icl_generic_range nr_of_cached_modules optional_pre_def_mod local_defs support_dynamics icl_functions macro_defs init_dcl_modules cdefs sizes heaps cs
	# (main_dcl_module_n,cs)=cs!cs_x.x_main_dcl_module_n
		
	  (copied_dcl_defs, dcl_conversions, dcl_modules, local_defs, cdefs, icl_sizes, cs)
	  		= combineDclAndIclModule mod_type init_dcl_modules local_defs cdefs sizes cs
	| not cs.cs_error.ea_ok
		= (False, abort "evaluated error 1 (check.icl)", {}, {}, {}, cs.cs_x.x_main_dcl_module_n,heaps, cs.cs_predef_symbols, cs.cs_symbol_table, cs.cs_error.ea_file, [])

	# icl_common = createCommonDefinitions cdefs
	
	  (dcl_modules, icl_functions, macro_defs, heaps, cs)
		= check_predefined_module optional_pre_def_mod dcl_modules icl_functions macro_defs heaps cs

	  (nr_of_icl_component, expl_imp_indices, directly_imported_dcl_modules, 
	   expl_imp_info, dcl_modules, icl_functions, macro_defs, heaps, cs)
	  		= checkDclModules mod_imports dcl_modules icl_functions macro_defs heaps cs
	| not cs.cs_error.ea_ok
		= (False, abort "evaluated error 2 (check.icl)", {}, {}, {}, cs.cs_x.x_main_dcl_module_n,heaps, cs.cs_predef_symbols, cs.cs_symbol_table, cs.cs_error.ea_file, [])


	# cs_symbol_table = cs.cs_symbol_table
	# cs_predef_symbols = cs.cs_predef_symbols
	# hp_var_heap = heaps.hp_var_heap
	# (icl_type_fun_range, dcl_modules, icl_functions, icl_common,
						cs_predef_symbols, hp_var_heap, cs_symbol_table)
		=	if support_dynamics
				(addTypeFunctions mod_ident nr_of_cached_modules dcl_modules
					icl_functions icl_common
					cs_predef_symbols hp_var_heap cs_symbol_table)
				({ir_from=0,ir_to=0}, dcl_modules, icl_functions, icl_common,
						cs_predef_symbols, hp_var_heap, cs_symbol_table)
	# cs = {cs & cs_symbol_table=cs_symbol_table, cs_predef_symbols=cs_predef_symbols}
	# heaps = {heaps & hp_var_heap=hp_var_heap}


	# (nr_of_functions, icl_functions) = usize icl_functions

	# def_macro_indices=cdefs.def_macro_indices
	# (icl_global_functions_ranges,icl_instances_ranges, icl_generic_ranges,icl_type_fun_ranges, n_exported_global_functions,local_functions_index_offset,def_macro_indices,icl_functions,icl_common,local_defs,dcl_modules, error)
		= renumber_icl_module mod_type icl_global_function_range icl_instance_range icl_generic_range icl_type_fun_range nr_of_functions main_dcl_module_n icl_sizes dcl_conversions def_macro_indices icl_functions icl_common local_defs dcl_modules cs.cs_error
	| not error.ea_ok
		= (False, abort "evaluated error 3 (check.icl)", {}, {}, {}, cs.cs_x.x_main_dcl_module_n,heaps, cs.cs_predef_symbols, cs.cs_symbol_table, error.ea_file, [])

	# (imported_module_numbers_of_main_dcl_mod, dcl_modules) = dcl_modules![main_dcl_module_n].dcl_imported_module_numbers
	  (imported_module_numbers, dcl_modules)
	  		= foldSt compute_used_module_nrs expl_imp_indices (addNr cPredefinedModuleIndex imported_module_numbers_of_main_dcl_mod, dcl_modules)
	 
	  cs = { cs & cs_error=error,cs_x.x_needed_modules = 0 }
	
	  (nr_of_modules, dcl_modules)	= usize dcl_modules

	  (dcl_macros, dcl_modules) = dcl_modules![main_dcl_module_n].dcl_macros

	  expl_imp_indices_ikh = ikhInsert` False nr_of_modules expl_imp_indices ikhEmpty

	  modules_in_component_set = bitvectCreate nr_of_modules
	  
	  (imports, (dcl_modules, _, _, cs))
			= solveExplicitImports expl_imp_indices_ikh modules_in_component_set nr_of_modules
									(dcl_modules, bitvectCreate nr_of_modules, expl_imp_info.[nr_of_icl_component], cs)

	  imports_ikh = ikhInsert` False nr_of_modules imports ikhEmpty
	  		// maps the module indices of all modules in the actual component to all explicit
	  		// imports of that module

	  (local_defs,dcl_modules,cs) = replace_icl_macros_by_dcl_macros mod_type def_macro_indices local_defs dcl_modules cs 

	  cs = addGlobalDefinitionsToSymbolTable local_defs cs

	  (dcls_import_list, dcl_modules, cs)
	  		= addImportedSymbolsToSymbolTable nr_of_modules (Yes dcl_macros) modules_in_component_set imports_ikh dcl_modules cs

	  (dcl_modules, icl_functions,macro_defs,hp_expression_heap, cs)
			= checkExplicitImportCompleteness imports.si_explicit dcl_modules icl_functions macro_defs heaps.hp_expression_heap cs

	  heaps	= { heaps & hp_expression_heap=hp_expression_heap }

	  icl_imported = { el \\ el<-dcls_import_list }
	  
	  (_,icl_common, dcl_modules, heaps=:{hp_var_heap, hp_type_heaps}, cs)
	  		= checkCommonDefinitions (Yes (copied_dcl_defs, nr_of_cached_modules)) main_dcl_module_n icl_common dcl_modules heaps cs
				
	  (instance_types, icl_common, dcl_modules, hp_var_heap, hp_type_heaps, cs)
	  		= checkInstances main_dcl_module_n icl_common dcl_modules hp_var_heap hp_type_heaps cs
	  		  	
	  heaps = { heaps & hp_type_heaps = hp_type_heaps, hp_var_heap = hp_var_heap }

	  e_info = { ef_type_defs = icl_common.com_type_defs, ef_selector_defs = icl_common.com_selector_defs, ef_class_defs = icl_common.com_class_defs, 
	  			  ef_cons_defs = icl_common.com_cons_defs, ef_member_defs = icl_common.com_member_defs, ef_generic_defs = icl_common.com_generic_defs,
	  			  ef_modules = dcl_modules, ef_macro_defs=macro_defs, ef_is_macro_fun = False }

	# (icl_functions, e_info, heaps, cs) = checkAndPartitionateIclMacros main_dcl_module_n def_macro_indices local_functions_index_offset icl_functions e_info heaps cs
	  (icl_functions, e_info, heaps, cs) = checkGlobalFunctionsInRanges icl_global_functions_ranges main_dcl_module_n local_functions_index_offset icl_functions e_info heaps cs

	  cs = check_start_rule mod_type mod_ident icl_global_functions_ranges cs

	  (icl_functions, e_info, heaps, cs) 
	  	= checkGlobalFunctionsInRanges icl_generic_ranges main_dcl_module_n local_functions_index_offset icl_functions e_info heaps cs

	  (icl_functions, e_info, heaps, cs)
	  	= checkInstanceBodies icl_instances_ranges local_functions_index_offset icl_functions e_info heaps cs

	  (icl_functions, e_info, heaps, cs) 
	  	= checkGlobalFunctionsInRanges icl_type_fun_ranges main_dcl_module_n local_functions_index_offset icl_functions e_info heaps cs

	  (foreign_exports,icl_functions,cs) = checkForeignExports mod_foreign_exports icl_global_functions_ranges icl_functions cs

	  cs = check_needed_modules_are_imported mod_ident ".icl" cs
	  {cs_symbol_table, cs_predef_symbols, cs_error,cs_x } = cs

	  (icl_functions, hp_type_heaps, cs_error)
	  	= foldSt checkSpecifiedInstanceType instance_types (icl_functions, heaps.hp_type_heaps, cs_error)
	  	  
	  heaps = { heaps & hp_type_heaps = hp_type_heaps }
	  
	  cs_symbol_table = removeDeclarationsFromSymbolTable local_defs cGlobalScope cs_symbol_table

	  cs_symbol_table
			= foldlArraySt removeImportedSymbolsFromSymbolTable icl_imported cs_symbol_table

	  dcl_modules = e_info.ef_modules
	  
	| cs_error.ea_ok
		# {hp_var_heap,hp_type_heaps=hp_type_heaps=:{th_vars},hp_expression_heap} = heaps

		# class_instances = icl_common.com_instance_defs

		  (icl_specials,dcl_modules, icl_functions, var_heap, th_vars, expr_heap)
				= collect_specialized_functions_in_dcl_module mod_type nr_of_functions main_dcl_module_n dcl_modules icl_functions hp_var_heap th_vars hp_expression_heap

		  icl_functions = copy_instance_types instance_types icl_functions

		  (dcl_modules, class_instances, icl_functions, cs_predef_symbols)
		  		= adjust_instance_types_of_array_functions_in_std_array_icl dcl_modules class_instances icl_functions main_dcl_module_n cs_predef_symbols

		  icl_common	= { icl_common & com_type_defs = e_info.ef_type_defs, com_selector_defs = e_info.ef_selector_defs, com_class_defs = e_info.ef_class_defs,
										 com_cons_defs = e_info.ef_cons_defs, com_member_defs = e_info.ef_member_defs,
										 com_generic_defs = e_info.ef_generic_defs, com_instance_defs = class_instances }	  			  

		  local_function_indices = {ir_from=icl_global_function_range.ir_to+local_functions_index_offset,
		  							ir_to=def_macro_indices.ir_from}
		  icl_function_indices = {	ifi_global_function_indices = icl_global_functions_ranges,
		 							ifi_local_function_indices = local_function_indices,
		  					  		ifi_instance_indices = icl_instances_ranges, ifi_specials_indices = icl_specials,
		  				  	 		ifi_gencase_indices = icl_generic_ranges, ifi_type_function_indices = icl_type_fun_ranges }

		  icl_mod	= { icl_name = mod_ident, icl_functions = icl_functions, icl_function_indices = icl_function_indices,
		  				icl_common = icl_common, icl_import = icl_imported, icl_imported_objects = mod_imported_objects,
		  				icl_foreign_exports = foreign_exports, icl_used_module_numbers = imported_module_numbers,
		  				icl_copied_from_dcl = copied_dcl_defs, icl_modification_time = mod_modification_time }

		  heaps = { heaps & hp_var_heap = var_heap, hp_expression_heap = expr_heap, hp_type_heaps = {hp_type_heaps & th_vars = th_vars}}
		  (main_dcl_module, dcl_modules) = dcl_modules![main_dcl_module_n]

		  (icl_mod, macro_defs, heaps, cs_error)
		  		= compareDefImp main_dcl_module_n main_dcl_module n_exported_global_functions icl_mod e_info.ef_macro_defs heaps cs_error

		# (predef_symbols_for_transform, cs_predef_symbols) = get_predef_symbols_for_transform cs_predef_symbols
		  (groups, icl_functions, macro_defs, var_heap, expr_heap, cs_symbol_table, cs_error)
		  		= partitionateAndLiftFunctions (icl_global_functions_ranges++icl_instances_ranges++icl_generic_ranges++icl_type_fun_ranges)
		  				main_dcl_module_n predef_symbols_for_transform icl_mod.icl_functions macro_defs
									  			heaps.hp_var_heap heaps.hp_expression_heap cs_symbol_table cs_error

		# heaps = {heaps & hp_var_heap=var_heap,hp_expression_heap=expr_heap}
		# icl_mod = {icl_mod & icl_functions=icl_functions}

		= (cs_error.ea_ok, icl_mod, dcl_modules, groups, macro_defs, cs_x.x_main_dcl_module_n, heaps, cs_predef_symbols, cs_symbol_table, cs_error.ea_file, directly_imported_dcl_modules)
		# icl_common = { icl_common & com_type_defs = e_info.ef_type_defs, com_selector_defs = e_info.ef_selector_defs, com_class_defs = e_info.ef_class_defs,
			  	 					  com_cons_defs = e_info.ef_cons_defs, com_member_defs = e_info.ef_member_defs, com_generic_defs = e_info.ef_generic_defs }

		  icl_function_indices = {	ifi_global_function_indices = icl_global_functions_ranges,
		 							ifi_local_function_indices = {ir_from=0,ir_to=0},
		  					  		ifi_instance_indices = icl_instances_ranges,
		  					  		ifi_specials_indices = {ir_from = nr_of_functions, ir_to = nr_of_functions},
		  				  	 		ifi_gencase_indices = icl_generic_ranges, ifi_type_function_indices = icl_type_fun_ranges }

		  icl_mod		= { icl_name = mod_ident, icl_functions = icl_functions, icl_function_indices = icl_function_indices,
		  					icl_common = icl_common, icl_import = icl_imported, icl_imported_objects = mod_imported_objects,
		  					icl_foreign_exports = foreign_exports, icl_used_module_numbers = imported_module_numbers,
		  					icl_copied_from_dcl = copied_dcl_defs, icl_modification_time = mod_modification_time }
		= (False, icl_mod, dcl_modules, {}, {}, cs_x.x_main_dcl_module_n,heaps, cs_predef_symbols, cs_symbol_table, cs_error.ea_file, directly_imported_dcl_modules)
	where
		check_start_rule mod_kind mod_ident icl_global_functions_ranges cs=:{cs_symbol_table,cs_x}
			# ({ste_kind, ste_index}, cs_symbol_table) = readPtr predefined_idents.[PD_Start].id_info cs_symbol_table
			  cs = { cs & cs_symbol_table = cs_symbol_table }
			= case ste_kind of
				STE_FunctionOrMacro _
					| index_in_ranges ste_index icl_global_functions_ranges
						-> { cs & cs_predef_symbols.[PD_Start] = { pds_def = ste_index, pds_module = cs_x.x_main_dcl_module_n }}
					where
						index_in_ranges index [{ir_from, ir_to}:ranges]
							= (index>=ir_from && index < ir_to) || index_in_ranges index ranges;
						index_in_ranges index []
							= False
				STE_Imported STE_DclFunction mod_index
					-> { cs & cs_predef_symbols.[PD_Start] = { pds_def = ste_index, pds_module = mod_index }}
				_
					-> case mod_kind of
							MK_Main
								# pos = newPosition predefined_idents.[PD_Start] (LinePos (mod_ident.id_name+++".icl") 1)
								-> { cs & cs_error = checkErrorWithIdentPos pos " has not been declared" cs.cs_error }
							_
								-> cs

		check_predefined_module (Yes {mod_ident={id_info}}) modules macro_and_fun_defs macro_defs heaps cs=:{cs_symbol_table}
			# (entry, cs_symbol_table) = readPtr id_info cs_symbol_table
			# cs = { cs & cs_symbol_table = cs_symbol_table <:= (id_info, { entry & ste_kind = STE_ClosedModule })}
			  {ste_kind = STE_Module mod, ste_index} = entry
			  solved_imports = { si_explicit = [], si_implicit = [] }			  	
			  imports_ikh = ikhInsert` False cPredefinedModuleIndex solved_imports ikhEmpty
			  (deferred_stuff, (_, modules, macro_and_fun_defs, macro_defs, heaps, cs))
			  		= checkDclModule EndNumbers [] imports_ikh cUndef False cDummyArray mod ste_index cDummyArray modules macro_and_fun_defs macro_defs heaps cs
			  (modules, heaps, cs)
					= checkInstancesOfDclModule cPredefinedModuleIndex deferred_stuff (modules, heaps, cs)
			  ({dcl_declared={dcls_import,dcls_local,dcls_local_for_import}}, modules) = modules![ste_index]
			= (modules, macro_and_fun_defs, macro_defs, heaps, 
			   addDeclarationsOfDclModToSymbolTable ste_index dcls_local_for_import dcls_import cs)
		check_predefined_module No modules macro_and_fun_defs macro_defs heaps cs
			= (modules, macro_and_fun_defs, macro_defs, heaps, cs)
			
		collect_specialized_functions_in_dcl_module :: ModuleKind !Index !Int !*{# DclModule} !*{# FunDef} !*VarHeap !*TypeVarHeap !*ExpressionHeap
															  -> (!IndexRange,!*{# DclModule},!*{# FunDef},!*VarHeap,!*TypeVarHeap,!*ExpressionHeap)
 		collect_specialized_functions_in_dcl_module MK_Main first_free_index main_dcl_module_n modules icl_functions var_heap type_var_heap expr_heap
			= ({ir_from=first_free_index,ir_to=first_free_index},modules, icl_functions, var_heap, type_var_heap, expr_heap)
 		collect_specialized_functions_in_dcl_module _ first_free_index main_dcl_module_n modules icl_functions var_heap type_var_heap expr_heap
			# (dcl_mod, modules) = modules![main_dcl_module_n]
			# {dcl_specials=dcl_specials=:{ir_from,ir_to},dcl_functions,dcl_common} = dcl_mod
			# (icl_functions, (var_heap, type_var_heap, expr_heap))
					= collect_specialized_functions ir_from ir_to dcl_functions (icl_functions, (var_heap, type_var_heap, expr_heap))
			= (dcl_specials,modules, icl_functions, var_heap, type_var_heap, expr_heap)

		where
			collect_specialized_functions spec_index last_index dcl_fun_types (icl_functions, heaps)
				| spec_index < last_index
					# {ft_type,ft_specials = SP_FunIndex decl_index} = dcl_fun_types.[spec_index]
					//  icl_index = conversion_table.[decl_index]
					  icl_index = decl_index
					  (icl_fun, icl_functions) = icl_functions![icl_index]
					  (new_fun_def, heaps) = build_function spec_index icl_fun icl_index ft_type heaps
					  (icl_functions, heaps) = collect_specialized_functions (inc spec_index) last_index dcl_fun_types (icl_functions, heaps)
					# icl_functions = {icl_functions & [spec_index]=new_fun_def}
					= (icl_functions, heaps)
					= (icl_functions, heaps)
		 
			build_function new_fun_index fun_def=:{fun_ident, fun_body = CheckedBody {cb_args}, fun_info} fun_index fun_type
						(var_heap, type_var_heap, expr_heap)
				# (tb_args, var_heap) = mapSt new_free_var cb_args var_heap
				  (app_args, expr_heap) = mapSt new_bound_var tb_args expr_heap
				  (app_info_ptr, expr_heap) = newPtr EI_Empty expr_heap
				  tb_rhs = App { app_symb = {	symb_ident = fun_ident,
												symb_kind = SK_Function { glob_module = main_dcl_module_n, glob_object = fun_index }},
								 app_args = app_args,
								 app_info_ptr = app_info_ptr }
				= ({ fun_def & fun_body = TransformedBody {tb_args = tb_args, tb_rhs = tb_rhs}, fun_type = Yes fun_type,
						fun_info = { EmptyFunInfo & fi_calls = [FunCall fun_index cGlobalScope] }},
					(var_heap, type_var_heap, expr_heap))
		
			new_bound_var :: !FreeVar !*ExpressionHeap -> (!Expression, !*ExpressionHeap)
			new_bound_var {fv_ident,fv_info_ptr} expr_heap
				# (var_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
				= (Var { var_ident = fv_ident, var_info_ptr = fv_info_ptr, var_expr_ptr = var_expr_ptr }, expr_heap)
	
			new_free_var :: !FreeVar *VarHeap -> (!FreeVar, !*VarHeap)
			new_free_var fv var_heap
				# (fv_info_ptr, var_heap) = newPtr VI_Empty var_heap
				= ({ fv & fv_info_ptr = fv_info_ptr, fv_def_level = NotALevel, fv_count = 0}, var_heap)
			
		copy_instance_types :: [(Index,SymbolType)] !*{# FunDef} -> *{# FunDef}
		copy_instance_types types fun_defs 
			= foldl copy_instance_type fun_defs types
		
		copy_instance_type fun_defs (index, symbol_type)
			# (inst_def, fun_defs) = fun_defs![index]
			= { fun_defs & [index] = { inst_def & fun_type = Yes symbol_type }}
		
		adjust_instance_types_of_array_functions_in_std_array_icl dcl_modules class_instances fun_defs main_dcl_module_n predef_symbols
			# ({pds_def}, predef_symbols) = predef_symbols![PD_StdArray]
			| pds_def == main_dcl_module_n
				#! nr_of_instances = size class_instances
				# ({dcl_common}, dcl_modules) = dcl_modules![main_dcl_module_n]
				  ({pds_def}, predef_symbols) = predef_symbols![PD_ArrayClass]
				  (offset_table, _, predef_symbols) = arrayFunOffsetToPD_IndexTable dcl_common.com_member_defs predef_symbols
				  (class_instances, fun_defs, predef_symbols) 
					= iFoldSt (adjust_instance_types_of_array_functions pds_def offset_table) 0 nr_of_instances
						(class_instances, fun_defs, predef_symbols)
				= (dcl_modules, class_instances, fun_defs, predef_symbols)
				= (dcl_modules, class_instances, fun_defs, predef_symbols)
		where
			adjust_instance_types_of_array_functions :: !Index !{#.Index} !Int !*(!u:{# ClassInstance},!*{# FunDef},!v:{#PredefinedSymbol})
					-> (!u:{# ClassInstance},!*{# FunDef},!v:{#PredefinedSymbol})
			adjust_instance_types_of_array_functions array_class_index offset_table inst_index (class_instances, fun_defs, predef_symbols)
				# ({ins_class={glob_module,glob_object={ds_index}},ins_type,ins_members}, class_instances) = class_instances![inst_index]
				| glob_module == main_dcl_module_n && ds_index == array_class_index && elemTypeIsStrict ins_type.it_types predef_symbols
					# fun_defs = iFoldSt (make_instance_strict ins_members offset_table) 0 (size ins_members) fun_defs
					= (class_instances, fun_defs, predef_symbols)
					= (class_instances, fun_defs, predef_symbols)
			
			make_instance_strict :: !{#DefinedSymbol} !{#Index} !Int !*{# FunDef} -> *{# FunDef}
			make_instance_strict instances offset_table ins_offset instance_defs
				# {ds_index} = instances.[ins_offset]
				  (inst_def, instance_defs) = instance_defs![ds_index]
				  (Yes symbol_type) = inst_def.fun_type
				= { instance_defs & [ds_index] = { inst_def & fun_type = Yes (makeElemTypeOfArrayFunctionStrict symbol_type ins_offset offset_table) } }

		checkSpecifiedInstanceType (index_of_member_fun, derived_symbol_type) (icl_functions, type_heaps, cs_error)
			# ({fun_type, fun_pos, fun_ident}, icl_functions) = icl_functions![index_of_member_fun]
			# (cs_error, type_heaps)
		  		= case fun_type of
		  			No
		  				-> (cs_error, type_heaps)
		  			Yes specified_symbol_type
		  				| not cs_error.ea_ok
							-> (cs_error, type_heaps)
						# (err_code, type_heaps)
						 		= symbolTypesCorrespond specified_symbol_type derived_symbol_type type_heaps
						| err_code==CEC_Ok
							-> (cs_error, type_heaps)
						# cs_error = pushErrorAdmin (newPosition fun_ident fun_pos) cs_error
						  luxurious_explanation
						  		= case err_code of
						  			CEC_ResultNotOK -> "result type"
									CEC_ArgNrNotOk -> "nr or arguments"
									CEC_ContextNotOK -> "context"
									CEC_AttrEnvNotOK -> "attribute environment"
									1 -> "first argument"
									2 -> "second argument"
									3 -> "third argument"
									_ -> toString err_code+++"th argument"
						  cs_error = checkError "the specified member type is incorrect ("(luxurious_explanation+++" not ok)") cs_error
						-> ( popErrorAdmin cs_error, type_heaps)
			= (icl_functions, type_heaps, cs_error)

checkForeignExports :: [ParsedForeignExport] [IndexRange] *{#FunDef} *CheckState -> (![ForeignExport],!*{#FunDef},!*CheckState)
checkForeignExports [{pfe_ident=pfe_ident=:{id_name,id_info},pfe_line,pfe_file,pfe_stdcall}:foreign_exports] icl_global_functions_ranges fun_defs cs
	# ({ste_kind,ste_index},cs_symbol_table) = readPtr id_info cs.cs_symbol_table
	# cs = { cs & cs_symbol_table = cs_symbol_table }
	# (foreign_export_fundef_index,fun_defs,cs) = check_foreign_export ste_kind icl_global_functions_ranges fun_defs cs
		with
			check_foreign_export (STE_FunctionOrMacro _) [{ir_from, ir_to}:_] fun_defs cs
				| ste_index>=ir_from && ste_index<ir_to
					# ({fun_type,fun_ident,fun_pos},fun_defs) = fun_defs![ste_index]
					# (foreign_export_fundef_index,cs) = case fun_type of
							No
								-> ([],cs)
							Yes {st_args,st_args_strictness,st_arity,st_result,st_context}
								| not (isEmpty st_context)
									-> ([],{cs & cs_error = checkErrorWithIdentPos (newPosition fun_ident fun_pos) "error in type of foreign exported function (context not allowed)" cs.cs_error})
								| not (first_n_are_strict st_arity st_args_strictness)
									-> ([],{cs & cs_error = checkErrorWithIdentPos (newPosition fun_ident fun_pos) "error in type of foreign exported function (strictness annotation missing)" cs.cs_error})
									-> ([{fe_fd_index=ste_index,fe_stdcall=pfe_stdcall}],cs)
					= (foreign_export_fundef_index,fun_defs,cs)
			check_foreign_export (STE_FunctionOrMacro _) [_,{ir_from, ir_to}:_] fun_defs cs
				| ste_index>=ir_from && ste_index<ir_to
					# ident_pos = { ip_ident=pfe_ident,ip_line=pfe_line,ip_file=pfe_file }
					= ([],fun_defs,{cs & cs_error = checkErrorWithIdentPos ident_pos "has not been exported" cs.cs_error})
			check_foreign_export _ _ fun_defs cs
				# ident_pos = { ip_ident=pfe_ident,ip_line=pfe_line,ip_file=pfe_file }
				= ([],fun_defs,{cs & cs_error = checkErrorWithIdentPos ident_pos "has not been declared" cs.cs_error})
	# (foreign_export_fundef_indexes,fun_defs,cs) = checkForeignExports foreign_exports icl_global_functions_ranges fun_defs cs
	= (foreign_export_fundef_index++foreign_export_fundef_indexes,fun_defs,cs)
checkForeignExports [] icl_global_functions_ranges fun_defs cs
	= ([],fun_defs,cs)

checkForeignExportedFunctionTypes :: ![ForeignExport] !*ErrorAdmin !p:PredefinedSymbols !*{#FunDef}
												  -> (!*ErrorAdmin,!p:PredefinedSymbols,!*{#FunDef})
checkForeignExportedFunctionTypes [{fe_fd_index}:icl_foreign_exports] error_admin predefined_symbols fun_defs
	| not (check_foreign_export_type st_result.at_type)
		# error_admin = checkErrorWithIdentPos (newPosition fun_ident fun_pos) "error in result type for foreign exported function" error_admin
		= checkForeignExportedFunctionTypes icl_foreign_exports error_admin predefined_symbols fun_defs2
	| not (check_foreign_export_types st_args)
		# error_admin = checkErrorWithIdentPos (newPosition fun_ident fun_pos) "error in argument type for foreign exported function" error_admin
		= checkForeignExportedFunctionTypes icl_foreign_exports error_admin predefined_symbols fun_defs2
		= checkForeignExportedFunctionTypes icl_foreign_exports error_admin predefined_symbols fun_defs2
	where
		({fun_type=Yes {st_args,st_result},fun_ident,fun_pos},fun_defs2) = fun_defs![fe_fd_index]

		check_foreign_export_types [{at_type}:argument_types]
			= check_foreign_export_type at_type && check_foreign_export_types argument_types 
		check_foreign_export_types []
			= True

		check_foreign_export_type (TB BT_Int)
			= True
		check_foreign_export_type (TB BT_Real)
			= True
		check_foreign_export_type (TB (BT_String _))
			= True
		check_foreign_export_type (TA {type_index={glob_module,glob_object},type_arity} [{at_type=TB BT_Char}])
			| predefined_symbols.[PD_UnboxedArrayType].pds_def==glob_object &&
			  predefined_symbols.[PD_UnboxedArrayType].pds_module==glob_module
			  = True
			  = False			
		check_foreign_export_type (TAS {type_arity,type_index={glob_object,glob_module}} arguments strictness)
			= glob_module==cPredefinedModuleIndex && glob_object==PD_Arity2TupleTypeIndex+(type_arity-2)
				&& first_n_are_strict type_arity strictness && check_foreign_export_types arguments
		check_foreign_export_type _
			= False
checkForeignExportedFunctionTypes [] error_admin predefined_symbols fun_defs
	= (error_admin,predefined_symbols,fun_defs)

check_needed_modules_are_imported mod_ident extension cs=:{cs_x={x_needed_modules}}
	# cs = case x_needed_modules bitand cNeedStdGeneric of
			0 -> cs
			_ -> check_it PD_StdGeneric mod_ident "" extension cs
	# cs = case x_needed_modules bitand cNeedStdDynamic of
			0 -> cs
			_ -> check_it PD_StdDynamic mod_ident "" extension cs
	# cs = case x_needed_modules bitand cNeedStdArray of
			0 -> cs
			_ -> check_it PD_StdArray mod_ident " (needed for array denotations)" extension cs
	# cs = case x_needed_modules bitand cNeedStdEnum of
			0 -> cs
			_ -> check_it PD_StdEnum mod_ident " (needed for [..] expressions)" extension cs
	# cs = case x_needed_modules bitand cNeedStdStrictLists of
			0 -> cs
			_ -> check_it PD_StdStrictLists mod_ident " (needed for strict lists)" extension cs
	= cs
  where
	check_it pd mod_ident explanation extension cs=:{cs_symbol_table}
 		# pds_ident = predefined_idents.[pd]	
		# ({ste_kind}, cs_symbol_table) = readPtr pds_ident.id_info cs_symbol_table
		  cs = { cs & cs_symbol_table = cs_symbol_table }
		= case ste_kind of
			STE_ClosedModule
				-> cs
			_ 
				# error_location = { ip_ident = mod_ident, ip_line = 1, ip_file = mod_ident.id_name+++extension}
				  cs_error = pushErrorAdmin error_location cs.cs_error
				  cs_error = checkError pds_ident ("not imported"+++explanation) cs_error
				  cs_error = popErrorAdmin cs_error
				-> { cs & cs_error = cs_error }
				
// MV ...
	switched_off_Clean_feature pd mod_ident explanation extension cs=:{cs_symbol_table}
 		# ident = predefined_idents.[pd]	
 		# error_location = { ip_ident = mod_ident, ip_line = 1, ip_file = mod_ident.id_name+++extension}
		  cs_error = pushErrorAdmin error_location cs.cs_error
		  cs_error = checkError ident ("not supported"+++explanation) cs_error
		  cs_error = popErrorAdmin cs_error
		= { cs & cs_error = cs_error}
// ... MV

arrayFunOffsetToPD_IndexTable :: !w:{# MemberDef} !v:{# PredefinedSymbol} -> (!{# Index}, !x:{#MemberDef}, !v:{#PredefinedSymbol}) , [w<=x]
arrayFunOffsetToPD_IndexTable member_defs predef_symbols
	#! nr_of_array_functions = size member_defs
	= iFoldSt offset_to_PD_index PD_CreateArrayFun (PD_CreateArrayFun + nr_of_array_functions)
			(createArray nr_of_array_functions NoIndex, member_defs, predef_symbols)
where	
	offset_to_PD_index pd_index (table, member_defs, predef_symbols)
		# ({pds_def}, predef_symbols) = predef_symbols![pd_index]
		# ({me_offset}, member_defs) = member_defs![pds_def]
		= ({ table & [me_offset] = pd_index }, member_defs, predef_symbols)

elemTypeIsStrict [TA {type_index={glob_object,glob_module}} _ : _] predef_symbols
	= glob_module == predef_symbols.[PD_PredefinedModule].pds_def &&
		(glob_object == predef_symbols.[PD_StrictArrayType].pds_def || glob_object == predef_symbols.[PD_UnboxedArrayType].pds_def)
elemTypeIsStrict [TAS {type_index={glob_object,glob_module}} _ _ : _] predef_symbols
	= glob_module == predef_symbols.[PD_PredefinedModule].pds_def &&
		(glob_object == predef_symbols.[PD_StrictArrayType].pds_def || glob_object == predef_symbols.[PD_UnboxedArrayType].pds_def)

makeElemTypeOfArrayFunctionStrict :: !SymbolType !Index !{# Index} -> SymbolType
makeElemTypeOfArrayFunctionStrict st=:{st_args,st_args_strictness,st_result} me_offset offset_table
	# array_fun_kind = offset_table.[me_offset]
	| array_fun_kind == PD_UnqArraySelectFun
		= case st_result.at_type of
			TA tuple elems
				-> { st & st_result = { st_result & at_type = TAS tuple elems (Strict 1)}}
			TAS tuple elems strictness
				-> { st & st_result = { st_result & at_type = TAS tuple elems (add_strictness 0 strictness)}}
	| array_fun_kind == PD_ArrayUpdateFun
		# [array, index, elem: _] = st_args
		= { st & st_args_strictness=add_strictness 2 st_args_strictness,st_args = [array, index, elem ] }
	| array_fun_kind == PD_CreateArrayFun
		# [array, elem: _] = st_args
		= { st & st_args_strictness=add_strictness 1 st_args_strictness,st_args = [array, elem ] }
	| array_fun_kind == PD_ArrayReplaceFun
		# [arg_array, index, elem: _] = st_args
		= case st_result.at_type of
			 TA tuple elems
				-> { st & st_args_strictness=add_strictness 2 st_args_strictness,st_args = [arg_array, index, elem],
					st_result = { st_result &  at_type = TAS tuple elems (Strict 1)}}
			 TAS tuple elems strictness
				-> { st & st_args_strictness=add_strictness 2 st_args_strictness,st_args = [arg_array, index, elem],
					st_result = { st_result &  at_type = TAS tuple elems (add_strictness 0 strictness)}}
		= st

initialDclModule ({mod_ident, mod_modification_time, mod_defs=mod_defs=:{def_funtypes,def_macro_indices}, mod_type}, sizes, all_defs) module_n
	# dcl_common= createCommonDefinitions mod_defs
	= 	{	dcl_name			= mod_ident
		,	dcl_functions		= { function \\ function <- mod_defs.def_funtypes }
		,	dcl_macros			= def_macro_indices
		,	dcl_instances		= { ir_from = 0, ir_to = 0}
		,	dcl_specials		= { ir_from = 0, ir_to = 0 }
		,	dcl_gencases		= { ir_from = 0, ir_to = 0 }
		,	dcl_type_funs		= { ir_from = 0, ir_to = 0 }
		,	dcl_common			= dcl_common
		,	dcl_sizes			= sizes
		,	dcl_dictionary_info = { n_dictionary_types=0,n_dictionary_constructors=0,n_dictionary_selectors=0 }
		,	dcl_declared		=
			{
				dcls_import 	= {}
			,	dcls_local		= all_defs
			,	dcls_local_for_import = {local_declaration_for_import decl module_n \\ decl<-all_defs}
			}
		,	dcl_macro_conversions = No
		,	dcl_module_kind	= mod_type
		,	dcl_modification_time = mod_modification_time
		,	dcl_imported_module_numbers = EndNumbers
		}

addImportedSymbolsToSymbolTable importing_mod opt_macro_range modules_in_component_set imports_ikh dcl_modules cs
	#! nr_of_dcl_modules
			= size dcl_modules
	# {si_explicit, si_implicit} = ikhSearch` importing_mod imports_ikh
	  (decls_accu, visited_modules, dcl_modules, cs)
	  		= foldSt (add_impl_imported_symbols_with_new_error_pos opt_macro_range importing_mod
	  					modules_in_component_set imports_ikh)
	  				si_implicit ([], bitvectCreate nr_of_dcl_modules, dcl_modules, cs)
	= foldSt (add_expl_imported_symbols_with_new_error_pos opt_macro_range importing_mod) si_explicit (decls_accu, dcl_modules, cs)
  where
	add_impl_imported_symbols_with_new_error_pos opt_macro_range importing_mod modules_in_component_set imports_ikh
			(mod_index, position) (decls_accu, visited_modules, dcl_modules, cs)
		# cs
				= pushErrorAdmin (newPosition import_ident position) cs
		  (decls_accu, visited_modules, dcl_modules, cs)
		  		= add_impl_imported_symbols opt_macro_range importing_mod modules_in_component_set imports_ikh
						mod_index (decls_accu, visited_modules, dcl_modules, cs)
		= (decls_accu, visited_modules, dcl_modules, popErrorAdmin cs)

	add_impl_imported_symbols opt_macro_range importing_mod modules_in_component_set imports_ikh mod_index
			(decls_accu, visited_modules, dcl_modules, cs)
		| bitvectSelect mod_index visited_modules
			= (decls_accu, visited_modules, dcl_modules, cs)
		# visited_modules
				= bitvectSet mod_index visited_modules 
		  ({ dcls_import, dcls_local_for_import }, dcl_modules)
				= dcl_modules![mod_index].dcl_declared
		  (decls_accu, cs)
		  		= foldlArraySt (add_declaration opt_macro_range importing_mod)
		  				dcls_local_for_import (decls_accu, cs)
		| not (bitvectSelect mod_index modules_in_component_set)
			// this module is outside of the actual component. All imported symbols are
			// already known
			# (decls_accu, cs)
			  		= foldlArraySt (add_declaration opt_macro_range importing_mod)
			  				dcls_import (decls_accu, cs)
			= (decls_accu, visited_modules, dcl_modules, cs)
		# {si_explicit, si_implicit}
				= ikhSearch` mod_index imports_ikh
		  (decls_accu, cs)
				= foldSt (\(decls, _) state ->
							foldSt (\decl state -> add_declaration opt_macro_range importing_mod decl state)
								decls state)
						si_explicit (decls_accu, cs)
		= foldSt (\(mod_index, _) state 
					-> add_impl_imported_symbols opt_macro_range importing_mod modules_in_component_set
						 imports_ikh mod_index state)
				si_implicit
				(decls_accu, visited_modules, dcl_modules, cs)

	add_expl_imported_symbols_with_new_error_pos opt_macro_range importing_mod (decls, position) (decls_accu, dcl_modules, cs)
		# cs = pushErrorAdmin (newPosition import_ident position) cs
		  (decls_accu, dcl_modules, cs) = foldSt (add_expl_imp_declaration opt_macro_range importing_mod) decls (decls_accu, dcl_modules, cs)
		= (decls_accu, dcl_modules, popErrorAdmin cs)		
		
	add_declaration :: (Optional IndexRange) Int Declaration *([Declaration],*CheckState) -> (![Declaration],!*CheckState)
	add_declaration opt_dcl_macro_range importing_mod declaration (decls_accu, cs)
		# (not_already_imported, cs)
				= add_declaration_to_symbol_table opt_dcl_macro_range declaration importing_mod cs
		| not_already_imported
			= ([declaration:decls_accu], cs)
		= (decls_accu, cs)

	add_expl_imp_declaration opt_dcl_macro_range importing_mod declaration (decls_accu, dcl_modules, cs)
		# (not_already_imported, cs)
				= add_declaration_to_symbol_table opt_dcl_macro_range declaration importing_mod cs
		| not_already_imported
			= ([declaration:decls_accu], dcl_modules, cs)
		= (decls_accu, dcl_modules, cs)

add_declaration_to_symbol_table opt_dcl_macro_range (Declaration {decl_kind=STE_FunctionOrMacro _, decl_ident, decl_index}) _ cs
	= addImportedFunctionOrMacro opt_dcl_macro_range decl_ident decl_index cs
add_declaration_to_symbol_table yes_for_icl_module (Declaration {decl_kind=decl_kind=:STE_Imported def_kind def_mod, decl_ident, decl_index, decl_pos}) importing_mod cs
	= addSymbol yes_for_icl_module decl_ident decl_pos decl_kind def_kind decl_index def_mod importing_mod cs

updateExplImpInfo :: [Int] Index {!Declaration} {!Declaration} u:{#DclModule} {!{!*ExplImpInfo}} *SymbolTable 
		-> (u:{#DclModule},!{!{!.ExplImpInfo}},.SymbolTable)
updateExplImpInfo super_components mod_index dcls_import dcls_local_for_import dcl_modules expl_imp_infos cs_symbol_table
	# (changed_symbols, (expl_imp_infos, cs_symbol_table))
	  		= mapSt markExplImpSymbols super_components (expl_imp_infos, cs_symbol_table)
	  (dcl_modules, expl_imp_infos, cs_symbol_table)
	  		= update_expl_imp_for_marked_symbols mod_index dcls_local_for_import (dcl_modules, expl_imp_infos, cs_symbol_table)
	  (dcl_modules, expl_imp_infos, cs_symbol_table)
	  		= update_expl_imp_for_marked_symbols mod_index dcls_import (dcl_modules, expl_imp_infos, cs_symbol_table)
	  cs_symbol_table
	  		= foldSt (\l cs_symbol_table->foldSt restoreHeap l cs_symbol_table) changed_symbols cs_symbol_table
	= (dcl_modules, expl_imp_infos, cs_symbol_table)

updateExplImpInfoForCachedModule :: [Int] Index {!Declaration} {!Declaration} {!{!*ExplImpInfo}} u:{#DclModule} *SymbolTable 
																		 -> (!{!{!.ExplImpInfo}},u:{#DclModule},.SymbolTable)
updateExplImpInfoForCachedModule super_components mod_index dcls_import dcls_local_for_import expl_imp_infos dcl_modules cs_symbol_table
	# (changed_symbols, (expl_imp_infos, cs_symbol_table))
	  		= mapSt markExplImpSymbols super_components (expl_imp_infos, cs_symbol_table)

	  dcl_modules__cs_symbol_table = mark_belongings_of_expl_imp_symbols dcls_local_for_import (dcl_modules, cs_symbol_table)
	  (dcl_modules, cs_symbol_table) = mark_belongings_of_expl_imp_symbols dcls_import dcl_modules__cs_symbol_table

	  cs_symbol_table = mark_belongings_of_expl_imp_symbols_as_exported dcls_local_for_import cs_symbol_table
	  cs_symbol_table = mark_belongings_of_expl_imp_symbols_as_exported dcls_import cs_symbol_table

	  (dcl_modules, expl_imp_infos, cs_symbol_table)
	  		= update_expl_imp_for_marked_symbols mod_index dcls_local_for_import (dcl_modules, expl_imp_infos, cs_symbol_table)
	  (dcl_modules, expl_imp_infos, cs_symbol_table)
	  		= update_expl_imp_for_marked_symbols mod_index dcls_import (dcl_modules, expl_imp_infos, cs_symbol_table)

	  dcl_modules__cs_symbol_table
	  		= unmark_belongings_of_expl_imp_symbols dcls_local_for_import (dcl_modules, cs_symbol_table)
	  (dcl_modules, cs_symbol_table)
	  		= unmark_belongings_of_expl_imp_symbols dcls_import dcl_modules__cs_symbol_table

	  cs_symbol_table = foldSt (\l cs_symbol_table->foldSt restoreHeap l cs_symbol_table) changed_symbols cs_symbol_table
	= (expl_imp_infos, dcl_modules, cs_symbol_table)
where
	mark_belongings_of_expl_imp_symbols decls (dcl_modules, cs_symbol_table)
		= foldlArraySt mark_belongings_of_expl_imp_symbol decls (dcl_modules, cs_symbol_table)
		where
			mark_belongings_of_expl_imp_symbol decl=:(Declaration {decl_ident={id_info}}) (dcl_modules, cs_symbol_table)
				# (ste, cs_symbol_table) = readPtr id_info cs_symbol_table
				= case ste of
					({ste_kind=STE_ExplImpComponentNrs component_numbers inst_indices})
						# (all_belonging_symbols, dcl_modules) = getBelongingSymbols decl dcl_modules
						-> (dcl_modules, foldlBelongingSymbols mark_belonging_symbol all_belonging_symbols cs_symbol_table)
						where
							mark_belonging_symbol {id_info} cs_symbol_table
								# (ste, cs_symbol_table) = readPtr id_info cs_symbol_table
								= case ste.ste_kind of
								 	STE_Empty
								 		-> writePtr id_info {ste & ste_kind=STE_BelongingSymbolForExportedSymbol} cs_symbol_table
								 	_
										-> cs_symbol_table
					_
						-> (dcl_modules, cs_symbol_table)

	mark_belongings_of_expl_imp_symbols_as_exported decls cs_symbol_table
		= foldlArraySt mark_belonging_of_expl_imp_marked_symbol_as_exported decls cs_symbol_table
		where
			mark_belonging_of_expl_imp_marked_symbol_as_exported decl=:(Declaration {decl_ident={id_info}}) cs_symbol_table
				# (ste, cs_symbol_table) = readPtr id_info cs_symbol_table
				= case ste.ste_kind of
				 	STE_BelongingSymbolForExportedSymbol
				 		-> writePtr id_info {ste & ste_kind=STE_BelongingSymbolExported} cs_symbol_table
				 	_
						-> cs_symbol_table

	unmark_belongings_of_expl_imp_symbols decls (dcl_modules, cs_symbol_table)
		= foldlArraySt unmark_belongings_of_expl_imp_symbol decls (dcl_modules, cs_symbol_table)
		where
			unmark_belongings_of_expl_imp_symbol decl=:(Declaration {decl_ident={id_info}}) (dcl_modules, cs_symbol_table)
				# (ste, cs_symbol_table) = readPtr id_info cs_symbol_table
				= case ste of
					({ste_kind=STE_ExplImpComponentNrs component_numbers inst_indices})
						# (all_belonging_symbols, dcl_modules) = getBelongingSymbols decl dcl_modules
						-> (dcl_modules, foldlBelongingSymbols unmark_belonging_symbol all_belonging_symbols cs_symbol_table)
						where
							unmark_belonging_symbol {id_info} cs_symbol_table
								# (ste, cs_symbol_table) = readPtr id_info cs_symbol_table
								= case ste.ste_kind of
								 	STE_BelongingSymbolExported
								 		-> writePtr id_info {ste & ste_kind=STE_Empty} cs_symbol_table
								 	STE_BelongingSymbolForExportedSymbol
								 		-> writePtr id_info {ste & ste_kind=STE_Empty} cs_symbol_table
								 	_
										-> cs_symbol_table
					_
						-> (dcl_modules, cs_symbol_table)

foldlBelongingSymbols f bs st
	:== case bs of
			BS_Constructors constructors
				-> foldSt (\{ds_ident} st -> f ds_ident st) constructors st 
			BS_Fields fields
				-> foldlArraySt (\{fs_ident} st -> f fs_ident st) fields st 
			BS_Members members
				-> foldlArraySt (\{ds_ident} st -> f ds_ident st) members st 
			BS_Nothing
				-> st

/*
ste_kind_to_string :: STE_Kind -> String
ste_kind_to_string ste_kind = case ste_kind of
	STE_FunctionOrMacro _
		-> "STE_FunctionOrMacro"
	STE_Type
		-> "STE_Type"
	STE_Constructor
		-> "STE_Constructor"
	STE_Selector _
		-> "STE_Selector"
	STE_Field _
		-> "STE_Field"
	STE_Class
		-> "STE_Class"
	STE_Member
		-> "STE_Member"
	STE_Instance
		-> "STE_Instance"
	STE_Variable _
		-> "STE_Variable"
	STE_TypeVariable _
		-> "STE_TypeVariable"
	STE_TypeAttribute _
		-> "STE_TypeAttribute"
	STE_BoundTypeVariable _
		-> "STE_BoundTypeVariable"
	STE_Imported ste_kind2 _
		-> "STE_Imported "+++ste_kind_to_string ste_kind2
	STE_DclFunction
		-> "STE_DclFunction"
	STE_Module _
		-> "STE_Module"
	STE_ClosedModule
		-> "STE_ClosedModule"
	STE_Empty
		-> "STE_Empty"
	STE_DictType _
		-> "STE_DictType"
	STE_DictCons _
		-> "STE_DictCons"
	STE_DictField _
		-> "STE_DictField"
	STE_Called _
		-> "STE_Called"
	STE_ExplImpSymbol _
		-> "STE_ExplImpSymbol"
	STE_ExplImpComponentNrs _ _
		-> "STE_ExplImpComponentNrs"
	STE_BelongingSymbol _
		-> "STE_BelongingSymbol"
*/

update_expl_imp_for_marked_symbols mod_index decls (dcl_modules, expl_imp_infos, cs_symbol_table)
	= foldlArraySt (update_expl_imp_for_marked_symbol mod_index) decls (dcl_modules, expl_imp_infos, cs_symbol_table)

update_expl_imp_for_marked_symbol mod_index decl=:(Declaration {decl_ident}) (dcl_modules, expl_imp_infos, cs_symbol_table)
	# (ste, cs_symbol_table) = readPtr decl_ident.id_info cs_symbol_table
	= updateExplImpForMarkedSymbol mod_index decl ste dcl_modules expl_imp_infos cs_symbol_table

update_expl_imp_for_marked_local_symbol mod_index decl=:(Declaration {decl_ident}) (dcl_modules, expl_imp_infos, cs_symbol_table)
	# (ste, cs_symbol_table) = readPtr decl_ident.id_info cs_symbol_table
	= updateExplImpForMarkedLocalSymbol mod_index decl ste dcl_modules expl_imp_infos cs_symbol_table
where
	updateExplImpForMarkedLocalSymbol :: !Index Declaration !SymbolTableEntry !u:{#DclModule} !{!{!*ExplImpInfo}} !*SymbolTable
			-> (!u:{#DclModule}, !{!{!.ExplImpInfo}}, !.SymbolTable)
	updateExplImpForMarkedLocalSymbol mod_index decl {ste_kind=STE_ExplImpComponentNrs component_numbers inst_indices}
				dcl_modules expl_imp_infos cs_symbol_table
		= foldSt (addExplImpInfo mod_index decl) component_numbers (dcl_modules, expl_imp_infos, cs_symbol_table)
	  where
		addExplImpInfo :: !Index Declaration !ComponentNrAndIndex !(!u:{#DclModule}, !{!{!*ExplImpInfo}}, !v:SymbolTable)
					-> (!u:{#DclModule}, !{!{!.ExplImpInfo}}, !v:SymbolTable)
		addExplImpInfo mod_index decl { cai_component_nr, cai_index } (dcl_modules, expl_imp_infos, cs_symbol_table)
			# (ExplImpInfo eii_ident eii_declaring_modules, expl_imp_infos)
					= replaceTwoDimArrElt cai_component_nr cai_index TemporarilyFetchedAway expl_imp_infos
			  (all_belongs, dcl_modules) = getBelongingSymbols decl dcl_modules
			  di_belonging = nsFromTo (nrOfBelongingSymbols all_belongs)
			  di = { di_decl = decl, di_instances = [], di_belonging = di_belonging }
			  new_expl_imp_info = ExplImpInfo eii_ident (ikhInsert` False mod_index di eii_declaring_modules)
			= (dcl_modules, { expl_imp_infos & [cai_component_nr,cai_index] = new_expl_imp_info }, cs_symbol_table)
	updateExplImpForMarkedLocalSymbol _ _ entry dcl_modules expl_imp_infos cs_symbol_table
		= (dcl_modules, expl_imp_infos, cs_symbol_table)

checkInstancesOfDclModule :: !.Int !(!.Int,.Int,.[FunType]) !(!*{#DclModule},!*Heaps,!*CheckState)
														  -> (!.{#DclModule},!.Heaps,!.CheckState);
checkInstancesOfDclModule mod_index	(nr_of_dcl_functions_and_instances, nr_of_dcl_funs_insts_and_specs, rev_special_defs) (dcl_modules, heaps=:{hp_type_heaps, hp_var_heap}, cs=:{cs_error})
	# (dcl_mod=:{dcl_functions, dcl_common}, dcl_modules) = dcl_modules![mod_index]
	  nr_of_dcl_functions = size dcl_functions
	  (memb_inst_defs, nr_of_dcl_functions_and_instances2, rev_spec_class_inst, 
		com_instance_defs, com_class_defs, com_member_defs, dcl_modules, hp_type_heaps, hp_var_heap, cs)
			= determineTypesOfInstances nr_of_dcl_functions mod_index
	  				{d \\ d<-:dcl_common.com_instance_defs}
	  				{d \\ d<-:dcl_common.com_class_defs}
	  				{d \\ d<-:dcl_common.com_member_defs}
	  				dcl_modules hp_type_heaps hp_var_heap { cs & cs_error = cs_error }
	  heaps
	  		= { heaps & hp_type_heaps = hp_type_heaps, hp_var_heap = hp_var_heap }
	  (nr_of_dcl_funs_insts_and_specs, new_class_instances, rev_special_defs, all_spec_types, heaps, cs_predef_symbols,cs_error)
			= checkSpecialsOfInstances mod_index nr_of_dcl_functions rev_spec_class_inst nr_of_dcl_funs_insts_and_specs []
					rev_special_defs { mem \\ mem <- memb_inst_defs } { [] \\ mem <- memb_inst_defs } heaps cs.cs_predef_symbols cs.cs_error			

	#! (nr_of_dcl_funs_insts_specs_and_gencases, gen_funs, com_gencase_defs, heaps)
	  		= create_gencase_funtypes nr_of_dcl_funs_insts_and_specs {d \\ d<-:dcl_common.com_gencase_defs} heaps	
	  
	#  dcl_functions
	  		= arrayPlusList dcl_functions
	  			(   [ { mem_inst & ft_specials = if (isEmpty spec_types) SP_None (SP_ContextTypes spec_types) } 
				  	  \\ mem_inst <- memb_inst_defs & spec_types <-: all_spec_types 
				  	]
	  			 ++ reverse rev_special_defs
	  			 ++ gen_funs
	  			)
  	  			
	#  cs = { cs & cs_predef_symbols=cs_predef_symbols,cs_error = cs_error}
	#! mod_index_of_std_array = cs.cs_predef_symbols.[PD_StdArray].pds_def
	# (com_member_defs, com_instance_defs, dcl_functions, cs)
	  		= case mod_index_of_std_array==mod_index of
				False
					-> (com_member_defs, com_instance_defs, dcl_functions, cs)
				True
					-> adjust_instance_types_of_array_functions_in_std_array_dcl mod_index
							com_member_defs com_instance_defs dcl_functions cs
	#! dcl_mod = { dcl_mod & dcl_functions = dcl_functions,
			  				dcl_specials = { ir_from = nr_of_dcl_functions_and_instances,
			  								ir_to = nr_of_dcl_funs_insts_and_specs },
			  				dcl_gencases = 	{ ir_from = nr_of_dcl_funs_insts_and_specs
			  								, ir_to = nr_of_dcl_funs_insts_specs_and_gencases},
			  				dcl_common = 
			  					{ dcl_common 
			  					& com_instance_defs = array_plus_list com_instance_defs new_class_instances
			  					, com_class_defs = com_class_defs
			  					, com_member_defs = com_member_defs
			  					, com_gencase_defs = com_gencase_defs
			  					}}

		// TODO: update the instance range or create another, generic function range
		
	   dcl_modules = { dcl_modules & [mod_index] = dcl_mod }
	= (dcl_modules, heaps, cs)
  where
  	create_gencase_funtypes :: !Index !*{#GenericCaseDef} !*Heaps
  		-> (!Index, ![FunType], !*{#GenericCaseDef}, !*Heaps)
  	create_gencase_funtypes fun_index gencase_defs heaps
 		#! (fun_index, new_funs, gencase_defs, hp_var_heap) 
 			= create_funs 0 fun_index gencase_defs heaps.hp_var_heap
  		= (fun_index, new_funs, gencase_defs, {heaps & hp_var_heap = hp_var_heap}) 
  	where
  	
  		create_funs gc_index fun_index gencase_defs hp_var_heap
  			| gc_index == size gencase_defs
  				= (fun_index, [], gencase_defs, hp_var_heap)
  				#! (fun, gencase_defs,hp_var_heap) 
  					= create_fun gc_index fun_index gencase_defs hp_var_heap
  				#! (fun_index, funs, gencase_defs,hp_var_heap) 
  					= create_funs (inc gc_index) (inc fun_index) gencase_defs hp_var_heap
  				= (fun_index, [fun:funs], gencase_defs, hp_var_heap)
  		create_fun gc_index fun_index gencase_defs hp_var_heap
  			# (gencase_def=:{gc_ident, gc_pos, gc_type_cons}, gencase_defs) = gencase_defs ! [gc_index]
  			# gencase_def = { gencase_def & gc_body = GCB_FunIndex fun_index }
  			# gencase_defs = {gencase_defs & [gc_index] = gencase_def} 
  			
			#! fun_ident = genericIdentToFunIdent gc_ident gc_type_cons
		 	#! (var_info_ptr, hp_var_heap) = newPtr VI_Empty hp_var_heap
	 		#! fun = 
	  			{ ft_ident = fun_ident
	  			, ft_arity = 0
	  			, ft_priority = NoPrio
	  			, ft_type = {st_vars=[],st_attr_vars=[],st_arity=0,st_args=[],st_result={at_type=TE,at_attribute=TA_Multi},st_attr_env=[],st_context=[],st_args_strictness=NotStrict} 
	  			, ft_pos = gc_pos
	  			, ft_specials = SP_None
	  			, ft_type_ptr = var_info_ptr
	  			}
 
   			= (fun, gencase_defs, hp_var_heap)
   				//---> ("create_gencase_funtypes", gc_ident, gc_type_cons, gc_index, fun_index)
   
	adjust_instance_types_of_array_functions_in_std_array_dcl array_mod_index class_members class_instances fun_types cs=:{cs_predef_symbols}
		#! nr_of_instances = size class_instances
		# ({pds_def}, cs_predef_symbols) = cs_predef_symbols![PD_ArrayClass]
		  (offset_table, class_members, cs_predef_symbols) = arrayFunOffsetToPD_IndexTable class_members cs_predef_symbols
		  (class_instances, fun_types, cs_predef_symbols) 
				= iFoldSt (adjust_instance_types_of_array_functions array_mod_index pds_def offset_table) 0 nr_of_instances
						(class_instances, fun_types, cs_predef_symbols)
		= (class_members, class_instances, fun_types, { cs & cs_predef_symbols = cs_predef_symbols })
	where
		adjust_instance_types_of_array_functions :: .Index !Index !{#.Index} !Int !*(!u:{# ClassInstance},!*{# FunType},!v:{#PredefinedSymbol})
			 -> (!u:{# ClassInstance},!*{# FunType},!v:{#PredefinedSymbol})
		adjust_instance_types_of_array_functions array_mod_index array_class_index offset_table inst_index (class_instances, fun_types, predef_symbols)
			# ({ins_class={glob_module,glob_object={ds_index}},ins_type,ins_members}, class_instances) = class_instances![inst_index]
			| glob_module == array_mod_index && ds_index == array_class_index && elemTypeIsStrict ins_type.it_types predef_symbols
				# fun_types = iFoldSt (make_instance_strict ins_members offset_table) 0 (size ins_members) fun_types
				= (class_instances, fun_types, predef_symbols)
				= (class_instances, fun_types, predef_symbols)
		
		make_instance_strict :: !{#DefinedSymbol} !{#Index} !Int !*{# FunType} -> *{# FunType}
		make_instance_strict instances offset_table ins_offset instance_defs
			# {ds_index} = instances.[ins_offset]
			  (inst_def, instance_defs) = instance_defs![ds_index]
			  (Yes symbol_type) = inst_def.ft_type
			= { instance_defs & [ds_index] = { inst_def & ft_type =  makeElemTypeOfArrayFunctionStrict inst_def.ft_type ins_offset offset_table } }

checkDclModule :: !NumberSet ![Int] !(IntKeyHashtable SolvedImports) !Int !Bool !LargeBitvect
					!(Module (CollectedDefinitions ClassInstance IndexRange)) !Index !*ExplImpInfos !*{#DclModule} !*{#FunDef} !*{#*{#FunDef}} !*Heaps !*CheckState
				-> (!(!Int,!Index,![FunType]), !(!*ExplImpInfos, !*{#DclModule}, !*{#FunDef},!*{#*{#FunDef}},!*Heaps, !*CheckState))
checkDclModule dcl_imported_module_numbers super_components imports_ikh component_nr is_on_cycle modules_in_component_set
		 mod=:{mod_ident,mod_defs=mod_defs=:{def_macro_indices,def_funtypes}} mod_index expl_imp_info modules icl_functions macro_defs heaps cs
//	| False--->("checkDclModule", mod_ident, mod_index) //, modules.[mod_index].dcl_declared.dcls_local)
//		= undef
	# dcl_common = createCommonDefinitions mod_defs
	#! first_type_index = size dcl_common.com_type_defs		
	# dcl_common = {dcl_common & com_class_defs = number_class_dictionaries 0 dcl_common.com_class_defs first_type_index}
		with
			number_class_dictionaries class_index class_defs index_type
				| class_index < size class_defs
					# class_defs = { class_defs & [class_index].class_dictionary.ds_index = index_type }
					= number_class_dictionaries (inc class_index) class_defs (inc index_type)
					= class_defs
	= checkDclModule2 dcl_imported_module_numbers super_components imports_ikh component_nr is_on_cycle modules_in_component_set
		 mod_ident dcl_common def_macro_indices def_funtypes mod_index expl_imp_info modules icl_functions macro_defs heaps cs

checkDclModule2 :: !NumberSet ![Int] !(IntKeyHashtable SolvedImports) !Int !Bool !LargeBitvect
					!Ident *CommonDefs !IndexRange ![FunType] !Index !*ExplImpInfos !*{#DclModule} !*{#FunDef} !*{#*{#FunDef}} !*Heaps !*CheckState
				-> (!(!Int,!Index,![FunType]), !(!*ExplImpInfos, !*{#DclModule}, !*{#FunDef},!*{#*{#FunDef}},!*Heaps, !*CheckState))
checkDclModule2 dcl_imported_module_numbers super_components imports_ikh component_nr is_on_cycle modules_in_component_set
		 mod_ident dcl_common dcl_macros dcl_funtypes mod_index expl_imp_info modules icl_functions macro_defs heaps cs
	# (dcl_mod, modules)			= modules![mod_index]
	  dcl_defined 					= dcl_mod.dcl_declared.dcls_local
	  cs							= addGlobalDefinitionsToSymbolTable dcl_defined cs
	  (dcls_import_list, modules, cs)
	  		= addImportedSymbolsToSymbolTable mod_index No modules_in_component_set imports_ikh modules cs
	  dcls_import					= { el \\ el<-dcls_import_list }
	  cs							= { cs & cs_x.x_needed_modules = 0 }
	  nr_of_dcl_functions 			= size dcl_mod.dcl_functions
	# (dictionary_info,dcl_common, modules, heaps, cs)
	  		= checkCommonDefinitions No mod_index dcl_common modules heaps cs
	# dcl_mod = {dcl_mod & dcl_dictionary_info=dictionary_info}
	| not cs.cs_error.ea_ok
	 	# cs_symbol_table = removeDeclarationsFromSymbolTable dcl_defined cModuleScope cs.cs_symbol_table
	 	# cs_symbol_table = foldlArraySt removeImportedSymbolsFromSymbolTable dcls_import cs_symbol_table
		= ((0, 0, []), (expl_imp_info, modules, icl_functions, macro_defs, heaps, {cs & cs_symbol_table = cs_symbol_table}))

	#!nr_of_members = count_members mod_index dcl_common.com_instance_defs dcl_common.com_class_defs modules
	# nr_of_dcl_functions_and_instances = nr_of_dcl_functions+nr_of_members


	  (nr_of_dcl_funs_insts_and_specs, rev_function_list, rev_special_defs, com_type_defs, com_class_defs, modules, heaps, cs)
	  		= checkDclFunctions mod_index nr_of_dcl_functions_and_instances dcl_funtypes
	  			dcl_common.com_type_defs dcl_common.com_class_defs modules heaps cs

	  dcl_functions = { function \\ function <- reverse rev_function_list }
	  com_member_defs = dcl_common.com_member_defs
	  e_info = { ef_type_defs = com_type_defs, ef_selector_defs = dcl_common.com_selector_defs, ef_class_defs = com_class_defs,
	  			 ef_cons_defs = dcl_common.com_cons_defs, ef_member_defs = com_member_defs, ef_generic_defs = dcl_common.com_generic_defs,
	  			 ef_modules = modules, ef_macro_defs=macro_defs, ef_is_macro_fun = False }

	  (icl_functions, e_info=:{ef_modules=modules,ef_macro_defs=macro_defs}, heaps=:{hp_expression_heap}, cs)
			= checkAndPartitionateDclMacros mod_index dcl_macros icl_functions e_info heaps cs
	  
	  cs = check_needed_modules_are_imported mod_ident ".dcl" cs

	  com_instance_defs = dcl_common.com_instance_defs

	  (ef_member_defs, com_instance_defs, dcl_functions, cs)
	  		= adjust_predefined_symbols mod_index e_info.ef_member_defs com_instance_defs dcl_functions cs

	  (modules, icl_functions, macro_defs, hp_expression_heap, cs)
			= case is_on_cycle of
				False 
					# decls_explicit = (ikhSearch` mod_index imports_ikh).si_explicit
					-> checkExplicitImportCompleteness decls_explicit modules icl_functions macro_defs hp_expression_heap cs
				True
					-> (modules, icl_functions, macro_defs, hp_expression_heap, cs)

	  heaps = { heaps & hp_expression_heap = hp_expression_heap }

	  dcl_common = { dcl_common & com_type_defs = e_info.ef_type_defs, com_selector_defs = e_info.ef_selector_defs, com_class_defs = e_info.ef_class_defs,
			  	 		com_instance_defs = com_instance_defs, com_cons_defs = e_info.ef_cons_defs, com_member_defs = e_info.ef_member_defs,
			  	 		com_generic_defs = e_info.ef_generic_defs
			  	 	}
	  (modules, expl_imp_info, cs_symbol_table)
	  		= updateExplImpInfo super_components mod_index dcls_import dcl_mod.dcl_declared.dcls_local_for_import modules expl_imp_info cs.cs_symbol_table
	
	  cs_symbol_table = removeDeclarationsFromSymbolTable dcl_defined cModuleScope cs_symbol_table
	  cs_symbol_table = foldlArraySt removeImportedSymbolsFromSymbolTable dcls_import cs_symbol_table

	  dcl_mod = { dcl_mod &  dcl_declared = { dcl_mod.dcl_declared & dcls_import = dcls_import },
	  			 dcl_common = dcl_common, dcl_functions = dcl_functions, 
	  			 dcl_instances = { ir_from = nr_of_dcl_functions, ir_to = nr_of_dcl_functions_and_instances },
	  			 dcl_specials = { ir_from = cUndef, ir_to = cUndef },
	  			 dcl_gencases = { ir_from = cUndef, ir_to = cUndef },
	  			 dcl_imported_module_numbers = dcl_imported_module_numbers}
	= ((nr_of_dcl_functions_and_instances, nr_of_dcl_funs_insts_and_specs, rev_special_defs),
		(expl_imp_info, { modules & [ mod_index ] = dcl_mod }, icl_functions, macro_defs, heaps, { cs & cs_symbol_table = cs_symbol_table }))
where
	adjust_predefined_symbols mod_index class_members class_instances fun_types cs=:{cs_predef_symbols}
		# (pre_mod, cs_predef_symbols) = cs_predef_symbols![PD_StdArray]
		| pre_mod.pds_def == mod_index
			# cs = { cs & cs_predef_symbols = cs_predef_symbols}
				<=< adjust_predef_symbols PD_CreateArrayFun PD_UnqArraySizeFun mod_index STE_Member
				<=< adjustPredefSymbol PD_ArrayClass mod_index STE_Class
			= (class_members, class_instances, fun_types, cs)
		# (pre_mod, cs_predef_symbols) = cs_predef_symbols![PD_PredefinedModule]
		| pre_mod.pds_def == mod_index
			= (class_members, class_instances, fun_types, { cs & cs_predef_symbols = cs_predef_symbols}
				<=< adjustPredefSymbolAndCheckIndex PD_StringType mod_index PD_StringTypeIndex STE_Type
				<=< adjust_predef_symbols PD_ListType PD_OverloadedListType mod_index STE_Type
				<=< adjust_predef_symbols_and_check_indices PD_Arity2TupleType PD_Arity32TupleType PD_Arity2TupleTypeIndex mod_index STE_Type
				<=< adjust_predef_symbols PD_LazyArrayType PD_UnboxedArrayType mod_index STE_Type
				<=< adjust_predef_symbols PD_ConsSymbol PD_Arity32TupleSymbol mod_index STE_Constructor
				<=< adjustPredefSymbol PD_TypeCodeClass mod_index STE_Class
				<=< adjustPredefSymbol PD_TypeCodeMember mod_index STE_Member
				<=< adjustPredefSymbol PD_DummyForStrictAliasFun mod_index STE_DclFunction)
		# (pre_mod, cs_predef_symbols) = cs_predef_symbols![PD_StdBool]
		| pre_mod.pds_def == mod_index
			= (class_members, class_instances, fun_types, { cs & cs_predef_symbols = cs_predef_symbols}
				<=< adjustPredefSymbol PD_AndOp mod_index STE_DclFunction
				<=< adjustPredefSymbol PD_OrOp mod_index STE_DclFunction)
		# (pre_mod, cs_predef_symbols) = cs_predef_symbols![PD_StdStrictLists]
		| pre_mod.pds_def == mod_index
			= (class_members, class_instances, fun_types, { cs & cs_predef_symbols = cs_predef_symbols}
				<=< adjust_predef_symbols PD_cons PD_decons_uts mod_index STE_Member
				<=< adjust_predef_symbols PD_nil PD_nil_uts mod_index STE_DclFunction
				<=< adjust_predef_symbols PD_ListClass PD_UTSListClass mod_index STE_Class)
		# (pre_mod, cs_predef_symbols) = cs_predef_symbols![PD_StdDynamic]	
		| pre_mod.pds_def == mod_index
			= (class_members, class_instances, fun_types, { cs & cs_predef_symbols = cs_predef_symbols}
				<=< adjustPredefSymbol PD_Dyn_DynamicTemp			mod_index STE_Type
				<=< adjustPredefSymbol PD_Dyn_TypeCode				mod_index STE_Type
				<=< adjustPredefSymbol PD_Dyn_TypeScheme 			mod_index STE_Constructor
				<=< adjustPredefSymbol PD_Dyn_TypeVar				mod_index STE_Constructor
				<=< adjustPredefSymbol PD_Dyn_TypeCons				mod_index STE_Constructor
				<=< adjustPredefSymbol PD_Dyn_TypeApp				mod_index STE_Constructor
				<=< adjustPredefSymbol PD_Dyn_TypeUnique			mod_index STE_Constructor
				<=< adjustPredefSymbol PD_Dyn__TypeFixedVar			mod_index STE_Constructor
				<=< adjustPredefSymbol PD_Dyn_UnificationEnvironment				mod_index STE_Type
				<=< adjustPredefSymbol PD_Dyn_initial_unification_environment		mod_index STE_DclFunction
				<=< adjustPredefSymbol PD_Dyn_bind_global_type_pattern_var	mod_index STE_DclFunction
				<=< adjustPredefSymbol PD_Dyn_unify					mod_index STE_DclFunction
				<=< adjustPredefSymbol PD_Dyn_normalise				mod_index STE_DclFunction

				<=< adjustPredefSymbol PD_Dyn_TypeCodeConstructorInt		mod_index STE_DclFunction
				<=< adjustPredefSymbol PD_Dyn_TypeCodeConstructorChar		mod_index STE_DclFunction
				<=< adjustPredefSymbol PD_Dyn_TypeCodeConstructorReal		mod_index STE_DclFunction
				<=< adjustPredefSymbol PD_Dyn_TypeCodeConstructorBool		mod_index STE_DclFunction
				<=< adjustPredefSymbol PD_Dyn_TypeCodeConstructorDynamic	mod_index STE_DclFunction
				<=< adjustPredefSymbol PD_Dyn_TypeCodeConstructorFile		mod_index STE_DclFunction
				<=< adjustPredefSymbol PD_Dyn_TypeCodeConstructorWorld		mod_index STE_DclFunction
				<=< adjustPredefSymbol PD_Dyn_TypeCodeConstructor_Arrow		mod_index STE_DclFunction
				<=< adjustPredefSymbol PD_Dyn_TypeCodeConstructor_List		mod_index STE_DclFunction
				<=< adjustPredefSymbol PD_Dyn_TypeCodeConstructor_StrictList		mod_index STE_DclFunction
				<=< adjustPredefSymbol PD_Dyn_TypeCodeConstructor_UnboxedList		mod_index STE_DclFunction
				<=< adjustPredefSymbol PD_Dyn_TypeCodeConstructor_TailStrictList		mod_index STE_DclFunction
				<=< adjustPredefSymbol PD_Dyn_TypeCodeConstructor_StrictTailStrictList		mod_index STE_DclFunction
				<=< adjustPredefSymbol PD_Dyn_TypeCodeConstructor_UnboxedTailStrictList		mod_index STE_DclFunction
				<=< adjustPredefSymbol PD_Dyn_TypeCodeConstructor_Tuple		mod_index STE_DclFunction
				<=< adjustPredefSymbol PD_Dyn_TypeCodeConstructor_LazyArray		mod_index STE_DclFunction
				<=< adjustPredefSymbol PD_Dyn_TypeCodeConstructor_StrictArray		mod_index STE_DclFunction
				<=< adjustPredefSymbol PD_Dyn_TypeCodeConstructor_UnboxedArray		mod_index STE_DclFunction
				<=< adjustPredefSymbol PD_Dyn__to_TypeCodeConstructor		mod_index STE_DclFunction)

		# (pre_mod, cs_predef_symbols) = cs_predef_symbols![PD_StdGeneric]
		# type_bimap = predefined_idents.[PD_TypeBimap]	
		| pre_mod.pds_def == mod_index
			= (class_members, class_instances, fun_types, { cs & cs_predef_symbols = cs_predef_symbols}
				<=< adjustPredefSymbol PD_TypeBimap				mod_index STE_Type
				<=< adjustPredefSymbol PD_ConsBimap				mod_index STE_Constructor				
				<=< adjustPredefSymbol PD_map_to				mod_index (STE_Field type_bimap)
				<=< adjustPredefSymbol PD_map_from				mod_index (STE_Field type_bimap)				
				<=< adjustPredefSymbol PD_TypeUNIT				mod_index STE_Type
				<=< adjustPredefSymbol PD_ConsUNIT				mod_index STE_Constructor
				<=< adjustPredefSymbol PD_TypePAIR				mod_index STE_Type
				<=< adjustPredefSymbol PD_ConsPAIR				mod_index STE_Constructor
				<=< adjustPredefSymbol PD_TypeEITHER			mod_index STE_Type
				<=< adjustPredefSymbol PD_ConsLEFT				mod_index STE_Constructor
				<=< adjustPredefSymbol PD_ConsRIGHT				mod_index STE_Constructor
				<=< adjustPredefSymbol PD_TypeCONS				mod_index STE_Type
				<=< adjustPredefSymbol PD_ConsCONS				mod_index STE_Constructor
				<=< adjustPredefSymbol PD_TypeFIELD				mod_index STE_Type
				<=< adjustPredefSymbol PD_ConsFIELD				mod_index STE_Constructor
				<=< adjustPredefSymbol PD_TypeOBJECT			mod_index STE_Type
				<=< adjustPredefSymbol PD_ConsOBJECT			mod_index STE_Constructor
				<=< adjustPredefSymbol PD_GenericInfo			mod_index STE_Type
				<=< adjustPredefSymbol PD_NoGenericInfo			mod_index STE_Constructor
				<=< adjustPredefSymbol PD_GenericConsInfo		mod_index STE_Constructor
				<=< adjustPredefSymbol PD_GenericFieldInfo		mod_index STE_Constructor
				<=< adjustPredefSymbol PD_GenericTypeInfo		mod_index STE_Constructor
				<=< adjustPredefSymbol PD_TGenericConsDescriptor mod_index STE_Type
				<=< adjustPredefSymbol PD_CGenericConsDescriptor mod_index STE_Constructor
				<=< adjustPredefSymbol PD_TGenericFieldDescriptor mod_index STE_Type
				<=< adjustPredefSymbol PD_CGenericFieldDescriptor mod_index STE_Constructor
				<=< adjustPredefSymbol PD_TGenericTypeDefDescriptor mod_index STE_Type
				<=< adjustPredefSymbol PD_CGenericTypeDefDescriptor mod_index STE_Constructor
				<=< adjustPredefSymbol PD_TGenConsPrio 			mod_index STE_Type
				<=< adjustPredefSymbol PD_CGenConsNoPrio 		mod_index STE_Constructor
				<=< adjustPredefSymbol PD_CGenConsPrio 			mod_index STE_Constructor
				<=< adjustPredefSymbol PD_TGenConsAssoc 		mod_index STE_Type
				<=< adjustPredefSymbol PD_CGenConsAssocNone 	mod_index STE_Constructor
				<=< adjustPredefSymbol PD_CGenConsAssocLeft 	mod_index STE_Constructor
				<=< adjustPredefSymbol PD_CGenConsAssocRight 	mod_index STE_Constructor
				<=< adjustPredefSymbol PD_TGenType 				mod_index STE_Type
				<=< adjustPredefSymbol PD_CGenTypeCons 			mod_index STE_Constructor
				<=< adjustPredefSymbol PD_CGenTypeVar 			mod_index STE_Constructor
				<=< adjustPredefSymbol PD_CGenTypeArrow 		mod_index STE_Constructor
				<=< adjustPredefSymbol PD_CGenTypeApp 			mod_index STE_Constructor

				<=< adjustPredefSymbol PD_GenericBimap			mod_index STE_Generic
				<=< adjustPredefSymbol PD_bimapId				mod_index STE_DclFunction				
				<=< adjustPredefSymbol PD_TypeGenericDict		mod_index STE_Type				
				)
		# (pre_mod, cs_predef_symbols) = cs_predef_symbols![PD_StdMisc]	
		| pre_mod.pds_def == mod_index
			= (class_members, class_instances, fun_types, { cs & cs_predef_symbols = cs_predef_symbols}
				<=< adjustPredefSymbol PD_abort				mod_index STE_DclFunction
				<=< adjustPredefSymbol PD_undef				mod_index STE_DclFunction)
		# (pre_mod, cs_predef_symbols) = cs_predef_symbols![PD_CleanTypes]	
		| pre_mod.pds_def == mod_index
			= (class_members, class_instances, fun_types, { cs & cs_predef_symbols = cs_predef_symbols}
			 <=< adjustPredefSymbol PD_CTTypeDef			mod_index STE_Type
			 <=< adjustPredefSymbol PD_CTAlgType			mod_index STE_Constructor
			 <=< adjustPredefSymbol PD_CTRecordType			mod_index STE_Constructor
			 <=< adjustPredefSymbol PD_CTSynType			mod_index STE_Constructor
			 <=< adjustPredefSymbol PD_CTPredefined			mod_index STE_Constructor
			 <=< adjustPredefSymbol PD_CTConsDef			mod_index STE_Type
			 <=< adjustPredefSymbol PD__CTToCons			mod_index STE_DclFunction
			 <=< adjustPredefSymbol PD_CTFieldDef			mod_index STE_Type )

			= (class_members, class_instances, fun_types, { cs & cs_predef_symbols = cs_predef_symbols})		
	where
		unused
			= { id_name = "unused", id_info = nilPtr }
					
		adjust_predef_symbols next_symb last_symb mod_index symb_kind cs
			| next_symb > last_symb
				= cs
				= cs
					<=< adjustPredefSymbol next_symb mod_index symb_kind
					<=< adjust_predef_symbols (inc next_symb) last_symb mod_index symb_kind

		adjust_predef_symbols_and_check_indices next_symb last_symb type_index mod_index symb_kind cs
			| next_symb > last_symb
				= cs
				= cs
					<=< adjustPredefSymbolAndCheckIndex next_symb mod_index type_index symb_kind
					<=< adjust_predef_symbols_and_check_indices (inc next_symb) last_symb (inc type_index) mod_index symb_kind

	count_members :: !Index !{# ClassInstance} !{# ClassDef} !{# DclModule} -> Int
	count_members mod_index com_instance_defs com_class_defs modules
		# (sum, _, _)
				= foldlArraySt (count_members_of_instance mod_index) com_instance_defs (0, com_class_defs, modules)
		= sum

	count_members_of_instance mod_index {ins_class} (sum, com_class_defs, modules)
		# ({class_members}, com_class_defs, modules)
			= getClassDef ins_class mod_index com_class_defs modules
 		= (size class_members + sum, com_class_defs, modules)

adjustPredefSymbol predef_index mod_index symb_kind cs=:{cs_symbol_table,cs_error}
	# pre_id = predefined_idents.[predef_index]
	#! pre_index = determine_index_of_symbol (sreadPtr pre_id.id_info cs_symbol_table) symb_kind
	| pre_index <> NoIndex
		= { cs & cs_predef_symbols.[predef_index] = { pds_def = pre_index, pds_module = mod_index }}
			//---> ("predef_index", predef_index, size predefined_idents)
		= { cs & cs_error = checkError pre_id " function not defined" cs_error }
where
	determine_index_of_symbol {ste_kind, ste_index} symb_kind
		| ste_kind == symb_kind
			= ste_index
			= NoIndex

adjustPredefSymbolAndCheckIndex predef_index mod_index symbol_index symb_kind cs=:{cs_symbol_table,cs_error}
	# pre_id = predefined_idents.[predef_index]
	#! pre_index = determine_index_of_symbol (sreadPtr pre_id.id_info cs_symbol_table) symb_kind
	| pre_index == symbol_index
		= { cs & cs_predef_symbols.[predef_index] = { pds_def = pre_index, pds_module = mod_index }}
		= { cs & cs_error = checkError pre_id " function not defined or wrong index in predef" cs_error }
where
	determine_index_of_symbol {ste_kind, ste_index} symb_kind
		| ste_kind == symb_kind
			= ste_index
			= NoIndex

NewEntry symbol_table symb_ptr def_kind def_index level previous :==
	 symbol_table <:= (symb_ptr,{  ste_kind = def_kind, ste_index = def_index, ste_def_level = level, ste_previous = previous })

instance <<< AuxiliaryPattern
where
	(<<<) file (AP_Algebraic symbol index patterns var)
		= file <<< symbol <<< ' ' <<< patterns
	(<<<) file (AP_Variable ident var_ptr var)
		= file <<< ident
	(<<<) file (AP_Basic val var)
		= file <<< val
	(<<<) file (AP_Constant kind symbol prio)
		= file <<< symbol
	(<<<) file (AP_WildCard _)
		= file <<< '_'
	(<<<) file (AP_Empty ident)
		= file <<< "<?" <<< ident <<< "?>"

instance <<< Priority
where
	(<<<) file (Prio ass prio) = file <<< "##" <<< prio <<< ass <<< "##"
	(<<<) file NoPrio = file <<< "#"

instance <<< Assoc
where
	(<<<) file LeftAssoc = file <<< 'L'
	(<<<) file RightAssoc = file <<< 'R'
	(<<<) file _ = file

instance <<< DefinedSymbol
where
	(<<<) file { ds_index, ds_ident } = file <<< ds_ident <<< '.' <<< ds_index
	
instance <<< Declarations
where
//	(<<<) file { dcls_import, dcls_local } = file <<< "I:" <<< dcls_import <<< "L:" <<< dcls_local
	(<<<) file { dcls_import, dcls_local } = file <<< "I:" <<< /*dcls_import <<< */ "L:" <<< dcls_local

instance <<< Specials
where
	(<<<) file (SP_ParsedSubstitutions _)	= file <<< "SP_ParsedSubstitutions"
	(<<<) file (SP_Substitutions substs)	= file <<< "SP_Substitutions " <<< substs
	(<<<) file (SP_ContextTypes specials)	= file <<< "SP_ContextTypes " <<< specials
	(<<<) file (SP_FunIndex _)				= file <<< "SP_ParsedSubstitutions"
	(<<<) file SP_None						= file <<< "SP_None"

instance <<< Special
where
	(<<<) file {spec_types} = file <<< spec_types


instance <<< SpecialSubstitution
where
	(<<<) file {ss_environ} = file <<< ss_environ

instance <<< (Ptr a)
where
	(<<<) file ptr = file <<< "[[" <<< ptrToInt ptr <<< "]]"

:: NodeNr				:== Int
:: ComponentNr			:== Int
:: NodesToComponents	:== {#ComponentNr}	// mapping from node numbers to component numbers

getComponentNumbers :: ![[NodeNr]] !Int -> (!Int, !.{#ComponentNr})
getComponentNumbers components nr_of_nodes
	# nodes_to_components
			= createArray nr_of_nodes cUndef
	= foldSt get_component_numbers components (0, nodes_to_components)
  where
	get_component_numbers component (component_nr, nodes_to_components)
		= ( component_nr+1
		  , foldSt (\node_nr nodes_to_components -> { nodes_to_components & [node_nr] = component_nr })
					component nodes_to_components
		  )

reverseDAG :: !DAG -> {![NodeNr]}
reverseDAG { dag_nr_of_nodes, dag_get_children }
	# reversed_children
			= createArray dag_nr_of_nodes []
	= iFoldSt reverse_arrows_of_node 0 dag_nr_of_nodes reversed_children
  where
	reverse_arrows_of_node parent_node_nr reversed_children
		# children
				= dag_get_children parent_node_nr
		= foldSt (reverse_arrow parent_node_nr) children reversed_children
	reverse_arrow parent_node_nr child_node_nr reversed_children
		# (current_parents, reversed_children)
				= reversed_children![child_node_nr]
		= { reversed_children & [child_node_nr] = [parent_node_nr : current_parents] }
		  

groupify :: !DAG !{#ComponentNr} !Int -> .{![ComponentNr]}
groupify { dag_nr_of_nodes, dag_get_children } component_numbers nr_of_components
	# visited_array
			= createArray nr_of_components False
	  node_to_components
	  		= createArray dag_nr_of_nodes []
	= snd (iFoldSt (groupifyPerNode component_numbers) 0 dag_nr_of_nodes (visited_array, node_to_components))
  where
	groupifyPerNode component_numbers node_nr (visited_array, node_to_components)
		// all i: not visited.[i]
		# children
				= dag_get_children node_nr
		  (visited_array, visited_list, node_to_components)
				= foldSt (groupifyPerArrow component_numbers node_nr) children (visited_array, [], node_to_components)
		  visited_array
		  		= foldSt (\i visited_array->{ visited_array & [i] = False }) visited_list visited_array
		= (visited_array, node_to_components)
	groupifyPerArrow :: !{#ComponentNr} !Int !Int !(!*{#Bool}, ![Int], !*{![ComponentNr]})
					-> (!.{#Bool}, ![Int], !.{![ComponentNr]})
	groupifyPerArrow component_numbers node_nr child_node_nr (visited_array, visited_list, node_to_components)
		# child_component_number
				= component_numbers.[child_node_nr]
		| visited_array.[child_component_number] || child_component_number==component_numbers.[node_nr]
			= (visited_array, visited_list, node_to_components)
		# (current_components, node_to_components)
				= node_to_components![node_nr]
		= ({ visited_array & [child_component_number] = True }, [child_component_number : visited_list],
			{ node_to_components & [node_nr] = [child_component_number:current_components] })
