implementation module check

import StdEnv

import syntax, typesupport, parse, checksupport, utilities, checktypes, transform, predef
import explicitimports, comparedefimp, checkFunctionBodies, containers, portToNewSyntax

cPredefinedModuleIndex 	:== 1
cUndef :== (-1)
cDummyArray :== {}

isMainModule :: ModuleKind -> Bool
isMainModule MK_Main	= True
isMainModule _ 			= False



checkTypeClasses :: !Index !Index !*{#ClassDef} !*{#MemberDef} !*{#CheckedTypeDef} !*{#DclModule} !*TypeHeaps !*CheckState
	-> (!*{#ClassDef}, !*{#MemberDef}, !*{#CheckedTypeDef}, !*{#DclModule}, !*TypeHeaps, !*CheckState)
checkTypeClasses class_index module_index class_defs member_defs type_defs modules type_heaps=:{th_vars} cs=:{cs_symbol_table,cs_error}
	| class_index == size class_defs
		= (class_defs, member_defs, type_defs, modules, type_heaps, cs)
		# (class_def=:{class_name,class_pos,class_args,class_context,class_members}, class_defs) = class_defs![class_index]
		  position = newPosition class_name class_pos
		  cs_error = setErrorAdmin position cs_error
		  (rev_class_args, cs_symbol_table, th_vars, cs_error)
		  		= add_variables_to_symbol_table cGlobalScope class_args [] cs_symbol_table th_vars cs_error
		  cs = {cs & cs_symbol_table = cs_symbol_table, cs_error = cs_error }
		  (class_context, type_defs, class_defs, modules, type_heaps, cs)
		  		= checkTypeContexts class_context module_index type_defs class_defs modules { type_heaps & th_vars = th_vars } cs
		  (class_args, cs_symbol_table) = retrieve_variables_from_symbol_table rev_class_args [] cs.cs_symbol_table
		  class_defs = { class_defs & [class_index] = { class_def & class_context = class_context, class_args = class_args }}
		  member_defs = set_classes_in_member_defs 0 class_members {glob_object = class_index, glob_module = module_index} member_defs 
		= checkTypeClasses (inc class_index) module_index class_defs member_defs type_defs modules type_heaps { cs & cs_symbol_table = cs_symbol_table }
where
	add_variables_to_symbol_table :: !Level ![TypeVar] ![TypeVar] !*SymbolTable !*TypeVarHeap !*ErrorAdmin
		-> (![TypeVar],!*SymbolTable,!*TypeVarHeap,!*ErrorAdmin)
	add_variables_to_symbol_table level [] rev_class_args symbol_table th_vars error
		= (rev_class_args, symbol_table, th_vars, error)
	add_variables_to_symbol_table level [var=:{tv_name={id_name,id_info}} : vars] rev_class_args symbol_table th_vars error
	  	# (entry, symbol_table) = readPtr id_info symbol_table
		| entry.ste_kind == STE_Empty || entry.ste_def_level < level
			# (new_var_ptr, th_vars) = newPtr TVI_Empty th_vars
			# symbol_table = NewEntry symbol_table id_info (STE_TypeVariable new_var_ptr) NoIndex level entry
			= add_variables_to_symbol_table level vars [{ var & tv_info_ptr = new_var_ptr} : rev_class_args] symbol_table th_vars error
			= add_variables_to_symbol_table level  vars rev_class_args symbol_table th_vars (checkError id_name "(variable) already defined" error)

	retrieve_variables_from_symbol_table :: ![TypeVar] ![TypeVar] !*SymbolTable -> (![TypeVar],!*SymbolTable)
	retrieve_variables_from_symbol_table [var=:{tv_name={id_name,id_info}} : vars] class_args symbol_table
		# (entry, symbol_table) = readPtr id_info symbol_table
		= retrieve_variables_from_symbol_table vars [var : class_args] (symbol_table <:= (id_info,entry.ste_previous))
	retrieve_variables_from_symbol_table [] class_args symbol_table
		= (class_args, symbol_table)
	
	set_classes_in_member_defs mem_offset class_members glob_class_index member_defs
		| mem_offset == size class_members
			= member_defs
			# {ds_index} = class_members.[mem_offset]
			# (member_def, member_defs) = member_defs![ds_index]
			= set_classes_in_member_defs (inc mem_offset) class_members glob_class_index { member_defs & [ds_index] = { member_def & me_class = glob_class_index }}

	
checkSpecial :: !Index !FunType !Index !SpecialSubstitution (!Index, ![FunType], !*Heaps, !*ErrorAdmin)
	-> (!Special, (!Index, ![FunType], !*Heaps, !*ErrorAdmin))
checkSpecial mod_index fun_type=:{ft_type} fun_index subst (next_inst_index, special_types, heaps, error)
	# (special_type, hp_type_heaps) = substitute_type ft_type subst heaps.hp_type_heaps
	  (spec_types, error) = checkAndCollectTypesOfContexts special_type.st_context error
	  ft_type = { special_type & st_context = [] }
	  (new_info_ptr, hp_var_heap) = newPtr VI_Empty heaps.hp_var_heap
	= ( { spec_index = { glob_module = mod_index, glob_object = next_inst_index }, spec_types = spec_types, spec_vars = subst.ss_vars, spec_attrs = subst.ss_attrs },
			((inc next_inst_index), [{ fun_type & ft_type = ft_type, ft_specials = SP_FunIndex fun_index, ft_type_ptr = new_info_ptr} : special_types ],
					{ heaps & hp_type_heaps = hp_type_heaps, hp_var_heap = hp_var_heap }, error))
where	
	substitute_type st=:{st_vars,st_attr_vars,st_args,st_result,st_context,st_attr_env} environment type_heaps
		# (st_vars, st_attr_vars, [st_result : st_args], st_context, st_attr_env, _, type_heaps)
			= instantiateTypes st_vars st_attr_vars [ st_result : st_args ] st_context st_attr_env environment [] type_heaps
		= ({st & st_vars = st_vars, st_args = st_args, st_result = st_result, st_attr_vars = st_attr_vars,
			st_context = st_context, st_attr_env = st_attr_env }, type_heaps)

checkDclFunctions :: !Index !Index ![FunType] !v:{#CheckedTypeDef} !x:{#ClassDef} !v:{#.DclModule} !*Heaps !*CheckState
	-> (!Index, ![FunType], ![FunType], !v:{#CheckedTypeDef}, !x:{#ClassDef}, !v:{#DclModule}, !*Heaps, !*CheckState)
checkDclFunctions module_index first_inst_index fun_types type_defs class_defs modules heaps cs
	= check_dcl_functions module_index fun_types 0 first_inst_index [] [] type_defs class_defs modules heaps cs
where
	check_dcl_functions ::  !Index ![FunType]   !Index  !Index ![FunType] ![FunType] !v:{#CheckedTypeDef} !x:{#ClassDef} !v:{#DclModule} !*Heaps !*CheckState
		 -> (!Index, ![FunType], ![FunType],!v:{#CheckedTypeDef}, !x:{#ClassDef}, !v:{#DclModule}, !*Heaps, !*CheckState)
	check_dcl_functions module_index [] fun_index next_inst_index collected_funtypes collected_instances type_defs class_defs modules heaps cs
		= (next_inst_index, collected_funtypes, collected_instances, type_defs, class_defs, modules, heaps, cs)
	check_dcl_functions module_index [fun_type=:{ft_symb,ft_type,ft_pos,ft_specials} : fun_types] fun_index
			next_inst_index collected_funtypes collected_instances type_defs class_defs modules heaps cs
		# position = newPosition ft_symb ft_pos
		  cs = { cs & cs_error = setErrorAdmin position cs.cs_error }
		  (ft_type, ft_specials, type_defs,  class_defs, modules, hp_type_heaps, cs)
		  		= checkSymbolType module_index ft_type ft_specials type_defs class_defs modules heaps.hp_type_heaps cs
		  (spec_types, next_inst_index, collected_instances, heaps, cs_error)
		  		= check_specials module_index { fun_type & ft_type = ft_type } fun_index ft_specials next_inst_index collected_instances
		  				{ heaps & hp_type_heaps = hp_type_heaps } cs.cs_error
		  (new_info_ptr, hp_var_heap) = newPtr VI_Empty heaps.hp_var_heap
		= check_dcl_functions module_index fun_types (inc fun_index) next_inst_index [
				{ fun_type & ft_type = ft_type, ft_specials = spec_types, ft_type_ptr = new_info_ptr } : collected_funtypes]
					collected_instances type_defs class_defs modules { heaps & hp_var_heap = hp_var_heap } { cs & cs_error = cs_error }

	check_specials :: !Index !FunType !Index !Specials !Index ![FunType] !*Heaps !*ErrorAdmin
		-> (!Specials, !Index, ![FunType], !*Heaps, !*ErrorAdmin)
	check_specials mod_index fun_type fun_index (SP_Substitutions substs) next_inst_index all_instances heaps error
		# (list_of_specials, (next_inst_index, all_instances, heaps, cs_error))
				= mapSt (checkSpecial mod_index fun_type fun_index) substs (next_inst_index, all_instances, heaps, error)
		= (SP_ContextTypes list_of_specials, next_inst_index, all_instances, heaps, cs_error)
	check_specials mod_index fun_type fun_index SP_None next_inst_index all_instances heaps error
		= (SP_None, next_inst_index, all_instances, heaps, error)


checkSpecialsOfInstances :: !Index !Index ![ClassInstance] !Index ![ClassInstance] ![FunType] {# FunType} *{! [Special] } !*Heaps !*ErrorAdmin
		-> (!Index, ![ClassInstance], ![FunType], !*{! [Special]}, !*Heaps, !*ErrorAdmin)
checkSpecialsOfInstances mod_index first_mem_index [class_inst=:{ins_members,ins_specials} : class_insts] next_inst_index all_class_instances all_specials
		new_inst_defs all_spec_types heaps error
	= case ins_specials of
		SP_TypeOffset type_offset
			# (next_inst_index, rev_mem_specials, all_specials, all_spec_types, heaps, error)
				= check_and_build_members mod_index first_mem_index 0 ins_members type_offset next_inst_index [] all_specials new_inst_defs all_spec_types heaps error
			  class_inst = { class_inst & ins_members = { mem \\ mem <- reverse rev_mem_specials } }
			-> checkSpecialsOfInstances mod_index first_mem_index class_insts next_inst_index [class_inst : all_class_instances]
					all_specials new_inst_defs all_spec_types heaps error
		SP_None
			-> checkSpecialsOfInstances mod_index first_mem_index class_insts next_inst_index [class_inst : all_class_instances]
					all_specials new_inst_defs all_spec_types heaps error
where
	check_and_build_members :: !Index !Index !Int {# DefinedSymbol} !Int !Index ![DefinedSymbol] ![FunType] !{#FunType} !*{! [Special]} !*Heaps !*ErrorAdmin
		-> (!Index, ![DefinedSymbol], ![FunType], !*{! [Special]}, !*Heaps, !*ErrorAdmin)
	check_and_build_members mod_index first_mem_index member_offset ins_members type_offset next_inst_index rev_mem_specials all_specials inst_spec_defs
			all_spec_types heaps error
		| member_offset < size ins_members
			# member = ins_members.[member_offset]
			  member_index = member.ds_index
			  spec_member_index = member_index - first_mem_index
		 	# (spec_types, all_spec_types) = all_spec_types![spec_member_index]
		 	# mem_inst = inst_spec_defs.[spec_member_index]
		 	  (SP_Substitutions specials) = mem_inst.ft_specials
		 	  env = specials !! type_offset
			  member = { member & ds_index = next_inst_index }
			  (spec_type, (next_inst_index, all_specials, heaps, error))
			  		= checkSpecial mod_index mem_inst member_index env (next_inst_index, all_specials, heaps, error)
			  all_spec_types = { all_spec_types & [spec_member_index] = [ spec_type : spec_types] }
			= check_and_build_members mod_index first_mem_index (inc member_offset) ins_members type_offset next_inst_index [ member : rev_mem_specials ]
					all_specials inst_spec_defs all_spec_types heaps error
			= (next_inst_index, rev_mem_specials, all_specials, all_spec_types, heaps, error)

checkSpecialsOfInstances mod_index first_mem_index [] next_inst_index all_class_instances all_specials inst_spec_defs all_spec_types heaps error
	= (next_inst_index, all_class_instances, all_specials, all_spec_types, heaps, error)	

checkMemberTypes :: !Index !*{#MemberDef} !*{#CheckedTypeDef} !*{#ClassDef} !*{#DclModule} !*TypeHeaps !*VarHeap !*CheckState
	-> (!*{#MemberDef}, !*{#CheckedTypeDef}, !*{#ClassDef}, !*{#DclModule}, !*TypeHeaps,  !*VarHeap, !*CheckState)
checkMemberTypes module_index member_defs type_defs class_defs modules type_heaps var_heap cs
	#! nr_of_members = size member_defs
	= iFoldSt (check_class_member module_index) 0 nr_of_members (member_defs, type_defs, class_defs, modules, type_heaps, var_heap, cs)
where
	check_class_member module_index member_index (member_defs, type_defs, class_defs, modules, type_heaps, var_heap, cs)
		# (member_def=:{me_symb,me_type,me_pos}, member_defs) = member_defs![member_index]
		  position = newPosition me_symb me_pos
		  cs = { cs & cs_error = setErrorAdmin position cs.cs_error }
		  (me_type, _, type_defs, class_defs, modules, type_heaps, cs)
		   		= checkSymbolType module_index me_type SP_None type_defs class_defs modules type_heaps cs
		  me_class_vars = map (\(TV type_var) -> type_var) (hd me_type.st_context).tc_types
		  (me_type_ptr, var_heap) = newPtr VI_Empty var_heap		   
		= ({ member_defs & [member_index] = { member_def & me_type = me_type, me_class_vars = me_class_vars, me_type_ptr = me_type_ptr }},
				type_defs, class_defs, modules, type_heaps, var_heap, cs)

::	InstanceSymbols =
	{	is_type_defs		:: !.{# CheckedTypeDef}
	,	is_class_defs		:: !.{# ClassDef}
	,	is_member_defs		:: !.{# MemberDef}
	,	is_modules			:: !.{# DclModule}
	}

checkInstanceDefs :: !Index !*{#ClassInstance} !u:{#CheckedTypeDef} !u:{#ClassDef} !u:{#MemberDef} !u:{#DclModule} !*TypeHeaps !*CheckState
	-> (!.{#ClassInstance},!u:{#CheckedTypeDef},!u:{#ClassDef},!u:{#MemberDef},!u:{#DclModule},!.TypeHeaps,!.CheckState)
checkInstanceDefs mod_index instance_defs type_defs class_defs member_defs modules type_heaps cs
	# is = { is_type_defs = type_defs, is_class_defs = class_defs, is_member_defs = member_defs, is_modules = modules }
	  (instance_defs, is, type_heaps, cs) = check_instance_defs 0 mod_index instance_defs is type_heaps cs
	= (instance_defs, is.is_type_defs, is.is_class_defs, is.is_member_defs, is.is_modules, type_heaps, cs)
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
			ins=:{ins_members,ins_class={glob_object = class_name =: {ds_ident = {id_name,id_info},ds_arity}},ins_type,ins_specials,ins_pos,ins_ident}
			is=:{is_class_defs,is_modules} type_heaps cs=:{cs_symbol_table}
		# (entry, cs_symbol_table) = readPtr id_info cs_symbol_table
		# (class_index, class_mod_index, class_def, is_class_defs, is_modules) = get_class_def entry module_index is_class_defs is_modules
		  is = { is & is_class_defs = is_class_defs, is_modules = is_modules }
		  cs = pushErrorAdmin (newPosition ins_ident ins_pos) { cs & cs_symbol_table = cs_symbol_table }
		| class_index <> NotFound
			| class_def.class_arity == ds_arity
				# ins_class = { glob_object = { class_name & ds_index = class_index }, glob_module = class_mod_index}
				  (ins_type, ins_specials, is_type_defs, is_class_defs, is_modules, type_heaps, cs)
				  		= checkInstanceType module_index ins_class ins_type ins_specials
								is.is_type_defs is.is_class_defs is.is_modules type_heaps cs
				  is = { is & is_type_defs = is_type_defs, is_class_defs = is_class_defs, is_modules = is_modules }
				= ({ins & ins_class = ins_class, ins_type = ins_type, ins_specials = ins_specials}, is, type_heaps, popErrorAdmin cs)
				= ( ins
				  , is
				  , type_heaps
				  , popErrorAdmin { cs & cs_error = checkError id_name ("wrong arity: expected "+++toString class_def.class_arity+++" found "+++toString ds_arity) cs.cs_error }
				  )
			= (ins, is, type_heaps, popErrorAdmin { cs & cs_error = checkError id_name "class undefined" cs.cs_error })

	get_class_def :: !SymbolTableEntry !Index v:{# ClassDef} u:{# DclModule} -> (!Index,!Index,ClassDef,!v:{# ClassDef},!u:{# DclModule})
	get_class_def {ste_kind = STE_Class, ste_index} mod_index class_defs modules
		# (class_def, class_defs) = class_defs![ste_index]
		= (ste_index, mod_index, class_def, class_defs, modules)
	get_class_def {ste_kind = STE_Imported STE_Class dcl_index, ste_index, ste_def_level} mod_index  class_defs modules
		# (dcl_mod, modules) = modules![dcl_index]
		# class_def = dcl_mod.dcl_common.com_class_defs.[ste_index]
		= (ste_index, dcl_index, class_def, class_defs, modules)
	get_class_def _ mod_index class_defs modules
		= (NotFound, -1/*cIclModIndex*/, abort "no class definition", class_defs, modules)
	
checkInstances :: !Index !*CommonDefs !u:{# DclModule} !*VarHeap !*TypeHeaps !*CheckState
	-> (![(Index,SymbolType)], !*CommonDefs, !u:{# DclModule}, !*VarHeap , !*TypeHeaps, !*CheckState)
checkInstances mod_index icl_common=:{com_instance_defs,com_class_defs,com_member_defs} modules var_heap type_heaps cs=:{cs_error}
	| cs_error.ea_ok
		# (instance_types, com_instance_defs, com_class_defs, com_member_defs, modules, var_heap, type_heaps, cs)
				= check_instances 0 mod_index [] com_instance_defs com_class_defs com_member_defs modules var_heap type_heaps cs
		= (instance_types, { icl_common & com_instance_defs = com_instance_defs,com_class_defs = com_class_defs,com_member_defs = com_member_defs },
			 	modules, var_heap, type_heaps, cs)
		= ([], icl_common, modules, var_heap, type_heaps, cs)
where
	check_instances :: !Index !Index ![(Index,SymbolType)] !x:{# ClassInstance} !w:{# ClassDef} !v:{# MemberDef} !u:{# DclModule}
		!*VarHeap !*TypeHeaps !*CheckState
			-> (![(Index,SymbolType)], !x:{# ClassInstance}, !w:{# ClassDef}, !v:{# MemberDef}, !u:{# DclModule}, !*VarHeap, !*TypeHeaps, !*CheckState)
	check_instances inst_index mod_index instance_types instance_defs class_defs member_defs modules var_heap type_heaps cs
		| inst_index < size instance_defs
			# ({ins_class,ins_members,ins_type}, instance_defs) = instance_defs![inst_index]
			# ({class_members,class_name}, class_defs, modules) = getClassDef ins_class mod_index class_defs modules
			  class_size = size class_members
			| class_size == size ins_members
				# (instance_types, member_defs, modules, var_heap, type_heaps, cs) = check_member_instances mod_index ins_class.glob_module
			  	         0 class_size ins_members class_members ins_type instance_types member_defs modules var_heap type_heaps cs
				= check_instances (inc inst_index) mod_index instance_types instance_defs class_defs member_defs modules var_heap type_heaps cs
				= check_instances (inc inst_index) mod_index instance_types instance_defs class_defs member_defs modules var_heap type_heaps
						{ cs & cs_error = checkError class_name "different number of members specified" cs.cs_error }
			= (instance_types, instance_defs, class_defs, member_defs, modules, var_heap, type_heaps, cs)

	check_member_instances :: !Index !Index !Int !Int !{#DefinedSymbol} !{#DefinedSymbol} !InstanceType ![(Index,SymbolType)]
		!v:{# MemberDef} !u:{# DclModule} !*VarHeap !*TypeHeaps !*CheckState
			-> (![(Index,SymbolType)], !v:{# MemberDef}, !u:{# DclModule},!*VarHeap, !*TypeHeaps, !*CheckState)

	check_member_instances module_index member_mod_index mem_offset class_size ins_members class_members
				ins_type instance_types member_defs modules var_heap type_heaps cs
		| mem_offset == class_size
			= (instance_types, member_defs, modules, var_heap, type_heaps, cs)
			# ins_member = ins_members.[mem_offset]
			  class_member = class_members.[mem_offset]
			| ins_member.ds_ident <> class_member.ds_ident
				= check_member_instances module_index member_mod_index (inc mem_offset) class_size ins_members class_members ins_type 
						instance_types member_defs modules var_heap type_heaps
							{ cs & cs_error = checkError class_member.ds_ident "instance of class member expected" cs.cs_error}
			| ins_member.ds_arity <> class_member.ds_arity
				= check_member_instances module_index member_mod_index (inc mem_offset) class_size ins_members class_members ins_type
						instance_types member_defs modules var_heap type_heaps
							{ cs & cs_error = checkError class_member.ds_ident "used with wrong arity" cs.cs_error}
				# ({me_type,me_class_vars}, member_defs, modules) = getMemberDef member_mod_index class_member.ds_index module_index member_defs modules
				  (instance_type, _, type_heaps) = determineTypeOfMemberInstance me_type me_class_vars ins_type SP_None type_heaps
				  (st_context, var_heap) = initializeContextVariables instance_type.st_context var_heap
				= check_member_instances module_index member_mod_index (inc mem_offset) class_size ins_members class_members ins_type
						[ (ins_member.ds_index, { instance_type & st_context = st_context }) : instance_types ] member_defs modules var_heap type_heaps cs

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

instantiateTypes :: ![TypeVar] ![AttributeVar] !types ![TypeContext] ![AttrInequality] !SpecialSubstitution ![SpecialSubstitution] !*TypeHeaps
	-> (![TypeVar], ![AttributeVar], !types , ![TypeContext], ![AttrInequality], ![SpecialSubstitution], !*TypeHeaps) | substitute types
instantiateTypes old_type_vars old_attr_vars types type_contexts attr_env {ss_environ, ss_vars, ss_attrs, ss_context} special_subst_list type_heaps=:{th_vars, th_attrs}
	# th_vars = clear_vars old_type_vars th_vars

	  (new_type_vars, th_vars) = foldSt build_var_subst ss_vars ([], th_vars)
	  (new_attr_vars, th_attrs) = foldSt build_attr_subst ss_attrs ([], th_attrs)

	  type_heaps = foldSt build_type_subst ss_environ { type_heaps & th_vars = th_vars, th_attrs = th_attrs }
	  (new_ss_context, type_heaps) = substitute ss_context type_heaps

	  (inst_vars, th_vars) =  foldSt determine_free_var old_type_vars (new_type_vars, type_heaps.th_vars) 
	  (inst_attr_vars, th_attrs) = foldSt build_attr_subst old_attr_vars (new_attr_vars, type_heaps.th_attrs)

	  (inst_types, type_heaps)		= substitute types { type_heaps & th_vars = th_vars, th_attrs = th_attrs }
	  (inst_contexts, type_heaps)	= substitute type_contexts type_heaps
	  (inst_attr_env, type_heaps)	= substitute attr_env type_heaps
	  
	  (special_subst_list, th_vars) =  mapSt adjust_special_subst special_subst_list type_heaps.th_vars

	= (inst_vars, inst_attr_vars, inst_types, inst_contexts ++ new_ss_context, inst_attr_env, special_subst_list, { type_heaps & th_vars = th_vars })
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
		= { type_heaps & th_vars = writePtr bind_dst.tv_info_ptr (TVI_Type bind_src) type_heaps.th_vars}

	build_var_subst var (free_vars, type_var_heap)
		# (new_info_ptr, type_var_heap) = newPtr TVI_Empty type_var_heap
		  new_fv = { var & tv_info_ptr = new_info_ptr}
	  	= ([ new_fv : free_vars ], writePtr var.tv_info_ptr (TVI_Type (TV new_fv)) type_var_heap)

	build_attr_subst attr (free_attrs, attr_var_heap)
		# (new_info_ptr, attr_var_heap) = newPtr AVI_Empty attr_var_heap
		  new_attr = { attr & av_info_ptr = new_info_ptr}
		= ([new_attr : free_attrs], writePtr attr.av_info_ptr (AVI_Attr (TA_Var new_attr)) attr_var_heap)
	
	adjust_special_subst special_subst=:{ss_environ} type_var_heap
		# (ss_environ, type_var_heap) = mapSt adjust_special_bind ss_environ type_var_heap
		= ({ special_subst & ss_environ = ss_environ }, type_var_heap)
		
	adjust_special_bind bind=:{bind_dst={tv_info_ptr}} type_var_heap
		# (TVI_Type (TV new_tv), type_var_heap) = readPtr tv_info_ptr type_var_heap
		= ({ bind & bind_dst = new_tv }, type_var_heap)

substituteInstanceType :: !InstanceType !SpecialSubstitution !*TypeHeaps -> (!InstanceType,!*TypeHeaps)
substituteInstanceType it=:{it_vars,it_attr_vars,it_types,it_context} environment type_heaps
	# (it_vars, it_attr_vars, it_types, it_context, _, _, type_heaps)
		= instantiateTypes it_vars it_attr_vars it_types it_context [] environment [] type_heaps
	= ({it & it_vars = it_vars, it_types = it_types, it_attr_vars = it_attr_vars, it_context = it_context }, type_heaps)

hasTypeVariables []
	= False
hasTypeVariables [TV tvar : types]
	= True
hasTypeVariables [ _ : types]
	= hasTypeVariables types

determineTypeOfMemberInstance :: !SymbolType ![TypeVar] !InstanceType !Specials !*TypeHeaps -> (!SymbolType, !Specials, !*TypeHeaps)
determineTypeOfMemberInstance mem_st class_vars {it_types,it_vars,it_attr_vars,it_context} specials type_heaps
	# env = { ss_environ = foldl2 (\binds var type -> [ {bind_src = type, bind_dst = var} : binds]) [] class_vars it_types,
			  ss_context = it_context, ss_vars = it_vars, ss_attrs = it_attr_vars} 
	= determine_type_of_member_instance mem_st env specials type_heaps
where
	determine_type_of_member_instance mem_st=:{st_context} env (SP_Substitutions substs) type_heaps
		# (mem_st, substs, type_heaps) = substitute_symbol_type { mem_st &  st_context = tl st_context } env substs type_heaps
		= (mem_st, SP_Substitutions substs, type_heaps) 
	determine_type_of_member_instance mem_st=:{st_context} env SP_None type_heaps
		# (mem_st, _, type_heaps) = substitute_symbol_type { mem_st &  st_context = tl st_context } env [] type_heaps 
		= (mem_st, SP_None, type_heaps)

	substitute_symbol_type st=:{st_vars,st_attr_vars,st_args,st_result,st_context,st_attr_env} environment specials type_heaps
		# (st_vars, st_attr_vars, [st_result : st_args], st_context, st_attr_env, specials, type_heaps)
			= instantiateTypes st_vars st_attr_vars [ st_result : st_args ] st_context st_attr_env environment specials type_heaps
		= ({st & st_vars = st_vars, st_args = st_args, st_result = st_result, st_attr_vars = st_attr_vars,
			st_context = st_context, st_attr_env = st_attr_env }, specials, type_heaps)

determineTypesOfInstances :: !Index !Index !*{#ClassInstance} !*{# ClassDef} !*{# MemberDef}
							 !*{#DclModule} !*TypeHeaps !*VarHeap !*CheckState
	-> (![FunType], !Index, ![ClassInstance], !*{#ClassInstance}, !*{# ClassDef}, !*{# MemberDef}, !*{#DclModule}, !*TypeHeaps, !*VarHeap, !*CheckState)
determineTypesOfInstances first_memb_inst_index mod_index com_instance_defs com_class_defs com_member_defs
		modules type_heaps var_heap cs=:{cs_error}
	| cs_error.ea_ok
		#! nr_of_class_instances = size com_instance_defs
		# (memb_inst_defs, next_mem_inst_index, all_class_specials, com_class_defs, com_member_defs, modules, com_instance_defs, type_heaps, var_heap, cs_error)
				= determine_types_of_instances 0 nr_of_class_instances first_memb_inst_index mod_index [] com_class_defs com_member_defs
						modules com_instance_defs type_heaps var_heap cs_error
		= (memb_inst_defs, next_mem_inst_index, all_class_specials, com_instance_defs, com_class_defs,
		   com_member_defs, modules, type_heaps, var_heap, { cs & cs_error = cs_error })
		= ([], first_memb_inst_index, [], com_instance_defs, com_class_defs, com_member_defs, modules, type_heaps, var_heap, cs)
where

	determine_types_of_instances :: !Index !Index !Index !Index ![ClassInstance] !v:{#ClassDef} !w:{#MemberDef}
		!x:{#DclModule} !*{#ClassInstance} !*TypeHeaps !*VarHeap !*ErrorAdmin
			-> (![FunType], !Index, ![ClassInstance], !v:{#ClassDef}, !w:{#MemberDef}, !x:{#DclModule}, !*{#ClassInstance}, !*TypeHeaps, !*VarHeap, !*ErrorAdmin)
	determine_types_of_instances inst_index next_class_inst_index next_mem_inst_index mod_index all_class_specials
			class_defs member_defs modules instance_defs type_heaps var_heap error
		| inst_index < size instance_defs
			# (instance_def, instance_defs) = instance_defs![inst_index]
			# {ins_class,ins_pos,ins_type,ins_specials} = instance_def
			  ({class_members}, class_defs, modules) = getClassDef ins_class mod_index class_defs modules
			  class_size = size class_members
			  (ins_members, memb_inst_defs1, member_defs, modules, type_heaps, var_heap)
			  		= determine_instance_symbols_and_types next_mem_inst_index 0 mod_index ins_class.glob_module class_size class_members
			  				ins_type ins_specials ins_pos member_defs modules type_heaps var_heap
			  instance_def = { instance_def & ins_members = { member \\ member <- ins_members }}
			  (ins_specials, next_class_inst_index, all_class_specials, type_heaps, error)
					= check_instance_specials mod_index instance_def inst_index ins_specials next_class_inst_index all_class_specials type_heaps error
			  (memb_inst_defs2, next_mem_inst_index, all_class_specials, class_defs, member_defs, modules, instance_defs, type_heaps, var_heap, error)
			  		= determine_types_of_instances (inc inst_index) next_class_inst_index (next_mem_inst_index + class_size) mod_index all_class_specials
			  				class_defs member_defs modules { instance_defs & [inst_index] = { instance_def & ins_specials = ins_specials }} type_heaps var_heap error

			= (memb_inst_defs1 ++ memb_inst_defs2, next_mem_inst_index, all_class_specials, class_defs, member_defs, modules, instance_defs, type_heaps, var_heap, error)
			= ([], next_mem_inst_index, all_class_specials, class_defs, member_defs, modules, instance_defs, type_heaps, var_heap, error)

	determine_instance_symbols_and_types :: !Index !Index !Index !Index !Int !{#DefinedSymbol} !InstanceType !Specials !Position
			!w:{#MemberDef} !u:{#DclModule} !*TypeHeaps !*VarHeap
					-> (![DefinedSymbol], ![FunType], !w:{#MemberDef}, !u:{#DclModule}, !*TypeHeaps, !*VarHeap)
	determine_instance_symbols_and_types first_inst_index mem_offset module_index member_mod_index class_size class_members
			ins_type ins_specials ins_pos member_defs modules type_heaps var_heap
		| mem_offset == class_size
			=  ([], [], member_defs, modules, type_heaps, var_heap)
			# class_member = class_members.[mem_offset]
			  ({me_symb,me_type,me_priority,me_class_vars}, member_defs, modules) = getMemberDef member_mod_index class_member.ds_index module_index member_defs modules
			  (instance_type, new_ins_specials, type_heaps) = determineTypeOfMemberInstance me_type me_class_vars ins_type ins_specials type_heaps
			  (new_info_ptr, var_heap) = newPtr VI_Empty var_heap
			  inst_def = MakeNewFunctionType me_symb me_type.st_arity me_priority instance_type ins_pos new_ins_specials new_info_ptr
			  (inst_symbols, memb_inst_defs, member_defs, modules, type_heaps, var_heap)
			  		= determine_instance_symbols_and_types first_inst_index (inc mem_offset) module_index member_mod_index
			  				class_size class_members ins_type ins_specials ins_pos member_defs modules type_heaps var_heap
			= ([{ class_member & ds_index = first_inst_index +  mem_offset } : inst_symbols], [inst_def : memb_inst_defs], member_defs, modules, type_heaps, var_heap)

	check_instance_specials :: !Index !ClassInstance !Index !Specials !Index ![ClassInstance] !*TypeHeaps !*ErrorAdmin
		-> (!Specials, !Index, ![ClassInstance], !*TypeHeaps, !*ErrorAdmin)
	check_instance_specials mod_index inst_type inst_index (SP_Substitutions substs) next_inst_index all_instances type_heaps error
		# (list_of_specials, next_inst_index, all_instances, type_heaps, error)
			= check_specials mod_index inst_type 0 substs [] next_inst_index all_instances type_heaps error
		= (SP_ContextTypes list_of_specials, next_inst_index, all_instances, type_heaps, error)
	where
		check_specials mod_index inst=:{ins_type} type_offset [ subst : substs ] list_of_specials next_inst_index all_instances type_heaps error
			# (special_type, type_heaps) = substituteInstanceType ins_type subst type_heaps
			  (spec_types, error) = checkAndCollectTypesOfContexts special_type.it_context error
			  special = { spec_index = { glob_module = mod_index, glob_object = next_inst_index }, spec_types = spec_types,
			  				spec_vars = subst.ss_vars, spec_attrs = subst.ss_attrs }
			= check_specials mod_index inst (inc type_offset) substs [ special : list_of_specials ] (inc next_inst_index)
					[{ inst & ins_type = { special_type & it_context = [] }, ins_specials = SP_TypeOffset type_offset} : all_instances ] type_heaps error
		check_specials mod_index inst=:{ins_type} type_offset [] list_of_specials next_inst_index all_instances type_heaps error
			= (list_of_specials,  next_inst_index, all_instances, type_heaps, error)
	
	check_instance_specials mod_index fun_type fun_index SP_None next_inst_index all_instances type_heaps error
		= (SP_None, next_inst_index, all_instances, type_heaps, error)

checkAndCollectTypesOfContexts type_contexts error
	= mapSt check_and_collect_context_types type_contexts error
where	
	check_and_collect_context_types {tc_class={glob_object={ds_ident}},tc_types} error
		| hasTypeVariables tc_types
			= (tc_types, checkError ds_ident.id_name "illegal specialization" error)
			= (tc_types, error)



consOptional (Yes thing) things
	= [ thing : things]
consOptional No things
	= things



initializeContextVariables :: ![TypeContext] !*VarHeap ->  (![TypeContext], !*VarHeap)
initializeContextVariables contexts var_heap
	= mapSt add_variable_to_context contexts var_heap
where
	add_variable_to_context context var_heap
		# (new_info_ptr, var_heap) = newPtr VI_Empty var_heap
		= ({ context & tc_var = new_info_ptr}, var_heap)

checkFunction :: !Index !Index !Level !*{#FunDef} !*ExpressionInfo !*Heaps !*CheckState -> (!*{#FunDef},!*ExpressionInfo, !*Heaps, !*CheckState);
checkFunction mod_index fun_index def_level fun_defs
			e_info=:{ef_type_defs,ef_modules,ef_class_defs,ef_is_macro_fun} heaps=:{hp_var_heap,hp_expression_heap,hp_type_heaps} cs=:{cs_error}
	# (fun_def,fun_defs) = fun_defs![fun_index]
	# {fun_symb,fun_pos,fun_body,fun_type,fun_kind} = fun_def
	  cs = { cs & cs_error = push_error_admin_beautifully fun_symb fun_pos fun_kind cs_error }
	  (fun_type, ef_type_defs, ef_class_defs, ef_modules, hp_var_heap, hp_type_heaps, cs)
			= check_function_type fun_type mod_index ef_type_defs ef_class_defs ef_modules hp_var_heap hp_type_heaps cs
	  e_info  = { e_info & ef_type_defs = ef_type_defs, ef_class_defs = ef_class_defs, ef_modules = ef_modules }
	  e_state = {   es_var_heap = hp_var_heap, es_expr_heap = hp_expression_heap, es_type_heaps = hp_type_heaps,
	  				es_dynamics = [], es_calls = [], es_fun_defs = fun_defs }
	  e_input = { ei_expr_level = inc def_level, ei_fun_index = fun_index, ei_fun_level = inc def_level, ei_mod_index = mod_index }
	  (fun_body, free_vars, e_state, e_info, cs) = checkFunctionBodies fun_body e_input e_state e_info cs

	# {es_fun_defs,es_calls,es_var_heap,es_expr_heap,es_type_heaps,es_dynamics} = e_state
	  (ef_type_defs, ef_modules, es_type_heaps, es_expr_heap, cs) = 
	  	checkDynamicTypes mod_index es_dynamics fun_type e_info.ef_type_defs e_info.ef_modules es_type_heaps es_expr_heap cs
	  cs = { cs & cs_error = popErrorAdmin cs.cs_error }
	  fun_info = { fun_def.fun_info & fi_calls = es_calls, fi_def_level = def_level, fi_free_vars = free_vars, fi_dynamics = es_dynamics,
	  					fi_is_macro_fun = ef_is_macro_fun }
	  fun_defs = { es_fun_defs & [fun_index] = { fun_def & fun_body = fun_body, fun_index = fun_index, fun_info = fun_info, fun_type = fun_type}}
	  (fun_defs, cs_symbol_table) = remove_calls_from_symbol_table fun_index def_level es_calls fun_defs cs.cs_symbol_table
	= (fun_defs,
			{ e_info & ef_type_defs = ef_type_defs, ef_modules = ef_modules },
			{ heaps & hp_var_heap = es_var_heap, hp_expression_heap = es_expr_heap, hp_type_heaps = es_type_heaps }, 
			{ cs & cs_symbol_table = cs_symbol_table })

where
	check_function_type (Yes ft) module_index type_defs class_defs modules var_heap type_heaps cs
		# (ft, _, type_defs, class_defs, modules, type_heaps, cs) = checkSymbolType module_index ft SP_None type_defs class_defs modules type_heaps cs
		  (st_context, var_heap) = initializeContextVariables ft.st_context var_heap
		= (Yes { ft & st_context = st_context } , type_defs,  class_defs, modules, var_heap, type_heaps, cs)

	check_function_type No module_index type_defs class_defs modules var_heap type_heaps cs
		= (No, type_defs,  class_defs, modules, var_heap, type_heaps, cs)

	remove_calls_from_symbol_table fun_index fun_level [{fc_index, fc_level} : fun_calls] fun_defs symbol_table
		| fc_level <= fun_level
			# ({fun_symb=fun_symb=:{id_info}}, fun_defs) = fun_defs![fc_index]
			# (entry, symbol_table) = readPtr id_info symbol_table
			# (c,cs) = get_calls entry.ste_kind 
			| fun_index == c
				= remove_calls_from_symbol_table fun_index fun_level fun_calls fun_defs (symbol_table <:= (id_info,{ entry & ste_kind = STE_FunctionOrMacro cs}))
				= abort " Error in remove_calls_from_symbol_table"
			= remove_calls_from_symbol_table fun_index fun_level fun_calls fun_defs symbol_table
	remove_calls_from_symbol_table fun_index fun_level [] fun_defs symbol_table
		= (fun_defs, symbol_table)

	get_calls (STE_FunctionOrMacro [x:xs]) = (x,xs)
	get_calls ste_kind = abort "get_calls (check.icl)" // <<- ste_kind

	push_error_admin_beautifully {id_name} fun_pos (FK_ImpFunction fun_name_is_location_dependent) cs_error
		| fun_name_is_location_dependent && size id_name>0
			# beautiful_name = if (id_name.[0]==backslash) "lambda" "comprehension"
			= pushErrorAdmin (newPosition { id_name=beautiful_name, id_info=nilPtr } fun_pos) cs_error
	push_error_admin_beautifully {id_name} fun_pos (FK_DefFunction fun_name_is_location_dependent) cs_error
		| fun_name_is_location_dependent && size id_name>0
			# beautiful_name = if (id_name.[0]==backslash) "lambda" "comprehension"
			= pushErrorAdmin (newPosition { id_name=beautiful_name, id_info=nilPtr } fun_pos) cs_error
	push_error_admin_beautifully fun_symb fun_pos _ cs_error
		= pushErrorAdmin (newPosition fun_symb fun_pos) cs_error

checkFunctions :: !Index !Level !Index !Index !*{#FunDef} !*ExpressionInfo !*Heaps !*CheckState -> (!*{#FunDef}, !*ExpressionInfo, !*Heaps, !*CheckState)
checkFunctions mod_index level from_index to_index fun_defs e_info heaps cs
	| from_index == to_index
		= (fun_defs, e_info, heaps, cs)
		# (fun_defs, e_info, heaps, cs) = checkFunction mod_index from_index level fun_defs e_info heaps cs
		= checkFunctions mod_index level (inc from_index) to_index fun_defs e_info heaps cs

checkMacros ::  !Index !IndexRange !*{#FunDef} !*ExpressionInfo !*Heaps !*CheckState
	-> (!*{#FunDef}, !*ExpressionInfo, !*Heaps, !*CheckState);
checkMacros mod_index range fun_defs e_info=:{ef_is_macro_fun=ef_is_macro_fun_old} heaps cs
	# (fun_defs, e_info, heaps=:{hp_var_heap, hp_expression_heap}, cs=:{cs_symbol_table, cs_predef_symbols, cs_error})
			= checkFunctions mod_index cGlobalScope range.ir_from range.ir_to fun_defs { e_info & ef_is_macro_fun=True } heaps cs
	  (e_info=:{ef_modules}) = { e_info & ef_is_macro_fun=ef_is_macro_fun_old }
	  (pds_alias_dummy, cs_predef_symbols) = cs_predef_symbols![PD_DummyForStrictAliasFun]
	  (fun_defs, ef_modules, hp_var_heap, hp_expression_heap, cs_symbol_table, cs_error)
	  		= partitionateMacros range mod_index pds_alias_dummy fun_defs ef_modules hp_var_heap hp_expression_heap cs_symbol_table cs_error
	= (fun_defs, { e_info & ef_modules = ef_modules }, {heaps &  hp_var_heap = hp_var_heap, hp_expression_heap = hp_expression_heap},
			{ cs & cs_symbol_table = cs_symbol_table, cs_predef_symbols = cs_predef_symbols, cs_error = cs_error })

checkInstanceBodies :: !IndexRange !*{#FunDef} !*ExpressionInfo !*Heaps !*CheckState -> (!*{#FunDef},!*ExpressionInfo,!*Heaps, !*CheckState);
checkInstanceBodies {ir_from, ir_to} fun_defs e_info heaps cs=:{cs_x}
	= checkFunctions cs_x.x_main_dcl_module_n cGlobalScope ir_from ir_to fun_defs e_info heaps cs

instance < FunDef 
where
	(<) fd1 fd2 = fd1.fun_symb.id_name < fd2.fun_symb.id_name

createCommonDefinitions {def_types,def_constructors,def_selectors,def_macros,def_classes,def_members,def_instances}
	=	{	com_type_defs		= { type \\ type <- def_types }
		,	com_cons_defs		= { cons \\ cons <- def_constructors }
		,	com_selector_defs	= { sel \\ sel <- def_selectors }
		,	com_class_defs		= { class_def \\ class_def <- def_classes }
		,	com_member_defs		= { member \\ member <- def_members }
		,	com_instance_defs	= { next_instance \\ next_instance <- def_instances }
		}

array_plus_list a [] = a
array_plus_list a l = arrayPlusList a l

checkCommonDefinitions :: !Bool !Index !*CommonDefs !*{# DclModule} !*TypeHeaps !*VarHeap !*CheckState
	-> (!*CommonDefs, !*{# DclModule}, !*TypeHeaps,  !*VarHeap, !*CheckState)
checkCommonDefinitions is_dcl module_index common modules type_heaps var_heap cs
	#! is_main_dcl_mod = is_dcl && module_index == cs.cs_x.x_main_dcl_module_n
	# (com_type_defs, com_cons_defs, com_selector_defs, modules, var_heap, type_heaps, cs)
			= checkTypeDefs is_main_dcl_mod common.com_type_defs module_index
							common.com_cons_defs common.com_selector_defs modules var_heap type_heaps cs
	  (com_class_defs, com_member_defs, com_type_defs, modules, type_heaps, cs)
	  		= checkTypeClasses 0 module_index common.com_class_defs common.com_member_defs com_type_defs modules type_heaps cs
	  (com_member_defs, com_type_defs, com_class_defs, modules, type_heaps, var_heap, cs)
	  		= checkMemberTypes module_index com_member_defs com_type_defs com_class_defs modules type_heaps var_heap cs
	  (com_instance_defs, com_type_defs, com_class_defs, com_member_defs, modules, type_heaps, cs)
	  		= checkInstanceDefs module_index common.com_instance_defs com_type_defs com_class_defs com_member_defs modules type_heaps cs

	  (size_com_type_defs,com_type_defs) = usize com_type_defs
	  (size_com_selector_defs,com_selector_defs) = usize com_selector_defs
	  (size_com_cons_defs,com_cons_defs) = usize com_cons_defs

	  (com_class_defs, modules, new_type_defs, new_selector_defs, new_cons_defs, th_vars, var_heap, cs)
	  	= createClassDictionaries module_index com_class_defs modules size_com_type_defs size_com_selector_defs size_com_cons_defs
	  		type_heaps.th_vars var_heap cs

	  com_type_defs = array_plus_list com_type_defs new_type_defs
	  com_selector_defs = array_plus_list com_selector_defs new_selector_defs
	  com_cons_defs = array_plus_list com_cons_defs new_cons_defs

	= ({common & com_type_defs = com_type_defs, com_cons_defs = com_cons_defs, com_selector_defs = com_selector_defs, com_class_defs = com_class_defs,
			com_member_defs = com_member_defs,  com_instance_defs = com_instance_defs }, modules, { type_heaps & th_vars = th_vars }, var_heap, cs)

collectCommonfinitions :: !(CollectedDefinitions ClassInstance a) -> (!*{# Int}, ![Declaration])
collectCommonfinitions {def_types,def_constructors,def_selectors,def_macros,def_classes,def_members,def_instances} 
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
	= (sizes, defs)
where
	type_def_to_dcl {td_name, td_pos} (dcl_index, decls)
		= (inc dcl_index, [{ dcl_ident = td_name, dcl_pos = td_pos, dcl_kind = STE_Type, dcl_index = dcl_index } : decls]) 
	cons_def_to_dcl {cons_symb, cons_pos} (dcl_index, decls)
		= (inc dcl_index, [{ dcl_ident = cons_symb, dcl_pos = cons_pos, dcl_kind = STE_Constructor, dcl_index = dcl_index } : decls]) 
	selector_def_to_dcl {sd_symb, sd_field, sd_pos} (dcl_index, decls)
		= (inc dcl_index, [{ dcl_ident = sd_field, dcl_pos = sd_pos, dcl_kind = STE_Field sd_symb, dcl_index = dcl_index } : decls]) 
	class_def_to_dcl {class_name, class_pos} (dcl_index, decls)
		= (inc dcl_index, [{ dcl_ident = class_name, dcl_pos = class_pos, dcl_kind = STE_Class, dcl_index = dcl_index } : decls]) 
	member_def_to_dcl {me_symb, me_pos} (dcl_index, decls)
		= (inc dcl_index, [{ dcl_ident = me_symb, dcl_pos = me_pos, dcl_kind = STE_Member, dcl_index = dcl_index } : decls]) 
	instance_def_to_dcl {ins_class, ins_ident, ins_pos} (dcl_index, decls)
		= (inc dcl_index, [{ dcl_ident = ins_ident, dcl_pos = ins_pos, dcl_kind = STE_Instance ins_class.glob_object.ds_ident, dcl_index = dcl_index } : decls]) 

collectMacros {ir_from,ir_to} macro_defs sizes_defs
	= collectGlobalFunctions cMacroDefs ir_from ir_to macro_defs sizes_defs

collectFunctionTypes fun_types (sizes, defs)
	# (size, defs) = foldSt fun_type_to_dcl fun_types (0, defs)
	= ({ sizes & [cFunctionDefs] = size }, defs)
where
	fun_type_to_dcl {ft_symb, ft_pos} (dcl_index, decls) 
		= (inc dcl_index, [{ dcl_ident = ft_symb, dcl_pos = ft_pos, dcl_kind = STE_DclFunction, dcl_index = dcl_index } : decls]) 

collectGlobalFunctions def_index from_index to_index fun_defs (sizes, defs)
	# (defs, fun_defs) = iFoldSt fun_def_to_dcl from_index to_index (defs, fun_defs)  
	= (fun_defs, ({ sizes & [def_index] = to_index - from_index }, defs))
where
	fun_def_to_dcl dcl_index (defs, fun_defs)
		# ({fun_symb, fun_pos}, fun_defs) = fun_defs![dcl_index]
		= ([{ dcl_ident = fun_symb, dcl_pos = fun_pos, dcl_kind = STE_FunctionOrMacro [], dcl_index = dcl_index } : defs], fun_defs)

gimme_a_lazy_array_type :: !u:{.a} -> v:{.a}, [u<=v]
gimme_a_lazy_array_type a = a

gimme_a_strict_array_type :: !u:{!.a} -> v:{!.a}, [u<=v]
gimme_a_strict_array_type a = a

renumber_icl_definitions_as_dcl_definitions :: !ModuleKind ![Declaration] !*{#DclModule} !*CommonDefs !{#Int} !*CheckState
											-> (![Declaration], !.{#DclModule}, !.CommonDefs, !.CheckState)
renumber_icl_definitions_as_dcl_definitions MK_Main icl_decl_symbols modules cdefs icl_sizes cs
	= (icl_decl_symbols,modules,cdefs,cs)
renumber_icl_definitions_as_dcl_definitions _ icl_decl_symbols modules cdefs icl_sizes cs
	#! main_dcl_module_n=cs.cs_x.x_main_dcl_module_n
	# (dcl_mod,modules) = modules![main_dcl_module_n]
	# (Yes conversion_table) = dcl_mod.dcl_conversions
	# icl_to_dcl_index_table = gimme_a_lazy_array_type {create_icl_to_dcl_index_table_for_kind table_size dcl_to_icl_table \\ table_size <-: icl_sizes & dcl_to_icl_table <-: conversion_table }
		with
			create_icl_to_dcl_index_table_for_kind :: !Int !{#Int} -> {#Int}
			create_icl_to_dcl_index_table_for_kind table_size dcl_to_icl_table
				# icl_to_dcl_index_table_for_kind = {createArray table_size NoIndex & [dcl_to_icl_table.[dcl_index]]=dcl_index \\ dcl_index<- [0..size dcl_to_icl_table-1]}
				#! max_index=size icl_to_dcl_index_table_for_kind-1
				# icl_to_dcl_index_table_for_kind = number_NoIndex_elements max_index max_index icl_to_dcl_index_table_for_kind
					with
						number_NoIndex_elements :: Int Int *{#Int} -> .{#Int};
						number_NoIndex_elements index free_position_index icl_to_dcl_index_table_for_kind
							| index>=0
								| icl_to_dcl_index_table_for_kind.[index]==NoIndex
									= number_NoIndex_elements (index-1) (free_position_index-1) {icl_to_dcl_index_table_for_kind & [index]=free_position_index}
									= number_NoIndex_elements (index-1) free_position_index icl_to_dcl_index_table_for_kind
								= icl_to_dcl_index_table_for_kind
				= icl_to_dcl_index_table_for_kind
	# modules = {modules & [main_dcl_module_n] = { dcl_mod & dcl_conversions = Yes conversion_table}}
	# (icl_decl_symbols,cdefs) = renumber_icl_decl_symbols icl_decl_symbols cdefs
		with
			renumber_icl_decl_symbols [] cdefs
				= ([],cdefs)
			renumber_icl_decl_symbols [icl_decl_symbol : icl_decl_symbols] cdefs
				# (icl_decl_symbol,cdefs) = renumber_icl_decl_symbol icl_decl_symbol cdefs
				# (icl_decl_symbols,cdefs) = renumber_icl_decl_symbols icl_decl_symbols cdefs
				= ([icl_decl_symbol : icl_decl_symbols],cdefs)
				where
					renumber_icl_decl_symbol icl_decl_symbol=:{dcl_kind = STE_Type, dcl_index} cdefs
						# (type_def,cdefs) = cdefs!com_type_defs.[dcl_index]
						# type_def = renumber_type_def type_def
						# cdefs={cdefs & com_type_defs.[dcl_index]=type_def}
						= ({icl_decl_symbol & dcl_index=icl_to_dcl_index_table.[cTypeDefs,dcl_index]},cdefs)
						where
							renumber_type_def td=:{td_rhs = AlgType conses}
								# conses = [{cons & ds_index=icl_to_dcl_index_table.[cConstructorDefs,cons.ds_index]} \\ cons <- conses]
								= { td & td_rhs = AlgType conses}
							renumber_type_def td=:{td_rhs = RecordType rt=:{rt_constructor,rt_fields}}
								# rt_constructor = {rt_constructor & ds_index=icl_to_dcl_index_table.[cConstructorDefs,rt_constructor.ds_index]}
								# rt_fields = {{field & fs_index=icl_to_dcl_index_table.[cSelectorDefs,field.fs_index]} \\ field <-: rt_fields}
								= {td & td_rhs=RecordType {rt_constructor=rt_constructor,rt_fields=rt_fields}}
							renumber_type_def td
								= td
					renumber_icl_decl_symbol icl_decl_symbol=:{dcl_kind = STE_Constructor, dcl_index} cdefs
						= ({icl_decl_symbol & dcl_index=icl_to_dcl_index_table.[cConstructorDefs,dcl_index]},cdefs)
					renumber_icl_decl_symbol icl_decl_symbol=:{dcl_kind = STE_Field _, dcl_index} cdefs
						= ({icl_decl_symbol & dcl_index=icl_to_dcl_index_table.[cSelectorDefs,dcl_index]},cdefs)
					renumber_icl_decl_symbol icl_decl_symbol=:{dcl_kind = STE_Member, dcl_index} cdefs
						= ({icl_decl_symbol & dcl_index=icl_to_dcl_index_table.[cMemberDefs,dcl_index]},cdefs)
					renumber_icl_decl_symbol icl_decl_symbol=:{dcl_kind = STE_Class, dcl_index} cdefs
						# (class_def,cdefs) = cdefs!com_class_defs.[dcl_index]
						# class_members = {{class_member & ds_index=icl_to_dcl_index_table.[cMemberDefs,class_member.ds_index]} \\ class_member <-: class_def.class_members}
						# class_def = {class_def & class_members=class_members}
						# cdefs = {cdefs & com_class_defs.[dcl_index] =class_def}
						= ({icl_decl_symbol & dcl_index=icl_to_dcl_index_table.[cClassDefs,dcl_index]},cdefs)
					renumber_icl_decl_symbol icl_decl_symbol cdefs
						= (icl_decl_symbol,cdefs)
	# cdefs=reorder_common_definitions cdefs
		with
			reorder_common_definitions {com_type_defs,com_cons_defs,com_selector_defs,com_class_defs,com_member_defs,com_instance_defs}
				# com_type_defs=reorder_array com_type_defs icl_to_dcl_index_table.[cTypeDefs]
				# com_cons_defs=reorder_array com_cons_defs icl_to_dcl_index_table.[cConstructorDefs]
				# com_selector_defs=reorder_array com_selector_defs icl_to_dcl_index_table.[cSelectorDefs]
				# com_class_defs=reorder_array com_class_defs icl_to_dcl_index_table.[cClassDefs]
				# com_member_defs=reorder_array com_member_defs icl_to_dcl_index_table.[cMemberDefs]
				= {com_type_defs=com_type_defs,com_cons_defs=com_cons_defs,com_selector_defs=com_selector_defs,com_class_defs=com_class_defs,com_member_defs=com_member_defs,com_instance_defs=com_instance_defs}
					where
						reorder_array array index_array
							# new_array={e\\e<-:array}
							= {new_array & [index_array.[i]]=e \\ e<-:array & i<-[0..]}				
	# conversion_table = {if (kind_index<=cMemberDefs) {i\\i<-[0..size table-1]} table \\ table<-:conversion_table & kind_index<-[0..]}
	# modules = {modules & [main_dcl_module_n].dcl_conversions=Yes conversion_table}
	= (icl_decl_symbols,modules,cdefs,cs)



combineDclAndIclModule :: ModuleKind *{#.DclModule} [Declaration] (CollectedDefinitions a b) *{#.Int} *CheckState -> (!*{#DclModule},![Declaration],!CollectedDefinitions a b,!*{#Int},!.CheckState);
combineDclAndIclModule MK_Main modules icl_decl_symbols icl_definitions icl_sizes cs
	= (modules, icl_decl_symbols, icl_definitions, icl_sizes, cs)
combineDclAndIclModule _ modules icl_decl_symbols icl_definitions icl_sizes cs
	#! main_dcl_module_n=cs.cs_x.x_main_dcl_module_n
	# (dcl_mod=:{dcl_declared={dcls_local},dcl_macros, dcl_sizes, dcl_common}, modules) =  modules![main_dcl_module_n]

	  cs = addGlobalDefinitionsToSymbolTable icl_decl_symbols cs

	  (moved_dcl_defs, conversion_table, icl_sizes, icl_decl_symbols, cs)
			= foldSt (add_to_conversion_table dcl_macros.ir_from dcl_common) dcls_local ([], { createArray size NoIndex \\ size <-: dcl_sizes }, icl_sizes, icl_decl_symbols, cs)
            
	  (new_type_defs, new_class_defs, new_cons_defs, new_selector_defs, new_member_defs, cs)
			= foldSt (add_dcl_definition dcl_common) moved_dcl_defs ([], [], [], [], [], cs)
	  cs_symbol_table
	  		= removeDeclarationsFromSymbolTable icl_decl_symbols cGlobalScope cs.cs_symbol_table

	=	( { modules & [main_dcl_module_n] = { dcl_mod & dcl_conversions = Yes conversion_table }}
		, icl_decl_symbols
		, { icl_definitions
				& def_types			= my_append icl_definitions.def_types new_type_defs
				, def_constructors	= my_append icl_definitions.def_constructors new_cons_defs
				, def_selectors		= my_append icl_definitions.def_selectors new_selector_defs
				, def_classes		= my_append icl_definitions.def_classes new_class_defs
				, def_members		= my_append icl_definitions.def_members new_member_defs
		  }
		,  icl_sizes
		, { cs & cs_symbol_table = cs_symbol_table }
		)
where
	add_to_conversion_table first_macro_index dcl_common decl=:{dcl_ident=dcl_ident=:{id_info},dcl_kind,dcl_index,dcl_pos}
			(moved_dcl_defs, conversion_table, icl_sizes, icl_defs, cs)
		# (entry=:{ste_kind,ste_index,ste_def_level}, cs_symbol_table) = readPtr id_info cs.cs_symbol_table
		| ste_kind == STE_Empty
			# def_index = toInt dcl_kind
 			| can_be_only_in_dcl def_index && not (def_index==cTypeDefs && is_abstract_type dcl_common.com_type_defs dcl_index)
				# (conversion_table, icl_sizes, icl_defs, cs_symbol_table)
					= add_dcl_declaration id_info entry decl def_index dcl_index (conversion_table, icl_sizes, icl_defs, cs_symbol_table)
				= ([ decl : moved_dcl_defs ], conversion_table, icl_sizes, icl_defs, { cs & cs_symbol_table = cs_symbol_table })
			| def_index == cMacroDefs
				# (conversion_table, icl_defs, cs_symbol_table)
					= add_macro_declaration id_info entry decl def_index (dcl_index - first_macro_index) dcl_index
								(conversion_table, icl_defs, cs_symbol_table)
				= ([ decl : moved_dcl_defs ], conversion_table, icl_sizes, icl_defs, { cs & cs_symbol_table = cs_symbol_table })
				# cs_error = checkError "definition module" "undefined in implementation module" (setErrorAdmin (newPosition dcl_ident dcl_pos) cs.cs_error)
				= (moved_dcl_defs, conversion_table, icl_sizes, icl_defs, { cs & cs_error = cs_error, cs_symbol_table = cs_symbol_table })
		| ste_def_level == cGlobalScope && ste_kind == dcl_kind
			# def_index = toInt dcl_kind
			  dcl_index = if (def_index == cMacroDefs) (dcl_index - first_macro_index) dcl_index
			= (moved_dcl_defs, { conversion_table & [def_index].[dcl_index] = ste_index },  icl_sizes, icl_defs, { cs & cs_symbol_table = cs_symbol_table })
			# cs_error = checkError "definition module" "conflicting definition in implementation module"
					(setErrorAdmin (newPosition dcl_ident dcl_pos) cs.cs_error)
			= (moved_dcl_defs, conversion_table,  icl_sizes, icl_defs, { cs & cs_error = cs_error, cs_symbol_table = cs_symbol_table })

/* To be done : cClassDefs and cMemberDefs */

	can_be_only_in_dcl def_kind
		=	def_kind == cTypeDefs	|| def_kind == cConstructorDefs || def_kind == cSelectorDefs
		||	def_kind == cClassDefs	|| def_kind == cMemberDefs

 	is_abstract_type com_type_defs dcl_index
 		= case com_type_defs.[dcl_index].td_rhs of (AbstractType _) -> True ; _ -> False
 
	add_dcl_declaration info_ptr entry dcl def_index dcl_index (conversion_table, icl_sizes, icl_defs, symbol_table)
		# (icl_index, icl_sizes) = icl_sizes![def_index]
		=	(	{ conversion_table & [def_index].[dcl_index] = icl_index }
			,	{ icl_sizes & [def_index] = inc icl_index }
			,	[ { dcl & dcl_index = icl_index } : icl_defs ]
			,	NewEntry symbol_table info_ptr dcl.dcl_kind icl_index cGlobalScope entry
			)

	add_macro_declaration info_ptr entry dcl def_index dcl_index icl_index (conversion_table, icl_defs, symbol_table)
		=	(	{ conversion_table & [def_index].[dcl_index] = icl_index }
			,	[ { dcl & dcl_index = icl_index } : icl_defs ]
			,	NewEntry symbol_table info_ptr dcl.dcl_kind icl_index cGlobalScope entry
			)
	
	add_dcl_definition {com_type_defs} dcl=:{dcl_kind = STE_Type, dcl_index}
			(new_type_defs, new_class_defs, new_cons_defs, new_selector_defs, new_member_defs, cs)
		# type_def = com_type_defs.[dcl_index]
		  (new_type_defs, cs) = add_type_def type_def new_type_defs cs
		= (new_type_defs, new_class_defs, new_cons_defs, new_selector_defs, new_member_defs, cs)
	where
		add_type_def td=:{td_pos, td_rhs = AlgType conses} new_type_defs cs
			# (conses, cs) = mapSt (redirect_defined_symbol STE_Constructor td_pos) conses cs
			= ([ { td & td_rhs = AlgType conses} : new_type_defs ], cs)
		add_type_def td=:{td_pos, td_rhs = RecordType rt=:{rt_constructor,rt_fields}} new_type_defs cs
			# (rt_constructor, cs) = redirect_defined_symbol STE_Constructor td_pos rt_constructor cs
			  (rt_fields, cs) = redirect_field_symbols td_pos rt_fields cs
			= ([ { td & td_rhs =  RecordType { rt & rt_constructor = rt_constructor, rt_fields = rt_fields }} : new_type_defs ], cs)
		add_type_def td=:{td_name, td_pos, td_rhs = AbstractType _} new_type_defs cs
			# cs_error = checkError "definition module" "abstract type not defined in implementation module"
					(setErrorAdmin (newPosition td_name td_pos) cs.cs_error)
			= (new_type_defs, { cs & cs_error = cs_error })
		add_type_def td new_type_defs cs
			= ([td : new_type_defs], cs) 

		redirect_field_symbols pos fields cs
			# new_fields = { field \\ field <-: fields }
			= iFoldSt (redirect_field_symbol pos fields) 0 (size fields) (new_fields, cs)
		where
			redirect_field_symbol pos fields field_nr (new_fields, cs)
				# field = fields.[field_nr]
				  ({ste_kind,ste_index}, cs_symbol_table) = readPtr field.fs_name.id_info cs.cs_symbol_table
				| is_field ste_kind
					= ({ new_fields & [field_nr] = { field & fs_index = ste_index }}, { cs & cs_symbol_table = cs_symbol_table })
					# cs_error = checkError "definition module" "conflicting definition in implementation module"
									(setErrorAdmin (newPosition field.fs_name pos) cs.cs_error)
					= (new_fields, { cs & cs_error = cs_error, cs_symbol_table = cs_symbol_table })

			is_field (STE_Field _)	= True
			is_field _				= False

	add_dcl_definition {com_cons_defs} dcl=:{dcl_kind = STE_Constructor, dcl_index} 
			(new_type_defs, new_class_defs, new_cons_defs, new_selector_defs, new_member_defs, cs)
		= (new_type_defs, new_class_defs, [ com_cons_defs.[dcl_index] : new_cons_defs ], new_selector_defs, new_member_defs, cs)
	add_dcl_definition {com_selector_defs} dcl=:{dcl_kind = STE_Field _, dcl_index} 
			(new_type_defs, new_class_defs, new_cons_defs, new_selector_defs, new_member_defs, cs)
		= (new_type_defs, new_class_defs, new_cons_defs, [ com_selector_defs.[dcl_index] : new_selector_defs ], new_member_defs, cs)
	add_dcl_definition {com_class_defs} dcl=:{dcl_kind = STE_Class, dcl_index, dcl_pos} 
			(new_type_defs, new_class_defs, new_cons_defs, new_selector_defs, new_member_defs, cs)
		# class_def = com_class_defs.[dcl_index]
		  (new_class_defs, cs) = add_class_def dcl_pos class_def new_class_defs cs
		= (new_type_defs, new_class_defs, new_cons_defs, new_selector_defs, new_member_defs, cs)
	  where
		add_class_def dcl_pos cd=:{class_members} new_class_defs cs
			# (new_class_members, cs) = mapSt (redirect_defined_symbol STE_Member dcl_pos) [ cm \\ cm<-:class_members ] cs
			= ([{cd & class_members={cm \\ cm<-new_class_members}}:new_class_defs], cs)
	add_dcl_definition {com_member_defs} dcl=:{dcl_kind = STE_Member, dcl_index, dcl_pos} 
			(new_type_defs, new_class_defs, new_cons_defs, new_selector_defs, new_member_defs, cs)
		# member_def = com_member_defs.[dcl_index]
		= (new_type_defs, new_class_defs, new_cons_defs, new_selector_defs, [member_def:new_member_defs], cs)
	add_dcl_definition _ _ 
			(new_type_defs, new_class_defs, new_cons_defs, new_selector_defs, new_member_defs, cs)
		= (new_type_defs, new_class_defs, new_cons_defs, new_selector_defs, new_member_defs, cs)

	redirect_defined_symbol req_kind pos ds=:{ds_ident} cs
		# ({ste_kind,ste_index}, cs_symbol_table) = readPtr ds_ident.id_info cs.cs_symbol_table
		| ste_kind == req_kind
			= ({ ds & ds_index = ste_index }, { cs & cs_symbol_table = cs_symbol_table })
			# cs_error = checkError "definition module" "conflicting definition in implementation module"
							(setErrorAdmin (newPosition ds_ident pos) cs.cs_error)
			= ({ ds & ds_index = ste_index }, { cs & cs_error = cs_error, cs_symbol_table = cs_symbol_table })

	my_append front []
		= front
	my_append front back
		= front ++ back

(<=<) infixl 
(<=<) state fun :== fun state 

checkDclModules imports_of_icl_mod dcl_modules icl_functions heaps cs=:{cs_symbol_table}
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
	  dependencies
	  		= { dependencies & [index_of_icl_module] = dependencies_of_icl_mod }
	  module_dag
	  		= { dag_nr_of_nodes = nr_of_dcl_modules+1, dag_get_children = select dependencies }
	  components
	  		= partitionateDAG module_dag [cs.cs_x.x_main_dcl_module_n,index_of_icl_module]
//	| False--->("biggest component:", maxList (map length components))
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
	  		= { cs & cs_symbol_table = cs_symbol_table } // --->("expl_imp_symbols_in_components", expl_imp_symbols_in_components)
	  nr_of_icl_component
	  		= component_numbers.[index_of_icl_module]
	  (_, expl_imp_infos, dcl_modules, icl_functions, heaps, cs)
	  		= unsafeFold2St (checkDclComponent components_array super_components) (reverse expl_imp_indices) (reverse components)
					(nr_of_components-1, expl_imp_infos, dcl_modules, icl_functions, heaps, cs)
//	# cs = cs--->"------------------------------------"
	= (nr_of_icl_component, hd expl_imp_indices!!nr_of_icl_component, expl_imp_infos,
		dcl_modules, icl_functions, heaps, cs)
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

	set_to_false :: (Import x) !(!*LargeBitvect, !u:SymbolTable) -> !(!.LargeBitvect, !u:SymbolTable)
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
		
	get_expl_imp_symbols_of_module imports_of_icl_mod mod_index
					(expl_imp_symbols_accu, nr_of_expl_imp_symbols, expl_imp_indices_accu, dcl_modules, cs_symbol_table)
		#! siz
				= size dcl_modules
		# (mod_imports, dcl_modules, cs_symbol_table)
				= get_mod_imports (mod_index==siz) imports_of_icl_mod dcl_modules cs_symbol_table
		  (expl_imp_symbols_accu, nr_of_expl_imp_symbols, expl_imp_indices, cs_symbol_table)
				= foldSt get_expl_imp_symbols mod_imports
						(expl_imp_symbols_accu, nr_of_expl_imp_symbols, [], cs_symbol_table)
		= (expl_imp_symbols_accu, nr_of_expl_imp_symbols, [expl_imp_indices:expl_imp_indices_accu],
			dcl_modules, cs_symbol_table)
	  where
		get_mod_imports is_icl_mod=:False _ dcl_modules cs_symbol_table
			# ({dcl_name}, dcl_modules)
					=  dcl_modules![mod_index]
			  ({ste_kind}, cs_symbol_table)
					= readPtr dcl_name.id_info cs_symbol_table
			= case ste_kind of
				STE_Module {mod_imports}
					-> (mod_imports, dcl_modules, cs_symbol_table)
				STE_ClosedModule
					-> ([], dcl_modules, cs_symbol_table)
		get_mod_imports _ imports_of_icl_mod dcl_modules cs_symbol_table
		 	= (imports_of_icl_mod, dcl_modules, cs_symbol_table)
			
	get_expl_imp_symbols {import_module, import_symbols, import_file_position}
			(expl_imp_symbols_accu, nr_of_expl_imp_symbols, expl_imp_indices_accu, cs_symbol_table)
		# (expl_imp_symbols_accu, nr_of_expl_imp_symbols, expl_imp_indices, cs_symbol_table)
				= foldSt get_expl_imp_symbol import_symbols
						(expl_imp_symbols_accu, nr_of_expl_imp_symbols, [], cs_symbol_table)
		  ({ste_index}, cs_symbol_table)
		  		= readPtr import_module.id_info cs_symbol_table
		= (expl_imp_symbols_accu, nr_of_expl_imp_symbols, 
			[(ste_index, import_file_position, expl_imp_indices):expl_imp_indices_accu], cs_symbol_table)

	get_expl_imp_symbol imp_decl=:(ID_OldSyntax idents) state
		= foldSt (get_symbol imp_decl) idents state
	get_expl_imp_symbol imp_decl state
		= get_symbol imp_decl (get_ident imp_decl) state

	get_symbol imp_decl ident=:{id_info} (expl_imp_symbols_accu, nr_of_expl_imp_symbols, expl_imp_indices_accu, cs_symbol_table)
		# (ste, cs_symbol_table)
				= readPtr id_info cs_symbol_table
		= case ste.ste_kind of
			STE_ExplImpSymbol expl_imp_symbols_nr
				# ini
						= { ini_symbol_nr = expl_imp_symbols_nr, ini_imp_decl = imp_decl }
				-> (expl_imp_symbols_accu, nr_of_expl_imp_symbols, 
					[ini:expl_imp_indices_accu], cs_symbol_table)
			STE_Empty
				# cs_symbol_table
						= writePtr id_info { ste & ste_kind = STE_ExplImpSymbol nr_of_expl_imp_symbols, ste_previous = ste }
								cs_symbol_table
				  ini
						= { ini_symbol_nr = nr_of_expl_imp_symbols, ini_imp_decl = imp_decl }
				-> ([ident:expl_imp_symbols_accu], nr_of_expl_imp_symbols+1,
					[ini:expl_imp_indices_accu], cs_symbol_table)

checkDclComponent :: !{![Int]} !{![Int]} ![[(Index, Position, [ImportNrAndIdents])]] ![Int] 
				!(!Int, !*ExplImpInfos, !*{# DclModule}, !*{# FunDef}, !*Heaps,!*CheckState)
			-> (!Int, !.ExplImpInfos, !.{# DclModule}, !.{# FunDef}, !.Heaps,!.CheckState)
checkDclComponent components_array super_components expl_imp_indices mod_indices
		(component_nr, expl_imp_infos, dcl_modules, icl_functions, heaps, cs=:{cs_x})
	| not cs.cs_error.ea_ok || hd mod_indices==size dcl_modules // the icl module!
		= (component_nr-1, expl_imp_infos, dcl_modules, icl_functions, heaps, cs)
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
					= foldSt (just_update_expl_imp_info components_array super_components) mod_indices
							(expl_imp_infos, dcl_modules, cs.cs_symbol_table)
 			-> (component_nr-1, expl_imp_infos, dcl_modules, icl_functions, heaps,
 				{ cs & cs_symbol_table = cs_symbol_table })
		STE_Module _
			# is_on_cycle
					= case mod_indices of
						[_]	-> False
						_	-> True
			  cs_error
			  		= fold2St check_whether_module_imports_itself expl_imp_indices mod_indices cs.cs_error
			  cs_error
			  		= case switch_import_syntax is_on_cycle False of
			  			True
			  				# ident_pos
			  						= { ip_ident = dcl_name_of_first_mod_in_component, ip_line = 1,
			  								ip_file = dcl_name_of_first_mod_in_component.id_name }
			  				  cs_error
			  						= pushErrorAdmin ident_pos cs_error
			  				  cs_error
			  				  		=  checkError "" 
				  							"cyclic module dependencies not allowed in conjunction with Clean 1.3 import syntax"
										cs_error
							-> popErrorAdmin cs_error
						_
							-> cs_error
			  cs
			  		= { cs & cs_error = cs_error }
			| not cs.cs_error.ea_ok
				-> (component_nr-1, expl_imp_infos, dcl_modules, icl_functions, heaps, cs)
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
				-> (component_nr-1, expl_imp_infos, dcl_modules, icl_functions, heaps, cs)
			# imports_ikh
			  		= fold2St (ikhInsert` False) mod_indices imports ikhEmpty
			  		// maps the module indices of all modules in the actual component to all explicit
			  		// imports of that module
		
			  (dcl_modules, cs)
			  		= switch_port_to_new_syntax
			  			(possibly_write_expl_imports_of_main_dcl_mod_to_file imports_ikh dcl_modules cs)
			  			(dcl_modules, cs)
		
			  (afterwards_info, (expl_imp_infos, dcl_modules, icl_functions, heaps, cs))
					= mapSt (checkDclModuleWithinComponent dcl_imported_module_numbers component_nr is_on_cycle modules_in_component_set
								super_components imports_ikh) mod_indices
							(expl_imp_infos, dcl_modules, icl_functions, heaps, cs)
		
			| not cs.cs_error.ea_ok
				-> (component_nr-1, expl_imp_infos, dcl_modules, icl_functions, heaps, cs)

			# (dcl_modules, icl_functions, heaps, cs)
					= case is_on_cycle of
						False
							-> (dcl_modules, icl_functions, heaps, cs)
						True
							# (dcl_modules, icl_functions, hp_expression_heap, cs)
									= fold2St check_expl_imp_completeness_of_dcl_mod_within_non_trivial_component
											mod_indices imports
											(dcl_modules, icl_functions, heaps.hp_expression_heap, cs)
							-> (dcl_modules, icl_functions, { heaps & hp_expression_heap = hp_expression_heap }, cs)	
			  (dcl_modules, heaps, cs)
			   		= fold2St doSomeThingsThatHaveToBeDoneAfterTheWholeComponentHasBeenChecked
					   		mod_indices afterwards_info
					   		(dcl_modules, heaps, cs)
			-> (component_nr-1, expl_imp_infos, dcl_modules, icl_functions, heaps, cs)
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
		  		= foldSt collect_expl_imp_info_per_module mod_indices
		  				(expl_imp_infos, dcl_modules, cs_symbol_table)
		  cs_symbol_table
		  		= foldSt restoreHeap changed_symbols cs_symbol_table
		= (expl_imp_infos, dcl_modules, { cs & cs_symbol_table = cs_symbol_table })

	collect_expl_imp_info_per_module mod_index (expl_imp_infos, dcl_modules, cs_symbol_table)
		# (dcls_local_for_import, dcl_modules)
				= dcl_modules![mod_index].dcl_declared.dcls_local_for_import
		  (dcl_modules, expl_imp_infos, cs_symbol_table)
				= foldlArraySt ((switch_import_syntax
									update_expl_imp_for_marked_symbol
									update_expl_imp_for_marked_local_symbol) mod_index)
						dcls_local_for_import
						(dcl_modules, expl_imp_infos, cs_symbol_table)
		= (expl_imp_infos, dcl_modules, cs_symbol_table)
	
	just_update_expl_imp_info components_array super_components mod_index
			(expl_imp_infos, dcl_modules, cs_symbol_table)
		# ({dcls_local_for_import, dcls_import}, dcl_modules)
				= dcl_modules![mod_index].dcl_declared
		  (dcl_modules, expl_imp_infos, cs_symbol_table)
				= updateExplImpInfo super_components.[mod_index] mod_index dcls_import dcls_local_for_import
							dcl_modules expl_imp_infos cs_symbol_table
		= (expl_imp_infos, dcl_modules, cs_symbol_table)

	check_expl_imp_completeness_of_dcl_mod_within_non_trivial_component mod_index {si_explicit}
					(dcl_modules, icl_functions, hp_expression_heap, cs)
			# ({dcl_declared}, dcl_modules)
					= dcl_modules![mod_index]
			  ({dcls_local_for_import, dcls_import})
			  		= dcl_declared
			  cs
			  		= addDeclarationsOfDclModToSymbolTable mod_index dcls_local_for_import dcls_import cs
			  (dcl_modules, icl_functions, hp_expression_heap, cs=:{cs_symbol_table})
			  		= checkExplicitImportCompleteness si_explicit
			  				dcl_modules icl_functions hp_expression_heap cs
  			  cs_symbol_table
  			  		= removeImportsAndLocalsOfModuleFromSymbolTable dcl_declared cs.cs_symbol_table
			= (dcl_modules, icl_functions, hp_expression_heap, { cs & cs_symbol_table = cs_symbol_table })
	

compute_used_module_nrs (mod_index, _, _) (mod_nr_accu, dcl_modules)
	| inNumberSet mod_index mod_nr_accu
		= (mod_nr_accu, dcl_modules)
	# ({dcl_imported_module_numbers}, dcl_modules)
			= dcl_modules![mod_index]
	= (addNr mod_index (numberSetUnion dcl_imported_module_numbers mod_nr_accu),
		 dcl_modules)
	

checkDclModuleWithinComponent dcl_imported_module_numbers component_nr is_on_cycle modules_in_component_set
		super_components imports_ikh mod_index
		(expl_imp_infos, dcl_modules, icl_functions, heaps, cs=:{cs_symbol_table})
	# ({dcl_name}, dcl_modules)
			= dcl_modules![mod_index]
	  (mod_entry, cs_symbol_table)
	  		= readPtr dcl_name.id_info cs_symbol_table
	  cs
	  		= { cs & cs_symbol_table = cs_symbol_table }
	  ({ ste_kind = STE_Module mod, ste_index })
			= mod_entry
	  cs_symbol_table 
			= writePtr dcl_name.id_info { mod_entry & ste_kind = STE_ClosedModule } cs.cs_symbol_table
	= checkDclModule dcl_imported_module_numbers super_components.[mod_index] imports_ikh component_nr
  	  				is_on_cycle modules_in_component_set
  	  				mod ste_index expl_imp_infos dcl_modules icl_functions heaps
  	  				{ cs & cs_symbol_table = cs_symbol_table }


checkModule :: !ScannedModule !IndexRange ![FunDef] !Int  !Int !(Optional ScannedModule) ![ScannedModule] !{#DclModule} !{#FunDef} !*PredefinedSymbols !*SymbolTable !*File !*Heaps
	-> (!Bool, *IclModule, *{# DclModule}, *{! Group}, !(Optional {# Index}), !.{#FunDef}, !Int,!*Heaps, !*PredefinedSymbols, !*SymbolTable, *File)
checkModule m icl_global_function_range fun_defs n_functions_and_macros_in_dcl_modules dcl_module_n_in_cache optional_dcl_mod scanned_modules dcl_modules functions_and_macros predef_symbols symbol_table err_file heaps
//	| False--->("checkModule", m.mod_name)
//		= undef
	# (optional_pre_def_mod,predef_symbols)
		= case size dcl_modules of
			0	# (predef_mod,predef_symbols) = buildPredefinedModule predef_symbols
				-> (Yes predef_mod,predef_symbols)
			_	-> (No,predef_symbols)
	# (mod_name,mod_imported_objects,mod_imports,mod_type,icl_global_function_range,nr_of_functions,first_inst_index,local_defs,icl_functions,init_dcl_modules,main_dcl_module_n,cdefs,sizes,cs)
		= check_module1 m icl_global_function_range fun_defs optional_dcl_mod optional_pre_def_mod scanned_modules dcl_modules functions_and_macros dcl_module_n_in_cache predef_symbols symbol_table err_file
	# icl_instance_range = {ir_from = first_inst_index, ir_to = nr_of_functions}
	= check_module2 mod_name mod_imported_objects mod_imports mod_type icl_global_function_range icl_instance_range nr_of_functions n_functions_and_macros_in_dcl_modules optional_pre_def_mod local_defs icl_functions init_dcl_modules cdefs sizes heaps cs

check_module1 {mod_type,mod_name,mod_imports,mod_imported_objects,mod_defs = cdefs} icl_global_function_range fun_defs optional_dcl_mod optional_pre_def_mod scanned_modules dcl_modules functions_and_macros dcl_module_n_in_cache predef_symbols symbol_table err_file
	# error = {ea_file = err_file, ea_loc = [], ea_ok = True }

	  first_inst_index = length fun_defs + size functions_and_macros
	  (inst_fun_defs, def_instances) = convert_class_instances cdefs.def_instances first_inst_index

	  new_icl_functions = gimme_a_strict_array_type { next_fun \\ next_fun <- fun_defs ++ inst_fun_defs }
	  
	  icl_functions = {if (i<size functions_and_macros) functions_and_macros.[i] new_icl_functions.[i-size functions_and_macros] \\ i<-[0..size functions_and_macros+size new_icl_functions-1]}

	  cdefs = { cdefs & def_instances = def_instances }
	#! nr_of_functions = size icl_functions

	# sizes_and_local_defs = collectCommonfinitions cdefs
	  (icl_functions, sizes_and_local_defs) = collectGlobalFunctions cFunctionDefs icl_global_function_range.ir_from icl_global_function_range.ir_to icl_functions sizes_and_local_defs
	  (icl_functions, (sizes, local_defs)) = collectMacros cdefs.def_macros icl_functions sizes_and_local_defs

	  main_dcl_module_n = if (dcl_module_n_in_cache<>NoIndex) dcl_module_n_in_cache (size dcl_modules)
	  cs = { cs_symbol_table = symbol_table, cs_predef_symbols = predef_symbols, cs_error = error, cs_x= {x_needed_modules=0,x_main_dcl_module_n=main_dcl_module_n}}

	  (scanned_modules, icl_functions, cs) = add_dcl_module_predef_module_and_modules_to_symbol_table optional_dcl_mod optional_pre_def_mod scanned_modules (size dcl_modules) icl_functions cs

	  init_new_dcl_modules = gimme_a_strict_array_type { initialDclModule scanned_module module_n \\ scanned_module <- scanned_modules & module_n<-[size dcl_modules..]}
			
	  init_dcl_modules = {if (i<size dcl_modules) dcl_modules.[i] init_new_dcl_modules.[i-size dcl_modules] \\ i<-[0..size dcl_modules+size init_new_dcl_modules-1]}
	= (mod_name,mod_imported_objects,mod_imports,mod_type,icl_global_function_range,nr_of_functions,first_inst_index,local_defs,icl_functions,init_dcl_modules,main_dcl_module_n,cdefs,sizes,cs)

	where
		add_dcl_module_predef_module_and_modules_to_symbol_table (Yes dcl_mod) optional_predef_mod modules mod_index macro_and_fun_defs cs
			# (mod_sizes_and_defs,macro_and_fun_defs,cs) = add_module_to_symbol_table dcl_mod mod_index macro_and_fun_defs cs
			  (mods, macro_and_fun_defs, cs) = add_predef_module_and_modules_to_symbol_table optional_predef_mod modules (inc mod_index) macro_and_fun_defs cs
			= ([mod_sizes_and_defs : mods], macro_and_fun_defs, cs)
		add_dcl_module_predef_module_and_modules_to_symbol_table No optional_predef_mod modules mod_index macro_and_fun_defs cs
			= add_predef_module_and_modules_to_symbol_table optional_predef_mod modules mod_index macro_and_fun_defs cs
		
		add_predef_module_and_modules_to_symbol_table (Yes predef_mod) modules mod_index macro_and_fun_defs cs
			# (mod_sizes_and_defs,macro_and_fun_defs,cs) = add_module_to_symbol_table predef_mod mod_index macro_and_fun_defs cs
			  (mods, macro_and_fun_defs, cs) = add_modules_to_symbol_table modules (inc mod_index) macro_and_fun_defs cs
			= ([mod_sizes_and_defs : mods], macro_and_fun_defs, cs)
		add_predef_module_and_modules_to_symbol_table No modules mod_index macro_and_fun_defs cs
			= add_modules_to_symbol_table modules mod_index macro_and_fun_defs cs
	
		add_modules_to_symbol_table [] mod_index macro_and_fun_defs cs=:{cs_predef_symbols,cs_symbol_table,cs_x}
			# (cs_predef_symbols, cs_symbol_table) = (cs_predef_symbols, cs_symbol_table) 
					<=< adjust_predefined_module_symbol PD_StdArray
					<=< adjust_predefined_module_symbol PD_StdEnum
					<=< adjust_predefined_module_symbol PD_StdBool
					<=< adjust_predefined_module_symbol PD_StdDynamics
					<=< adjust_predefined_module_symbol PD_PredefinedModule
			= ([], macro_and_fun_defs, { cs & cs_predef_symbols = cs_predef_symbols, cs_symbol_table = cs_symbol_table})
		where
			adjust_predefined_module_symbol :: !Index !(!*PredefinedSymbols, !*SymbolTable) -> (!*PredefinedSymbols, !*SymbolTable)
			adjust_predefined_module_symbol predef_index (pre_def_symbols, symbol_table)
				# (mod_symb, pre_def_symbols) = pre_def_symbols![predef_index]
				# (mod_entry, symbol_table) = readPtr mod_symb.pds_ident.id_info symbol_table
				= case mod_entry.ste_kind of
					STE_Module _
						-> ({ pre_def_symbols & [predef_index] = { mod_symb & pds_module = cs_x.x_main_dcl_module_n, pds_def =  mod_entry.ste_index }}, symbol_table)
					_
						-> (pre_def_symbols, symbol_table)

		add_modules_to_symbol_table [mod : mods] mod_index macro_and_fun_defs cs
			# (mod_sizes_and_defs,macro_and_fun_defs,cs) = add_module_to_symbol_table mod mod_index macro_and_fun_defs cs
			  (mods, macro_and_fun_defs, cs) = add_modules_to_symbol_table mods (inc mod_index) macro_and_fun_defs cs
			= ([mod_sizes_and_defs : mods], macro_and_fun_defs, cs)

		add_module_to_symbol_table mod=:{mod_defs} mod_index macro_and_fun_defs cs=:{cs_predef_symbols,cs_symbol_table, cs_error}
			# def_instances	= convert_class_instances mod_defs.def_instances
			  mod_defs = { mod_defs & def_instances = def_instances }
			  sizes_and_defs = collectFunctionTypes mod_defs.def_funtypes (collectCommonfinitions mod_defs)
			  (macro_and_fun_defs, (sizes, defs)) = collectMacros mod_defs.def_macros macro_and_fun_defs sizes_and_defs
  			  mod = { mod & mod_defs = mod_defs }
		   	  (cs_symbol_table, cs_error) = addDefToSymbolTable cGlobalScope mod_index mod.mod_name (STE_Module mod) cs_symbol_table cs_error
		   	= ((mod,sizes,defs),macro_and_fun_defs,{ cs & cs_symbol_table = cs_symbol_table, cs_error = cs_error })
		where
			convert_class_instances :: ![ParsedInstance a] -> [ClassInstance]
			convert_class_instances [pi : pins]
				= [ParsedInstanceToClassInstance pi {} : convert_class_instances pins]
			convert_class_instances []
				= []

		convert_class_instances :: .[ParsedInstance FunDef] Int -> (!.[FunDef],!.[ClassInstance]);
		convert_class_instances [pi=:{pi_members} : pins] next_fun_index
			# ins_members = sort pi_members
			  (member_symbols, next_fun_index) = determine_indexes_of_members ins_members next_fun_index
			  (next_fun_defs, cins) =  convert_class_instances pins next_fun_index
			= (ins_members ++ next_fun_defs, [ParsedInstanceToClassInstance pi { member \\ member <- member_symbols} : cins])
		convert_class_instances [] next_fun_index
			= ([], [])

		determine_indexes_of_members [{fun_symb,fun_arity}:members] next_fun_index
			#! (member_symbols, last_fun_index) = determine_indexes_of_members members (inc next_fun_index)
			= ([{ds_ident = fun_symb, ds_index = next_fun_index, ds_arity = fun_arity} : member_symbols], last_fun_index)
		determine_indexes_of_members [] next_fun_index
			= ([], next_fun_index)

replace_icl_macros_by_dcl_macros MK_Main icl_macro_index_range decls dcl_modules cs 
	= (decls,dcl_modules,cs)
replace_icl_macros_by_dcl_macros _ {ir_from=first_icl_macro_index,ir_to=end_icl_macro_index} decls dcl_modules cs
	#! main_dcl_module_n=cs.cs_x.x_main_dcl_module_n
	#  ({dcl_macros={ir_from=first_macro_n},dcl_conversions},dcl_modules) = dcl_modules![main_dcl_module_n]
	| case dcl_conversions of No -> True ; _ -> False
		= (decls,dcl_modules,cs)
	# (Yes dcl_to_icl_table) = dcl_conversions
	# macro_renumber_table = create_icl_to_dcl_index_table_for_kind dcl_to_icl_table.[cMacroDefs]
		with
			create_icl_to_dcl_index_table_for_kind :: !{#Int} -> {#Int}
			create_icl_to_dcl_index_table_for_kind dcl_to_icl_table
				= {createArray (end_icl_macro_index-first_icl_macro_index) NoIndex & [dcl_to_icl_table.[dcl_index]-first_icl_macro_index]=dcl_index \\ dcl_index<- [0..size dcl_to_icl_table-1]}
	# decls = replace_icl_macros_by_dcl_macros decls
		with
		replace_icl_macros_by_dcl_macros [decl=:{dcl_kind=STE_FunctionOrMacro _,dcl_index}:decls]
			# icl_n=macro_renumber_table.[dcl_index-first_icl_macro_index]
			# decls = replace_icl_macros_by_dcl_macros decls;
			| dcl_index>=first_icl_macro_index && dcl_index<end_icl_macro_index && icl_n<>NoIndex
//				&& trace_tn decl.dcl_ident
				= [{decl & dcl_kind=STE_FunctionOrMacro [], dcl_index=first_macro_n+icl_n} : decls]
				= [decl : decls]
		replace_icl_macros_by_dcl_macros [decl:decls]
			# decls = replace_icl_macros_by_dcl_macros decls;
			= [decl : decls]
		replace_icl_macros_by_dcl_macros []
			= []
	= (decls,dcl_modules,cs)

remove_function_conversion_table main_dcl_module_n dcl_modules
	# (dcl_mod,dcl_modules) = dcl_modules![main_dcl_module_n]
	= case dcl_mod.dcl_conversions of
		No
			-> ({},dcl_modules)
		(Yes conversion_table)
			#! size_function_conversions = size conversion_table.[cFunctionDefs]
			# conversion_table = {e \\ e <-:conversion_table}
			# (function_conversions,conversion_table) = replace conversion_table cFunctionDefs {n \\ n<-[0..size_function_conversions-1]}
			# dcl_modules = {dcl_modules & [main_dcl_module_n].dcl_conversions=Yes conversion_table}
			-> (function_conversions,dcl_modules)

add_function_conversion_table dcl_to_icl_function_conversions main_dcl_module_n dcl_modules
	# (dcl_mod,dcl_modules) = dcl_modules![main_dcl_module_n]
	= case dcl_mod.dcl_conversions of
		No
			-> dcl_modules
		(Yes conversion_table)
			# conversion_table = {e \\ e <-:conversion_table}
			# conversion_table = {conversion_table & [cFunctionDefs]=dcl_to_icl_function_conversions}
			# dcl_modules = {dcl_modules & [main_dcl_module_n].dcl_conversions=Yes conversion_table}
			-> dcl_modules

check_module2 :: Ident [.ImportedObject] .[Import ImportDeclaration] .ModuleKind !.IndexRange !.IndexRange !Int !Int 
				(Optional (Module a)) [Declaration] *{#FunDef} *{#DclModule} (CollectedDefinitions ClassInstance IndexRange) 
				*{#.Int} *Heaps *CheckState 
			-> (!Bool,.IclModule,!.{#DclModule},.{!Group},!Optional {#Int},!.{#FunDef},!Int,!.Heaps,!.{#PredefinedSymbol},
				!.Heap SymbolTableEntry,!.File);
check_module2 mod_name mod_imported_objects mod_imports mod_type icl_global_function_range icl_instance_range nr_of_functions n_functions_and_macros_in_dcl_modules optional_pre_def_mod local_defs icl_functions init_dcl_modules cdefs sizes heaps cs
	# (main_dcl_module_n,cs)=cs!cs_x.x_main_dcl_module_n
	  (icl_sizes_without_added_dcl_defs, sizes) = memcpy sizes
	  (dcl_modules, local_defs, cdefs, icl_sizes, cs)
	  		= combineDclAndIclModule mod_type init_dcl_modules local_defs cdefs sizes cs

	  icl_common = createCommonDefinitions cdefs

	  (local_defs,dcl_modules,icl_common,cs)
		= renumber_icl_definitions_as_dcl_definitions mod_type local_defs dcl_modules icl_common {icl_sizes.[i] \\ i<-[0..cMacroDefs-1]} cs

	  (dcl_modules, icl_functions, heaps, cs)
		= check_predefined_module optional_pre_def_mod dcl_modules icl_functions heaps cs

	  (dcl_to_icl_function_conversions,dcl_modules) = remove_function_conversion_table main_dcl_module_n dcl_modules

	  (nr_of_icl_component, expl_imp_indices, expl_imp_info, dcl_modules, icl_functions, heaps, cs)
	  		= checkDclModules mod_imports dcl_modules icl_functions heaps cs

	| not cs.cs_error.ea_ok
		= (False, abort "evaluated error 1 (check.icl)", {}, {}, No, {}, cs.cs_x.x_main_dcl_module_n,heaps, cs.cs_predef_symbols, cs.cs_symbol_table, cs.cs_error.ea_file)
	# (imported_module_numbers, dcl_modules)
	  		= foldSt compute_used_module_nrs
			  		expl_imp_indices
	  				(addNr main_dcl_module_n (addNr cPredefinedModuleIndex EndNumbers),
						dcl_modules)

	  dcl_modules = add_function_conversion_table dcl_to_icl_function_conversions main_dcl_module_n dcl_modules
	 
	  cs = { cs & cs_x.x_needed_modules = 0 }
	
	  (nr_of_modules, dcl_modules)	= usize dcl_modules

	  (dcl_macros, dcl_modules)
	  		= dcl_modules![main_dcl_module_n].dcl_macros

	  expl_imp_indices_ikh
			= ikhInsert` False nr_of_modules expl_imp_indices ikhEmpty

	  modules_in_component_set
	  		= bitvectCreate nr_of_modules
	  
	  (imports, (dcl_modules, _, _, cs))
			= solveExplicitImports expl_imp_indices_ikh modules_in_component_set nr_of_modules
					(dcl_modules, bitvectCreate nr_of_modules, expl_imp_info.[nr_of_icl_component], cs)

	  (dcl_modules, cs)
	  		= switch_port_to_new_syntax
	  			(writeExplImportsToFile "icl.txt" imports.si_explicit dcl_modules cs)
	  			(dcl_modules, cs)
	  imports_ikh
	  		= ikhInsert` False nr_of_modules imports ikhEmpty
	  		// maps the module indices of all modules in the actual component to all explicit
	  		// imports of that module

	  cs = addGlobalDefinitionsToSymbolTable local_defs cs

	  (dcls_import_list, dcl_modules, cs)
	  		= addImportedSymbolsToSymbolTable nr_of_modules (Yes dcl_macros) modules_in_component_set
	  				imports_ikh dcl_modules cs

	  (dcl_modules, icl_functions, hp_expression_heap, cs)
			= checkExplicitImportCompleteness imports.si_explicit
									dcl_modules icl_functions heaps.hp_expression_heap cs

	  heaps	= { heaps & hp_expression_heap=hp_expression_heap }

	  icl_imported
	  		= { el \\ el<-dcls_import_list }

	  (local_defs,dcl_modules,cs ) = replace_icl_macros_by_dcl_macros mod_type cdefs.def_macros local_defs dcl_modules cs 
	   
	  (icl_common, dcl_modules, hp_type_heaps, hp_var_heap, cs)
	  		= checkCommonDefinitions cIsNotADclModule main_dcl_module_n icl_common dcl_modules heaps.hp_type_heaps heaps.hp_var_heap cs
	  
	  (unexpanded_icl_type_defs, icl_common)
	  		= copy_com_type_defs icl_common
	  
	  (com_type_defs, dcl_modules, hp_type_heaps, cs_error)
			= expandSynonymTypes main_dcl_module_n icl_common.com_type_defs dcl_modules hp_type_heaps cs.cs_error
	  icl_common
	  		= { icl_common & com_type_defs = com_type_defs }
	  cs
	  		= { cs & cs_error = cs_error }

	  (instance_types, icl_common, dcl_modules, hp_var_heap, hp_type_heaps, cs)
	  		= checkInstances main_dcl_module_n icl_common dcl_modules hp_var_heap hp_type_heaps cs

	  heaps = { heaps & hp_type_heaps = hp_type_heaps, hp_var_heap = hp_var_heap }

	  e_info = { ef_type_defs = icl_common.com_type_defs, ef_selector_defs = icl_common.com_selector_defs, ef_class_defs = icl_common.com_class_defs, 
	  			  ef_cons_defs = icl_common.com_cons_defs, ef_member_defs = icl_common.com_member_defs, ef_modules = dcl_modules,
					ef_is_macro_fun = False }

	  (icl_functions, e_info, heaps, cs) = checkMacros main_dcl_module_n cdefs.def_macros icl_functions e_info heaps cs
	  (icl_functions, e_info, heaps, cs) = checkFunctions main_dcl_module_n cGlobalScope icl_global_function_range.ir_from icl_global_function_range.ir_to icl_functions e_info heaps cs

	  cs = check_start_rule mod_type mod_name icl_global_function_range cs
	  cs = check_needed_modules_are_imported mod_name ".icl" cs

	  (icl_functions, e_info, heaps, {cs_symbol_table, cs_predef_symbols, cs_error,cs_x})
	  	= checkInstanceBodies icl_instance_range icl_functions e_info heaps cs

	  cs_symbol_table = removeDeclarationsFromSymbolTable local_defs cGlobalScope cs_symbol_table

	  cs_symbol_table
			= foldlArraySt removeImportedSymbolsFromSymbolTable icl_imported cs_symbol_table

	  dcl_modules = e_info.ef_modules
	  
	| cs_error.ea_ok
		# {hp_var_heap,hp_type_heaps=hp_type_heaps=:{th_vars},hp_expression_heap} = heaps
		  (spec_functions, dcl_modules, class_instances, icl_functions, new_nr_of_functions, dcl_icl_conversions, var_heap, th_vars, expr_heap)
				= collect_specialized_functions_in_dcl_module dcl_modules icl_common.com_instance_defs icl_functions nr_of_functions main_dcl_module_n
							hp_var_heap th_vars hp_expression_heap
		  icl_instances				= icl_instance_range
		  icl_specials				= {ir_from = nr_of_functions,	ir_to = new_nr_of_functions}
		  icl_functions = copy_instance_types instance_types (array_plus_list icl_functions spec_functions)

		  (dcl_modules, class_instances, icl_functions, cs_predef_symbols)
		  		= adjust_instance_types_of_array_functions_in_std_array_icl dcl_modules class_instances icl_functions main_dcl_module_n cs_predef_symbols

		  (untransformed_fun_bodies, icl_functions) = copy_bodies icl_functions

		  (cached_functions_and_macros,icl_functions) = arrayCopyBegin icl_functions n_functions_and_macros_in_dcl_modules

		  (pds_alias_dummy, cs_predef_symbols) = cs_predef_symbols![PD_DummyForStrictAliasFun]

		  (groups, icl_functions, dcl_modules, var_heap, expr_heap, cs_symbol_table, cs_error)
		  		= partitionateAndLiftFunctions [icl_global_function_range, icl_instances] main_dcl_module_n pds_alias_dummy icl_functions
		  			dcl_modules var_heap expr_heap cs_symbol_table cs_error
		  icl_common	= { icl_common & com_type_defs = e_info.ef_type_defs, com_selector_defs = e_info.ef_selector_defs, com_class_defs = e_info.ef_class_defs,
			  	 			  com_cons_defs = e_info.ef_cons_defs, com_member_defs = e_info.ef_member_defs, com_instance_defs = class_instances }	  			  
		  icl_mod		= { icl_name = mod_name, icl_functions = icl_functions, icl_common = icl_common, icl_instances = icl_instances, icl_specials = icl_specials,
								icl_imported_objects = mod_imported_objects, icl_used_module_numbers = imported_module_numbers,
	  			  				icl_import = icl_imported }

		  heaps = { heaps & hp_var_heap = var_heap, hp_expression_heap = expr_heap, hp_type_heaps = {hp_type_heaps & th_vars = th_vars}}

		  (main_dcl_module, dcl_modules)
		  		= dcl_modules![main_dcl_module_n]
		  (icl_mod, heaps, cs_error)
		  		= compareDefImp icl_sizes_without_added_dcl_defs untransformed_fun_bodies main_dcl_module_n
		  				unexpanded_icl_type_defs main_dcl_module icl_mod heaps cs_error

		= (cs_error.ea_ok, icl_mod, dcl_modules, groups, dcl_icl_conversions, cached_functions_and_macros, cs_x.x_main_dcl_module_n, heaps, cs_predef_symbols, cs_symbol_table, cs_error.ea_file)
		# icl_common	= { icl_common & com_type_defs = e_info.ef_type_defs, com_selector_defs = e_info.ef_selector_defs, com_class_defs = e_info.ef_class_defs,
			  	 			  com_cons_defs = e_info.ef_cons_defs, com_member_defs = e_info.ef_member_defs }	  			  
		  icl_mod		= { icl_name = mod_name, icl_functions = icl_functions, icl_common = icl_common,
		  					icl_instances = icl_instance_range,
		  					icl_specials = {ir_from = nr_of_functions, ir_to = nr_of_functions},
							icl_imported_objects = mod_imported_objects, icl_used_module_numbers = imported_module_numbers,
	    		  			icl_import = icl_imported }
		= (False, icl_mod, dcl_modules, {}, No, {}, cs_x.x_main_dcl_module_n,heaps, cs_predef_symbols, cs_symbol_table, cs_error.ea_file)
	where
		check_start_rule mod_kind mod_name {ir_from, ir_to} cs=:{cs_predef_symbols,cs_symbol_table,cs_x}
			# (pre_symb, cs_predef_symbols) = cs_predef_symbols![PD_Start]
			  ({ste_kind, ste_index}, cs_symbol_table) = readPtr pre_symb.pds_ident.id_info cs_symbol_table
			  cs = { cs & cs_predef_symbols = cs_predef_symbols, cs_symbol_table = cs_symbol_table }
			= case ste_kind of
				STE_FunctionOrMacro _
					| ir_from <= ste_index &&  ste_index < ir_to
						-> { cs & cs_predef_symbols = { cs.cs_predef_symbols & [PD_Start] = { pre_symb & pds_def = ste_index, pds_module = cs_x.x_main_dcl_module_n }}}
				STE_Imported STE_DclFunction mod_index
					-> { cs & cs_predef_symbols = { cs.cs_predef_symbols & [PD_Start] = { pre_symb & pds_def = ste_index, pds_module = mod_index }}}
				_
					-> case mod_kind of
							MK_Main
								# pos = newPosition pre_symb.pds_ident (LinePos (mod_name.id_name+++".icl") 1)
								-> { cs & cs_error = checkErrorWithIdentPos pos " has not been declared" cs.cs_error }
							_
								-> cs

		check_predefined_module (Yes {mod_name={id_info}}) modules macro_and_fun_defs heaps cs=:{cs_symbol_table}
			# (entry, cs_symbol_table) = readPtr id_info cs_symbol_table
			# cs = { cs & cs_symbol_table = cs_symbol_table <:= (id_info, { entry & ste_kind = STE_ClosedModule })}
			  {ste_kind = STE_Module mod, ste_index} = entry
			  solved_imports
			  	= { si_explicit = [], si_implicit = [] }
			  (deferred_stuff, (_, modules, macro_and_fun_defs, heaps, cs))
			  		= checkDclModule EndNumbers [] (ikhInsert` False cPredefinedModuleIndex solved_imports ikhEmpty) cUndef False cDummyArray mod ste_index cDummyArray modules macro_and_fun_defs heaps cs
			  (modules, heaps, cs)
					= doSomeThingsThatHaveToBeDoneAfterTheWholeComponentHasBeenChecked cPredefinedModuleIndex
							deferred_stuff (modules, heaps, cs)
			  ({dcl_declared={dcls_import,dcls_local,dcls_local_for_import}}, modules) = modules![ste_index]
			= (modules, macro_and_fun_defs, heaps, 
			   addDeclarationsOfDclModToSymbolTable ste_index dcls_local_for_import dcls_import cs)
		check_predefined_module No modules macro_and_fun_defs heaps cs
			= (modules, macro_and_fun_defs, heaps, cs)

		collect_specialized_functions_in_dcl_module :: !w:{# DclModule} !v:{# ClassInstance} !u:{# FunDef} !Index !Int !*VarHeap !*TypeVarHeap !*ExpressionHeap
			-> (![FunDef], !w:{# DclModule}, !v:{# ClassInstance}, !u:{# FunDef}, !Index, !(Optional {# Index}), !*VarHeap,  !*TypeVarHeap, !*ExpressionHeap)
 		collect_specialized_functions_in_dcl_module modules icl_instances icl_functions first_free_index main_dcl_module_n var_heap type_var_heap expr_heap
			# (dcl_mod, modules) = modules![main_dcl_module_n]
			# {dcl_specials,dcl_functions,dcl_common,dcl_conversions} = dcl_mod
			= case dcl_conversions of
				Yes conversion_table
					# (new_conversion_table, icl_instances)
					  		= build_conversion_table_for_instances_of_dcl_mod dcl_specials first_free_index
					  				dcl_functions dcl_common.com_instance_defs conversion_table icl_instances
					  (spec_fun_defs, (icl_functions, last_index, (var_heap, type_var_heap, expr_heap)))
							= collect_specialized_functions dcl_specials.ir_from dcl_specials.ir_to dcl_functions new_conversion_table
									(icl_functions, first_free_index, (var_heap, type_var_heap, expr_heap))
					-> (spec_fun_defs, modules, icl_instances, icl_functions, last_index, Yes new_conversion_table, var_heap, type_var_heap, expr_heap)
				No
					-> ([], modules, icl_instances, icl_functions, first_free_index, No, var_heap, type_var_heap, expr_heap)
		where
			build_conversion_table_for_instances_of_dcl_mod {ir_from,ir_to} first_free_index dcl_functions dcl_instances conversion_table icl_instances
				#! nr_of_dcl_functions = size dcl_functions
				# dcl_instances_table = conversion_table.[cInstanceDefs]
				  dcl_function_table = conversion_table.[cFunctionDefs]
				  new_table = { createArray nr_of_dcl_functions NoIndex & [i] = icl_index \\ icl_index <-: dcl_function_table & i <- [0..] }
				  index_diff = first_free_index - ir_from
				  new_table = { new_table & [i] = i + index_diff \\ i <- [ir_from .. ir_to - 1] }
				= build_conversion_table_for_instances 0 dcl_instances dcl_instances_table icl_instances new_table

			build_conversion_table_for_instances dcl_class_inst_index dcl_instances class_instances_table icl_instances new_table 
				| dcl_class_inst_index < size class_instances_table
					# icl_index = class_instances_table.[dcl_class_inst_index]
					# (icl_instance, icl_instances) = icl_instances![icl_index]
					  dcl_instance = dcl_instances.[dcl_class_inst_index]
					# new_table = build_conversion_table_for_instances_of_members 0 dcl_instance.ins_members icl_instance.ins_members new_table
					= build_conversion_table_for_instances (inc dcl_class_inst_index) dcl_instances class_instances_table icl_instances new_table
					= (new_table, icl_instances)
			
			build_conversion_table_for_instances_of_members mem_index dcl_members icl_members new_table
				| mem_index < size dcl_members
					# dcl_member = dcl_members.[mem_index]
					  icl_member = icl_members.[mem_index]
					= build_conversion_table_for_instances_of_members (inc mem_index) dcl_members icl_members
						{ new_table & [dcl_member.ds_index] = icl_member.ds_index }
					= new_table
			
			collect_specialized_functions spec_index last_index dcl_fun_types conversion_table (icl_functions, next_fun_index, heaps)
				| spec_index < last_index
					# {ft_type,ft_specials = SP_FunIndex dcl_index} = dcl_fun_types.[spec_index]
					  icl_index = conversion_table.[dcl_index]
					  (icl_fun, icl_functions) = icl_functions![icl_index]
					  (new_fun_def, heaps) = build_function next_fun_index icl_fun ft_type heaps
					  (new_fun_defs, funs_index_heaps)
					   		= collect_specialized_functions (inc spec_index) last_index dcl_fun_types conversion_table (icl_functions, inc next_fun_index, heaps)
					= ([new_fun_def : new_fun_defs], funs_index_heaps) 
					= ([], (icl_functions, next_fun_index, heaps))
		 
			build_function new_fun_index fun_def=:{fun_symb, fun_index, fun_arity,  fun_body = CheckedBody {cb_args}, fun_info} fun_type
						(var_heap, type_var_heap, expr_heap)
				# (tb_args, var_heap) = mapSt new_free_var cb_args var_heap
				  (app_args, expr_heap) = mapSt new_bound_var tb_args expr_heap
				  (app_info_ptr, expr_heap) = newPtr EI_Empty expr_heap
				  tb_rhs = App { app_symb = {	symb_name = fun_symb, symb_arity = fun_arity,
												symb_kind = SK_Function { glob_module = main_dcl_module_n, glob_object = fun_index }},
								 app_args = app_args,
								 app_info_ptr = app_info_ptr }
				= ({ fun_def & fun_index=new_fun_index, fun_body = TransformedBody {tb_args = tb_args, tb_rhs = tb_rhs}, fun_type = Yes fun_type,
						fun_info = { EmptyFunInfo & fi_calls = [ { fc_index = fun_index, fc_level = cGlobalScope }] }},
					(var_heap, type_var_heap, expr_heap))
		
		new_bound_var :: !FreeVar !*ExpressionHeap -> (!Expression, !*ExpressionHeap)
		new_bound_var {fv_name,fv_info_ptr} expr_heap
			# (var_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
			= (Var { var_name = fv_name, var_info_ptr = fv_info_ptr, var_expr_ptr = var_expr_ptr }, expr_heap)

		new_free_var :: !FreeVar *VarHeap -> (!FreeVar, !*VarHeap)
		new_free_var fv var_heap
			# (fv_info_ptr, var_heap) = newPtr VI_Empty var_heap
			= ({ fv & fv_info_ptr = fv_info_ptr, fv_def_level = NotALevel, fv_count = 0}, var_heap)
			
		copy_instance_types :: [(Index,SymbolType)] !*{# FunDef} -> !*{# FunDef}
		copy_instance_types types fun_defs 
			= foldl copy_instance_type fun_defs types
		copy_instance_type fun_defs (index, symbol_type)
			# (inst_def, fun_defs) = fun_defs![index]
			= { fun_defs & [index] = { inst_def & fun_type = Yes symbol_type }}
		
		adjust_instance_types_of_array_functions_in_std_array_icl dcl_modules class_instances fun_defs main_dcl_module_n predef_symbols
			# ({pds_def}, predef_symbols) = predef_symbols![PD_StdArray]
			| pds_def == main_dcl_module_n
				#! nr_of_instances = size class_instances
				# ({dcl_common, dcl_conversions = Yes conversion_table}, dcl_modules) = dcl_modules![main_dcl_module_n]
				  ({pds_def}, predef_symbols) = predef_symbols![PD_ArrayClass]
				  (offset_table, _, predef_symbols) = arrayFunOffsetToPD_IndexTable dcl_common.com_member_defs predef_symbols
				  array_class_index = conversion_table.[cClassDefs].[pds_def]
				  (class_instances, fun_defs, predef_symbols) 
					= iFoldSt (adjust_instance_types_of_array_functions array_class_index offset_table) 0 nr_of_instances
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

		copy_bodies :: !*{# FunDef} -> (!.{!FunctionBody}, !*{# FunDef})
		copy_bodies fun_defs
			#! size = size fun_defs
			# new = createArray size NoBody
			= iFoldSt (\i (dst, src=:{[i]=src_i})->({ dst & [i] = src_i.fun_body }, src)) 0 size (new, fun_defs)

		copy_com_type_defs icl_common=:{com_type_defs}
			# (com_type_defs`, com_type_defs)
				= memcpy com_type_defs
			= (com_type_defs`, { icl_common & com_type_defs = com_type_defs })

check_needed_modules_are_imported mod_name extension cs=:{cs_x={x_needed_modules}}
	# cs = case x_needed_modules bitand cNeedStdDynamics of
			0 -> cs
			_ -> check_it PD_StdDynamics mod_name "" extension cs
	# cs = case x_needed_modules bitand cNeedStdArray of
			0 -> cs
			_ -> check_it PD_StdArray mod_name " (needed for array denotations)" extension cs
	# cs = case x_needed_modules bitand cNeedStdEnum of
			0 -> cs
			_ -> check_it PD_StdEnum mod_name " (needed for [..] expressions)" extension cs
	= cs
  where
	check_it pd mod_name explanation extension cs=:{cs_predef_symbols, cs_symbol_table}
  		#! {pds_ident} = cs_predef_symbols.[pd]	
		# ({ste_kind}, cs_symbol_table) = readPtr pds_ident.id_info cs_symbol_table
		  cs = { cs & cs_symbol_table = cs_symbol_table }
		= case ste_kind of
			STE_ClosedModule
				-> cs
			STE_Empty
				# error_location = { ip_ident = mod_name, ip_line = 1, ip_file = mod_name.id_name+++extension}
				  cs_error = pushErrorAdmin error_location cs.cs_error
				  cs_error = checkError pds_ident ("not imported"+++explanation) cs_error
				  cs_error = popErrorAdmin cs_error
				-> { cs & cs_error = cs_error }

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

makeElemTypeOfArrayFunctionStrict :: !SymbolType !Index !{# Index} -> SymbolType
makeElemTypeOfArrayFunctionStrict st=:{st_args,st_result} me_offset offset_table
	# array_fun_kind = offset_table.[me_offset]
	| array_fun_kind == PD_UnqArraySelectFun
		# (TA tuple [elem : res_array]) = st_result.at_type
		= { st & st_result = { st_result &  at_type = TA tuple [{ elem & at_annotation = AN_Strict } : res_array]}}
	| array_fun_kind == PD_ArrayUpdateFun
		# [array, index, elem: _] = st_args
		= { st & st_args = [array, index, { elem & at_annotation = AN_Strict }] }
	| array_fun_kind == PD_CreateArrayFun
		# [array, elem: _] = st_args
		= { st & st_args = [array, { elem & at_annotation = AN_Strict }] }
	| array_fun_kind == PD_ArrayReplaceFun
		# [arg_array, index, elem: _] = st_args
		  (TA tuple [elem : res_array]) = st_result.at_type
		= { st & st_args = [arg_array, index, { elem & at_annotation = AN_Strict }],
					st_result = { st_result &  at_type = TA tuple [{ elem & at_annotation = AN_Strict } : res_array]}}
		= st

initialDclModule ({mod_name, mod_defs=mod_defs=:{def_funtypes,def_macros}, mod_type}, sizes, all_defs) module_n
	# dcl_common= createCommonDefinitions mod_defs
	= 	{	dcl_name			= mod_name
		,	dcl_functions		= { function \\ function <- mod_defs.def_funtypes }
		,	dcl_macros			= def_macros
		,	dcl_instances		= { ir_from = 0, ir_to = 0 }
		,	dcl_specials		= { ir_from = 0, ir_to = 0 }
		,	dcl_common			= dcl_common
		,	dcl_sizes			= sizes
		,	dcl_declared		=
			{
				dcls_import 	= {}
			,	dcls_local		= all_defs
			,	dcls_local_for_import = {local_declaration_for_import decl module_n \\ decl<-all_defs}
			}
		,	dcl_conversions = No
		,	dcl_is_system	= case mod_type of
								MK_System 	-> True
								_			-> False
		, dcl_imported_module_numbers = EndNumbers
		}

addImportedSymbolsToSymbolTable importing_mod opt_macro_range modules_in_component_set imports_ikh
			dcl_modules cs
	#! nr_of_dcl_modules
			= size dcl_modules
	# {si_explicit, si_implicit}
			= ikhSearch` importing_mod imports_ikh
	  (decls_accu, visited_modules, dcl_modules, cs)
	  		= foldSt (add_impl_imported_symbols_with_new_error_pos opt_macro_range importing_mod
	  					modules_in_component_set imports_ikh)
	  				si_implicit ([], bitvectCreate nr_of_dcl_modules, dcl_modules, cs)
	= foldSt (add_expl_imported_symbols_with_new_error_pos opt_macro_range importing_mod) si_explicit
 				(decls_accu, dcl_modules, cs)
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

		
	add_expl_imported_symbols_with_new_error_pos opt_macro_range importing_mod (decls, position)
			(decls_accu, dcl_modules, cs)
		# cs
				= pushErrorAdmin (newPosition import_ident position) cs
		  (decls_accu, dcl_modules, cs)
				= foldSt (add_expl_imp_declaration opt_macro_range importing_mod) decls
						(decls_accu, dcl_modules, cs)
		= (decls_accu, dcl_modules, popErrorAdmin cs)		
		
	add_declaration opt_dcl_macro_range importing_mod declaration (decls_accu, cs)
		# (not_already_imported, cs)
				= add_declaration_to_symbol_table opt_dcl_macro_range declaration importing_mod cs
		| not_already_imported
			= ([declaration:decls_accu], cs)
		= (decls_accu, cs)

	add_expl_imp_declaration opt_dcl_macro_range importing_mod declaration
			(decls_accu, dcl_modules, cs)
		# (not_already_imported, cs)
				= add_declaration_to_symbol_table opt_dcl_macro_range declaration importing_mod cs
		| not_already_imported
			# (consequence_declarations, dcl_modules, cs)
					= switch_import_syntax
							(add_consequences_to_symbol_table importing_mod declaration dcl_modules cs)
							([], dcl_modules, cs)
			= (consequence_declarations++[declaration:decls_accu], dcl_modules, cs)
		= (decls_accu, dcl_modules, cs)

	// this function is for old syntax only
	add_consequences_to_symbol_table _ {dcl_kind=STE_FunctionOrMacro _} dcl_modules cs
		= ([], dcl_modules, cs)
	add_consequences_to_symbol_table importing_mod {dcl_index, dcl_kind=STE_Imported ste_kind mod_index} dcl_modules cs
		= add_consequences importing_mod dcl_index ste_kind mod_index dcl_modules cs
	  where
		add_consequences _ dcl_index STE_Type mod_index dcl_modules cs
			# (td=:{td_rhs}, dcl_modules)
					= dcl_modules![mod_index].dcl_common.com_type_defs.[dcl_index]
			= case td_rhs of
				RecordType {rt_fields}
					-> foldlArraySt (add_field importing_mod mod_index) rt_fields ([], dcl_modules, cs)
				_
					-> ([], dcl_modules, cs)
		add_consequences importing_mod dcl_index STE_Class mod_index dcl_modules cs
			# (cd=:{class_members}, dcl_modules)
					= dcl_modules![mod_index].dcl_common.com_class_defs.[dcl_index]
			= foldlArraySt (add_member importing_mod mod_index) class_members ([], dcl_modules, cs)
		add_consequences _ dcl_index _ mod_index dcl_modules cs
			= ([], dcl_modules, cs)

		add_field importing_mod mod_index {fs_index} (declarations_accu, dcl_modules, cs)
			# (sd=:{sd_symb, sd_field, sd_pos}, dcl_modules)
					= dcl_modules![mod_index].dcl_common.com_selector_defs.[fs_index]
			  declaration
					= { dcl_ident = sd_field, dcl_pos = sd_pos,
						dcl_kind = STE_Imported (STE_Field sd_symb) mod_index, dcl_index = fs_index }
			  (is_new, cs)
			  		= add_declaration_to_symbol_table No declaration importing_mod cs
			| is_new
				= ([declaration:declarations_accu], dcl_modules, cs)
			= (declarations_accu, dcl_modules, cs)
		add_member importing_mod mod_index {ds_ident, ds_index} (declarations_accu, dcl_modules, cs)
			# (sd=:{me_symb, me_pos}, dcl_modules)
					= dcl_modules![mod_index].dcl_common.com_member_defs.[ds_index]
			  declaration
					= { dcl_ident = me_symb, dcl_pos = me_pos,
						dcl_kind = STE_Imported STE_Member mod_index, dcl_index = ds_index }
			  (is_new, cs)
			  		= add_declaration_to_symbol_table No declaration importing_mod cs
			| is_new
				= ([declaration:declarations_accu], dcl_modules, cs)
			= (declarations_accu, dcl_modules, cs)

add_declaration_to_symbol_table opt_dcl_macro_range {dcl_kind=STE_FunctionOrMacro _, dcl_ident, dcl_index} _ cs
	= addImportedFunctionOrMacro opt_dcl_macro_range dcl_ident dcl_index cs
add_declaration_to_symbol_table yes_for_icl_module {dcl_kind=dcl_kind=:STE_Imported def_kind def_mod, dcl_ident, dcl_index, dcl_pos} importing_mod cs
	= addSymbol yes_for_icl_module dcl_ident dcl_pos dcl_kind def_kind dcl_index def_mod importing_mod cs

updateExplImpInfo super_components mod_index dcls_import dcls_local_for_import
			dcl_modules expl_imp_infos cs_symbol_table
	# (changed_symbols, (expl_imp_infos, cs_symbol_table))
	  		= mapSt markExplImpSymbols super_components (expl_imp_infos, cs_symbol_table)
	  cs_symbol_table
	  		= switch_import_syntax
	  			(foldlArraySt opt_store_instance_with_class_symbol dcls_local_for_import cs_symbol_table)
	  			cs_symbol_table
	  cs_symbol_table
	  		= switch_import_syntax
	  			(foldlArraySt opt_store_instance_with_class_symbol dcls_import cs_symbol_table)
	  			cs_symbol_table
	  (dcl_modules, expl_imp_infos, cs_symbol_table)
	  		= foldlArraySt (update_expl_imp_for_marked_symbol mod_index) dcls_local_for_import
	  				(dcl_modules, expl_imp_infos, cs_symbol_table)
	  (dcl_modules, expl_imp_infos, cs_symbol_table)
	  		= foldlArraySt (update_expl_imp_for_marked_symbol mod_index) dcls_import
	  				(dcl_modules, expl_imp_infos, cs_symbol_table)
	  cs_symbol_table
	  		= foldSt (\l cs_symbol_table->foldSt restoreHeap l cs_symbol_table)
	  				changed_symbols cs_symbol_table
	= (dcl_modules, expl_imp_infos, cs_symbol_table)
	
	
opt_store_instance_with_class_symbol decl=:{dcl_kind=STE_Imported (STE_Instance class_ident) _} cs_symbol_table
	/* This function is only for old import syntax.
	   All declared instances for a class have to be collected
	*/
	= optStoreInstanceWithClassSymbol decl class_ident cs_symbol_table
opt_store_instance_with_class_symbol _ cs_symbol_table
	= cs_symbol_table


update_expl_imp_for_marked_symbol mod_index decl=:{dcl_ident} (dcl_modules, expl_imp_infos, cs_symbol_table)
	# (ste, cs_symbol_table)
			= readPtr dcl_ident.id_info cs_symbol_table
	= updateExplImpForMarkedSymbol mod_index decl ste dcl_modules expl_imp_infos cs_symbol_table

update_expl_imp_for_marked_local_symbol mod_index decl=:{dcl_ident} (dcl_modules, expl_imp_infos, cs_symbol_table)
	# (ste, cs_symbol_table)
			= readPtr dcl_ident.id_info cs_symbol_table
	= updateExplImpForMarkedLocalSymbol mod_index decl ste dcl_modules expl_imp_infos cs_symbol_table

updateExplImpForMarkedLocalSymbol :: !Index Declaration !SymbolTableEntry !u:{#DclModule} !{!{!*ExplImpInfo}} !*SymbolTable
		-> (!u:{#DclModule}, !{!{!.ExplImpInfo}}, !.SymbolTable)
updateExplImpForMarkedLocalSymbol mod_index decl {ste_kind=STE_ExplImpComponentNrs component_numbers inst_indices}
			dcl_modules expl_imp_infos cs_symbol_table
	= foldSt (addExplImpInfo mod_index decl) component_numbers
			(dcl_modules, expl_imp_infos, cs_symbol_table)
  where
	addExplImpInfo :: !Index Declaration !ComponentNrAndIndex !(!u:{#DclModule}, !{!{!*ExplImpInfo}}, !v:SymbolTable)
				-> (!u:{#DclModule}, !{!{!.ExplImpInfo}}, !v:SymbolTable)
	addExplImpInfo mod_index decl { cai_component_nr, cai_index } (dcl_modules, expl_imp_infos, cs_symbol_table)
		# (ExplImpInfo eii_ident eii_declaring_modules, expl_imp_infos)
				= replaceTwoDimArrElt cai_component_nr cai_index TemporarilyFetchedAway expl_imp_infos
		  (all_belongs, dcl_modules)
		  		= getBelongingSymbols decl dcl_modules
		  di_belonging
		  		= nsFromTo (nrOfBelongingSymbols all_belongs)
		  di
		  		= { di_decl = decl, di_instances = [], di_belonging = di_belonging }
		  new_expl_imp_info
		  		= ExplImpInfo eii_ident (ikhInsert` False mod_index di eii_declaring_modules)
		= (dcl_modules, { expl_imp_infos & [cai_component_nr,cai_index] = new_expl_imp_info }, cs_symbol_table)
updateExplImpForMarkedLocalSymbol _ _ entry dcl_modules expl_imp_infos cs_symbol_table
	= (dcl_modules, expl_imp_infos, cs_symbol_table)


//1.3
memcpy :: u:(a b) -> (!.(c b),!v:(a b)) | Array a & createArray_u , createArrayc_u , size_u , update_u , uselect_u b & Array c, [u <= v];
//3.1
/*2.0
memcpy :: u:(a b) -> (!.(c b),!u:(a b)) | Array c b & Array a b
0.2*/
memcpy src
	#! size
			= size src
	| size==0
		= ({}, src)
	# (el0, src)
			= src![0]
	  new
			= createArray size el0
	= iFoldSt (\i (dst, src=:{[i]=src_i})->({ dst & [i] = src_i }, src)) 0 size (new, src)

doSomeThingsThatHaveToBeDoneAfterTheWholeComponentHasBeenChecked 
		:: !.Int !(!.Int,.Int,.[FunType])
		!(!*{#.DclModule},!*Heaps,!*CheckState)
	 -> (!.{#DclModule},!.Heaps,!.CheckState);
doSomeThingsThatHaveToBeDoneAfterTheWholeComponentHasBeenChecked mod_index
			(nr_of_dcl_functions_and_instances, nr_of_dcl_funs_insts_and_specs, rev_special_defs)
			(dcl_modules, heaps=:{hp_type_heaps, hp_var_heap}, cs=:{cs_error})
	#! main_dcl_module_n
			= cs.cs_x.x_main_dcl_module_n
	# (dcl_modules, hp_type_heaps, cs_error)
	  		= case mod_index==main_dcl_module_n of
	  			True
	  				-> (dcl_modules, hp_type_heaps, cs_error)
	  			False
	  				-> expand_syn_types_of_dcl_mod mod_index (dcl_modules, hp_type_heaps, cs_error)
	  (dcl_mod=:{dcl_functions, dcl_common}, dcl_modules)
			= dcl_modules![mod_index]
	  nr_of_dcl_functions
	  		= size dcl_functions
	  (memb_inst_defs, nr_of_dcl_functions_and_instances2, rev_spec_class_inst, 
		com_instance_defs, com_class_defs, com_member_defs, dcl_modules, hp_type_heaps, hp_var_heap, cs)
			= determineTypesOfInstances nr_of_dcl_functions mod_index
	  				(fst (memcpy dcl_common.com_instance_defs))
	  				(fst (memcpy dcl_common.com_class_defs))
	  				(fst (memcpy dcl_common.com_member_defs))
	  				dcl_modules hp_type_heaps hp_var_heap { cs & cs_error = cs_error }
	  heaps
	  		= { heaps & hp_type_heaps = hp_type_heaps, hp_var_heap = hp_var_heap }
	  (nr_of_dcl_funs_insts_and_specs, new_class_instances, rev_special_defs, all_spec_types, heaps, cs_error)
			= checkSpecialsOfInstances mod_index nr_of_dcl_functions rev_spec_class_inst nr_of_dcl_funs_insts_and_specs []
					rev_special_defs { mem \\ mem <- memb_inst_defs } { [] \\ mem <- memb_inst_defs } heaps cs.cs_error
	  dcl_functions
	  		= arrayPlusList dcl_functions
	  			(   [ { mem_inst & ft_specials = if (isEmpty spec_types) SP_None (SP_ContextTypes spec_types) } 
				  	  \\ mem_inst <- memb_inst_defs & spec_types <-: all_spec_types 
				  	]
	  			 ++ reverse rev_special_defs
	  			)
	  cs
	  		= { cs & cs_error = cs_error }
	#! mod_index_of_std_array = cs.cs_predef_symbols.[PD_StdArray].pds_def
	# (com_member_defs, com_instance_defs, dcl_functions, cs)
	  		= case mod_index_of_std_array==mod_index of
				False
					-> (com_member_defs, com_instance_defs, dcl_functions, cs)
				True
					-> adjust_instance_types_of_array_functions_in_std_array_dcl mod_index
							com_member_defs com_instance_defs dcl_functions cs
	  dcl_mod
	  		= { dcl_mod & 
	  				dcl_functions = dcl_functions,
	  				dcl_specials = { ir_from = nr_of_dcl_functions_and_instances,
	  								ir_to = nr_of_dcl_funs_insts_and_specs },
	  				dcl_common = { dcl_common & com_instance_defs = com_instance_defs,
	  								com_class_defs = com_class_defs, com_member_defs = com_member_defs }}
	  dcl_modules
	  		= { dcl_modules & [mod_index] = dcl_mod }
	= (dcl_modules, heaps, cs)
  where
	expand_syn_types_of_dcl_mod mod_index (dcl_modules, hp_type_heaps, cs_error)
		# (type_defs, dcl_modules)
				= dcl_modules![mod_index].dcl_common.com_type_defs
		  unique_type_defs
		  		= { el \\ el <-:type_defs }
		  (expanded_type_defs, dcl_modules, hp_type_heaps, cs_error)
				= expandSynonymTypes mod_index unique_type_defs dcl_modules hp_type_heaps cs_error
		  dcl_modules
		  		= { dcl_modules & [mod_index].dcl_common.com_type_defs = expanded_type_defs }
		= (dcl_modules, hp_type_heaps, cs_error)

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
					!(Module (CollectedDefinitions ClassInstance IndexRange)) !Index
					!*ExplImpInfos !*{#DclModule} !*{#FunDef} !*Heaps !*CheckState
				-> (!(!Int,!Index,![FunType]), !(!*ExplImpInfos, !*{#DclModule}, !*{#FunDef}, !*Heaps, !*CheckState))
checkDclModule dcl_imported_module_numbers super_components imports_ikh component_nr is_on_cycle modules_in_component_set
		 {mod_name,mod_imports,mod_defs} mod_index
		 expl_imp_info modules icl_functions heaps=:{hp_var_heap, hp_type_heaps,hp_expression_heap} cs
//	| False--->("checkDclModule", mod_name, mod_index) //, modules.[mod_index].dcl_declared.dcls_local)
//		= undef
	# (dcl_mod, modules)			= modules![mod_index]
	  dcl_defined 					= dcl_mod.dcl_declared.dcls_local
	  dcl_common					= createCommonDefinitions mod_defs
	  dcl_macros					= mod_defs.def_macros
	  cs							= addGlobalDefinitionsToSymbolTable dcl_defined cs
	  (dcls_import_list, modules, cs)
	  		= addImportedSymbolsToSymbolTable mod_index No modules_in_component_set
	  				imports_ikh modules cs
	  dcls_import
	  		= { el \\ el<-dcls_import_list }
	  cs							= { cs & cs_x.x_needed_modules = 0 }
	  nr_of_dcl_functions 			= size dcl_mod.dcl_functions

	#! main_dcl_module_n = cs.cs_x.x_main_dcl_module_n

	# (dcl_common, modules, hp_type_heaps, hp_var_heap, cs)
	  		= checkCommonDefinitions cIsADclModule mod_index dcl_common modules hp_type_heaps hp_var_heap cs
	#!nr_of_members
	  		= count_members mod_index dcl_common.com_instance_defs dcl_common.com_class_defs modules
	# nr_of_dcl_functions_and_instances
			= nr_of_dcl_functions+nr_of_members
	  heaps
	  		= { heaps & hp_type_heaps = hp_type_heaps, hp_var_heap = hp_var_heap, hp_expression_heap=hp_expression_heap}
	  (nr_of_dcl_funs_insts_and_specs, rev_function_list, rev_special_defs, com_type_defs, com_class_defs, modules, heaps, cs)
	  		= checkDclFunctions mod_index nr_of_dcl_functions_and_instances mod_defs.def_funtypes
	  			dcl_common.com_type_defs dcl_common.com_class_defs modules heaps cs

	  dcl_functions = { function \\ function <- reverse rev_function_list }

	  com_member_defs = dcl_common.com_member_defs
	  e_info = { ef_type_defs = com_type_defs, ef_selector_defs = dcl_common.com_selector_defs, ef_class_defs = com_class_defs,
	  			 ef_cons_defs = dcl_common.com_cons_defs, ef_member_defs = com_member_defs, ef_modules = modules,
				 ef_is_macro_fun = False }

	  (icl_functions, e_info=:{ef_modules=modules}, heaps=:{hp_expression_heap}, cs)
			= checkMacros mod_index dcl_macros icl_functions e_info heaps cs
	  
	  cs = check_needed_modules_are_imported mod_name ".dcl" cs

	  com_instance_defs = dcl_common.com_instance_defs

	  (ef_member_defs, com_instance_defs, dcl_functions, cs)
	  		= adjust_predefined_symbols mod_index e_info.ef_member_defs com_instance_defs dcl_functions cs

	  (modules, icl_functions, hp_expression_heap, cs)
			= case is_on_cycle of
				False 	-> checkExplicitImportCompleteness (ikhSearch` mod_index imports_ikh).si_explicit
									modules icl_functions hp_expression_heap cs
				True	-> (modules, icl_functions, hp_expression_heap, cs)
	  heaps = { heaps & hp_expression_heap = hp_expression_heap }

	  dcl_common = { dcl_common & com_type_defs = e_info.ef_type_defs, com_selector_defs = e_info.ef_selector_defs, com_class_defs = e_info.ef_class_defs,
			  	 		com_instance_defs = com_instance_defs, com_cons_defs = e_info.ef_cons_defs, com_member_defs = e_info.ef_member_defs }

	  (modules, expl_imp_info, cs_symbol_table)
	  		= updateExplImpInfo super_components mod_index dcls_import dcl_mod.dcl_declared.dcls_local_for_import
	  				modules expl_imp_info cs.cs_symbol_table
	
	  cs_symbol_table
	  		= removeDeclarationsFromSymbolTable dcl_defined cModuleScope cs_symbol_table

	  cs_symbol_table
			= foldlArraySt removeImportedSymbolsFromSymbolTable dcls_import cs_symbol_table
	  dcl_mod = { dcl_mod &  dcl_declared = { dcl_mod.dcl_declared & dcls_import = dcls_import },
	  			 dcl_common = dcl_common, dcl_functions = dcl_functions, 
	  			 dcl_instances = { ir_from = nr_of_dcl_functions, ir_to = nr_of_dcl_functions_and_instances },
	  			 dcl_specials = { ir_from = cUndef, ir_to = cUndef },
	  			 dcl_imported_module_numbers = dcl_imported_module_numbers}
	= ((nr_of_dcl_functions_and_instances, nr_of_dcl_funs_insts_and_specs, rev_special_defs),
		(expl_imp_info, { modules & [ mod_index ] = dcl_mod }, icl_functions, heaps, { cs & cs_symbol_table = cs_symbol_table }))
where
	adjust_predefined_symbols mod_index class_members class_instances fun_types cs=:{cs_predef_symbols}
		# (pre_mod, cs_predef_symbols) = cs_predef_symbols![PD_StdArray]
		| pre_mod.pds_def == mod_index
			# cs = { cs & cs_predef_symbols = cs_predef_symbols}
				<=< adjust_predef_symbols PD_CreateArrayFun PD_UnqArraySizeFun mod_index STE_Member
				<=< adjust_predef_symbol PD_ArrayClass mod_index STE_Class
			= (class_members, class_instances, fun_types, cs)
		# (pre_mod, cs_predef_symbols) = cs_predef_symbols![PD_PredefinedModule]
		| pre_mod.pds_def == mod_index
			= (class_members, class_instances, fun_types, { cs & cs_predef_symbols = cs_predef_symbols}
				<=< adjust_predef_symbols PD_ListType PD_UnboxedArrayType mod_index STE_Type
				<=< adjust_predef_symbols PD_ConsSymbol PD_Arity32TupleSymbol mod_index STE_Constructor
				<=< adjust_predef_symbol PD_TypeCodeClass mod_index STE_Class
				<=< adjust_predef_symbol PD_TypeCodeMember mod_index STE_Member
				<=< adjust_predef_symbol PD_DummyForStrictAliasFun mod_index STE_DclFunction)
		# (pre_mod, cs_predef_symbols) = cs_predef_symbols![PD_StdBool]
		| pre_mod.pds_def == mod_index
			= (class_members, class_instances, fun_types, { cs & cs_predef_symbols = cs_predef_symbols}
				<=< adjust_predef_symbol PD_AndOp mod_index STE_DclFunction
				<=< adjust_predef_symbol PD_OrOp mod_index STE_DclFunction)
		# (pre_mod, cs_predef_symbols) = cs_predef_symbols![PD_StdDynamics]	
		| pre_mod.pds_def == mod_index
			= (class_members, class_instances, fun_types, { cs & cs_predef_symbols = cs_predef_symbols}
				<=< adjust_predef_symbol PD_TypeObjectType		mod_index STE_Type
				<=< adjust_predef_symbol PD_TypeConsSymbol		mod_index STE_Constructor
				<=< adjust_predef_symbol PD_variablePlaceholder mod_index STE_Constructor
				<=< adjust_predef_symbol PD_unify				mod_index STE_DclFunction
				<=< adjust_predef_symbol PD_coerce				mod_index STE_DclFunction
				<=< adjust_predef_symbol PD_undo_indirections	mod_index STE_DclFunction
// MV ...
				<=< adjust_predef_symbol PD_DynamicTemp			mod_index STE_Type
				<=< adjust_predef_symbol PD_DynamicType			mod_index (STE_Field unused)
				<=< adjust_predef_symbol PD_DynamicValue		mod_index (STE_Field unused))

// ... MV
			= (class_members, class_instances, fun_types, { cs & cs_predef_symbols = cs_predef_symbols})
	where
// MV ...
		unused
			= { id_name = "unused", id_info = nilPtr }
// ... MV
					
		adjust_predef_symbols next_symb last_symb mod_index symb_kind cs=:{cs_predef_symbols, cs_symbol_table, cs_error} 
			| next_symb > last_symb
				= cs
				= cs
					<=< adjust_predef_symbol next_symb mod_index symb_kind
					<=< adjust_predef_symbols (inc next_symb) last_symb mod_index symb_kind
			
		adjust_predef_symbol predef_index mod_index symb_kind cs=:{cs_predef_symbols,cs_symbol_table,cs_error}
			# (pre_symb, cs_predef_symbols) = cs_predef_symbols![predef_index]
			# pre_id = pre_symb.pds_ident
			#! pre_index = determine_index_of_symbol (sreadPtr pre_id.id_info cs_symbol_table) symb_kind
			| pre_index <> NoIndex
				= { cs & cs_predef_symbols = {cs_predef_symbols & [predef_index] = { pre_symb & pds_def = pre_index, pds_module = mod_index }}}
				= { cs & cs_predef_symbols = cs_predef_symbols, cs_error = checkError pre_id " function not defined" cs_error }
		where
			determine_index_of_symbol {ste_kind, ste_index} symb_kind
				| ste_kind == symb_kind
					= ste_index
					= NoIndex
		
	count_members :: !Index !{# ClassInstance} !{# ClassDef} !{# DclModule} -> Int
	count_members mod_index com_instance_defs com_class_defs modules
		# (sum, _, _)
				= foldlArraySt (count_members_of_instance mod_index) com_instance_defs (0, com_class_defs, modules)
		= sum

	count_members_of_instance mod_index {ins_class} (sum, com_class_defs, modules)
		# ({class_members}, com_class_defs, modules)
				= getClassDef ins_class mod_index com_class_defs modules
	 	= (size class_members + sum, com_class_defs, modules)


NewEntry symbol_table symb_ptr def_kind def_index level previous :==
	 symbol_table <:= (symb_ptr,{  ste_kind = def_kind, ste_index = def_index, ste_def_level = level, ste_previous = previous })
	
file_and_status {ea_file,ea_ok}
	= (ea_file, ea_ok)

instance <<< FunCall
where
	(<<<) file {fc_index} = file <<< fc_index

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

array_to_list a = [el\\el<-:a]

Ste_Empty :== STE_Empty

dummy_decl
	=: { dcl_ident = { id_name = "", id_info = nilPtr }, dcl_pos = NoPos, dcl_kind = STE_Empty, dcl_index = cUndef }

possibly_write_expl_imports_of_main_dcl_mod_to_file imports_ikh dcl_modules cs
	| switch_port_to_new_syntax False True
		= abort "possibly_write_expl_imports_of_main_dcl_mod_to_file is only used for portToNewSyntax"
	#! x_main_dcl_module_n
			= cs.cs_x.x_main_dcl_module_n
	= case ikhSearch x_main_dcl_module_n imports_ikh of
		No
			// the main dcl module is not part of the currently checked module component
			-> (dcl_modules, cs)
		Yes {si_explicit}
			-> writeExplImportsToFile "dcl.txt" si_explicit dcl_modules cs

