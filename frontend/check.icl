implementation module check

import StdEnv

import syntax, typesupport, parse, checksupport, utilities, checktypes, transform, predef//, RWSDebug
import explicitimports, comparedefimp

cPredefinedModuleIndex 	:== 1

isMainModule :: ModuleKind -> Bool
isMainModule MK_Main	= True
isMainModule _ 			= False

convertIndex :: !Index !Index !(Optional ConversionTable) -> !Index
convertIndex index table_index (Yes tables)
	= tables.[table_index].[index]
convertIndex index table_index No
	= index
	
getPredefinedGlobalSymbol :: !Index !Index !STE_Kind !Int !*CheckState -> (!Global DefinedSymbol, !*CheckState)
getPredefinedGlobalSymbol symb_index module_index req_ste_kind arity cs=:{cs_predef_symbols,cs_symbol_table}
	# (pre_def_mod, cs_predef_symbols)	= cs_predef_symbols![module_index]
	# mod_id							= pre_def_mod.pds_ident
	# (mod_entry, cs_symbol_table)		= readPtr mod_id.id_info cs_symbol_table
	| mod_entry.ste_kind == STE_ClosedModule
		# (glob_object, cs) = get_predefined_symbol symb_index req_ste_kind arity mod_entry.ste_index
										{ cs & cs_predef_symbols = cs_predef_symbols, cs_symbol_table = cs_symbol_table}
		= ({ glob_object = glob_object, glob_module = mod_entry.ste_index }, cs)
		= ({ glob_object = { ds_ident = { id_name = "** ERRONEOUS **", id_info = nilPtr }, ds_index = NoIndex, ds_arity = arity }, glob_module = NoIndex},
				  		{ cs & cs_error = checkError mod_id "not imported" cs.cs_error, cs_predef_symbols = cs_predef_symbols, cs_symbol_table = cs_symbol_table })
where
	get_predefined_symbol :: !Index !STE_Kind !Int !Index !*CheckState -> (!DefinedSymbol,!*CheckState)
	get_predefined_symbol symb_index req_ste_kind arity mod_index cs=:{cs_predef_symbols,cs_symbol_table,cs_error}
		# (pre_def_symb, cs_predef_symbols)	= cs_predef_symbols![symb_index]
		  symb_id							= pre_def_symb.pds_ident
		  (symb_entry, cs_symbol_table) 	= readPtr symb_id.id_info cs_symbol_table
		  cs = { cs & cs_predef_symbols = cs_predef_symbols, cs_symbol_table = cs_symbol_table }
		| symb_entry.ste_kind == req_ste_kind
			= ({ ds_ident = symb_id, ds_index = symb_entry.ste_index, ds_arity = arity }, cs)
			= case symb_entry.ste_kind of
				STE_Imported kind module_index
					| mod_index == module_index && kind == req_ste_kind
						-> ({ ds_ident = symb_id, ds_index = symb_entry.ste_index, ds_arity = arity }, cs)
				_
					-> ({ ds_ident = symb_id, ds_index = NoIndex, ds_arity = arity }, { cs & cs_error = checkError symb_id "undefined" cs.cs_error })
		
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
				# (ins_type, ins_specials, is_type_defs, is_class_defs, is_modules, type_heaps, cs) = checkInstanceType module_index ins_type ins_specials
						is.is_type_defs is.is_class_defs is.is_modules type_heaps cs
				  ins_class = { glob_object = { class_name & ds_index = class_index }, glob_module = class_mod_index}
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
		= (NotFound, cIclModIndex, abort "no class definition", class_defs, modules)
	
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

determineTypesOfInstances :: !Index !Index !*CommonDefs !*{#DclModule} !*TypeHeaps !*VarHeap !*CheckState
	-> (![FunType], !Index, ![ClassInstance], !*CommonDefs, !*{#DclModule}, !*TypeHeaps, !*VarHeap, !*CheckState)
determineTypesOfInstances first_memb_inst_index mod_index dcl_common=:{com_instance_defs,com_class_defs,com_member_defs}
		modules type_heaps var_heap cs=:{cs_error}
	| cs_error.ea_ok
		#! nr_of_class_instances = size com_instance_defs
		# (memb_inst_defs, next_mem_inst_index, all_class_specials, com_class_defs, com_member_defs, modules, com_instance_defs, type_heaps, var_heap, cs_error)
				= determine_types_of_instances 0 nr_of_class_instances first_memb_inst_index mod_index [] com_class_defs com_member_defs
						modules com_instance_defs type_heaps var_heap cs_error
		= (memb_inst_defs, next_mem_inst_index, all_class_specials,
				{ dcl_common & com_instance_defs = com_instance_defs,com_class_defs = com_class_defs, com_member_defs = com_member_defs },
					 modules, type_heaps, var_heap, { cs & cs_error = cs_error })
		= ([], first_memb_inst_index, [], dcl_common, modules, type_heaps, var_heap, cs)
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

/*
retrieveSelectorIndexes mod_index {ste_kind = STE_Selector selector_list, ste_index, ste_previous }
	# imported_selectors = retrieveSelectorIndexes mod_index ste_previous
	= mapAppend (\ sel -> { sel & glob_module = mod_index }) selector_list [{glob_module = mod_index, glob_object = ste_index } : imported_selectors ]
retrieveSelectorIndexes mod_index {ste_kind = STE_Imported (STE_Selector selector_list) dcl_mod_index, ste_index }
	= [ { glob_object = ste_index, glob_module = dcl_mod_index } : selector_list ]
retrieveSelectorIndexes mod_index off_kind
	= []
*/

retrieveSelectorIndexes mod_index {ste_kind = STE_Selector selector_list, ste_index, ste_previous }
	= map (adjust_mod_index mod_index) selector_list
where
	adjust_mod_index mod_index selector=:{glob_module}
		| glob_module == NoIndex
			= { selector & glob_module = mod_index }
			= selector
retrieveSelectorIndexes mod_index off_kind
	= []

checkFields :: !Index ![FieldAssignment] !(Optional Ident) !u:ExpressionInfo !*CheckState
	-> (!Optional ((Global DefinedSymbol), Index, [Bind ParsedExpr (Global FieldSymbol)]), !u:ExpressionInfo, !*CheckState)
checkFields mod_index field_ass opt_type e_info=:{ef_selector_defs,ef_type_defs,ef_modules} cs
	# (ok, field_ass, cs) = check_fields field_ass cs
	| ok
		# (opt_type_def, ef_selector_defs, ef_type_defs, ef_modules, cs)
				= determine_record_type mod_index opt_type field_ass ef_selector_defs ef_type_defs ef_modules cs
		  e_info = { e_info & ef_selector_defs = ef_selector_defs, ef_type_defs = ef_type_defs, ef_modules = ef_modules}
		= case opt_type_def of
			Yes ({td_index,td_rhs = RecordType {rt_constructor,rt_fields}}, type_mod_index)
				# (field_exprs, cs_error) = check_and_rearrange_fields type_mod_index 0 rt_fields field_ass cs.cs_error
				-> (Yes ({ glob_object = rt_constructor, glob_module = type_mod_index }, td_index, field_exprs), e_info, { cs & cs_error = cs_error })
			No
				-> (No, e_info, cs)
		= (No, e_info, cs)
where

	check_fields [ bind=:{bind_dst} : field_ass ] cs=:{cs_symbol_table,cs_error}
		# (entry, cs_symbol_table) = readPtr bind_dst.id_info cs_symbol_table
		# fields = retrieveSelectorIndexes mod_index entry 
		| isEmpty fields
			= (False, [], { cs & cs_symbol_table = cs_symbol_table, cs_error = checkError bind_dst "not defined as a record field" cs_error })
			# (ok, field_ass, cs) = check_fields field_ass { cs & cs_symbol_table = cs_symbol_table }
			= (ok, [{bind & bind_dst = (bind_dst, fields)} : field_ass], cs)
	check_fields [] cs
		= (True, [], cs)

	try_to_get_unique_field []
		= No
	try_to_get_unique_field [ {bind_dst = (field_id, [field])} : fields ]
		= Yes field
	try_to_get_unique_field [ _ : fields ]
		= try_to_get_unique_field fields
	
	determine_record_type mod_index (Yes type_id=:{id_info}) _ selector_defs type_defs modules cs=:{cs_symbol_table, cs_error}
		# (entry, cs_symbol_table) = readPtr id_info cs_symbol_table
		# (type_index, type_mod_index) = retrieveGlobalDefinition entry STE_Type mod_index
		| type_index <> NotFound
			| mod_index == type_mod_index
			 	# (type_def, type_defs) = type_defs![type_index]
			 	= (Yes (type_def, type_mod_index), selector_defs, type_defs, modules, { cs & cs_symbol_table = cs_symbol_table })
				# (type_def, modules) = modules![type_mod_index].dcl_common.com_type_defs.[type_index]
				= (Yes (type_def, type_mod_index), selector_defs, type_defs, modules, { cs & cs_symbol_table = cs_symbol_table })
			= (No, selector_defs, type_defs, modules, { cs & cs_error = checkError type_id " not defined" cs_error, cs_symbol_table = cs_symbol_table})
	determine_record_type mod_index No fields selector_defs type_defs modules cs=:{cs_error}
		# succ = try_to_get_unique_field fields
		= case succ of
			Yes {glob_module, glob_object}
				| glob_module == mod_index
					# (selector_def, selector_defs) = selector_defs![glob_object]
					  (type_def, type_defs) = type_defs![selector_def.sd_type_index]
					-> (Yes (type_def, glob_module), selector_defs, type_defs, modules, cs)
					# ({dcl_common={com_selector_defs,com_type_defs}}, modules) = modules![glob_module]
					# selector_def = com_selector_defs.[glob_object]
					  type_def = com_type_defs.[selector_def.sd_type_index]
					-> (Yes (type_def,glob_module), selector_defs, type_defs, modules, cs)
			No
				-> (No, selector_defs, type_defs, modules, { cs & cs_error = checkError "" " could not determine the type of this record" cs.cs_error })
			

	check_and_rearrange_fields mod_index field_index fields field_ass cs_error
		| field_index < size fields
			# (field_expr, field_ass) = look_up_field mod_index fields.[field_index] field_ass
		 	  (field_exprs, cs_error) = check_and_rearrange_fields mod_index (inc field_index) fields field_ass cs_error
			= ([field_expr : field_exprs], cs_error)
			| isEmpty field_ass
				= ([], cs_error)
				= ([], foldSt field_error field_ass cs_error)

	where			
		look_up_field mod_index field []
			= ({bind_src = PE_WildCard,  bind_dst = { glob_object = field, glob_module = mod_index }}, [])
		look_up_field mod_index field=:{fs_index} [ass=:{bind_src, bind_dst = (_, fields)} : field_ass]
			| field_list_contains_field mod_index fs_index fields
				= ({bind_src = bind_src, bind_dst = { glob_module = mod_index, glob_object = field}}, field_ass)
				# (field_expr, field_ass) = look_up_field mod_index field field_ass
				= (field_expr, [ass : field_ass])

		field_list_contains_field mod_index fs_index []
			= False
		field_list_contains_field mod_index fs_index [{glob_object,glob_module} : fields]
			= mod_index == glob_module && fs_index == glob_object || field_list_contains_field mod_index fs_index fields

		field_error {bind_dst=(field_id,_)} error
			= checkError field_id " field is either multiply used or not a part of this record" error

::	ExpressionInfo =
	{	ef_type_defs		:: !.{# CheckedTypeDef}
	,	ef_selector_defs	:: !.{# SelectorDef}
	,	ef_cons_defs		:: !.{# ConsDef}
	,	ef_member_defs		:: !.{# MemberDef}
	,	ef_class_defs		:: !.{# ClassDef}
	,	ef_modules			:: !.{# DclModule}
	,	ef_is_macro_fun		:: !Bool
	}

::	ExpressionState =
	{	es_expr_heap	:: !.ExpressionHeap
	,	es_var_heap			:: !.VarHeap
	,	es_type_heaps		:: !.TypeHeaps
	,	es_calls			:: ![FunCall]
	,	es_dynamics			:: ![ExprInfoPtr]
	,	es_fun_defs			:: !.{# FunDef}
	}
	
::	ExpressionInput =
	{	ei_expr_level	:: !Level
	,	ei_fun_index	:: !Index
	,	ei_fun_level	:: !Level
	,	ei_mod_index	:: !Index
//	,	ei_fun_kind		:: !FunKind
	}


cIsInExpressionList		:== True
cIsNotInExpressionList	:== False


::	UnfoldMacroState =
	{	ums_var_heap	:: !.VarHeap
	,	ums_modules		:: !.{# DclModule}
	,	ums_cons_defs	:: !.{# ConsDef}
	,	ums_error		:: !.ErrorAdmin
	}

unfoldPatternMacro mod_index macro_index macro_args opt_var ps=:{ps_var_heap, ps_fun_defs} modules cons_defs error
	# (macro, ps_fun_defs) = ps_fun_defs![macro_index]
	= case macro.fun_body of
		TransformedBody {tb_args,tb_rhs}
			| no_sharing tb_args
				# ums = { ums_var_heap = fold2St bind_var tb_args macro_args ps_var_heap, ums_modules = modules, ums_cons_defs = cons_defs, ums_error = error }
				  (pattern, {ums_var_heap,ums_modules,ums_cons_defs,ums_error}) = unfold_pattern_macro mod_index macro.fun_symb opt_var tb_rhs ums
				-> (pattern, { ps_fun_defs = ps_fun_defs, ps_var_heap = ums_var_heap}, ums_modules, ums_cons_defs, ums_error)
				-> (AP_Empty macro.fun_symb, { ps_fun_defs = ps_fun_defs, ps_var_heap = ps_var_heap},
						modules, cons_defs, checkError macro.fun_symb " sharing not allowed" error)
		_
			-> (AP_Empty macro.fun_symb, { ps_fun_defs = ps_fun_defs, ps_var_heap = ps_var_heap},
					modules, cons_defs, checkError macro.fun_symb " illegal macro in pattern" error)
	
where
	no_sharing [{fv_count} : args]
		= fv_count <= 1 && no_sharing args
	no_sharing []
		= True
	
	bind_var {fv_info_ptr} pattern ps_var_heap
		= ps_var_heap <:= (fv_info_ptr, VI_Pattern pattern)

	unfold_pattern_macro mod_index macro_ident _ (Var {var_name,var_info_ptr}) ums=:{ums_var_heap}
		# (VI_Pattern pattern, ums_var_heap) = readPtr var_info_ptr ums_var_heap
		= (pattern, { ums & ums_var_heap = ums_var_heap})
	unfold_pattern_macro mod_index macro_ident opt_var (App {app_symb,app_args}) ums
		= unfold_application  mod_index macro_ident opt_var app_symb app_args ums
	where
		unfold_application  mod_index macro_ident opt_var {symb_kind=SK_Constructor {glob_module,glob_object},symb_name,symb_arity} args 
										ums=:{ums_cons_defs, ums_modules,ums_error}
				# (cons_def, cons_index, ums_cons_defs, ums_modules) = get_cons_def mod_index glob_module glob_object ums_cons_defs ums_modules
				| cons_def.cons_type.st_arity == symb_arity
					# (patterns, ums) = mapSt (unfold_pattern_macro mod_index macro_ident No) app_args { ums & ums_cons_defs = ums_cons_defs, ums_modules = ums_modules }
					  cons_symbol = { glob_object = MakeDefinedSymbol symb_name cons_index symb_arity, glob_module = glob_module }	
					= (AP_Algebraic cons_symbol cons_def.cons_type_index patterns opt_var, ums)	
					= (AP_Empty cons_def.cons_symb, { ums & ums_cons_defs = ums_cons_defs, ums_modules = ums_modules,
							ums_error = checkError cons_def.cons_symb " missing argument(s)" ums_error })
		get_cons_def mod_index cons_mod cons_index cons_defs modules
			| mod_index == cons_mod
				# (cons_def, cons_defs) = cons_defs![cons_index]
				= (cons_def, cons_index, cons_defs, modules)
				# ({dcl_common,dcl_conversions}, modules) = modules![cons_mod]
				  cons_def = dcl_common.com_cons_defs.[cons_index]
				= (cons_def, convertIndex cons_index (toInt STE_Constructor) dcl_conversions, cons_defs, modules)

		get_cons_def mod_index cons_mod cons_index cons_defs modules
			# ({dcl_common,dcl_conversions}, modules) = modules![cons_mod]
			  cons_def = dcl_common.com_cons_defs.[cons_index]
			= (cons_def, convertIndex cons_index (toInt STE_Constructor) dcl_conversions, cons_defs, modules)

	unfold_pattern_macro mod_index macro_ident opt_var (BasicExpr bv bt) ums
		= (AP_Basic bv opt_var, ums)
	unfold_pattern_macro mod_index macro_ident opt_var expr ums=:{ums_error}
		= (AP_Empty macro_ident, { ums & ums_error = checkError macro_ident " illegal rhs for a pattern macro" ums_error })
	
	
			
checkPatternVariable :: !Level !SymbolTableEntry !Ident !VarInfoPtr !*CheckState -> !*CheckState
checkPatternVariable def_level entry=:{ste_def_level,ste_kind} ident=:{id_info} var_info cs=:{cs_symbol_table,cs_error}
	| ste_kind == STE_Empty || def_level > ste_def_level
		# entry = {ste_kind = STE_Variable var_info, ste_index = NoIndex, ste_def_level = def_level, ste_previous = entry }
		= { cs & cs_symbol_table = cs_symbol_table <:= (id_info,entry)}
		= { cs & cs_error = checkError ident "(pattern variable) already defined" cs_error }

checkPatternConstructor :: !Index !Bool !SymbolTableEntry !Ident !(Optional (Bind Ident VarInfoPtr)) !*PatternState !*ExpressionInfo !*CheckState
	-> (!AuxiliaryPattern, !*PatternState, !*ExpressionInfo, !*CheckState);
checkPatternConstructor _ _ {ste_kind = STE_Empty} ident _  ps e_info cs=:{cs_error}
	= (AP_Empty ident, ps, e_info, { cs & cs_error = checkError ident " not defined" cs_error })
checkPatternConstructor mod_index is_expr_list {ste_kind = STE_FunctionOrMacro _,ste_index} ident opt_var  ps=:{ps_fun_defs} e_info cs=:{cs_error}
	# ({fun_symb,fun_arity,fun_kind,fun_priority},ps_fun_defs) = ps_fun_defs![ste_index]
	  ps = { ps & ps_fun_defs = ps_fun_defs }
	| fun_kind == FK_Macro
		| is_expr_list
			# macro_symbol = { glob_object = MakeDefinedSymbol fun_symb ste_index fun_arity, glob_module = cIclModIndex }
	 		= (AP_Constant APK_Macro macro_symbol fun_priority, ps, e_info, cs)
		| fun_arity == 0
			# (pattern, ps, ef_modules, ef_cons_defs, cs_error)
					= unfoldPatternMacro mod_index ste_index [] opt_var ps e_info.ef_modules e_info.ef_cons_defs cs_error
			= (pattern, ps, { e_info & ef_modules = ef_modules, ef_cons_defs = ef_cons_defs }, { cs & cs_error = cs_error })
			= (AP_Empty ident, ps, e_info, { cs & cs_error = checkError ident " not defined" cs_error })
		= (AP_Empty ident, ps, e_info, { cs & cs_error = checkError fun_symb " not allowed in a pattern" cs_error })
checkPatternConstructor mod_index is_expr_list {ste_index, ste_kind} cons_symb opt_var ps
		e_info=:{ef_cons_defs,ef_modules} cs=:{cs_error}
	# (cons_index, cons_module, cons_arity, cons_priority, cons_type_index, ef_cons_defs, ef_modules, cs_error)
			= determine_pattern_symbol mod_index ste_index ste_kind cons_symb.id_name ef_cons_defs ef_modules cs_error
	  e_info = { e_info & ef_cons_defs = ef_cons_defs, ef_modules = ef_modules }
	  cons_symbol = { glob_object = MakeDefinedSymbol cons_symb cons_index cons_arity, glob_module = cons_module }
   	| is_expr_list
		= (AP_Constant (APK_Constructor cons_type_index) cons_symbol cons_priority, ps, e_info, { cs & cs_error = cs_error })
	| cons_arity == 0
		= (AP_Algebraic cons_symbol cons_type_index [] opt_var, ps, e_info, { cs & cs_error = cs_error })
		= (AP_Algebraic cons_symbol cons_type_index [] opt_var, ps, e_info, { cs & cs_error = checkError cons_symb " constructor arguments are missing" cs_error })
where
	determine_pattern_symbol mod_index id_index STE_Constructor id_name cons_defs modules error
		# ({cons_type={st_arity},cons_priority, cons_type_index}, cons_defs) = cons_defs![id_index]
		= (id_index, mod_index, st_arity, cons_priority, cons_type_index, cons_defs, modules, error)
	determine_pattern_symbol mod_index id_index (STE_Imported STE_Constructor import_mod_index) id_name cons_defs modules error
		# ({dcl_common,dcl_conversions},modules) = modules![import_mod_index]
		  {cons_type={st_arity},cons_priority, cons_type_index} = dcl_common.com_cons_defs.[id_index]
		  id_index = convertIndex id_index (toInt STE_Constructor) dcl_conversions
		= (id_index, import_mod_index, st_arity, cons_priority, cons_type_index, cons_defs, modules, error)
	determine_pattern_symbol mod_index id_index id_kind id_name cons_defs modules error
		= (id_index, NoIndex, 0, NoPrio, NoIndex, cons_defs, modules, checkError id_name " constructor expected" error)


checkIdentPattern :: !Bool !Ident !(Optional (Bind Ident VarInfoPtr)) !PatternInput !(![Ident], ![ArrayPattern]) !*PatternState !*ExpressionInfo !*CheckState
	-> (!AuxiliaryPattern, !(![Ident], ![ArrayPattern]), !*PatternState, !*ExpressionInfo, !*CheckState)
checkIdentPattern is_expr_list id=:{id_name,id_info} opt_var {pi_def_level, pi_mod_index} accus=:(var_env, array_patterns)
					ps e_info cs=:{cs_symbol_table}
	# (entry, cs_symbol_table) = readPtr id_info cs_symbol_table
	| isLowerCaseName id_name
		# (new_info_ptr, ps_var_heap) = newPtr VI_Empty ps.ps_var_heap
		  cs = checkPatternVariable pi_def_level entry id new_info_ptr { cs & cs_symbol_table = cs_symbol_table }
		= (AP_Variable id new_info_ptr opt_var, ([ id : var_env ], array_patterns), { ps & ps_var_heap = ps_var_heap}, e_info, cs)
		# (pattern, ps, e_info, cs) = checkPatternConstructor pi_mod_index is_expr_list entry id opt_var ps e_info { cs & cs_symbol_table = cs_symbol_table }
		= (pattern, accus, ps, e_info, cs)

::	PatternState =
	{	ps_var_heap :: !.VarHeap
	,	ps_fun_defs :: !.{# FunDef}
	}

::	PatternInput =
	{	pi_def_level		:: !Int
	,	pi_mod_index		:: !Index
	,	pi_is_node_pattern	:: !Bool
	}
	
::	ArrayPattern =
	{	ap_opt_var		:: !Optional (Bind Ident VarInfoPtr)
	,	ap_array_var	:: !FreeVar
	,	ap_selections	:: ![Bind FreeVar [ParsedExpr]]
	}

buildPattern mod_index (APK_Constructor type_index) cons_symb args opt_var ps e_info cs
	= (AP_Algebraic cons_symb type_index args opt_var, ps, e_info, cs)
buildPattern mod_index APK_Macro {glob_object} args opt_var ps e_info=:{ef_modules,ef_cons_defs} cs=:{cs_error}
	# (pattern, ps, ef_modules, ef_cons_defs, cs_error)
			= unfoldPatternMacro mod_index glob_object.ds_index args opt_var ps ef_modules ef_cons_defs cs_error
	= (pattern, ps, { e_info & ef_modules = ef_modules, ef_cons_defs = ef_cons_defs }, { cs & cs_error = cs_error })

checkPattern :: !ParsedExpr !(Optional (Bind Ident VarInfoPtr)) !PatternInput !(![Ident], ![ArrayPattern]) !*PatternState !*ExpressionInfo !*CheckState
									-> (!AuxiliaryPattern, !(![Ident], ![ArrayPattern]), !*PatternState, !*ExpressionInfo, !*CheckState)
checkPattern (PE_List [exp]) opt_var p_input accus ps e_info cs=:{cs_symbol_table}
	= case exp of
		PE_Ident ident
			-> checkIdentPattern cIsNotInExpressionList ident opt_var p_input accus ps e_info cs
		_
			-> checkPattern exp opt_var p_input accus ps e_info cs

checkPattern (PE_List [exp1, exp2 : exps]) opt_var p_input accus ps e_info cs
	# (exp_pat, accus, ps, e_info, cs) = check_pattern exp1 p_input accus ps e_info cs
	= check_patterns [exp_pat] exp2 exps opt_var p_input accus ps e_info cs
	where
		check_patterns left middle [] opt_var p_input=:{pi_mod_index} accus ps e_info cs
			# (mid_pat, accus, ps, e_info, cs) = checkPattern middle No p_input accus ps e_info cs
			  (pat, ps, e_info, cs) = combine_patterns pi_mod_index opt_var [mid_pat : left] [] 0 ps e_info cs
			= (pat, accus, ps, e_info, cs)
		check_patterns left middle [right:rest] opt_var p_input=:{pi_mod_index} accus ps e_info cs
			# (mid_pat, accus, ps, e_info, cs) = check_pattern middle p_input accus ps e_info cs
			= case mid_pat of
				AP_Constant kind constant=:{glob_object={ds_arity,ds_ident}} prio
					| ds_arity == 0
						# (pattern, ps, e_info, cs) = buildPattern pi_mod_index kind constant [] No ps e_info cs
						-> check_patterns [pattern: left] right rest opt_var p_input accus ps e_info cs
					| is_infix_constructor prio
						# (left_arg, ps, e_info, cs) = combine_patterns pi_mod_index No left [] 0 ps e_info cs
						  (right_pat, accus, ps, e_info, cs) = check_pattern right p_input accus ps e_info cs
						-> check_infix_pattern [] left_arg kind constant prio [right_pat] rest
									opt_var p_input accus ps e_info cs
						-> (AP_Empty ds_ident, accus, ps, e_info,
								{ cs & cs_error = checkError ds_ident "arguments of constructor are missing" cs.cs_error })
				_
					-> check_patterns [mid_pat : left] right rest opt_var p_input accus ps e_info cs

		check_pattern (PE_Ident id) p_input accus ps e_info cs
			= checkIdentPattern cIsInExpressionList id No p_input accus ps e_info cs
		check_pattern expr p_input accus ps e_info cs
			= checkPattern expr No p_input accus ps e_info cs
		
	 	check_infix_pattern left_args left kind cons prio middle [] opt_var p_input=:{pi_mod_index} accus ps e_info cs
			# (middle_pat, ps, e_info, cs) = combine_patterns pi_mod_index No middle [] 0 ps e_info cs
			  (pattern, ps, e_info, cs) = buildPattern pi_mod_index kind cons [left,middle_pat] opt_var ps e_info cs
			  (pattern, ps, e_info, cs) = build_final_pattern pi_mod_index left_args pattern ps e_info cs
			= (pattern, accus, ps, e_info, cs)
	 	check_infix_pattern left_args left kind cons prio middle [right] opt_var  p_input=:{pi_mod_index} accus ps e_info cs
			# (right_pat, accus, ps, e_info, cs) = checkPattern right No p_input accus ps e_info cs
			  (right_arg, ps, e_info, cs) = combine_patterns pi_mod_index No [right_pat : middle] [] 0 ps e_info cs
			  (pattern, ps, e_info, cs) = buildPattern pi_mod_index kind cons [left,right_arg] opt_var ps e_info cs
			  (pattern, ps, e_info, cs) = build_final_pattern pi_mod_index left_args pattern ps e_info cs
			= (pattern, accus, ps, e_info, cs)
	 	check_infix_pattern left_args left kind1 cons1 prio1 middle [inf_cons, arg : rest] opt_var p_input=:{pi_mod_index} accus ps e_info cs
			# (inf_cons_pat, accus, ps, e_info, cs) = check_pattern inf_cons p_input accus ps e_info cs
			= case inf_cons_pat of
				AP_Constant kind2 cons2=:{glob_object={ds_ident,ds_arity}} prio2
					| ds_arity == 0
						# (middle_pat, ps, e_info, cs) = combine_patterns pi_mod_index No middle [] 0 ps e_info cs
						  (pattern2, ps, e_info, cs) = buildPattern pi_mod_index kind2 cons2 [] No ps e_info cs
						  (pattern1, ps, e_info, cs) = buildPattern pi_mod_index kind1 cons1 [left,middle_pat] No ps e_info cs
						  (pattern1, ps, e_info, cs) = build_final_pattern pi_mod_index left_args pattern1 ps e_info cs
						-> check_patterns [pattern2,pattern1] arg rest opt_var p_input accus ps e_info cs
					| is_infix_constructor prio2
						# optional_prio = determinePriority prio1 prio2
						-> case optional_prio of
							Yes priority
								# (arg_pat, accus, ps, e_info, cs) = check_pattern arg p_input accus ps e_info cs
								| priority
									# (middle_pat, ps, e_info, cs) = combine_patterns pi_mod_index No middle [] 0 ps e_info cs
								      (pattern, ps, e_info, cs) = buildPattern pi_mod_index kind1 cons1 [left,middle_pat] No ps e_info cs
								      (left_args, pattern, ps, e_info, cs) = build_left_pattern pi_mod_index left_args prio2 pattern ps e_info cs
									-> check_infix_pattern left_args pattern kind2 cons2 prio2 [arg_pat] rest opt_var p_input accus ps e_info cs 
									# (middle_pat, ps, e_info, cs) = combine_patterns pi_mod_index No middle [] 0 ps e_info cs
									-> check_infix_pattern [(kind1, cons1, prio1, left) : left_args]
									  				middle_pat kind2 cons2 prio2 [arg_pat] rest No p_input accus ps e_info cs
							No
								-> (AP_Empty ds_ident, accus, ps, e_info, { cs & cs_error = checkError ds_ident "conflicting priorities" cs.cs_error })
						-> (AP_Empty ds_ident, accus, ps, e_info, { cs & cs_error = checkError ds_ident "arguments of constructor are missing" cs.cs_error })
				_
					-> check_infix_pattern left_args left kind1 cons1 prio1 [inf_cons_pat : middle] [arg : rest] opt_var p_input accus ps e_info cs 

		is_infix_constructor (Prio _ _) = True
		is_infix_constructor _ = False

		build_left_pattern mod_index [] _ result_pattern ps e_info cs
			= ([], result_pattern, ps, e_info, cs)		
		build_left_pattern mod_index la=:[(kind, cons, priol, left) : left_args] prior result_pattern ps e_info cs
			# optional_prio = determinePriority priol prior
			= case optional_prio of
				Yes priority
					| priority
						# (result_pattern,  ps, e_info, cs) = buildPattern mod_index kind cons [left,result_pattern] No ps e_info cs
						-> build_left_pattern mod_index left_args prior result_pattern ps e_info cs
						-> (la, result_pattern,  ps, e_info, cs)
				No
					-> (la, result_pattern,  ps, e_info,{ cs & cs_error = checkError cons.glob_object.ds_ident "conflicting priorities" cs.cs_error })

		build_final_pattern mod_index [] result_pattern ps e_info cs
			= (result_pattern,  ps, e_info, cs)		
		build_final_pattern mod_index [(kind, cons, priol, left) : left_appls] result_pattern ps e_info cs
			# (result_pattern, ps, e_info, cs) = buildPattern mod_index kind cons [left,result_pattern] No ps e_info cs
			= build_final_pattern mod_index left_appls result_pattern ps e_info cs

		combine_patterns mod_index opt_var [first_expr] args nr_of_args ps e_info cs
			= case first_expr of
				AP_Constant kind constant=:{glob_object={ds_ident,ds_arity}} _
					| ds_arity == nr_of_args
						# (pattern, ps, e_info, cs) = buildPattern mod_index kind constant args opt_var ps e_info cs
						-> (pattern, ps, e_info, cs)
						-> (AP_Empty ds_ident, ps, e_info, { cs & cs_error = checkError ds_ident "used with wrong arity" cs.cs_error})
				_
					| nr_of_args == 0
						-> (first_expr, ps, e_info, cs)
						-> (first_expr, ps, e_info, { cs & cs_error = checkError "<pattern>" "(curried) application not allowed " cs.cs_error })
		combine_patterns mod_index opt_var [rev_arg : rev_args] args arity ps e_info cs
			= combine_patterns mod_index opt_var rev_args [rev_arg : args] (inc arity) ps e_info cs
/*
		combine_optional_variables (Yes var1) (Yes var2) error
			= (Yes var1, checkError var2.bind_dst "pattern already bound" error)
		combine_optional_variables No opt_var error
			= (opt_var, error)
		combine_optional_variables opt_var _ error
			= (opt_var, error)
*/

checkPattern (PE_DynamicPattern pattern type) opt_var p_input accus ps e_info cs
	# (dyn_pat, accus, ps, e_info, cs) = checkPattern pattern No p_input accus ps e_info cs
	= (AP_Dynamic dyn_pat type opt_var, accus, ps, e_info, { cs & cs_needed_modules = cs.cs_needed_modules bitor cNeedStdDynamics })

checkPattern (PE_Basic basic_value) opt_var p_input accus ps e_info cs
	= (AP_Basic basic_value opt_var, accus, ps, e_info, cs)

checkPattern (PE_Tuple tuple_args) opt_var p_input accus ps e_info cs
	# (patterns, arity, accus, ps, e_info, cs) = check_tuple_patterns tuple_args p_input accus ps e_info cs
	  (tuple_symbol, cs) = getPredefinedGlobalSymbol (GetTupleConsIndex arity) PD_PredefinedModule STE_Constructor arity cs
	# ({cons_type_index}, e_info) = e_info!ef_modules.[tuple_symbol.glob_module].dcl_common.com_cons_defs.[tuple_symbol.glob_object.ds_index]
	= (AP_Algebraic tuple_symbol cons_type_index patterns opt_var, accus, ps, e_info, cs)
where
	check_tuple_patterns [] p_input accus ps e_info cs
		= ([], 0, accus, ps, e_info, cs)
	check_tuple_patterns [expr : exprs] p_input accus ps e_info cs
		# (pattern, accus, ps, e_info, cs) = checkPattern expr No p_input accus ps e_info cs
		  (patterns, length, accus, ps, e_info, cs) = check_tuple_patterns exprs p_input accus ps e_info cs
		= ([pattern : patterns], inc length, accus, ps, e_info, cs)
checkPattern (PE_Record record opt_type fields) opt_var p_input=:{pi_mod_index, pi_is_node_pattern} accus=:(var_env, array_patterns) ps e_info cs
	# (opt_record_and_fields, e_info, cs) = checkFields pi_mod_index fields opt_type e_info cs
	= case opt_record_and_fields of
		Yes (record_symbol, type_index, new_fields)
			# (patterns, (var_env, array_patterns, ps, e_info, cs)) = mapSt (check_field_pattern p_input) new_fields (var_env, array_patterns, ps, e_info, cs)
			  (patterns, ps_var_heap) = bind_opt_record_variable opt_var pi_is_node_pattern patterns new_fields ps.ps_var_heap
			-> (AP_Algebraic record_symbol type_index patterns opt_var, (var_env, array_patterns), { ps & ps_var_heap = ps_var_heap }, e_info, cs)
		No
			-> (AP_Empty (hd fields).bind_dst, accus, ps, e_info, cs)
where

	check_field_pattern p_input=:{pi_def_level} {bind_src = PE_Empty, bind_dst = {glob_object={fs_var}}} 
						(var_env, array_patterns, ps, e_info, cs)
		# (entry, cs_symbol_table) = readPtr fs_var.id_info cs.cs_symbol_table
		# (new_info_ptr, ps_var_heap) = newPtr VI_Empty ps.ps_var_heap
		  cs = checkPatternVariable pi_def_level entry fs_var new_info_ptr { cs & cs_symbol_table = cs_symbol_table }
		= (AP_Variable fs_var new_info_ptr No, ([ fs_var : var_env ], array_patterns, { ps & ps_var_heap = ps_var_heap }, e_info, cs))
	check_field_pattern p_input {bind_src = PE_WildCard, bind_dst={glob_object={fs_var}}} (var_env, array_patterns, ps, e_info, cs)
		# (new_info_ptr, ps_var_heap) = newPtr VI_Empty ps.ps_var_heap
		= (AP_WildCard (Yes { bind_src = fs_var, bind_dst = new_info_ptr}), (var_env, array_patterns, { ps & ps_var_heap = ps_var_heap }, e_info, cs))
	check_field_pattern p_input {bind_src,bind_dst} (var_env, array_patterns, ps, e_info, cs)
		# (pattern, (var_env, array_patterns), ps, e_info, cs) = checkPattern bind_src No p_input (var_env, array_patterns) ps e_info cs
		= (pattern, (var_env, array_patterns, ps, e_info, cs))


	add_bound_variable (AP_Algebraic symbol index patterns No) {bind_dst = {glob_object={fs_var}}} ps_var_heap
		# (new_info_ptr, ps_var_heap) = newPtr VI_Empty ps_var_heap
		= (AP_Algebraic symbol index patterns (Yes { bind_src = fs_var, bind_dst = new_info_ptr}), ps_var_heap)
	add_bound_variable (AP_Basic bas_val No) {bind_dst = {glob_object={fs_var}}} ps_var_heap
		# (new_info_ptr, ps_var_heap) = newPtr VI_Empty ps_var_heap
		= (AP_Basic bas_val (Yes { bind_src = fs_var, bind_dst = new_info_ptr}), ps_var_heap)
	add_bound_variable (AP_Dynamic dynamic_pattern dynamic_type No) {bind_dst = {glob_object={fs_var}}} ps_var_heap
		# (new_info_ptr, ps_var_heap) = newPtr VI_Empty ps_var_heap
		= (AP_Dynamic dynamic_pattern dynamic_type (Yes { bind_src = fs_var, bind_dst = new_info_ptr}), ps_var_heap)
	add_bound_variable pattern _ ps_var_heap
		= (pattern, ps_var_heap)

	add_bound_variables [] _ var_heap
		= ([] , var_heap)
	add_bound_variables [ap : aps] [field : fields] var_heap
		# (ap, var_heap) = add_bound_variable ap field var_heap
		  (aps, var_heap) = add_bound_variables aps fields var_heap
		= ([ap : aps], var_heap)

	bind_opt_record_variable (Yes {bind_dst}) False patterns fields var_heap
		# (patterns, var_heap) = add_bound_variables patterns fields var_heap
		= (patterns, var_heap <:= (bind_dst, VI_Record patterns))
	bind_opt_record_variable no is_node_pattern patterns _ var_heap
		= (patterns, var_heap)

checkPattern (PE_ArrayPattern selections) opt_var p_input (var_env, array_patterns) ps e_info cs
	# (var_env, ap_selections, ps_var_heap, cs)
			= foldSt (check_array_selection p_input.pi_def_level) selections (var_env, [], ps.ps_var_heap, cs)
	  array_var_ident = case opt_var of 
	  						Yes {bind_src}
	  							-> bind_src
	  						No
	  							-> { id_name = "_a", id_info = nilPtr }
	  (array_var, ps_var_heap) = allocate_free_var array_var_ident ps_var_heap
	= (AP_Variable array_var_ident array_var.fv_info_ptr No, 
		(var_env, [{ ap_opt_var = opt_var, ap_array_var = array_var, ap_selections = ap_selections } :array_patterns]),
		{ ps & ps_var_heap = ps_var_heap }, e_info, cs)
  where
	check_array_selection def_level bind=:{bind_dst} states
		= check_rhs def_level bind (foldSt check_index_expr bind_dst states)
		
	check_index_expr (PE_Ident {id_name}) states
		| isLowerCaseName id_name
			= states
		// further with next alternative
	check_index_expr (PE_Basic (BVI _)) states
			= states
	check_index_expr _ (var_env, ap_selections, var_heap, cs)
		= (var_env, ap_selections, var_heap, { cs & cs_error = checkError "" "variable or integer constant expected as index expression" cs.cs_error })

	check_rhs def_level {bind_src=PE_Ident ident, bind_dst} (var_env, ap_selections, var_heap, cs)
		| isLowerCaseName ident.id_name
			# (entry,cs_symbol_table) = readPtr ident.id_info cs.cs_symbol_table
			# (rhs_var, var_heap) = allocate_free_var ident var_heap
			  cs = checkPatternVariable def_level entry ident rhs_var.fv_info_ptr { cs & cs_symbol_table = cs_symbol_table }
			= ([ident : var_env], [ { bind_src = rhs_var, bind_dst = bind_dst } : ap_selections], var_heap, cs)
		// further with next alternative
	check_rhs _ _ (var_env, ap_selections, var_heap, cs)
		= (var_env, ap_selections, var_heap, 
			{ cs & cs_error = checkError "" "variable expected on right hand side of array pattern" cs.cs_error })

checkPattern (PE_Bound bind) opt_var p_input accus ps e_info cs
	= checkBoundPattern bind opt_var p_input accus ps e_info cs

checkPattern (PE_Ident id) opt_var p_input accus ps e_info cs
	= checkIdentPattern cIsNotInExpressionList id opt_var p_input accus ps e_info cs
checkPattern PE_WildCard opt_var p_input accus ps e_info cs
	= (AP_WildCard No, accus, ps, e_info, cs)
checkPattern expr opt_var p_input accus ps e_info cs
	= abort "checkPattern: do not know how to handle pattern" ---> expr

checkBoundPattern {bind_src,bind_dst} opt_var p_input (var_env, array_patterns) ps e_info cs=:{cs_symbol_table}
	| isLowerCaseName bind_dst.id_name
		# (entry, cs_symbol_table) = readPtr bind_dst.id_info cs_symbol_table
		# (new_info_ptr, ps_var_heap) = newPtr VI_Empty ps.ps_var_heap
		  cs = checkPatternVariable p_input.pi_def_level entry bind_dst new_info_ptr { cs & cs_symbol_table = cs_symbol_table }
		  ps = { ps & ps_var_heap = ps_var_heap }
		  new_var_env = [ bind_dst : var_env ]
		= case opt_var of
			Yes bind
				-> checkPattern bind_src (Yes { bind_src = bind_dst, bind_dst = new_info_ptr }) p_input (new_var_env, array_patterns) ps
					 	e_info { cs & cs_error = checkError bind.bind_src "pattern may be bound once only" cs.cs_error }
			No
				-> checkPattern bind_src (Yes { bind_src = bind_dst, bind_dst = new_info_ptr }) p_input (new_var_env, array_patterns) ps e_info cs
	= checkPattern bind_src opt_var p_input (var_env, array_patterns) ps e_info { cs & cs_error = checkError bind_dst "variable expected" cs.cs_error }

newFreeVariable :: !FreeVar ![FreeVar] ->(!Bool, ![FreeVar])
newFreeVariable new_var vars=:[free_var=:{fv_def_level,fv_info_ptr}: free_vars]
	| new_var.fv_def_level > fv_def_level
		= (True, [new_var : vars])
	| new_var.fv_def_level == fv_def_level
		| new_var.fv_info_ptr == fv_info_ptr
			= (False, vars)
			#! (free_var_added, free_vars) = newFreeVariable new_var free_vars
			= (free_var_added, [free_var : free_vars])
		#! (free_var_added, free_vars) = newFreeVariable new_var free_vars
		= (free_var_added, [free_var : free_vars])
newFreeVariable new_var []
	= (True, [new_var])


buildTypeCase type_case_dynamic type_case_patterns type_case_default type_case_info_ptr :==
	Case {	case_expr = type_case_dynamic, case_guards = DynamicPatterns type_case_patterns, case_default = type_case_default, 
			case_info_ptr = type_case_info_ptr, case_ident = No }


consOptional (Yes thing) things
	= [ thing : things]
consOptional No things
	= things

buildApplication :: !SymbIdent !Int !Int !Bool ![Expression] !*ExpressionState !*ErrorAdmin -> (!Expression,!*ExpressionState,!*ErrorAdmin)
buildApplication symbol form_arity act_arity is_fun args e_state=:{es_expr_heap} error
	| is_fun
		# (new_info_ptr, es_expr_heap) = newPtr EI_Empty es_expr_heap
		| form_arity < act_arity
			# app = { app_symb = { symbol & symb_arity = form_arity }, app_args = take form_arity args, app_info_ptr = new_info_ptr }
			= (App app @ drop form_arity args, { e_state & es_expr_heap = es_expr_heap }, error)
			# app = { app_symb = { symbol & symb_arity = act_arity }, app_args = take form_arity args, app_info_ptr = new_info_ptr }
			= (App app, { e_state & es_expr_heap = es_expr_heap }, error)
		# app = App { app_symb = { symbol & symb_arity = act_arity }, app_args = args, app_info_ptr = nilPtr }
		| form_arity < act_arity
			= (app, e_state, checkError symbol.symb_name " used with too many arguments" error)
			= (app, e_state, error)

checkIdentExpression :: !Bool ![FreeVar] !Ident !ExpressionInput !*ExpressionState !u:ExpressionInfo !*CheckState
	-> (!Expression, ![FreeVar], !*ExpressionState, !u:ExpressionInfo, !*CheckState)
checkIdentExpression is_expr_list free_vars id=:{id_info} e_input e_state e_info cs=:{cs_symbol_table}
	# (entry, cs_symbol_table) = readPtr id_info cs_symbol_table
	= check_id_expression entry is_expr_list free_vars id e_input e_state e_info { cs & cs_symbol_table = cs_symbol_table }
where
	check_id_expression :: !SymbolTableEntry !Bool ![FreeVar] !Ident !ExpressionInput !*ExpressionState !u:ExpressionInfo !*CheckState
		-> (!Expression, ![FreeVar], !*ExpressionState, !u:ExpressionInfo, !*CheckState)
	check_id_expression {ste_kind = STE_Empty} is_expr_list free_vars id e_input e_state e_info cs=:{cs_error}
		= (EE, free_vars, e_state, e_info, { cs & cs_error = checkError id " undefined" cs_error })
	check_id_expression {ste_kind = STE_Variable info_ptr,ste_def_level} is_expr_list free_vars id e_input=:{ei_fun_level} e_state=:{es_expr_heap} e_info cs
		| ste_def_level < ei_fun_level
			# free_var = { fv_def_level = ste_def_level, fv_name = id, fv_info_ptr = info_ptr, fv_count = 0 }
			  (free_var_added, free_vars) = newFreeVariable free_var free_vars
			= (FreeVar free_var, free_vars, e_state, e_info, cs)
			#! (var_expr_ptr, es_expr_heap) = newPtr EI_Empty es_expr_heap
			= (Var {var_name = id, var_info_ptr = info_ptr, var_expr_ptr = var_expr_ptr}, free_vars,
					{e_state & es_expr_heap = es_expr_heap}, e_info, cs)
	check_id_expression entry is_expr_list free_vars id=:{id_info} e_input e_state e_info cs
		# (symb_kind, arity, priority, is_a_function, e_state, e_info, cs) = determine_info_of_symbol entry id_info e_input e_state e_info cs
		  symbol = { symb_name = id, symb_kind = symb_kind, symb_arity = 0 }
  		| is_expr_list
			= (Constant symbol arity priority is_a_function, free_vars, e_state, e_info, cs)
			# (app_expr, e_state, cs_error) = buildApplication symbol arity 0 is_a_function [] e_state cs.cs_error
			= (app_expr, free_vars, e_state, e_info, { cs & cs_error = cs_error })

	determine_info_of_symbol :: !SymbolTableEntry !SymbolPtr !ExpressionInput !*ExpressionState !u:ExpressionInfo !*CheckState
		-> (!SymbKind, !Int, !Priority, !Bool, !*ExpressionState, !u:ExpressionInfo,!*CheckState)
	determine_info_of_symbol entry=:{ste_kind=STE_FunctionOrMacro calls,ste_index,ste_def_level} symb_info
				e_input=:{ei_fun_index, ei_mod_index} e_state=:{es_fun_defs,es_calls} e_info cs=:{cs_symbol_table}
		# ({fun_symb,fun_arity,fun_kind,fun_priority}, es_fun_defs) = es_fun_defs![ste_index]
		# index = { glob_object = ste_index, glob_module = cIclModIndex }
		| is_called_before ei_fun_index calls
			| fun_kind == FK_Macro
				= (SK_Macro index, fun_arity, fun_priority, cIsAFunction, { e_state & es_fun_defs = es_fun_defs }, e_info, cs)
				= (SK_Function index, fun_arity, fun_priority, cIsAFunction, { e_state & es_fun_defs = es_fun_defs }, e_info, cs)
			# cs = { cs & cs_symbol_table = cs_symbol_table <:= (symb_info, { entry & ste_kind = STE_FunctionOrMacro [ ei_fun_index : calls ]})}
			  e_state = { e_state & es_fun_defs = es_fun_defs, es_calls = [{ fc_index = ste_index, fc_level = ste_def_level} : es_calls ]}
			= (if (fun_kind == FK_Macro) (SK_Macro index) (SK_Function index), fun_arity, fun_priority, cIsAFunction, e_state, e_info, cs)
	where
		is_called_before caller_index []
			= False
		is_called_before caller_index [called_index : calls]
			= caller_index == called_index || is_called_before caller_index calls

	determine_info_of_symbol entry=:{ste_kind=STE_Imported kind mod_index,ste_index} symb_index e_input e_state e_info=:{ef_modules} cs
		# (mod_def, ef_modules) = ef_modules![mod_index]
		# (kind, arity, priotity, is_fun) = ste_kind_to_symbol_kind kind ste_index mod_index mod_def
		= (kind, arity, priotity, is_fun, e_state, { e_info & ef_modules = ef_modules }, cs)
	where
		ste_kind_to_symbol_kind :: !STE_Kind !Index !Index !DclModule -> (!SymbKind, !Int, !Priority, !Bool);
		ste_kind_to_symbol_kind STE_DclFunction def_index mod_index {dcl_functions,dcl_conversions}
			# {ft_type={st_arity},ft_priority} = dcl_functions.[def_index]
			# def_index = convertIndex def_index (toInt STE_DclFunction) dcl_conversions
			= (SK_Function { glob_object = def_index, glob_module = mod_index }, st_arity, ft_priority, cIsAFunction)
		ste_kind_to_symbol_kind STE_Member def_index mod_index {dcl_common={com_member_defs},dcl_conversions}
			# {me_type={st_arity},me_priority} = com_member_defs.[def_index]
			# def_index = convertIndex def_index (toInt STE_Member) dcl_conversions
			= (SK_OverloadedFunction { glob_object = def_index, glob_module = mod_index }, st_arity, me_priority, cIsAFunction)
		ste_kind_to_symbol_kind STE_Constructor def_index mod_index {dcl_common={com_cons_defs},dcl_conversions}
			# {cons_type={st_arity},cons_priority} = com_cons_defs.[def_index]
			# def_index = convertIndex def_index (toInt STE_Constructor) dcl_conversions
			= (SK_Constructor { glob_object = def_index, glob_module = mod_index }, st_arity, cons_priority, cIsNotAFunction)

	determine_info_of_symbol {ste_kind=STE_Member, ste_index} _ e_input=:{ei_mod_index} e_state e_info=:{ef_member_defs} cs
		# ({me_type={st_arity},me_priority}, ef_member_defs) = ef_member_defs![ste_index]
		= (SK_OverloadedFunction { glob_object = ste_index, glob_module = ei_mod_index}, st_arity, me_priority, cIsAFunction,
				e_state, { e_info & ef_member_defs = ef_member_defs }, cs)
	determine_info_of_symbol {ste_kind=STE_Constructor, ste_index} _ e_input=:{ei_mod_index} e_state e_info=:{ef_cons_defs} cs
		# ({cons_type={st_arity},cons_priority}, ef_cons_defs) = ef_cons_defs![ste_index]
		= (SK_Constructor { glob_object = ste_index, glob_module =  ei_mod_index}, st_arity, cons_priority, cIsNotAFunction,
				e_state, { e_info & ef_cons_defs = ef_cons_defs }, cs)
	determine_info_of_symbol {ste_kind=STE_DclFunction, ste_index} _ e_input=:{ei_mod_index} e_state e_info=:{ef_modules} cs
		# (mod_def, ef_modules) = ef_modules![ei_mod_index]
		# {ft_type={st_arity},ft_priority} = mod_def.dcl_functions.[ste_index]
		  def_index = convertIndex ste_index (toInt STE_DclFunction) mod_def.dcl_conversions
		= (SK_Function { glob_object = def_index, glob_module =  ei_mod_index}, st_arity, ft_priority, cIsAFunction,
				e_state, { e_info & ef_modules = ef_modules }, cs)

::	RecordKind = RK_Constructor | RK_Update | RK_UpdateToConstructor ![AuxiliaryPattern]

cEndWithUpdate :== True
cEndWithSelection :== False

checkExpression :: ![FreeVar] !ParsedExpr !ExpressionInput !*ExpressionState !*ExpressionInfo !*CheckState
	-> *(!Expression, ![FreeVar], !*ExpressionState, !*ExpressionInfo, !*CheckState);
checkExpression free_vars (PE_List exprs) e_input e_state e_info cs	
	# (exprs, free_vars, e_state, e_info, cs) = check_expressions free_vars exprs e_input e_state e_info cs
	  (expr, e_state, cs_error) = build_expression exprs e_state cs.cs_error
	= (expr, free_vars, e_state, e_info, { cs & cs_error = cs_error })

where
	check_expressions free_vars [expr : exprs] e_input e_state e_info cs
		# (exprs, free_vars, e_state, e_info, cs) = check_expressions free_vars exprs e_input e_state e_info cs
		= case expr of
			PE_Ident id
				# (expr, free_vars, e_state, e_info, cs) = checkIdentExpression cIsInExpressionList free_vars id e_input e_state e_info cs
 				-> ([expr : exprs], free_vars, e_state, e_info, cs)
 			_
				# (expr, free_vars, e_state, e_info, cs) = checkExpression free_vars expr e_input e_state e_info cs
 				-> ([expr : exprs], free_vars, e_state, e_info, cs)
 	check_expressions free_vars [] e_input e_state e_info cs
		= ([], free_vars, e_state, e_info, cs)

	build_expression [Constant symb arity _ is_fun] e_state cs_error
		= buildApplication symb arity 0 is_fun [] e_state cs_error
	build_expression [expr] e_state cs_error
		= (expr, e_state, cs_error)
	build_expression [expr : exprs] e_state cs_error
		# (opt_opr, left, e_state, cs_error) = split_at_operator [expr] exprs e_state cs_error
		  (left_expr, e_state, cs_error) = combine_expressions left [] 0 e_state cs_error
		= case opt_opr of
			Yes (symb, prio, is_fun, right)
				-> build_operator_expression [] left_expr (symb, prio, is_fun) right e_state cs_error
			No
				-> (left_expr, e_state, cs_error)
	where
		split_at_operator left [Constant symb arity NoPrio is_fun : exprs] e_state cs_error
			# (appl_exp, e_state, cs_error) = buildApplication symb arity 0 is_fun [] e_state cs_error
			= split_at_operator [appl_exp : left] exprs e_state cs_error
		split_at_operator left [Constant symb arity prio is_fun] e_state cs_error
			# (appl_exp, e_state, cs_error) = buildApplication symb arity 0 is_fun [] e_state cs_error
			= (No, [appl_exp : left], e_state, cs_error)
		split_at_operator left [expr=:(Constant symb _ prio is_fun) : exprs] e_state cs_error
			= (Yes (symb, prio, is_fun, exprs), left, e_state, cs_error)
		split_at_operator left [expr : exprs] e_state cs_error
			= split_at_operator [expr : left] exprs e_state cs_error
		split_at_operator exp [] e_state cs_error
			= (No, exp, e_state, cs_error)

		combine_expressions [first_expr] args arity e_state cs_error
			= case first_expr of
				Constant symb form_arity _ is_fun
					# (app_exp, e_state, cs_error) = buildApplication symb form_arity arity is_fun args e_state cs_error
					-> (app_exp, e_state, cs_error)
				_
					| arity == 0
						-> (first_expr, e_state, cs_error)
						-> (first_expr @ args, e_state, cs_error)
		combine_expressions [rev_arg : rev_args] args arity e_state cs_error
			= combine_expressions rev_args [rev_arg : args] (inc arity) e_state cs_error
		

 		build_operator_expression left_appls left1 (symb1, prio1, is_fun1) [re : res] e_state cs_error
			# (opt_opr, left2, e_state, cs_error) = split_at_operator [re] res e_state cs_error
			= case opt_opr of
				Yes (symb2, prio2, is_fun2, right)
					# optional_prio = determinePriority prio1 prio2
					-> case optional_prio of
						Yes priority
							| priority
						  		# (middle_exp, e_state, cs_error) = combine_expressions left2 [] 0 e_state cs_error
								  (new_left, e_state, cs_error) = buildApplication symb1 2 2 is_fun1 [left1,middle_exp] e_state cs_error
								  (left_appls, new_left, e_state, cs_error) = build_left_operand left_appls prio2 new_left e_state cs_error
								-> build_operator_expression left_appls new_left (symb2, prio2, is_fun2) right e_state cs_error
						  		# (middle_exp, e_state, cs_error) = combine_expressions left2 [] 0 e_state cs_error
								-> build_operator_expression [(symb1, prio1, is_fun1, left1) : left_appls]
										middle_exp (symb2, prio2, is_fun2) right e_state cs_error
						No
							-> (EE, e_state, checkError symb1.symb_name "conflicting priorities" cs_error)
				No
					# (right, e_state, cs_error) = combine_expressions left2 [] 0 e_state cs_error
					  (result_expr, e_state, cs_error) = buildApplication symb1 2 2 is_fun1 [left1,right] e_state cs_error
					-> build_final_expression left_appls result_expr e_state cs_error

		build_left_operand [] _ result_expr e_state cs_error
			= ([], result_expr, e_state, cs_error)		
		build_left_operand la=:[(symb, priol, is_fun, left) : left_appls] prior result_expr e_state cs_error
			# optional_prio = determinePriority priol prior
			= case optional_prio of
				Yes priority
					| priority
						# (result_expr, e_state, cs_error) = buildApplication symb 2 2 is_fun [left,result_expr] e_state cs_error
						-> build_left_operand left_appls prior result_expr e_state cs_error
						-> (la, result_expr, e_state, cs_error)
				No
					-> (la, EE, e_state, checkError symb.symb_name "conflicting priorities" cs_error)
		
		build_final_expression [] result_expr e_state cs_error
			= (result_expr, e_state, cs_error)		
		build_final_expression [(symb, _, is_fun, left) : left_appls] result_expr e_state cs_error
			# (result_expr, e_state, cs_error) = buildApplication symb 2 2 is_fun [left,result_expr] e_state cs_error
			= build_final_expression left_appls result_expr e_state cs_error
					
checkExpression free_vars (PE_Let strict let_locals expr) e_input=:{ei_expr_level,ei_mod_index} e_state e_info cs
	# ei_expr_level = inc ei_expr_level
	  (loc_defs, (var_env, array_patterns), e_state, e_info, cs)
	  		= checkLhssOfLocalDefs ei_expr_level ei_mod_index let_locals e_state e_info cs
	  e_input = { e_input & ei_expr_level = ei_expr_level }
	  (let_expr, free_vars, e_state, e_info, cs) = checkExpression free_vars expr e_input e_state e_info cs
	  (expr, free_vars, e_state=:{es_dynamics,es_expr_heap,es_var_heap}, e_info, cs)
			= addArraySelections array_patterns let_expr free_vars e_input e_state e_info cs
	  (expr, free_vars, e_state, e_info, cs) = checkRhssAndTransformLocalDefs free_vars loc_defs expr e_input e_state e_info cs
	  (es_fun_defs, e_info, heaps, cs)
			= checkLocalFunctions ei_mod_index ei_expr_level let_locals e_state.es_fun_defs e_info
	  			{ hp_var_heap = e_state.es_var_heap, hp_expression_heap = e_state.es_expr_heap, hp_type_heaps = e_state.es_type_heaps } cs
	  (es_fun_defs, cs_symbol_table) = removeLocalsFromSymbolTable ei_expr_level var_env let_locals es_fun_defs cs.cs_symbol_table
	= (expr, free_vars,
		{ e_state & es_fun_defs = es_fun_defs, es_var_heap = heaps.hp_var_heap, es_expr_heap = heaps.hp_expression_heap,
			es_type_heaps = heaps.hp_type_heaps }, e_info, { cs & cs_symbol_table = cs_symbol_table })

checkExpression free_vars (PE_Case case_ident expr alts) e_input e_state e_info cs
	# (pattern_expr, free_vars, e_state, e_info, cs) = checkExpression free_vars expr e_input e_state e_info cs
	  (guards, _, pattern_variables, defaul, free_vars, e_state, e_info, cs) = check_guarded_expressions free_vars alts [] case_ident.id_name e_input e_state e_info cs
	  (pattern_expr, binds, es_expr_heap) = bind_pattern_variables pattern_variables pattern_expr e_state.es_expr_heap
	  (case_expr, es_expr_heap) = build_case guards defaul pattern_expr case_ident es_expr_heap
	  (result_expr, es_expr_heap) = buildLetExpression [] binds case_expr es_expr_heap
	= (result_expr, free_vars, { e_state & es_expr_heap = es_expr_heap }, e_info, cs)
	
where
	check_guarded_expressions free_vars [g] pattern_variables case_name e_input=:{ei_expr_level} e_state e_info cs
		# e_input = { e_input & ei_expr_level = inc ei_expr_level }
		= check_guarded_expression free_vars g NoPattern NoPattern pattern_variables No case_name e_input e_state e_info cs 
	check_guarded_expressions free_vars [g : gs] pattern_variables case_name e_input=:{ei_expr_level} e_state e_info cs
		# e_input = { e_input & ei_expr_level = inc ei_expr_level }
		  (gs, pattern_scheme, pattern_variables, defaul, free_vars, e_state, e_info, cs)
		  	= check_guarded_expressions free_vars gs pattern_variables case_name e_input e_state e_info cs
		= check_guarded_expression free_vars g gs pattern_scheme pattern_variables defaul case_name e_input e_state e_info cs 
	check_guarded_expression free_vars {calt_pattern,calt_rhs={rhs_alts,rhs_locals}} patterns pattern_scheme pattern_variables defaul case_name 
				e_input=:{ei_expr_level,ei_mod_index} e_state=:{es_fun_defs,es_var_heap} e_info cs
		# (pattern, (var_env, array_patterns), {ps_fun_defs,ps_var_heap}, e_info, cs)
				= checkPattern calt_pattern No { pi_def_level = ei_expr_level, pi_mod_index = ei_mod_index, pi_is_node_pattern = False } ([], [])
					{ps_var_heap = es_var_heap, ps_fun_defs = es_fun_defs} e_info cs
		  e_state = { e_state & es_var_heap = ps_var_heap, es_fun_defs = ps_fun_defs }
		  (rhs_expr, free_vars, e_state, e_info, cs)
		  		= checkRhs free_vars rhs_alts rhs_locals e_input e_state e_info cs
		  (expr_with_array_selections, free_vars, e_state=:{es_dynamics,es_expr_heap,es_var_heap}, e_info, cs)
				= addArraySelections array_patterns rhs_expr free_vars e_input e_state e_info cs
		  cs_symbol_table = removeLocalIdentsFromSymbolTable ei_expr_level var_env cs.cs_symbol_table
		  (guarded_expr, pattern_scheme, pattern_variables, defaul, es_var_heap, es_expr_heap, dynamics_in_patterns, cs)
		  		= transform_pattern pattern patterns pattern_scheme pattern_variables defaul expr_with_array_selections case_name
		  									es_var_heap es_expr_heap es_dynamics { cs & cs_symbol_table = cs_symbol_table }
		= (guarded_expr, pattern_scheme, pattern_variables, defaul, free_vars,
			{ e_state & es_var_heap = es_var_heap, es_expr_heap = es_expr_heap, es_dynamics = dynamics_in_patterns },
				e_info, cs)

	transform_pattern :: !AuxiliaryPattern !CasePatterns !CasePatterns !(Env Ident VarInfoPtr) !(Optional (!Optional FreeVar, !Expression)) !Expression
			!String !*VarHeap !*ExpressionHeap ![DynamicPtr] !*CheckState
				-> (!CasePatterns, !CasePatterns, !Env Ident VarInfoPtr, !Optional (!Optional FreeVar,!Expression), !*VarHeap, !*ExpressionHeap, ![DynamicPtr], !*CheckState)
	transform_pattern (AP_Algebraic cons_symbol type_index args opt_var) patterns pattern_scheme pattern_variables defaul result_expr _ var_store expr_heap opt_dynamics cs
		# (var_args, result_expr, var_store, expr_heap, opt_dynamics, cs) = convertSubPatterns args result_expr var_store expr_heap opt_dynamics cs
		  type_symbol = { glob_module = cons_symbol.glob_module, glob_object = type_index}
		  pattern = { ap_symbol = cons_symbol, ap_vars = var_args, ap_expr = result_expr}
		  pattern_variables = cons_optional opt_var pattern_variables
		= case pattern_scheme of
			AlgebraicPatterns alg_type _
				| type_symbol == alg_type
					# alg_patterns = case patterns of
							AlgebraicPatterns _ alg_patterns -> alg_patterns
							NoPattern -> []
					-> (AlgebraicPatterns type_symbol [pattern : alg_patterns], pattern_scheme, pattern_variables, defaul, var_store, expr_heap, opt_dynamics, cs)
					-> (patterns, pattern_scheme, pattern_variables, defaul, var_store, expr_heap, opt_dynamics,
								{ cs & cs_error = checkError cons_symbol.glob_object.ds_ident "incompatible types of patterns" cs.cs_error })
			NoPattern
				-> (AlgebraicPatterns type_symbol [pattern], AlgebraicPatterns type_symbol [], pattern_variables, defaul, var_store, expr_heap, opt_dynamics, cs)
			_
				-> (patterns, pattern_scheme, pattern_variables, defaul, var_store, expr_heap, opt_dynamics,
						{ cs & cs_error = checkError cons_symbol.glob_object.ds_ident "illegal combination of patterns" cs.cs_error })
	transform_pattern (AP_Basic basic_val opt_var) patterns pattern_scheme pattern_variables defaul result_expr _ var_store expr_heap opt_dynamics cs
		# pattern = { bp_value = basic_val, bp_expr = result_expr}
		  pattern_variables = cons_optional opt_var pattern_variables
		  (type_symbol, cs) = typeOfBasicValue basic_val cs
		= case pattern_scheme of
			BasicPatterns basic_type _
				| type_symbol == basic_type
					# basic_patterns = case patterns of
							BasicPatterns _ basic_patterns
								-> basic_patterns
							NoPattern
								-> [] 
					-> (BasicPatterns basic_type [pattern : basic_patterns], pattern_scheme, pattern_variables, defaul, var_store, expr_heap, opt_dynamics, cs)
					-> (patterns, pattern_scheme, pattern_variables, defaul, var_store, expr_heap, opt_dynamics,
							{ cs & cs_error = checkError basic_val "incompatible types of patterns" cs.cs_error })
			NoPattern
				-> (BasicPatterns type_symbol [pattern], BasicPatterns type_symbol [], pattern_variables, defaul, var_store, expr_heap, opt_dynamics, cs)
			_
				-> (patterns, pattern_scheme, pattern_variables, defaul, var_store, expr_heap, opt_dynamics,
						{ cs & cs_error = checkError basic_val "illegal combination of patterns" cs.cs_error})
	transform_pattern (AP_Dynamic pattern type opt_var) patterns pattern_scheme pattern_variables defaul result_expr _ var_store expr_heap opt_dynamics cs
		# (var_arg, result_expr, var_store, expr_heap, opt_dynamics, cs) = convertSubPattern pattern result_expr var_store expr_heap opt_dynamics cs
		  (dynamic_info_ptr, expr_heap) = newPtr (EI_DynamicType type opt_dynamics) expr_heap
		  pattern = { dp_var = var_arg, dp_type	= dynamic_info_ptr,	dp_rhs = result_expr, dp_type_patterns_vars = [], dp_type_code = TCE_Empty }
		  pattern_variables = cons_optional opt_var pattern_variables
		= case pattern_scheme of
			DynamicPatterns _
				# dyn_patterns = case patterns of 
										DynamicPatterns dyn_patterns
											-> dyn_patterns
										NoPattern
											-> []
				-> (DynamicPatterns [pattern : dyn_patterns], pattern_scheme, pattern_variables, defaul, var_store, expr_heap, [dynamic_info_ptr], cs)
			NoPattern
				-> (DynamicPatterns [pattern], DynamicPatterns [], pattern_variables, defaul, var_store, expr_heap, [dynamic_info_ptr], cs)
			_
				-> (patterns, pattern_scheme, pattern_variables, defaul, var_store, expr_heap, opt_dynamics,
						{ cs & cs_error = checkError "<dynamic pattern>" "illegal combination of patterns" cs.cs_error })
	transform_pattern (AP_Variable name var_info opt_var) NoPattern pattern_scheme pattern_variables No result_expr _ var_store expr_heap opt_dynamics cs
		= ( NoPattern, pattern_scheme, cons_optional opt_var pattern_variables, 
		  	Yes (Yes { fv_name = name, fv_info_ptr = var_info, fv_def_level = NotALevel, fv_count = 0 }, result_expr),
			var_store, expr_heap, opt_dynamics, cs)		
	transform_pattern (AP_Variable name var_info opt_var) patterns pattern_scheme pattern_variables defaul result_expr case_name var_store expr_heap opt_dynamics cs
		# free_var = { fv_name = name, fv_info_ptr = var_info, fv_def_level = NotALevel, fv_count = 0 }
		  (new_bound_var, expr_heap) = allocate_bound_var free_var expr_heap
		  case_ident = { id_name = case_name, id_info = nilPtr }
		  (new_case, expr_heap) = build_case patterns defaul (Var new_bound_var) case_ident expr_heap
		  new_defaul = insert_as_default new_case result_expr
		= (NoPattern, pattern_scheme, (cons_optional opt_var pattern_variables), Yes (Yes free_var, new_defaul),
			var_store, expr_heap, opt_dynamics, cs)
	transform_pattern (AP_WildCard (Yes opt_var)) patterns pattern_scheme pattern_variables defaul result_expr case_name var_store expr_heap opt_dynamics cs
		= transform_pattern (AP_Variable opt_var.bind_src opt_var.bind_dst No) patterns pattern_scheme pattern_variables defaul
							result_expr case_name var_store expr_heap opt_dynamics cs
	transform_pattern (AP_WildCard no) NoPattern pattern_scheme pattern_variables No result_expr _ var_store expr_heap opt_dynamics cs
		= (NoPattern, pattern_scheme, pattern_variables, Yes (No, result_expr), var_store, expr_heap, opt_dynamics, cs)
	transform_pattern (AP_WildCard _) patterns pattern_scheme pattern_variables defaul result_expr case_name var_store expr_heap opt_dynamics cs
		# (new_info_ptr, var_store) = newPtr VI_Empty var_store
		= transform_pattern (AP_Variable (newVarId "wc") new_info_ptr No) patterns pattern_scheme pattern_variables defaul
							result_expr case_name var_store expr_heap opt_dynamics cs
	transform_pattern (AP_Empty name) patterns pattern_scheme pattern_variables defaul result_expr _ var_store expr_heap opt_dynamics cs
		= (patterns, pattern_scheme, pattern_variables, defaul, var_store, expr_heap, opt_dynamics, cs)


	insert_as_default :: !Expression !Expression -> Expression
	insert_as_default to_insert (Let lad=:{let_expr})
		= Let { lad & let_expr = insert_as_default to_insert let_expr }
	insert_as_default to_insert (Case kees=:{case_default})
		= case case_default of
			No			-> Case { kees & case_default = Yes to_insert }
			Yes defaul	-> Case { kees & case_default = Yes (insert_as_default to_insert defaul)}
	insert_as_default _ expr = expr // checkWarning "pattern won't match"

	build_case NoPattern defaul expr case_ident expr_heap
		= case defaul of
			Yes (opt_var, result)
				-> case opt_var of
					Yes var
						# (let_expression, expr_heap) = bind_default_variable expr var result expr_heap
						-> (let_expression, expr_heap)
					No
						-> (result, expr_heap)
			No
				-> (EE, expr_heap)
	build_case (DynamicPatterns patterns) defaul expr case_ident expr_heap
		= case defaul of
			Yes (opt_var, result)
				-> case opt_var of
					Yes var
						# (type_case_info_ptr, expr_heap) = newPtr EI_Empty expr_heap
						  (bound_var, expr_heap) = allocate_bound_var var expr_heap
						  result = buildTypeCase (Var bound_var) patterns (Yes result) type_case_info_ptr
						  (case_expression, expr_heap) = bind_default_variable expr var result expr_heap
					 	-> (case_expression, expr_heap)
					No
						# (type_case_info_ptr, expr_heap) = newPtr EI_Empty expr_heap
						-> (buildTypeCase expr patterns (Yes result) type_case_info_ptr, expr_heap)
			No
				# (type_case_info_ptr, expr_heap) = newPtr EI_Empty expr_heap
				-> (buildTypeCase expr patterns No type_case_info_ptr, expr_heap)
	build_case patterns (Yes (opt_var,result)) expr case_ident expr_heap
		= case opt_var of
			Yes var
				# (case_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
				  (bound_var, expr_heap) = allocate_bound_var var expr_heap
				  result = Case {case_expr = Var bound_var, case_guards = patterns, case_default = Yes result,
								 case_ident = Yes case_ident, case_info_ptr = case_expr_ptr}
				  (case_expression, expr_heap) = bind_default_variable expr var result expr_heap
				-> (case_expression, expr_heap)
			No
				#  (case_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
				-> (Case {case_expr = expr, case_guards = patterns, case_default = Yes result,
						case_ident = Yes case_ident, case_info_ptr = case_expr_ptr }, expr_heap)
	build_case patterns No expr case_ident expr_heap
		# (case_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
		= (Case {case_expr = expr, case_guards = patterns, case_default = No, case_ident = Yes case_ident, case_info_ptr = case_expr_ptr }, expr_heap)

	bind_default_variable bind_src bind_dst result_expr expr_heap
		#  (let_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
		= (Let {let_strict_binds = [], let_lazy_binds = [{ bind_src = bind_src, bind_dst = bind_dst }],
				let_expr = result_expr, let_info_ptr = let_expr_ptr }, expr_heap)

	bind_pattern_variables [] pattern_expr expr_heap
		= (pattern_expr, [], expr_heap)
	bind_pattern_variables [{bind_src,bind_dst} : variables] this_pattern_expr expr_heap
		# free_var = { fv_name = bind_src, fv_info_ptr = bind_dst, fv_def_level = NotALevel, fv_count = 0 }
		  (bound_var, expr_heap) = allocate_bound_var free_var expr_heap
		  (pattern_expr, binds, expr_heap) = bind_pattern_variables variables (Var bound_var) expr_heap
		= (pattern_expr, [{bind_src = this_pattern_expr, bind_dst = free_var} : binds], expr_heap)

	cons_optional (Yes var) variables
		= [ var : variables ]
	cons_optional No variables
		= variables

checkExpression free_vars (PE_Selection is_unique expr [PS_Array index_expr]) e_input e_state e_info cs	
	# (expr, free_vars, e_state, e_info, cs) = checkExpression free_vars expr e_input e_state e_info cs
	| is_unique
		# (glob_select_symb, cs) = getPredefinedGlobalSymbol PD_UnqArraySelectFun PD_StdArray STE_Member 2 cs
		  (selector, free_vars, e_state, e_info, cs) = checkArraySelection glob_select_symb free_vars index_expr e_input e_state e_info cs
		= (Selection No expr [selector], free_vars, e_state, e_info, cs)
		# (glob_select_symb, cs) = getPredefinedGlobalSymbol PD_ArraySelectFun PD_StdArray STE_Member 2 cs
		  (selector, free_vars, e_state, e_info, cs) = checkArraySelection glob_select_symb free_vars index_expr e_input e_state e_info cs
		= (Selection No expr [selector], free_vars, e_state, e_info, cs)
checkExpression free_vars (PE_Selection is_unique expr selectors) e_input e_state e_info cs	
	# (selectors, free_vars, e_state, e_info, cs) = checkSelectors cEndWithSelection free_vars selectors e_input e_state e_info cs
	  (expr, free_vars, e_state, e_info, cs) = checkExpression free_vars expr e_input e_state e_info cs
	| is_unique
		# (tuple_type, cs) = getPredefinedGlobalSymbol (GetTupleTypeIndex 2) PD_PredefinedModule STE_Type 2 cs
		= (Selection (Yes tuple_type) expr selectors, free_vars, e_state, e_info, cs)
		= (Selection No expr selectors, free_vars, e_state, e_info, cs)
checkExpression free_vars (PE_Update expr1 selectors expr2) e_input e_state e_info cs	
	# (expr1, free_vars, e_state, e_info, cs) = checkExpression free_vars expr1 e_input e_state e_info cs
	  (selectors, free_vars, e_state, e_info, cs) = checkSelectors cEndWithUpdate free_vars selectors e_input e_state e_info cs
	  (expr2, free_vars, e_state, e_info, cs) = checkExpression free_vars expr2 e_input e_state e_info cs
	= (Update expr1 selectors expr2, free_vars, e_state, e_info, cs)
checkExpression free_vars (PE_Tuple exprs) e_input e_state e_info cs
	# (exprs, arity, free_vars, e_state, e_info, cs) = check_expression_list free_vars exprs e_input e_state e_info cs
	  ({glob_object={ds_ident,ds_index, ds_arity},glob_module}, cs)
	  		= getPredefinedGlobalSymbol (GetTupleConsIndex arity) PD_PredefinedModule STE_Constructor arity cs
	= (App { app_symb = { symb_name = ds_ident, symb_arity = ds_arity,
						  symb_kind = SK_Constructor { glob_object = ds_index, glob_module = glob_module }},
			 app_args = exprs, app_info_ptr = nilPtr }, free_vars, e_state, e_info, cs)
where
	check_expression_list free_vars [] e_input e_state e_info cs
		= ([], 0, free_vars, e_state, e_info, cs)
	check_expression_list free_vars [expr : exprs] e_input e_state e_info cs
		# (expr, free_vars, e_state, e_info, cs) = checkExpression free_vars expr e_input e_state e_info cs
		  (exprs, length, free_vars, e_state, e_info, cs) = check_expression_list free_vars exprs e_input e_state e_info cs
		= ([expr : exprs], inc length, free_vars, e_state, e_info, cs)

checkExpression free_vars rec=:(PE_Record record opt_type fields) e_input=:{ei_expr_level,ei_mod_index} e_state e_info cs
	# (opt_record_and_fields, e_info, cs) = checkFields ei_mod_index fields opt_type e_info cs
	= case opt_record_and_fields of
		Yes (cons=:{glob_module, glob_object}, _, new_fields)
			# {ds_ident,ds_index,ds_arity} = glob_object
			  rec_cons = { symb_name = ds_ident, symb_kind = SK_Constructor { glob_object = ds_index, glob_module = glob_module }, symb_arity = ds_arity }
			-> case record of
				PE_Empty
					# (exprs, free_vars, e_state, e_info, cs) = check_field_exprs free_vars new_fields 0 RK_Constructor e_input e_state e_info cs
					-> (App { app_symb = rec_cons, app_args = remove_fields exprs, app_info_ptr = nilPtr }, free_vars, e_state, e_info, cs)
				_
					# (rec_expr, free_vars, e_state, e_info, cs) = checkExpression free_vars record e_input e_state e_info cs
					-> case rec_expr of
						Var {var_info_ptr,var_name}
							# (var_info, es_var_heap) = readPtr var_info_ptr e_state.es_var_heap
							  e_state = { e_state & es_var_heap = es_var_heap }
							-> case var_info of
								VI_Record fields
									# (exprs, free_vars, e_state, e_info, cs) 
											= check_field_exprs free_vars new_fields 0 (RK_UpdateToConstructor fields) e_input e_state e_info cs
									-> (App { app_symb = rec_cons, app_args = remove_fields exprs, app_info_ptr = nilPtr }, free_vars, e_state, e_info, cs)
								_ 
									# (exprs, free_vars, e_state, e_info, cs)
											= check_field_exprs free_vars new_fields 0 RK_Update e_input e_state e_info cs
									-> (RecordUpdate cons rec_expr exprs, free_vars, e_state, e_info, cs)
						_ 
							# (exprs, free_vars, e_state, e_info, cs)
									= check_field_exprs free_vars new_fields 0 RK_Update e_input e_state e_info cs
							-> (RecordUpdate cons rec_expr exprs, free_vars, e_state, e_info, cs)
		No
			-> (EE, free_vars, e_state, e_info, cs)
where
	remove_fields binds = [ bind_src \\ {bind_src} <- binds ]

	check_field_exprs free_vars [] field_nr record_kind e_input e_state e_info cs
		= ([], free_vars, e_state, e_info, cs)
	check_field_exprs free_vars [field_expr : field_exprs] field_nr record_kind e_input e_state e_info cs
		# (expr, free_vars, e_state, e_info, cs)
			= check_field_expr free_vars field_expr field_nr record_kind e_input e_state e_info cs
		  (exprs, free_vars, e_state, e_info, cs) = check_field_exprs free_vars field_exprs (inc field_nr) record_kind e_input e_state e_info cs
		= ([expr : exprs], free_vars, e_state, e_info, cs)

	check_field_expr free_vars field=:{bind_src = PE_Empty, bind_dst={glob_object={fs_var,fs_name,fs_index},glob_module}} field_nr record_kind e_input e_state e_info cs
		# (expr, free_vars, e_state, e_info, cs)
			= checkIdentExpression cIsNotInExpressionList free_vars fs_var e_input e_state e_info cs
		= ({ field & bind_src = expr }, free_vars, e_state, e_info, cs)
	check_field_expr free_vars field=:{bind_src = PE_WildCard, bind_dst={glob_object=fs_name}} field_nr RK_Constructor e_input e_state e_info cs
		= ({ field & bind_src = NoBind nilPtr }, free_vars, e_state, e_info, { cs & cs_error = checkError fs_name "field not specified" cs.cs_error })
	check_field_expr free_vars field=:{bind_src = PE_WildCard} field_nr RK_Update e_input e_state=:{es_expr_heap} e_info cs
		# (bind_expr_ptr, es_expr_heap) = newPtr EI_Empty es_expr_heap
		= ({ field & bind_src = NoBind bind_expr_ptr }, free_vars, { e_state & es_expr_heap = es_expr_heap }, e_info, cs)
	check_field_expr free_vars field=:{bind_src = PE_WildCard} field_nr (RK_UpdateToConstructor fields) e_input e_state=:{es_expr_heap} e_info cs
		# (var_name, var_info_ptr) = get_field_var (fields !! field_nr)
		  (var_expr_ptr, es_expr_heap) = newPtr EI_Empty es_expr_heap
		= ({ field & bind_src = Var { var_name = var_name, var_info_ptr = var_info_ptr, var_expr_ptr = var_expr_ptr }}, free_vars,
				{ e_state & es_expr_heap = es_expr_heap }, e_info, cs)
	check_field_expr free_vars field=:{bind_src} field_nr upd_record e_input e_state e_info cs
		# (expr, free_vars, e_state, e_info, cs)
			= checkExpression free_vars bind_src e_input e_state e_info cs
		= ({ field & bind_src = expr }, free_vars, e_state, e_info, cs)
	
	get_field_var (AP_Algebraic _ _ _ (Yes {bind_src,bind_dst}))
		= (bind_src, bind_dst)
	get_field_var (AP_Basic _ (Yes {bind_src,bind_dst}))
		= (bind_src, bind_dst)
	get_field_var (AP_Dynamic _ _ (Yes {bind_src,bind_dst}))
		= (bind_src, bind_dst)
	get_field_var (AP_Variable id var_ptr _)
		= (id, var_ptr)
	get_field_var (AP_WildCard (Yes {bind_src,bind_dst}))
		= (bind_src, bind_dst)
	get_field_var _
		= ({ id_name = "** ERRONEOUS **", id_info = nilPtr }, nilPtr)

checkExpression free_vars (PE_Dynamic expr opt_type) e_input e_state=:{es_expr_heap,es_dynamics} e_info cs	
	# (dyn_info_ptr, es_expr_heap) = newPtr (EI_Dynamic opt_type) es_expr_heap
	  (dyn_expr, free_vars, e_state, e_info, cs) = checkExpression free_vars expr e_input
	  		{e_state & es_dynamics = [dyn_info_ptr : es_dynamics], es_expr_heap = es_expr_heap } e_info cs
	= (DynamicExpr { dyn_expr = dyn_expr, dyn_opt_type = opt_type, dyn_info_ptr = dyn_info_ptr, dyn_type_code = TCE_Empty, dyn_uni_vars = [] },
			free_vars, e_state, e_info, { cs & cs_needed_modules = cs.cs_needed_modules bitor cNeedStdDynamics }) 

checkExpression free_vars (PE_Basic basic_value) e_input e_state e_info cs
	# (basic_type, cs) = typeOfBasicValue basic_value cs
	= (BasicExpr basic_value basic_type, free_vars, e_state, e_info, cs)

checkExpression free_vars (PE_ABC_Code code_sequence do_inline) e_input e_state e_info cs
	= (ABCCodeExpr code_sequence do_inline, free_vars, e_state, e_info, cs)
checkExpression free_vars (PE_Any_Code ins outs code_sequence) e_input e_state e_info cs
	# (ins, (free_vars, e_state, e_info, cs)) = check_in_parameters e_input ins (free_vars, e_state, e_info, cs)
	  (new_outs, (e_state, cs)) = check_out_parameters e_input.ei_expr_level outs (e_state, cs)
	  cs_symbol_table = remove_out_parameters_from_symbol_table e_input.ei_expr_level outs cs.cs_symbol_table
	= (AnyCodeExpr ins new_outs code_sequence, free_vars, e_state, e_info, { cs & cs_symbol_table = cs_symbol_table })
where
	check_in_parameters e_input params fv_es_ei_cs
		= mapSt (check_in_parameter e_input) params fv_es_ei_cs

	check_in_parameter e_input { bind_src, bind_dst } (free_vars, e_state, e_info, cs)
		# (id_expr, free_vars, e_state, e_info, cs) = checkIdentExpression cIsNotInExpressionList free_vars bind_dst e_input e_state e_info cs
		= case id_expr of
			Var var
				-> ({ bind_dst = var, bind_src = bind_src }, (free_vars, e_state, e_info, cs))
			_
				-> ({ bind_dst = { var_name = bind_dst, var_info_ptr = nilPtr, var_expr_ptr = nilPtr }, bind_src = bind_src }, (free_vars, e_state, e_info,
						{ cs & cs_error = checkError bind_src "bound variable expected" cs.cs_error }))

	check_out_parameters expr_level params es_cs
		= mapSt (check_out_parameter expr_level) params es_cs

	check_out_parameter expr_level bind=:{ bind_src, bind_dst } (e_state, cs)
		| isLowerCaseName bind_dst.id_name
			# (entry, cs_symbol_table) = readPtr bind_dst.id_info cs.cs_symbol_table
			# (new_info_ptr, es_var_heap) = newPtr VI_Empty e_state.es_var_heap
			  cs = checkPatternVariable expr_level entry bind_dst new_info_ptr { cs & cs_symbol_table = cs_symbol_table }
			= (	{ bind & bind_dst = { fv_def_level = expr_level, fv_name = bind_dst, fv_info_ptr = new_info_ptr, fv_count = 0 }},
					( { e_state & es_var_heap = es_var_heap }, cs))
			= ( { bind & bind_dst = { fv_def_level = expr_level, fv_name = bind_dst, fv_info_ptr = nilPtr, fv_count = 0 }},
					( e_state, { cs & cs_error = checkError bind_src "variable expected" cs.cs_error }))

	remove_out_parameters_from_symbol_table expr_level idents symbol_table
		= foldSt (\{bind_dst} -> removeIdentFromSymbolTable expr_level bind_dst) idents symbol_table

checkExpression free_vars (PE_Ident id) e_input e_state e_info cs
	= checkIdentExpression cIsNotInExpressionList free_vars id e_input e_state e_info cs
checkExpression free_vars expr e_input e_state e_info cs
	= abort "checkExpression (check.icl, line 1433)" // <<- expr

:: LastSelection	= LS_Update | LS_Selction | LS_UniqueSelection
 
checkSelectors end_with_update free_vars [ selector : selectors ] e_input e_state e_info cs
	| isEmpty selectors
		# (selector, free_vars, e_state, e_info, cs) = check_selector end_with_update free_vars selector e_input e_state e_info cs
		= ([ selector ], free_vars, e_state, e_info, cs)
		# (selector, free_vars, e_state, e_info, cs) = check_selector cEndWithSelection free_vars selector e_input e_state e_info cs
		  (selectors, free_vars, e_state, e_info, cs) = checkSelectors end_with_update free_vars selectors e_input e_state e_info cs
		= ([ selector : selectors ], free_vars, e_state, e_info, cs)
where		
	check_selector _ free_vars (PS_Record selector=:{id_info,id_name} opt_type) e_input=:{ei_mod_index} e_state
			e_info=:{ef_selector_defs, ef_modules} cs=:{cs_symbol_table}
		# (entry, cs_symbol_table) = readPtr id_info cs_symbol_table
		# selectors = retrieveSelectorIndexes ei_mod_index entry 
		  (field_module, field_index, field_nr, ef_selector_defs, ef_modules, cs)
		  		= get_field_nr ei_mod_index selector opt_type selectors ef_selector_defs ef_modules { cs & cs_symbol_table = cs_symbol_table }
		= (RecordSelection { glob_object = MakeDefinedSymbol selector field_index 1, glob_module = field_module } field_nr, free_vars, e_state,
								{e_info & ef_selector_defs = ef_selector_defs, ef_modules = ef_modules }, cs)
	where					
		get_field_nr :: !Index !Ident !(Optional Ident) ![Global Index] !u:{#SelectorDef} !v:{# DclModule} !*CheckState
				-> (!Index, !Index, !Index, u:{#SelectorDef}, v:{#DclModule}, !*CheckState)
		get_field_nr mod_index sel_id _ [] selector_defs modules cs=:{cs_error}
			= (NoIndex, NoIndex, NoIndex, selector_defs, modules, { cs & cs_error = checkError id_name " selector not defined" cs_error })
		get_field_nr mod_index sel_id (Yes type_id=:{id_info}) selectors selector_defs modules cs=:{cs_symbol_table,cs_error}
			# (entry, cs_symbol_table) = readPtr id_info cs_symbol_table
			# (type_index, type_module) = retrieveGlobalDefinition entry STE_Type mod_index
			| type_index <> NotFound
				# (selector_index, selector_offset, selector_defs, modules)
						= determine_selector mod_index type_module type_index selectors selector_defs modules
				| selector_offset <> NoIndex
					= (type_module, selector_index, selector_offset, selector_defs, modules, { cs & cs_symbol_table = cs_symbol_table })
					= (NoIndex, NoIndex, NoIndex, selector_defs, modules, { cs & cs_symbol_table = cs_symbol_table,
								cs_error = checkError id_name " selector not defined" cs_error })
				= (NoIndex, NoIndex, NoIndex, selector_defs, modules, { cs & cs_symbol_table = cs_symbol_table,
						cs_error = checkError type_id " type not defined" cs_error })
		get_field_nr mod_index sel_id No [{glob_object,glob_module}] selector_defs modules cs
			| mod_index == glob_module
				# (selector_offset,selector_defs) = selector_defs![glob_object].sd_field_nr
				= (glob_module, glob_object, selector_offset, selector_defs, modules, cs)
				# (selector_offset,modules) = modules![glob_module].dcl_common.com_selector_defs.[glob_object].sd_field_nr
				= (glob_module, glob_object, selector_offset, selector_defs, modules, cs)
		get_field_nr mod_index sel_id No _  selector_defs modules cs=:{cs_error}
			= (NoIndex, NoIndex, NoIndex, selector_defs, modules, { cs & cs_error = checkError sel_id " ambiguous selector specified" cs_error })

		determine_selector :: !Index !Index !Index ![Global Index] !u:{# SelectorDef} !v:{# DclModule} -> (!Int, !Int, !u:{# SelectorDef}, !v:{# DclModule})
		determine_selector mod_index type_mod_index type_index [] selector_defs modules
			= (NoIndex, NoIndex, selector_defs, modules)
		determine_selector mod_index type_mod_index type_index [{glob_module, glob_object} : selectors] selector_defs modules
			| type_mod_index == glob_module
				| type_mod_index == mod_index
					#! selector_def = selector_defs.[glob_object]
					| selector_def.sd_type_index == type_index
						= (glob_object, selector_def.sd_field_nr, selector_defs, modules)
						= determine_selector mod_index type_mod_index type_index selectors selector_defs modules
					#! {dcl_common={com_selector_defs}} = modules.[glob_module]
					#! selector_def = com_selector_defs.[glob_object]
					| selector_def.sd_type_index == type_index
						= (glob_object, selector_def.sd_field_nr, selector_defs, modules)
						= determine_selector mod_index type_mod_index type_index selectors selector_defs modules
				= determine_selector mod_index type_mod_index type_index selectors selector_defs modules

	check_selector end_with_update free_vars (PS_Array index_expr) e_input e_state e_info cs
		| end_with_update
			# (glob_select_symb, cs) = getPredefinedGlobalSymbol PD_ArrayUpdateFun PD_StdArray STE_Member 3 cs
			= checkArraySelection glob_select_symb free_vars index_expr e_input e_state e_info cs
			# (glob_select_symb, cs) = getPredefinedGlobalSymbol PD_ArraySelectFun PD_StdArray STE_Member 2 cs
			= checkArraySelection glob_select_symb free_vars index_expr e_input e_state e_info cs

checkArraySelection glob_select_symb free_vars index_expr e_input e_state e_info cs
	# (index_expr, free_vars, e_state, e_info, cs) = checkExpression free_vars index_expr e_input e_state e_info cs
	  (new_info_ptr, es_expr_heap) = newPtr EI_Empty e_state.es_expr_heap
	= (ArraySelection glob_select_symb new_info_ptr index_expr, free_vars, { e_state & es_expr_heap = es_expr_heap }, e_info, cs)

buildLetExpression :: !(Env Expression FreeVar) !(Env Expression FreeVar) !Expression !*ExpressionHeap  -> (!Expression, !*ExpressionHeap)
buildLetExpression [] [] expr expr_heap
	= (expr, expr_heap)
buildLetExpression let_strict_binds let_lazy_binds expr expr_heap
	# (let_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
	= (Let {let_strict_binds = let_strict_binds, let_lazy_binds = let_lazy_binds, let_expr = expr, let_info_ptr = let_expr_ptr }, expr_heap)

checkLhssOfLocalDefs def_level mod_index (CollectedLocalDefs {loc_functions={ir_from,ir_to},loc_nodes}) e_state=:{es_var_heap,es_fun_defs} e_info cs
	# (loc_defs, accus, {ps_fun_defs,ps_var_heap}, e_info, cs)
			= check_patterns loc_nodes {pi_def_level = def_level, pi_mod_index = mod_index, pi_is_node_pattern = True } ([], [])
					{ps_fun_defs = es_fun_defs, ps_var_heap = es_var_heap} e_info cs
	  (es_fun_defs, cs_symbol_table, cs_error) = addLocalFunctionDefsToSymbolTable def_level ir_from ir_to ps_fun_defs cs.cs_symbol_table cs.cs_error
	= (loc_defs, accus, { e_state & es_fun_defs = es_fun_defs, es_var_heap = ps_var_heap }, e_info, { cs & cs_symbol_table = cs_symbol_table, cs_error = cs_error })
where
	check_patterns [ (_,node_def) : node_defs ] p_input accus var_store e_info cs
		# (pattern, accus, var_store, e_info, cs) = checkPattern node_def.nd_dst No p_input accus var_store e_info cs
		  (patterns, accus, var_store, e_info, cs) = check_patterns node_defs p_input accus var_store e_info cs
		= ([{ node_def & nd_dst = pattern } : patterns], accus, var_store, e_info, cs)
	check_patterns [] p_input accus var_store e_info cs
		= ([], accus, var_store, e_info, cs)

checkRhssAndTransformLocalDefs free_vars [] rhs_expr e_input e_state e_info cs
	= (rhs_expr, free_vars, e_state, e_info, cs)
checkRhssAndTransformLocalDefs free_vars loc_defs rhs_expr e_input e_state e_info cs
	# (binds, free_vars, e_state, e_info, cs) = checkAndTransformPatternIntoBind free_vars loc_defs e_input e_state e_info cs
	  (rhs_expr, es_expr_heap) = buildLetExpression [] binds rhs_expr e_state.es_expr_heap
	= (rhs_expr, free_vars, { e_state & es_expr_heap = es_expr_heap }, e_info, cs)

checkAndTransformPatternIntoBind free_vars [{nd_dst,nd_alts,nd_locals} : local_defs] e_input=:{ei_expr_level,ei_mod_index} e_state e_info cs
	# (bind_src, free_vars, e_state, e_info, cs) = checkRhs free_vars nd_alts nd_locals e_input e_state e_info cs	
	  (binds_of_bind, es_var_heap, es_expr_heap, e_info, cs)
			= transfromPatternIntoBind ei_mod_index ei_expr_level nd_dst bind_src e_state.es_var_heap e_state.es_expr_heap e_info cs
	  e_state = { e_state & es_var_heap = es_var_heap, es_expr_heap = es_expr_heap }
	  (binds_of_local_defs, free_vars, e_state, e_info, cs) = checkAndTransformPatternIntoBind free_vars local_defs e_input e_state e_info cs
	= (binds_of_bind ++ binds_of_local_defs, free_vars, e_state, e_info, cs)
checkAndTransformPatternIntoBind free_vars [] e_input e_state e_info cs
	= ([], free_vars, e_state, e_info, cs)

transfromPatternIntoBind :: !Index !Level !AuxiliaryPattern !Expression !*VarHeap !*ExpressionHeap !*ExpressionInfo !*CheckState
	-> *(![Bind Expression FreeVar], !*VarHeap, !*ExpressionHeap,  !*ExpressionInfo, !*CheckState)
transfromPatternIntoBind mod_index def_level (AP_Variable name var_info _) src_expr var_store expr_heap e_info cs
	# bind = {bind_src = src_expr, bind_dst = { fv_name = name, fv_info_ptr = var_info, fv_def_level = def_level, fv_count = 0 }}
	= ([bind], var_store, expr_heap, e_info, cs)
transfromPatternIntoBind mod_index def_level (AP_Algebraic cons_symbol=:{glob_module,glob_object=ds_cons=:{ds_arity, ds_index, ds_ident}} type_index args opt_var)
		src_expr var_store expr_heap e_info=:{ef_type_defs,ef_modules} cs
	# (src_expr, opt_var_bind, var_store, expr_heap) = bind_opt_var opt_var src_expr var_store expr_heap
	| ds_arity == 0
		= ([], var_store, expr_heap, e_info, { cs & cs_error = checkError ds_ident " constant not allowed in a node pattern" cs.cs_error})
	# (is_tuple, cs) = is_tuple_symbol glob_module ds_index cs
	| is_tuple
		# (tuple_var, tuple_bind, var_store, expr_heap) = bind_match_expr src_expr opt_var_bind var_store expr_heap
		= transform_sub_patterns mod_index def_level args ds_cons 0 tuple_var tuple_bind var_store expr_heap e_info cs
		# ({td_rhs}, ef_type_defs, ef_modules) = get_type_def mod_index glob_module type_index ef_type_defs ef_modules
		  e_info = { e_info & ef_type_defs = ef_type_defs, ef_modules = ef_modules }
		= case td_rhs of
			RecordType {rt_fields}
				| size rt_fields == 1
					-> transform_sub_patterns_of_record mod_index def_level args rt_fields glob_module 0 src_expr opt_var_bind var_store expr_heap e_info cs
					# (record_var, record_bind, var_store, expr_heap)
						= bind_match_expr src_expr opt_var_bind var_store expr_heap
					-> transform_sub_patterns_of_record mod_index def_level args rt_fields glob_module 0 record_var record_bind var_store expr_heap e_info cs
			_
				| ds_arity == 1
		  			# (binds, var_store, expr_heap, e_info, cs)
						= transfromPatternIntoBind mod_index def_level (hd args) (MatchExpr No cons_symbol src_expr) var_store expr_heap e_info cs
					-> (opt_var_bind ++ binds, var_store, expr_heap, e_info, cs)
					# (tuple_type, cs) = getPredefinedGlobalSymbol (GetTupleTypeIndex ds_arity) PD_PredefinedModule STE_Type ds_arity cs
					  (tuple_cons, cs) = getPredefinedGlobalSymbol (GetTupleConsIndex ds_arity) PD_PredefinedModule STE_Constructor ds_arity cs
					  (match_var, match_bind, var_store, expr_heap)
						=  bind_match_expr (MatchExpr (Yes tuple_type) cons_symbol src_expr) opt_var_bind var_store expr_heap
					-> transform_sub_patterns mod_index def_level args tuple_cons.glob_object 0 match_var match_bind var_store expr_heap e_info cs


where
	get_type_def mod_index type_mod_index type_index ef_type_defs ef_modules
		| mod_index == type_mod_index
			# (type_def, ef_type_defs) = ef_type_defs![type_index]
			= (type_def, ef_type_defs, ef_modules)
			# ({dcl_common},  ef_modules) = ef_modules![type_mod_index]
			= (dcl_common.com_type_defs.[type_index], ef_type_defs, ef_modules)
		
	is_tuple_symbol cons_module cons_index cs
		# (tuple_2_symbol, cs) = getPredefinedGlobalSymbol (GetTupleConsIndex 2) PD_PredefinedModule STE_Constructor 2 cs
		= (tuple_2_symbol.glob_module == cons_module &&
		   tuple_2_symbol.glob_object.ds_index <= cons_index && cons_index <= tuple_2_symbol.glob_object.ds_index + 30, cs)

	transform_sub_patterns mod_index def_level [pattern : patterns] tup_id tup_index arg_var all_binds var_store expr_heap e_info cs
		# (this_arg_var, expr_heap) = adjust_match_expression arg_var expr_heap
		  match_expr = TupleSelect tup_id tup_index this_arg_var
		  (binds, var_store, expr_heap, e_info, cs) = transfromPatternIntoBind mod_index def_level pattern match_expr var_store expr_heap e_info cs
		= transform_sub_patterns mod_index def_level patterns tup_id (inc tup_index) arg_var (binds ++ all_binds) var_store expr_heap e_info cs
	transform_sub_patterns mod_index _ [] _ _ _ binds var_store expr_heap e_info cs
		= (binds, var_store, expr_heap, e_info, cs)

	transform_sub_patterns_of_record mod_index def_level [pattern : patterns] fields field_module field_index record_expr
			all_binds var_store expr_heap e_info cs
		# {fs_name, fs_index} = fields.[field_index]
		  selector = { glob_module = field_module, glob_object = MakeDefinedSymbol fs_name fs_index 1}
		  (this_record_expr, expr_heap) = adjust_match_expression record_expr expr_heap
		  (binds, var_store, expr_heap, e_info, cs)
				= transfromPatternIntoBind mod_index def_level pattern (Selection No this_record_expr [ RecordSelection selector field_index ])
						var_store expr_heap e_info cs
		= transform_sub_patterns_of_record mod_index def_level patterns fields field_module (inc field_index) record_expr
				(binds ++ all_binds) var_store expr_heap e_info cs
	transform_sub_patterns_of_record mod_index _ [] _ _ _ _ binds var_store expr_heap e_info cs
		= (binds, var_store, expr_heap, e_info, cs)

	bind_opt_var (Yes {bind_src,bind_dst}) src_expr var_heap expr_heap
		# free_var = { fv_name = bind_src, fv_info_ptr = bind_dst, fv_def_level = NotALevel, fv_count = 0 }
		  (var_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
		  bound_var = { var_name = bind_src, var_info_ptr = bind_dst, var_expr_ptr = var_expr_ptr }
		= (Var bound_var, [{bind_src = src_expr, bind_dst = free_var}], var_heap <:= (bind_dst, VI_Empty), expr_heap)
	bind_opt_var No src_expr var_heap expr_heap
		= (src_expr, [], var_heap, expr_heap)
		
	bind_match_expr var_expr=:(Var var) opt_var_bind var_heap expr_heap
		= (var_expr, opt_var_bind, var_heap, expr_heap)
	bind_match_expr match_expr opt_var_bind var_heap expr_heap
		# new_name = newVarId "_x"
		  (var_info_ptr, var_heap) = newPtr VI_Empty var_heap
//		  (var_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
		  bound_var = { var_name = new_name, var_info_ptr = var_info_ptr, var_expr_ptr = nilPtr }
		  free_var = { fv_name = new_name, fv_info_ptr = var_info_ptr, fv_def_level = def_level, fv_count = 0 }
		= (Var bound_var, [{bind_src = match_expr, bind_dst = free_var} : opt_var_bind], var_heap, expr_heap)

	adjust_match_expression (Var var) expr_heap
		# (var_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
		= (Var { var & var_expr_ptr = var_expr_ptr }, expr_heap)
	adjust_match_expression match_expr expr_heap
		= (match_expr, expr_heap)

transfromPatternIntoBind mod_index def_level (AP_WildCard _) src_expr var_store expr_heap e_info cs
	= ([], var_store, expr_heap, e_info, cs)
transfromPatternIntoBind _ _ pattern src_expr var_store expr_heap e_info cs
	= ([], var_store, expr_heap, e_info, { cs & cs_error = checkError "<pattern>" " illegal node pattern" cs.cs_error})

checkLocalFunctions mod_index level (CollectedLocalDefs {loc_functions={ir_from,ir_to}}) fun_defs e_info heaps cs
	= checkFunctions mod_index level ir_from ir_to fun_defs e_info heaps cs

checkRhs free_vars rhs_alts rhs_locals e_input=:{ei_expr_level,ei_mod_index} e_state e_info cs
	# ei_expr_level = inc ei_expr_level
	  (loc_defs, (var_env, array_patterns), e_state, e_info, cs) = checkLhssOfLocalDefs ei_expr_level ei_mod_index rhs_locals e_state e_info cs
	  (es_fun_defs, e_info, heaps, cs)
	  		= checkLocalFunctions ei_mod_index ei_expr_level rhs_locals e_state.es_fun_defs e_info
	  			{ hp_var_heap = e_state.es_var_heap, hp_expression_heap = e_state.es_expr_heap, hp_type_heaps = e_state.es_type_heaps } cs
	  (rhs_expr, free_vars, e_state, e_info, cs) 
	  		= check_opt_guarded_alts free_vars rhs_alts { e_input & ei_expr_level = ei_expr_level }
	  			{ e_state & es_fun_defs = es_fun_defs, es_var_heap = heaps.hp_var_heap, es_expr_heap = heaps.hp_expression_heap,
					es_type_heaps = heaps.hp_type_heaps } e_info cs
	  (expr, free_vars, e_state, e_info, cs)
			= addArraySelections array_patterns rhs_expr free_vars e_input e_state e_info cs
	  (expr, free_vars, e_state, e_info, cs) = checkRhssAndTransformLocalDefs free_vars loc_defs expr e_input e_state e_info cs
	  (es_fun_defs, cs_symbol_table) = removeLocalsFromSymbolTable ei_expr_level var_env rhs_locals e_state.es_fun_defs cs.cs_symbol_table
	= (expr, free_vars, { e_state & es_fun_defs = es_fun_defs}, e_info, { cs & cs_symbol_table = cs_symbol_table })
where
	check_opt_guarded_alts free_vars (GuardedAlts guarded_alts default_expr) e_input e_state e_info cs
		# (let_vars_list, rev_guarded_exprs, last_expr_level, free_vars, e_state, e_info, cs)
				= check_guarded_expressions free_vars guarded_alts [] [] e_input e_state e_info cs
		  (default_expr, free_vars, e_state, e_info, cs)
		  		= check_default_expr free_vars default_expr { e_input & ei_expr_level = last_expr_level } e_state e_info cs
		  cs = { cs & cs_symbol_table = remove_seq_let_vars e_input.ei_expr_level let_vars_list cs.cs_symbol_table }
	  	  (result_expr, es_expr_heap) = convert_guards_to_cases rev_guarded_exprs default_expr e_state.es_expr_heap
	  	= (result_expr, free_vars, { e_state & es_expr_heap = es_expr_heap }, e_info, cs)
	check_opt_guarded_alts free_vars (UnGuardedExpr unguarded_expr) e_input e_state e_info cs
		= check_unguarded_expression free_vars unguarded_expr e_input e_state e_info cs

	check_default_expr free_vars (Yes default_expr) e_input e_state e_info cs
		# (expr, free_vars, e_state, e_info, cs) = check_unguarded_expression free_vars default_expr e_input e_state e_info cs
		= (Yes expr, free_vars, e_state, e_info, cs)
	check_default_expr free_vars No e_input e_state e_info cs
		= (No, free_vars, e_state, e_info, cs)
		
	convert_guards_to_cases [(let_binds, guard, expr)] result_expr es_expr_heap
		# (case_expr_ptr, es_expr_heap) = newPtr EI_Empty es_expr_heap
		  case_expr = Case { case_expr = guard, case_guards = BasicPatterns BT_Bool [{bp_value = (BVB True), bp_expr = expr}],
		  		case_default = result_expr, case_ident = No, case_info_ptr = case_expr_ptr }
		= build_sequential_lets let_binds case_expr es_expr_heap
	convert_guards_to_cases [(let_binds, guard, expr) : rev_guarded_exprs] result_expr es_expr_heap
		# (case_expr_ptr, es_expr_heap) = newPtr EI_Empty es_expr_heap
		  case_expr = Case { case_expr = guard, case_guards = BasicPatterns BT_Bool [{bp_value = (BVB True), bp_expr = expr}],
		  		case_default = result_expr, case_ident = No, case_info_ptr = case_expr_ptr }
		  (result_expr, es_expr_heap) = build_sequential_lets let_binds case_expr es_expr_heap
		= convert_guards_to_cases rev_guarded_exprs (Yes result_expr) es_expr_heap
	
	check_guarded_expressions free_vars [gexpr : gexprs] let_vars_list rev_guarded_exprs e_input e_state e_info cs
		# (let_vars_list, rev_guarded_exprs, ei_expr_level, free_vars, e_state, e_info, cs)
				= check_guarded_expression free_vars gexpr let_vars_list rev_guarded_exprs e_input e_state e_info cs
		= check_guarded_expressions free_vars gexprs let_vars_list rev_guarded_exprs { e_input & ei_expr_level = ei_expr_level } e_state e_info cs
	check_guarded_expressions free_vars [] let_vars_list rev_guarded_exprs {ei_expr_level} e_state e_info cs
		= (let_vars_list, rev_guarded_exprs, ei_expr_level, free_vars, e_state, e_info, cs)

	check_guarded_expression free_vars {alt_nodes,alt_guard,alt_expr}
			let_vars_list rev_guarded_exprs e_input=:{ei_expr_level,ei_mod_index} e_state e_info cs
		# (let_binds, let_vars_list, ei_expr_level, free_vars, e_state, e_info, cs) = check_sequential_lets free_vars alt_nodes let_vars_list
		  		{ e_input & ei_expr_level = inc ei_expr_level } e_state e_info cs
		  e_input = { e_input & ei_expr_level = ei_expr_level }
	  	  (guard, free_vars, e_state, e_info, cs) = checkExpression free_vars alt_guard e_input e_state e_info cs
		  (expr, free_vars, e_state, e_info, cs) = check_opt_guarded_alts free_vars alt_expr e_input e_state e_info cs
	  	= (let_vars_list, [(let_binds, guard, expr) : rev_guarded_exprs], ei_expr_level, free_vars, e_state, e_info,  cs )

	check_unguarded_expression free_vars {ewl_nodes,ewl_expr,ewl_locals} e_input=:{ei_expr_level,ei_mod_index} e_state e_info cs
		# this_expr_level = inc ei_expr_level
		  (loc_defs, (var_env, array_patterns), e_state, e_info, cs)
		 		= checkLhssOfLocalDefs this_expr_level ei_mod_index ewl_locals e_state e_info cs
		  (binds, let_vars_list, rhs_expr_level, free_vars, e_state, e_info, cs) = check_sequential_lets free_vars ewl_nodes [] { e_input & ei_expr_level = this_expr_level } e_state e_info cs
	  	  (expr, free_vars, e_state, e_info, cs) = checkExpression free_vars ewl_expr { e_input & ei_expr_level = rhs_expr_level } e_state e_info cs
		  (expr, free_vars, e_state, e_info, cs)
				= addArraySelections array_patterns expr free_vars e_input e_state e_info cs
		  cs = { cs & cs_symbol_table = remove_seq_let_vars rhs_expr_level let_vars_list cs.cs_symbol_table }
		  (seq_let_expr, es_expr_heap) = build_sequential_lets binds expr e_state.es_expr_heap
	  	  (expr, free_vars, e_state, e_info, cs)
				= checkRhssAndTransformLocalDefs free_vars loc_defs seq_let_expr e_input { e_state & es_expr_heap = es_expr_heap} e_info cs
	  	  (es_fun_defs, e_info, heaps, cs)
	  	  		= checkLocalFunctions ei_mod_index rhs_expr_level ewl_locals e_state.es_fun_defs e_info 
	  	  		{ hp_var_heap = e_state.es_var_heap, hp_expression_heap = e_state.es_expr_heap, hp_type_heaps = e_state.es_type_heaps } cs
		  (es_fun_defs, cs_symbol_table) = removeLocalsFromSymbolTable this_expr_level var_env ewl_locals es_fun_defs cs.cs_symbol_table
	  	= (expr, free_vars, {e_state & es_fun_defs = es_fun_defs, es_var_heap = heaps.hp_var_heap,
	  			es_expr_heap = heaps.hp_expression_heap, es_type_heaps = heaps.hp_type_heaps }, e_info, { cs & cs_symbol_table = cs_symbol_table} )
	
	remove_seq_let_vars level [] symbol_table
		= symbol_table
	remove_seq_let_vars level [let_vars : let_vars_list] symbol_table
		= remove_seq_let_vars (dec level) let_vars_list (removeLocalIdentsFromSymbolTable level let_vars symbol_table)
		
	check_sequential_lets free_vars [seq_let:seq_lets] let_vars_list e_input=:{ei_expr_level,ei_mod_index} e_state e_info cs
		# ei_expr_level = inc ei_expr_level
		  e_input = { e_input & ei_expr_level = ei_expr_level }
		  (src_expr, pattern_expr, (let_vars, array_patterns), free_vars, e_state, e_info, cs) = check_sequential_let free_vars seq_let e_input e_state e_info cs
	      (binds, loc_envs, max_expr_level, free_vars, e_state, e_info, cs)
	      		= check_sequential_lets free_vars seq_lets [let_vars : let_vars_list] e_input e_state e_info cs
		  (let_binds, es_var_heap, es_expr_heap, e_info, cs)
				= transfromPatternIntoBind ei_mod_index ei_expr_level pattern_expr src_expr e_state.es_var_heap e_state.es_expr_heap e_info cs
		  e_state = { e_state & es_var_heap = es_var_heap, es_expr_heap = es_expr_heap }
		  (strict_array_pattern_binds, lazy_array_pattern_binds, free_vars, e_state, e_info, cs)
				= foldSt (buildSelections e_input) array_patterns ([], [], free_vars, e_state, e_info, cs)
		  all_binds = [if seq_let.ndwl_strict (s, l) ([],let_binds), (strict_array_pattern_binds, lazy_array_pattern_binds) : binds]
		    with (l,s) = splitAt ((length let_binds)-1) let_binds
	    = (all_binds, loc_envs, max_expr_level, free_vars, e_state, e_info, cs)
	check_sequential_lets free_vars [] let_vars_list e_input=:{ei_expr_level} e_state e_info cs
		= ([], let_vars_list, ei_expr_level, free_vars, e_state, e_info, cs)

	check_sequential_let free_vars {ndwl_def={bind_src,bind_dst},ndwl_locals} e_input=:{ei_expr_level,ei_mod_index} e_state e_info cs
		# (loc_defs, (loc_env, loc_array_patterns), e_state, e_info, cs) = checkLhssOfLocalDefs ei_expr_level ei_mod_index ndwl_locals e_state e_info cs
		  (src_expr, free_vars, e_state, e_info, cs) = checkExpression free_vars bind_src e_input e_state e_info cs
		  (src_expr, free_vars, e_state, e_info, cs)
				= addArraySelections loc_array_patterns src_expr free_vars e_input e_state e_info cs
		  (src_expr, free_vars, e_state, e_info, cs) = checkRhssAndTransformLocalDefs free_vars loc_defs src_expr e_input e_state e_info cs
		  (es_fun_defs, e_info, {hp_var_heap,hp_expression_heap,hp_type_heaps}, cs)
				= checkLocalFunctions ei_mod_index ei_expr_level ndwl_locals e_state.es_fun_defs e_info
	  				{ hp_var_heap = e_state.es_var_heap, hp_expression_heap = e_state.es_expr_heap, hp_type_heaps = e_state.es_type_heaps } cs
	  	  (es_fun_defs, cs_symbol_table) = removeLocalsFromSymbolTable ei_expr_level loc_env ndwl_locals es_fun_defs cs.cs_symbol_table
		  (pattern, accus, {ps_fun_defs,ps_var_heap}, e_info, cs)
				= checkPattern bind_dst No { pi_def_level = ei_expr_level, pi_mod_index = ei_mod_index, pi_is_node_pattern = True } ([], []) 
					{ps_var_heap = hp_var_heap, ps_fun_defs = es_fun_defs } e_info { cs & cs_symbol_table = cs_symbol_table }
		  e_state = { e_state & es_var_heap = ps_var_heap, es_expr_heap = hp_expression_heap, es_type_heaps = hp_type_heaps, es_fun_defs = ps_fun_defs }
		= (src_expr, pattern, accus, free_vars, e_state, e_info, cs)
	
	build_sequential_lets :: ![(![Bind Expression FreeVar],![Bind Expression FreeVar])] !Expression !*ExpressionHeap -> (!Expression, !*ExpressionHeap)
	build_sequential_lets [] expr expr_heap
		= (expr, expr_heap)
	build_sequential_lets [(strict_binds, lazy_binds) : seq_lets] expr expr_heap
		# (let_expr, expr_heap) = build_sequential_lets seq_lets expr expr_heap
	  	= buildLetExpression strict_binds lazy_binds let_expr expr_heap


newVarId name = { id_name = name, id_info = nilPtr }

determinePatternVariable (Yes bind) var_heap
	= (bind, var_heap)
determinePatternVariable No var_heap
	# (new_info_ptr, var_heap) = newPtr VI_Empty var_heap
	= ({ bind_src = newVarId "_x", bind_dst = new_info_ptr }, var_heap)

convertSubPatterns [] result_expr var_store expr_heap opt_dynamics cs
	= ([], result_expr, var_store, expr_heap, opt_dynamics, cs)
convertSubPatterns [pattern : patterns] result_expr var_store expr_heap opt_dynamics cs
	# (var_args, result_expr, var_store, expr_heap, opt_dynamics, cs) = convertSubPatterns patterns result_expr var_store expr_heap opt_dynamics cs
	  (var_arg, result_expr, var_store, expr_heap, opt_dynamics, cs) = convertSubPattern pattern result_expr var_store expr_heap opt_dynamics cs
	= ([var_arg : var_args], result_expr, var_store, expr_heap, opt_dynamics, cs)

convertSubPattern (AP_Variable name var_info (Yes {bind_src,bind_dst})) result_expr var_store expr_heap opt_dynamics cs
	# (var_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
	  bound_var = { var_name = bind_src, var_info_ptr = bind_dst, var_expr_ptr = var_expr_ptr }
	  free_var = { fv_name = bind_src, fv_info_ptr = bind_dst, fv_def_level = NotALevel, fv_count = 0 }
	  (let_expr, expr_heap)	= buildLetExpression [] [{ bind_src = Var bound_var,
	  			bind_dst = { fv_name = name, fv_info_ptr = var_info, fv_def_level = NotALevel, fv_count = 0 }}] result_expr expr_heap
	= (free_var, let_expr, var_store, expr_heap, opt_dynamics, cs)
convertSubPattern (AP_Variable name var_info No) result_expr var_store expr_heap opt_dynamics cs
	= ({ fv_name = name, fv_info_ptr = var_info, fv_def_level = NotALevel, fv_count = 0 }, result_expr, var_store, expr_heap, opt_dynamics, cs)
convertSubPattern (AP_Algebraic cons_symbol type_index args opt_var) result_expr var_store expr_heap opt_dynamics cs
	# (var_args, result_expr, var_store, expr_heap, opt_dynamics, cs) = convertSubPatterns args result_expr var_store expr_heap opt_dynamics cs
	  type_symbol = { glob_module = cons_symbol.glob_module, glob_object = type_index }
	  case_guards = AlgebraicPatterns type_symbol [{ ap_symbol = cons_symbol, ap_vars = var_args, ap_expr = result_expr }]
	  ({bind_src,bind_dst}, var_store) = determinePatternVariable opt_var var_store
	  (var_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
	  (case_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
	= ({ fv_name = bind_src, fv_info_ptr = bind_dst, fv_def_level = NotALevel, fv_count = 0 },
			Case { case_expr = Var { var_name = bind_src, var_info_ptr = bind_dst, var_expr_ptr = var_expr_ptr },
				case_guards = case_guards, case_default = No, case_ident = No, case_info_ptr = case_expr_ptr }, var_store, expr_heap, opt_dynamics, cs)
convertSubPattern (AP_Basic basic_val opt_var) result_expr var_store expr_heap opt_dynamics cs
	# (basic_type, cs) = typeOfBasicValue basic_val cs
	  case_guards = BasicPatterns basic_type [{ bp_value = basic_val, bp_expr = result_expr }]
  	  ({bind_src,bind_dst}, var_store) = determinePatternVariable opt_var var_store
	  (var_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
	  (case_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
	= ({ fv_name = bind_src, fv_info_ptr = bind_dst, fv_def_level = NotALevel, fv_count = 0 },
			Case { case_expr = Var { var_name = bind_src, var_info_ptr = bind_dst, var_expr_ptr = var_expr_ptr },
				case_guards = case_guards, case_default = No, case_ident = No, case_info_ptr = case_expr_ptr}, var_store, expr_heap, opt_dynamics, cs)
convertSubPattern (AP_Dynamic pattern type opt_var) result_expr var_store expr_heap opt_dynamics cs
	# (var_arg, result_expr, var_store, expr_heap, opt_dynamics, cs) = convertSubPattern pattern result_expr var_store expr_heap opt_dynamics cs
 	  ({bind_src,bind_dst}, var_store) = determinePatternVariable opt_var var_store
	  (var_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
	  (type_case_info_ptr, expr_heap) = newPtr EI_Empty expr_heap
	  (dynamic_info_ptr, expr_heap) = newPtr (EI_DynamicType type opt_dynamics) expr_heap
 	  type_case_patterns = [{ dp_var = var_arg, dp_type = dynamic_info_ptr, dp_rhs = result_expr, dp_type_patterns_vars = [], dp_type_code = TCE_Empty }]
	= ({ fv_name = bind_src, fv_info_ptr = bind_dst, fv_def_level = NotALevel, fv_count = 0 },
			buildTypeCase (Var { var_name = bind_src, var_info_ptr = bind_dst, var_expr_ptr = var_expr_ptr }) type_case_patterns No type_case_info_ptr,
				var_store, expr_heap, [dynamic_info_ptr], cs)
convertSubPattern (AP_WildCard opt_var) result_expr var_store expr_heap opt_dynamics cs
 	# ({bind_src,bind_dst}, var_store) = determinePatternVariable opt_var var_store
	= ({ fv_name = bind_src, fv_info_ptr = bind_dst, fv_def_level = NotALevel, fv_count = 0  }, result_expr, var_store, expr_heap, opt_dynamics, cs)
convertSubPattern (AP_Empty _) result_expr var_store expr_heap opt_dynamics cs
	= convertSubPattern (AP_WildCard No) EE var_store expr_heap opt_dynamics cs

typeOfBasicValue :: !BasicValue !*CheckState -> (!BasicType, !*CheckState)
typeOfBasicValue (BVI _) cs = (BT_Int, cs)
typeOfBasicValue (BVC _) cs = (BT_Char, cs)
typeOfBasicValue (BVB _) cs = (BT_Bool, cs)
typeOfBasicValue (BVR _) cs = (BT_Real, cs)
typeOfBasicValue (BVS _) cs
	# ({glob_module,glob_object={ds_ident,ds_index,ds_arity}}, cs) = getPredefinedGlobalSymbol PD_StringType PD_PredefinedModule STE_Type 0 cs
	= (BT_String (TA (MakeTypeSymbIdent { glob_object = ds_index, glob_module = glob_module } ds_ident ds_arity) []), cs)


addArraySelections [] rhs_expr free_vars e_input e_state e_info cs
	= (rhs_expr, free_vars, e_state, e_info, cs)
addArraySelections array_patterns rhs_expr free_vars e_input e_state e_info cs
	# (let_strict_binds, let_lazy_binds, free_vars, e_state, e_info, cs)
			= foldSt (buildSelections e_input) array_patterns ([], [], free_vars, e_state, e_info, cs)
	  (let_expr_ptr, es_expr_heap)
	  		= newPtr EI_Empty e_state.es_expr_heap
	= ( Let {let_strict_binds = let_strict_binds, let_lazy_binds = let_lazy_binds,
				let_expr = rhs_expr, let_info_ptr = let_expr_ptr }
	  , free_vars
	  , { e_state & es_expr_heap = es_expr_heap}
	  , e_info
	  , cs
	  )

buildSelections e_input {ap_opt_var, ap_array_var, ap_selections}
					(strict_binds, lazy_binds, free_vars, e_state, e_info, cs)
	# (ap_array_var, [last_array_selection:lazy_binds], free_vars, e_state, e_info, cs)
			= foldSt (build_sc e_input) (reverse ap_selections) // reverse to make cycle-in-spine behaviour compatible to Clean 1.3
						(ap_array_var, lazy_binds, free_vars, e_state, e_info, cs)
	  (lazy_binds, e_state)
	  		= case ap_opt_var of
	  			Yes { bind_src = opt_var_ident, bind_dst = opt_var_var_info_ptr }
					# (bound_array_var, es_expr_heap) = allocate_bound_var ap_array_var e_state.es_expr_heap
					  free_var = { fv_name = opt_var_ident, fv_info_ptr = opt_var_var_info_ptr, fv_def_level = NotALevel,
					  				fv_count = 0 }
	  				-> ([{ bind_dst = free_var, bind_src = Var bound_array_var }: lazy_binds],
	  					{ e_state & es_expr_heap = es_expr_heap })
	  			no	-> (lazy_binds, e_state)
	= ([last_array_selection:strict_binds], lazy_binds, free_vars, e_state, e_info, cs)
  where
	build_sc e_input {bind_dst=parsed_index_exprs, bind_src=array_element_var} (ap_array_var, binds, free_vars, e_state, e_info, cs)
		# (var_for_uselect_result, es_var_heap)
				= allocate_free_var { id_name = "_x", id_info = nilPtr } e_state.es_var_heap
		  (new_array_var, es_var_heap)
		  		= allocate_free_var ap_array_var.fv_name es_var_heap
		  (bound_array_var, es_expr_heap)
		  		= allocate_bound_var ap_array_var e_state.es_expr_heap
		  (bound_var_for_uselect_result, es_expr_heap)
		  		= allocate_bound_var var_for_uselect_result es_expr_heap
		  dimension
		  		= length parsed_index_exprs
		  (new_expr_ptrs, es_expr_heap)
		  		= mapSt newPtr (repeatn dimension EI_Empty) es_expr_heap
		  (tuple_cons, cs)
		  		= getPredefinedGlobalSymbol (GetTupleConsIndex 2) PD_PredefinedModule STE_Constructor 2 cs
		  (glob_select_symb, opt_tuple_type, cs)
		  		= case dimension of
		  			1	# (unq_select_symb, cs) = getPredefinedGlobalSymbol PD_UnqArraySelectFun PD_StdArray STE_Member 2 cs
		  				-> (unq_select_symb, No, cs)
		  			_	# (select_symb, cs) = getPredefinedGlobalSymbol PD_ArraySelectFun PD_StdArray STE_Member 2 cs
						  (tuple_type, cs) = getPredefinedGlobalSymbol (GetTupleTypeIndex 2) PD_PredefinedModule STE_Type 2 cs
		  				-> (select_symb, Yes tuple_type, cs)
		  e_state
		  		= { e_state & es_var_heap = es_var_heap, es_expr_heap = es_expr_heap }
		  (index_exprs, (free_vars, e_state, e_info, cs))
		  		= mapSt (check_index_expr e_input) parsed_index_exprs (free_vars, e_state, e_info, cs)
		  selections
		  		= [ ArraySelection glob_select_symb new_expr_ptr index_expr \\ new_expr_ptr<-new_expr_ptrs & index_expr<-index_exprs ]
		= (	new_array_var
		  ,	[ {bind_dst = var_for_uselect_result, bind_src = Selection opt_tuple_type (Var bound_array_var) selections}
		    , {bind_dst = new_array_var, bind_src = TupleSelect tuple_cons.glob_object 1 (Var bound_var_for_uselect_result)}
		    , {bind_dst = array_element_var, bind_src = TupleSelect tuple_cons.glob_object 0 (Var bound_var_for_uselect_result)}
		  	: binds
			]
		  , free_vars
		  , e_state
		  , e_info 
		  , cs
		  )

	check_index_expr e_input parsed_index_expr (free_vars, e_state, e_info, cs)
		# (index_expr, free_vars, e_state, e_info, cs) = checkExpression free_vars parsed_index_expr e_input e_state e_info cs
		= (index_expr, (free_vars, e_state, e_info, cs))
		
allocate_free_var ident var_heap
	# (new_var_info_ptr, var_heap) = newPtr VI_Empty var_heap
	= ({ fv_def_level = NotALevel, fv_name = ident, fv_info_ptr = new_var_info_ptr,	fv_count = 0 }, var_heap)

checkFunctionBodies (ParsedBody [{pb_args,pb_rhs={rhs_alts,rhs_locals}} : bodies]) e_input=:{ei_expr_level,ei_mod_index}
		e_state=:{es_var_heap, es_fun_defs} e_info cs
	# (aux_patterns, (var_env, array_patterns), {ps_var_heap, ps_fun_defs}, e_info, cs)
			= check_patterns pb_args {pi_def_level = ei_expr_level, pi_mod_index = ei_mod_index, pi_is_node_pattern = False} ([], [])
							{ps_var_heap = es_var_heap, ps_fun_defs = es_fun_defs} e_info cs 
	  (rhs_expr, free_vars, e_state, e_info, cs)
	  		= checkRhs [] rhs_alts rhs_locals e_input { e_state & es_var_heap = ps_var_heap, es_fun_defs = ps_fun_defs } e_info cs
	  (dynamics_in_rhs, e_state)
	  		= e_state!es_dynamics
	  (expr_with_array_selections, free_vars, e_state=:{es_var_heap}, e_info, cs)
			= addArraySelections array_patterns rhs_expr free_vars e_input e_state e_info cs
	  cs_symbol_table = removeLocalIdentsFromSymbolTable ei_expr_level var_env cs.cs_symbol_table
	  (cb_args, es_var_heap) = mapSt determine_function_arg aux_patterns es_var_heap
	  (rhss, free_vars, e_state=:{es_dynamics,es_expr_heap,es_var_heap}, e_info, cs)
	  		= check_function_bodies free_vars cb_args bodies e_input { e_state & es_dynamics = [], es_var_heap = es_var_heap } e_info
	  								{ cs & cs_symbol_table = cs_symbol_table }
	  (rhs, es_var_heap, es_expr_heap, dynamics_in_patterns, cs)
	  		= transform_patterns_into_cases aux_patterns cb_args expr_with_array_selections es_var_heap es_expr_heap
	  										dynamics_in_rhs cs
	= (CheckedBody { cb_args = cb_args, cb_rhs = [rhs : rhss] }, free_vars,
		{ e_state & es_var_heap = es_var_heap, es_expr_heap = es_expr_heap, es_dynamics = dynamics_in_patterns ++ es_dynamics }, e_info, cs)
where
	check_patterns [pattern : patterns] p_input accus var_store e_info cs
		# (aux_pat, accus, var_store, e_info, cs) = checkPattern pattern No p_input accus var_store e_info cs
		  (aux_pats, accus, var_store, e_info, cs) = check_patterns patterns p_input accus var_store e_info cs
		= ([aux_pat : aux_pats], accus, var_store, e_info, cs)
	check_patterns [] p_input accus var_store e_info cs
		= ([], accus, var_store, e_info, cs)

	determine_function_arg (AP_Variable name var_info (Yes {bind_src, bind_dst})) var_store
		= ({ fv_name = bind_src, fv_info_ptr = bind_dst, fv_def_level = NotALevel, fv_count = 0 }, var_store)
	determine_function_arg (AP_Variable name var_info No) var_store
		= ({ fv_name = name, fv_info_ptr = var_info, fv_def_level = NotALevel, fv_count = 0 }, var_store)
	determine_function_arg (AP_Algebraic _ _ _ opt_var) var_store
		# ({bind_src,bind_dst}, var_store) = determinePatternVariable opt_var var_store
		= ({ fv_name = bind_src, fv_info_ptr = bind_dst, fv_def_level = NotALevel, fv_count = 0 }, var_store)
	determine_function_arg (AP_Basic _ opt_var) var_store
		# ({bind_src,bind_dst}, var_store) = determinePatternVariable opt_var var_store
		= ({ fv_name = bind_src, fv_info_ptr = bind_dst, fv_def_level = NotALevel, fv_count = 0 }, var_store)
	determine_function_arg (AP_Dynamic _ _ opt_var) var_store
		# ({bind_src,bind_dst}, var_store) = determinePatternVariable opt_var var_store
		= ({ fv_name = bind_src, fv_info_ptr = bind_dst, fv_def_level = NotALevel, fv_count = 0 }, var_store)
	determine_function_arg _ var_store
		# ({bind_src,bind_dst}, var_store) = determinePatternVariable No var_store
		= ({ fv_name = bind_src, fv_info_ptr = bind_dst, fv_def_level = NotALevel, fv_count = 0 }, var_store)
	
	check_function_bodies free_vars fun_args [{pb_args,pb_rhs={rhs_alts,rhs_locals}} : bodies] e_input=:{ei_expr_level,ei_mod_index}
			e_state=:{es_var_heap,es_fun_defs} e_info cs
		# (aux_patterns, (var_env, array_patterns), {ps_var_heap, ps_fun_defs}, e_info, cs)
				= check_patterns pb_args { pi_def_level = ei_expr_level, pi_mod_index = ei_mod_index, pi_is_node_pattern = False } ([], [])
					{ps_var_heap = es_var_heap, ps_fun_defs = es_fun_defs} e_info cs
		  e_state = { e_state & es_var_heap = ps_var_heap, es_fun_defs = ps_fun_defs}
		  (rhs_expr, free_vars, e_state, e_info, cs) = checkRhs free_vars rhs_alts rhs_locals e_input e_state e_info cs
		  (rhs_expr, free_vars, e_state=:{es_dynamics=dynamics_in_rhs}, e_info, cs)
				= addArraySelections array_patterns rhs_expr free_vars e_input e_state e_info cs
	 	  cs_symbol_table = removeLocalIdentsFromSymbolTable ei_expr_level var_env cs.cs_symbol_table
		  (rhs_exprs, free_vars, e_state=:{es_dynamics,es_expr_heap,es_var_heap}, e_info, cs)
		  		= check_function_bodies free_vars fun_args bodies e_input { e_state & es_dynamics = [] } e_info { cs & cs_symbol_table = cs_symbol_table }
		  (rhs_expr, es_var_heap, es_expr_heap, dynamics_in_patterns, cs)
		  		= transform_patterns_into_cases aux_patterns fun_args rhs_expr es_var_heap es_expr_heap dynamics_in_rhs cs
		= ([rhs_expr : rhs_exprs], free_vars, { e_state & es_var_heap = es_var_heap, es_expr_heap = es_expr_heap,
				es_dynamics = dynamics_in_patterns ++ es_dynamics }, e_info, cs)
	check_function_bodies free_vars fun_args [] e_input e_state e_info cs
		= ([], free_vars, e_state, e_info, cs) 
		
	transform_patterns_into_cases [pattern : patterns] [fun_arg : fun_args] result_expr var_store expr_heap opt_dynamics cs
		# (patterns_expr, var_store, expr_heap, opt_dynamics, cs)
				= transform_succeeding_patterns_into_cases patterns fun_args result_expr var_store expr_heap opt_dynamics cs
		= transform_pattern_into_cases pattern fun_arg patterns_expr var_store expr_heap opt_dynamics cs
	where
		transform_succeeding_patterns_into_cases [] _ result_expr var_store expr_heap opt_dynamics cs
			= (result_expr, var_store, expr_heap, opt_dynamics, cs)
		transform_succeeding_patterns_into_cases [pattern : patterns] [fun_arg : fun_args] result_expr var_store expr_heap opt_dynamics cs
			# (patterns_expr, var_store, expr_heap, opt_dynamics, cs)
				= transform_succeeding_patterns_into_cases patterns fun_args result_expr var_store expr_heap opt_dynamics cs
			= transform_pattern_into_cases pattern fun_arg patterns_expr var_store expr_heap opt_dynamics cs
	transform_patterns_into_cases [] _ result_expr var_store expr_heap opt_dynamics cs
		= (result_expr, var_store, expr_heap, opt_dynamics, cs)
		
	transform_pattern_into_cases :: !AuxiliaryPattern !FreeVar !Expression !*VarHeap !*ExpressionHeap ![DynamicPtr] !*CheckState
		-> (!Expression, !*VarHeap, !*ExpressionHeap, ![DynamicPtr], !*CheckState)
	transform_pattern_into_cases (AP_Variable name var_info opt_var) fun_arg=:{fv_info_ptr,fv_name} result_expr var_store expr_heap opt_dynamics cs
		= case opt_var of
			Yes {bind_src, bind_dst}
				| bind_dst == fv_info_ptr
					# (var_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
					  (let_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
					-> (Let { let_lazy_binds = [], let_strict_binds = [
								{ bind_src = Var { var_name = fv_name, var_info_ptr = fv_info_ptr, var_expr_ptr = var_expr_ptr },
									bind_dst = { fv_name = name, fv_info_ptr = var_info, fv_def_level = NotALevel, fv_count = 0 }}],
							  let_expr = result_expr, let_info_ptr = let_expr_ptr}, var_store, expr_heap, opt_dynamics, cs)
					# (var_expr_ptr1, expr_heap) = newPtr EI_Empty expr_heap
					  (var_expr_ptr2, expr_heap) = newPtr EI_Empty expr_heap
					  (let_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
					-> (Let { let_lazy_binds = [], let_strict_binds = [
								{ bind_src = Var { var_name = fv_name, var_info_ptr = fv_info_ptr, var_expr_ptr = var_expr_ptr1 },
									bind_dst = { fv_name = name, fv_info_ptr = var_info, fv_def_level = NotALevel, fv_count = 0 }},
								{ bind_src = Var { var_name = fv_name, var_info_ptr = fv_info_ptr, var_expr_ptr = var_expr_ptr2 },
									bind_dst = { fv_name = bind_src, fv_info_ptr = bind_dst, fv_def_level = NotALevel, fv_count = 0 }}],
							  let_expr = result_expr, let_info_ptr = let_expr_ptr}, var_store, expr_heap, opt_dynamics, cs)
			No
				| var_info == fv_info_ptr
					-> (result_expr, var_store, expr_heap, opt_dynamics, cs)
					# (var_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
					  (let_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
					-> (Let { let_lazy_binds = [], let_strict_binds =
									[{ bind_src = Var { var_name = fv_name, var_info_ptr = fv_info_ptr, var_expr_ptr = var_expr_ptr },
										 bind_dst = { fv_name = name, fv_info_ptr = var_info, fv_def_level = NotALevel, fv_count = 0 }}],
							  let_expr = result_expr, let_info_ptr = let_expr_ptr}, var_store, expr_heap, opt_dynamics, cs)
	transform_pattern_into_cases (AP_Algebraic cons_symbol type_index args opt_var) fun_arg result_expr var_store expr_heap opt_dynamics cs
		# (var_args, result_expr, var_store, expr_heap, opt_dynamics, cs) = convertSubPatterns args result_expr var_store expr_heap opt_dynamics cs
		  type_symbol = {glob_module = cons_symbol.glob_module, glob_object = type_index}
	  	  (act_var, result_expr, expr_heap) = transform_pattern_variable fun_arg opt_var result_expr expr_heap
	  	  case_guards = AlgebraicPatterns type_symbol [{ ap_symbol = cons_symbol, ap_vars = var_args, ap_expr = result_expr }]
		  (case_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
		= (Case { case_expr = act_var, case_guards = case_guards, case_default = No, case_ident = No, case_info_ptr = case_expr_ptr },
				var_store, expr_heap, opt_dynamics, cs)	
	transform_pattern_into_cases (AP_Basic basic_val opt_var) fun_arg result_expr var_store expr_heap opt_dynamics cs
		# (basic_type, cs) = typeOfBasicValue basic_val cs
	  	  (act_var, result_expr, expr_heap) = transform_pattern_variable fun_arg opt_var result_expr expr_heap
		  case_guards = BasicPatterns basic_type [{ bp_value = basic_val, bp_expr = result_expr }]
		  (case_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
		= (Case { case_expr = act_var, case_guards = case_guards, case_default = No, case_ident = No, case_info_ptr = case_expr_ptr },
			var_store, expr_heap, opt_dynamics, cs)	
	transform_pattern_into_cases (AP_Dynamic pattern type opt_var) fun_arg result_expr var_store expr_heap opt_dynamics cs
		# (var_arg, result_expr, var_store, expr_heap, opt_dynamics, cs) = convertSubPattern pattern result_expr var_store expr_heap opt_dynamics cs
		  (type_case_info_ptr, expr_heap) = newPtr EI_Empty expr_heap
		  (dynamic_info_ptr, expr_heap) = newPtr (EI_DynamicType type opt_dynamics) expr_heap
	  	  (act_var, result_expr, expr_heap) = transform_pattern_variable fun_arg opt_var result_expr expr_heap
	  	  type_case_patterns = [{ dp_var = var_arg, dp_type	= dynamic_info_ptr,	dp_rhs = result_expr, dp_type_patterns_vars = [], dp_type_code = TCE_Empty }]
		= (buildTypeCase act_var type_case_patterns No type_case_info_ptr, var_store, expr_heap, [dynamic_info_ptr], cs)	
	transform_pattern_into_cases (AP_WildCard _) fun_arg result_expr var_store expr_heap opt_dynamics cs
		= (result_expr, var_store, expr_heap, opt_dynamics, cs)	
	transform_pattern_into_cases (AP_Empty name) fun_arg result_expr var_store expr_heap opt_dynamics cs
		= (result_expr, var_store, expr_heap, opt_dynamics, cs)

	transform_pattern_variable :: !FreeVar !(Optional !(Bind Ident VarInfoPtr)) !Expression !*ExpressionHeap
		-> (!Expression, !Expression, !*ExpressionHeap)
	transform_pattern_variable {fv_info_ptr,fv_name} (Yes {bind_src,bind_dst}) result_expr expr_heap
		| bind_dst == fv_info_ptr
			# (var_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
			= (Var { var_name = fv_name, var_info_ptr = fv_info_ptr, var_expr_ptr = var_expr_ptr }, result_expr, expr_heap)
			# (var_expr_ptr1, expr_heap) = newPtr EI_Empty expr_heap
			  (var_expr_ptr2, expr_heap) = newPtr EI_Empty expr_heap
			  (let_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
			= (Var { var_name = fv_name, var_info_ptr = fv_info_ptr, var_expr_ptr = var_expr_ptr1 },
						Let { let_strict_binds = [], let_lazy_binds =
						 		[{ bind_src = Var { var_name = fv_name, var_info_ptr = fv_info_ptr, var_expr_ptr = var_expr_ptr2 },
											bind_dst = { fv_name = bind_src, fv_info_ptr = bind_dst, fv_def_level = NotALevel, fv_count = 0 }}],
							  let_expr = result_expr, let_info_ptr = let_expr_ptr}, expr_heap)
	transform_pattern_variable {fv_info_ptr,fv_name} No result_expr expr_heap
		# (var_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
		= (Var { var_name = fv_name, var_info_ptr = fv_info_ptr, var_expr_ptr = var_expr_ptr }, result_expr, expr_heap)

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
	# {fun_symb,fun_pos,fun_body,fun_type} = fun_def
	  position = newPosition fun_symb fun_pos
	  cs = { cs & cs_error = pushErrorAdmin position cs_error }
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

			
checkFunctions :: !Index !Level !Index !Index !*{#FunDef} !*ExpressionInfo !*Heaps !*CheckState -> (!*{#FunDef}, !*ExpressionInfo, !*Heaps, !*CheckState)
checkFunctions mod_index level from_index to_index fun_defs e_info heaps cs
	| from_index == to_index
		= (fun_defs, e_info, heaps, cs)
		# (fun_defs, e_info, heaps, cs) = checkFunction mod_index from_index level fun_defs e_info heaps cs
		= checkFunctions mod_index level (inc from_index) to_index fun_defs e_info heaps cs

checkMacros ::  !Index !IndexRange !*{#FunDef} !*ExpressionInfo !*Heaps !*CheckState
	-> (!*{#FunDef}, !*ExpressionInfo, !*Heaps, !*CheckState);
checkMacros mod_index range fun_defs e_info=:{ef_is_macro_fun=ef_is_macro_fun_old} heaps cs
	# (fun_defs, e_info, heaps=:{hp_var_heap, hp_expression_heap}, cs=:{cs_symbol_table,cs_error})
			= checkFunctions mod_index cGlobalScope range.ir_from range.ir_to fun_defs { e_info & ef_is_macro_fun=True } heaps cs
	  (e_info=:{ef_modules}) = { e_info & ef_is_macro_fun=ef_is_macro_fun_old }
	  (fun_defs, ef_modules, hp_var_heap, hp_expression_heap, cs_symbol_table, cs_error)
	  		= partitionateMacros range mod_index fun_defs ef_modules hp_var_heap hp_expression_heap cs_symbol_table cs_error
	= (fun_defs, { e_info & ef_modules = ef_modules }, {heaps &  hp_var_heap = hp_var_heap, hp_expression_heap = hp_expression_heap},
			{ cs & cs_symbol_table = cs_symbol_table, cs_error = cs_error })

checkInstanceBodies :: !IndexRange !*{#FunDef} !*ExpressionInfo !*Heaps !*CheckState -> (!*{#FunDef},!*ExpressionInfo,!*Heaps, !*CheckState);
checkInstanceBodies {ir_from, ir_to} fun_defs e_info heaps cs
	= checkFunctions cIclModIndex cGlobalScope ir_from ir_to fun_defs e_info heaps cs

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
			

IsMainDclMod is_dcl module_index :== is_dcl && module_index == cIclModIndex


checkCommonDefinitions :: !Bool !Index !*CommonDefs !*{# DclModule} !*TypeHeaps !*VarHeap !*CheckState
	-> (!*CommonDefs, !*{# DclModule}, !*TypeHeaps,  !*VarHeap, !*CheckState)
checkCommonDefinitions is_dcl module_index common modules type_heaps var_heap cs
	# (com_type_defs, com_cons_defs, com_selector_defs, modules, var_heap, type_heaps, cs)
			= checkTypeDefs (IsMainDclMod is_dcl module_index) common.com_type_defs module_index
							common.com_cons_defs common.com_selector_defs modules var_heap type_heaps cs
	  (com_class_defs, com_member_defs, com_type_defs, modules, type_heaps, cs)
	  		= checkTypeClasses 0 module_index common.com_class_defs common.com_member_defs com_type_defs modules type_heaps cs
	  (com_member_defs, com_type_defs, com_class_defs, modules, type_heaps, var_heap, cs)
	  		= checkMemberTypes module_index com_member_defs com_type_defs com_class_defs modules type_heaps var_heap cs
	  (com_instance_defs, com_type_defs, com_class_defs, com_member_defs, modules, type_heaps, cs)
	  		= checkInstanceDefs module_index common.com_instance_defs com_type_defs com_class_defs com_member_defs modules type_heaps cs
	  (com_class_defs, modules, new_type_defs, new_selector_defs, new_cons_defs, th_vars, var_heap, cs)
	  	= createClassDictionaries module_index com_class_defs modules (size com_type_defs) (size com_selector_defs)
	  		(size com_cons_defs) type_heaps.th_vars var_heap cs
	  com_type_defs = { type_def \\ type_def <- [ type_def \\ type_def <-: com_type_defs ] ++ new_type_defs }
	  com_selector_defs = { sel_def \\ sel_def <- [ sel_def \\ sel_def <-: com_selector_defs ] ++ new_selector_defs }
	  com_cons_defs = { cons_def \\ cons_def <- [ cons_def \\ cons_def <-: com_cons_defs ] ++ new_cons_defs }
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
	  (size, defs) = foldSt class_def_to_dcl def_classes (0, defs)
	  sizes = { sizes & [cClassDefs] = size }
	  (size, defs) = foldSt instance_def_to_dcl def_instances (0, defs)
	  sizes = { sizes & [cInstanceDefs] = size }
	  (size, defs) = foldSt member_def_to_dcl def_members (0, defs)
	  sizes = { sizes & [cMemberDefs] = size }
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
	instance_def_to_dcl {ins_ident, ins_pos} (dcl_index, decls) 
		= (inc dcl_index, [{ dcl_ident = ins_ident, dcl_pos = ins_pos, dcl_kind = STE_Instance, dcl_index = dcl_index } : decls]) 

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

combineDclAndIclModule MK_Main modules icl_decl_symbols icl_definitions icl_sizes cs
	= (modules, icl_decl_symbols, icl_definitions, icl_sizes, cs)
combineDclAndIclModule _ modules icl_decl_symbols icl_definitions icl_sizes cs
	# (dcl_mod=:{dcl_declared={dcls_local},dcl_macros, dcl_sizes, dcl_common}, modules) =  modules![cIclModIndex]

	  cs = addGlobalDefinitionsToSymbolTable icl_decl_symbols cs

	  (moved_dcl_defs, conversion_table, icl_sizes, icl_decl_symbols, cs)
			= foldSt (add_to_conversion_table dcl_macros.ir_from) dcls_local ([], { createArray size NoIndex \\ size <-: dcl_sizes }, icl_sizes, icl_decl_symbols, cs)
	  (new_type_defs, new_class_defs, new_cons_defs, new_selector_defs, new_member_defs, cs)
			= foldSt (add_dcl_definition dcl_common) moved_dcl_defs ([], [], [], [], [], cs)

	  cs_symbol_table = removeDeclarationsFromSymbolTable icl_decl_symbols cGlobalScope cs.cs_symbol_table

	=	( { modules & [cIclModIndex] = { dcl_mod & dcl_conversions = Yes conversion_table }}
		, icl_decl_symbols
		, { icl_definitions
				& def_types			= my_append icl_definitions.def_types new_type_defs
				, def_constructors	= my_append icl_definitions.def_constructors new_cons_defs
				, def_selectors		= my_append icl_definitions.def_selectors new_selector_defs
				, def_classes		= my_append icl_definitions.def_classes new_class_defs
				, def_members		= my_append icl_definitions.def_members new_member_defs
		  }
		, icl_sizes
		, { cs & cs_symbol_table = cs_symbol_table }
		)

where
	add_to_conversion_table first_macro_index decl=:{dcl_ident=dcl_ident=:{id_info},dcl_kind,dcl_index,dcl_pos}
			(moved_dcl_defs, conversion_table, icl_sizes, icl_defs, cs)
		# (entry=:{ste_kind,ste_index,ste_def_level}, cs_symbol_table) = readPtr id_info cs.cs_symbol_table
		| ste_kind == STE_Empty
			# def_index = toInt dcl_kind
			| can_be_only_in_dcl def_index
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


checkModule :: !ScannedModule !IndexRange ![FunDef] !ScannedModule !ScannedModule ![ScannedModule] !*PredefinedSymbols !*SymbolTable !*File
	-> (!Bool, !*IclModule, *{# DclModule}, *{! Group}, !(Optional {# Index}), !*Heaps, !*PredefinedSymbols, !*SymbolTable, *File)
checkModule {mod_type,mod_name,mod_imports,mod_imported_objects,mod_defs = cdefs} icl_global_function_range fun_defs dcl_mod pre_def_mod scanned_modules predef_symbols symbol_table err_file
	# error = {ea_file = err_file, ea_loc = [], ea_ok = True }

	  first_inst_index = length fun_defs
	  
	  (inst_fun_defs, def_instances) = convert_class_instances cdefs.def_instances first_inst_index
	  icl_functions = { next_fun \\ next_fun <- fun_defs ++ inst_fun_defs }
	  cdefs = { cdefs & def_instances = def_instances }
	#! nr_of_functions = size icl_functions

	# sizes_and_local_defs = collectCommonfinitions cdefs
	  (icl_functions, sizes_and_local_defs) = collectGlobalFunctions cFunctionDefs icl_global_function_range.ir_from icl_global_function_range.ir_to icl_functions sizes_and_local_defs
	  (icl_functions, (sizes, local_defs)) = collectMacros cdefs.def_macros icl_functions sizes_and_local_defs

	  (scanned_modules, icl_functions, cs)
	  		= add_modules_to_symbol_table [ dcl_mod, pre_def_mod : scanned_modules ] 0 icl_functions
	  				{ cs_symbol_table = symbol_table, cs_predef_symbols = predef_symbols, cs_error = error, cs_needed_modules = 0 }
	  
	  init_dcl_modules = [ initialDclModule scanned_module \\ scanned_module <- scanned_modules ]
	  (icl_sizes_without_added_dcl_defs, sizes) = memcpy sizes
	  (dcl_modules, local_defs, cdefs, _, cs)
	  		= combineDclAndIclModule mod_type { dcl_module \\ dcl_module <- init_dcl_modules } local_defs cdefs sizes cs

	  icl_common = createCommonDefinitions cdefs

	  heaps = { hp_var_heap = newHeap, hp_expression_heap = newHeap, hp_type_heaps = { th_vars = newHeap, th_attrs = newHeap }}

	  (dcl_modules, icl_functions, heaps, cs)
	  		= check_predefined_module pre_def_mod.mod_name dcl_modules icl_functions heaps cs

	  iinfo = {	ii_modules = dcl_modules, ii_funs_and_macros = icl_functions, ii_next_num = 0, ii_deps = [] }

	  (iinfo, heaps, cs) = check_dcl_module iinfo heaps cs

	  (_, {ii_modules,ii_funs_and_macros = icl_functions}, heaps, cs) = checkImports mod_imports iinfo heaps cs

	  cs = { cs & cs_needed_modules = 0 }
	  
	  (nr_of_modules, (f_consequences, ii_modules, icl_functions, hp_expression_heap, cs))
	  	= check_completeness_of_all_dcl_modules ii_modules icl_functions heaps.hp_expression_heap cs

	  (dcls_explicit, dcl_modules, cs)	= addImportsToSymbolTable mod_imports [] ii_modules cs
	  cs			    				= addGlobalDefinitionsToSymbolTable local_defs cs

	  (_, dcl_modules, icl_functions, hp_expression_heap, cs)
		= check_completeness_of_module nr_of_modules dcls_explicit (mod_name.id_name+++".icl")
							 (f_consequences, dcl_modules, icl_functions, hp_expression_heap, cs)

	  heaps	= { heaps & hp_expression_heap=hp_expression_heap }

	  (icl_common, dcl_modules, hp_type_heaps, hp_var_heap, cs)
	  		= checkCommonDefinitions cIsNotADclModule cIclModIndex icl_common dcl_modules heaps.hp_type_heaps heaps.hp_var_heap cs
	  
	  (instance_types, icl_common, dcl_modules, hp_var_heap, hp_type_heaps, cs)
	  		= checkInstances cIclModIndex icl_common dcl_modules hp_var_heap hp_type_heaps cs

	  heaps = { heaps & hp_type_heaps = hp_type_heaps, hp_var_heap = hp_var_heap }

	  e_info = { ef_type_defs = icl_common.com_type_defs, ef_selector_defs = icl_common.com_selector_defs, ef_class_defs = icl_common.com_class_defs, 
	  			  ef_cons_defs = icl_common.com_cons_defs, ef_member_defs = icl_common.com_member_defs, ef_modules = dcl_modules,
					ef_is_macro_fun = False }

	  (icl_functions, e_info, heaps, cs) = checkMacros cIclModIndex cdefs.def_macros icl_functions e_info heaps cs
	  (icl_functions, e_info, heaps, cs) = checkFunctions cIclModIndex cGlobalScope icl_global_function_range.ir_from icl_global_function_range.ir_to icl_functions e_info heaps cs

	  cs = check_start_rule mod_type mod_name icl_global_function_range cs
	  cs = check_needed_modules_are_imported mod_name ".icl" cs

	  (icl_functions, e_info, heaps, {cs_symbol_table, cs_predef_symbols, cs_error})
	  	= checkInstanceBodies {ir_from = first_inst_index, ir_to = nr_of_functions} icl_functions e_info heaps cs

	  (icl_imported, dcl_modules, cs_symbol_table) = retrieveImportsFromSymbolTable mod_imports [] e_info.ef_modules cs_symbol_table
	| cs_error.ea_ok
		# {hp_var_heap,hp_type_heaps=hp_type_heaps=:{th_vars},hp_expression_heap} = heaps
		  (spec_functions, dcl_modules, class_instances, icl_functions, new_nr_of_functions, dcl_icl_conversions, var_heap, th_vars, expr_heap)
				= collect_specialized_functions_in_dcl_module dcl_modules icl_common.com_instance_defs icl_functions nr_of_functions
							hp_var_heap th_vars hp_expression_heap
		  icl_instances				= {ir_from = first_inst_index,	ir_to = nr_of_functions}
		  icl_specials				= {ir_from = nr_of_functions,	ir_to = new_nr_of_functions}
		  icl_functions = copy_instance_types instance_types { icl_fun \\ icl_fun <- [ icl_fun \\ icl_fun <-: icl_functions ] ++ spec_functions }

		  (dcl_modules, class_instances, icl_functions, cs_predef_symbols)
		  		= adjust_instance_types_of_array_functions_in_std_array_icl dcl_modules class_instances icl_functions cs_predef_symbols

		  (untransformed_fun_bodies, icl_functions) = copy_bodies icl_functions
		  (groups, icl_functions, dcl_modules, var_heap, expr_heap, cs_symbol_table, cs_error)
		  		= partitionateAndLiftFunctions [icl_global_function_range, icl_instances] cIclModIndex icl_functions
		  			dcl_modules var_heap expr_heap cs_symbol_table cs_error
		  icl_common	= { icl_common & com_type_defs = e_info.ef_type_defs, com_selector_defs = e_info.ef_selector_defs, com_class_defs = e_info.ef_class_defs,
			  	 			  com_cons_defs = e_info.ef_cons_defs, com_member_defs = e_info.ef_member_defs, com_instance_defs = class_instances }	  			  
		  icl_mod		= { icl_name = mod_name, icl_functions = icl_functions, icl_common = icl_common, icl_instances = icl_instances, icl_specials = icl_specials,
							icl_imported_objects = mod_imported_objects,
	  			  			icl_declared = {dcls_local = local_defs, dcls_import = icl_imported, dcls_explicit = dcls_explicit} }

		  heaps = { heaps & hp_var_heap = var_heap, hp_expression_heap = expr_heap, hp_type_heaps = {hp_type_heaps & th_vars = th_vars}}

		  (dcl_modules, icl_mod, heaps, cs_error)
		  		= compareDefImp icl_sizes_without_added_dcl_defs untransformed_fun_bodies dcl_modules icl_mod heaps cs_error

		= (cs_error.ea_ok, icl_mod, dcl_modules, groups, dcl_icl_conversions, heaps, cs_predef_symbols, cs_symbol_table, cs_error.ea_file)
		# icl_common	= { icl_common & com_type_defs = e_info.ef_type_defs, com_selector_defs = e_info.ef_selector_defs, com_class_defs = e_info.ef_class_defs,
			  	 			  com_cons_defs = e_info.ef_cons_defs, com_member_defs = e_info.ef_member_defs }	  			  
		  icl_mod		= { icl_name = mod_name, icl_functions = icl_functions, icl_common = icl_common,
		  					icl_instances = {ir_from = first_inst_index, ir_to = nr_of_functions},
		  					icl_specials = {ir_from = nr_of_functions, ir_to = nr_of_functions},
									icl_imported_objects = mod_imported_objects,
	    		  			icl_declared = {dcls_local = local_defs, dcls_import = icl_imported, dcls_explicit = dcls_explicit} }
		= (False, icl_mod, dcl_modules, {}, No, heaps, cs_predef_symbols, cs_symbol_table, cs_error.ea_file)
	where
		check_start_rule mod_kind mod_name {ir_from, ir_to} cs=:{cs_predef_symbols,cs_symbol_table}
			# (pre_symb, cs_predef_symbols) = cs_predef_symbols![PD_Start]
			  ({ste_kind, ste_index}, cs_symbol_table) = readPtr pre_symb.pds_ident.id_info cs_symbol_table
			  cs = { cs & cs_predef_symbols = cs_predef_symbols, cs_symbol_table = cs_symbol_table }
			= case ste_kind of
				STE_FunctionOrMacro _
					| ir_from <= ste_index &&  ste_index < ir_to
						-> { cs & cs_predef_symbols = { cs.cs_predef_symbols & [PD_Start] = { pre_symb & pds_def = ste_index, pds_module = cIclModIndex }}}
				STE_Imported STE_DclFunction mod_index
					-> { cs & cs_predef_symbols = { cs.cs_predef_symbols & [PD_Start] = { pre_symb & pds_def = ste_index, pds_module = mod_index }}}
				_
					-> case mod_kind of
							MK_Main
								# pos = newPosition pre_symb.pds_ident (LinePos (mod_name.id_name+++".icl") 1)
								-> { cs & cs_error = checkErrorWithIdentPos pos " has not been declared" cs.cs_error }
							_
								-> cs

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

		add_modules_to_symbol_table [] mod_index macro_and_fun_defs cs=:{cs_predef_symbols,cs_symbol_table}
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
						-> ({ pre_def_symbols & [predef_index] = { mod_symb & pds_module = cIclModIndex, pds_def =  mod_entry.ste_index }}, symbol_table)
					_
						-> (pre_def_symbols, symbol_table)

		add_modules_to_symbol_table [mod=:{mod_defs} : mods] mod_index macro_and_fun_defs cs=:{cs_predef_symbols,cs_symbol_table, cs_error}
			# def_instances	= convert_class_instances mod_defs.def_instances
			  mod_defs = { mod_defs & def_instances = def_instances }
			  sizes_and_defs = collectFunctionTypes mod_defs.def_funtypes (collectCommonfinitions mod_defs)
			  (macro_and_fun_defs, (sizes, defs)) = collectMacros mod_defs.def_macros macro_and_fun_defs sizes_and_defs
  			  mod = { mod & mod_defs = mod_defs }
		   	  (cs_symbol_table, cs_error) = addDefToSymbolTable cGlobalScope mod_index mod.mod_name (STE_Module mod) cs_symbol_table cs_error
			  (mods, macro_and_fun_defs, cs)
			  		= add_modules_to_symbol_table mods (inc mod_index) macro_and_fun_defs { cs & cs_symbol_table = cs_symbol_table, cs_error = cs_error }
			= ([(mod, sizes, defs) : mods], macro_and_fun_defs, cs)
		where
			convert_class_instances :: ![ParsedInstance a] -> [ClassInstance]
			convert_class_instances [pi : pins]
				= [ParsedInstanceToClassInstance pi {} : convert_class_instances pins]
			convert_class_instances []
				= []

		check_predefined_module {id_info} modules macro_and_fun_defs heaps cs=:{cs_symbol_table}
			# (entry, cs_symbol_table) = readPtr id_info cs_symbol_table
			# cs = { cs & cs_symbol_table = cs_symbol_table <:= (id_info, { entry & ste_kind = STE_ClosedModule })}
			  {ste_kind = STE_Module mod, ste_index} = entry
			  (modules, macro_and_fun_defs, heaps, cs)
			  		= checkDclModule mod ste_index modules macro_and_fun_defs heaps cs
			  ({dcl_declared={dcls_import,dcls_local}}, modules) = modules![ste_index]
			= (modules, macro_and_fun_defs, heaps, addDeclaredSymbolsToSymbolTable cIsADclModule ste_index dcls_local dcls_import cs)

		check_dcl_module iinfo=:{ii_modules} heaps cs=:{cs_symbol_table}
			# (dcl_mod, ii_modules) = ii_modules![cIclModIndex]
			# dcl_info = dcl_mod.dcl_name.id_info			
			# (entry, cs_symbol_table) = readPtr dcl_info cs_symbol_table
			# (_, iinfo, heaps, cs) = checkImport dcl_info entry { iinfo & ii_modules = ii_modules } heaps { cs & cs_symbol_table = cs_symbol_table }
			= (iinfo, heaps, cs)

		collect_specialized_functions_in_dcl_module :: !w:{# DclModule} !v:{# ClassInstance} !u:{# FunDef} !Index !*VarHeap !*TypeVarHeap !*ExpressionHeap
			-> (![FunDef], !w:{# DclModule}, !v:{# ClassInstance}, !u:{# FunDef}, !Index, !(Optional {# Index}), !*VarHeap,  !*TypeVarHeap, !*ExpressionHeap)
 		collect_specialized_functions_in_dcl_module modules icl_instances icl_functions first_free_index var_heap type_var_heap expr_heap
			# (dcl_mod, modules) = modules![cIclModIndex]
			# {dcl_specials,dcl_functions,dcl_common,dcl_class_specials,dcl_conversions} = dcl_mod
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
				# dcl_instances_table = conversion_table.[toInt STE_Instance]
				  dcl_function_table = conversion_table.[toInt STE_DclFunction]
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
		 
			build_function new_fun_index fun_def=:{fun_symb, fun_arity, fun_index, fun_body = CheckedBody {cb_args}, fun_info} fun_type
						(var_heap, type_var_heap, expr_heap)
				# (tb_args, var_heap) = mapSt new_free_var cb_args var_heap
				  (app_args, expr_heap) = mapSt new_bound_var tb_args expr_heap
				  (app_info_ptr, expr_heap) = newPtr EI_Empty expr_heap
				  tb_rhs = App { app_symb = {	symb_name = fun_symb, symb_arity = fun_arity,
												symb_kind = SK_Function { glob_module = cIclModIndex, glob_object = fun_index }},
								 app_args = app_args,
								 app_info_ptr = app_info_ptr }
				= ({ fun_def & fun_index = new_fun_index, fun_body = TransformedBody {tb_args = tb_args, tb_rhs = tb_rhs}, fun_type = Yes fun_type,
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
		
		adjust_instance_types_of_array_functions_in_std_array_icl dcl_modules class_instances fun_defs predef_symbols
			# ({pds_def}, predef_symbols) = predef_symbols![PD_StdArray]
			| pds_def == cIclModIndex
				#! nr_of_instances = size class_instances
				# ({dcl_common, dcl_conversions = Yes conversion_table}, dcl_modules) = dcl_modules![cIclModIndex]
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
				| glob_module == cIclModIndex && ds_index == array_class_index && elemTypeIsStrict ins_type.it_types predef_symbols
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

		memcpy :: !a:{#Int} -> (!.{#Int}, !a:{#Int})
		memcpy src
			#! size = size src
			# new = createArray size 0
			= iFoldSt (\i (dst, src=:{[i]=src_i})->({ dst & [i] = src_i }, src)) 0 size (new, src)

check_needed_modules_are_imported mod_name extension cs=:{cs_needed_modules}
	# cs = case cs_needed_modules bitand cNeedStdDynamics of
			0 -> cs
			_ -> check_it PD_StdDynamics mod_name extension cs
	# cs = case cs_needed_modules bitand cNeedStdArray of
			0 -> cs
			_ -> check_it PD_StdArray mod_name extension cs
	# cs = case cs_needed_modules bitand cNeedStdEnum of
			0 -> cs
			_ -> check_it PD_StdEnum mod_name extension cs
	= cs
  where
	check_it pd mod_name extension cs=:{cs_predef_symbols, cs_symbol_table}
  		#! {pds_ident} = cs_predef_symbols.[pd]	
		# ({ste_kind}, cs_symbol_table) = readPtr pds_ident.id_info cs_symbol_table
		  cs = { cs & cs_symbol_table = cs_symbol_table }
		= case ste_kind of
			STE_ClosedModule
				-> cs
			STE_Empty
				# error_location = { ip_ident = mod_name, ip_line = 1, ip_file = mod_name.id_name+++extension}
				  cs_error = pushErrorAdmin error_location cs.cs_error
				  cs_error = checkError pds_ident "not imported" cs_error
				  cs_error = popErrorAdmin cs_error
				-> { cs & cs_error = cs_error }

arrayFunOffsetToPD_IndexTable :: !{# MemberDef} !v:{# PredefinedSymbol} -> (!{# Index}, !{#MemberDef}, !v:{#PredefinedSymbol})
arrayFunOffsetToPD_IndexTable member_defs predef_symbols
	# nr_of_array_functions = size member_defs
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


::	ImportInfo =
	{	ii_modules			:: !.{# DclModule}
	,	ii_funs_and_macros	:: !.{# FunDef}
	,	ii_next_num			:: !Int
	,	ii_deps				:: ![SymbolPtr]
	}
	
checkImports :: ![ParsedImport] !*ImportInfo !*Heaps !*CheckState -> (!Int, !*ImportInfo, !*Heaps, !*CheckState)
checkImports [] iinfo=:{ii_modules,ii_deps} heaps cs
	#! mod_num = size ii_modules
	= (mod_num, iinfo, heaps, cs)
checkImports [ {import_module = {id_info}}: mods ] iinfo heaps cs=:{cs_symbol_table}
	# (entry, cs_symbol_table) = readPtr id_info cs_symbol_table
	# (min_mod_num1, iinfo, heaps, cs) = checkImport id_info entry iinfo heaps { cs & cs_symbol_table = cs_symbol_table }
	  (min_mod_num2, iinfo, heaps, cs) = checkImports mods iinfo heaps cs
	= (min min_mod_num1 min_mod_num2, iinfo, heaps, cs)

	
checkImport :: SymbolPtr SymbolTableEntry *ImportInfo *Heaps *CheckState -> *(Int,*ImportInfo,*Heaps,*CheckState)
checkImport module_id_info entry=:{ste_kind = STE_OpenModule mod_num _} iinfo heaps cs
	= (mod_num, iinfo, heaps, cs)
checkImport module_id_info entry=:{ste_kind = STE_ClosedModule} iinfo=:{ii_modules} heaps cs
	#! mod_num = size ii_modules
	= (mod_num, iinfo, heaps, cs)
checkImport module_id_info entry=:{ste_kind = STE_Module mod, ste_index} iinfo=:{ii_next_num,ii_deps} heaps cs=:{cs_symbol_table}
	# entry = { entry & ste_kind = STE_OpenModule ii_next_num mod}
	  cs = { cs & cs_symbol_table = cs_symbol_table <:= (module_id_info,entry) }
	  iinfo = { iinfo & ii_next_num = inc ii_next_num, ii_deps = [module_id_info : ii_deps] }
	  (min_mod_num, iinfo, heaps, cs) = checkImports mod.mod_imports iinfo heaps cs

	| ii_next_num <= min_mod_num
		# {ii_deps,ii_modules,ii_funs_and_macros} = iinfo
		  (ii_deps, ii_modules, ii_funs_and_macros, heaps, cs)
		  		= check_component module_id_info ii_deps ii_modules ii_funs_and_macros heaps cs
		#! max_mod_num = size ii_modules
		= (max_mod_num, { iinfo & ii_deps = ii_deps, ii_modules = ii_modules, ii_funs_and_macros = ii_funs_and_macros }, heaps, cs) 
		= (min_mod_num, iinfo, heaps, cs)
	where
		check_component lowest_mod_info [mod_info : ds] modules macro_and_fun_defs heaps cs=:{cs_symbol_table}
			# (entry, cs_symbol_table) = readPtr mod_info cs_symbol_table
			# {ste_kind=STE_OpenModule _ mod,ste_index} = entry
		  	  (modules, macro_and_fun_defs, heaps, cs) = checkDclModule mod ste_index modules macro_and_fun_defs heaps { cs & cs_symbol_table = cs_symbol_table }
		  	  cs = { cs & cs_symbol_table = cs.cs_symbol_table <:= (mod_info, { entry & ste_kind = STE_ClosedModule })}
			| lowest_mod_info == mod_info
				= (ds, modules, macro_and_fun_defs, heaps, cs)
				= check_component lowest_mod_info ds modules macro_and_fun_defs heaps cs

initialDclModule ({mod_name, mod_defs=mod_defs=:{def_funtypes,def_macros}, mod_type}, sizes, all_defs)
	# dcl_common= createCommonDefinitions mod_defs
	= 	{	dcl_name			= mod_name
		,	dcl_functions		= { function \\ function <- mod_defs.def_funtypes }
		,	dcl_macros			= def_macros
		,	dcl_instances		= { ir_from = 0, ir_to = 0 }
		,	dcl_class_specials	= { ir_from = 0, ir_to = 0 }
		,	dcl_specials		= { ir_from = 0, ir_to = 0 }
		,	dcl_common			= dcl_common
		,	dcl_sizes			= sizes
		,	dcl_declared		=
			{	dcls_import 	= []
			,	dcls_local		= all_defs
			,	dcls_explicit	= []
			}
		,	dcl_conversions = No
		,	dcl_is_system	= case mod_type of
								MK_System 	-> True
								_			-> False
		}

checkDclModule :: !(Module (CollectedDefinitions ClassInstance IndexRange)) !Index !*{#DclModule} !*{#FunDef} !*Heaps !*CheckState
	-> (!*{#DclModule}, !*{#FunDef}, !*Heaps, !*CheckState)
checkDclModule {mod_name,mod_imports,mod_defs} mod_index modules icl_functions heaps=:{hp_var_heap, hp_type_heaps} cs
	# (dcl_mod, modules)			= modules![mod_index]
	# dcl_defined 					= dcl_mod.dcl_declared.dcls_local
	  dcl_common					= createCommonDefinitions mod_defs
	  dcl_macros					= mod_defs.def_macros
	  (imports, modules, cs)		= collect_imported_symbols mod_imports [] modules cs
	  cs							= add_imported_symbols_to_symbol_table imports cs
	  cs							= addGlobalDefinitionsToSymbolTable dcl_defined cs
	  cs							= { cs & cs_needed_modules = 0 }
	  nr_of_dcl_functions 			= size dcl_mod.dcl_functions

	  (dcl_common, modules, hp_type_heaps, hp_var_heap, cs)
	  		= checkCommonDefinitions cIsADclModule mod_index dcl_common modules hp_type_heaps hp_var_heap cs
	  (memb_inst_defs, nr_of_dcl_functions_and_instances, rev_spec_class_inst, dcl_common, modules, hp_type_heaps, hp_var_heap, cs)
	  		= determineTypesOfInstances nr_of_dcl_functions  mod_index dcl_common modules hp_type_heaps hp_var_heap cs
	  (nr_of_dcl_funs_insts_and_specs, rev_function_list, rev_special_defs, com_type_defs, com_class_defs, modules, heaps, cs)
	  		= checkDclFunctions mod_index nr_of_dcl_functions_and_instances mod_defs.def_funtypes
	  			dcl_common.com_type_defs dcl_common.com_class_defs modules { heaps & hp_type_heaps = hp_type_heaps, hp_var_heap = hp_var_heap } cs

	  (nr_of_dcl_funs_insts_and_specs, new_class_instances, rev_special_defs, all_spec_types, heaps, cs_error)
			= checkSpecialsOfInstances mod_index nr_of_dcl_functions rev_spec_class_inst nr_of_dcl_funs_insts_and_specs []
					rev_special_defs { mem \\ mem <- memb_inst_defs } { [] \\ mem <- memb_inst_defs } heaps cs.cs_error

	  dcl_functions = { function \\ function <- revAppend rev_function_list
	  		( [ { mem_inst & ft_specials = if (isEmpty spec_types) SP_None (SP_ContextTypes spec_types) } \\
	  					mem_inst <- memb_inst_defs & spec_types <-: all_spec_types ] ++
	  						reverse rev_special_defs) }
	  
	  e_info = { ef_type_defs = com_type_defs, ef_selector_defs = dcl_common.com_selector_defs, ef_class_defs = com_class_defs,
	  			 ef_cons_defs = dcl_common.com_cons_defs, ef_member_defs = dcl_common.com_member_defs, ef_modules = modules,
				 ef_is_macro_fun = False }

	  (icl_functions, e_info, heaps, cs)
			= checkMacros mod_index dcl_macros icl_functions e_info heaps { cs & cs_error = cs_error }

	  cs = check_needed_modules_are_imported mod_name ".dcl" cs

	  com_instance_defs = dcl_common.com_instance_defs
	  com_instance_defs = { inst_def \\ inst_def <- [ inst_def \\ inst_def <-: com_instance_defs ] ++ new_class_instances }

	  (ef_member_defs, com_instance_defs, dcl_functions, cs)
	  		= adjust_predefined_symbols mod_index e_info.ef_member_defs com_instance_defs dcl_functions cs

 	  first_special_class_index = size com_instance_defs
 	  last_special_class_index = first_special_class_index + length new_class_instances
	  
	  dcl_common = { dcl_common & com_type_defs = e_info.ef_type_defs, com_selector_defs = e_info.ef_selector_defs, com_class_defs = e_info.ef_class_defs,
			  	 		com_instance_defs = com_instance_defs, com_cons_defs = e_info.ef_cons_defs, com_member_defs = ef_member_defs }	  			  

	  (dcl_imported, cs_symbol_table) = retrieveAndRemoveImportsFromSymbolTable imports [] cs.cs_symbol_table
	  cs_symbol_table = removeDeclarationsFromSymbolTable dcl_defined cModuleScope cs_symbol_table

	  dcls_explicit	= flatten [dcls_explicit \\ (_,{dcls_explicit})<-imports]

	  dcl_mod = { dcl_mod &  dcl_declared = { dcl_mod.dcl_declared & dcls_import = dcl_imported, dcls_explicit = dcls_explicit },
	  			 dcl_common = dcl_common, dcl_functions = dcl_functions, 
	  			 dcl_instances = { ir_from = nr_of_dcl_functions, ir_to = nr_of_dcl_functions_and_instances },
	  			 dcl_specials = { ir_from = nr_of_dcl_functions_and_instances, ir_to = nr_of_dcl_funs_insts_and_specs },
	  			 dcl_class_specials = { ir_from = first_special_class_index, ir_to = last_special_class_index }}
	= ({ e_info.ef_modules & [ mod_index ] = dcl_mod }, icl_functions, heaps, { cs & cs_symbol_table = cs_symbol_table })
where
	collect_imported_symbols [{import_module={id_info},import_symbols,import_file_position} : mods ] all_decls modules cs=:{cs_symbol_table}
		# (entry, cs_symbol_table) = readPtr id_info cs_symbol_table
		# (decls_of_imported_module, modules, cs) = collect_declarations_of_module id_info entry [] modules { cs & cs_symbol_table = cs_symbol_table}
		  (imported_decls, modules, cs)	= possibly_filter_decls 
		  										import_symbols decls_of_imported_module import_file_position modules cs
		= collect_imported_symbols mods (imported_decls++all_decls) modules cs
	collect_imported_symbols [] all_decls modules cs
		= (all_decls, modules, cs)

	collect_declarations_of_module module_id_info entry=:{ste_index, ste_kind= old_kind=:STE_OpenModule mod_num {mod_imports} }
			all_decls modules cs=:{cs_symbol_table}
		# cs = { cs & cs_symbol_table = cs_symbol_table <:= (module_id_info, { entry & ste_kind = STE_LockedModule })}
		  (imported_decls, modules, cs) = collect_imported_symbols mod_imports [] modules cs
		# (dcl_mod, modules) = modules![ste_index]
		# (declared, cs) = determine_declared_symbols ste_index dcl_mod.dcl_declared.dcls_local imported_decls cs
		= (	[(ste_index, declared) : all_decls]
		  ,	modules
		  ,	{ cs & cs_symbol_table	= cs.cs_symbol_table <:= (module_id_info, { entry & ste_kind = old_kind })}
		  )
	collect_declarations_of_module module_id_info entry=:{ste_index, ste_kind= STE_ClosedModule} all_decls modules cs
		# ({dcl_declared}, modules) = modules![ste_index]
		= ([(ste_index, dcl_declared) : all_decls], modules, cs)
	collect_declarations_of_module module_id_info entry=:{ste_kind= STE_LockedModule} all_decls modules cs
		= (all_decls, modules, cs)

	determine_declared_symbols mod_index definitions imported_decls cs
		# cs = addGlobalDefinitionsToSymbolTable definitions (add_imported_symbols_to_symbol_table imported_decls cs)
		  (dcls_import, cs_symbol_table) = retrieveAndRemoveImportsFromSymbolTable imported_decls [] cs.cs_symbol_table
		  cs_symbol_table = removeDeclarationsFromSymbolTable definitions cModuleScope cs_symbol_table
		= (	{dcls_import = dcls_import, dcls_local = definitions, dcls_explicit = []}, { cs & cs_symbol_table = cs_symbol_table })

	add_imported_symbols_to_symbol_table [(mod_index, {dcls_import,dcls_local}) : imports] cs
		= add_imported_symbols_to_symbol_table imports (addDeclaredSymbolsToSymbolTable cIsADclModule mod_index dcls_local dcls_import cs)
	add_imported_symbols_to_symbol_table [] cs
		= cs

	adjust_predefined_symbols mod_index class_members class_instances fun_types cs=:{cs_predef_symbols}
		# (pre_mod, cs_predef_symbols) = cs_predef_symbols![PD_StdArray]
		| pre_mod.pds_def == mod_index
			# cs = { cs & cs_predef_symbols = cs_predef_symbols}
				<=< adjust_predef_symbols PD_CreateArrayFun PD_UnqArraySizeFun mod_index STE_Member
				<=< adjust_predef_symbol PD_ArrayClass mod_index STE_Class
			  (class_members, class_instances, fun_types, cs_predef_symbols)
			  		= adjust_instance_types_of_array_functions_in_std_array_dcl mod_index class_members class_instances fun_types cs.cs_predef_symbols
			= (class_members, class_instances, fun_types, { cs & cs_predef_symbols = cs_predef_symbols })
		# (pre_mod, cs_predef_symbols) = cs_predef_symbols![PD_PredefinedModule]
		| pre_mod.pds_def == mod_index
			= (class_members, class_instances, fun_types, { cs & cs_predef_symbols = cs_predef_symbols}
				<=< adjust_predef_symbols PD_ListType PD_UnboxedArrayType mod_index STE_Type
				<=< adjust_predef_symbols PD_ConsSymbol PD_Arity32TupleSymbol mod_index STE_Constructor
				<=< adjust_predef_symbol PD_TypeCodeClass mod_index STE_Class
				<=< adjust_predef_symbol PD_TypeCodeMember mod_index STE_Member)
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
				<=< adjust_predef_symbol PD_undo_indirections	mod_index STE_DclFunction)
			= (class_members, class_instances, fun_types, { cs & cs_predef_symbols = cs_predef_symbols})
	where
		
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
		
		adjust_instance_types_of_array_functions_in_std_array_dcl array_mod_index class_members class_instances fun_types predef_symbols
			#! nr_of_instances = size class_instances
			# ({pds_def}, predef_symbols) = predef_symbols![PD_ArrayClass]
			  (offset_table, class_members, predef_symbols) = arrayFunOffsetToPD_IndexTable class_members predef_symbols
			  (class_instances, fun_types, predef_symbols) 
					= iFoldSt (adjust_instance_types_of_array_functions array_mod_index pds_def offset_table) 0 nr_of_instances
							(class_instances, fun_types, predef_symbols)
			= (class_members, class_instances, fun_types, predef_symbols)
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

NewEntry symbol_table symb_ptr def_kind def_index level previous :==
	 symbol_table <:= (symb_ptr,{  ste_kind = def_kind, ste_index = def_index, ste_def_level = level, ste_previous = previous })
	
addImportsToSymbolTable :: ![ParsedImport] ![(!Declaration, !LineNr)] !*{# DclModule} !*CheckState 
						-> (![(!Declaration, !LineNr)], !*{# DclModule}, !*CheckState)
addImportsToSymbolTable [{import_module={id_info},import_symbols, import_file_position} : mods ]  explicit_akku modules cs=:{cs_symbol_table}
	# ({ste_index}, cs_symbol_table)						= readPtr id_info cs_symbol_table
	# ({dcl_declared=decls_of_imported_module}, modules)	= modules![ste_index]
	  (imported_decls, modules, cs)	= possibly_filter_decls import_symbols [(ste_index, decls_of_imported_module)] import_file_position
	  		modules { cs & cs_symbol_table = cs_symbol_table }
	| isEmpty imported_decls
		= addImportsToSymbolTable mods explicit_akku modules cs
		# (_,{dcls_import,dcls_local,dcls_explicit}) = hd imported_decls
		= addImportsToSymbolTable mods (dcls_explicit++explicit_akku) 
									modules (addDeclaredSymbolsToSymbolTable cIsNotADclModule ste_index dcls_local dcls_import cs)
addImportsToSymbolTable [] explicit_akku modules cs
	= (explicit_akku, modules, cs)


file_and_status {ea_file,ea_ok}
	= (ea_file, ea_ok)

allocate_bound_var :: !FreeVar !*ExpressionHeap -> (!BoundVar, !.ExpressionHeap)
allocate_bound_var {fv_name, fv_info_ptr} expr_heap
	# (var_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
	= ({ var_name = fv_name, var_info_ptr = fv_info_ptr, var_expr_ptr = var_expr_ptr }, expr_heap)

allocate_bound_var` :: !Ident !VarInfoPtr !*ExpressionHeap -> (!BoundVar, !.ExpressionHeap)
allocate_bound_var` fv_name fv_info_ptr expr_heap
	# (var_expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
	= ({ var_name = fv_name, var_info_ptr = fv_info_ptr, var_expr_ptr = var_expr_ptr }, expr_heap)

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
	
instance <<< FieldSymbol
where
	(<<<) file { fs_var } = file <<< fs_var


instance <<< Declarations
where
	(<<<) file { dcls_import, dcls_local } = file <<< "I:" <<< dcls_import <<< "L:" <<< dcls_local

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

retrieveGlobalDefinition :: !SymbolTableEntry !STE_Kind !Index -> (!Index, !Index)
retrieveGlobalDefinition {ste_kind = STE_Imported kind dcl_index, ste_def_level, ste_index} requ_kind mod_index
	| kind == requ_kind
		= (ste_index, dcl_index)
		= (NotFound, mod_index)
retrieveGlobalDefinition {ste_kind,ste_def_level,ste_index} requ_kind mod_index
	| ste_kind == requ_kind && ste_def_level == cGlobalScope
		= (ste_index, mod_index)
		= (NotFound, mod_index)

/* 2.0 ...
removeLocalsFromSymbolTable :: !Level ![Ident] !LocalDefs !u:(m a) !*(Heap SymbolTableEntry)
			-> (!u:(m a), !.Heap SymbolTableEntry) | Array m a & toIdent a
... */
removeLocalsFromSymbolTable level loc_vars (CollectedLocalDefs {loc_functions={ir_from,ir_to}}) defs symbol_table
	= remove_defs_from_symbol_table level ir_from ir_to defs (removeLocalIdentsFromSymbolTable level loc_vars symbol_table)
where
	remove_defs_from_symbol_table level from_index to_index defs symbol_table
		| from_index == to_index
			= (defs, symbol_table)	
			#! def = defs.[from_index]
			   id_info = (toIdent def).id_info
			   entry = sreadPtr id_info symbol_table
			| level == entry.ste_def_level
				= remove_defs_from_symbol_table level (inc from_index) to_index defs (symbol_table <:= (id_info, entry.ste_previous))
				= remove_defs_from_symbol_table level (inc from_index) to_index defs symbol_table



