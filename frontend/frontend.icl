/*
	module owner: Ronny Wichers Schreur
*/
implementation module frontend

import scanner, parse, postparse, check, type, trans, convertcases, overloading, utilities, convertDynamics,
		convertimportedtypes, /*checkKindCorrectness, */ compilerSwitches, analtypes, generics1

//import print

:: FrontEndOptions 
	=	{	feo_up_to_phase			:: !FrontEndPhase
		,	feo_generics 			:: !Bool
		,	feo_fusion	 			:: !Bool
		}

:: FrontEndSyntaxTree
	=	{	fe_icl					:: !IclModule
		,	fe_dcls					:: !{#DclModule}
		,	fe_components			:: !{!Group}
		,	fe_arrayInstances		:: !ArrayAndListInstances
		}

// trace macro
(-*->) infixl
(-*->) value trace
	:==	value // ---> trace

:: FrontEndPhase
	=	FrontEndPhaseCheck
	|	FrontEndPhaseTypeCheck
	|	FrontEndPhaseConvertDynamics
	|	FrontEndPhaseTransformGroups
	|	FrontEndPhaseConvertModules
	|	FrontEndPhaseAll

instance == FrontEndPhase where
	(==) a b
		=	equal_constructor a b

frontSyntaxTree cached_dcl_macros cached_dcl_mods n_functions_and_macros_in_dcl_modules main_dcl_module_n predef_symbols hash_table files error io out tcl_file icl_mod dcl_mods fun_defs components array_instances heaps
	:== (Yes {
				fe_icl = {icl_mod & icl_functions=fun_defs }
			,	fe_dcls = dcl_mods
			,	fe_components = components
			,	fe_arrayInstances = array_instances
			},cached_dcl_macros,cached_dcl_mods,n_functions_and_macros_in_dcl_modules,main_dcl_module_n,predef_symbols,hash_table,files,error,io,out,tcl_file,heaps
		)

// import StdDebug

frontEndInterface :: !FrontEndOptions !Ident !SearchPaths !{#DclModule} !*{#*{#FunDef}} !(Optional Bool) !*PredefinedSymbols !*HashTable (ModTimeFunction *Files) !*Files !*File !*File !*File !(Optional *File) !*Heaps
  	-> ( !Optional *FrontEndSyntaxTree,!*{#*{#FunDef}},!{#DclModule},!Int,!Int,!*PredefinedSymbols, !*HashTable, !*Files, !*File, !*File, !*File, !Optional *File, !*Heaps) 
frontEndInterface options mod_ident search_paths cached_dcl_modules functions_and_macros list_inferred_types predef_symbols hash_table modtimefunction files error io out tcl_file heaps 
// 	# files = trace_n ("Compiling "+++mod_ident.id_name) files
	# (ok, mod, hash_table, error, files)
		= wantModule cWantIclFile mod_ident NoPos options.feo_generics(hash_table /* ---> ("Parsing:", mod_ident)*/) error search_paths modtimefunction files
	| not ok
		= (No,{},{},0,0,predef_symbols, hash_table, files, error, io, out, tcl_file, heaps)

	# cached_module_idents = [dcl_mod.dcl_name \\ dcl_mod<-:cached_dcl_modules]
	# (ok, mod, global_fun_range, mod_functions, optional_dcl_mod, modules, dcl_module_n_in_cache,n_functions_and_macros_in_dcl_modules,hash_table, error, files)
		= scanModule (mod -*-> "Scanning") cached_module_idents options.feo_generics hash_table error search_paths modtimefunction files
	/* JVG: */
//	# hash_table = {hash_table & hte_entries={}}
	# hash_table = remove_icl_symbols_from_hash_table hash_table
	/**/
	| not ok
		= (No,{},{},0,0,predef_symbols, hash_table, files, error, io, out, tcl_file, heaps)
  	# symbol_table = hash_table.hte_symbol_heap
  	#! n_cached_dcl_modules=size cached_dcl_modules
  	# (ok, icl_mod, dcl_mods, components, cached_dcl_macros,main_dcl_module_n,heaps, predef_symbols, symbol_table, error, directly_imported_dcl_modules)
  	  	= checkModule mod global_fun_range mod_functions n_functions_and_macros_in_dcl_modules dcl_module_n_in_cache optional_dcl_mod modules cached_dcl_modules functions_and_macros predef_symbols (symbol_table -*-> "Checking") error heaps
	  hash_table = { hash_table & hte_symbol_heap = symbol_table}

	| not ok
		= (No,{},dcl_mods,0,main_dcl_module_n,predef_symbols, hash_table, files, error, io, out, tcl_file, heaps)

	#! (icl_functions,icl_mod) = select_and_remove_icl_functions_from_record icl_mod
		with
			select_and_remove_icl_functions_from_record :: !*IclModule -> (!.{#FunDef},!.IclModule)
			select_and_remove_icl_functions_from_record icl_mod=:{icl_functions} = (icl_functions,{icl_mod & icl_functions={}})

	# {icl_global_functions,icl_instances,icl_gencases, icl_specials, icl_common,icl_import,icl_name,icl_imported_objects,icl_used_module_numbers,icl_copied_from_dcl} = icl_mod
/**/
	  (_,f,files) = fopen "components" FWriteText files
	  (components, icl_functions, f) = showComponents components 0 True icl_functions f
	/*	
	  (n_functions,icl_functions) = usize icl_functions
	  (icl_functions,f) = showFunctions {ir_from=0,ir_to=n_functions} icl_functions f
	  (cached_dcl_macros,f) = showMacros cached_dcl_macros f
	*/
	  (ok,files) = fclose f files
	| ok<>ok
		= abort "";
/**/

//	# dcl_mods = {{dcl_mod & dcl_declared={dcls_import={},dcls_local=[],dcls_local_for_import={},dcls_explicit={}}}\\ dcl_mod<-:dcl_mods}

	# var_heap = heaps.hp_var_heap
	  gen_heap = heaps.hp_generic_heap
	  type_heaps = heaps.hp_type_heaps
	  fun_defs = icl_functions

	| options.feo_up_to_phase == FrontEndPhaseCheck
		# array_instances = {ali_array_first_instance_indices=[],ali_list_first_instance_indices=[],ali_tail_strict_list_first_instance_indices=[],ali_instances_range={ir_from=0,ir_to=0}}
		=	frontSyntaxTree cached_dcl_macros dcl_mods n_functions_and_macros_in_dcl_modules main_dcl_module_n
							predef_symbols hash_table files error io out tcl_file icl_mod dcl_mods fun_defs components array_instances heaps

	# error_admin = {ea_file = error, ea_loc = [], ea_ok = True }
/*
	# (ti_common_defs, dcl_mods) = get_common_defs dcl_mods
	  ti_common_defs = { ti_common_defs & [main_dcl_module_n] = icl_common }
*/

	# (cached_dcl_mods, dcl_mods) = copy_dcl_modules dcl_mods
	
	# (type_groups, ti_common_defs, td_infos, icl_common, dcl_mods, type_heaps, error_admin)
			= partionateAndExpandTypes icl_used_module_numbers main_dcl_module_n icl_common dcl_mods type_heaps error_admin
	  ti_common_defs = { ti_common_defs & [main_dcl_module_n] = icl_common }
	# (td_infos, th_vars, error_admin) = analyseTypeDefs ti_common_defs type_groups td_infos type_heaps.th_vars error_admin
/*
	  (fun_defs, dcl_mods, th_vars, td_infos, error_admin) 
      		= checkKindCorrectness main_dcl_module_n nr_of_cached_functions_and_macros icl_instances ti_common_defs n_cached_dcl_modules fun_defs dcl_mods type_heaps.th_vars td_infos error_admin
*/
	  (class_infos, td_infos, th_vars, error_admin)
			= determineKindsOfClasses icl_used_module_numbers ti_common_defs td_infos th_vars error_admin
	# (fun_defs, dcl_mods, td_infos, th_vars, gen_heap, error_admin)
			= checkKindsOfCommonDefsAndFunctions n_cached_dcl_modules main_dcl_module_n icl_used_module_numbers icl_global_functions
				ti_common_defs fun_defs dcl_mods td_infos class_infos th_vars gen_heap error_admin

      type_heaps = { type_heaps & th_vars = th_vars }

	# heaps = { heaps & hp_type_heaps = type_heaps, hp_generic_heap = gen_heap }
	# (saved_main_dcl_common, ti_common_defs) = replace (dcl_common_defs dcl_mods) main_dcl_module_n icl_common
		with 
			dcl_common_defs :: .{#DclModule} -> .{#CommonDefs} // needed for Clean 2.0 to disambiguate overloading
			dcl_common_defs dcl_mods
				=	{dcl_common \\ {dcl_common} <-: dcl_mods }

	#! (ti_common_defs, components, fun_defs, generic_ranges, td_infos, heaps, hash_table, predef_symbols, dcl_mods, error_admin) = 
		SwitchGenerics
			(case options.feo_generics of
				True -> 
					convertGenerics
							main_dcl_module_n icl_used_module_numbers ti_common_defs components fun_defs td_infos 
							heaps hash_table predef_symbols dcl_mods error_admin
				False -> 
					(ti_common_defs, components, fun_defs, [], td_infos, heaps, hash_table, predef_symbols, dcl_mods, error_admin)
			)
			(ti_common_defs, components, fun_defs, [], td_infos, heaps, hash_table, predef_symbols, dcl_mods, error_admin)	
	# (icl_common, ti_common_defs) = replace copied_ti_common_defs main_dcl_module_n saved_main_dcl_common		
		with 
			copied_ti_common_defs :: .{#CommonDefs} // needed for Clean 2.0 to disambiguate overloading of replace
			copied_ti_common_defs = {x \\ x <-: ti_common_defs}

	# dcl_mods = { {dcl_mod & dcl_common = common} \\ dcl_mod <-: dcl_mods & common <-: ti_common_defs }

	# icl_mod = {icl_mod & icl_common = icl_common} 
		
	# error = error_admin.ea_file

/*
	# (_,genout,files) = fopen "c:\\Generics\\genout.icl" FWriteText files
	# (fun_defs, genout) = printFunDefs fun_defs genout
	# (ok,files) = fclose genout files
	| not ok = abort "could not write genout.icl" 
*/

	#! ok = error_admin.ea_ok
	| not ok
		= (No,{},{},0,main_dcl_module_n,predef_symbols, hash_table, files, error, io, out, tcl_file, heaps)

	# (ok, fun_defs, array_instances, type_code_instances, common_defs, imported_funs, type_def_infos, heaps, predef_symbols, error,out)
		= typeProgram (components -*-> "Typing") main_dcl_module_n fun_defs/*icl_functions*/ icl_specials list_inferred_types icl_common [a\\a<-:icl_import] dcl_mods icl_used_module_numbers td_infos heaps predef_symbols error out dcl_mods

	| not ok
		= (No,{},{},0,main_dcl_module_n,predef_symbols, hash_table, files, error, io, out, tcl_file, heaps)
			

	# (fun_def_size, fun_defs) = usize fun_defs
	# (components, fun_defs) 	= partitionateFunctions (fun_defs -*-> "partitionateFunctions") (icl_global_functions++icl_instances ++ [icl_specials] ++ icl_gencases ++ generic_ranges)
		
//	  (components, fun_defs, error)	= showTypes components 0 fun_defs error
//	  (components, fun_defs, out)	= showComponents components 0 True fun_defs out
//	  (fun_defs, error)	= showFunctions array_instances fun_defs error
		
	| options.feo_up_to_phase == FrontEndPhaseTypeCheck
		=	frontSyntaxTree cached_dcl_macros cached_dcl_mods n_functions_and_macros_in_dcl_modules main_dcl_module_n
							predef_symbols hash_table files error io out tcl_file icl_mod dcl_mods fun_defs components array_instances heaps

	# (components, fun_defs, predef_symbols, dcl_types, used_conses_in_dynamics, var_heap, type_heaps, expression_heap, tcl_file)
	  		= convertDynamicPatternsIntoUnifyAppls type_code_instances common_defs main_dcl_module_n (components -*-> "convertDynamics") fun_defs predef_symbols
					heaps.hp_var_heap heaps.hp_type_heaps heaps.hp_expression_heap tcl_file dcl_mods icl_mod directly_imported_dcl_modules
//	#  (components, fun_defs, error) = showComponents3 components 0 False fun_defs error
//	  (components, fun_defs, error)	= showComponents components 0 True fun_defs error

	| options.feo_up_to_phase == FrontEndPhaseConvertDynamics
		# heaps = {hp_var_heap=var_heap, hp_type_heaps=type_heaps, hp_expression_heap=expression_heap, hp_generic_heap=newHeap}
		=	frontSyntaxTree cached_dcl_macros cached_dcl_mods n_functions_and_macros_in_dcl_modules main_dcl_module_n
							predef_symbols hash_table files error io out tcl_file icl_mod dcl_mods fun_defs components array_instances heaps

//	  (components, fun_defs, error) = showComponents components 0 True fun_defs error

	#  (stdStrictLists_module_n,predef_symbols) = get_StdStrictLists_module_n predef_symbols
	  	with
	  		get_StdStrictLists_module_n predef_symbols
	  			# (pre_mod,predef_symbols) = predef_symbols![PD_StdStrictLists]
				| pre_mod.pds_def<>NoIndex
					= (pre_mod.pds_def,predef_symbols)
					= (-1,predef_symbols)
	# (cleanup_info, acc_args, components, fun_defs, var_heap, expression_heap)
		 = analyseGroups common_defs imported_funs array_instances.ali_instances_range main_dcl_module_n stdStrictLists_module_n (components -*-> "Analyse") fun_defs var_heap expression_heap
//	# (components, fun_defs, error) = showComponents2 components 0 fun_defs acc_args error

	  (components, fun_defs, dcl_types, used_conses, var_heap, type_heaps, expression_heap, acc_args)
	  	= transformGroups cleanup_info main_dcl_module_n stdStrictLists_module_n (components -*-> "Transform") fun_defs acc_args common_defs imported_funs dcl_types used_conses_in_dynamics type_def_infos var_heap type_heaps expression_heap options.feo_fusion

	| options.feo_up_to_phase == FrontEndPhaseTransformGroups
		# heaps = {hp_var_heap=var_heap, hp_type_heaps=type_heaps, hp_expression_heap=expression_heap,hp_generic_heap=heaps.hp_generic_heap}
		=	frontSyntaxTree cached_dcl_macros cached_dcl_mods n_functions_and_macros_in_dcl_modules main_dcl_module_n
							predef_symbols hash_table files error io out tcl_file icl_mod dcl_mods fun_defs components array_instances heaps

	# (dcl_types, used_conses, var_heap, type_heaps) = convertIclModule main_dcl_module_n common_defs (dcl_types -*-> "Convert icl") used_conses var_heap type_heaps
	# (dcl_types, used_conses, var_heap, type_heaps) = convertDclModule main_dcl_module_n dcl_mods common_defs (dcl_types -*-> "Convert dcl") used_conses var_heap type_heaps

//	  (components, fun_defs, out) = showComponents components 0 False fun_defs out

	| options.feo_up_to_phase == FrontEndPhaseConvertModules
		# heaps = {hp_var_heap=var_heap, hp_type_heaps=type_heaps, hp_expression_heap=expression_heap,hp_generic_heap=heaps.hp_generic_heap}
		=	frontSyntaxTree cached_dcl_macros cached_dcl_mods n_functions_and_macros_in_dcl_modules main_dcl_module_n
							predef_symbols hash_table files error io out tcl_file icl_mod dcl_mods fun_defs components array_instances heaps

//	  (components, fun_defs, out) = showComponents components 0 False fun_defs out
	# (used_funs, components, fun_defs, dcl_types, used_conses, var_heap, type_heaps, expression_heap)
	  		= convertCasesOfFunctions components main_dcl_module_n imported_funs common_defs fun_defs (dcl_types -*-> "Convert cases") used_conses
					var_heap type_heaps expression_heap
	#!  (dcl_types, type_heaps, var_heap)
			= convertImportedTypeSpecifications main_dcl_module_n dcl_mods imported_funs common_defs used_conses used_funs (dcl_types -*-> "Convert types") type_heaps var_heap		
//	# (components, fun_defs, error)	= showTypes components 0 fun_defs error
//	# (dcl_mods, out) = showDclModules dcl_mods out
//	# (components, fun_defs, out) = showComponents components 0 False fun_defs out

/*
	# (_,f,files) = fopen "components2" FWriteText files
	  (components, fun_defs, f) = showComponents components 0 False fun_defs f
	  (ok,files) = fclose f files
	| ok<>ok
		= abort "";
*/
//	# (fun_defs,out,var_heap,predef_symbols) = sa components main_dcl_module_n dcl_mods fun_defs out var_heap predef_symbols;

	# heaps = {hp_var_heap = var_heap, hp_expression_heap=expression_heap, hp_type_heaps=type_heaps,hp_generic_heap=heaps.hp_generic_heap}
	# 	fe ={	fe_icl =
//							 {icl_mod & icl_functions=fun_defs }
							 {icl_functions=fun_defs,icl_global_functions=icl_global_functions,icl_instances=icl_instances,icl_specials=icl_specials,
							 icl_common=icl_common,icl_import=icl_import,
							 icl_gencases = icl_gencases ++ generic_ranges,
							 icl_name=icl_name,icl_imported_objects=icl_imported_objects,icl_used_module_numbers=icl_used_module_numbers,
							 icl_copied_from_dcl=icl_copied_from_dcl,icl_modification_time=icl_mod.icl_modification_time}

			,	fe_dcls = dcl_mods
			,	fe_components = components
			,	fe_arrayInstances = array_instances
			}

	= (Yes fe,cached_dcl_macros,cached_dcl_mods,n_functions_and_macros_in_dcl_modules,main_dcl_module_n,predef_symbols,hash_table,files,error,io,out,tcl_file,heaps)
	where
		copy_dcl_modules dcl_mods
			#! nr_of_dcl_mods = size dcl_mods
			= arrayCopyBegin dcl_mods nr_of_dcl_mods

newSymbolTable :: !Int -> *{# SymbolTableEntry}
newSymbolTable size
	= createArray size {  ste_index = NoIndex, ste_def_level = -1, ste_kind = STE_Empty, ste_previous = abort "PreviousPlaceholder"}

showFunctions :: !IndexRange !*{# FunDef} !*File  -> (!*{# FunDef},!*File)
showFunctions {ir_from, ir_to} fun_defs file
	= iFoldSt show_function ir_from ir_to (fun_defs, file)
where
	show_function fun_index (fun_defs, file)
		# (fd, fun_defs) = fun_defs![fun_index]
		= (fun_defs, file <<< fun_index <<< fd <<< '\n')

showMacros :: !*{#*{#FunDef}} !*File -> (!*{#*{#FunDef}},!*File)
showMacros macro_defs file
	#! n_dcl_modules=size macro_defs
	= iFoldSt showMacrosInModule 0 n_dcl_modules (macro_defs,file)

showMacrosInModule :: !Int (!*{#*{#FunDef}},!*File) -> (!*{#*{#FunDef}},!*File)
showMacrosInModule dcl_index (macro_defs,file)
	# file=file <<< dcl_index <<< '\n'
	#! n_macros=size macro_defs.[dcl_index]
	= iFoldSt show_macro 0 n_macros (macro_defs,file)
	where
		show_macro macro_index (macro_defs, file)
			# (macro,macro_defs) = macro_defs![dcl_index,macro_index]
			= (macro_defs, file <<< macro_index <<< macro <<< '\n')

showComponents :: !*{! Group} !Int !Bool !*{# FunDef} !*File  -> (!*{! Group}, !*{# FunDef},!*File)
showComponents comps comp_index show_types fun_defs file
	| comp_index >= size comps
		= (comps, fun_defs, file)
		# (comp, comps) = comps![comp_index]
		# (fun_defs, file) = show_component comp.group_members show_types fun_defs (file <<< "component " <<< comp_index <<< '\n')
		= showComponents comps (inc comp_index) show_types fun_defs file
where
	show_component [] show_types fun_defs file
		= (fun_defs, file <<< '\n')
	show_component [fun:funs] show_types fun_defs file
		# (fun_def, fun_defs) = fun_defs![fun]
		# file=file<<<fun<<<'\n'
		| show_types
			= show_component funs show_types fun_defs (file <<< fun_def.fun_type <<< '\n' <<< fun_def)
			= show_component funs show_types fun_defs (file <<< fun_def)
//		= show_component funs show_types fun_defs (file <<< fun_def.fun_symb)

showComponents2 :: !*{! Group} !Int !*{# FunDef} !{! ConsClasses} !*File  -> (!*{! Group},!*{# FunDef},!*File)
showComponents2 comps comp_index fun_defs acc_args file
	| comp_index >= (size comps)
		= (comps, fun_defs, file)
	# (comp, comps) = comps![comp_index]
	# (fun_defs, file) = show_component comp.group_members fun_defs acc_args file
	= showComponents2 comps (inc comp_index) fun_defs acc_args file
where
	show_component [] fun_defs _ file
		= (fun_defs, file <<< '\n')
	show_component [fun:funs] fun_defs acc_args file
		# (fd, fun_defs) = fun_defs![fun]
		| fun >= size acc_args
			# file = file <<< fd.fun_symb <<< '.' <<< fun <<< " ???"
			= show_component funs fun_defs acc_args file
		# file = file <<< fd.fun_symb <<< '.' <<< fun <<< " ("
		# file = show_producer_status acc_args.[fun].cc_producer file
		# file = show_accumulating_arguments acc_args.[fun].cc_args file
		# file = show_linear_arguments acc_args.[fun].cc_linear_bits file
		= show_component funs fun_defs acc_args (file <<< ") ")
	
	show_producer_status pc file
		| pc == True
			= file <<< "+:"
			= file <<< "-:"
	
	show_accumulating_arguments [ cc : ccs] file
		| cc == cPassive
			= show_accumulating_arguments ccs (file <<< 'p')
		| cc == cActive
			= show_accumulating_arguments ccs (file <<< 'c')
		| cc == cAccumulating
			= show_accumulating_arguments ccs (file <<< 'a')
		| cc == cVarOfMultimatchCase
			= show_accumulating_arguments ccs (file <<< 'm')
			= show_accumulating_arguments ccs (file <<< '?')
	show_accumulating_arguments [] file
		= file

	show_linear_arguments [ cc : ccs] file
		| cc == True
			= show_linear_arguments ccs (file <<< 'l')
			= show_linear_arguments ccs (file <<< 'n')
	show_linear_arguments [] file
		= file

//show_components comps fun_defs = map (show_component fun_defs) comps

show_component fun_defs [] = []
show_component fun_defs [fun:funs] = [fun_defs.[fun ---> fun] : show_component fun_defs funs]

showTypes :: !*{! Group} !Int !*{# FunDef} !*File  -> (!*{! Group}, !*{# FunDef},!*File)
showTypes comps comp_index fun_defs file
	| comp_index >= size comps
		= (comps, fun_defs, file)
		# (comp, comps) = comps![comp_index]
		# (fun_defs, file) = show_types comp.group_members fun_defs (file <<< "component " <<< comp_index <<< '\n')
		= showTypes comps (inc comp_index) fun_defs file
where
	show_types [] fun_defs file
		= (fun_defs, file <<< '\n')
	show_types [fun:funs] fun_defs file
		# (fun_def, fun_defs) = fun_defs![fun]
		# properties = { form_properties = cAttributed bitor cAnnotated, form_attr_position = No }
		  (Yes ftype) = fun_def.fun_type
		= show_types funs fun_defs (file <<< fun_def.fun_symb <<< " :: " <:: (properties, ftype, No) <<< '\n' )

showDclModules :: !u:{#DclModule} !*File -> (!u:{#DclModule}, !*File)
showDclModules dcl_mods file
	= show_dcl_mods 0 dcl_mods file
where
	show_dcl_mods mod_index dcl_mods file
		# (size_dcl_mods, dcl_mods) = usize dcl_mods
		| mod_index == size_dcl_mods
			= (dcl_mods, file)
		| otherwise
			# (dcl_mod, dcl_mods) = dcl_mods ! [mod_index]	
			# file =  show_dcl_mod dcl_mod file
			= (dcl_mods, file)
			
	show_dcl_mod {dcl_name, dcl_functions} file
		# file = file <<< dcl_name <<< ":\n"
		# file = show_dcl_functions 0 dcl_functions file
		= file <<< "\n"
	show_dcl_functions fun_index dcl_functions file					 				
		| fun_index == size dcl_functions
			= file
		| otherwise
			# file = show_dcl_function dcl_functions.[fun_index] file
			= show_dcl_functions (inc fun_index) dcl_functions file 
	show_dcl_function {ft_symb, ft_type} file
		= file <<< ft_symb <<< " :: " <<< ft_type <<< "\n"			
		

:: ListTypesKind = ListTypesNone | ListTypesInferred | ListTypesStrictExports | ListTypesAll
:: ListTypesOption =
	{	lto_showAttributes :: Bool
	,	lto_listTypesKind :: ListTypesKind
	}
instance == ListTypesKind where
	(==) ListTypesNone ListTypesNone
		=	True
	(==) ListTypesInferred ListTypesInferred
		=	True
	(==) ListTypesStrictExports ListTypesStrictExports
		=	True
	(==) ListTypesAll ListTypesAll
		=	True
	(==) _ _
		=	False
		  			