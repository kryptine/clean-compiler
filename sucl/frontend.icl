implementation module frontend

// $Id$

// vi:set tabstop=4 noet:

import scanner, parse, postparse, check, type, trans, convertcases, overloading, utilities, convertDynamics,
		convertimportedtypes, checkKindCorrectness, compilerSwitches, analtypes, generics, supercompile

:: FrontEndSyntaxTree
	=	{	fe_icl :: !IclModule
		,	fe_dcls :: !{#DclModule}
		,	fe_components :: !{!Group}
		,	fe_dclIclConversions ::!Optional {# Index}
		,	fe_iclDclConversions ::!Optional {# Index}
		,	fe_globalFunctions :: !IndexRange
		,	fe_arrayInstances :: !IndexRange
		}

// trace macro
(-*->) infixl
(-*->) value trace
	:==	value // ---> trace

build_optional_icl_dcl_conversions :: !Int !(Optional {# Index}) -> Optional {# Index}
build_optional_icl_dcl_conversions size No
	=	Yes (buildIclDclConversions size {})
build_optional_icl_dcl_conversions size (Yes dcl_icl_conversions)
	=	Yes (buildIclDclConversions size dcl_icl_conversions)

buildIclDclConversions :: !Int !{# Index} -> {# Index}
buildIclDclConversions table_size dcl_icl_conversions
	# dcl_table_size = size dcl_icl_conversions
	  icl_dcl_conversions = update_conversion_array 0 dcl_table_size dcl_icl_conversions (createArray table_size NoIndex)
	= fill_empty_positions 0 table_size dcl_table_size icl_dcl_conversions

where	
	update_conversion_array	dcl_index dcl_table_size dcl_icl_conversions icl_conversions
		| dcl_index < dcl_table_size
			#  icl_index = dcl_icl_conversions.[dcl_index]
			= update_conversion_array (inc dcl_index) dcl_table_size dcl_icl_conversions
					{ icl_conversions & [icl_index] = dcl_index } 
			= icl_conversions

	fill_empty_positions next_index table_size next_new_index icl_conversions
		| next_index < table_size
			| icl_conversions.[next_index] == NoIndex
				= fill_empty_positions (inc next_index) table_size (inc next_new_index) { icl_conversions & [next_index] = next_new_index }
				= fill_empty_positions (inc next_index) table_size next_new_index icl_conversions
			= icl_conversions

:: FrontEndOptions
	=	{	feo_upToPhase    :: !FrontEndPhase  // How much of the frontend to execute
			feo_search_paths :: !SearchPaths    // Folders in which to search for files
			feo_typelisting  :: !Optional !Bool // Whether to list derived types, and if so whether to list attributes
			feo_fusionstyle  :: !FusionStyle    // What type of fusion to perform
		}

:: FrontEndPhase
	=	FrontEndPhaseCheck
	|	FrontEndPhaseTypeCheck
	|	FrontEndPhaseConvertDynamics
	|	FrontEndPhaseTransformGroups
	|	FrontEndPhaseConvertModules
	|	FrontEndPhaseAll

:: FusionStyle
	=	FS_online  // Do online fusion (supercompilation)
	|	FS_offline // Do offline fusion (deforestation)
	|	FS_none    // Do no fusion

instance == FrontEndPhase where
	(==) a b
		=	equal_constructor a b

frontSyntaxTree cached_functions_and_macros n_functions_and_macros_in_dcl_modules main_dcl_module_n predef_symbols hash_table files error io out tcl_file icl_mod dcl_mods fun_defs components array_instances optional_dcl_icl_conversions
	global_fun_range heaps
	:== (Yes {
				fe_icl = {icl_mod & icl_functions=fun_defs }
			,	fe_dcls = dcl_mods
			,	fe_components = components
			,	fe_dclIclConversions =  optional_dcl_icl_conversions
			,	fe_iclDclConversions =  build_optional_icl_dcl_conversions (size fun_defs) optional_dcl_icl_conversions
			,	fe_globalFunctions = global_fun_range
			,	fe_arrayInstances = array_instances
			},cached_functions_and_macros,n_functions_and_macros_in_dcl_modules,main_dcl_module_n,predef_symbols,hash_table,files,error,io,out,tcl_file,heaps
		)

//frontEndInterface :: !FrontEndPhase !Ident !SearchPaths !{#DclModule} !{#FunDef} !(Optional Bool) !*PredefinedSymbols !*HashTable !*Files !*File !*File !*File !*File !*Heaps -> ( !Optional *FrontEndSyntaxTree,!.{# FunDef },!Int,!Int,!*PredefinedSymbols, !*HashTable, !*Files, !*File !*File, !*File, !*File, !*Heaps) 
frontEndInterface :: !FrontEndOptions !Ident !{#DclModule} !{#FunDef} !*PredefinedSymbols !*HashTable !*Files !*File !*File !*File (!Optional !*File) !*Heaps
	-> ( !Optional *FrontEndSyntaxTree,!.{# FunDef },!Int,!Int,!*PredefinedSymbols, !*HashTable, !*Files, !*File, !*File, !*File, !Optional !*File, !*Heaps) 

frontEndInterface opts mod_ident dcl_modules functions_and_macros predef_symbols hash_table files error io out tcl_file heaps 
	# {feo_upToPhase=upToPhase, feo_search_paths=search_paths,feo_list_inferred_types=list_inferred_types} = opts
	# (ok, mod, hash_table, error, predef_symbols, files)
		= wantModule cWantIclFile mod_ident NoPos (hash_table /* ---> ("Parsing:", mod_ident)*/) error search_paths predef_symbols files
	| not ok
		= (No,{},0,0,predef_symbols, hash_table, files, error, io, out, tcl_file, heaps)
	# cached_module_idents = [dcl_mod.dcl_name \\ dcl_mod<-:dcl_modules]
	# (ok, mod, global_fun_range, mod_functions, optional_dcl_mod, modules, dcl_module_n_in_cache,n_functions_and_macros_in_dcl_modules,hash_table, error, predef_symbols, files)
		= scanModule (mod -*-> "Scanning") cached_module_idents (size functions_and_macros) hash_table error search_paths predef_symbols files
	/* JVG: */
//	# hash_table = {hash_table & hte_entries={}}
	# hash_table = remove_icl_symbols_from_hash_table hash_table
	/**/
	| not ok
		= (No,{},0,0,predef_symbols, hash_table, files, error, io, out, tcl_file, heaps)
  	# symbol_table = hash_table.hte_symbol_heap
  	  (ok, icl_mod, dcl_mods, components, optional_dcl_icl_conversions,cached_functions_and_macros,main_dcl_module_n,heaps, predef_symbols, symbol_table, error /* TD */, directly_imported_dcl_modules)
  	  	= checkModule mod global_fun_range mod_functions n_functions_and_macros_in_dcl_modules dcl_module_n_in_cache optional_dcl_mod modules dcl_modules functions_and_macros predef_symbols (symbol_table -*-> "Checking") error heaps
	  hash_table = { hash_table & hte_symbol_heap = symbol_table}

	| not ok
		= (No,{},0,main_dcl_module_n,predef_symbols, hash_table, files, error, io, out, tcl_file, heaps)

	#! (icl_functions,icl_mod) = select_and_remove_icl_functions_from_record icl_mod
		with
			select_and_remove_icl_functions_from_record :: !*IclModule -> (!.{#FunDef},!.IclModule)
			select_and_remove_icl_functions_from_record icl_mod=:{icl_functions} = (icl_functions,{icl_mod & icl_functions={}})

//	# {icl_functions,icl_instances,icl_specials,icl_common,icl_import} = icl_mod
	# {icl_instances,icl_specials,icl_common,icl_import,icl_name,icl_imported_objects,icl_used_module_numbers} = icl_mod
/*
	  (_,f,files) = fopen "components" FWriteText files
	  (components, icl_functions, f) = showComponents components 0 True icl_functions f
	  (ok,files) = fclose f files
	| ok<>ok
		= abort "";
*/
//	  dcl_mods = {{dcl_mod & dcl_declared={dcls_import=[],dcls_local=[],dcls_explicit=[]}}\\ dcl_mod<-:dcl_mods}
//	# dcl_mods = {{dcl_mod & dcl_declared={dcls_import={},dcls_local=[],dcls_local_for_import={},dcls_explicit={}}}\\ dcl_mod<-:dcl_mods}

	# var_heap = heaps.hp_var_heap
	  type_heaps = heaps.hp_type_heaps
	  fun_defs = icl_functions
	  array_instances = {ir_from=0, ir_to=0}

	| upToPhase == FrontEndPhaseCheck
		=	frontSyntaxTree cached_functions_and_macros n_functions_and_macros_in_dcl_modules main_dcl_module_n predef_symbols hash_table files error io out tcl_file icl_mod dcl_mods fun_defs components array_instances optional_dcl_icl_conversions global_fun_range heaps

// AA..
	# error_admin = {ea_file = error, ea_loc = [], ea_ok = True }
	# (ti_common_defs, dcl_mods) = get_common_defs dcl_mods
	  ti_common_defs = { ti_common_defs & [main_dcl_module_n] = icl_common }
	# (td_infos, type_heaps, error_admin) = analTypeDefs ti_common_defs icl_used_module_numbers type_heaps error_admin
      (fun_defs, dcl_mods, th_vars, td_infos, error_admin) 
      		= checkKindCorrectness main_dcl_module_n icl_instances 
      				fun_defs ti_common_defs dcl_mods type_heaps.th_vars td_infos error_admin
      type_heaps = { type_heaps & th_vars = th_vars }
	# heaps = { heaps & hp_type_heaps = type_heaps }
	# ti_common_defs = {dcl_common \\ {dcl_common} <-: dcl_mods }
	# (saved_main_dcl_common, ti_common_defs) = replace ti_common_defs main_dcl_module_n icl_common

	#! (components, ti_common_defs, fun_defs, generic_range, td_infos, heaps, hash_table, predef_symbols, dcl_mods, optional_dcl_icl_conversions, error_admin) = 
		case SupportGenerics of
		True -> convertGenerics 
					components main_dcl_module_n ti_common_defs fun_defs td_infos 
					heaps hash_table predef_symbols dcl_mods optional_dcl_icl_conversions error_admin
		False -> (components, ti_common_defs, fun_defs, {ir_to=0,ir_from=0}, td_infos, heaps, hash_table, predef_symbols, dcl_mods, optional_dcl_icl_conversions, error_admin)	

	# (icl_common, ti_common_defs) = replace copied_ti_common_defs main_dcl_module_n saved_main_dcl_common		
		with 
			copied_ti_common_defs :: !.{#CommonDefs} // needed for Clean 2.0 to disambiguate overloading of replace
			copied_ti_common_defs = {x \\ x <-: ti_common_defs}
	# dcl_mods = { {dcl_mod & dcl_common = common} \\ dcl_mod <-: dcl_mods & common <-: ti_common_defs }
		
	# error = error_admin.ea_file
	#! ok = error_admin.ea_ok
	| not ok
		= (No,{},0,main_dcl_module_n,predef_symbols, hash_table, files, error, io, out, tcl_file, heaps)
// ..AA

	# (ok, fun_defs, array_instances, type_code_instances, common_defs, imported_funs, type_def_infos, heaps, predef_symbols, error,out)
		= typeProgram (components -*-> "Typing") main_dcl_module_n fun_defs/*icl_functions*/ icl_specials list_inferred_types icl_common [a\\a<-:icl_import] dcl_mods icl_used_module_numbers td_infos heaps predef_symbols error out dcl_mods

	| not ok
		= (No,{},0,main_dcl_module_n,predef_symbols, hash_table, files, error, io, out, tcl_file, heaps)
			

	# (fun_def_size, fun_defs) = usize fun_defs
	# (components, fun_defs) 	= partitionateFunctions (fun_defs -*-> "partitionateFunctions") [ global_fun_range, icl_instances, icl_specials, generic_range]
		
//	  (components, fun_defs, error)	= showTypes components 0 fun_defs error
//	  (components, fun_defs, error)	= showComponents components 0 True fun_defs error
//	  (fun_defs, error)	= showFunctions array_instances fun_defs error
		
	| upToPhase == FrontEndPhaseTypeCheck
		=	frontSyntaxTree cached_functions_and_macros n_functions_and_macros_in_dcl_modules main_dcl_module_n predef_symbols hash_table files error io out tcl_file icl_mod dcl_mods fun_defs components array_instances optional_dcl_icl_conversions global_fun_range heaps

	# (components, fun_defs, predef_symbols, dcl_types, used_conses_in_dynamics, var_heap, type_heaps, expression_heap, tcl_file)
	  		= convertDynamicPatternsIntoUnifyAppls type_code_instances common_defs main_dcl_module_n (components -*-> "convertDynamics") fun_defs predef_symbols
					heaps.hp_var_heap heaps.hp_type_heaps heaps.hp_expression_heap tcl_file dcl_mods icl_mod  /* TD */ directly_imported_dcl_modules
//	#  (components, fun_defs, error) = showComponents3 components 0 False fun_defs error
//	  (components, fun_defs, error)	= showComponents components 0 True fun_defs error

	| upToPhase == FrontEndPhaseConvertDynamics
		# heaps = {hp_var_heap=var_heap, hp_type_heaps=type_heaps, hp_expression_heap=expression_heap}
		=	frontSyntaxTree cached_functions_and_macros n_functions_and_macros_in_dcl_modules main_dcl_module_n predef_symbols hash_table files error io out tcl_file icl_mod dcl_mods fun_defs components array_instances optional_dcl_icl_conversions global_fun_range heaps

//	  (components, fun_defs, error) = showComponents components 0 True fun_defs error

// VZ..
// Select fusion style and do fusion
	# (components, fun_defs, dcl_types, used_conses, var_heap, type_heaps, expression_heap)
		= case opts.feo_fusionstyle of
		  	FS_offline
				# (cleanup_info, acc_args, components, fun_defs, var_heap, expression_heap)
					= analyseGroups common_defs array_instances main_dcl_module_n (components -*-> "Analyse") fun_defs var_heap expression_heap
	  			-> transformGroups cleanup_info main_dcl_module_n (components -*-> "Transform")  fun_defs acc_args common_defs imported_funs dcl_types used_conses_in_dynamics type_def_infos var_heap type_heaps expression_heap
			FS_online
				-> supercompile common_defs array_instances main_dcl_module_n (components -*-> "Supercompile") fun_defs var_heap expression_heap imported_funs dcl_types used_conses_in_dynamics type_def_infos type_heaps
			FS_none
			    -> (components, fun_defs, dcl_types, used_conses_in_dynamics, var_heap, expression_heap)
// ..VZ

	| upToPhase == FrontEndPhaseTransformGroups
		# heaps = {hp_var_heap=var_heap, hp_type_heaps=type_heaps, hp_expression_heap=expression_heap}
		=	frontSyntaxTree cached_functions_and_macros n_functions_and_macros_in_dcl_modules main_dcl_module_n predef_symbols hash_table files error io out tcl_file icl_mod dcl_mods fun_defs components array_instances optional_dcl_icl_conversions global_fun_range heaps

	# (dcl_types, used_conses, var_heap, type_heaps) = convertIclModule main_dcl_module_n common_defs (dcl_types -*-> "Convert icl") used_conses var_heap type_heaps
	# (dcl_types, used_conses, var_heap, type_heaps) = convertDclModule main_dcl_module_n dcl_mods common_defs (dcl_types -*-> "Convert dcl") used_conses var_heap type_heaps

//	  (components, fun_defs, out) = showComponents components 0 False fun_defs out

	| upToPhase == FrontEndPhaseConvertModules
		# heaps = {hp_var_heap=var_heap, hp_type_heaps=type_heaps, hp_expression_heap=expression_heap}
		=	frontSyntaxTree cached_functions_and_macros n_functions_and_macros_in_dcl_modules main_dcl_module_n predef_symbols hash_table files error io out tcl_file icl_mod dcl_mods fun_defs components array_instances optional_dcl_icl_conversions global_fun_range heaps

//	  (components, fun_defs, out) = showComponents components 0 False fun_defs out
	# (used_funs, components, fun_defs, dcl_types, used_conses, var_heap, type_heaps, expression_heap)
	  		= convertCasesOfFunctions components main_dcl_module_n imported_funs common_defs fun_defs (dcl_types -*-> "Convert cases") used_conses
					var_heap type_heaps expression_heap
	#!  (dcl_types, type_heaps, var_heap)
			= convertImportedTypeSpecifications main_dcl_module_n dcl_mods imported_funs common_defs used_conses used_funs (dcl_types -*-> "Convert types") type_heaps var_heap		
	# heaps = {hp_var_heap = var_heap, hp_expression_heap=expression_heap, hp_type_heaps=type_heaps}
//	  (components, fun_defs, error)	= showTypes components 0 fun_defs error
//	  (dcl_mods, out) = showDclModules dcl_mods out
//	  (components, fun_defs, out) = showComponents components 0 False fun_defs out

	#! 	fe ={	fe_icl =
//							 {icl_mod & icl_functions=fun_defs }
							{icl_functions=fun_defs,icl_instances=icl_instances,icl_specials=icl_specials,icl_common=icl_common,icl_import=icl_import,
							 icl_name=icl_name,icl_imported_objects=icl_imported_objects,icl_used_module_numbers=icl_used_module_numbers }

			,	fe_dcls = dcl_mods
			,	fe_components = components
			,	fe_dclIclConversions =  optional_dcl_icl_conversions
			,	fe_iclDclConversions =  build_optional_icl_dcl_conversions (size fun_defs) optional_dcl_icl_conversions
			,	fe_arrayInstances = array_instances,fe_globalFunctions=global_fun_range
			}
	= (Yes fe,cached_functions_and_macros,n_functions_and_macros_in_dcl_modules,main_dcl_module_n,predef_symbols,hash_table,files,error,io,out,tcl_file,heaps)
	where
		build_optional_icl_dcl_conversions :: !Int !(Optional {# Index}) -> Optional {# Index}
		build_optional_icl_dcl_conversions size No
			=	Yes (build_icl_dcl_conversions size {})
		build_optional_icl_dcl_conversions size (Yes dcl_icl_conversions)
			=	Yes (build_icl_dcl_conversions size dcl_icl_conversions)
	
		build_icl_dcl_conversions :: !Int !{# Index} -> {# Index}
		build_icl_dcl_conversions table_size dcl_icl_conversions
			# dcl_table_size = size dcl_icl_conversions
			  icl_dcl_conversions = update_conversion_array 0 dcl_table_size dcl_icl_conversions (createArray table_size NoIndex)
			= fill_empty_positions 0 table_size dcl_table_size icl_dcl_conversions

		update_conversion_array	dcl_index dcl_table_size dcl_icl_conversions icl_conversions
			| dcl_index < dcl_table_size
				#  icl_index = dcl_icl_conversions.[dcl_index]
				= update_conversion_array (inc dcl_index) dcl_table_size dcl_icl_conversions
						{ icl_conversions & [icl_index] = dcl_index }
				= icl_conversions
	
		fill_empty_positions next_index table_size next_new_index icl_conversions
			| next_index < table_size
				| icl_conversions.[next_index] == NoIndex
					= fill_empty_positions (inc next_index) table_size (inc next_new_index) { icl_conversions & [next_index] = next_new_index }
					= fill_empty_positions (inc next_index) table_size next_new_index icl_conversions
				= icl_conversions
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
		| show_types
			= show_component funs show_types fun_defs (file <<< fun_def.fun_type <<< '\n' <<< fun_def)
			= show_component funs show_types fun_defs (file <<< fun_def)
//		= show_component funs show_types fun_defs (file <<< fun_def.fun_symb)
			
showComponents2 :: !{! Group} !Int !*{# FunDef} !{! ConsClasses} !*File  -> (!*{# FunDef},!*File)
showComponents2 comps comp_index fun_defs acc_args file
	| comp_index >= (size comps)
		= (fun_defs, file)
	# (fun_defs, file) = show_component comps.[comp_index].group_members fun_defs acc_args file
	= showComponents2 comps (inc comp_index) fun_defs acc_args file
where
	show_component [] fun_defs _ file
		= (fun_defs, file <<< '\n')
	show_component [fun:funs] fun_defs acc_args file
		# (fd, fun_defs) = fun_defs![fun]
		# file = show_accumulating_arguments acc_args.[fun].cc_args (file <<< fd.fun_symb <<< '.' <<< fun <<< " (")
		= show_component funs fun_defs acc_args (file <<< ") ")
	
	show_accumulating_arguments [ cc : ccs] file
		| cc == cPassive
			= show_accumulating_arguments ccs (file <<< 'p')
		| cc == cActive
			= show_accumulating_arguments ccs (file <<< 'c')
		| cc == cAccumulating
			= show_accumulating_arguments ccs (file <<< 'a')
			= show_accumulating_arguments ccs (file <<< '?')
	show_accumulating_arguments [] file
		= file


show_components comps fun_defs = map (show_component fun_defs) comps

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
