implementation module frontend

import scanner, parse, postparse, check, type, trans, convertcases, overloading, utilities, convertDynamics
import RWSDebug

:: FrontEndSyntaxTree
	=	{	fe_icl :: !IclModule
		,	fe_dcls :: !{#DclModule}
		,	fe_components :: !{!Group}
		,	fe_varHeap :: !.VarHeap
// MdM
		,	fe_typeHeap :: !.TypeVarHeap
// ... MdM
		,	fe_dclIclConversions ::!Optional {# Index}
		,	fe_iclDclConversions ::!Optional {# Index}
		,	fe_globalFunctions :: !IndexRange
		,	fe_arrayInstances :: !IndexRange
		}

// trace macro
(-*->) infixl
(-*->) value trace
	:==	value // ---> trace

frontSyntaxTree predef_symbols hash_table files error io out icl_mod dcl_mods fun_defs components array_instances var_heap /* MdM */ type_heap optional_dcl_icl_conversions
	global_fun_range
	:== (predef_symbols,hash_table,files,error,io,out,
		Yes	{	fe_icl = {icl_mod & icl_functions=fun_defs }
			,	fe_dcls = dcl_mods
			,	fe_components = components
			,	fe_varHeap = var_heap
// MdM
			,	fe_typeHeap = type_heap
// ... MdM
			,	fe_dclIclConversions =  optional_dcl_icl_conversions
			,	fe_iclDclConversions =  build_optional_icl_dcl_conversions (size fun_defs) optional_dcl_icl_conversions
			,	fe_globalFunctions = global_fun_range
			,	fe_arrayInstances = array_instances
			}
		)

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

frontEndInterface :: !FrontEndPhase !Ident !SearchPaths !(Optional Bool) !*PredefinedSymbols !*HashTable !*Files !*File !*File !*File -> (!*PredefinedSymbols, !*HashTable, !*Files, !*File, !*File, !*File, !Optional *FrontEndSyntaxTree) 
frontEndInterface upToPhase mod_ident search_paths list_inferred_types predef_symbols hash_table files error io out
	# (ok, mod, hash_table, error, predef_symbols, files)
		= wantModule cWantIclFile mod_ident NoPos (hash_table -*-> ("Parsing:", mod_ident)) error search_paths predef_symbols files
	| not ok
		= (predef_symbols, hash_table, files, error, io, out, No)
	# (ok, mod, global_fun_range, mod_functions, dcl_mod, predef_mod, modules, hash_table, error, predef_symbols, files)
		= scanModule (mod -*-> "Scanning") hash_table error search_paths predef_symbols files
	| not ok
		= (predef_symbols, hash_table, files, error, io, out, No)
  	# symbol_table = hash_table.hte_symbol_heap
  	  (ok, icl_mod, dcl_mods, components, optional_dcl_icl_conversions, heaps, predef_symbols, symbol_table, error)
  	  	= checkModule mod global_fun_range mod_functions dcl_mod predef_mod modules predef_symbols (symbol_table -*-> "Checking") error
	  hash_table = { hash_table & hte_symbol_heap = symbol_table}
	| not ok
		= (predef_symbols, hash_table, files, error, io, out, No)
	# {icl_functions,icl_instances,icl_specials,icl_common,icl_declared} = icl_mod
//	  (components, icl_functions, error) = showComponents components 0 True icl_functions error

	  dcl_mods = {{dcl_mod & dcl_declared={dcls_import=[],dcls_local=[],dcls_explicit=[]}}\\ dcl_mod<-:dcl_mods}

	  var_heap = heaps.hp_var_heap
// MdM
	  type_heaps = heaps.hp_type_heaps
// ... MdM
	  fun_defs = icl_functions
	  array_instances = {ir_from=0, ir_to=0}

	| upToPhase == FrontEndPhaseCheck
		=	frontSyntaxTree predef_symbols hash_table files error io out icl_mod dcl_mods fun_defs components array_instances
// MdM
//				var_heap optional_dcl_icl_conversions global_fun_range
				var_heap type_heaps.th_vars optional_dcl_icl_conversions global_fun_range
// ... MdM

	# (ok, fun_defs, array_instances, type_code_instances, common_defs, imported_funs, heaps, predef_symbols, error, out)
		= typeProgram (components -*-> "Typing") fun_defs icl_specials list_inferred_types icl_common 
					icl_declared.dcls_import dcl_mods heaps predef_symbols error out
	| not ok
		= (predef_symbols, hash_table, files, error, io, out, No)

	# (components, fun_defs) 		= partitionateFunctions (fun_defs -*-> "partitionateFunctions") [ global_fun_range, icl_instances, icl_specials]
//	  (components, fun_defs, error)	= showTypes components 0 fun_defs error
//	  (components, fun_defs, error)	= showComponents components 0 True fun_defs error
//	  (fun_defs, error)	= showFunctions array_instances fun_defs error

	| upToPhase == FrontEndPhaseTypeCheck
		=	frontSyntaxTree predef_symbols hash_table files error io out icl_mod dcl_mods fun_defs components array_instances
// MdM
//				heaps.hp_var_heap optional_dcl_icl_conversions global_fun_range
				heaps.hp_var_heap heaps.hp_type_heaps.th_vars optional_dcl_icl_conversions global_fun_range
// ... MdM

	# (components, fun_defs, predef_symbols, dcl_types, used_conses_in_dynamics, var_heap, type_heaps, expression_heap)
	  		= convertDynamicPatternsIntoUnifyAppls type_code_instances common_defs (components -*-> "convertDynamics") fun_defs predef_symbols
					heaps.hp_var_heap heaps.hp_type_heaps heaps.hp_expression_heap

	| upToPhase == FrontEndPhaseConvertDynamics
		=	frontSyntaxTree predef_symbols hash_table files error io out icl_mod dcl_mods fun_defs components array_instances
// MdM
//				var_heap optional_dcl_icl_conversions global_fun_range
				var_heap type_heaps.th_vars optional_dcl_icl_conversions global_fun_range
// ... MdM


//	  (components, fun_defs, error) = showComponents components 0 True fun_defs error
	# (cleanup_info, acc_args, components, fun_defs, var_heap, expression_heap)
		 = analyseGroups common_defs array_instances (components -*-> "Transform") fun_defs var_heap expression_heap
	  (components, fun_defs, dcl_types, used_conses, var_heap, type_heaps, expression_heap)
	  	= transformGroups cleanup_info components fun_defs acc_args common_defs imported_funs dcl_types used_conses_in_dynamics var_heap type_heaps expression_heap

	| upToPhase == FrontEndPhaseTransformGroups
		=	frontSyntaxTree predef_symbols hash_table files error io out icl_mod dcl_mods fun_defs components array_instances
// MdM
//				var_heap optional_dcl_icl_conversions global_fun_range
				var_heap type_heaps.th_vars optional_dcl_icl_conversions global_fun_range
// ... MdM

	# (dcl_types, used_conses, var_heap, type_heaps) = convertIclModule common_defs dcl_types used_conses var_heap type_heaps
	  (dcl_types, used_conses, var_heap, type_heaps) = convertDclModule dcl_mods common_defs dcl_types used_conses var_heap type_heaps

	| upToPhase == FrontEndPhaseConvertModules
		=	frontSyntaxTree predef_symbols hash_table files error io out icl_mod dcl_mods fun_defs components array_instances
// MdM
//				var_heap optional_dcl_icl_conversions global_fun_range
				var_heap type_heaps.th_vars optional_dcl_icl_conversions global_fun_range
// ... MdM

//	  (components, fun_defs, out) = showComponents components 0 False fun_defs out
	# (used_funs, components, fun_defs, dcl_types, used_conses, var_heap, type_heaps, expression_heap)
	  		= convertCasesOfFunctionsIntoPatterns components imported_funs common_defs fun_defs dcl_types used_conses
					var_heap type_heaps expression_heap
	  (dcl_types, type_heaps, var_heap)
			= convertImportedTypeSpecifications dcl_mods imported_funs common_defs used_conses used_funs dcl_types type_heaps var_heap		
//	  (components, fun_defs, error)	= showTypes components 0 fun_defs error
//	  (components, fun_defs, out) = showComponents components 0 False fun_defs out

	=	frontSyntaxTree predef_symbols hash_table files error io out icl_mod dcl_mods fun_defs components array_instances
// MdM
//				var_heap optional_dcl_icl_conversions global_fun_range
				var_heap type_heaps.th_vars optional_dcl_icl_conversions global_fun_range
// ... MdM

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
