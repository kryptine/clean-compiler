module main

import scanner, parse, postparse, check, type, trans, convertcases, utilities, convertDynamics

import StdEnv

Start world
	# (std_io, world) = stdio world
	  (_, ms_out, world) = fopen "out" FWriteText world
	  (ms_out,world) = accFiles (
	  		\files -> 
				(let
				    (ms_paths, ms_files, ms_error) = converFileToListOfStrings "mainPrefs" files stderr
					ms = CommandLoop No { ms_io = std_io, ms_out = ms_out, ms_error = ms_error, ms_files = ms_files, ms_paths = ms_paths }
				in
					(ms.ms_out, ms.ms_files))) world
	= fclose ms_out world

CommandLoop proj ms=:{ms_io}
	# (answer, ms_io)		= freadline (ms_io <<< "> ")
	  (command, argument)	= SplitAtLayoutChar (dropWhile isSpace (fromString answer))
	| command == []
		= CommandLoop proj { ms & ms_io = ms_io}
		# (ready, proj, ms) = DoCommand command argument proj { ms & ms_io = ms_io}
		| ready
			= ms
			= CommandLoop proj ms

::	MainStateDefs funs funtypes types conses classes instances members selectors =
	{	msd_funs		:: !funs
	,	msd_funtypes	:: !funtypes
	,	msd_types		:: !types
	,	msd_conses		:: !conses
	,	msd_classes		:: !classes
	,	msd_instances	:: !instances
	,	msd_members		:: !members
	,	msd_selectors	:: !selectors
	,	msd_genfuns		:: ![FunDef]
	}
	

::	*MainState funs funtypes types conses classes instances members selectors =
	{	ms_io			:: !*File
	,	ms_error		:: !*File
	,	ms_out			:: !*File
	,	ms_paths		:: !SearchPaths
	,	ms_files		:: !*Files
	}	

::	ModuleTree = ModuleNode !InterMod !ModuleTree !ModuleTree | NoModules

containsModule name (ModuleNode {inter_name = {id_name}} left right)
	# cmp = id_name =< name
	| cmp == Equal
		= True
	| cmp == Smaller
		= containsModule name right
		= containsModule name left
containsModule name NoModules
	= False

addModule name mod tree=:(ModuleNode this_mod=:{inter_name = {id_name}} left right)
	# cmp = id_name =< name
	| cmp == Equal
		= tree
	| cmp == Smaller
		= ModuleNode this_mod left (addModule name mod right)
		= ModuleNode this_mod (addModule name mod left) right
addModule _ mod NoModules
	= ModuleNode mod NoModules NoModules

::	Project =
	{	proj_main_module	:: !Ident
	,	proj_hash_table		:: !.HashTable
	,	proj_predef_symbols	:: !.PredefinedSymbols
	,	proj_modules		:: !ModuleTree
	}

::	InterMod =
	{	inter_name					:: Ident
	,	inter_modules				:: !{# Ident}
	,	inter_fun_defs				:: !{# FunDef}
	,	inter_icl_dcl_conversions	:: !Optional {# Index}
	,	inter_dcl_icl_conversions	:: !Optional {# Index}
	}


DoCommand ['c':_] argument proj ms 
	# (file_name, rest_input) = SplitAtLayoutChar (dropWhile isSpace argument)
	  (opt_mod, ms) = compileModule (toString file_name) ms
	= (False, proj, ms)
DoCommand ['s':_] argument proj ms=:{ms_io, ms_files} 
	# (file_name, rest_input)	= SplitAtLayoutChar (dropWhile isSpace argument)
	  file_name 				= toString (file_name++['.icl'])
	  (ok,file,files)			= fopen file_name FReadText ms_files
	  (lines,file)				= freadlines file
	  (ok,files)				= fclose file files
	= (False, proj, {ms & ms_io = ms_io <<< ("file "+++file_name+++" "+++toString (length lines)+++" lines\n") <<< lines <<< "\n", ms_files = files})
DoCommand ['t':_] argument proj ms=:{ms_files, ms_io}
	# (file_names, ms_files, ms_io) = converFileToListOfStrings "testfiles" ms_files ms_io
	= (False, proj, foldSt check_module file_names { ms & ms_files = ms_files, ms_io = ms_io })
where
	check_module file_name ms
  		# (opt_mod, ms) = compileModule file_name (ms ---> file_name)
		= case opt_mod of
			No
				-> { ms & ms_io = ms.ms_io <<< file_name <<< " is not OK\n" }
			_
				-> ms
DoCommand ['p':_] argument proj ms=:{ms_io, ms_files}
	# (file_name, rest_input)		= SplitAtLayoutChar (dropWhile isSpace argument)
	  (predef_symbols, hash_table) 	= buildPredefinedSymbols newHashTable
	  (mod_ident, hash_table) 		= putIdentInHashTable (toString file_name) IC_Module hash_table
	= (False, Yes { proj_main_module = mod_ident, proj_hash_table = hash_table, proj_predef_symbols = predef_symbols, proj_modules = NoModules }, ms)
DoCommand ['q':_] argument proj ms
	= (True, proj, ms)
DoCommand ['h':_] argument proj  ms=:{ms_io}
	= (False, proj, {ms & ms_io = ms_io <<< "No help available. Sorry.\n"})
DoCommand command argument proj  ms=:{ms_io}
	= (False, proj, {ms & ms_io = ms_io <<< toString command <<< "?\n"})

freadlines file
    |   sfend file
        =   ([],file)
	    #   (line, file)    = freadline file
   		#   (lines,file)    = freadlines file
        =   ([line:lines],file)

SplitAtLayoutChar [] = ([], [])
SplitAtLayoutChar [x:xs]
	| x == ' ' || x == '\t' || x == '\n'
		= ([], xs)
	| otherwise
		= ([x:word], rest_input)
where
	(word, rest_input) = SplitAtLayoutChar xs

compileModule mod_name ms
	# (predef_symbols, hash_table) = buildPredefinedSymbols newHashTable
	  (mod_ident, hash_table) = putIdentInHashTable mod_name IC_Module hash_table
	  (opt_module, predef_symbols, hash_table, ms) = loadModule mod_ident predef_symbols hash_table ms
	= (opt_module, ms)

loadModule mod_ident predef_symbols hash_table ms=:{ms_files,ms_error,ms_io,ms_out,ms_paths}
	# (ok, mod, hash_table, ms_error, predef_symbols, ms_files)
		= wantModule cWantIclFile mod_ident (hash_table ---> ("Parsing:", mod_ident)) ms_error ms_paths predef_symbols ms_files
	| not ok
		= (No,  predef_symbols, hash_table, { ms & ms_files = ms_files, ms_io = ms_io, ms_error = ms_error })
	# (ok, mod, nr_of_global_funs, mod_functions, dcl_mod, predef_mod, modules, hash_table, ms_error, predef_symbols, ms_files)
		= scanModule (mod ---> "Scanning") hash_table ms_error ms_paths predef_symbols ms_files
	| not ok
		= (No,  predef_symbols, hash_table, { ms & ms_files = ms_files, ms_io = ms_io, ms_error = ms_error })
  	# symbol_table = hash_table.hte_symbol_heap
  	  (ok, icl_mod, dcl_mods, components, dcl_icl_conversions, heaps, predef_symbols, symbol_table, ms_error)
  	  	= checkModule mod nr_of_global_funs mod_functions dcl_mod predef_mod modules predef_symbols (symbol_table ---> "Checking") ms_error
	| not ok
		= (No,  predef_symbols, { hash_table & hte_symbol_heap = symbol_table}, { ms & ms_files = ms_files, ms_error = ms_error, ms_io = ms_io })
	# {icl_functions,icl_instances,icl_specials,icl_common,icl_declared={dcls_import}} = icl_mod
//	  (components, icl_functions, ms_error) = showComponents components 0 True icl_functions ms_error
	  (ok, fun_defs, array_instances, type_code_instances, common_defs, imported_funs, heaps, predef_symbols, ms_error)
		= typeProgram (components ---> "Typing") icl_functions icl_specials icl_common dcls_import dcl_mods heaps predef_symbols ms_error
	| not ok
		= (No,  predef_symbols, { hash_table & hte_symbol_heap = symbol_table}, { ms & ms_files = ms_files, ms_error = ms_error, ms_io = ms_io, ms_out = ms_out })

	# (components, fun_defs) = partitionateFunctions (fun_defs ---> "partitionateFunctions") [ { ir_from = 0, ir_to = nr_of_global_funs }, icl_instances, icl_specials]
	  (components, fun_defs, ms_io) = showTypes components 0 fun_defs ms_io
//	  (components, fun_defs, ms_out) = showComponents components 0 True fun_defs ms_out
	  (acc_args, components, fun_defs, var_heap) = analyseGroups (components ---> "Transform") fun_defs heaps.hp_var_heap
	  (components, fun_defs, dcl_types, used_conses, var_heap, type_heaps, expression_heap)
	  		= transformGroups components fun_defs acc_args common_defs imported_funs var_heap heaps.hp_type_heaps heaps.hp_expression_heap
//	  (components, fun_defs, ms_error) = showComponents components 0 True fun_defs ms_error
	  (dcl_types, used_conses, var_heap, type_heaps) = convertIclModule common_defs dcl_types used_conses var_heap type_heaps
	  (dcl_types, used_conses, var_heap, type_heaps) = convertDclModule dcl_mods common_defs dcl_types used_conses var_heap type_heaps
	  (components, fun_defs, predef_symbols, dcl_types, used_conses, var_heap, type_heaps, expression_heap)
	  		= convertDynamicPatternsIntoUnifyAppls type_code_instances common_defs (components ---> "convertDynamics") fun_defs predef_symbols
					dcl_types used_conses var_heap type_heaps expression_heap
	  (components, fun_defs, ms_out) = showComponents components 0 True fun_defs ms_out
	  (used_funs, components, fun_defs, dcl_types, used_conses, var_heap, type_heaps, expression_heap)
	  		= convertCasesOfFunctionsIntoPatterns components imported_funs common_defs fun_defs dcl_types used_conses var_heap type_heaps expression_heap
	  (dcl_types, var_heap, type_heaps)
			= convertImportedTypeSpecifications dcl_mods imported_funs common_defs used_conses used_funs dcl_types type_heaps var_heap		
//	  (components, fun_defs, ms_out) = showComponents components 0 False fun_defs ms_out
	= (Yes (buildInterMod mod_ident dcl_mods fun_defs dcl_icl_conversions),  predef_symbols,
		{ hash_table & hte_symbol_heap = symbol_table}, { ms & ms_files = ms_files, ms_error = ms_error, ms_io = ms_io, ms_out = ms_out })


makeProject (Yes proj=:{proj_main_module,proj_hash_table,proj_predef_symbols}) ms
	# (main_mod, proj_predef_symbols, proj_hash_table, ms) = loadModule proj_main_module proj_predef_symbols proj_hash_table ms
	  proj = { proj & proj_hash_table = proj_hash_table, proj_predef_symbols = proj_predef_symbols }
	= case main_mod of
		Yes main_mod=:{inter_modules}
			# (proj_modules, ms) = collect_modules [ mod \\ mod <-: inter_modules ] (ModuleNode main_mod NoModules NoModules) ms
			-> (Yes { proj & proj_modules = proj_modules }, ms)
		_
			-> (Yes proj, ms)
where
	collect_modules [{id_name} : modules] collected_modules ms
		| containsModule id_name collected_modules
			= collect_modules modules collected_modules ms
			# (this_mod, ms) = compileModule id_name ms
			= case this_mod of
				Yes new_mod
					-> collect_modules (modules ++ [ mod \\ mod <-: new_mod.inter_modules ]) (addModule id_name new_mod collected_modules) ms
				_
					-> (NoModules, ms)
	collect_modules [{id_name} : modules] collected_modules ms
		= (collected_modules, ms)

buildInterMod name dcl_modules fun_defs dcl_icl_conversions
	=	{	inter_name					= name
		,	inter_modules				= { dcl_name \\ {dcl_name} <-: dcl_modules }
		,	inter_fun_defs				= fun_defs
		,	inter_icl_dcl_conversions	= build_icl_dcl_conversions (size fun_defs) dcl_icl_conversions
		,	inter_dcl_icl_conversions	= dcl_icl_conversions
		}
where
	build_icl_dcl_conversions table_size (Yes conversion_table)
		# dcl_table_size = size conversion_table
		  icl_dcl_conversions = update_conversion_array 0 dcl_table_size conversion_table (createArray table_size NoIndex)
		= Yes (fill_empty_positions 0 table_size dcl_table_size icl_dcl_conversions)
	build_icl_dcl_conversions table_size No
		= No
		
	update_conversion_array	dcl_index dcl_table_size conversion_table icl_conversions
		| dcl_index < dcl_table_size
			#  icl_index = conversion_table.[dcl_index]
			= update_conversion_array (inc dcl_index) dcl_table_size conversion_table
					{ icl_conversions & [icl_index] = dcl_index }
			= icl_conversions

	fill_empty_positions next_index table_size next_new_index icl_conversions
		| next_index < table_size
			| icl_conversions.[next_index] == NoIndex
				= fill_empty_positions (inc next_index) table_size (inc next_new_index) { icl_conversions & [next_index] = next_new_index }
				= fill_empty_positions (inc next_index) table_size next_new_index icl_conversions
			= icl_conversions
			
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
		#! fun_def = fun_defs.[fun]
		| show_types
			= show_component funs show_types fun_defs (file <<< '\n' <<< fun_def)
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
		#! fd = fun_defs.[fun]
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
		#! fun_def = fun_defs.[fun]
		= show_types funs fun_defs (file <<< '\n' <<< fun_def.fun_type)

converFileToListOfStrings file_name files error
	# (ok, file, files) = fopen file_name FReadText files
	| ok
		# (lines, file) = read_lines file
		= (lines, snd (fclose file files), error)
		= ([], files, error <<< "Could not open \"" <<< file_name <<< "\"\n")
where
	read_lines file
		# (line, file) = freadline file
		  last_char_index = size line - 1
		| last_char_index < 0
			= ([], file)
		| line.[last_char_index] == '\n'
			| last_char_index == 0 || line.[0] == '|'
				= read_lines file
				# (lines, file) = read_lines file
				= ([line % (0, last_char_index - 1) : lines ], file)
		// otherwise
			= ([line], file)
