module main

import scanner, parse, postparse, check, type, trans, convertcases, utilities, convertDynamics

import StdEnv
// RWS ...
import frontend
// ... RWS

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
	,	ms_paths		:: ![{#Char}]
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
	# (predef_symbols, hash_table, ms_files, ms_error, ms_io, ms_out, optional_syntax_tree)
		=	frontEndInterface FrontEndPhaseAll mod_ident {sp_locations = [], sp_paths = ms_paths} False predef_symbols hash_table ms_files ms_error ms_io ms_out
	  ms
	  	=	{ms & ms_files=ms_files, ms_error=ms_error,ms_io=ms_io,ms_out=ms_out}
	= case optional_syntax_tree of
		Yes {fe_icl={icl_functions}, fe_dcls, fe_dclIclConversions, fe_iclDclConversions}
			->	(Yes (buildInterMod mod_ident fe_dcls icl_functions fe_dclIclConversions fe_iclDclConversions), predef_symbols, hash_table, ms)
		No
			->	(No, predef_symbols, hash_table, ms)

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

buildInterMod name dcl_modules fun_defs dcl_icl_conversions /* RWS ... */ icl_dcl_conversions /* ... RWS */
	=	{	inter_name					= name
		,	inter_modules				= { dcl_name \\ {dcl_name} <-: dcl_modules }
		,	inter_fun_defs				= fun_defs
/* RWS ...
		,	inter_icl_dcl_conversions	= build_icl_dcl_conversions (size fun_defs) dcl_icl_conversions
*/
		,	inter_icl_dcl_conversions	= icl_dcl_conversions
/* ... RWS */
		,	inter_dcl_icl_conversions	= dcl_icl_conversions
		}
/* RWS
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
*/

/* RWS			
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
		# properties = { form_properties = cAttributed bitor cAnnotated, form_attr_position = No }
		  (Yes ftype) = fun_def.fun_type
		= show_types funs fun_defs (file <<< fun_def.fun_symb <<< " :: " <:: (properties, ftype) <<< '\n' )
*/

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
