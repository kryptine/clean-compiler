implementation module compile

// $Id$

// vi:set tabstop=4 noet:

import StdEnv
import frontend
import backendinterface
import CoclSystemDependent
import portToNewSyntax
//import RWSDebug

// MV ...
generate_tcl_file :== False;
// ... MV

::	CoclOptions =
	{
		moduleName:: {#Char}
	,	pathName ::{#Char}
	,	errorPath:: {#Char}
	,	errorMode::	Int
	,	outPath:: {#Char}
	,	outMode::	Int
	,	searchPaths:: SearchPaths
// MV ...
	,	compile_for_dynamics	:: !Bool
// ... MV
// VZ ...
	,	supercompilation :: !Bool
// ... VZ
	}

InitialCoclOptions =
	{	moduleName=	""
	,	pathName=	""
	,	errorPath=	"errors"
	,	errorMode=	FWriteText
	,	outPath=	"out"
	,	outMode=	FWriteText
	,	searchPaths=	{sp_locations = [], sp_paths = []}
// MV ...
	,	compile_for_dynamics	= False
// ... MV
// VZ ...
	,	supercompilation = False
// ... VZ
	}

:: DclCache = {
	dcl_modules::!{#DclModule},
	functions_and_macros::!{#FunDef},
	predef_symbols::!.PredefinedSymbols,
	hash_table::!.HashTable,
	heaps::!.Heaps
 };

empty_cache :: *DclCache
empty_cache
	# heaps = {hp_var_heap = newHeap, hp_expression_heap = newHeap, hp_type_heaps = {th_vars = newHeap, th_attrs = newHeap}}
	# (predef_symbols, hash_table) = buildPredefinedSymbols newHashTable
	= {dcl_modules={},functions_and_macros={},predef_symbols=predef_symbols,hash_table=hash_table,heaps=heaps}

compile :: ![{#Char}] !*DclCache !*Files -> (!Bool,!*DclCache,!*Files)
compile args cache files
	# (args_without_modules,modules,cocl_options) = parseCommandLine args InitialCoclOptions
	= compile_modules modules 0 cocl_options args_without_modules cache files;

// WARNING:
// if you add an option which is not supported by the backend, then you should remove it from
// the first list in the tuple returned by parseCommandLine
parseCommandLine :: [{#Char}] CoclOptions -> ([{#Char}],[{#Char}],CoclOptions)
parseCommandLine [] options
	=	([],[],options)
/*
	// JVG: removed hack because the searchPaths list becomes too large when >1 file is compiled
	=	prependModulePath options
	where
		// RWS +++ hack, both module name and file path should be passed to frontEndInterface
		prependModulePath options=:{pathName, searchPaths}
			=	{	options
				&	moduleName = baseName pathName
				,	searchPaths = {searchPaths & sp_paths = [directoryName pathName : searchPaths.sp_paths]}
				}
*/
parseCommandLine [arg1=:"-P", searchPathsString : args] options=:{searchPaths}
// RWS, voor Maarten +++	=	parseCommandLine args {options & searchPaths = {searchPaths & sp_paths = splitPaths searchPathsString}}
	# (args,modules,options) =	parseCommandLine args {options & searchPaths.sp_paths = splitPaths searchPathsString}
	= ([arg1,searchPathsString:args],modules,options)
parseCommandLine [arg1=:"-RO", outPath : args] options
	# (args,modules,options)=	parseCommandLine args {options & outPath = stripQuotes outPath, outMode = FWriteText}
	= ([arg1,outPath:args],modules,options)
parseCommandLine [arg1=:"-RAO", outPath : args] options
	# (args,modules,options)=	parseCommandLine args {options & outPath = stripQuotes outPath, outMode = FAppendText}
	= ([arg1,outPath:args],modules,options)
parseCommandLine [arg1=:"-RE", errorPath : args] options
	# (args,modules,options)=	parseCommandLine args {options & errorPath = stripQuotes errorPath, errorMode = FWriteText}
	= ([arg1,errorPath:args],modules,options)
parseCommandLine [arg1=:"-RAE", errorPath : args] options
	# (args,modules,options)=	parseCommandLine args {options & errorPath = stripQuotes errorPath, errorMode = FAppendText}
	= ([arg1,errorPath:args],modules,options)
// MV ...
parseCommandLine [arg1=:"-dynamics":args] options
	// generates for each icl an tcl (which contains the type information for that module)
	# (args,modules,options)=	parseCommandLine args {options & compile_for_dynamics = True}
	= (args,modules,options)
// ... MV

// VZ ...
	// Select supercompilation instead of standard fusion
parseCommandLine [arg1=:"-SC":args] options
	# (args,modules,options) = parseCommandLine args {options & supercompilation = True}
	= (args,modules,options)
// ... VZ

parseCommandLine [arg : args] options
	| arg.[0] == '-'
		# (args,modules,options)=	parseCommandLine args options
		= ([arg:args],modules,options)
	// otherwise
		# (args,modules,options) = parseCommandLine args options
		= (args,[arg : modules],options);

stripExtension :: {#Char} {#Char} -> {#Char}
stripExtension extension string
	| stringSize >= extensionSize && (string % (stringSize-extensionSize, stringSize-1)) == extension
		=	string % (0, stringSize-extensionSize-1)
	// otherwise
		=	string
	where
		stringSize
			=	size string
		extensionSize
			=	size extension

stripQuotes :: {#Char} -> {#Char}
stripQuotes string
	| stringSize > 1 && string.[0] == '"' && string.[stringSize-1] == '"'
		=	string % (1, stringSize-2)
	// otherwise
		=	string
	where
		stringSize
			=	size string

splitPaths :: {#Char} -> [{#Char}]
splitPaths paths
	=	[path +++ {DirectorySeparator} \\ path <- splitBy PathSeparator paths]

splitBy :: Char {#Char} -> [{#Char}]
splitBy char string
	=	splitBy` 0 0
	where
		splitBy` frm to
			| to >= stringSize
				=	[string % (frm, to-1)]
			| string.[to] == char
				=	[string % (frm, to-1) : splitBy` (to+1) (to+1)]
			// otherwise
				=	splitBy` frm (to+1)
		stringSize
			=	size string

baseName :: {#Char} -> {#Char}
baseName path
	=	last (splitBy DirectorySeparator path)

directoryName :: {#Char} -> {#Char}
directoryName path
	=	foldr (\p ps -> p +++ {DirectorySeparator} +++ ps) "" (init (splitBy DirectorySeparator path))

compile_modules [module_:modules] n_compiles cocl_options args_without_modules cache files
	# cocl_options = prependModulePath {cocl_options & pathName=stripExtension ".icl" (stripQuotes module_)}
		with
		// RWS +++ hack, both module name and file path should be passed to frontEndInterface
		prependModulePath options=:{pathName, searchPaths}
			=	{	options
				&	moduleName = baseName pathName
					// RWS, voor Maarten +++				,	searchPaths = {searchPaths & sp_paths = [directoryName pathName : searchPaths.sp_paths]}
//				,	searchPaths = [directoryName pathName : searchPaths]
				}
	# (ok,cache,files)
		= compileModule cocl_options (args_without_modules++[module_]) cache files;
	| ok
/*
		# heaps = { hp_var_heap = newHeap, hp_expression_heap = newHeap, hp_type_heaps = { th_vars = newHeap, th_attrs = newHeap }}
		# (predef_symbols, hash_table) = buildPredefinedSymbols newHashTable
		= compile_modules modules 0 cocl_options args_without_modules {} {} predef_symbols hash_table heaps files;
*/
		= compile_modules modules (n_compiles+1) cocl_options args_without_modules cache files;

		= (ok,cache,files);
compile_modules [] n_compiles cocl_options args_without_modules cache files
	= (True,cache,files);

compileModule :: CoclOptions [{#Char}] *DclCache *Files -> (!Bool,!*DclCache,!*Files)
compileModule options commandLineArgs {dcl_modules,functions_and_macros,predef_symbols,hash_table,heaps} files
	# (opened, error, files)
		=	fopen options.errorPath options.errorMode files
	| not opened
		=	abort ("couldn't open error file \"" +++ options.errorPath +++ "\"\n")
	# (opened, out, files)
		=	fopen options.outPath options.outMode files
	| not opened
		=	abort ("couldn't open out file \"" +++ options.outPath +++ "\"\n")
	# (tcl_file, files)
		= openTclFile options options.pathName files
	# (io, files)
		=	stdio files
//	  (moduleIdent, hash_table) = putIdentInHashTable options.moduleName IC_Module hash_table
	# ({boxed_ident=moduleIdent}, hash_table) = putIdentInHashTable options.moduleName IC_Module hash_table
// VZ..
	# feopts
		=	{	feo_upToPhase		= FrontEndPhaseAll
			,	feo_search_paths	= options.searchPaths
			,	feo_typelisting		= if (isMember "-lt" commandLineArgs) (Yes (not (isMember "-lattr" commandLineArgs))) No
			,	feo_fusionstyle		= if options.supercompilation FS_online FS_offline
			}
	# (optionalSyntaxTree,cached_functions_and_macros,n_functions_and_macros_in_dcl_modules,main_dcl_module_n,predef_symbols, hash_table, files, error, io, out,tcl_file,heaps)
		=	frontEndInterface feopts moduleIdent dcl_modules functions_and_macros predef_symbols hash_table files error io out tcl_file heaps
// ..VZ
	# unique_copy_of_predef_symbols={predef_symbol\\predef_symbol<-:predef_symbols}

// MV ...
	# (closed, files)
		= closeTclFile tcl_file files
// ... MV
	| not closed
		=	abort ("couldn't close tcl file \"" +++ options.pathName +++ "tcl\"\n")

	# (closed, files)
		=	fclose io files
	| not closed
		=	abort ("couldn't close stdio")
	# (closed, files)
		=	fclose out files
	| not closed
		=	abort ("couldn't close out file \"" +++ options.outPath +++ "\"\n")
	# var_heap=heaps.hp_var_heap
	# (success,dcl_modules,functions_and_macros,n_functions_and_macros_in_dcl_modules,var_heap,error, files)
		= case optionalSyntaxTree of
			Yes syntaxTree
				# dcl_modules=syntaxTree.fe_dcls
				# functions_and_macros = syntaxTree.fe_icl.icl_functions
				# (porting_ok, files)
					 = switch_port_to_new_syntax 
							(createPortedFiles options.moduleName options.searchPaths files)
							(False, files)
				  error = switch_port_to_new_syntax 
				  			(case porting_ok of
				  				True
				  					-> error
				  				False
				  					-> error <<< "Error: couldn't write ported versions of module "
				  							 <<< options.moduleName <<< '\n')
				  			error
				# (success,var_heap,error, files)
					= backEndInterface outputPath (map appendRedirection commandLineArgs) predef_symbols syntaxTree main_dcl_module_n var_heap error files
				-> (success,dcl_modules,functions_and_macros,n_functions_and_macros_in_dcl_modules,var_heap,error, files)
				with
					appendRedirection arg
						= case arg of
							"-RE"
								-> "-RAE"
							"-RO"
								-> "-RAO"
							arg
								->	arg
			No
				-> (False,{},{},0,var_heap,error, files)
		with
			outputPath
	//				=	/* directoryName options.pathName +++ "Clean System Files" +++ {DirectorySeparator} +++ */ baseName options.pathName
				=	baseName options.pathName
	# heaps = {heaps & hp_var_heap=var_heap}
	# (closed, files)
		=	fclose error files
	| not closed
		=	abort ("couldn't close error file \"" +++ options.errorPath +++ "\"\n")
	| success
		# dcl_modules={{dcl_module \\ dcl_module<-:dcl_modules} & [main_dcl_module_n].dcl_conversions=No}
		# cache={dcl_modules=dcl_modules,functions_and_macros=cached_functions_and_macros,predef_symbols=unique_copy_of_predef_symbols,hash_table=hash_table,heaps=heaps}
		= (success,cache,files)
		# cache={dcl_modules=dcl_modules,functions_and_macros=cached_functions_and_macros,predef_symbols=unique_copy_of_predef_symbols,hash_table=hash_table,heaps=heaps}
		= (success,cache,files)

// MV ...
openTclFile :: CoclOptions !String !*Files -> (Optional !.File, !*Files)
openTclFile options=:{compile_for_dynamics=False} icl_mod_pathname files
	= (No,files)
openTclFile options icl_mod_pathname files
	# csf_path
		= directoryName icl_mod_pathname +++ "Clean System Files"
	# tcl_path
		= csf_path +++ {DirectorySeparator} +++ baseName icl_mod_pathname +++ ".tcl"
	# (opened, tcl_file, files)
		= fopen tcl_path FWriteData files
	| opened
		= (Yes tcl_file, files)
	// try again after creating Clean System Files folder
	# (ok, files)
		= ensureCleanSystemFilesExists csf_path files
	| not ok
		= abort ("can't create folder \"" +++ csf_path +++"\"\n")
	# (opened, tcl_file, files)
		= fopen tcl_path FWriteData files
	| opened
		=(Yes tcl_file, files)
	= abort ("couldn't open file \"" +++ tcl_path +++ "\"\n")
	
closeTclFile (Yes tcl_file) files
	= fclose tcl_file files
closeTclFile _ files
	= (True,files);
// ... MV

