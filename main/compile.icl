implementation module compile

import StdEnv
import frontend
import backendinterface
import CoclSystemDependent
import RWSDebug

::	CoclOptions =
	{
		moduleName
			:: {#Char}
	,	pathName ::
			{#Char}
	,	errorPath
			:: {#Char}
	,	errorMode
			::	Int
	,	outPath
			:: {#Char}
	,	outMode
			::	Int
	,	searchPaths
			:: SearchPaths
	}

InitialCoclOptions =
	{	moduleName
			=	""
	,	pathName
			=	""
	,	errorPath
			=	"errors"
	,	errorMode
			=	FWriteText
	,	outPath
			=	"out"
	,	outMode
			=	FWriteText
	,	searchPaths
			=	{sp_locations = [], sp_paths = []}
	}

compile :: [{#Char}] *Files -> (!Bool, !*Files)
compile args files
	# (args_without_modules,modules,cocl_options) = parseCommandLine args InitialCoclOptions
	# heaps = { hp_var_heap = newHeap, hp_expression_heap = newHeap, hp_type_heaps = { th_vars = newHeap, th_attrs = newHeap }}
	# (predef_symbols, hash_table) = buildPredefinedSymbols newHashTable
	= compile_modules modules 0 cocl_options args_without_modules {} {} predef_symbols hash_table heaps files;

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

compile_modules [module_:modules] n_compiles cocl_options args_without_modules dcl_modules functions_and_macros predef_symbols hash_table heaps files
	# cocl_options = prependModulePath {cocl_options & pathName=stripExtension ".icl" (stripQuotes module_)}
		with
		// RWS +++ hack, both module name and file path should be passed to frontEndInterface
		prependModulePath options=:{pathName, searchPaths}
			=	{	options
				&	moduleName = baseName pathName
					// RWS, voor Maarten +++				,	searchPaths = {searchPaths & sp_paths = [directoryName pathName : searchPaths.sp_paths]}
//				,	searchPaths = [directoryName pathName : searchPaths]
				}
	# (ok,dcl_modules,functions_and_macros,n_functions_and_macros_in_dcl_modules,predef_symbols,hash_table,heaps,files)
		= compileModule cocl_options (args_without_modules++[module_]) dcl_modules functions_and_macros predef_symbols hash_table heaps files;
	| ok
//		# hash_table=remove_module_idents_from_symbol_table 0 dcl_modules hash_table;
/*		# hash_table=remove_module_ident_from_symbol_table dcl_modules.[0] hash_table;
			with
			remove_module_idents_from_symbol_table module_n dcl_modules hash_table
				| module_n==size dcl_modules
					= hash_table;
					# hash_table = remove_module_ident_from_symbol_table dcl_modules.[module_n] hash_table
					= remove_module_idents_from_symbol_table (module_n+1) dcl_modules hash_table

			remove_module_ident_from_symbol_table dcl_module hash_table
					# module_symbol_pointer = dcl_module.dcl_name.id_info;
					# symbol_heap=hash_table.hte_symbol_heap;
					# (hte_entry,symbol_heap) = readPtr module_symbol_pointer symbol_heap
					# symbol_heap=writePtr module_symbol_pointer {hte_entry & ste_kind=STE_Empty} symbol_heap
					= {hash_table & hte_symbol_heap=symbol_heap}
		# dcl_modules = {dcl_modules.[module_n] \\ module_n <-[1..size dcl_modules-1]}
*/
/*
		# heaps = { hp_var_heap = newHeap, hp_expression_heap = newHeap, hp_type_heaps = { th_vars = newHeap, th_attrs = newHeap }}
		# (predef_symbols, hash_table) = buildPredefinedSymbols newHashTable
		= compile_modules modules 0 cocl_options args_without_modules {} {} predef_symbols hash_table heaps files;
*/
		= compile_modules modules (n_compiles+1) cocl_options args_without_modules dcl_modules functions_and_macros predef_symbols hash_table heaps files;

		= (ok,files);
compile_modules [] n_compiles cocl_options args_without_modules dcl_modules functions_and_macros predef_symbols hash_table heaps files
	= (True,files);

compileModule :: CoclOptions [{#Char}] {#DclModule} {#FunDef} *PredefinedSymbols !*HashTable *Heaps *Files -> (!Bool,!{#DclModule},!{#FunDef},!Int,!*PredefinedSymbols,!*HashTable,!*Heaps, !*Files)
compileModule options commandLineArgs dcl_modules functions_and_macros predef_symbols hash_table heaps files
	# (opened, error, files)
		=	fopen options.errorPath options.errorMode files
	| not opened
		=	abort ("couldn't open error file \"" +++ options.errorPath +++ "\"\n")
	# (opened, out, files)
		=	fopen options.outPath options.outMode files
	| not opened
		=	abort ("couldn't open out file \"" +++ options.outPath +++ "\"\n")
	# (io, files)
		=	stdio files
//	  (moduleIdent, hash_table) = putIdentInHashTable options.moduleName IC_Module hash_table
	# ({boxed_ident=moduleIdent}, hash_table) = putIdentInHashTable options.moduleName IC_Module hash_table
	#  list_inferred_types = if (isMember "-lt" commandLineArgs) (Yes (not (isMember "-lattr" commandLineArgs))) No
	# (optionalSyntaxTree,cached_functions_and_macros,n_functions_and_macros_in_dcl_modules,main_dcl_module_n,predef_symbols, hash_table, files, error, io, out,heaps)
		=	frontEndInterface FrontEndPhaseAll moduleIdent options.searchPaths dcl_modules functions_and_macros No predef_symbols hash_table files error io out heaps
	# unique_copy_of_predef_symbols={predef_symbol\\predef_symbol<-:predef_symbols}
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
		=	case optionalSyntaxTree of
				Yes syntaxTree
					# dcl_modules=syntaxTree.fe_dcls
					# functions_and_macros = syntaxTree.fe_icl.icl_functions
					# (success,var_heap,error, files) = backEndInterface outputPath (map appendRedirection commandLineArgs) predef_symbols syntaxTree main_dcl_module_n var_heap error files
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
		=	(success,dcl_modules,cached_functions_and_macros,n_functions_and_macros_in_dcl_modules,unique_copy_of_predef_symbols,hash_table,heaps,files)
		=	(success,dcl_modules,cached_functions_and_macros,n_functions_and_macros_in_dcl_modules,unique_copy_of_predef_symbols,hash_table,heaps,files)
