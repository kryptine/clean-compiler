/*
	module owner: Ronny Wichers Schreur
*/
implementation module compile

import StdEnv
import frontend
import backendinterface
import filesystem, CoclSystemDependent
import portToNewSyntax
import compilerSwitches
//import RWSDebug
from type_io import openTclFile, closeTclFile, baseName, directoryName, splitBy


::	CoclOptions =
	{	moduleName:: {#Char}
	,	pathName ::{#Char}
	,	errorPath:: {#Char}
	,	errorMode::	Int
	,	outPath:: {#Char}
	,	outMode::	Int
	,	searchPaths:: SearchPaths
	,	listTypes :: ListTypesOption
	,	compile_for_dynamics	:: !Bool
	,	support_generics 		:: !Bool
	,	compile_with_fusion		:: !Bool
	,	compile_with_generics   :: !Bool
	}

InitialCoclOptions =
	{	moduleName=	""
	,	pathName=	""
	,	errorPath=	"errors"
	,	errorMode=	FWriteText
	,	outPath=	"out"
	,	outMode=	FWriteText
	,	searchPaths=	{sp_locations = [], sp_paths = []}
	,	listTypes = {lto_showAttributes = True, lto_listTypesKind = ListTypesNone}
	,	compile_for_dynamics	= False
	, 	support_generics 		= True	//???
	,	compile_with_fusion		= False
	,	compile_with_generics 	= True 
	}

:: DclCache = {
	dcl_modules::!{#DclModule},
	functions_and_macros::!.{#.{#FunDef}},
	predef_symbols::!.PredefinedSymbols,
	hash_table::!.HashTable,
	heaps::!.Heaps
 };

empty_cache :: *SymbolTable -> *DclCache
empty_cache symbol_heap
	# heaps = {hp_var_heap = newHeap, hp_expression_heap = newHeap, hp_type_heaps = {th_vars = newHeap, th_attrs = newHeap}, hp_generic_heap = newHeap}
	# (predef_symbols, hash_table) = buildPredefinedSymbols (newHashTable symbol_heap)
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
parseCommandLine ["-id",compiler_id_string : args] options
	# compiler_id=toInt compiler_id_string
	| set_compiler_id compiler_id==compiler_id
		= parseCommandLine args options
parseCommandLine [arg1=:"-dynamics":args] options
	// generates for each .icl module a .tcl file (which contains the type information for that module)
	=	parseCommandLine args {options & compile_for_dynamics = True}
parseCommandLine [arg1=:"-fusion":args] options
	// switch on fusion transformations
	= parseCommandLine args {options & compile_with_fusion = True}
parseCommandLine ["-generics":args] options
	// enable generics
	= parseCommandLine args (SwitchGenerics {options & compile_with_generics = True} options)
parseCommandLine ["-lattr":args] options
	= parseCommandLine args {options & listTypes.lto_showAttributes = False}
parseCommandLine ["-lt":args] options
	= parseCommandLine args {options & listTypes.lto_listTypesKind = ListTypesInferred}
parseCommandLine ["-lset":args] options
	= parseCommandLine args {options & listTypes.lto_listTypesKind = ListTypesStrictExports}
parseCommandLine ["-lat":args] options
	= parseCommandLine args {options & listTypes.lto_listTypesKind = ListTypesAll}
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
		= compile_modules modules (n_compiles+1) cocl_options args_without_modules cache files;
	// otherwise
		= (ok,cache,files);
compile_modules [] n_compiles cocl_options args_without_modules cache files
	= (True,cache,files);

compileModule :: CoclOptions [{#Char}] *DclCache *Files -> (!Bool,!*DclCache,!*Files)
compileModule options backendArgs {dcl_modules,functions_and_macros,predef_symbols,hash_table,heaps} files
	# (opened, error, files)
		=	fopen options.errorPath options.errorMode files
	| not opened
		=	abort ("couldn't open error file \"" +++ options.errorPath +++ "\"\n")
	# (opened, out, files)
		=	fopen options.outPath options.outMode files
	| not opened
		=	abort ("couldn't open out file \"" +++ options.outPath +++ "\"\n")
	# (tcl_file, files)
		= openTclFile options.compile_for_dynamics options.pathName files
 	# (io, files)
		=	stdio files
	# ({boxed_ident=moduleIdent}, hash_table) = putIdentInHashTable options.moduleName IC_Module hash_table
	# list_inferred_types
		=	if (options.listTypes.lto_listTypesKind == ListTypesInferred)
				(Yes options.listTypes.lto_showAttributes)
				No
	# (optionalSyntaxTree,cached_functions_and_macros,cached_dcl_mods,n_functions_and_macros_in_dcl_modules,main_dcl_module_n,predef_symbols, hash_table, files, error, io, out,tcl_file,heaps)
		=	frontEndInterface {feo_up_to_phase=FrontEndPhaseAll,feo_generics=options.compile_with_generics,feo_fusion=options.compile_with_fusion} moduleIdent options.searchPaths dcl_modules functions_and_macros list_inferred_types predef_symbols hash_table fmodificationtime files error io out tcl_file heaps 
	# unique_copy_of_predef_symbols={predef_symbol\\predef_symbol<-:predef_symbols}
	# (closed, files)
		= closeTclFile tcl_file files
	| not closed
		=   abort ("couldn't close tcl file \"" +++ options.pathName +++ "tcl\"\n")
	# (closed, files)
		=	fclose io files
	| not closed
		=	abort ("couldn't close stdio")
	# (closed, files)
		=	fclose out files
	| not closed
		=	abort ("couldn't close out file \"" +++ options.outPath +++ "\"\n")
	# var_heap=heaps.hp_var_heap
	  hp_type_heaps=heaps.hp_type_heaps
	  attrHeap=hp_type_heaps.th_attrs
	# (success,functions_and_macros,n_functions_and_macros_in_dcl_modules,var_heap,attrHeap,error, files)
		= case optionalSyntaxTree of
			Yes syntaxTree
				# functions_and_macros = syntaxTree.fe_icl.icl_functions
				# (porting_ok, files)
					 = switch_port_to_new_syntax (createPortedFiles options.moduleName options.searchPaths files) (False, files)
				  error = switch_port_to_new_syntax 
				  			(case porting_ok of
				  				True
				  					-> error
				  				False
				  					-> error <<< "Error: couldn't write ported versions of module "
				  							 <<< options.moduleName <<< '\n')
				  			error
				# (success, var_heap, attrHeap, error, files)
					= backEndInterface outputPath (map appendRedirection backendArgs) options.listTypes options.outPath predef_symbols syntaxTree main_dcl_module_n var_heap attrHeap error files
				-> (success,functions_and_macros,n_functions_and_macros_in_dcl_modules,var_heap,attrHeap, error, files)
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
				-> (False,{},0,var_heap,attrHeap,error, files)
		with
			outputPath
	//				=	/* directoryName options.pathName +++ "Clean System Files" +++ {DirectorySeparator} +++ */ baseName options.pathName
				=	baseName options.pathName
	# heaps = {heaps & hp_var_heap=var_heap, hp_type_heaps = {hp_type_heaps  & th_attrs = attrHeap}}
	# (closed, files)
		=	fclose error files
	| not closed
		=	abort ("couldn't close error file \"" +++ options.errorPath +++ "\"\n")
	| success
		# dcl_modules={{dcl_module \\ dcl_module<-:cached_dcl_mods} & [main_dcl_module_n].dcl_macro_conversions=No}
		# cache={dcl_modules=dcl_modules,functions_and_macros=cached_functions_and_macros,predef_symbols=unique_copy_of_predef_symbols,hash_table=hash_table,heaps=heaps}
		= (success,cache,files)
		# cache={dcl_modules=cached_dcl_mods,functions_and_macros=cached_functions_and_macros,predef_symbols=unique_copy_of_predef_symbols,hash_table=hash_table,heaps=heaps}
		= (success,cache,files)