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
	,	pathName
			:: {#Char}
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
			=	"messages"
	,	outMode
			=	FWriteText
	,	searchPaths
// RWS, voor Maarten +++			=	{sp_locations = [], sp_paths = []}
				=	[]
	}

compile :: [{#Char}] *Files -> (!Bool, !*Files)
compile args files
	=	compileModule (parseCommandLine args InitialCoclOptions) args files

parseCommandLine :: [{#Char}] CoclOptions -> CoclOptions
parseCommandLine [] options
	=	prependModulePath options
	where
		// RWS +++ hack, both module name and file path should be passed to frontEndInterface
		prependModulePath options=:{pathName, searchPaths}
			=	{	options
				&	moduleName = baseName pathName
// RWS, voor Maarten +++				,	searchPaths = {searchPaths & sp_paths = [directoryName pathName : searchPaths.sp_paths]}
				,	searchPaths = [directoryName pathName : searchPaths]
				}
parseCommandLine ["-P", searchPathsString : args] options=:{searchPaths}
// RWS, voor Maarten +++	=	parseCommandLine args {options & searchPaths = {searchPaths & sp_paths = splitPaths searchPathsString}}
	=	parseCommandLine args {options & searchPaths = splitPaths searchPathsString}
parseCommandLine ["-RO", outPath : args] options
	=	parseCommandLine args {options & outPath = stripQuotes outPath, outMode = FWriteText}
parseCommandLine ["-RAO", outPath : args] options
	=	parseCommandLine args {options & outPath = stripQuotes outPath, outMode = FAppendText}
parseCommandLine ["-RE", errorPath : args] options
	=	parseCommandLine args {options & errorPath = stripQuotes errorPath, errorMode = FWriteText}
parseCommandLine ["-RAE", errorPath : args] options
	=	parseCommandLine args {options & errorPath = stripQuotes errorPath, errorMode = FAppendText}
parseCommandLine [arg : args] options
	| arg.[0] == '-'
		=	parseCommandLine args options
	// otherwise
		=	parseCommandLine args {options & pathName = stripExtension ".icl" (stripQuotes arg)}

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

compileModule :: CoclOptions [{#Char}] *Files -> (!Bool, !*Files)
compileModule options commandLineArgs files
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

	# (predefSymbols, hashTable) = buildPredefinedSymbols newHashTable
	  (moduleIdent, hashTable) = putIdentInHashTable options.moduleName IC_Module hashTable
	# (predefs, _, files, error, io, out, optionalSyntaxTree)
		=	frontEndInterface moduleIdent options.searchPaths predefSymbols hashTable files error io out
	# (closed, files)
		=	fclose io files
	| not closed
		=	abort ("couldn't close stdio")
	# (closed, files)
		=	fclose out files
	| not closed
		=	abort ("couldn't close out file \"" +++ options.outPath +++ "\"\n")
	# (success, error, files)
		=	case optionalSyntaxTree of
				Yes syntaxTree
					->	backEndInterface outputPath (map appendRedirection commandLineArgs) predefs syntaxTree error files
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
					-> (False, error, files)
		with
			outputPath
	//				=	/* directoryName options.pathName +++ "Clean System Files" +++ {DirectorySeparator} +++ */ baseName options.pathName
				=	baseName options.pathName
	# (closed, files)
		=	fclose error files
	| not closed
		=	abort ("couldn't close error file \"" +++ options.errorPath +++ "\"\n")
	=	(success, files)