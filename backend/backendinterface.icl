implementation module backendinterface

import StdEnv

import frontend
import backend
import backendpreprocess, backendsupport, backendconvert
import RWSDebug, Version

checkVersion :: VersionsCompatability *File -> (!Bool, !*File)
checkVersion VersionsAreCompatible errorFile
	=	(True, errorFile)
checkVersion VersionObservedIsTooNew errorFile
	#	errorFile
			=	fwrites "[Backend] the back end library is too new\n" errorFile
	=	(False, errorFile)
checkVersion VersionObservedIsTooOld errorFile
	#	errorFile
			=	fwrites "[Backend] the back end library is too old\n" errorFile
	=	(False, errorFile)

backEndInterface :: !{#Char} [{#Char}] !PredefinedSymbols !FrontEndSyntaxTree !Int !*VarHeap !*File !*Files -> (!Bool,!*VarHeap, !*File, !*Files)
backEndInterface outputFileName commandLineArgs predef_symbols syntaxTree=:{fe_icl,fe_components} main_dcl_module_n var_heap errorFile files
	# (observedCurrent, observedOldestDefinition, observedOldestImplementation)
		=	BEGetVersion
	  observedVersion =
		{	versionCurrent
				=	observedCurrent
		,	versionOldestDefinition
				=	observedOldestDefinition
		,	versionOldestImplementation
				=	observedOldestImplementation
		}
	  expectedVersion =
		{	versionCurrent
				=	kBEVersionCurrent
		,	versionOldestDefinition
				=	kBEVersionOldestDefinition
		,	versionOldestImplementation
				=	kBEVersionOldestImplementation
		}
	# (compatible, errorFile)
		=	checkVersion (versionCompare expectedVersion observedVersion) errorFile
	| not compatible
		=	(False, var_heap,errorFile, files)
	# varHeap
		=	backEndPreprocess predef_symbols.[PD_DummyForStrictAliasFun].pds_ident functionIndices fe_icl var_heap
		with
			functionIndices
				=	flatten [[member \\ member <- group.group_members] \\ group <-: fe_components]
	# backEndFiles
		=	0
	# (backEnd, backEndFiles)
		=	BEInit (length commandLineArgs) backEndFiles
	# backEnd
		=	foldState BEArg commandLineArgs backEnd
	# (var_heap,backEnd)
		=	backEndConvertModules predef_symbols syntaxTree main_dcl_module_n varHeap backEnd
	# (success, backEnd)
		=	BEGenerateCode outputFileName backEnd
	# backEndFiles
		=	BEFree backEnd backEndFiles
	=	(backEndFiles == 0 && success, var_heap,errorFile, files)
