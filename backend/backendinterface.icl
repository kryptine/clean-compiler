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
			=	fwrites "[Backend] the backend library is too new\n" errorFile
	=	(False, errorFile)
checkVersion VersionObservedIsTooOld errorFile
	#	errorFile
			=	fwrites "[Backend] the backend library is too old\n" errorFile
	=	(False, errorFile)

backEndInterface :: !{#Char} [{#Char}] !PredefinedSymbols !*FrontEndSyntaxTree !*File !*Files -> (!Bool, !*File, !*Files)
backEndInterface outputFileName commandLineArgs predefs syntaxTree errorFile files
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
		=	(False, errorFile, files)
	# varHeap
		=	backendPreprocess functionIndices syntaxTree.fe_icl syntaxTree.fe_varHeap
		with
			functionIndices
				=	flatten [[member \\ member <- group.group_members] \\ group <-: syntaxTree.fe_components]
	  syntaxTree
		=	{syntaxTree & fe_varHeap = varHeap}
	# backEndFiles
		=	0
	# (backEnd, backEndFiles)
		=	BEInit (length commandLineArgs) backEndFiles
	# backEnd
		=	foldState BEArg commandLineArgs backEnd
	# backEnd
		=	backEndConvertModules predefs syntaxTree varHeap backEnd
	# (success, backEnd)
		=	BEGenerateCode outputFileName backEnd
	# backEndFiles
		=	BEFree backEnd backEndFiles
	=	(backEndFiles == 0 && success, errorFile, files)
