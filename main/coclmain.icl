implementation module coclmain

CoclMainVersion :== 0

import StdEnv
import ArgEnv
import Version
import set_return_code

import compile

// coclMain :: ![{#Char}] !*World -> *World
// testArgs world
coclMain :== coclMainWithVersionCheck CoclMainVersionCurrent CoclMainVersionLatestDef CoclMainVersionLatestImp

CoclMainVersionCurrent
	:==	0x02000205
CoclMainVersionLatestDef
	:==	0x02000205
CoclMainVersionLatestImp
	:==	0x02000205

checkVersion :: VersionsCompatability *File -> (!Bool, !*File)
checkVersion VersionsAreCompatible errorFile
	=	(True, errorFile)
checkVersion VersionObservedIsTooNew errorFile
	#	errorFile
			=	fwrites "[Coclmain] the library is too new\n" errorFile
	=	(False, errorFile)
checkVersion VersionObservedIsTooOld errorFile
	#	errorFile
			=	fwrites "[Coclmain] the library is too old\n" errorFile
	=	(False, errorFile)

coclMainWithVersionCheck :: !Int !Int !Int ![{#Char}] !*World -> *World
// currentVersion latestDefVersion latestImpVersion testArgs world
coclMainWithVersionCheck  currentVersion latestDefVersion latestImpVersion testArgs world
	# observedVersion =
		{	versionCurrent
				=	CoclMainVersionCurrent
		,	versionOldestDefinition
				=	CoclMainVersionLatestDef
		,	versionOldestImplementation
				=	CoclMainVersionLatestImp
		}
	  expectedVersion =
		{	versionCurrent
				=	currentVersion
		,	versionOldestDefinition
				=	latestDefVersion
		,	versionOldestImplementation
				=	latestImpVersion
		}
	| not (fst (checkVersion (versionCompare expectedVersion observedVersion) stderr))
		=	set_return_code (-1) world
	# (success, world)
		=	accFiles (\files0 -> let (r,cache,files)=compile commandArgs empty_cache files0 in (r,files)) world
	=	set_return_code (if success 0(-1)) world
	where
		commandArgs
			=	if (length realArgs == 0) testArgs realArgs
		realArgs
			=	tl [arg \\ arg <-: getCommandLine]
