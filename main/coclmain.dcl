definition module coclmain

/*
	The coclmain library

	includes
		compile
		backend (needs dynamic library backend.dll)
		ArgEnv
		Version
		set_return_code

	uses
		StdEnv
		compiler

	This library is compiled with profiling code. This means that profiling
	should also be enabled in projects that use the coclmain library.

	Note:	The interface from coclmain to the compiler is not version checked.
			It's safest to build and use a new coclmain library whenever the
			type of the compiler's syntax tree changes.
*/

// coclMain :: ![{#Char}] !*World -> *World
// testArgs world
coclMain :== coclMainWithVersionCheck CoclMainVersionCurrent CoclMainVersionLatestDef CoclMainVersionLatestImp

CoclMainVersionCurrent
	:==	0x02000205
CoclMainVersionLatestDef
	:==	0x02000205
CoclMainVersionLatestImp
	:==	0x02000205

coclMainWithVersionCheck :: !Int !Int !Int ![{#Char}] !*World -> *World
// currentVersion latestDefVersion latestImpVersion testArgs world
