// this is for Unix
implementation module CoclSystemDependent

import StdEnv

// import for filesystem
import code from "cDirectory.o" // Unix
import code from "ipc.o"
from filesystem import ensureDirectoryExists

PathSeparator
	:==	':'
DirectorySeparator
	:== '/'

SystemDependentDevices :: [a]
SystemDependentDevices
		=	[]

SystemDependentInitialIO :: [a]
SystemDependentInitialIO
		=	[]

ensureCleanSystemFilesExists :: !String !*Files -> (!Bool, !*Files)
// returned bool: now there is such a subfolder
ensureCleanSystemFilesExists path env
	= ensureDirectoryExists path env

set_compiler_id :: Int -> Int
set_compiler_id compiler_id = compiler_id
