// this is for Windows
implementation module CoclSystemDependent

import StdEnv
//import code from "cDirectory.obj",  library "directory_library" // Windows

PathSeparator
	:==	';'
DirectorySeparator
	:== '\\'

SystemDependentDevices :: [a]
SystemDependentDevices
		=	[]

SystemDependentInitialIO :: [a]
SystemDependentInitialIO
		=	[]

ensureCleanSystemFilesExists :: !String !*Files -> (!Bool, !*Files)
// returned bool: now there is such a subfolder
ensureCleanSystemFilesExists path env
	= (False,env)

/*	# path_c_string = path +++ "\0"
	  (err_code, env) = createDirectoryC path_c_string env
	= (err_code==M_NoDirError || err_code==M_AlreadyExists, env)
*/

createDirectoryC :: !String !*env -> (!Int, !*env)
createDirectoryC _ _
	= code
		{
			ccall createDirectoryC "S:I:A"
		}

// createDirectoryC returns the following error codes:
M_NoDirError		:==  0
M_OtherDirError		:== -1
M_DoesntExist		:== -2
M_BadName			:== -3
M_NotEnoughSpace	:== -4
M_AlreadyExists		:== -5
M_NoPermission		:== -6

set_compiler_id :: Int -> Int
set_compiler_id compiler_id = compiler_id
