// this is for Windows
definition module CoclSystemDependent

//1.3
from StdString import String
//3.1
from StdFile import Files

// RWS split
// from deltaIOSystem import DeviceSystem
// from deltaEventIO import InitialIO, IOState

PathSeparator
	:==	';'
DirectorySeparator
	:== '\\'

SystemDependentDevices :: [a]
SystemDependentInitialIO :: [a]

ensureCleanSystemFilesExists :: !String !*Files -> (!Bool, !*Files)

set_compiler_id :: Int -> Int
