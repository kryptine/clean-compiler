module cocl

import coclmain

import StdEnv
import frontend

Start :: *World -> *World
Start world
	=	coclMain testArgs world
	where
		testArgs
			=	[
					// main module			
					"hello.icl"
					// list all types
				,	"-lat"
					// generate readable abc code
				,	"-d"
					// Supercompilation
				,	"-SC"
					// paths
				,	"-P", testDir +++ ";" +++ cleanDir +++ "IOInterface" +++ ";" +++ cleanDir +++ "StdEnv"
				]
		testDir
			=	"C:\\Vincent\\Sucl\\"
		cleanDir
			=	"C:\\Clean 1.3.3\\"
