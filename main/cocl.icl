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
				,	"-P", testDir +++ ";" +++ clean20Dir +++ "StdEnv" +++ ";" +++ clean20Dir +++ "IOInterface"
				]
		testDir
			=	"c:\\Vincent\\Sucl\\"
		clean20Dir
			=	"e:\\Users\\Ronny\\Develop\\Clean 2.0\\"
