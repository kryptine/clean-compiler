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
					"t.icl"
					// list all types
				,	"-lat"
					// generate readable abc code
				,	"-d"
					// redirect out
				,	"-RO", "messages.txt"	
					// redirect errors
				,	"-RE", "errors.txt"
					// paths
				,	"-P", testDir +++ ";" +++ clean20Dir +++ "StdEnv" +++ ";" +++ clean20Dir +++ "IOInterface"
				]
		testDir
			=	"e:\\Users\\Ronny\\Develop\\Clean Programs\\"
		clean20Dir
			=	"e:\\Users\\Ronny\\Develop\\Clean 2.0\\"
