/*
	module owner: Ronny Wichers Schreur
*/
module cocl


import StdEnv
import coclmain

import frontend

// Start :: *World -> *World
Start world
	=	(testArgs, coclMain testArgs world)
	where
		testArgs
			=	[
					// main module
					testDir +++ "t"
//				,	// unknown option
//					"-xxx"
//					// list all types
				,	"-lat"
					// generate readable abc code
				,	"-d"
					// time profiling
				,	"-pt"
					// reuse unique nodes
				,	"-ou"
					// redirect out
//				,	"-RO", "messages.txt"	
					// redirect errors
//				,	"-RE", "errors.txt"
					// paths
				,	"-P", testDir +++ ";" +++ io08Dir +++ ";" +++ stdenvDir
//				,	"-P", paths
				]

		baseDir
			=	"d:\\Users\\Ronny\\Develop\\"
		testDir
			=	baseDir +++ "Clean Programs\\" +++ "testes\\" 

		coclDir
			=	baseDir +++ "CleanSystem\\cocl\\"

		cleanSystemDir
			=	baseDir +++ "CleanSystem\\"

		cleanVersion
			=	"2.0 repository\\"

		stdenvDir
			=	cleanSystemDir +++ cleanVersion +++ "\\StdEnv\\"

		io08Dir
//			=	cleanSystemDir +++ cleanVersion +++ "\\IOInterface\\"
			=	"d:\\Users\\Ronny\\Profile\\Desktop\\test\\IOInterface 0.8.2\\"
		paths
			=	foldl  (\a b -> a +++ ";" +++ b) ""
				(
					[	coclDir +++ path
					\\	path <-
						[	""
						,	"compiler"
						,	"main"
						,	"main/Windows"
						,	"backend"
						,	"backendCModules"
						,	"ArgEnvWindows"
						,	"WrapDebug"
						]
					]
				++
					[	stdenvDir
					]
				)
