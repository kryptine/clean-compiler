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
            =   [ "-SC"             // Supercompilation
                , "-c"
                , "-pt"
                , "-desc"
                , "-d"              // Generate readable abc code
                , "-lat"            // List all types
                , "-ou"
                , iclFile           // Main module
                , "-P",  paths      // Paths
                , "-RE", errFile    // Error output
                , "-RO", outFile    // Standard output
                ]

        modname = "hello"

        iclFile = testDir+++modname+++".icl"
        outFile = testDir+++modname+++".out"
        errFile = testDir+++modname+++".err"

        paths = testDir+++";;"+++cleanDir+++"StdEnv"

		testDir     =	"C:\\Vincent\\Sucl\\"
		cleanDir    =	"C:\\Clean\\2.0 (beta 3)\\"
