module cocl

import coclmain
import StdString
import StdEnv

Start :: *World -> *World
Start world
	=	coclMain testArgs world
	where
		testArgs
			=	[
					// main module			
//					"Dialog1"
					"t"
//					"typesupport.icl"
//					"EdProject.icl"
					// list all types
				,	"-lat"
					// generate readable abc code
				,	"-d"
					// redirect out
				,	"-RO", "messages.txt"	
					// redirect errors
				,	"-RE", "errors.txt"
					// paths
				,	"-P", clean20Dir +++ "StdEnv" +++ ";" +++ clean20Dir +++ "IOInterface"
					// test specific
					+++ ";" +++ testDir
//					+++ ";" +++ clean20Dir +++ "test\\Clean 2 Compiler Test"
//					+++ ";" +++ ideDir +++ ";" +++ ideDir +++ "Windows\\" +++ ";" +++ ideDir +++ "Util\\"
				]
		testDir
			=	"e:\\Users\\Ronny\\Develop\\Clean Programs\\"
		clean20Dir
			=	"e:\\Users\\Ronny\\Develop\\CleanSystem\\2.0\\"
		ideDir
			=	clean20Dir +++ "test\\Clean IDE\\"
