/*
	module owner: Ronny Wichers Schreur
*/
module cocl


import StdEnv
import coclmain

import frontend
import StdDebug

Start :: *World -> *World
Start world
	=	coclMain [] world
