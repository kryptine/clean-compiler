/*
	module owner: Ronny Wichers Schreur
*/
module cocl


import StdEnv
import coclmain

import frontend

Start :: *World -> *World
Start world
	=	coclMain [] world
