module CleanCocl

import StdEnv
import deltaEventIO, deltaIOState
import CoclSystemDependent

Don`tCareId
	:==	0

Start :: !*World -> *World
Start world
	# (_, world)
		=	StartIO [menus : SystemDependentDevices] 0 SystemDependentInitialIO world
		with
			menus
				=	MenuSystem [file]
			file
				=	PullDownMenu Don`tCareId "File" Able
						[MenuItem Don`tCareId "Quit" (Key 'Q') Able Quit]
	=	world

Quit :: *s (IOState *s) -> (*s, IOState *s)
Quit s io
	=	(s, QuitIO io)
