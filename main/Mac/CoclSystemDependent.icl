// this is for the PowerMac
implementation module CoclSystemDependent

import StdEnv
import deltaIOSystem, deltaEventIO, deltaIOState
import AppleEventDevice
import compile
import docommand
import RWSDebug

PathSeparator
	:==	','
DirectorySeparator
	:==	':'

SystemDependentDevices :: [DeviceSystem .a (IOState .a)]
SystemDependentDevices
		=	[AppleEventSystem {openHandler = openDummy, quitHandler = Quit,
								clipboardChangedHandler = clipboardDummy, scriptHandler = scriptHandler}];
		where
			openDummy filePath s io
				=	(s, io) <<- ("open", filePath)
			clipboardDummy s io
				=	(s, io) <<- "clipboard"

		/*
			scriptHandler script s io
				# (result, env) = DoCommandNullTerminated (script +++ "\0") 17
				| result >= 0
					=	(s, io)
				// otherwise
					=	(s, io) <<- ("error in docommand", result, script)
		*/
			scriptHandler script s io
				=	(s, appFiles (compile (processArgs script)) io) <<- ("script", processArgs script)
				where
					processArgs s
						=	[replace arg \\ arg <- filter ((<>) "") (splitArgs s)]

					replace s
						| s == "\xb3" /* \xb3 == >= ligature */
							=	"-RE"
						| s == ">"
							=	"-RO"
						// otherwise
							=	s
					splitArgs s
						=	split False 0 0 (size s) s
					split quoted frm to n s
						| to >= n
							=	[s % (frm, to)]
						| s.[to] == '\\' && to < n-1
							=	split quoted frm (to+2) n s
						| s.[to] == ' ' && not quoted 
							=	[s % (frm, to-1) : split False (to+1) (to+1) n s]
						| s.[to] == '\'' && quoted
							=	[s % (frm, to-1) : split False (to+1) (to+1) n s]
						| s.[to] == '\''
							=	[s % (frm, to-1) : split True (to+1) (to+1) n s]
						// otherwise
							=	split quoted frm (to+1) n s

SystemDependentInitialIO :: InitialIO *s
SystemDependentInitialIO
		=	[]

Quit :: *s (IOState *s) -> (*s, IOState *s)
Quit s io
	=	(s, QuitIO io)
