definition module Debug

:: DebugShowFunction a :== !a -> [{#Char}]

debugBefore :: !.a !(DebugShowFunction .a) .b -> .b
debugAfter :: !.a !(DebugShowFunction .a) !.b -> .b
debugValue :: !(DebugShowFunction .a) !.a -> .a

debugShow :: DebugShowFunction .a
debugShowWithOptions :: [DebugShowOption] -> DebugShowFunction .a

:: DebugShowOption 
	=	DebugMaxDepth !Int			// default MaxInt
	|	DebugMaxBreadth !Int		// default MaxInt
	|	DebugMaxChars !Int			// default MaxInt
	|	DebugTerminator !{#Char}	// default "\n"

