implementation module RWSDebug

import Debug

show
	=	debugShowWithOptions [] // [DebugMaxChars 80, DebugMaxDepth 5]

(->>) :: !.a !.b -> .a
(->>) value debugValue
	=	debugAfter debugValue show value

(<<-) :: .a !.b -> .a
(<<-) value debugValue
	=	debugBefore debugValue show value

<<->> :: !.a -> .a
<<->> value
	=	debugValue show value
