definition module docommand;

from StdString import String;

:: *DoCommandEnvironment :== Int;
DoCommandNullTerminated :: !String !DoCommandEnvironment -> (!Int,!DoCommandEnvironment);
