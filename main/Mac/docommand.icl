implementation module docommand;

from StdString import String;

:: *DoCommandEnvironment :== Int;

DoCommandNullTerminated :: !String !DoCommandEnvironment -> (!Int,!DoCommandEnvironment);
DoCommandNullTerminated a0 a1 = code {
	ccall DoCommandNullTerminated "S:I:I"
}
// int DoCommandNullTerminated(CleanString);
