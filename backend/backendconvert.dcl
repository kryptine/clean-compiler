/*
	module owner: Ronny Wichers Schreur
*/
definition module backendconvert

/*2.0
from backend import ::BackEnd
0.2*/
//1.3
from backend import BackEnd
//3.1
import frontend

backEndConvertModules :: PredefinedSymbols FrontEndSyntaxTree !Int *VarHeap *AttrVarHeap *BackEnd -> (!*VarHeap, *AttrVarHeap, !*BackEnd)
