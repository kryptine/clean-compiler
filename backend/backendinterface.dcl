/*
	module owner: Ronny Wichers Schreur
*/
definition module backendinterface

import frontend

backEndInterface :: !{#Char} [{#Char}] !ListTypesOption !{#Char} !PredefinedSymbols !FrontEndSyntaxTree !Int !*VarHeap !*AttrVarHeap !*File !*File -> (!Bool, !*VarHeap, !*AttrVarHeap, !*File, !*File)
