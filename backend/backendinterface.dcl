/*
	module owner: Ronny Wichers Schreur
*/
definition module backendinterface

import frontend

backEndInterface :: !{#Char} [{#Char}] !ListTypesOption !{#Char} !PredefinedSymbols !FrontEndSyntaxTree !Int !*VarHeap !*AttrVarHeap !*File !*Files -> (!Bool, !*VarHeap, !*AttrVarHeap, !*File, !*Files)
