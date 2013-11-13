/*
	module owner: Ronny Wichers Schreur
*/
definition module backendinterface

import frontend, backend

backEndInterface :: !{#Char} [{#Char}] !ListTypesOption !{#Char} !PredefinedSymbols !FrontEndSyntaxTree !Int !*VarHeap !*AttrVarHeap !*(Optional *File) !*File !*File -> (!Bool, !*VarHeap, !*AttrVarHeap, !*(Optional *File), !*File, !*File)

addStrictnessFromBackEnd :: Int {#Char} *BackEnd SymbolType -> (Bool, SymbolType, *BackEnd)