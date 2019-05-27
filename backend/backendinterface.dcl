definition module backendinterface

import frontend, backend

backEndInterface :: !{#Char} [{#Char}] !ListTypesOption !{#Char} !PredefinedSymbols !FrontEndSyntaxTree !Int !*Heaps !*File !*File -> (!Bool, !*Heaps, !*File, !*File)

addStrictnessFromBackEnd :: Int {#Char} *BackEnd SymbolType -> (Bool, SymbolType, *BackEnd)