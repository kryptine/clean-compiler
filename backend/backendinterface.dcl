definition module backendinterface

import frontend

backEndInterface :: !{#Char} [{#Char}] !PredefinedSymbols !FrontEndSyntaxTree !Int !*VarHeap !*File !*Files -> (!Bool,!*VarHeap, !*File, !*Files)
