definition module backendinterface

import frontend

backEndInterface :: !{#Char} [{#Char}] !PredefinedSymbols !FrontEndSyntaxTree !Int !*VarHeap !*AttrVarHeap !*File !*Files -> (!Bool, !*VarHeap, !*AttrVarHeap, !*File, !*Files)
