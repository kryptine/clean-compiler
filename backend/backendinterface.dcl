definition module backendinterface

import frontend

backEndInterface :: !{#Char} [{#Char}] !PredefinedSymbols !*FrontEndSyntaxTree !*File !*Files -> (!Bool, !*File, !*Files)
