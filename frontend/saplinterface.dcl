definition module saplinterface

import StdEnv, syntax,transform 

gensaplfiles :: !Files {#DclModule} {#{#CheckedTypeDef}} !*{! Group} !*{# FunDef} CommonDefs {#CommonDefs} Ident  [IndexRange] !String
                -> (!Files,!*{! Group}, !*{# FunDef})
