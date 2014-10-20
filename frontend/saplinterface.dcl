definition module saplinterface

import StdEnv, syntax, backend
from partition import ::Component

gensaplfiles :: Int {#DclModule} !{!Component} !{# FunDef} CommonDefs {#CommonDefs} Ident  [IndexRange] !*File !*BackEnd
                -> *(!*File, !*BackEnd)
