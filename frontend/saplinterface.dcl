definition module saplinterface

import StdEnv, syntax, backend
from partition import ::Component

gensaplfiles :: {#DclModule} !{!Component} !{# FunDef} CommonDefs {#CommonDefs} Ident  [IndexRange] !*File !*BackEnd
                -> *(!*File, !*BackEnd)
