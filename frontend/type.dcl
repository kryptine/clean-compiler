definition module type

import StdArray
import syntax, check

typeProgram ::!{! Group} !*{# FunDef} !IndexRange !CommonDefs ![Declaration] !{# DclModule} !*Heaps !*PredefinedSymbols !*File
	-> (!Bool, !*{# FunDef}, !IndexRange, {! GlobalTCType}, !{# CommonDefs}, !{# {# FunType} }, !*Heaps, !*PredefinedSymbols, !*File)

