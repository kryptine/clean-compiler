definition module type

import StdArray
import syntax, check

typeProgram ::!{! Group} !Int !*{# FunDef} !IndexRange !(Optional Bool) !CommonDefs ![Declaration] !{# DclModule} !ModuleNumberSet !*Heaps !*PredefinedSymbols !*File !*File
	-> (!Bool, !*{# FunDef}, !IndexRange, {! GlobalTCType}, !{# CommonDefs}, !{# {# FunType} }, !*Heaps, !*PredefinedSymbols, !*File, !*File)
