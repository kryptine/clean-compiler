definition module type

import StdArray
import syntax, check

/* MW4 was:
typeProgram ::!{! Group} !*{# FunDef} !IndexRange !CommonDefs ![Declaration] !{# DclModule} !*Heaps !*PredefinedSymbols !*File
	-> (!Bool, !*{# FunDef}, !IndexRange, {! GlobalTCType}, !{# CommonDefs}, !{# {# FunType} }, !*Heaps, !*PredefinedSymbols, !*File)
*/
typeProgram ::!{! Group} !*{# FunDef} !IndexRange !(Optional Bool) !CommonDefs ![Declaration] !{# DclModule} !*Heaps !*PredefinedSymbols !*File !*File
	-> (!Bool, !*{# FunDef}, !IndexRange, {! GlobalTCType}, !{# CommonDefs}, !{# {# FunType} }, !*Heaps, !*PredefinedSymbols, !*File, !*File)
