definition module Tonic.CompilerInterface

import syntax, checksupport
from overloading import :: InstanceTree
from Tonic.Util import copyFunDefs

ginTonic :: ScannedModule String SearchPaths ModuleN !*{#FunDef} !*{#FunDef} !{!Group} IclModule {#DclModule} !{#CommonDefs} [(String, ParsedExpr)] !*PredefinedSymbols !{#{!InstanceTree}} *HashTable !*File !*Files !*Heaps -> *(!*{#FunDef}, !*PredefinedSymbols, !{!Group}, *HashTable, !*File, !*Files, !*Heaps)
