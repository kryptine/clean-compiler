definition module Tonic.CompilerInterface

import syntax, checksupport
from overloading import :: InstanceTree
from Tonic.Util import copyFunDefs

ginTonic :: String ModuleN !*{#FunDef} !*{#FunDef} IclModule {#DclModule} !{#CommonDefs} [(String, ParsedExpr)] !*PredefinedSymbols !{#{!InstanceTree}} *HashTable !*File !*Files !*Heaps -> *(!*{#FunDef}, !*PredefinedSymbols, *HashTable, !*File, !*Files, !*Heaps)
