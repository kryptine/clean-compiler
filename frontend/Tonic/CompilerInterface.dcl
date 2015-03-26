definition module Tonic.CompilerInterface

import syntax, checksupport
from Tonic.Util import copyFunDefs

ginTonic :: String ModuleN !*{#FunDef} !*{#FunDef} IclModule {#DclModule} !{#CommonDefs} [(String, ParsedExpr)] !*PredefinedSymbols *HashTable !*File !*Files !*Heaps -> *(!*{#FunDef}, !*PredefinedSymbols, *HashTable, !*File, !*Files, !*Heaps)
