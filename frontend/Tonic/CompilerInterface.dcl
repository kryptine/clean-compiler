definition module Tonic.CompilerInterface

import syntax, checksupport
from Tonic.Util import copyFunDefs

ginTonic :: ModuleN !*{#FunDef} !*{#FunDef} IclModule {#DclModule} !{#CommonDefs} !*PredefinedSymbols *HashTable !*Files !*Heaps -> *(!*{#FunDef}, !*PredefinedSymbols, *HashTable, !*Files, !*Heaps)
