definition module Tonic.CompilerInterface

import syntax, checksupport
from Tonic.Util import copyFunDefs

ginTonic :: ModuleN !*{#FunDef} !*{#FunDef} IclModule {#DclModule} !{#CommonDefs} !*PredefinedSymbols !*Files !*Heaps -> *(!*{#FunDef}, !*PredefinedSymbols, !*Files, !*Heaps)
