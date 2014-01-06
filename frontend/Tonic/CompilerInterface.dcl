definition module Tonic.CompilerInterface

import syntax, checksupport

ginTonic :: ModuleN !*{#FunDef} IclModule {#DclModule} !{#CommonDefs} !*PredefinedSymbols !*Files !*Heaps -> *(!*{#FunDef}, !*PredefinedSymbols, !*Files, !*Heaps)
