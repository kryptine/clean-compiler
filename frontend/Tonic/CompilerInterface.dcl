definition module Tonic.CompilerInterface

import syntax, checksupport

ginTonic :: !*{#FunDef} IclModule {#DclModule} !{#CommonDefs} !*PredefinedSymbols !*Files -> *(!*{#FunDef}, !*PredefinedSymbols, !*Files)
