definition module Tonic.CompilerInterface

import syntax, checksupport

:: *FrontendTuple :== (!Bool, !*{# FunDef}, !ArrayAndListInstances, !{# CommonDefs}, !{# {# FunType} }, !*TypeDefInfos,!*Heaps,!*PredefinedSymbols,!*File,!*File)

ginTonic :: IclModule {#DclModule} *FrontendTuple !*Files -> *(*FrontendTuple, !*Files)

