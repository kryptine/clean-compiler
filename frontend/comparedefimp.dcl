definition module comparedefimp

import syntax, checksupport

// compare definition and implementation module

compareDefImp :: !{#Int} !{!FunctionBody} !Int {#CheckedTypeDef} !*{# DclModule} !*IclModule !*Heaps !*ErrorAdmin 
				-> (!.{# DclModule}, !.IclModule,!.Heaps,!.ErrorAdmin)

