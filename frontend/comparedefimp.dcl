definition module comparedefimp

import syntax, checksupport

// compare definition and implementation module

compareDefImp :: !{#Int} !{!FunctionBody} !Int !*{# DclModule} !*IclModule !*Heaps !*ErrorAdmin 
				-> (!.{# DclModule}, !.IclModule,!.Heaps,!.ErrorAdmin)

