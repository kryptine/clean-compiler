definition module comparedefimp

import syntax, checksupport

// compare definition and implementation module

compareDefImp :: !*{# DclModule} !*IclModule !*Heaps !*ErrorAdmin 
				-> (!.{# DclModule}, !.IclModule,!.Heaps,!.ErrorAdmin);

