definition module checkKindCorrectness

import syntax, checksupport, containers

checkKindCorrectness :: !Index IndexRange !u:{# FunDef} !{#CommonDefs} !*{#DclModule} !*TypeVarHeap !*TypeDefInfos !*ErrorAdmin
					-> (!u:{# FunDef}, !*{#DclModule}, !*TypeVarHeap, !*TypeDefInfos, !*ErrorAdmin)
