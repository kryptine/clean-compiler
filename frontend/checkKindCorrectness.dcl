definition module checkKindCorrectness

import syntax, checksupport, containers

checkKindCorrectness :: !NumberSet !Index IndexRange !{#CommonDefs} !{#DclModule} !u:{# FunDef} !*TypeVarHeap !*TypeDefInfos !*ErrorAdmin
					-> (!u:{# FunDef}, !*TypeVarHeap, !*TypeDefInfos, !*ErrorAdmin)
