definition module checkKindCorrectness

import syntax, checksupport

checkKindCorrectness :: !Index IndexRange !{#CommonDefs} !Int !u:{# FunDef} !*{#DclModule} !*TypeVarHeap !*TypeDefInfos !*ErrorAdmin
																						-> (!u:{# FunDef}, !*{#DclModule}, !*TypeVarHeap, !*TypeDefInfos, !*ErrorAdmin)
