definition module analtypes

import checksupport, typesupport

partionateAndExpandTypes :: !NumberSet !Index !*CommonDefs !*{#DclModule} !*TypeHeaps !*ErrorAdmin
	-> (!TypeGroups, !*{# CommonDefs}, !*TypeDefInfos, !*CommonDefs, !*{#DclModule}, !*TypeHeaps, !*ErrorAdmin)

::	TypeGroups :== [[GlobalIndex]]

analyseTypeDefs :: !{#CommonDefs} !TypeGroups !*TypeDefInfos !*TypeVarHeap !*ErrorAdmin -> (!*TypeDefInfos, !*TypeVarHeap, !*ErrorAdmin)

determineKindsOfClasses :: !NumberSet !{#CommonDefs} !*TypeDefInfos !*TypeVarHeap !*ErrorAdmin
	-> (!*ClassDefInfos, !*TypeDefInfos, !*TypeVarHeap, !*ErrorAdmin)

checkKindsOfCommonDefsAndFunctions :: !Index !Index !NumberSet !IndexRange !{#CommonDefs} !u:{# FunDef} !v:{#DclModule} !*TypeDefInfos !*ClassDefInfos
	!*TypeVarHeap !*ErrorAdmin -> (!u:{# FunDef}, !v:{#DclModule}, !*TypeDefInfos, !*TypeVarHeap, !*ErrorAdmin)

isATopConsVar cv		:== cv < 0
encodeTopConsVar cv		:== dec (~cv)
decodeTopConsVar cv		:== ~(inc cv)
