definition module analtypes

import checksupport, typesupport

partionateAndExpandTypes :: !NumberSet !Index !*CommonDefs !*{#DclModule} !*TypeHeaps !*ErrorAdmin
	-> (!TypeGroups, !*{# CommonDefs}, !*TypeDefInfos, !*CommonDefs, !*{#DclModule}, !*TypeHeaps, !*ErrorAdmin)

::	TypeGroups :== [[GlobalIndex]]

analyseTypeDefs :: !{#CommonDefs} !TypeGroups !*TypeDefInfos !*TypeHeaps !*ErrorAdmin -> (!*TypeDefInfos, !*TypeHeaps, !*ErrorAdmin)
