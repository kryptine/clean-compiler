definition module analtypes

import checksupport, typesupport

analTypeDefs :: !{#CommonDefs} !ModuleNumberSet !*TypeHeaps !*ErrorAdmin -> (!*TypeDefInfos, !*TypeHeaps, !*ErrorAdmin)

instance <<< TypeKind
