definition module generics 

import checksupport
from transform import Group

convertGenerics :: !{!Group} !Int !{#CommonDefs} !*{# FunDef} !*TypeDefInfos !*Heaps !*HashTable !*PredefinedSymbols !u:{# DclModule} !*ErrorAdmin 
	-> (!{!Group}, !{#CommonDefs}, !*{# FunDef}, !IndexRange, !*TypeDefInfos, !*Heaps, !*HashTable, !*PredefinedSymbols, !u:{# DclModule}, !*ErrorAdmin)

getGenericMember :: !(Global Index) !TypeKind !{#CommonDefs} -> (Bool, Global Index)
	