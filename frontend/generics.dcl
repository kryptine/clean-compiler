definition module generics 

import checksupport
/*2.0
from transform import ::Group
0.2*/
//1.3
from transform import Group
//3.1

convertGenerics :: !{!Group} !Int !{#CommonDefs} !*{# FunDef} !*TypeDefInfos !*Heaps !*HashTable !*PredefinedSymbols !u:{# DclModule} /*!(Optional {#Index})*/ !*ErrorAdmin 
	-> (!{!Group}, !{#CommonDefs}, !*{# FunDef}, !IndexRange, !*TypeDefInfos, !*Heaps, !*HashTable, !*PredefinedSymbols, !u:{# DclModule}, /*!(Optional {#Index}),*/ !*ErrorAdmin)

getGenericMember :: !(Global Index) !TypeKind !{#CommonDefs} -> (Bool, Global Index)
	