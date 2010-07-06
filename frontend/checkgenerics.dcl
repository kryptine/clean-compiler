definition module checkgenerics

import syntax
from checksupport import ::Heaps,::CheckState

checkGenericDefs :: !Index !(Optional (CopiedDefinitions, Int))
		!*{#GenericDef} !*{#CheckedTypeDef} !*{#ClassDef} !*{#DclModule} !*Heaps !*CheckState
	-> (!*{#GenericDef},!*{#CheckedTypeDef},!*{#ClassDef},!*{#DclModule},!*Heaps,!*CheckState)

checkGenericCaseDefs :: !Index !*{#GenericCaseDef} !*{#GenericDef} !u:{#CheckedTypeDef} !*{#DclModule} !*Heaps !*CheckState
						   -> (!*{#GenericCaseDef},!*{#GenericDef},!u:{#CheckedTypeDef},!*{#DclModule},!.Heaps,!.CheckState)

convert_generic_instances :: !.[GenericCaseDef] !Int -> (!.[FunDef], !.[GenericCaseDef])

create_gencase_funtypes :: !Index !*{#GenericCaseDef} !*Heaps
		  -> (!Index, ![FunType], !*{#GenericCaseDef},!*Heaps)
