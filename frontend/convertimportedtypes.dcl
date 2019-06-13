definition module convertimportedtypes

import syntax

convertIclModule :: !Int !{# CommonDefs} !*{#{# CheckedTypeDef}} !ImportedConstructors !*VarHeap !*TypeHeaps
									 -> (!*{#{# CheckedTypeDef}},!ImportedConstructors,!*VarHeap,!*TypeHeaps)

convertDclModule :: !Int !{# DclModule} !{# CommonDefs} !*{#{# CheckedTypeDef}} !ImportedConstructors !*VarHeap !*TypeHeaps
													-> (!*{#{# CheckedTypeDef}},!ImportedConstructors,!*VarHeap,!*TypeHeaps)

convertMemberTypesAndImportedTypeSpecifications
	:: !Int !NumberSet !{#DclModule} !{#{#FunType}} !{#CommonDefs} !ImportedConstructors !ImportedFunctions !*{#{#CheckedTypeDef}}
		!*TypeHeaps !*VarHeap -> (!*TypeHeaps, !*VarHeap)
