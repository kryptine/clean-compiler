/*
	module owner: Ronny Wichers Schreur
*/
definition module frontend

from scanner import ::SearchPaths
from general import ::Optional (Yes, No)
import checksupport, transform, overloading

:: FrontEndOptions 
	=	{	feo_up_to_phase			:: !FrontEndPhase
		,	feo_generics 			:: !Bool
		,	feo_fusion	 			:: !Bool
		,	feo_dump_core			:: !Bool
		,	feo_strip_unused		:: !Bool
		}

:: FrontEndSyntaxTree
	=	{	fe_icl					:: !IclModule
		,	fe_dcls					:: !{#DclModule}
		,	fe_components			:: !{!Group}
		,	fe_arrayInstances		:: !ArrayAndListInstances
		}

:: FrontEndPhase
	=	FrontEndPhaseCheck
	|	FrontEndPhaseTypeCheck
	|	FrontEndPhaseConvertDynamics
	|	FrontEndPhaseTransformGroups
	|	FrontEndPhaseConvertModules
	|	FrontEndPhaseAll

:: ListTypesKind = ListTypesNone | ListTypesInferred | ListTypesStrictExports | ListTypesAll
:: ListTypesOption =
	{	lto_showAttributes :: Bool
	,	lto_listTypesKind :: ListTypesKind
	}
instance == ListTypesKind

frontEndInterface :: !FrontEndOptions !Ident !SearchPaths !{#DclModule} !*{#*{#FunDef}} !(Optional Bool) !*PredefinedSymbols !*HashTable (ModTimeFunction *Files) !*Files !*File !*File !*File !(Optional *File) !*Heaps
	-> ( !Optional *FrontEndSyntaxTree,!*{#*{#FunDef}},!{#DclModule},!Int,!Int,!*PredefinedSymbols, !*HashTable, !*Files, !*File, !*File, !*File, !Optional *File, !*Heaps) 
