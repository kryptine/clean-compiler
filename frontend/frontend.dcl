/*
	module owner: Ronny Wichers Schreur
*/
definition module frontend

from scanner import SearchPaths
from general import Optional, Yes, No
import checksupport, transform, overloading

:: FrontEndOptions 
	=	{	feo_up_to_phase			:: !FrontEndPhase
		,	feo_generics 			:: !Bool
		,	feo_fusion	 			:: !Bool
		}

:: FrontEndSyntaxTree
	=	{	fe_icl					:: !IclModule
		,	fe_dcls					:: !{#DclModule}
		,	fe_components			:: !{!Group}
		,	fe_dclIclConversions	:: !Optional {# Index}
		,	fe_iclDclConversions	:: !Optional {# Index}
		,	fe_globalFunctions		:: !IndexRange
		,	fe_arrayInstances		:: !ArrayAndListInstances
		}

:: FrontEndPhase
	=	FrontEndPhaseCheck
	|	FrontEndPhaseTypeCheck
	|	FrontEndPhaseConvertDynamics
	|	FrontEndPhaseTransformGroups
	|	FrontEndPhaseConvertModules
	|	FrontEndPhaseAll

frontEndInterface :: !FrontEndOptions !Ident !SearchPaths !{#DclModule} !{#FunDef} !(Optional Bool) !*PredefinedSymbols !*HashTable !*Files !*File !*File !*File (!Optional !*File) !*Heaps
  	-> ( !Optional *FrontEndSyntaxTree,!*{# FunDef },!{#DclModule},!Int,!Int,!*PredefinedSymbols, !*HashTable, !*Files, !*File, !*File, !*File, !Optional !*File, !*Heaps) 
