definition module frontend

from scanner import SearchPaths
from general import Optional, Yes, No
import checksupport, transform, overloading

:: FrontEndSyntaxTree
	=	{	fe_icl :: !IclModule
		,	fe_dcls :: !{#DclModule}
		,	fe_components :: !{!Group}
		,	fe_dclIclConversions ::!Optional {# Index}
		,	fe_iclDclConversions ::!Optional {# Index}
		,	fe_globalFunctions :: !IndexRange
		,	fe_arrayInstances :: !IndexRange
		}

:: FrontEndPhase
	=	FrontEndPhaseCheck
	|	FrontEndPhaseTypeCheck
	|	FrontEndPhaseConvertDynamics
	|	FrontEndPhaseTransformGroups
	|	FrontEndPhaseConvertModules
	|	FrontEndPhaseAll

frontEndInterface :: !FrontEndPhase !Ident !SearchPaths !{#DclModule} !{#FunDef} !(Optional Bool) !*PredefinedSymbols !*HashTable !*Files !*File !*File !*File (!Optional !*File) !*Heaps
	-> ( !Optional *FrontEndSyntaxTree,!.{# FunDef },!Int,!Int,!*PredefinedSymbols, !*HashTable, !*Files, !*File, !*File, !*File, !Optional !*File, !*Heaps) 
