definition module frontend

// $Id$

// vi:set tabstop=4 noet:

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

:: FrontEndOptions
	=	{	feo_upToPhase    :: !FrontEndPhase  // How much of the frontend to execute
		,	feo_search_paths :: !SearchPaths    // Folders in which to search for files
		,	feo_typelisting  :: !Optional !Bool // Whether to list derived types, and if so whether to list attributes
		,	feo_fusionstyle  :: !FusionStyle    // What type of fusion to perform
		}

:: FrontEndPhase
	=	FrontEndPhaseCheck
	|	FrontEndPhaseTypeCheck
	|	FrontEndPhaseConvertDynamics
	|	FrontEndPhaseTransformGroups
	|	FrontEndPhaseConvertModules
	|	FrontEndPhaseAll

:: FusionStyle
	=	FS_online  // Do online fusion (supercompilation)
	|	FS_offline // Do offline fusion (deforestation)
	|	FS_none    // Do no fusion

frontEndInterface :: !FrontEndOptions !Ident !{#DclModule} !{#FunDef} !*PredefinedSymbols !*HashTable !*Files !*File !*File !*File (!Optional !*File) !*Heaps
	-> ( !Optional *FrontEndSyntaxTree,!.{# FunDef },!Int,!Int,!*PredefinedSymbols, !*HashTable, !*Files, !*File, !*File, !*File, !Optional !*File, !*Heaps) 
