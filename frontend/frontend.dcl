definition module frontend

from scanner import SearchPaths
from general import Optional, Yes, No
import checksupport, transform, overloading

:: FrontEndSyntaxTree
	=	{	fe_icl :: !IclModule
		,	fe_dcls :: !{#DclModule}
		,	fe_components :: !{!Group}
		,	fe_varHeap :: !.VarHeap
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

frontEndInterface :: !FrontEndPhase !Ident !SearchPaths !Bool !*PredefinedSymbols !*HashTable !*Files !*File !*File !*File -> (!*PredefinedSymbols, !*HashTable, !*Files, !*File, !*File, !*File, !Optional *FrontEndSyntaxTree) 
// upToPhase name paths list_inferred_types predefs files error io out