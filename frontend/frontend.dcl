definition module frontend

from scanner import SearchPaths, String
from general import Optional, Yes, No
import checksupport, transform, overloading

:: FrontEndSyntaxTree
	=	{	fe_icl :: !IclModule
		,	fe_dcls :: !{#DclModule}
		,	fe_components :: {!Group}
		,	fe_varHeap :: !.VarHeap
		,	fe_dclIclConversions ::!Optional {# Index}
		,	fe_iclDclConversions ::!Optional {# Index}
		,	fe_arrayInstances :: !{!(Index, SymbolType)}
		}

frontEndInterface :: !Ident !SearchPaths !*PredefinedSymbols !*HashTable !*Files !*File !*File !*File -> (!*PredefinedSymbols, !*HashTable, !*Files, !*File, !*File, !*File, !Optional *FrontEndSyntaxTree) 
// name paths predefs files error io out