definition module frontend

from scanner import SearchPaths
from general import Optional, Yes, No
import checksupport, transform, overloading

:: FrontEndSyntaxTree
	=	{	fe_icl :: !IclModule                            //   The ICL being compiled
		,	fe_dcls :: !{#DclModule}                        // ? The DCLs that were imported
		,	fe_components :: !{!Group}                      // ? Component groups of functions
		,	fe_dclIclConversions ::!Optional {# Index}      // ?
		,	fe_iclDclConversions ::!Optional {# Index}      // ?
		,	fe_globalFunctions :: !IndexRange               // ?
		,	fe_arrayInstances :: !IndexRange                // ?
		}

:: FrontEndPhase
	=	FrontEndPhaseCheck
	|	FrontEndPhaseTypeCheck
	|	FrontEndPhaseConvertDynamics
	|	FrontEndPhaseTransformGroups
	|	FrontEndPhaseConvertModules
	|	FrontEndPhaseAll

frontEndInterface
 :: !FrontEndPhase                      //   Up to where we want `frontEndInterface' to do its work
    !Ident                              // ? Name of module being compiled
    !SearchPaths                        // ? Where to look for input files
    !{#DclModule}                       //   Modules in the DCL cache
    !{#FunDef}                          //   Functions and macros in the DCL cache
    !(Optional Bool)                    //   List generated types (with or without attributes)
    !*PredefinedSymbols                 //   Symbols that are predefined in the Clean langauge (which?), from the DCL cache (?)
    !*HashTable                         // ? ... from the DCL cache
    !*Files                             //   Original file system state
    !*File                              //   Original standard error stream state
    !*File                              //   Original standard io stream state
    !*File                              //   Original standard out stream state
    (!Optional !*File)                  // ? TCL file (?)
    !*Heaps                             // ? ... from the DCL cache

 -> ( !Optional *FrontEndSyntaxTree     //   Resulting syntax tree if successful
    , !.{# FunDef }                     // ? Cached functions and macros (which?)
    , !Int                              // ? Don't care (?)
    , !Int                              // ? main_dcl_module_n (?)
    , !*PredefinedSymbols               // ? Symbols that are predefined in the Clean language
    , !*HashTable                       // ?
    , !*Files                           //   Resulting file system state
    , !*File                            //   Resulting standard error stream state
    , !*File                            //   Resulting standard io stream state
    , !*File                            //   Resulting standard out stream state
    , !Optional !*File                  // ? TCL file (?)
    , !*Heaps                           // ?
    )
