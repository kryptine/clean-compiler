definition module convert

// $Id$

from newtest import Symredresult
from newfold import FuncDef
from rule import Rule
from coreclean import SuclTypeSymbol,SuclTypeVariable,SuclSymbol,SuclSymbolKind,SuclVariable
from checksupport import DclModule
from syntax import FunDef,FunType,ExpressionHeap
from predef import PredefinedSymbols,PredefinedSymbol
/*2.0
from StdArray import Array
0.2*/

// Transitively required stuff
from newfold import FuncBody
from trace import Trace,Transformation
from spine import Answer,Spine,Subspine
from history import History,HistoryAssociation,HistoryPattern
from rule import Rgraph
from cleanversion import String
from checksupport import CommonDefs,ConversionTable,Declarations
from syntax import Ident,Priority,FunctionBody,Optional,SymbolType,Position,DefOrImpFunKind,FunInfo,SymbolPtr,TypeVar,AType,AType,TypeContext,AttributeVar,AttrInequality,FunCall,Index,Level,FreeVar,FreeVar,ExprInfoPtr,BITVECT,Ptr,Specials,SymbolTableEntry,TypeVarInfoPtr,TypeAttribute,Annotation,Type,Global,DefinedSymbol,Type,VarInfoPtr,AttrVarInfoPtr,Expression,VarInfoPtr,Ptr,ExprInfo,PtrN,HeapN,PtrN,STE_Kind,TypeVarInfo,VarInfo,AttrVarInfo,CheckedTypeDef,ClassDef,ClassInstance,ConsDef,Declaration,GenericDef,IndexRange,MemberDef,SelectorDef,ATypeVar,DeclarationRecord,GenericClassInfos,GenericType,InstanceType,TypeDef,TypeKind,TypeRhs,GenericClassInfo,ModuleKind,GlobalIndex
from containers import NumberSet
from Heap import Heap
from scanner import ScanContext


// Derive a symbol representation function for the program
suclsymbol_to_string ::
    {#.DclModule}               // DCL modules used
    .Index                      // Index of main module in DCL array
    .CommonDefs                 // ICL definitions excluding function definitions
    u:{#FunDef}                 // Function definitions in ICL
 -> ( .(SuclSymbol -> String)   // Resulting representation function
    , v:{#FunDef}               // Consulted function definitions
    )
 ,  [u<=v]

// Cocl to Sucl for functions
cts_function ::
    (SuclSymbol -> String)                                  // Get representation of symbol
    Int                                                     // Index of current module
    u:{#FunDef}                                             // Function definitions (from ICL)
 -> ( [(SuclSymbol,Rule SuclTypeSymbol SuclTypeVariable)]   // Type rule (derives arity)
    , [(SuclSymbol,[Bool])]                                 // Strict arguments (just main args for now)
    , [(SuclSymbol,(Int,[Rule SuclSymbol SuclVariable]))]   // Arity and rewrite rules
    , [(SuclSymbol,SuclSymbolKind)]                         // Kind of symbol
    , v:{#FunDef}                                           // Consulted function definitions
    )
 ,  [u<=v]

// Get the arities of the imported functions
cts_funtypes ::
    {#.DclModule}           // DCL modules to read types from
    .Index                  // Index of main module (because we must ignore its DCL)
 -> [(.SuclSymbol,Int)]     // List of function symbols and their associated arities

//Cocl to Sucl for exports (function decls from main dcl)
cts_exports ::
    {#DclModule}            // List of imported DCL modules
    *PredefinedSymbols      // Table of predefined symbols (for looking up the start symbol)
    Int                     // Index of current module
 -> ( .PredefinedSymbols    // Consulted predefined symbol table
    , [SuclSymbol]          // Exported symbols
    )

cts_getconstrs ::
    {#DclModule}    // Info from used DCL modules
	Int				// Index of current module in DCL module array
	CommonDefs		// CommonDefs in ICL module (excluding FunDefs)
 -> [(SuclTypeSymbol,[(SuclSymbol,(Rule SuclTypeSymbol SuclTypeVariable,[Bool]))])]
                    // List of constructor symbols for each type symbol

//Sucl to Cocl for function bodies
//1.3
stc_funcdefs ::
    PredefinedSymbol    // Compiler-predefined String symbol
    {#.DclModule}       // DCL for looking up constructor types
    Int                 // Index of current module
    CommonDefs          // Common defs in icl module (excluding FunDefs)
    Int                 // Index of first new generated function
    *ExpressionHeap     // Fresh expression space
    *(Heap VarInfo)     // Fresh variable space
    [Symredresult .SuclSymbol .SuclVariable SuclTypeSymbol SuclTypeVariable]
                        // Function definitions to convert
    *{#FunDef}          // Old function definitions
 -> ( .ExpressionHeap   // Remaining expression space
    , .(Heap VarInfo)   // Remaining variable space
    , .{#FunDef}        // Converted function definitions
    )
//3.1
/*2.0
stc_funcdefs ::
    PredefinedSymbol
    {#.DclModule}
    Int
    CommonDefs          // Common defs in icl module (excluding FunDefs)
    Int
    *ExpressionHeap
    *(Heap VarInfo)
    [Symredresult SuclSymbol .SuclVariable a b]
    *(c FunDef)
 -> ( .ExpressionHeap
    , .(Heap VarInfo)
    , .{#FunDef}
    )
 |  Array c FunDef
0.2*/

showfundefs :: (*File,*{#FunDef}) -> (.File,.{#FunDef})
