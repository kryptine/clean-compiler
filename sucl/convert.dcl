definition module convert

// $Id$

from syntax import FunDef,FunType
from checksupport import DclModule
from rule import Rule
from coreclean import SuclTypeSymbol,SuclTypeVariable,SuclSymbol,SuclSymbolKind,SuclVariable

// Transitively required stuff
from syntax import Ident,Priority,FunctionBody,Optional,SymbolType,Position,DefOrImpFunKind,FunInfo,SymbolPtr,TypeVar,AType,AType,TypeContext,AttributeVar,AttrInequality,FunCall,Index,Level,FreeVar,FreeVar,ExprInfoPtr,BITVECT,Ptr,Specials,SymbolTableEntry,TypeVarInfoPtr,TypeAttribute,Annotation,Type,Context,Global,DefinedSymbol,Type,VarInfoPtr,AttrVarInfoPtr,Expression,VarInfoPtr,Ptr,ExprInfo,PtrN,HeapN,PtrN,STE_Kind,TypeVarInfo,VarInfo,AttrVarInfo,CheckedTypeDef,ClassDef,ClassInstance,ConsDef,Declaration,GenericDef,IndexRange,MemberDef,SelectorDef,ATypeVar,DeclarationRecord,GenericClassInfos,GenericType,InstanceType,TypeDef,TypeKind,TypeRhs,GenericClassInfo
from StdString import String
from checksupport import CommonDefs,ConversionTable,Declarations
from containers import NumberSet


// Cocl to Sucl for functions
cts_function
 :: Int                                                 // Index of current module
    {#FunDef}                                           // Function definitions (from ICL)
 -> ( [(SuclSymbol,Rule SuclTypeSymbol SuclTypeVariable)]//Type rule (derives arity)
    , [(SuclSymbol,[Bool])]                             // Strict arguments (just main args for now)
    , [(SuclSymbol,[Rule SuclSymbol SuclVariable])]     // Rewrite rules
    , [(SuclSymbol,SuclSymbolKind)]                     // Kind of symbol
    )

//Cocl to Sucl for exports (function decls from main dcl)
cts_exports ::
    {#FunDef}       // List of function definitions (from ICL)
    {#DclModule}    // List of imported DCL modules
    Int             // Index of current module
 -> [SuclSymbol]
