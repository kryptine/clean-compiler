definition module supercompile

// $Id$

from trans import ImportedConstructors
from transform import Group
from checksupport import CommonDefs,VarHeap,DclModule
from syntax import IndexRange,ExpressionHeap,FunType,CheckedTypeDef,TypeDefInfos,TypeHeaps,FunDef
from predef import PredefinedSymbols

// Transitive necessities

from checksupport import Declarations,ConversionTable
from containers import NumberSet
from syntax import AType,ATypeVar,Annotation,AttrInequality,AttrVarHeap,AttrVarInfo,AttrVarInfoPtr,AttributeVar,ClassDef,ClassInstance,ConsDef,Declaration,DeclarationRecord,DefOrImpFunKind,DefinedSymbol,ExprInfo,ExprInfoPtr,Expression,FreeVar,FunCall,FunInfo,FunctionBody,GenericClassInfo,GenericClassInfos,GenericDef,GenericType,Global,Ident,Index,InstanceType,Level,MemberDef,Position,STE_Kind,SelectorDef,Specials,SymbolPtr,SymbolTableEntry,SymbolType,Type,TypeAttribute,TypeContext,TypeDef,TypeDefInfo,TypeKind,TypeRhs,TypeVar,TypeVarHeap,TypeVarInfo,TypeVarInfoPtr,VarInfo,VarInfoPtr
from predef import PredefinedSymbol
from typeproperties import TypeClassification
from scanner import Context,Priority
from general import BITVECT,Optional
from Heap import Heap,HeapN,Ptr,PtrN
from StdString import String

supercompile ::
    !{#DclModule}               // dcl_mods
    !Int                        // main_dcl_module_n
    !*{#FunDef}                 // fun_defs
    !*VarHeap                   // var_heap
    !*ExpressionHeap            // expression_heap
    !*PredefinedSymbols         // Predefined symbol table
    !*File                      // Log file
 -> (   !*{#FunDef}             // fun_defs
    ,   !*VarHeap               // var_heap
    ,   !*ExpressionHeap        // expression_heap
    ,   IndexRange              // Range of newly generated functions (already existing functions are overwritten)
    ,   !.PredefinedSymbols     // Consulted predefined symbol table
    ,   !.File                  // Written log file
    )
