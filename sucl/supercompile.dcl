definition module supercompile

from trans import ImportedConstructors
from transform import Group
from checksupport import CommonDefs,VarHeap,DclModule
from syntax import IndexRange,ExpressionHeap,FunType,CheckedTypeDef,TypeDefInfos,TypeHeaps,FunDef

// Transitive necessities

from checksupport import Declarations,ConversionTable
from containers import NumberSet
from syntax import AType,ATypeVar,Annotation,AttrInequality,AttrVarHeap,AttrVarInfo,AttrVarInfoPtr,AttributeVar,ClassDef,ClassInstance,ConsDef,Declaration,DeclarationRecord,DefOrImpFunKind,DefinedSymbol,ExprInfo,ExprInfoPtr,Expression,FreeVar,FunCall,FunInfo,FunctionBody,GenericClassInfo,GenericClassInfos,GenericDef,GenericType,Global,Ident,Index,InstanceType,Level,MemberDef,Position,STE_Kind,SelectorDef,Specials,SymbolPtr,SymbolTableEntry,SymbolType,Type,TypeAttribute,TypeContext,TypeDef,TypeDefInfo,TypeKind,TypeRhs,TypeVar,TypeVarHeap,TypeVarInfo,TypeVarInfoPtr,VarInfo,VarInfoPtr
from typeproperties import TypeClassification
from scanner import Context,Priority
from general import BITVECT,Optional
from Heap import Heap,HeapN,Ptr,PtrN
from StdString import String

supercompile
 :: !{# CommonDefs}             // common_defs
    !IndexRange                 // array_instances
    !{#DclModule}               // dcl_mods
    !Int                        // main_dcl_module_n
    !*{!Group}                  // components
    !*{#FunDef}                 // fun_defs
    !*VarHeap                   // var_heap
    !*ExpressionHeap            // expression_heap
    !{#{#FunType}}              // imported_funs
    !*{#{#CheckedTypeDef}}      // dcl_types
    !ImportedConstructors       // used_conses_in_dynamics
    !*TypeDefInfos              // type_def_infos
    !*TypeHeaps                 // type_heaps

 -> (   !*{!Group}              // components
    ,   !*{#FunDef}             // fun_defs
    ,   !*{#{#CheckedTypeDef}}  // dcl_types
    ,   !ImportedConstructors   // used_conses
    ,   !*VarHeap               // var_heap
    ,   !*TypeHeaps             // type_heaps
    ,   !*ExpressionHeap        // expression_heap
    )
