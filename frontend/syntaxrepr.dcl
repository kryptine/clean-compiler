definition module syntaxrepr

from StdOverloaded import toString
from StdString import String
from Heap import Ptr,HeapN,PtrN
from general import BITVECT
from scanner import Priority,ScanContext
from typeproperties import PropClassification,SignClassification
from StdFile import <<<

/* This module defines additional functions for
 * converting (the contents of) data structures to string representation.
 * It just contains a lot of toString instances
 */

from syntax import AType
instance toString  AType

from syntax import ATypeVar
instance toString  ATypeVar

from syntax import Annotation

from syntax import App
instance toString  App

from syntax import AttrInequality
instance toString  AttrInequality

from syntax import AttrVarInfo

from syntax import AttrVarInfoPtr

from syntax import AttributeVar

from syntax import BasicType
instance toString  BasicType

from syntax import ClassDef
instance <<<       ClassDef
instance toString  ClassDef

from syntax import ConsDef
instance toString  ConsDef

from syntax import ConsVariable
instance toString  ConsVariable

from syntax import DefinedSymbol
instance toString  DefinedSymbol

from syntax import ExprInfo

from syntax import ExprInfoPtr

from syntax import Expression
instance toString  Expression

from syntax import FieldSymbol
instance toString  FieldSymbol

from syntax import GenericClassInfo

from syntax import GenericClassInfos

from syntax import GenericDef
instance <<<       GenericDef

from syntax import GenericType

from syntax import Global
instance toString (Global a) | toString a

from syntax import GlobalIndex
instance toString  GlobalIndex

from syntax import Ident

from syntax import Index

from syntax import Level

from syntax import MemberDef
instance <<<       MemberDef
instance toString  MemberDef

from syntax import Position
instance toString  Position

from syntax import RecordType
instance toString  RecordType

from syntax import STE_Kind

from syntax import SelectorDef
//instance <<<     SelectorDef
instance toString  SelectorDef

from syntax import SymbIdent
instance toString  SymbIdent

from syntax import SymbKind
instance <<<       SymbKind
instance toString  SymbKind

from syntax import SymbolPtr

from syntax import SymbolTableEntry

from syntax import SymbolType
instance toString  SymbolType

from syntax import Type
instance toString  Type

from syntax import TypeAttribute

from syntax import TypeContext
instance toString  TypeContext

from syntax import TypeDef
instance toString (TypeDef a) | toString a

from syntax import TypeKind

from syntax import TypeRhs
instance toString  TypeRhs

from syntax import TypeSymbIdent
instance toString  TypeSymbIdent

from syntax import TypeSymbProperties

from syntax import TypeVar
instance toString  TypeVar

from syntax import TypeVarInfo
//instance toString TypeVarInfo

from syntax import TypeVarInfoPtr

from syntax import VarInfo

from syntax import VarInfoPtr
