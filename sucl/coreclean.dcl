definition module coreclean

// $Id$

from syntax import TypeSymbIdent,Ident,TypeVar,ExprInfoPtr,VarInfoPtr

// Transitive necessities
from syntax import SymbolPtr,SymbolTableEntry,STE_Kind,Index,Level,Global,TypeSymbProperties,SignClassification,PropClassification,TypeVarInfoPtr,TypeVarInfo,ExprInfo,VarInfo
from general import BITVECT
from Heap import Ptr,PtrN,HeapN
from StdOverloaded import ==
from StdString import String

:: SuclTypeSymbol
 = SuclUSER TypeSymbIdent
 | SuclFN
 | SuclINT
 | SuclCHAR
 | SuclREAL
 | SuclBOOL
 | SuclDYNAMIC
 | SuclFILE
 | SuclWORLD

:: SuclTypeVariable
 = SuclANONYMOUS Int
 | SuclNAMED TypeVar

sucltypeheap :: [SuclTypeVariable]

:: SuclSymbol
 = SuclUser SymbolPtr
 | SuclCase ExprInfoPtr
 | SuclInt Int
 | SuclChar Char
 | SuclBool Bool

:: SuclSymbolKind
 = SuclFunction
 | SuclConstructor
 | SuclPrimitive

:: SuclVariable
 = SuclAnonymous Int
 | SuclNamed VarInfoPtr

instance == SuclVariable
