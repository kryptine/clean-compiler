definition module coreclean

// $Id$

from syntax import TypeSymbIdent,Ident,TypeVar

// Transitive necessities
from syntax import SymbolPtr,SymbolTableEntry,STE_Kind,Index,Level,Global,TypeSymbProperties,SignClassification,PropClassification,TypeVarInfoPtr,TypeVarInfo
from general import BITVECT
from Heap import Ptr,PtrN,HeapN
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
 = SuclUser Ident

:: SuclSymbolKind

:: SuclVariable
