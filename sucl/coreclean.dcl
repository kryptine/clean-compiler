definition module coreclean

// $Id$

from syntax import Ident

// Transitive necessities
from syntax import SymbolPtr,SymbolTableEntry,STE_Kind,Index,Level
from Heap import Ptr,PtrN,HeapN
from StdString import String

:: SuclTypeSymbol

:: SuclTypeVariable

:: SuclSymbol
 = SuclUser Ident

:: SuclSymbolKind

:: SuclVariable
