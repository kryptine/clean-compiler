definition module coreclean

// $Id$

from strat import Strategy
from rule import Rule
from syntax import TypeSymbIdent,Ident,TypeVar,ExprInfoPtr,VarInfoPtr,SymbKind

// Transitive necessities
from strat import Substrategy
from spine import Spine,Subspine
from graph import Graph,Node
from syntax import SymbolPtr,SymbolTableEntry,STE_Kind,Index,Level,Global,TypeSymbProperties,SignClassification,PropClassification,TypeVarInfoPtr,TypeVarInfo,ExprInfo,VarInfo
from general import BITVECT
from Heap import Ptr,PtrN,HeapN
from StdOverloaded import ==
from StdString import String

:: SuclTypeSymbol
 = SuclUSER TypeSymbIdent   // A user-defined type symbol
 | SuclFN Int               // THE function type for a function with specified arity
 | SuclINT                  // Built-in integer
 | SuclCHAR                 // Etc.
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
 = SuclUser SymbKind
 | SuclCase ExprInfoPtr
 | SuclApply Int
 | SuclInt Int
 | SuclChar Char
 | SuclReal Real
 | SuclBool Bool

:: SuclSymbolKind
 = SuclFunction
 | SuclConstructor
 | SuclPrimitive

:: SuclVariable
 = SuclAnonymous Int
 | SuclNamed VarInfoPtr

suclheap :: [SuclVariable]

instance == SuclTypeSymbol
instance == SuclTypeVariable
instance == SuclSymbol
instance == SuclVariable

// Get the type rule and strictness of a built in core clean symbol
coretypeinfo :: SuclSymbol -> (Rule SuclTypeSymbol SuclTypeVariable,[Bool])

// Determine if a list of constructors completely covers a given type
corecomplete :: SuclTypeSymbol -> [SuclSymbol] -> Bool
