definition module coreclean

// $Id$

from strat import Strategy
from rule import Rule
from syntax import TypeSymbIdent,Ident,TypeVar,ExprInfoPtr,VarInfoPtr,SymbKind
from StdOverloaded import ==,toString
from StdFile import <<<

// Transitive necessities
from strat import Substrategy
from spine import Spine,Subspine
from graph import Graph,Node
from syntax import SymbolPtr,SymbolTableEntry,STE_Kind,Index,Level,Global,TypeSymbProperties,SignClassification,PropClassification,TypeVarInfoPtr,TypeVarInfo,ExprInfo,VarInfo
from general import BITVECT
from Heap import Ptr,PtrN,HeapN
from cleanversion import String

:: SuclTypeSymbol
 = SuclUSER (Global Index)  // A user-defined type symbol (index into com_type_def array)
 | SuclFN Int               // THE function type for a function with specified arity
 | SuclINT                  // Built-in integer
 | SuclCHAR                 // Etc.
 | SuclREAL
 | SuclBOOL
 | SuclSTRING
 | SuclDYNAMIC
 | SuclFILE
 | SuclWORLD
 | SuclERROR				// Type error

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
 | SuclString String

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
instance == SymbKind

instance toString SuclTypeSymbol
instance <<< SuclTypeSymbol
instance toString SuclTypeVariable
instance <<< SuclTypeVariable
instance toString SuclSymbol
instance <<< SuclSymbol
instance toString SuclSymbolKind
instance <<< SuclSymbolKind
instance toString SuclVariable
instance <<< SuclVariable
instance toString SymbKind
instance <<< SymbKind

instance toString (Ptr a)
instance <<< (Ptr a)

// Get the type rule and strictness of a built in core clean symbol
coretyperule :: !SuclSymbol -> Rule SuclTypeSymbol SuclTypeVariable
corestricts :: SuclSymbol -> [Bool]

// Determine if a list of constructors completely covers a given type
corecomplete :: SuclTypeSymbol -> [SuclSymbol] -> Bool
