definition module coreclean

// $Id$

from strat import Strategy
from rule import Rule
from syntax import TypeSymbIdent,Ident,TypeVar,ExprInfoPtr,VarInfoPtr,SymbKind,BoundVar,DefinedSymbol
from StdOverloaded import ==,toString
from StdFile import <<<

// Transitive necessities
from strat import Substrategy
from spine import Spine,Subspine
from graph import Graph,Node
from syntax import SymbolPtr,SymbolTableEntry,STE_Kind,Index,Level,Global,TypeSymbProperties,SignClassification,PropClassification,TypeVarInfoPtr,TypeVarInfo,ExprInfo,VarInfo,ConsVariable
from general import BITVECT
from Heap import Ptr,PtrN,HeapN
from cleanversion import String

:: SuclTypeSymbol
 = SuclUSER (Global Index)  // A user-defined type symbol (index into com_type_def array)
 | SuclTCVAR ConsVariable   // A type constructor variable
 | SuclFN                   // THE function type for a function with specified arity
 | SuclTUPLE Int            // The tuple type of the specified size
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
 | SuclTupleSelect Int Int	// tuple's size and element's index in that order
 | SuclFieldSelect (Global DefinedSymbol) Int
 | SuclArraySelect (Global DefinedSymbol)
 | SuclDictSelect BoundVar // [Selection] // FIXME: from DictionarySelection; what to do with these?
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

// Get the type rule and strictness of a built in core clean symbol
coretyperule :: !SuclSymbol -> Rule SuclTypeSymbol SuclTypeVariable
corestricts :: SuclSymbol -> [Bool]

// Determine if a list of constructors completely covers a given type
corecomplete :: SuclTypeSymbol -> [SuclSymbol] -> Bool
