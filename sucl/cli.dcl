definition module cli

// $Id$

from coreclean import SuclSymbol,SuclVariable,SuclTypeSymbol,SuclTypeVariable
from strat import Strategy
from rule import Rule
from graph import Graph
from StdOverloaded import ==
from StdFile import <<<
from cleanversion import String

// Transitive necessities

from strat import Substrategy
from spine import Spine,Subspine
from graph import Node

:: Cli

arity :: Cli SuclSymbol -> Int
typerule :: Cli SuclSymbol -> Rule SuclTypeSymbol SuclTypeVariable
exports :: Cli -> [SuclSymbol]
complete :: Cli -> [SuclSymbol] -> Bool
clistrategy :: Cli ((Graph SuclSymbol SuclVariable) SuclVariable var -> Bool) -> Strategy SuclSymbol var SuclVariable answer | == var

// Build a cli structure
mkcli ::
    (SuclSymbol->String)                                                            // Symbol representation for debugging
    [(SuclSymbol,Rule SuclTypeSymbol SuclTypeVariable)]                             // Type rules of local and imported functions
    [(SuclSymbol,[Bool])]                                                           // Strictness information derived from function types
    [SuclSymbol]                                                                    // Exported symbols
    [(SuclSymbol,Int)]                                                              // Imported function symbols with their arities
    [(SuclTypeSymbol,[(SuclSymbol,(Rule SuclTypeSymbol SuclTypeVariable,[Bool]))])] // (Algebraic) types with their constructors, and the constructors' type info
    [(SuclSymbol,(Int,[Rule SuclSymbol SuclVariable]))]                             // Function bodies with their arities and their rules
 -> Cli

instance <<< Cli
