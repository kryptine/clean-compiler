definition module cli

// $Id$

from coreclean import SuclSymbol,SuclVariable,SuclTypeSymbol,SuclTypeVariable
from strat import Strategy
from rule import Rule
from graph import Graph
from StdOverloaded import ==

// Transitive necessities

from strat import Substrategy
from spine import Spine,Subspine
from graph import Node

:: Cli

typerule :: Cli SuclSymbol -> Rule SuclTypeSymbol SuclTypeVariable
exports :: Cli -> [SuclSymbol]
complete :: Cli -> [SuclSymbol] -> Bool
clistrategy :: Cli ((Graph SuclSymbol SuclVariable) SuclVariable var -> Bool) -> Strategy SuclSymbol var SuclVariable answer | == var

// Build a cli structure
mkcli ::
    [(SuclSymbol,Rule SuclTypeSymbol SuclTypeVariable)]
    [(SuclSymbol,[Bool])]
    [SuclSymbol]
    [(SuclTypeSymbol,[SuclSymbol])]
    [(SuclSymbol,[Rule SuclSymbol SuclVariable])]
 -> Cli
