definition module law

// $Id$

from coreclean import SuclSymbol,SuclVariable
from strat import Law,Strategy
from StdOverloaded import ==

// Transitive necessities

from strat import Substrategy
from spine import Spine,Subspine
from graph import Graph,Node

// The list of special Clean transformation laws
cleanlaws :: [(SuclSymbol,Law SuclSymbol var SuclVariable result)]

// The strategy for built in clean symbols
corestrategy :: ((Graph SuclSymbol SuclVariable) SuclVariable var -> Bool) -> Strategy SuclSymbol var SuclVariable result | == var
