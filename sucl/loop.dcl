definition module loop

// $Id$

from strat import Strategy
from trace import Trace
from spine import Answer
from history import HistoryAssociation,HistoryPattern
from rule import Rgraph,Rule
from graph import Graph
from StdOverloaded import ==
from StdFile import <<<
from StdString import toString

from strat import Substrategy,Subspine   // for Strategy
from trace import History,Transformation // for Trace
from spine import Spine                  // for Answer
from graph import Node                   // for Strategy
from basic import Optional               // for Answer

loop
 :: (((Graph sym pvar) pvar var -> ub:Bool) -> Strategy sym var pvar (Answer sym var pvar))
    ([Rgraph sym pvar] (Rgraph sym pvar) -> ub:Bool)
    !(.[var],.Rule sym var)
 -> Trace sym var pvar
 |  == sym
 &  == var
 &  == pvar
 &  toString sym    // Debugging
 &  toString var    // Debugging
 &  <<< var         // Debugging

initrule
 :: ![var]
    (sym->[pvar])
    sym
 -> ([var],Rule sym var)
