definition module loop

from strat import Strategy
from spine import Answer
from trace import Trace
from rule import Rgraph,Rule
from graph import Graph
from StdOverloaded import ==

from strat import Substrategy,Subspine   // for Strategy
from graph import Node                   // for Strategy
from basic import Optional               // for Answer
from spine import Spine                  // for Answer
from trace import History,Transformation // for Trace

loop
 :: (((Graph sym pvar) pvar var -> ub:Bool) -> Strategy sym var pvar (Answer sym var pvar))
    ([Rgraph sym pvar] (Rgraph sym pvar) -> ub:Bool)
    !(.[var],.Rule sym var)
 -> Trace sym var pvar
 |  == sym
 &  == var
 &  == pvar

initrule
 :: ![var]
    (sym->[pvar])
    sym
 -> ([var],Rule sym var)
