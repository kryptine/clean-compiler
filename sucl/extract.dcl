definition module extract

from rule import Rgraph,Rule
from graph import Graph,Node
from general import Optional
from StdOverloaded import ==

actualfold ::
    [var]
    [var]
    ((Rgraph sym var)->Node sym var)
    (pvar->var->bool)
    (sym,[pvar])
    [(pvar,Graph sym pvar)]
    (Rule sym var)
 -> Optional (Rule sym var,[Rgraph sym var])
 |  == var
 &  == pvar

splitrule ::
    ((Rgraph sym var)->Node sym var)
    [var]
    [var]
    (Rule sym var)
    (Rgraph sym var)
 -> (Rule sym var,[Rgraph sym var])
 |  == var

finishfold ::
    ((Rgraph sym var)->Node sym var)
    [var]
    [var]
    var
    (Graph sym var)
 -> (Graph sym var,[Rgraph sym var])
 |  == var
