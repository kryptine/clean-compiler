definition module complete

from graph import Graph
from StdOverloaded import ==

:: Pattern sym var
   :== (Graph sym var,[var])

coveredby
 :: ([sym]->Bool)
    (Graph sym var)
    ![Pattern sym pvar]
    [var]
 -> Bool
 |  == sym
 &  == var
 &  == pvar
