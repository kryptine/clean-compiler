definition module newfold

// $Id$

from trace import Trace,Transformation
from spine import Answer,Spine,Subspine
from history import History,HistoryAssociation,HistoryPattern
from rule import Rgraph,Rule
from general import Optional
from StdOverloaded import ==

:: FunBody sym var
   :== [Rule sym var]

:: Etracer sym var pvar :==
       (Trace sym var pvar)
       (Rgraph sym var)
       Bool
    -> Bool

fullfold ::
    (Etracer sym var pvar)
    ((Rgraph sym var)->(sym,[var]))
    sym
    (Trace sym var pvar)
 -> ([Bool],FunBody sym var,[Rgraph sym var])
 |  == sym
 &  == var
 &  == pvar
