definition module newfold

// $Id$

from trace import Trace,Transformation
from spine import Answer,Spine,Subspine
from history import History,HistoryAssociation,HistoryPattern
from rule import Rgraph,Rule
from general import Optional
from StdOverloaded import ==
from StdFile import <<<
from StdString import toString

:: FuncDef sym var
   :== ( [var]              // Arguments of function
       , FuncBody sym var   // Right hand side of function
       )

:: FuncBody sym var
   = MatchPattern
       (Rgraph sym var)     // Pattern to match
       (FuncBody sym var)   // Right hand side for matching graph (case branch)
       (FuncBody sym var)   // Right hand side for failed match (case default)
   | BuildGraph
       (Rgraph sym var)     // Right hand side to reduce to

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
 -> ([Bool],FuncDef sym var,[Rgraph sym var])
 |  == sym
 &  == var
 &  == pvar
 &  toString var
 &  <<< var
 &  toString sym

instance <<< FuncBody sym var | toString sym & ==,toString var
