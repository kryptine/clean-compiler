definition module history

// $Id$

from spine import Spine
from rule import Rgraph
from graph import Graph

from spine import Subspine // for Spine

:: History sym var
   :== [(var,[Rgraph sym var])]

extendhistory
 :: (Graph sym var)
    (var -> var)
    (Spine sym var pvar)
    (History sym var)
 -> History sym var
