definition module history

// $Id$

from graph import Graph
from spine import Spine
from StdOverloaded import ==

// Transitive necessities

from spine import Subspine

:: History sym var

extendhistory
 :: (Graph sym var)         // Subject graph
    (Spine sym var pvar)    // Spine leading to the reduction operation
    (History sym var)       // Old history
 -> History sym var         // New history
 |  == sym
 &  == var
 &  == pvar
