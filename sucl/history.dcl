definition module history

// $Id$

from spine import Spine
from graph import Graph
from general import Optional
from StdOverloaded import ==

// Transitive necessities

from spine import Subspine

// A history relates node-ids in the subject graph to patterns
:: History sym var
   :== [HistoryAssociation sym var]

// An association between a node-id in the subject graph and a history pattern
:: HistoryAssociation sym var
   :== ( (Link var)             // Attachment point in the subject graph where the history pattern is "housed"
       , HistoryPattern sym var // The pattern in the history
       )

// A pattern in the history, specifying the most general subject graph (footprint) for a reduction sequence
:: HistoryPattern sym var

// A link in a graph, indicated by its source node-id and the argument number
// The root of a graph can be indicated by the No constructor
:: Link var
   :== Optional (var,Int)

// Extend the history according to a spine
extendhistory
 :: (Graph sym var)         // Subject graph
    (Spine sym var pvar)    // Spine leading to the reduction operation
    (History sym var)       // Old history
 -> History sym var         // New history
 |  == sym
 &  == var
 &  == pvar

// Check the current subject graph in the history
checkhistory
 :: (History sym var)
    [Link var]
    (Graph sym var)
    var
 -> [HistoryPattern sym var]
 |  == sym
 &  == var
