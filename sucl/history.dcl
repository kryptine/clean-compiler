definition module history

// $Id$

from graph import Graph
from general import Optional
from StdOverloaded import ==

// A history relates node-ids in the subject graph to patterns
:: History sym var
   :== [HistoryAssociation sym var]

// An association between a node-id in the subject graph and a history pattern
:: HistoryAssociation sym var
   :== ( var                    // Attachment point in the subject graph where the history pattern is "housed"
       , HistoryPattern sym var // The pattern in the history
       )

// A pattern in the history, specifying the most general subject graph (footprint) for a reduction sequence
:: HistoryPattern sym var
   = Closed sym [HistoryPattern sym var]    // Indicates a closed node-id in the subject graph (created by a (partial) match)
   | OpenHist                               // Indicates an open node-id in the subject graph (created by instantiation)
   | Extensible (Link var)                  // Indicates a link to an untouched node-id in the subject graph, where this pattern can be extended

// A link in a graph, indicated by its source node-id and the argument number
// The root of a graph can be indicated by the No constructor
:: Link var
   :== Optional (var,Int)

// Check the current subject graph in the history
matchhistory
 :: (History sym var)           // Complete history against which to check
    [var]                       // Node-ids for which to include history patterns
    (Graph sym var)             // Current subject graph
    var                         // Current application point of strategy
 -> [HistoryPattern sym var]    // Matching history patterns
 |  == sym
 &  == var
