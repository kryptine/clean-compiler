definition module history

// $Id$

from rule import Rgraph
from graph import Graph
from general import Optional
from StdOverloaded import ==
from StdString import toString
from StdClass import Eq
from cleanversion import String

// A history relates node-ids in the subject graph to patterns
:: History sym var
   :== [HistoryAssociation sym var]

// An association between a node-id in the subject graph and a history pattern
:: HistoryAssociation sym var
   :== ( var                        // Attachment point in the subject graph where the history pattern is "housed"
       , [HistoryPattern sym var]   // The pattern in the history
       )

// A pattern in the history, specifying the most general subject graph (footprint) for a reduction sequence
:: HistoryPattern sym var
   :== Rgraph sym var

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
 |  Eq sym
 &  Eq var

// Convert a history to its string representation
historyToString ::
    (History sym var)
 -> String
 |  toString sym
 &  toString var
 &  Eq var

(writeHistory) infixl :: *File (History sym var) -> .File | toString sym & toString,== var
(writeHistoryAssociation) infixl :: *File (HistoryAssociation sym var) -> .File | toString sym & toString,== var
