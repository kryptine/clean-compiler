implementation module history

// $Id$

import rule
import graph
import pfun
import basic
from general import Optional,Yes,No
import StdEnv

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


/************************************************
* Verifying a subject graph against the history *
************************************************/

matchhistory
 :: (History sym var)           // Complete history against which to check
    [var]                       // Node-ids for which to include history patterns
    (Graph sym var)             // Current subject graph
    var                         // Current application point of strategy
 -> [HistoryPattern sym var]    // Matching history patterns
 |  == sym
 &  == var

matchhistory hist spinenodes sgraph snode
 = foldr (checkassoc spinenodes sgraph snode) [] hist

checkassoc spinenodes sgraph snode (var,pats) rest
 = if (isMember var spinenodes) (foldr checkpat rest pats) rest
   where checkpat pat rest
         = if (isinstance (hgraph,hroot) (sgraph,snode)) [pat:rest] rest
           where hgraph = rgraphgraph pat; hroot = rgraphroot pat

/*
instantiate ::
    (HistoryPattern sym pvar)
    (Graph sym var)
    var
    ([(pvar,var)],[(pvar,var)],[(pvar,var)])
 -> ([(pvar,var)],[(pvar,var)],[(pvar,var)])
*/

(writeHistory) infixl :: *File (History sym var) -> .File | toString sym & toString,== var
(writeHistory) file history = sfoldl (writeHistoryAssociation) file history

(writeHistoryAssociation) infixl :: *File (HistoryAssociation sym var) -> .File | toString sym & toString,== var
(writeHistoryAssociation) file ha = file <<< showpair toString (showlist toString) ha <<< nl
