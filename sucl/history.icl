implementation module history

// $Id$

import rule
import graph
import pfun
import basic
from general import Optional,Yes,No,--->
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
 |  Eq sym
 &  Eq var

matchhistory hist spinenodes sgraph snode
= foldr ((checkassoc--->"history.checkassoc begins from history.matchhistory") spinenodes sgraph snode) [] hist <--- "history.matchhistory ends"

checkassoc spinenodes sgraph snode (var,pats) rest
= ((if (isMember var spinenodes) (foldr (checkpat--->"history.checkassoc.checkpat begins from history.checkassoc") rest pats) (rest--->"history.checkassoc history attachment node is not part of the spine nodes")) <--- "history.checkassoc ends") ---> ("history.checkassoc number of history patterns for node is "+++toString (length pats))
  where checkpat pat rest
        = (if ((isinstance--->"graph.isinstance begins from history.checkassoc.checkpat") (hgraph,hroot) (sgraph,snode)) [pat:rest] rest) <--- "history.checkassoc.checkpat ends"
          where hgraph = rgraphgraph pat; hroot = rgraphroot pat

/*
instantiate ::
    (HistoryPattern sym pvar)
    (Graph sym var)
    var
    ([(pvar,var)],[(pvar,var)],[(pvar,var)])
 -> ([(pvar,var)],[(pvar,var)],[(pvar,var)])
*/

historyToString ::
    (History sym var)
 -> String
 |  toString sym
 &  toString var
 &  Eq var

historyToString history
= showlist (showpair toString (showlist toString)) history

(writeHistory) infixl :: *File (History sym var) -> .File | toString sym & toString,== var
(writeHistory) file history = file <<< "<history>" // sfoldl (writeHistoryAssociation) file history

(writeHistoryAssociation) infixl :: *File (HistoryAssociation sym var) -> .File | toString sym & toString,== var
(writeHistoryAssociation) file ha = file <<< "<historyassociation>" // showpair toString (showlist toString) ha <<< nl

printhistory ::
    (sym->String)
    (var->String)
    String
    (History sym var)
    *File
 -> .File
 |  == var

printhistory showsym showvar indent history file
= foldl (flip (printhistoryassociation showsym showvar indent)) file history

printhistoryassociation showsym showvar indent vargraphs file
= printlist (myshowrgraph showsym showvar) (indent+++"   ") rgraphs (file <<< indent <<< showvar var <<< " <=" <<< nl)
//= file <<< indent <<< showvar var <<< " <=" <<< showlist (showrgraph showsym showvar) rgraphs <<< nl
//= file <<< indent <<< showpair showvar (showlist toString) vargraphs <<< nl
//= file <<< "<history>" <<< nl
  where (var,rgraphs) = vargraphs

myshowrgraph showsym showvar rgraph
= hd (printgraphBy showsym showvar (rgraphgraph rgraph) [rgraphroot rgraph])
