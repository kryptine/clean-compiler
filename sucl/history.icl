implementation module history

// $Id$

import spine
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
   :== ( (Link var)             // Attachment point in the subject graph where the history pattern is "housed"
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


/*********************************************
* Extending the history according to a spine *
*********************************************/

// A function that associates specific patterns with extensible nodes
// To be used for extending history patterns
:: LinkExtender sym var
   :== (Link var)               // The extensible link to look for
    -> HistoryPattern sym var   // The associated pattern

extendhistory
 :: (Graph sym var)         // Subject graph
    (Spine sym var pvar)    // Spine leading to the reduction operation
    (History sym var)       // Old history
 -> History sym var         // New history
 |  == sym
 &  == var
 &  == pvar

extendhistory sgraph spine history
 = [newpattern:touchmod history]
   where (newpattern,_,extender)
          = foldspine extendpair extenddefault extenddefault (extendforce sgraph) extenddefault extendopen (extendpartial sgraph) (const extenddefault) (extendredex sgraph) extenddefault spine No Extensible
         touchmod = map (mapsnd (patextend extender))

patextend
 :: (LinkExtender sym var)
    (HistoryPattern sym var)
 -> HistoryPattern sym var

patextend extender (Closed sym args) = Closed sym (map (patextend extender) args)
patextend extender OpenHist = OpenHist
patextend extender (Extensible link) = extender link

extendpair
 :: var                         // Subject node-id where spine is rooted
    (  var
       (Link var)
       (LinkExtender sym var)
    -> ( HistoryAssociation sym var
       , HistoryPattern sym var
       , LinkExtender sym var
       )
    )
    (Link var)                  // Link in subject graph to this spine
    (LinkExtender sym var)      // Input link extender
 -> ( HistoryAssociation sym var
    , HistoryPattern sym var    // Returned history pattern
    , LinkExtender sym var      // Returned link extender
    )

extendpair snode extendsub link extender
 = extendsub snode link extender

extenddefault
 :: var
    (Link var) 
    (LinkExtender sym var)
 -> ( HistoryAssociation sym var
    , HistoryPattern sym var
    , LinkExtender sym var
    )
extenddefault _ link extender
 = (nonewpattern,Extensible link,extender)
   where nonewpattern = abort "history: extenddefault: no new pattern for default spine"

// Extend history for a Force spine
// FIXME: For now, only look at function node and to-be-strict argument
//        Forget what was already determined strict
extendforce
 :: (Graph sym var)
    Int
    (  (Link var)
       (LinkExtender sym var)
    -> ( HistoryAssociation sym var
       , HistoryPattern sym var
       , LinkExtender sym var
       )
    )
    var
    (Link var)
    (LinkExtender sym var)
 -> ( HistoryAssociation sym var
    , HistoryPattern sym var
    , LinkExtender sym var
    )
 |  == var

extendforce sgraph argno forcesub snode link extender0
 | not sdef
   = abort "history: extendforce: force from open node-id???"
 = (newpattern,histpat1,extender2)
   where (newpattern,histpat0,extender1) = forcesub (Yes (snode,argno)) extender0
         histpat1 = Closed ssym [argpat i \\ i <- [0..] & _ <- sargs]
         argpat i
          = if (i==argno) histpat0 (Extensible (Yes (snode,i)))
         (sdef,(ssym,sargs)) = varcontents sgraph snode
         extender2 = adjust link histpat1 extender1

// Extend history patterns according to an Open spine
extendopen
 :: rgraph                      // Pattern to drive instantiation (not used)
    var                         // Node-id in subject graph that was open
    (Link var)                  // Where subject graph pointed to this open node-id
    (LinkExtender sym var)      // Input link extender
 -> ( HistoryAssociation sym var
    , HistoryPattern sym var    // Pattern for this spine
    , LinkExtender sym var      // Resulting link extender
    )
 |  == var

extendopen _ _ link extender0
 = (newpattern,histpat,extender1)
   where histpat = OpenHist
         newpattern = (link,histpat)
         extender1 = adjust link histpat extender0

extendpartial
 :: (Graph sym var)             // Subject graph
    (Rule sym pvar)             // Applied rewrite rule
    (Pfun pvar var)             // Partial match from rewrite rule's pattern to subject graph
    pvar                        // Node-id in rule where partial match went to subspine
    (  (Link var)               // Link passed to subspine handler
       (LinkExtender sym var)   // Link extender input to subspine handler
    -> ( HistoryAssociation sym var
       , HistoryPattern sym var // Pattern returned for subspine
       , LinkExtender sym var   // Link extender returned for subspine
       )
    )
    var                         // Node-id in subject with function application
    (Link var)                  // Link to root of partial match in subject graph
    (LinkExtender sym var)      // Remaining link extender
 -> ( HistoryAssociation sym var
    , HistoryPattern sym var    // History patterns with derived pattern prefixed
    , LinkExtender sym var      // Extended link extender
    )
 |  == sym
 &  == var
 &  == pvar

extendpartial sgraph rule matching subnode extendsub snode link restextender
 = extendfunction sgraph rule matching ((==)subnode) (const extendsub) snode link restextender

extendredex
 :: (Graph sym var)             // Subject graph
    (Rule sym pvar)             // Applied rewrite rule
    (Pfun pvar var)             // Partial match from rewrite rule's pattern to subject graph
    var                         // Root of redex in subject graph
    (Link var)                  // Link to root of redex in subject graph
    (LinkExtender sym var)      // Remaining link extender
 -> ( HistoryAssociation sym var
    , HistoryPattern sym var    // History patterns with derived pattern prefixed
    , LinkExtender sym var      // Extended link extender
    )
 |  == sym
 &  == var
 &  == pvar

extendredex sgraph rule matching snode link extender
 = extendfunction sgraph rule matching (const False) nosub snode link extender
   where nosub = abort "history: extendredex: full match with subspine??"

extendfunction
 :: (Graph sym var)             // Subject graph
    (Rule sym pvar)             // Applied rewrite rule
    (Pfun pvar var)             // Partial match from rewrite rule's pattern to subject graph
    (pvar -> Bool)              // Checks whether the subspine applies here
    (  (HistoryAssociation sym var)
       (Link var)               // Link passed to subspine handler
       (LinkExtender sym var)   // Link extender input to subspine handler
    -> ( HistoryAssociation sym var
       , HistoryPattern sym var // Pattern returned for subspine
       , LinkExtender sym var   // Link extender returned for subspine
       )
    )
    var                         // Root of partial match in subject graph
    (Link var)                  // Link to root of partial match in subject graph
    (LinkExtender sym var)      // Remaining link extender
 -> ( HistoryAssociation sym var
    , HistoryPattern sym var    // History patterns with derived pattern prefixed
    , LinkExtender sym var      // Extended link extender
    )
 |  == sym
 &  == var
 &  == pvar

extendfunction sgraph rule matching issub extendsub snode link extender0
 | not sdef
   = abort "history: extendfunction: partial or full match at open node-id???"
 = (newpattern,thispat,extender2)
   where extender2 = adjust link thispat extender1
         thispat = Closed ssym argpatts
         (newpattern,argpatts,extender1) = extendnodes sgraph rgraph matching snode issub extendsub thisnewpattern extender0 rargs
         (sdef,(ssym,_)) = varcontents sgraph snode
         rgraph = rulegraph rule
         rargs = arguments rule
         thisnewpattern = (link,thispat)

extendnodes
 :: (Graph sym var)             // Subject graph
    (Graph sym pvar)            // Applied rewrite rule
    (Pfun pvar var)             // Partial match from rewrite rule's pattern to subject graph
    var                         // Parent node-id in subject graph to this node-id list for creating links
    (pvar -> Bool)              // Tells if this is where the subspine was attached
    (  (HistoryAssociation sym var)
       (Link var)               // Link passed to subspine handler
       (LinkExtender sym var)   // Link extender input to subspine handler
    -> ( HistoryAssociation sym var
       , HistoryPattern sym var // Pattern returned for subspine
       , LinkExtender sym var   // Link extender returned for subspine
       )
    )
    (HistoryAssociation sym var)
    (LinkExtender sym var)      // Remaining link extender
    [pvar]                      // Node-ids in rule to handle
 -> ( HistoryAssociation sym var
    , [HistoryPattern sym var]  // History patterns with derived pattern prefixed
    , LinkExtender sym var      // Extended link extender
    )
 |  == sym
 &  == var
 &  == pvar

extendnodes sgraph rgraph matching sparent issub extendsub newpattern restextender rnodes
 = foldr (extendnode sgraph rgraph matching issub extendsub) (newpattern,[],restextender) (zip2 links rnodes)
   where links = [Yes (sparent,i)\\i<-[0..]]

extendnode
 :: (Graph sym var)                 // Subject graph
    (Graph sym pvar)                // Applied rewrite rule
    (Pfun pvar var)                 // Partial match from rewrite rule's pattern to subject graph
    (pvar -> Bool)                  // Tells if this is where the subspine was attached
    (  (HistoryAssociation sym var)
       (Link var)                   // Link passed to subspine handler
       (LinkExtender sym var)       // Link extender input to subspine handler
    -> ( HistoryAssociation sym var
       , HistoryPattern sym var     // Pattern returned for subspine
       , LinkExtender sym var       // Link extender returned for subspine
       )
    )
    ( Link var                      // Referring link to current node-id
    , pvar                          // Current node-id in rule
    )
    ( HistoryAssociation sym var
    , [HistoryPattern sym var]      // History patterns to prefix derived patterns to
    , (LinkExtender sym var)        // Remaining link extender
    )
 -> ( HistoryAssociation sym var
    , [HistoryPattern sym var]      // History patterns with derived pattern prefixed
    , (LinkExtender sym var)        // Extended link extender
    )
 |  == sym
 &  == var
 &  == pvar

extendnode sgraph rgraph matching issub extendsub (link,rnode) (newpattern0,rest,extender0)
 | issub rnode
   = (subnewpattern,[subpattern:rest],subextender)
 | rdef
   = foldpfun mapped unmapped matching rnode
 = unmapped
   where (subnewpattern,subpattern,subextender)
          = extendsub newpattern0 link extender0
         mapped snode
          = (newpattern1,[thispat:rest],extender2)
            where extender2 = adjust link thispat extender1
                  thispat = Closed rsym argpatts
                  (newpattern1,argpatts,extender1) = extendnodes sgraph rgraph matching snode issub extendsub newpattern0 extender0 rargs
         unmapped
          = (newpattern0,[Extensible link:rest],extender0)
         (rdef,(rsym,rargs)) = varcontents rgraph rnode


/************************************************
* Verifying a subject graph against the history *
************************************************/

checkhistory
 :: (History sym var)
    [Link var]
    (Graph sym var)
    var
 -> [HistoryPattern sym var]
 |  == sym
 &  == var

checkhistory hist spinelinks sgraph snode
 = foldr (checkassoc spinelinks sgraph snode) [] hist

checkassoc spinelinks sgraph snode (link,pat) rest
 | isMember link spinelinks && checkpat sgraph pat snode
   = [pat:rest]
 = rest

checkpat :: (Graph sym var) (HistoryPattern sym var) var -> Bool | == sym & == var
checkpat sgraph (Closed psym pargs) snode
 # (sdef,(ssym,sargs)) = varcontents sgraph snode
 = sdef && psym==ssym && eqlen pargs sargs && and [checkpat sgraph parg sarg \\ parg<-pargs & sarg<-sargs]
checkpat sgraph OpenHist snode
 = not (fst (varcontents sgraph snode))
checkpat _ (Extensible _) _
 = True


/****************
* Miscellaneous *
****************/

instance == (Optional a) | == a
 where (==) No No = True
       (==) (Yes x1) (Yes x2) = x1==x2
       (==) _ _ = False
