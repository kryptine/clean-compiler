implementation module spine

// $Id$

import history
import rule
import graph
import pfun
import basic
from general import No,Yes
import StdEnv

/*

spine.lit - The extended functional strategy
============================================

Description
-----------

This script implements the strategy answer, and a function to compute it
for a given graph in a rewrite system.

The  strategy  answer  is  a  spine  --  in principle a colon of partial
matches from patterns of rewrite rules to the graph, with at the  bottom
the insteresting part: a redex, an open node or something else.  See the
definition of subspine for that.

The strategy function attempts to find a redex to reduce  the  graph  to
normal  form  instead  of  root normal form.  This is done by applying a
root normal form strategy recursively in preorder  over  the  graph  (of
course  ignoring  cycles).   The  node  at  which  the  root normal form
strategy was applied is returned in the strategy answer, so laziness can
be preserved.

------------------------------------------------------------

Interface
---------

Exported identifiers:

>   %export
>       answer          ||  Strategy answer type
>       foldspine       ||  Higher order general spine folding
>       ifopen          ||  Check for answer indicating Open
>       printanswer     ||  Make a human-readable representation of an answer
>       printspine      ||  Make a human-readable representation of a spine
>       showanswer      ||  Make a representation of an answer
>       showspine       ||  Make a representation of a spine
>       showsubspine    ||  Make a representation of a subspine
>       spine           ||  Colon of partial matches
>       spinenodes      ||  Determine nodes in a spine
>       spinetip        ||  Determine bottom of spine
>       subspine        ||  Bottom of spine

>       history         ||  Symbolic reduction history type
>       printhistory    ||  Make a human-readable representation of a history
>       showhistory     ||  Make a representation of a history

Required types:

    subspine - rule@rule.lit,rgraph@rule.lit,pfun@pfun.lit

------------------------------------------------------------

Includes
--------

>   %include "basic.lit"    ||  optional
>   %include "pfun.lit"     ||  pfun
>   %include "graph.lit"    ||  graph
>   %include "rule.lit"     ||  rgraph rule

------------------------------------------------------------

Implementation
--------------


Answer describes the answer of a strategy.  Absence of a  spine  implies
that the node was in root normal form.

>   answer * ** *** == optional (spine * ** ***)

>   showanswer showa showb showc = showoptional (showspine showa showb showc)
>   printanswer printa printb printc = foldoptional ["Rnf"] (printspine printa printb printc)

*/

:: Answer sym var pvar
   :== Optional (Spine sym var pvar)

/*

Spine  describes the spine returned by a strategy.  It contains the node
at which the strategy was applied, and the result for that node.

>   spine * ** *** == (**,subspine * ** ***)

>   showspine showa showb showc = showpair showb (showsubspine showa showb showc)

>   printspine printa printb printc
>   =   foldspine pair cycle delta force missingcase open partial unsafe redex strict
>       where pair node (line,lines) = (printb node++" => "++line):lines
>             cycle = ("Cycle",[])
>             delta = ("Delta",[])
>             force lines = ("Force",lines)
>             missingcase = ("MissingCase",[])
>             open rgraph = ("Open "++printrgraph printa printc rgraph,[])
>             partial rule matching lines = ("Partial <fn> "++printrule printa printc rule++' ':printpfun printc printb matching,lines)
>             unsafe rgraph = ("Unsafe "++printrgraph printa printb rgraph,[])
>             redex rule matching = ("Redex <fn> "++printrule printa printc rule++' ':printpfun printc printb matching,[])
>             strict = ("Strict",[])

*/

:: Spine sym var pvar
   :== (var,Subspine sym var pvar)

/*

Subspine describes what was the result of the strategy applied to a node
in a graph.

>   subspine * ** ***
>   ::= Cycle                                               | ||  The spine contains a cycle
>       Delta                                               | ||  An imported (delta) rule was found
>       Force (spine * ** ***)                              | ||  Global strictness annotation forced evaluation of a subgraph
>       MissingCase                                         | ||  All alternatives failed for a function symbol
>       Open (rgraph * ***)                                 | ||  Need root normal form of open node for matching
>       Partial (rule * ***) (pfun *** **) (spine * ** ***) | ||  A rule was strictly partially matched
>       Unsafe (rgraph * **)                                | ||  Terminated due to immininent recursion
>       Redex (rule * ***) (pfun *** **)                    | ||  Total match
>       Strict                                                ||  Need root normal form due to strictness

>   showsubspine showa showb showc
>   =   sh
>       where sh Cycle = "Cycle"
>             sh Delta = "Delta"
>             sh (Force spine) = "(Force "++showspine showa showb showc spine++")"
>             sh MissingCase = "MissingCase"
>             sh (Open rgraph) = "(Open "++showrgraph showa showc rgraph++")"
>             sh (Partial rule matching spine) = "(Partial "++showrule showa showc rule++' ':showpfun showc showb matching++' ':showspine showa showb showc spine++")"
>             sh (Unsafe rgraph) = "(Unsafe "++showrgraph showa showb rgraph++")"
>             sh (Redex rule matching) = "(Redex "++showrule showa showc rule++' ':showpfun showc showb matching++")"
>             sh Strict = "Strict"

    printsubspine printa printb printc
    =   pr
        where pr Cycle = "Cycle"
              pr Delta = "Delta"
              pr (Force argno spine) = "(Force <argno> "++printspine printa printb printc spine++")"
              pr MissingCase = "MissingCase"
              pr (Open rgraph) = "(Open "++printrgraph printa printc rgraph++")"
              pr (Partial rule matching spine) = "(Partial "++printrule printa printc rule++' ':printpfun printc printb matching++' ':printspine printa printb printc spine++")"
              pr (Unsafe rgraph) = "(Unsafe "++printrgraph printa printb rgraph++")"
              pr (Redex rule matching) = "(Redex "++printrule printa printc rule++' ':printpfun printc printb matching++")"
              pr Strict = "Strict"

*/

:: Subspine sym var pvar
   = Cycle                                                              // The spine contains a cycle
   | Delta                                                              // An imported (delta) rule was found
   | Force Int (Spine sym var pvar)                                     // Global strictness annotation forced evaluation of a subgraph at specified argument position
   | MissingCase                                                        // All alternatives failed for a function symbol
   | Open (Rgraph sym pvar)                                             // Need root normal form of open node for matching
   | Partial (Rule sym pvar) (Pfun pvar var) pvar (Spine sym var pvar)  // A rule was strictly partially matched
   | Unsafe (HistoryPattern sym var)                                    // Terminated due to immininent recursion
   | Redex (Rule sym pvar) (Pfun pvar var)                              // Total match
   | Strict                                                             // Need root normal form due to strictness

/*

>   foldspine
>   ::  (**->****->*****) ->
>       **** ->
>       **** ->
>       (*****->****) ->
>       **** ->
>       (rgraph * ***->****) ->
>       (rule * ***->pfun *** **->*****->****) ->
>       (rgraph * **->****) ->
>       (rule * ***->pfun *** **->****) ->
>       **** ->
>       spine * ** *** ->
>       *****

>   foldspine pair cycle delta force missingcase open partial unsafe redex strict
>   =   fold
>       where fold (node,subspine) = pair node (foldsub subspine)
>             foldsub Cycle = cycle
>             foldsub Delta = delta
>             foldsub (Force spine) = force (fold spine)
>             foldsub MissingCase = missingcase
>             foldsub (Open rgraph) = open rgraph
>             foldsub (Partial rule matching spine) = partial rule matching (fold spine)
>             foldsub (Unsafe rgraph) = unsafe rgraph
>             foldsub (Redex rule matching) = redex rule matching
>             foldsub Strict = strict

*/

foldspine
 :: !(var .subresult -> .result)                                    // Fold the spine itself
    .subresult                                                      // Fold a Cycle subspine
    .subresult                                                      // Fold a Delta subspine
    (Int .result -> .subresult)                                     // Fold a Force subspine
    .subresult                                                      // Fold a MissingCase subspine
    ((Rgraph sym pvar) -> .subresult)                               // Fold an Open subspine
    ((Rule sym pvar) (Pfun pvar var) pvar .result -> .subresult)    // Fold a Partial subspine
    ((HistoryPattern sym var) -> .subresult)                        // Fold an Unsafe subspine
    ((Rule sym pvar) (Pfun pvar var) -> .subresult)                 // Fold a Redex subspine
    .subresult                                                      // Fold a Strict subspine
    .(Spine sym var pvar)                                           // The spine to fold
 -> .result                                                         // The final result

foldspine pair cycle delta force missingcase open partial unsafe redex strict spine
= fold spine
  where fold spine
        = pair node (foldsub subspine)
          where (node,subspine) = spine
        foldsub Cycle = cycle
        foldsub Delta = delta
        foldsub (Force argno spine) = force argno (fold spine)
        foldsub MissingCase = missingcase
        foldsub (Open rgraph) = open rgraph
        foldsub (Partial rule matching rnode spine) = partial rule matching rnode (fold spine)
        foldsub (Unsafe histpat) = unsafe histpat
        foldsub (Redex rule matching) = redex rule matching
        foldsub Strict = strict

spinetip :: !(Spine sym var pvar) -> Spine sym var pvar
spinetip (_,Force argno spine) = spinetip spine
spinetip (_,Partial _ _ pnode spine) = spinetip spine
spinetip spine = spine

spinenodes :: .(Spine sym var pvar) -> [var]
spinenodes spine
= foldspine cons [] [] (const id) [] (const []) partial (const []) redex [] spine
  where partial _ _ _ = id
        redex _ _ = []

ifopen :: result result !.(Answer sym var pvar) -> result
ifopen open other spine
= foldoptional other (checkopen o spinetip) spine
  where checkopen (onode,Open pattern) = open
        checkopen tip = other


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

extendopen _ snode link extender0
 = (newpattern,histpat,extender1)
   where histpat = OpenHist
         newpattern = (snode,histpat)
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
         thisnewpattern = (snode,thispat)

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


/****************
* Miscellaneous *
****************/

instance == (Optional a) | == a
 where (==) No No = True
       (==) (Yes x1) (Yes x2) = x1==x2
       (==) _ _ = False
