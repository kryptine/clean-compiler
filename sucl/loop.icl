implementation module loop

// $Id$

import trace
import strat
import history
import spine
import rewr
import rule
import graph
import pfun
import basic
from general import Yes,No
import StdEnv

/*

loop.lit - Looping to produce a trace
=====================================

Description
-----------

This module describes the transformation of a  tree  of  spines  into  a
trace.   This  is where the actual transformations on graphs are applied
like instantiation, reduction or strict annotation.

------------------------------------------------------------

Types
-----

*/

/* The action itself takes various arguments, and returns a transformation
*/

:: Action sym var pvar
   :== (Actcont sym var pvar)  //  Continuation to do subsequent symbolic reduction
       (History sym var)       //  Termination patterns
       (Failinfo sym var pvar) //  Failed matches
       Bool                    //  Instantiation attempted
       [Bool]                  //  Strict arguments of function to generate
       var                     //  Root of subject graph
       (Graph sym var)         //  Subject graph
       [var]                   //  Heap of unused nodes
   ->  Transformation sym var pvar

/* Action continuation
   An action continuation takes the result of a single partial evaluation action,
   and ultimately collects all suchs actions into a trace.
*/

:: Actcont sym var pvar
   :== (History sym var)       //  Termination patterns
       (Failinfo sym var pvar) //  Failed matches
       Bool                    //  Instantiation attempted
       [Bool]                  //  Strict arguments of function to generate
       var                     //  Root of subject graph
       (Graph sym var)         //  Subject graph
       [var]                   //  Heap of unused nodes
   ->  Trace sym var pvar

/* Failinfo is a function type
   A function of this type assigns a list of rooted graphs to a varable.
   This list of rooted graphs are precisely those patterns that symfailedsym to
   match at the given variable in the subject graph.
*/

:: Failinfo sym var pvar
   :== var
   ->  [Rgraph sym pvar]

/*

------------------------------------------------------------

Implementation
--------------

*/

loop
 :: (((Graph sym pvar) pvar var -> ub:Bool) -> Strategy sym var pvar (Answer sym var pvar))
    ([Rgraph sym pvar] (Rgraph sym pvar) -> ub:Bool)
    !(.[var],.Rule sym var)
 -> Trace sym var pvar
 |  == sym
 &  == var
 &  == pvar

loop strategy matchable (initheap,rule)
= maketrace inithistory initfailinfo initinstdone initstricts initsroot initsubject initheap

  where maketrace history failinfo instdone stricts sroot subject heap
        = Trace stricts (mkrule sargs sroot subject) answer history transf
          where answer = makernfstrategy history (strategy matchable`) rnfnodes sroot subject
                transf = transform sroot sargs answer maketrace history failinfo instdone stricts sroot subject heap

                rnfnodes = removeDup (listselect stricts sargs++fst (graphvars subject sargs))

                matchable` pgraph pnode snode
                = matchable (failinfo snode) (mkrgraph pnode pgraph)

        inithistory = []
        initfailinfo = const []
        initinstdone = False
        initstricts = map (const False) sargs

        sargs = arguments rule; initsroot = ruleroot rule; initsubject = rulegraph rule

listselect :: [.Bool] [.elem] -> [.elem]
listselect _ _ = undef

initrule
 :: ![var]
    (sym->[pvar])
    sym
 -> ([var],Rule sym var)

initrule [root:heap] template sym
= (heap`,mkrule args root (updategraph root (sym,args) emptygraph))
  where (args,heap`) = claim (template sym) heap
initrule _ _ _
= abort "initrule: out of heap space"

/* ------------------------------------------------------------------------ */

transform
 :: var                    // Top of spine (starting point for strategy)
    [var]                  // Arguments of function to generate
    !(Answer sym var pvar) // Result of strategy
 -> Action sym var pvar
 |  == var
 &  == pvar

transform anode sargs (Yes spine)
= selectfromtip (spinetip spine)
  where selectfromtip (nid,Open rgraph) = tryinstantiate nid rgraph anode sargs
        selectfromtip (nid,Redex rule matching) = tryunfold nid rule matching spine
        selectfromtip (nid,Strict) = tryannotate nid sargs
        selectfromtip spine = dostop

transform anode sargs No
= dostop

// ==== ATTEMPT TO INSTANTIATE A FREE VARIABLE WITH A PATTERN ====

tryinstantiate
 :: var               // The open node
    (Rgraph sym pvar) // The pattern to instantiate with
    var               // The root of the spine
    [var]             // Arguments of the function to generate
 -> Action sym var pvar
 |  == var
 &  == pvar

tryinstantiate onode rpattern anode sargs
= act
  where act continue history failinfo instdone stricts sroot subject heap
        | anode==sroot                                   // Check if strategy applied at root
          && goodorder strictargs sargs subject subject` // Check if order of arguments of rule ok
        = Instantiate success fail
        = Stop
          where success = continue history failinfo True stricts` sroot subject` heap`
                fail = continue history failinfo` True stricts` sroot subject heap
                failinfo` = adjust onode [rpattern:failinfo onode] failinfo
                (heap`,subject`) = instantiate pgraph proot onode (heap,subject)
                proot = rgraphroot rpattern; pgraph = rgraphgraph rpattern

                stricts` = if instdone stricts (map2 ((||) o (==) onode) sargs stricts)
                // Quickly annotate the open node as strict if this is the first instantiation

                strictargs = [sarg\\(True,sarg)<-zip2 stricts` sargs]

goodorder
 :: [var]
    [var]
    (Graph sym var)
    (Graph sym var)
 -> Bool
 |  == var

goodorder stricts sargs subject subject`
= startswith match match`
  where match = removeMembers (fst (graphvars subject sargs)) stricts
        match` = removeMembers (fst (graphvars subject` sargs)) stricts

// See if second argument list has the first one as its initial part
startswith
 :: .[elem] // list S
    .[elem] // list L
 -> .Bool   // whether L starts with S
 |  == elem

startswith [] _ = True
startswith [x:xs] [y:ys]
| x==y
= startswith xs ys
startswith _ _  = False


// ==== ATTEMPT TO UNFOLD A REWRITE RULE ====

tryunfold
 :: var                  // The root of the redex
    (Rule sym pvar)      // The rule to unfold
    (Pfun pvar var)      // The matching from rule's pattern to subject
    (Spine sym var pvar) // The spine returned by the strategy
 -> Action sym var pvar
 |  == var
 &  == pvar

tryunfold redexroot rule matching spine
= act
  where act continue history failinfo instdone stricts sroot subject heap
        = Reduce reductroot trace
          where (heap`,sroot`,subject`,matching`)
                = xunfold redexroot rule (heap,sroot,subject,matching)
                noredir = abort "transtree: no mapping foor root of replacement"
                reductroot = total noredir matching` (ruleroot rule)
                redirect = adjust redexroot reductroot id
                history` = extendhistory subject redirect spine history
                trace = continue history` failinfo instdone stricts sroot` subject` heap`

tryannotate
 :: var   // The node to be made strict
    [var] // Arguments of the function to generate
 -> Action sym var pvar
 |  == var

tryannotate strictnode sargs
= act
  where act continue history failinfo instdone stricts sroot subject heap
        | not instdone && isMember strictnode sargs
        = Annotate trace
        = Stop
          where stricts` = map2 ((||) o (==) strictnode) sargs stricts
                trace = continue history failinfo instdone stricts` sroot subject heap


// ==== STOP PARTIAL EVALUATION ====

dostop
 :: Action sym var pvar

dostop
= ds
  where ds continue history failinfo instdone stricts sroot subject heap = Stop
