implementation module loop

// $Id$

import strat
import trace
import spine
import history
import rewr
import rule
import graph
import pfun
import basic
from general import Yes,No,--->
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

The function that produces a trace is given an initial task expression.

The function first determines a transformation (Reduce,Annotate,Instantiate) to
apply, using the strategy.

This may fail when the termination history indicates a required abstraction
higher up.  In that case, return at once with failure, and the current graph
(with shared parts excluded) as the most specific generaliser.

After application of the transformation, a trace is produced for the resulting
graph(s).

However, the production of the subtraces may fail initially because of a
necessary abstraction higher-up which wasn't there (introduced recursion).

Therefore, producing a trace can return one of two results: either a successful
trace, or failure, with an indication of which abstraction was actually
necessary.

The needed generalisation is computed by taking the most specific generaliser
for each pattern in the termination history.

In the general case, generation of the subtraces fails for both the history
pattern of the current transformation, and some patterns higher up (which were
also passed to the trace generation function.  There are now two courses of
action:

[1] Apply abstraction instead of the current transformation.  Use the returned
    most specific generaliser and the original graph to determine how to
    abstract.  Then, generate subtraces.  There should be no more abstractions
    necessary for the current node, because they should be handled in the
    graphs resulting from the abstraction.[*]

[2] Immediately return the failure, assuming (rule of thumb) that when the
    upper generalisation was necessary, the lower one won't make it go away.
    This is probably an optimisation of the optimisation process, but it can be
    important, as some backtracking code (exponential!) may not have to be
    executed.

[*] This may not be entirely true in the case of sharing.  Because shared parts
    must be pruned, the termination pattern may get smaller in the abstraction
    operation.

Questions:

[?] Which would yield better results and/or perform better: [1] or [2] above?

[?] Must the abstracted areas be associated with termination patterns that
    caused their introduction?  Or somehow with the trace node where they were
    introduced?  The termination patterns don't have to be the same over
    different branches of the trace!  Do they play a role at all in selecting
    the abstracted part?  Actually, they don't.  We just need their roots so we
    can find the corresponding subgraphs and determine the MSG's.

It would appear we can traverse the trace when everything is done and collected
all the introduced functions from it.

------------------------------------------------------------

*/

/* Disable the new abstraction node
   Unsafe subtraces are going to be pruned again.

:: FallibleTrace sym var pvar
   = GoodTrace (Trace sym var pvar)
   | NeedAbstraction [Rgraph sym var]

:: Strat sym var pvar
   :== (History sym var)
       (Rgraph sym var)
    -> Answer sym var pvar

maketrace
 :: (Strat sym var pvar)        // The strategy
    (History sym var)           // Patterns to stop partial evaluation
    (Rgraph sym var)            // Subject graph
 -> FallibleTrace sym var pvar  // The result

maketrace strategy history subject
 = ( case answer
     of No                          // Root normal form, abstract and continue with arguments
         -> handlernf
        Yes spine                   // Do something, even if it is to fail
         -> ( case subspine
              of Cycle              // Cycle in spine.  Generate x:_Strict x x with _Strict :: !a b -> b.  Probably becomes a #!
                  -> handlecycle
                 Delta              // Primitive function.  Abstract its application and continue with remainder.
                  -> handledelta
                 Force n (spine)    // Shouldn't happen
                  -> abort "loop: maketrace: spinetip returned Force???"
                 MissingCase        // Missing case.  Generate _MissingCase, possibly parametrised with user function?
                  -> handlemissingcase
                 Open pattern       // Need instantiation.  Generate two branches, extend history (for both) and continue.
                  -> handleopen pattern
                 Partial rule match rulenode spine
                  -> abort "loop: maketrace: spinetop returned Partial???"
                 Unsafe histpat     // Require pattern from history.
                  -> handleunsafe histpat // If we have a more general version with a name attached, use that.  
                                    // Otherwise, fail with the corresponding subgraph
                 Redex rule match   // Found a redex.  Unfold, extend history and continue.
                  -> handleredex rule match
                 Strict             // Need to put a strictness annotation on an open node-id.
                  -> handlestrict   // Abstract _Strict <mumble> <mumble> and continue with rest.
            ) spine
            where (redexroot,subspine) = spinetip spine
   ) strategy history subject
   where answer = strategy history subject

handlernf :: (Strat sym var pvar) (History sym var) (Rgraph sym var) -> FallibleTrace sym var pvar
handlernf _ _ _ = undef

handlecycle :: (Spine sym var pvar) (Strat sym var pvar) (History sym var) (Rgraph sym var) -> FallibleTrace sym var pvar
handlecycle _ _ _ _ = undef

handledelta :: (Spine sym var pvar) (Strat sym var pvar) (History sym var) (Rgraph sym var) -> FallibleTrace sym var pvar
handledelta _ _ _ _ = undef

handlemissingcase :: (Spine sym var pvar) (Strat sym var pvar) (History sym var) (Rgraph sym var) -> FallibleTrace sym var pvar
handlemissingcase _ _ _ _ = undef

handleopen :: (Rgraph sym pvar) (Spine sym var pvar) (Strat sym var pvar) (History sym var) (Rgraph sym var) -> FallibleTrace sym var pvar
handleopen _ _ _ _ _ = undef

handleunsafe :: (HistoryPattern sym var) (Spine sym var pvar) (Strat sym var pvar) (History sym var) (Rgraph sym var) -> FallibleTrace sym var pvar
handleunsafe _ _ _ _ _ = undef

handleredex :: (Rule sym pvar) (Pfun pvar var) (Spine sym var pvar) (Strat sym var pvar) (History sym var) (Rgraph sym var) -> FallibleTrace sym var pvar
handleredex _ _ _ _ _ _ = undef

handlestrict :: (Spine sym var pvar) (Strat sym var pvar) (History sym var) (Rgraph sym var) -> FallibleTrace sym var pvar
handlestrict _ _ _ _ = undef

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
listselect [True:bs] [x:xs] = [x:listselect bs xs]
listselect [False:bs] [x:xs] = listselect bs xs
listselect _ _ = []

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
 |  == sym
 &  == var
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
                (heap`,subject`) = rewrinstantiate pgraph proot onode (heap,subject)
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

tryunfold ::
    var                  // The root of the redex
    (Rule sym pvar)      // The rule to unfold
    (Pfun pvar var)      // The matching from rule's pattern to subject
    (Spine sym var pvar) // The spine returned by the strategy
 -> Action sym var pvar
 |  == sym
 &  == var
 &  == pvar

tryunfold redexroot rule matching spine
= act
  where act continue history failinfo instdone stricts sroot subject heap
        = Reduce reductroot trace
          where (heap`,sroot`,subject`,matching`)
                = xunfold redexroot rule (heap,sroot,subject,matching)
                noredir = abort "transtree: no mapping foor root of replacement"
                reductroot = total noredir matching` (ruleroot rule)
                history` = extendhistory subject redirect spine history
                redirect = adjust redexroot reductroot id
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
