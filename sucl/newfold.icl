implementation module newfold

// $Id$

import extract
import trace
import spine
import rule
import dnc
import graph
import basic
import StdEnv

/*

newfold.lit - New folding function
==================================

Description
-----------

This module defines one function, `fullfold'.   It  derives  a  function
defintion  from  a  trace, by first searching and folding autorecursion,
and searching the remainder of the trace for introduced recursion.

------------------------------------------------------------

Includes
--------

>   %include "dnc.lit"

>   %include "../src/basic.lit"
>   %include "../src/pfun.lit"
>   %include "../src/graph.lit"
>   %include "../src/rule.lit"
>   %include "../src/spine.lit"
>   %include "trace.lit"
>   %include "extract.lit"

------------------------------------------------------------

Interface
---------

Exported identifiers:

>   %export
>       fullfold ||  Full folding function
>       tracer   ||  Debugging
> ||    extract  ||  Fold a trace and extract new functions
> ||    etracer  ||  Debugging

------------------------------------------------------------

Deprecated type
---------------

>   tracer * ** ***
>   ==  (   (rgraph * **->(*,[**])) ->
>           * ->
>           trace * ** *** ->
>           (bool,([bool],[rule * **],[rgraph * **]))
>       ) ->
>       (rgraph * **->(*,[**])) ->
>       * ->
>       trace * ** *** ->
>       (bool,([bool],[rule * **],[rgraph * **]))

Implementation
--------------

`Fullfold foldarea fnsymbol  trace'  folds  the  trace.   It  returns  a
resulting  list  of  rewrite  rules  and  rooted  graphs  for  which new
functions have to be introduced.

First, an attempt is made to fold to the right hand side of the  initial
rewrite  rule  (autorecursion),  or  residues of the right hand side for
which no instantiation was necessary.  If any tip of the  trace  can  be
folded, this is done.

The remaining subtraces of the trace (which is possibly the whole trace)
are folded in their own right.  Introduced recursion is  applied  if  it
occurs within any subtrace.
*/

fullfold ::
    (Etracer sym var pvar)
    ((Rgraph sym var)->(sym,[var]))
    sym
    (Trace sym var pvar)
 -> ([Bool],[Rule sym var],[Rgraph sym var])
 |  == sym
 &  == var
 &  == pvar

fullfold trc foldarea fnsymbol trace
| recursive
  = recurseresult
= newextract trc foldarea trace
  where (recursive,recurseresult) = recurse foldarea fnsymbol trace

/*
`Recurse foldarea fnsymbol trace' is a pair `(recursive,recurseresult)'.
`Recurseresult'  is  the derived function definition (strictness, rules,
and new areas), obtained by folding the trace.  `Recurse' tries to  fold
the areas in the trace to recursive function calls when at all possible.
The allowed patterns for the autorecursion are derived from the  top  of
the  trace.  If no recursive function call can be found, `recurseresult'
is `False'.
*/

recurse ::
    ((Rgraph sym var)->(sym,[var]))
    sym
 -> (Trace sym var pvar)
 -> (Bool,([Bool],[Rule sym var],[Rgraph sym var]))
 |  == sym
 &  == var
 &  == pvar

recurse foldarea fnsymbol
= f ([],[])
  where f (newhist,hist) (Trace stricts rule answer history (Reduce reductroot trace))
        | isEmpty pclosed && superset popen ropen
          = f (newhist`,newhist`) trace
            where rargs = arguments rule; rroot = ruleroot rule; rgraph = rulegraph rule
                  (pclosed,popen) = graphvars rgraph rargs
                  (_,ropen) = graphvars rgraph [rroot]
                  newhist` = [(rroot,rgraph):newhist]
        f (newhist,hist) (Trace stricts rule answer history (Annotate trace))
        | isEmpty pclosed && superset popen ropen
          = f (newhist`,hist) trace
            where rargs = arguments rule; rroot = ruleroot rule; rgraph = rulegraph rule
                  (pclosed,popen) = graphvars rgraph rargs
                  (_,ropen) = graphvars rgraph [rroot]
                  newhist` = [(rroot,rgraph):newhist]
        f (newhist,hist) (Trace stricts rule answer history transf)
        = foldtips foldarea (fnsymbol,arguments rule) (removeDup newhist`,removeDup hist) (Trace stricts rule answer history transf)
          where rroot = ruleroot rule; rgraph = rulegraph rule
                newhist` = [(rroot,rgraph):newhist]


/*
`Foldtips foldarea foldcont hist trace' folds all occurrences of (rooted
graphs  in  hist)  in the tips of the trace. It returns a list of rules,
which are the results  of  folding,  and  a  list  of  areas  for  which
functions  must  be  introduced. If no occurrences were found, Absent is
returned.

>   foldtips ::
>       (rgraph * **->(*,[**])) ->
>       (*,[**]) ->
>       ([(**,graph * **)],[(**,graph * **)]) ->
>       trace * ** *** ->
>       (bool,([bool],[rule * **],[rgraph * **]))

>   foldtips foldarea foldcont
>   =   ft
>       where ft hist trace
>             =   ft' transf
>                 where Trace stricts rule answer history transf = trace
>                       ft' Stop
>                       =   foldoptional exres (pair True.addstrict stricts) (actualfold deltanodes rnfnodes foldarea (=) foldcont (snd hist) rule)
>                           where deltanodes = foldoptional [] getdeltanodes answer
>                                 rnfnodes = foldoptional [rhs rule] (const []) answer
>                       ft' (Instantiate yestrace notrace)
>                       =   ft'' (ft hist yestrace) (ft hist notrace)
>                           where ft'' (False,yessra) (False,nosra) = exres
>                                 ft'' (yesfound,(yesstricts,yesrules,yesareas)) (nofound,(nostricts,norules,noareas))
>                                 =   (True,(stricts,yesrules++norules,yesareas++noareas))
>                       ft' (Reduce reductroot trace)
>                       =   ft'' (ft (fst hist,fst hist) trace)
>                           where ft'' (False,sra) = exres
>                                 ft'' (found,sra) = (True,sra)
>                       ft' (Annotate trace)
>                       =   ft'' (ft hist trace)
>                           where ft'' (False,sra) = exres
>                                 ft'' (found,sra) = (True,sra)
>                    || exres = (False,mapfst3 only (extract noetrc foldarea trace ([],[],[])))
>                       exres = (False,newextract noetrc foldarea trace)

>   addstrict stricts (rule,areas) = (stricts,[rule],areas)

>   noetrc trace area = id

>   pair x y = (x,y)

>   only :: [*] -> *
>   only [x] = x
>   only xs = error "only: not a singleton list"
*/

foldtips ::
    ((Rgraph sym var)->(sym,[var]))
    (sym,[var])
 -> ([(var,Graph sym var)],[(var,Graph sym var)])
    (Trace sym var pvar)
 -> (Bool,([Bool],[Rule sym var],[Rgraph sym var]))
 |  == sym
 &  == var
 &  == pvar

foldtips foldarea foldcont
= ft
  where ft hist trace
        = case transf
          of Stop
              -> foldoptional exres (pair True o addstrict stricts) (actualfold deltanodes rnfnodes foldarea (==) foldcont (snd hist) rule)
                 where deltanodes = foldoptional [] getdeltanodes answer
                       rnfnodes = foldoptional [ruleroot rule] (const []) answer
             Instantiate yestrace notrace
              -> ft`` (ft hist yestrace) (ft hist notrace)
                 where ft`` (False,yessra) (False,nosra) = exres
                       ft`` (yesfound,(yesstricts,yesrules,yesareas)) (nofound,(nostricts,norules,noareas))
                       = (True,(stricts,yesrules++norules,yesareas++noareas))
             Reduce reductroot trace
              -> ft`` (ft (fst hist,fst hist) trace)
                 where ft`` (False,sra) = exres
                       ft`` (found,sra) = (True,sra)
             Annotate trace
              -> ft`` (ft hist trace)
                 where ft`` (False,sra) = exres
                       ft`` (found,sra) = (True,sra)
          where (Trace stricts rule answer history transf) = trace
                exres = (False,newextract noetrc foldarea trace)

addstrict stricts (rule,areas) = (stricts,[rule],areas)

noetrc trace area = id

pair x y = (x,y)

only :: [.elem] -> .elem
only [x] = x
only xs = abort "only: not a singleton list"

/*
------------------------------------------------------------------------

`Extract foldarea trace (rules,areas)' folds the trace,  creating  rules
which  are prepended to `rules' and areas for introduced functions which
are prepended to `areas'.

The use of `extract' is to derive rules for parts of a trace that aren't
already folded by the detection of either auto or introduced recursion.

The  accumulator  argument  is  for  efficiency reasons.  It is probably
clearer to drop it and instead apply `concat' at a higher level.

Introduced recursion may be detected inside the trace.  Since the  trace
is  in  practice a subtrace of another trace, introduced recursion might
exist to the supertrace.  This does not count, since it is not  possible
to fold the first occurrence of the termination history pattern which is
in the supertrace.

>   etracer * ** ***
>   ==  trace * ** *** ->
>       rgraph * ** ->
>       bool ->
>       bool
*/

:: Etracer sym var pvar :==
       (Trace sym var pvar)
       (Rgraph sym var)
       Bool
    -> Bool

/*
>   extract
>   ::  etracer * ** *** ->
>       (rgraph * **->(*,[**])) ->
>       trace * ** *** ->
>       ([[bool]],[rule * **],[rgraph * **]) ->
>       ([[bool]],[rule * **],[rgraph * **])

>   extract trc newname (Trace stricts rule answer history transf) (strictss,rules,areas)
>   =   (strictss',recrule:rules,recareas++areas), if trc (Trace stricts rule answer history transf) unsafearea recursive
>   =   mapfst3 (ifopen (const strictss') id answer) (f transf (strictss,rules,areas)), otherwise
>       where f (Reduce reductroot trace) = extract trc newname trace
>             f (Annotate trace) = extract trc newname trace
>             f (Instantiate yestrace notrace) = extract trc newname yestrace.extract trc newname notrace
>             f Stop (strictss,rules,areas) = (stricts:strictss,mkrule rargs rroot stoprgraph:rules,stopareas++areas)

>             (recursive,unsafearea)
>             =   foldoptional (False,undef) (findspinepart rule transf) answer, if isreduce transf
>             =   (False,error "extract: not a Reduce transformation"), otherwise

>             (recrule,recareas) = splitrule newname rnfnodes deltanodes rule unsafearea
>             (stoprgraph,stopareas) = finishfold newname rnfnodes deltanodes rroot rgraph

>             rargs = lhs rule; rroot = rhs rule; rgraph = rulegraph rule
>             rnfnodes = foldoptional (rroot:) (const id) answer (nodelist rgraph rargs)

>             deltanodes = foldoptional [] getdeltanodes answer

>             strictss' = stricts:strictss


This is a version of `extract' that does not use the collector argument.

>   newextract
>   ::  etracer * ** *** ->
>       (rgraph * **->(*,[**])) ->
>       trace * ** *** ->
>       ([bool],[rule * **],[rgraph * **])

>   newextract trc newname (Trace stricts rule answer history transf)
>   =   (stricts,[recrule],recareas), if recursive
>   =   subex transf, otherwise
>       where subex (Reduce reductroot trace) = newextract trc newname trace
>             subex (Annotate trace) = newextract trc newname trace
>             subex (Instantiate yestrace notrace)
>             = (stricts,yesrules++norules,yesareas++noareas)
>               where (yesstricts,yesrules,yesareas) = newextract trc newname yestrace
>                     (nostricts,norules,noareas) = newextract trc newname notrace
>             subex Stop = (stricts,[mkrule rargs rroot stoprgraph],stopareas)

>             (recursive,unsafearea)
>             =   foldoptional (False,undef) (findspinepart rule transf) answer, if isreduce transf
>             =   (False,error "newextract: not a Reduce transformation"), otherwise

>             (recrule,recareas) = splitrule newname rnfnodes deltanodes rule unsafearea
>             (stoprgraph,stopareas) = finishfold newname rnfnodes deltanodes rroot rgraph

>             rargs = lhs rule; rroot = rhs rule; rgraph = rulegraph rule
>             rnfnodes = foldoptional (rroot:) (const id) answer (nodelist rgraph rargs)

>             deltanodes = foldoptional [] getdeltanodes answer

>   isreduce (Reduce reductroot trace) = True
>   isreduce transf = False
*/

newextract ::
    (Etracer sym var pvar)
    ((Rgraph sym var)->(sym,[var]))
    (Trace sym var pvar)
 -> ([Bool],[Rule sym var],[Rgraph sym var])
 |  == sym
 &  == var
 &  == pvar

newextract trc newname (Trace stricts rule answer history transf)
| recursive
  = (stricts,[recrule],recareas)
= subex transf
  where subex (Reduce reductroot trace) = newextract trc newname trace
        subex (Annotate trace) = newextract trc newname trace
        subex (Instantiate yestrace notrace)
        = (stricts,yesrules++norules,yesareas++noareas)
          where (yesstricts,yesrules,yesareas) = newextract trc newname yestrace
                (nostricts,norules,noareas) = newextract trc newname notrace
        subex Stop = (stricts,[mkrule rargs rroot stoprgraph],stopareas)

        (recursive,unsafearea)
        = if (isreduce transf)
             (foldoptional (False,undef) (findspinepart rule transf) answer)
             (False,abort "newextract: not a Reduce transformation")

        (recrule,recareas) = splitrule newname rnfnodes deltanodes rule unsafearea
        (stoprgraph,stopareas) = finishfold newname rnfnodes deltanodes rroot rgraph

        rargs = arguments rule; rroot = ruleroot rule; rgraph = rulegraph rule
        rnfnodes = foldoptional (cons rroot) (const id) answer (varlist rgraph rargs)

        deltanodes = foldoptional [] getdeltanodes answer

isreduce (Reduce reductroot trace) = True
isreduce transf = False


/*
`Findspinepart toprule rule spine (transformation,trace)' is a pair with
a  boolean  determining whether some instance of the `spine', determined
using `toprule', occurs in a residu of itself in `trace'.

The use of `findspinepart' is to detect introduced recursion in  `trace'
to its root.

>   findspinepart :: rule * ** -> transformation * ** *** -> spine * ** *** -> (bool,rgraph * **)

>   findspinepart rule transf spine
>   =   snd (foldspine pair stop stop id stop (const stop) partial (const stop) redex stop spine)
>       where pair node (pattern,recursion)
>             =   (pattern',recursion')
>                 where pattern'
>                       =   updategraph node cnt pattern, if def
>                       =   pattern, otherwise
>                       (def,cnt) = dnc (const "in findspinepart") graph node
>                       recursion'
>                       =   (True,mkrgraph node pattern'), if findpattern (pattern',node) (spinenodes spine) node transf
>                       =   recursion, otherwise
>             partial rule matching (pattern,recursion) = (extgraph' graph rule matching pattern,recursion)
>             redex rule matching = (extgraph' graph rule matching emptygraph,norecursion)
>             stop = (emptygraph,norecursion)
>             norecursion = (False,error "findspinepart: no part of spine found")
>             graph = rulegraph rule

>   extgraph' sgraph rule
>   =   extgraph sgraph rgraph (nodelist rgraph (lhs rule))
>       where rgraph = rulegraph rule
*/

findspinepart :: (Rule sym var) (Transformation sym var pvar) (Spine sym var pvar) -> (Bool,Rgraph sym var) | == sym & == var & == pvar

findspinepart rule transf spine
= snd (foldspine pair stop stop force stop (const stop) partial (const stop) redex stop spine)
  where pair node (pattern,recursion)
        = (pattern`,recursion`)
          where pattern`
                = if def (updategraph node cnt pattern) pattern
                (def,cnt) = dnc (const "in findspinepart") graph node
                recursion`
                | findpattern (pattern`,node) (spinenodes spine) node transf
                  = (True,mkrgraph node pattern`)
                = recursion
        force _ res = res
        partial rule matching _ (pattern,recursion) = (extgraph` graph rule matching pattern,recursion)
        redex rule matching = (extgraph` graph rule matching emptygraph,norecursion)
        stop = (emptygraph,norecursion)
        norecursion = (False,abort "findspinepart: no part of spine found")
        graph = rulegraph rule

extgraph` sgraph rule
= extgraph sgraph rgraph (varlist rgraph (arguments rule))
  where rgraph = rulegraph rule

/*
`Findpattern pattern rule residuroot transformation  trace'  bepaalt  of
een instance van `pattern' voorkomt in een residu van `residuroot' in de
`trace'.

Omwille van optimalisatie worden, met  behulp  van  `transformation'  en
`rule',  alleen  nieuw  toegevoegde  nodes  na  een  rewrite in de trace
bekeken. De rest is toch niet veranderd.
*/

findpattern :: (Graph sym var2,var2) [var] var (Transformation sym var pvar) -> Bool | == sym & == var & == var2 & == pvar

findpattern pattern thespinenodes residuroot transf
| isMember residuroot thespinenodes
  = False       // Root of residu no longer in spine - must have come to RNF.

findpattern pattern thespinenodes residuroot (Reduce reductroot trace)
= fp (redirect residuroot) trace
  where fp residuroot (Trace stricts rule answer history transf)
         | or [isinstance pattern (graph,node) \\ node<-varlist graph [residuroot]]
           = True
             where graph = rulegraph rule
        fp residuroot trace = findpattern` pattern residuroot trace
        redirect = adjust (last thespinenodes) reductroot id

findpattern pattern thespinenodes residuroot (Instantiate yestrace notrace)
= findpattern` pattern residuroot yestrace || findpattern` pattern residuroot notrace

findpattern pattern thespinenodes residuroot (Annotate trace)
= findpattern` pattern residuroot trace

findpattern pattern thespinenodes residuroot Stop
= False


findpattern` :: (Graph sym var2,var2) var (Trace sym var pvar) -> Bool | == sym & == var & == var2 & == pvar

findpattern` pattern residuroot (Trace stricts rule answer history transf)
= findpattern pattern thespinenodes residuroot transf
  where thespinenodes = foldoptional [] spinenodes answer

/*
`Getdeltanodes spine' is the list of nodes in the spine  that  we  don't
want  to introduce new functions for because they contain a delta symbol
or a strict argument.
*/

getdeltanodes ::
    (Spine sym var pvar)
 -> [var]

getdeltanodes spine
= foldspine pair none (True,[]) force none (const none) partial (const none) redex none spine
  where pair node (forced,nodes) = if forced [node:nodes] nodes
        none = (False,[])
        force _ nodes = (True,nodes)
        partial _ _ _ nodes = (False,nodes)
        redex _ _ = none
