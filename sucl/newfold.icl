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

import general

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
*/

:: FuncDef sym var
   :== ( [var]              // Arguments of function
       , FuncBody sym var   // Right hand side of function
       )

:: FuncBody sym var
   = MatchPattern
       (Rgraph sym var)     // Pattern to match
       (FuncBody sym var)   // Right hand side for matching graph (case branch)
       (FuncBody sym var)   // Right hand side for failed match (case default)
   | BuildGraph
       (Rgraph sym var)     // Right hand side to reduce to

/*
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
 -> ([Bool],FuncDef sym var,[Rgraph sym var])
 |  == sym
 &  == var
 &  == pvar
 &  toString sym
 &  toString var
 &  toString pvar
 &  <<< var
 &  <<< pvar

fullfold trc foldarea fnsymbol trace
| recursive
  = addlhs recurseresult
= addlhs (newextract trc foldarea trace)
  where (recursive,recurseresult) = recurse foldarea fnsymbol trace
        addlhs = mapsnd3 (pair (arguments rule))
        (Trace _ rule _ _ _) = trace

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
 -> (Bool,([Bool],FuncBody sym var,[Rgraph sym var]))
 |  == sym
 &  == var
 &  == pvar
 &  toString sym
 &  toString var
 &  toString pvar
 &  <<< var
 &  <<< pvar

recurse foldarea fnsymbol
= f ([],[])
  where f newhisthist trace
        | (trace--->trace) $ False
          = error "shouldn't happen"
        f newhisthist (Trace stricts rule answer history (Reduce reductroot trace))
        | isEmpty pclosed && superset popen ropen
          = f (newhist`,newhist`) trace
            where rargs = arguments rule; rroot = ruleroot rule; rgraph = rulegraph rule
                  (pclosed,popen) = graphvars rgraph rargs
                  (_,ropen) = graphvars rgraph [rroot]
                  newhist` = [(rroot,rgraph):newhist]
                  (newhist,hist) = newhisthist
        f newhisthist (Trace stricts rule answer history (Annotate trace))
        | isEmpty pclosed && superset popen ropen
          = f (newhist`,hist) trace
            where rargs = arguments rule; rroot = ruleroot rule; rgraph = rulegraph rule
                  (pclosed,popen) = graphvars rgraph rargs
                  (_,ropen) = graphvars rgraph [rroot]
                  newhist` = [(rroot,rgraph):newhist]
                  (newhist,hist) = newhisthist
        f newhisthist (Trace stricts rule answer history transf)
        = foldtips foldarea (fnsymbol,arguments rule) (removeDup newhist`,removeDup hist) (Trace stricts rule answer history transf)
          where rroot = ruleroot rule; rgraph = rulegraph rule
                newhist` = [(rroot,rgraph):newhist]
                (newhist,hist) = newhisthist


/*
`Foldtips foldarea foldcont hist trace' folds all occurrences of (rooted
graphs  in  hist)  in the tips of the trace. It returns a list of rules,
which are the results  of  folding,  and  a  list  of  areas  for  which
functions  must  be  introduced. If no occurrences were found, Absent is
returned.
*/

foldtips ::
    ((Rgraph sym var)->(sym,[var]))
    (sym,[var])
 -> ([(var,Graph sym var)],[(var,Graph sym var)])
    (Trace sym var pvar)
 -> (Bool,([Bool],FuncBody sym var,[Rgraph sym var]))
 |  == sym
 &  == var
 &  == pvar

foldtips foldarea foldcont
= ft
  where ft hist trace
        = case transf
          of Stop
              -> foldoptional exres (pair True o addstrict stricts o mapfst rule2body) (actualfold deltanodes rnfnodes foldarea (==) foldcont (snd hist) rule)
                 where deltanodes = foldoptional [] getdeltanodes answer
                       rnfnodes = foldoptional [ruleroot rule] (const []) answer
             Instantiate ipattern yestrace notrace
              -> ft` (ft hist yestrace) (ft hist notrace)
                 where ft` (False,yessra) (False,nosra) = exres
                       ft` (yesfound,(yesstricts,yesbody,yesareas)) (nofound,(nostricts,nobody,noareas))
                       = (True,(stricts,MatchPattern ipattern yesbody nobody,yesareas++noareas))
             Reduce reductroot trace
              -> ft` (ft (fst hist,fst hist) trace)
                 where ft` (False,sra) = exres
                       ft` (found,sra) = (True,sra)
             Annotate trace
              -> ft` (ft hist trace)
                 where ft` (False,sra) = exres
                       ft` (found,sra) = (True,sra)
          where (Trace stricts rule answer _ transf) = trace
                exres = (False,newextract noetrc foldarea trace)

rule2body rule = buildgraph (arguments rule) (ruleroot rule) (rulegraph rule)

addstrict stricts (body,areas) = (stricts,body,areas)

noetrc trace area = id

pair x y = (x,y)

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
*/

:: Etracer sym var pvar :==
       (Trace sym var pvar)
       (Rgraph sym var)
       Bool
    -> Bool

newextract ::
    (Etracer sym var pvar)
    ((Rgraph sym var)->(sym,[var]))
    (Trace sym var pvar)
 -> ([Bool],FuncBody sym var,[Rgraph sym var])
 |  == sym
 &  == var
 &  == pvar

newextract trc newname (Trace stricts rule answer history transf)
| recursive
  = (stricts,rule2body recrule,recareas)
= case transf
  of Reduce reductroot trace
      -> newextract trc newname trace
     Annotate trace
      -> newextract trc newname trace
     Instantiate ipattern yestrace notrace
      -> (stricts,MatchPattern ipattern yesbody nobody,yesareas++noareas)
         where (_,yesbody,yesareas) = newextract trc newname yestrace
               (_,nobody,noareas) = newextract trc newname notrace
     Stop
      -> (stricts,buildgraph rargs rroot stoprgraph,stopareas)

  where (recursive,unsafearea)
        = if (isreduce transf)
             (foldoptional (False,dummycontents) (findspinepart rule transf) answer)
             (False,abort "newextract: not a Reduce transformation")
        dummycontents = abort "newfold: newextract: accessing dummy node contents"

        (recrule,recareas) = splitrule newname rnfnodes deltanodes rule unsafearea
        (stoprgraph,stopareas) = finishfold newname rnfnodes deltanodes rroot rgraph

        rargs = arguments rule; rroot = ruleroot rule; rgraph = rulegraph rule
        rnfnodes = foldoptional (cons rroot) (const id) answer (varlist rgraph rargs)

        deltanodes = foldoptional [] getdeltanodes answer

buildgraph ::
    [var]
    var
    (Graph sym var)
 -> FuncBody sym var | == var
buildgraph args root graph
= BuildGraph (mkrgraph root (compilegraph (map (pairwith (snd o varcontents graph)) newnodes)))
  where newnodes = closedreplnodes--patnodes
        closedreplnodes = fst (graphvars graph [root])
        patnodes = varlist graph args

isreduce (Reduce reductroot trace) = True
isreduce transf = False


/*
`Findspinepart toprule rule spine (transformation,trace)' is a pair with
a  boolean  determining whether some instance of the `spine', determined
using `toprule', occurs in a residu of itself in `trace'.

The use of `findspinepart' is to detect introduced recursion in  `trace'
to its root.
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
        partial rule matching _ pr
        = (extgraph` graph rule matching pattern,recursion)
          where (pattern,recursion) = pr
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

findpattern pattern thespinenodes residuroot (Instantiate ipattern yestrace notrace)
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

instance <<< (FuncBody sym var) | toString sym & ==,toString var
where (<<<) file (MatchPattern pat yesbody nobody)
      = file <<< "?Match: " /* <<< toString (rgraphroot pat) <<< " =?= " */ <<< pat <<< nl
             <<< "Match succes:" <<< nl
             <<< yesbody
             <<< "Match failure:" <<< nl
             <<< nobody
      (<<<) file (BuildGraph rgraph)
      = file <<< "Build: " <<< toString rgraph <<< nl

printfuncdef :: (sym->String) (var->String) (FuncDef sym var) *File -> .File | == var
printfuncdef showsym showvar funcdef file
= printfuncbody showsym showvar "" body (file <<< "Arguments: " <<< showlist showvar args <<< nl)
  where (args,body) = funcdef

printfuncbody :: (sym->String) (var->String) String (FuncBody sym var) *File -> .File | == var
printfuncbody showsym showvar indent (MatchPattern pattern yesbody nobody) file0
= file3
  where file3 = printfuncbody showsym showvar indent nobody (file2 <<< indent <<< "Otherwise:" <<< nl)
        file2 = printfuncbody showsym showvar (indent+++"    ") yesbody file1
        file1 = file0 <<< indent <<< "Match " <<< showvar (rgraphroot pattern) <<< " =?= " <<< showrgraph showsym showvar pattern <<< nl
printfuncbody showsym showvar indent (BuildGraph replacement) file0
= file1
  where file1 = file0 <<< indent <<< showrgraph showsym showvar replacement <<< nl
