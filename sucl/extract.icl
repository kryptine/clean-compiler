implementation module extract

// $Id$

import rule
import dnc
import graph
import basic
from general import Yes,No
import StdEnv

/*

extract.lit - Folding of subject graphs
=======================================

Description
-----------

This module defines functions that can fold subject graphs, as they are
usually found at the tips of the trace of a symbolic reduction process.

Three versions are provided; `actualfold' for folding initiated by
autorecursion, `splitrule' for folding initiated by introduced recursion
and `finishfold' for folding initiated without recursion.

------------------------------------------------------------

Interface
---------

Exported identifiers:

>   %export
>       actualfold    ||  Fold subject graph according to autorecursion
>       splitrule     ||  Fold subject graph according to introduced recursion
>       finishfold    ||  Finish folding by introducing areas

------------------------------------------------------------

Includes
--------

>   %include "dnc.lit"

>   %include "../src/basic.lit"
>   %include "../src/pfun.lit"
>   %include "../src/graph.lit"
>   %include "../src/rule.lit"

------------------------------------------------------------

Implementation
--------------

`Actualfold  foldarea   foldcont   hist   rule'   is   the   result   of
folding occurrences of areas in `hist' to `foldcont', and introducing new
areas for parts that aren't folded.

`Self' determines whether an instance of a history graph is the  history
graph itself. We don't want to fold back something we unfolded earlier!
*/

actualfold ::
    [var]
    [var]
    ((Rgraph sym var)->Node sym var)
    (pvar->var->bool)
    (sym,[pvar])
    [(pvar,Graph sym pvar)]
    (Rule sym var)
 -> Optional (Rule sym var,[Rgraph sym var])
 |  == sym
 &  == var
 &  == pvar

actualfold deltanodes rnfnodes foldarea self foldcont hist rule
| isEmpty list3
  = No
= Yes (mkrule rargs rroot rgraph``,areas`)
  where rargs = arguments rule; rroot = ruleroot rule; rgraph = rulegraph rule

        list2 = map (pairwith (findoccs hist rule)) (varlist rgraph [rroot]--varlist rgraph rargs)
        // list2: list combining every node with list of every instantiable history graph

        list3 = [(rnode,mapping) \\ (rnode,[mapping:_])<-list2]
        // list3: list combining every instantiable node with first instantiable history graph

        rgraph`
        = foldr foldrec rgraph list3
          where foldrec (rnode,mapping) = updategraph rnode (mapsnd (map (lookup mapping)) foldcont)

        (rgraph``,areas`) = finishfold foldarea fixednodes singlenodes rroot rgraph`
        fixednodes = intersect (removeDup (argnodes++foldednodes++rnfnodes)) (varlist rgraph` [rroot])
        singlenodes = intersect deltanodes (varlist rgraph` [rroot])
        argnodes = varlist rgraph` rargs
        foldednodes = map fst list3

findoccs ::
    [(pvar,Graph sym pvar)]
    (Rule sym var)
    var
 -> [[(pvar,var)]]
 |  == sym
 &  == var
 &  == pvar

findoccs hist rule rnode
= [  mapping
  \\ ((hroot,hgraph),(seen,mapping,[]))<-list1 // Find instantiable history rgraphs...
  |  unshared rnode (hroot,hgraph) mapping     // ...which don't have shared contents
  ]
  where rargs = arguments rule; rroot = ruleroot rule; rgraph = rulegraph rule
        list1
        = [((hroot,hgraph),inst (hroot,hgraph))\\(hroot,hgraph)<-hist]
          where inst (hroot,hgraph)
                = instantiate (hgraph,rgraph) (hroot,rnode) ([],[],[])
        // list1: all instantiation attempts at rnode with the history rgraphs

        unshared rnode (hroot,hgraph) mapping
        = disjoint inner outer
          where inner = map (lookup mapping) (fst (graphvars hgraph [hroot]))
                outer = varlist (prunegraph rnode rgraph) [rroot:rargs]--[rnode]

/*
------------------------------------------------------------------------


Splitting a rule into areas to fold to a certain area
*/

splitrule ::
    ((Rgraph sym var)->Node sym var)
    [var]
    [var]
    (Rule sym var)
    (Rgraph sym var)
 -> (Rule sym var,[Rgraph sym var])
 |  == var

splitrule fold rnfnodes deltanodes rule area
= (mkrule rargs rroot rgraph``,[area`:areas])
  where rargs = arguments rule; rroot = ruleroot rule; rgraph = rulegraph rule
        aroot = rgraphroot area; agraph = rgraphgraph area

        (rgraph``,areas) = finishfold fold fixednodes deltanodes rroot rgraph`
        fixednodes = intersect (removeDup [aroot:varlist rgraph` rargs++rnfnodes]) (varlist rgraph` [rroot])
        rgraph` = updategraph aroot (fold area`) rgraph
        area` = mkrgraph aroot agraph`
        agraph` = foldr addnode emptygraph ins
        ins = varlist agraph [aroot]--outs
        outs = varlist (prunegraph aroot rgraph) [rroot:rargs++snd (graphvars agraph [aroot])]--[aroot]

        addnode node = updategraph node (snd (dnc (const "in splitrule") rgraph node))

/*
------------------------------------------------------------


`Finishfold foldarea fixednodes root graph' finishes folding of a  graph
by  introducing  areas for parts of the graph that are not fixed in some
way (e.g. when part of the pattern  of  the  rule,  already  folded,  or
bearing a delta function symbol).
*/

finishfold ::
    ((Rgraph sym var)->Node sym var)
    [var]
    [var]
    var
    (Graph sym var)
 -> (Graph sym var,[Rgraph sym var])
 |  == var

finishfold foldarea fixednodes singlenodes root graph
= (graph`,areas)
  where graph` = foldr foldarea` graph areas
        foldarea` area = updategraph (rgraphroot area) (foldarea area)
        areas = depthfirst generate process arearoots
        process aroot
        = mkrgraph aroot (foldr addnode emptygraph ins)
          where outs_and_aroot = varlist (prunegraph aroot graph) arearoots++fixednodes
                ins = [aroot:varlist graph [aroot]--outs_and_aroot]
        generate area
        = snd (graphvars agraph [aroot])--fixednodes
          where aroot = rgraphroot area; agraph = rgraphgraph area
        arearoots = removeDup [root:singlenodes++singfixargs]--fixednodes
        singfixargs = flatten (map arguments (singlenodes++fixednodes))

        arguments node
        = if def args []
          where (def,(_,args)) = dnc (const "in finishfold/1") graph node

        addnode node
        = if def (updategraph node cnt) id
          where (def,cnt) = dnc (const "in finishfold/2") graph node
