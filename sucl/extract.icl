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

>   actualfold ::
>       [**] ->
>       [**] ->
>       (rgraph * **->(*,[**])) ->
>       (***->**->bool) ->
>       (*,[***]) ->
>       [(***,graph * ***)] ->
>       rule * ** ->
>       optional (rule * **,[rgraph * **])

>   actualfold deltanodes rnfnodes foldarea self foldcont hist rule
>   =   Absent, if list3=[]
>   =   Present (mkrule rargs rroot rgraph'',areas'), otherwise
>       where rargs = lhs rule; rroot = rhs rule; rgraph = rulegraph rule

>             list2 = map (pairwith (findoccs hist rule)) (nodelist rgraph [rroot]--nodelist rgraph rargs)
>             ||  list2: list combining every node with list of every instantiable history graph

>             list3 = [(rnode,hgraph,mapping)|(rnode,(((hroot,hgraph),mapping):rest))<-list2]
>             ||  list3: list combining every instantiable node with first instantiable history graph

>             rgraph'
>             =   foldr foldrec rgraph list3
>                 where foldrec (rnode,hgraph,mapping) = updategraph rnode (mapsnd (map (lookup mapping)) foldcont)

>             (rgraph'',areas') = finishfold foldarea fixednodes singlenodes rroot rgraph'
>             fixednodes = intersect (mkset (argnodes++foldednodes++rnfnodes)) (nodelist rgraph' [rroot])
>             singlenodes = intersect deltanodes (nodelist rgraph' [rroot])
>             argnodes = nodelist rgraph' rargs
>             foldednodes = map fst3 list3

>   findoccs
>   ::  [(***,graph * ***)] ->
>       rule * ** ->
>       ** ->
>       [((***,graph * ***),[(***,**)])]

>   findoccs hist rule rnode
>   =   [   ((hroot,hgraph),mapping)
>       |   ((hroot,hgraph),(seen,mapping,[]))<-list1 ||  Find instantiable history rgraphs...
>       ;   unshared rnode (hroot,hgraph) mapping     ||  ...which don't have shared contents...
>||     ;   ~self hroot rnode                         ||  ...and aren't the history graph itself
>       ]
>       where rargs = lhs rule; rroot = rhs rule; rgraph = rulegraph rule
>             list1
>             =   [((hroot,hgraph),inst (hroot,hgraph))|(hroot,hgraph)<-hist]
>                 where inst (hroot,hgraph)
>                       =   instantiate (hgraph,rgraph) (hroot,rnode) ([],[],[])
>             ||  list1: all instantiation attempts at rnode with the history rgraphs

>             unshared rnode (hroot,hgraph) mapping
>             =   disjoint inner outer
>                 where inner = map (lookup mapping) (fst (nodeset hgraph [hroot]))
>                       outer = nodelist (prunegraph rnode rgraph) (rroot:rargs)--[rnode]

------------------------------------------------------------------------


Splitting a rule into areas to fold to a certain area

>   splitrule
>   ::  (rgraph * **->(*,[**])) ->
>       [**] ->
>       [**] ->
>       rule * ** ->
>       rgraph * ** ->
>       (rule * **,[rgraph * **])

>   splitrule fold rnfnodes deltanodes rule area
>   =   (mkrule rargs rroot rgraph'',area':areas)
>       where

>             rargs = lhs rule; rroot = rhs rule; rgraph = rulegraph rule
>             aroot = rgraphroot area; agraph = rgraphgraph area

>             (rgraph'',areas) = finishfold fold fixednodes deltanodes rroot rgraph'
>             fixednodes = intersect (mkset (aroot:nodelist rgraph' rargs++rnfnodes)) (nodelist rgraph' [rroot])
>             rgraph' = updategraph aroot (fold area') rgraph
>             area' = mkrgraph aroot agraph'
>             agraph' = foldr addnode emptygraph ins
>             ins = nodelist agraph [aroot]--outs
>             outs = nodelist (prunegraph aroot rgraph) (rroot:rargs++snd (nodeset agraph [aroot]))--[aroot]

>             addnode node = updategraph node (snd (dnc (const "in splitrule") rgraph node))

------------------------------------------------------------


`Finishfold foldarea fixednodes root graph' finishes folding of a  graph
by  introducing  areas for parts of the graph that are not fixed in some
way (e.g. when part of the pattern  of  the  rule,  already  folded,  or
bearing a delta function symbol).

>   finishfold
>   ::  (rgraph * **->(*,[**])) ->
>       [**] ->
>       [**] ->
>       ** ->
>       graph * ** ->
>       (graph * **,[rgraph * **])

>   finishfold foldarea fixednodes singlenodes root graph
>   =   (graph',areas)
>       where graph' = foldr foldarea' graph areas
>             foldarea' area = updategraph (rgraphroot area) (foldarea area)
>             areas = depthfirst generate process arearoots
>             process aroot
>             =   mkrgraph aroot (foldr addnode emptygraph ins)
>                 where outs_and_aroot = nodelist (prunegraph aroot graph) arearoots++fixednodes
>                       ins = aroot:nodelist graph [aroot]--outs_and_aroot
>             generate area
>             =   snd (nodeset agraph [aroot])--fixednodes
>                 where aroot = rgraphroot area; agraph = rgraphgraph area
>             arearoots = mkset (root:singlenodes++singfixargs)--fixednodes
>             singfixargs = concat (map arguments (singlenodes++fixednodes))

>             arguments node
>             =   args, if def
>             =   [], otherwise
>                 where (def,(sym,args)) = dnc (const "in finishfold/1") graph node

>             addnode node
>             =   updategraph node cnt, if def
>             =   id, otherwise
>                 where (def,cnt) = dnc (const "in finishfold/2") graph node
