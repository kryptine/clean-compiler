implementation module canon

// $Id$

import rule
import graph
import basic
import general
import StdEnv

/*

canon.lit - Area canonicalization
=================================

Description
-----------

This script defines functions for folding areas and generating canonical
forms from them for renewed symbolic reduction.

------------------------------------------------------------------------

Interface
---------

Exported identifiers:

>   %export
>       canonise  ||  Transform an area into canonical form
>       foldarea  ||  Fold an area to an application of its assigned symbol
>       labelarea ||  Use a list of symbols to label a list of areas

------------------------------------------------------------------------

Includes
--------

>   %include "basic.lit" -uncurry -split
>   %include "graph.lit" -extgraph
>   %include "rule.lit"

------------------------------------------------------------------------

`Canonise heap' canonises an area to a  standard  form,  so  that  equal
areas  are  detected by the `=' operator.  Canonisation is done in three
steps:

(1) Splitting arguments to prevent too much sharing and  allowing  delta
    functions to be recognised.

(2) Adding extra arguments to the full complement according to the  type
    rule for the top symbol.

(3) Relabeling the nodes in a standard way.

>   canonise :: (*->rule **** *****) -> [***] -> rgraph * ** -> rgraph * ***
>   canonise typerule heap = relabel heap.etaexpand typerule.splitrg.relabel localheap

*/

canonise :: (sym -> Int) [var2] (Rgraph sym var1) -> Rgraph sym var2 | == var1
canonise arity heap rg
 = ((relabel heap o etaexpand arity o splitrg o relabel localheap) rg <--- "canon.canonise ends") ---> "canon.canonise begins"

/*

>   split :: rgraph * num -> rgraph * num
>   split rgraph
>   =   foldsingleton single rgraph rgraph
>       where single root sym args = mkrgraph root (updategraph root (sym,fst (claim args (localheap--[root]))) emptygraph)

*/

splitrg :: (Rgraph sym Int) -> Rgraph sym Int
splitrg rgraph
 = foldsingleton single rgraph rgraph
   where single root sym args = mkrgraph root (updategraph root (sym,fst ((claim--->"basic.claim begins from canon.splitrg") args (localheap--[root]))) emptygraph)

/*
>   uncurry :: (*->rule **** *****) -> rgraph * num -> rgraph * num
>   uncurry typerule rgraph
>   =   f (nc root)
>       where f (True,(sym,args))
>             =   mkrgraph root (updategraph root (sym,fst ((claim--->"basic.claim begins from canon.uncurry") targs (args++localheap--nodelist graph [root]))) graph)
>                 where targs = lhs (typerule sym)
>             f cont = rgraph
>             nc = nodecontents graph
>             root = rgraphroot rgraph; graph = rgraphgraph rgraph
*/

etaexpand :: (sym->Int) (Rgraph sym Int) -> Rgraph sym Int
etaexpand arity rgraph
 = f (nc root)
   where f (True,(sym,args))
          = mkrgraph root (updategraph root (sym,take (arity sym) (args++(localheap--(varlist graph [root])))) graph)
         f cont = rgraph
         nc = varcontents graph
         root = rgraphroot rgraph; graph = rgraphgraph rgraph

localheap :: [Int]
localheap =: [0..]

/*
------------------------------------------------------------------------

>   foldarea :: (rgraph * **->*) -> rgraph * ** -> (*,[**])
>   foldarea label rgraph
>   =   (label rgraph,foldsingleton single nosingle rgraph)
>       where single root sym args = args
>             nosingle = snd (varset (rgraphgraph rgraph) [rgraphroot rgraph])
*/

foldarea :: ((Rgraph sym var) -> sym) (Rgraph sym var) -> Node sym var | == var
foldarea label rgraph
 = (((labelrgraph<---"canon.foldarea.labelrgraph begins")--->"canon.foldarea.labelrgraph ends",(foldsingleton single nosingle rgraph<---"canon.foldarea.foldsingleton ends")--->"canon.foldarea.foldsingleton begins") <--- "canon.foldarea ends") ---> "canon.foldarea begins"
   where single root sym args = map (\arg->(arg<---"canon.foldarea.single.arg ends")--->"canon.foldarea.single.arg begins") args
         nosingle = map (\arg->(arg<---"newfold.foldarea.nosingle.arg ends")--->"newfold.foldarea.nosingle.arg begins") (snd (graphvars (rgraphgraph rgraph) [rgraphroot rgraph]))
         labelrgraph = (label rgraph <--- "canon.foldarea.labelrgraph ends") ---> "canon.foldarea.labelrgraph begins"

/*
------------------------------------------------------------------------

>   labelarea :: [rgraph * **] -> [*] -> rgraph * ** -> *
>   labelarea areas labels
>   =   foldmap id nolabel (maketable areas labels)
>       where nolabel = error "labelarea: no label assigned to area"

>   maketable :: [rgraph * **] -> [*] -> [(rgraph * **,*)]
>   maketable [] = const []
>   maketable (area:areas) labels
>   =   (area,label):maketable areas labels'
>       where (label,labels') = getlabel (nc aroot) labels
>             getlabel (True,(asym,aargs)) labels = (asym,labels), if ~or (map (fst.nc) aargs)
>             getlabel acont (label:labels) = (label,labels)
>             getlabel = error "maketable: out of labels"
>             nc = varcontents agraph
>             aroot = rgraphroot area; agraph = rgraphgraph area
*/

labelarea :: (sym->Bool) [Rgraph sym var] [sym] (Rgraph sym var) -> sym | == sym & == var
labelarea reusable areas labels rg
 = ((foldmap--->"canon.labelarea uses foldmap") id nolabel ((maketable--->"canon.maketable begins from canon.labelarea") reusable ((areas<---"canon.labelarea.areas ends")--->"canon.labelarea.areas begins") ((labels<---"canon.labelarea.labels ends")--->"canon.labelarea.labels begins")) ((rg<---"canon.labelarea.rg ends")--->"canon.labelarea.rg begins") <--- "canon.labelarea ends") ---> "canon.labelarea begins"
   where nolabel = abort "canon: labelarea: no label assigned to area"

maketable :: (sym->Bool) [Rgraph sym var] [sym] -> [(Rgraph sym var,sym)] | == var
maketable _ [] _ = [] <--- "canon.maketable ends empty"
maketable reusable [area:areas] labels
 = [(((area<---"canon.maketable.area ends")--->"canon.maketable.area begins",(label<---"canon.maketable.label ends")--->"canon.maketable.label begins") <--- "canon.maketable.head ends") ---> "canon.maketable.head begins":(maketable--->"canon.maketable begins from maketable") reusable areas labels`] <--- "canon.maketable ends nonempty"
   where (label,labels`) = getlabel (nc aroot) labels
         getlabel (True,(asym,aargs)) labels
          | reusable asym && not (or (map (fst o nc) aargs))
            = (asym,labels)
         getlabel acont [label:labels]
          = (label,labels)
         getlabel _ _
          = abort "canon: maketable: out of labels"
         nc = varcontents agraph
         aroot = rgraphroot area; agraph = rgraphgraph area

/*
------------------------------------------------------------------------

>   relabel :: [***] -> rgraph * ** -> rgraph * ***

>   relabel heap rgraph
>   =   mkrgraph (move root) graph'
>       where root = rgraphroot rgraph; graph = rgraphgraph rgraph
>             nodes = nodelist graph [root]
>             table = zip2 nodes heap
>             move = foldmap id nonew table
>             nonew = error "relabel: no new node assigned to node"
>             graph' = foldr addnode emptygraph table
>             addnode (node,node')
>             =   updategraph node' (sym,map move args), if def
>             =   id, otherwise
>                 where (def,(sym,args)) = nc node
>             nc = nodecontents graph
*/

relabel :: [var2] (Rgraph sym var1) -> Rgraph sym var2 | == var1
relabel heap rgraph
 = mkrgraph (move root) graph`
   where root = rgraphroot rgraph; graph = rgraphgraph rgraph
         nodes = varlist graph [root]
         table = zip2 nodes heap
         move = foldmap id nonew table
         nonew = abort "relabel: no new node assigned to node"
         graph` = foldr addnode emptygraph table
         addnode (node,node`)
          | def
            = updategraph node` (sym,map move args)
          = id
            where (def,(sym,args)) = nc node
         nc = varcontents graph

/*
>   foldsingleton
>   ::  (**->*->[**]->***) ->
>       *** ->
>       rgraph * ** ->
>       ***

>   foldsingleton single nosingle rgraph
>   =   f (nc root)
>       where f (True,(sym,args)) = single root sym args, if ~or (map (fst.nc) args)
>             f cont = nosingle
>             nc = nodecontents graph
>             root = rgraphroot rgraph; graph = rgraphgraph rgraph
*/

foldsingleton ::
    (var sym [var] -> pvar)
    pvar
    (Rgraph sym var)
 -> pvar
 |  == var

foldsingleton single nosingle rgraph
 = case nc root
   of (True,(sym,args))
       | not (or (map (fst o nc) args))
         -> single root sym args
      _
       -> nosingle
   where nc = varcontents graph
         root = rgraphroot rgraph; graph = rgraphgraph rgraph
