implementation module trd

// $Id$

import rule
import graph
import basic
import StdEnv

/*

trd.lit - Type rule derivation
==============================

Description
-----------

This module defines the derivation of a type rule from a given rule.

------------------------------------------------------------

Interface
---------

Exported identifiers:

>   %export
>       ruletype  ||  Derive a type rule from a rule

------------------------------------------------------------

Includes
--------

>   %include "basic.lit"
>   %include "pfun.lit"
>   %include "graph.lit"
>   %include "rule.lit"

Naming conventions:

    *      - symbol (sym)
    **     - node (node)
    ***    - type symbol (tsym)
    ****   - type node in type rule to build (tnode)
    *****  - type node in given type rules (trnode)

------------------------------------------------------------

Implementation
--------------

`Ruletype' determines the type of a rule.

First, for every closed node, its type rule  is  copied  into  a  global
(initially  unconnected) type graph, and for every open node, a distinct
type node is allocated in the same type graph.  Then  for  every  closed
node n and argument n-i, the result type of n-i is unified with the i-th
argument type of n.

>   ruletype
>   ::  [****] ->
>       ((*,[**])->rule *** *****) ->
>       rule * ** ->
>       rule *** ****

>   ruletype theap typerule rule
>   =   foldr (buildtype typerule graph) bcont nodes theap emptygraph []
>       where args = lhs rule; root = rhs rule; graph = rulegraph rule
>             nodes = nodelist graph (root:args)
>             bcont theap tgraph assignment
>             =   foldr sharepair spcont pairs id tgraph assignment
>                 where pairs = mkpairs assignment
>             spcont redirection tgraph assignment
>             =   mkrule (map lookup args) (lookup root) tgraph
>                 where lookup = redirection.foldmap id notype assignment
>             notype = error "ruletype: no type node assigned to node"

*/

ruletype
 :: .[tvar]
    ((Node sym var) -> .Rule tsym trvar)
    .(Rule sym var)
 -> .Rule tsym tvar
 |  == var
 &  == tsym
 &  == tvar
 &  == trvar

ruletype theap typerule rule
= foldr (buildtype typerule graph) bcont nodes theap emptygraph []
  where args = arguments rule
        root = ruleroot rule
        graph = rulegraph rule
        nodes = varlist graph [root:args]
        bcont theap tgraph assignment
        = foldr sharepair spcont pairs id tgraph assignment
          where pairs = mkpairs assignment
        spcont redirection tgraph assignment
        = mkrule (map lookup args) (lookup root) tgraph
          where lookup = redirection o (foldmap id notype assignment)
        notype = abort "ruletype: no type node assigned to node"

/*

`Buildtype' builds the part of the global type graph corresponding to  a
node.   For  a closed node, the type rule is copied; for an open node, a
single type node is allocated.  Track is kept of which type  nodes  have
been assigned to the node and its arguments.

*/

buildtype
 :: .((Node sym var) -> .Rule tsym trvar)                                       // Assignement of type rules to symbols
    .(Graph sym var)                                                            // Graph to which to apply typing
    var                                                                         // ???
    .([tvar] -> .(z:(Graph tsym tvar) -> .(x:[y:(var,tvar)] -> .result)))       // Continuation
    .[tvar]                                                                     // Type heap
    w:(Graph tsym tvar)                                                         // Type graph build so far
    u:[v:(var,tvar)]                                                            // Assignment of type variables to variables
 -> .result                                                                     // Final result
 |  == var
 &  == trvar
 ,  [u<=x,v<=y,w<=z]

buildtype typerule graph node bcont theap tgraph assignment
| def
= bcont theap` tgraph` assignment`
= bcont (tl theap) tgraph [(node,hd theap):assignment]
  where (def,cont) = varcontents graph node
        (_,args) = cont
        trule = typerule cont
        trargs = arguments trule; trroot = ruleroot trule; trgraph = rulegraph trule
        trnodes = varlist trgraph [trroot:trargs]
        (tnodes,theap`) = claim trnodes theap
        matching = zip2 trnodes tnodes
        tgraph` = foldr addnode tgraph matching
        addnode (trnode,tnode)
        | trdef
        = updategraph tnode (mapsnd (map match) trcont)
        = id
          where (trdef,trcont) = varcontents trgraph trnode
        match = foldmap id nomatch matching
        nomatch = abort "buildtype: no match from type rule node to type node"
        assignment` = zip2 [node:args] (map match [trroot:trargs])++assignment

sharepair
 :: (.var,.var)                                    // Variables to share
    w:((.var->var2) -> v:(x:(Graph sym var2) -> .result))       // Continuation
    (.var->var2)                                   // Redirection
    u:(Graph sym var2)                              // Graph before redirection
 -> .result                  // Final result
 |  == sym
 &  == var2
 ,  [u<=x,v<=w]

sharepair lrnode spcont redirection graph
= share (mappair redirection redirection lrnode) spcont redirection graph

/*

`Share' shares two nodes in a graph by redirecting all  references  from
one  to the other, and sharing the arguments recursively.  The resulting
redirection function is also returned.

*/
/*
share ::
   (var,var)                                    // Variables to share
   ((var->var) (Graph sym var) -> result)       // Continuation
   (var->var)                                   // Redirection
   (Graph sym var)                              // Graph before redirection
   -> result | == sym & == var                  // Final result
*/
share lrnode scont redirect graph
| lnode==rnode
= scont redirect graph
| ldef && rdef
= foldr share scont lrargs redirect` graph`
= scont redirect` graph`
  where (lnode,rnode) = lrnode
        (ldef,(lsym,largs)) = varcontents graph lnode
        (rdef,(rsym,rargs)) = varcontents graph rnode
        lrargs
        | lsym<>rsym
        = abort "share: incompatible symbols"
        | not (eqlen largs rargs)
        = abort "share: incompatible arities"
        = zip2 (redargs largs) (redargs rargs)
        redargs = map adjustone
        redirect` = adjustone o redirect
        adjustone
        | ldef
        = adjust rnode lnode id
        = adjust lnode rnode id
        graph` = redirectgraph adjustone graph
/*
mkpairs :: [(var1,var2)] -> [(var2,var2)] | == var1
*/
mkpairs pairs
= f (map snd (partition fst snd pairs))
  where f [[x1,x2:xs]:xss] = [(x1,x2):f [[x2:xs]:xss]]
        f [xs:xss] = f xss
        f [] = []
