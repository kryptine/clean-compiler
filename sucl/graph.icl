implementation module graph

// $Id$

import pfun
import basic
import general
import StdEnv

/*

graph.lit - Unrooted graphs
===========================

Description
-----------

This script implements an abstract type for unrooted graphs  and  useful
functions to manipulate them.

*/

// A mapping from variables to nodes (unrooted)
:: Graph sym var
    = GraphAlias !(Pfun var (Node sym var))

// A node, bearing the contents of a variable
:: Node sym var
   :== (sym,[var])

// ==> Symbols and variables are going to be defined in different modules.
//     They're here now because I don't want to throw them away.
:: Symbol
   = Apply              // Unwritten expression application
   | Cons               // Non-empty list
   | Nil                // Empty list
   | Int Int            // A specified integer
   | Char Char          // A specified character
   | User String String // A user-supplied symbol
   | Tuple Int          // A tuple symbol of specified arity
   | Select Int Int     // A tuple selection operator of specified arity and index
   | If                 // Predefined IF function
   | Bool Bool          // A specified boolean
// | MkRecord [Field]   // Record construction?
// | GetField [Field] Field // Record field selection?

:: Variable
   = Named String  // Variable was named in the program
   | Anonymous Int // Implicit variable

/*

>   emptygraph    = emptypfun
>   updategraph   = extend
>   prunegraph    = restrict
>   restrictgraph = domres
>   redirectgraph = postcomp.mapsnd.map
>   overwritegraph = overwrite
>   showgraph showfunc shownode = showpfun shownode (showpair showfunc (showlist shownode))
*/

// The empty set of bindings
emptygraph :: Graph .sym .var
emptygraph = GraphAlias emptypfun

updategraph :: var .(Node sym var) !.(Graph sym var) -> .Graph sym var
updategraph var node graph = mapgraph (extend var node) graph

prunegraph :: var !.(Graph sym var) -> .Graph sym var
prunegraph var graph = mapgraph (restrict var) graph

restrictgraph :: .[var] .(Graph sym var) -> .Graph sym var | == var
restrictgraph vars graph = mapgraph (domres vars) graph

redirectgraph :: (var->var) !.(Graph sym var) -> .Graph sym var
redirectgraph redirection graph
= mapgraph (postcomp (mapsnd (map redirection))) graph

overwritegraph :: !.(Graph sym var) !.(Graph sym var) -> .Graph sym var
overwritegraph (GraphAlias newpf) oldgraph = mapgraph (overwrite newpf) oldgraph

movegraph :: (var1->var2) !.[var1] .(Graph sym var1) -> .Graph sym var2 | == var1
movegraph movevar varspace oldgraph
= foldr addvar emptygraph varspace
  where addvar var
        | def
        = updategraph (movevar var) (sym,map movevar args)
        = id
          where (def,(sym,args)) = varcontents oldgraph var

varcontents :: !.(Graph sym var) var -> (.Bool,Node sym var) | == var
varcontents (GraphAlias pfun) v
= (total (False,(nosym,noargs)) o postcomp found) pfun v
  where found x = (True,x)
        nosym = abort "varcontents: getting symbol of free variable"
        noargs = abort "varcontents: getting arguments of free variable"

graphvars :: .(Graph sym var) !.[var] -> (.[var],.[var]) | == var
graphvars graph roots
= (graphvars` [] graph roots<---"graph.graphvars ends")--->"graph.graphvars begins"

// Finds bound and free variables in a graph
// Excludes the variables only reachable through "prune"
graphvars` :: .[var] .(Graph sym var) .[var] -> (.[var],.[var]) | == var
graphvars` prune graph roots
= (snd (foldlr (ns--->"graph.graphvars`.ns begins from graph.graphvars`") (prune,([],[])) roots)<---"graph.graphvars` ends")--->"graph.graphvars` begins"
  where ns var seenboundfree
        | isMember var seen = seenboundfree<---"graph.graphvars`.ns ends (already seen)"
        | not def           = ([var:seen],(bound,[var:free]))<---"graph.graphvars`.ns ends (open variable)"
                            = (seen`,([var:bound`],free`))<---"graph.graphvars`.ns ends (closed variable)"
          where (seen`,(bound`,free`)) = foldlr (ns--->"graph.graphvars`.ns begins from graph.graphvars`.ns") ([var:seen],boundfree) args
                (def,(_,args)) = varcontents graph var
                (seen,boundfree=:(bound,free)) = seenboundfree
varlist :: .(Graph sym var) !.[var] -> .[var] | == var
varlist graph roots
= depthfirst arguments id roots
  where arguments var
        | def = args
              = []
          where (def,(_,args)) = varcontents graph var

/*
>   prefix graph without nodes
>   =   foldlr f (without,[]) nodes
>       where f node (seen,nodes)
>             =   (seen,nodes), if member seen node
>             =   (seen',node:nodes'), otherwise
>                 where (seen',nodes')
>                       =   (node:seen,nodes), if ~def
>                       =   foldlr f (node:seen,nodes) args, otherwise
>                       (def,(sym,args)) = nodecontents graph node
*/
prefix :: .(Graph sym var) .[var] !.[var] -> .([var],[var]) | == var
prefix graph without vars
= foldlr f (without,[]) vars
  where f var (seen,vars)
        | isMember var seen = (seen,vars)
                            = (seen`,[var:vars`])
          where (seen`,vars`)
                = if (not def) ([var:seen],vars)
                               (foldlr f ([var:seen],vars) args)
                (def,(_,args)) = varcontents graph var

/*
>   printgraph showfunc shownode graph nodes
>       = prntgrph showfunc shownode (refcount graph nodes) graph nodes

>   prntgrph showfunc shownode count graph
>       = snd.foldlr pg ([],[])
>         where pg node (seen,reprs)
>                   = (seen2,repr3:reprs)
>                     where repr3
>                               = shownode node++':':repr2, if ~member seen node & def & count node>1
>                               = repr2, otherwise
>                           (seen2,repr2)
>                               = (seen,shownode node), if member seen node \/ ~def
>                               = (seen1,showfunc func), if args=[]
>                               = (seen1,'(':showfunc func++concat (map (' ':) repr1)++")"), otherwise
>                           (seen1,repr1) = foldlr pg (node:seen,[]) args
>                           (def,(func,args)) = nodecontents graph node
*/

printgraph :: .(Graph sym var) .[var] -> .[String] | toString sym & toString var & == var
printgraph graph nodes
= prntgrph (refcount graph nodes) graph nodes

prntgrph count graph nodes
= snd (foldlr pg ([],[]) nodes)
  where pg node (seen,reprs)
        = (seen2,[repr3:reprs])
          where repr3
                = if (not (isMember node seen) && def && count node>1)
                     (toString node+++":"+++repr2)
                     repr2
                (seen2,repr2)
                = if (isMember node seen || not def)
                     (seen,toString node)
                     (if (args==[])
                         (seen1,toString func)
                         (seen1,"("+++toString func+++foldr (+++) ")" (map ((+++)" ") repr1)))
                (seen1,repr1) = foldlr pg ([node:seen],[]) args
                (def,(func,args)) = varcontents graph node

/*
>   refcount graph
>       = foldr rfcnt (const 0)
>         where rfcnt node count
>                   = count',                  if count node>0 \/ ~def
>                   = foldr rfcnt count' args, otherwise
>                     where count' = inc node count
>                           (def,(func,args)) = nodecontents graph node

>   inc n f n = f n+1
>   inc m f n = f n
*/
refcount :: .(Graph sym var) !.[var] -> (var -> Int) | == var
refcount graph roots
= foldr rfcnt (const 0) roots
  where rfcnt var count
        | (count var>0) || (not def) = count`
                                     = foldr rfcnt count` args
          where count` = inccounter var count
                (def,(_,args)) = varcontents graph var

/*

Compilegraph compiles a graph from parts.
Uses in Miranda:
 * reading a parsed program from a file.
*/

compilegraph :: ![(var,Node sym var)] -> Graph sym var
compilegraph nds = foldr (uncurry updategraph) emptygraph nds

/*

`Instance g1 g2' determines whether g2 is an instance of g1.
Uses in Miranda:
 * strat.lit.m: checking whether the strategy is starting a graph that is already in the history.
 * newfold.lit.m: checking whether a tail of the spine occurs in the history.

>   instance :: (graph * ***,***) -> (graph * **,**) -> bool
>   instance (pgraph,pnode) (sgraph,snode)
>   =   errs=[]
>       where (seen,mapping,errs) = instantiate (pgraph,sgraph) (pnode,snode) ([],[],[])

*/

isinstance
 :: (.Graph sym pvar,pvar)
    (.Graph sym var,var)
 -> Bool
 |  == sym
 &  == var
 &  == pvar

isinstance (pgraph,pvar) (sgraph,svar)
= isEmpty (thd3 (findmatching (pgraph,sgraph) (pvar,svar) ([],[],[])))

/*

Suppose `Instantiate (pattern,graph) (pnode,gnode) (seen,mapping,errs)'
returns `(seen',mapping',errs')'.

Then `mapping'' is the best attempt at extending the `mapping' to show that `graph' is an instance of `pattern'.
If it is not, then `errs'' is `errs' extended with node pairs that fail to match.
In the mean time, the nodes pairs examined are added to `seen', and returned as `seen''.
Node pairs already in `seen' are assumed to have already been checked and are not checked again.

Uses in Miranda:
 * extract.lit.m: used to find instances of patterns in the termination history, while folding trace tips.
 * transform.lit.m: Uses a different `instantiate' from rewr.lit.m.

`Instantiateargs' is the logical extension of `instantiate' to lists of node pairs.

*/

instantiate ::
    (Graph sym pvar,Graph sym var)
    (pvar,var)
    ([(pvar,var)],[(pvar,var)],[(pvar,var)])
 -> ([(pvar,var)],[(pvar,var)],[(pvar,var)])
 |  == sym
 &  == var
 &  == pvar

instantiate (pgraph,sgraph) (pnode,snode) (seen,mapping,errs)
| isMember psnode seen
  = (seen,mapping,errs)
| isMember pnode (map fst seen)
  = ([psnode:seen],mapping,[psnode:errs])
| not pdef
  = ([psnode:seen],[psnode:mapping],errs)
| not sdef
  = ([psnode:seen],mapping,[psnode:errs])
| not (psym==ssym && eqlen pargs sargs)
  = ([psnode:seen],mapping,[psnode:errs])
= (seen`,[psnode:mapping`],errs`)
  where (pdef,(psym,pargs)) = varcontents pgraph pnode
        (sdef,(ssym,sargs)) = varcontents sgraph snode
        (seen`,mapping`,errs`) = instantiateargs (pgraph,sgraph) (zip2 pargs sargs) ([psnode:seen],mapping,errs)
        psnode = (pnode,snode)

instantiateargs ::
    (Graph sym pvar,Graph sym var)
    [(pvar,var)]
    ([(pvar,var)],[(pvar,var)],[(pvar,var)])
 -> ([(pvar,var)],[(pvar,var)],[(pvar,var)])
 |  == sym
 &  == var
 &  == pvar

instantiateargs psgraph [] sme = sme
instantiateargs psgraph [psnode:psnodes] (seen,mapping,errs)
= (seen``,mapping``,errs``)
  where (seen`,mapping``,errs``) = instantiate psgraph psnode (seen,mapping`,errs`)
        (seen``,mapping`,errs`) = instantiateargs psgraph psnodes (seen`,mapping,errs)

:: Matchstate var pvar
   :== ( [(pvar,var)]  // Pattern-subject var combo's already visited
       , [(pvar,var)]  // Mapping from pattern vars to subject vars
       , [(pvar,var)]  // Pattern-subject var combo's that don't match (different symbol or arities)
       )

findmatching
 :: (Graph sym pvar,Graph sym var)
    .(pvar,var)
    u:(Matchstate var pvar)
 -> u:Matchstate var pvar
 |  == sym
 &  == var
 &  == pvar

findmatching (pgraph,sgraph) (pvar,svar) (seen,mapping,errs)
| isMember psvar seen
= (seen,mapping,errs)
| isMember pvar (map fst seen)
= ([psvar:seen],mapping,[psvar:errs])
| not pdef
= ([psvar:seen],[psvar:mapping],errs)
| not sdef
= ([psvar:seen],mapping,[psvar:errs])
| not (psym==ssym && eqlen pargs sargs)
= ([psvar:seen],mapping,[psvar:errs])
= (seen`,[psvar:mapping`],errs`)
  where (pdef,(psym,pargs)) = varcontents pgraph pvar
        (sdef,(ssym,sargs)) = varcontents sgraph svar
        (seen`,mapping`,errs`) = findargmatching (pgraph,sgraph) (zip2 pargs sargs) ([psvar:seen],mapping,errs)
        psvar = (pvar,svar)

findargmatching
 :: (Graph sym pvar,Graph sym var)
    [.(pvar,var)]
    u:(Matchstate var pvar)
 -> v:Matchstate var pvar
 |  == sym
 &  == var
 &  == pvar
 ,  [u<=v]

findargmatching psgraph [] seenmappingerrs = seenmappingerrs
findargmatching psgraph [psvar:psvars] (seen,mapping,errs)
= (seen``,mapping``,errs``)
  where (seen`,mapping``,errs``) = findmatching psgraph psvar (seen,mapping`,errs`)
        (seen``,mapping`,errs`) = findargmatching psgraph psvars (seen`,mapping,errs)

/*

------------------------------------------------------------------------

A folding function for graphs.
Uses in Miranda:
 * clean.lit.m: pretty-printing rewrite rules.
 * pretty.lit.m: pretty-printing rewrite rules.

>   foldgraph
>   ::  (**->***->***) ->
>       (**->***) ->
>       (*->[***]->***) ->
>       graph * ** ->
>       [**] ->
>       [***]

>   foldgraph folddef foldref foldcont graph roots
>   =   foldedroots
>       where count = refcount graph roots
>             (unused,foldedroots) = foldlm fold ([],roots)
>             fold (seen,node)
>             =   (seen,foldref node), if member seen node
>             =   (seen'',cond (def&count node>1) (folddef node folded) folded), otherwise
>                 where (seen'',folded)
>                       =   (seen',foldcont sym foldedargs), if def
>                       =   (node:seen,foldref node), otherwise
>                       (seen',foldedargs) = foldlm fold (node:seen,args)
>                       (def,(sym,args)) = nodecontents graph node

`Paths' lists all paths in a graph.
Never used in Miranda.

>   paths :: graph * ** -> ** -> [[**]]
>   paths graph node
>   =   paths' [] node []
>       where paths' top node rest
>             =   rest, if member top node
>             =   top':cond def (foldr (paths' top') rest args) rest, otherwise
>                 where (def,(sym,args)) = nodecontents graph node
>                       top' = node:top

`Extgraph sgraph pattern pnodes matching' extends some graph according
to the closed nodes in sgraph that closed nodes in pgraph are mapped to.
That is, we take the nodes from `pnodes', see if they are closed,
follow the mapping to `sgraph', see if they are closed there too,
and if so, add the contents in `sgraph' to the graph we're extending.

Uses in Miranda:
 * newfold.lit.m: function `findspinepart', to find parts of a spine.
       Specifically, to extend history patterns as one traverses down the trace.
 * transtree.lit.m: to extend the history when the reduce transformation is applied.
 * transform.lit.m: idem.

`Extgraph' is excluded in most import statements,
but there doesn't seem to be any other definition of it.
*/

extgraph :: (Graph sym var) (Graph sym pvar) [pvar] (Pfun pvar var) (Graph sym var) -> Graph sym var | == var & == pvar
extgraph sgraph pattern pnodes matching graph
= foldr addnode graph pnodes
  where addnode pnode
        = if (fst (varcontents pattern pnode)) (total id (postcomp addnode` matching) pnode) id
        addnode` snode
        = if sdef (updategraph snode scont) id
          where (sdef,scont) = varcontents sgraph snode

mapgraph ::
    !(  (Pfun var1 (sym1,[var1]))
     -> Pfun .var2 (.sym2,[.var2])
     )
    !.(Graph sym1 var1)
 -> Graph .sym2 .var2
mapgraph f (GraphAlias pfun) = GraphAlias (f pfun)

instance == (Graph sym var) | == sym & == var
where (==) (GraphAlias pf1) (GraphAlias pf2)
      = ((pf1 == pf2) <--- "graph.==(Graph) ends") ---> "graph.==(Graph) begins"
