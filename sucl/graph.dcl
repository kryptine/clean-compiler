definition module graph

// $Id$

from StdOverloaded import ==

// A rule associating a replacement with a pattern
//:: Rule sym var

// A mapping from variables to nodes (unrooted)
:: Graph sym var

// A node, bearing the contents of a variable
:: Node sym var
   :== (sym,[var])

/*

graph.lit - Unrooted graphs
===========================

Description
-----------

This script implements an abstract type for unrooted graphs  and  useful
functions to manipulate them.

------------------------------------------------------------

Interface
---------

Exported identifiers:

>   %export
>       compilegraph   ||  Compile graph from list of node definitions
>       emptygraph     ||  The empty unrooted graph
>       extgraph       ||  Extend a graph with the image of a matching
>       foldgraph      ||  Fold up a graph
>       graph          ||  Unrooted graphs over functorspace * and nodespace **
>       instance       ||  Check whether second graph is instance of first
>       instantiate    ||  Matches a pattern in a graph, if possible
>       movegraph      ||  Move a graph to a new node domain
>       nodecontents   ||  Determine the contents of a node
>       nodelist       ||  Determine the preorder list of reachable nodes from a given node
>       nodeset        ||  Determine the reachable nodes from a given node
>       overwritegraph ||  Overwrite a graph with a given graph
>       paths          ||  List of all paths in the graph
>       printgraph     ||  Prints a graph seen from given nodes
>       prunegraph     ||  Undefine the contents of a node
>       redirectgraph  ||  Redirects all references to nodes in a graph
>       refcount       ||  Determines the reference count function of a graph
>       restrictgraph  ||  Restricts the graph to certain defined nodes
>       showgraph      ||  Text representation of a graph
>       updategraph    ||  Update the contents of a node

Required types: none

------------------------------------------------------------

Includes
--------

>   %include "basic.lit" ||  foldlr mapsnd showlist showpair
>   %include "pfun.lit"  ||  domres emptypfun extend overwrite pfun postcomp restrict showpfun total

------------------------------------------------------------

Implementation
--------------

>   abstype graph * **
>      with emptygraph    :: graph * **
>           updategraph   :: ** -> (*,[**]) -> graph * ** -> graph * **
>           prunegraph    :: ** -> graph * ** -> graph * **
>           restrictgraph :: [**] -> graph * ** -> graph * **
>           redirectgraph :: (**->**) -> graph * ** -> graph * **
>           overwritegraph :: graph * ** -> graph * ** -> graph * **
>           showgraph     :: (*->[char]) -> (**->[char]) -> graph * ** -> [char]
>           nodecontents  :: graph * ** -> ** -> (bool,(*,[**]))
>           nodeset       :: graph * ** -> [**] -> ([**],[**])

>   movegraph  :: (***->**) -> [***] -> graph * *** -> graph * **
>   printgraph :: (*->[char]) -> (**->[char]) -> graph * ** -> [**] -> [[char]]
>   refcount   :: graph * ** -> [**] -> ** -> num

>   graph * ** == pfun ** (*,[**])

>   emptygraph    = emptypfun
>   updategraph   = extend
>   prunegraph    = restrict
>   restrictgraph = domres
>   redirectgraph = postcomp.mapsnd.map
>   overwritegraph = overwrite
>   showgraph showfunc shownode = showpfun shownode (showpair showfunc (showlist shownode))
*/

// The empty graph.
emptygraph :: Graph .sym .var

// Assign a node to a variable in a graph.
updategraph :: .var (Node .sym .var) (Graph .sym .var) -> Graph .sym .var

// Unassign a variable in a graph, making it free.
prunegraph :: .var (Graph .sym .var) -> Graph .sym .var

// Restrict a graph to a given domain, i.e.
// make all variables free except those in the domain.
restrictgraph :: !.[var] .(Graph sym var) -> Graph sym var | == var

// Redirect references (node arguments) in a graph
// according to a redirection function
redirectgraph :: (.var->.var) !(Graph .sym .var) -> Graph .sym .var | == var

// Overwrite the variables in the second graph by their contents in the first.
// Keeps the contents of the second graph if free in the first.
overwritegraph :: !(Graph .sym .var) (Graph .sym .var) -> Graph .sym .var

// Movegraph moves a graph to a different variable domain
// Requires a list of bound variables in the graph
movegraph :: (var1->.var2) !.[var1] .(Graph sym var1) -> Graph sym .var2 | == var1

// Varcontents obtains the contents of a variable in a graph
// Returns a boolean determining if it's bound, and
// its contents if the boolean is True.
varcontents :: !(Graph .sym var) var -> (.Bool,Node .sym var) | == var

// Graphvars determines the top-level-bound and free variables in a graph,
// reachable from a given list of variables.
// No duplicates.
graphvars :: .(Graph sym var) !.[var] -> (.[var],.[var]) | == var

// Graphvarlist determines all top level variables in a graph,
// reachable from a given list of variables.
// No duplicates.
varlist :: .(Graph sym var) !.[var] -> .[var] | == var

// Cannot remember what this one does???
prefix :: .(Graph sym var) .[var] !.[var] -> .([var],[var]) | == var

// Do reference counting in a graph for the outer bindings.
// References from case branches are counted once only.
// Initial list of variables is counted too.
refcount :: .(Graph sym var) !.[var] -> (var -> Int) | == var

// Determine whether the second argument is an instance of the first,
// i.e. whether there is a structure preserving mapping from the first to the second.
// Free variables may be mapped to anything.
// Bound variables may not be mapped to free variables.
isinstance
 :: (.Graph sym pvar,pvar)
    (.Graph sym var,var)
 -> Bool
 |  == sym
 &  == var
 &  == pvar

/*
>   compilegraph :: [(**,(*,[**]))] -> graph * **
>   compilegraph = foldr (uncurry updategraph) emptygraph

------------------------------------------------------------------------

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


>   paths :: graph * ** -> ** -> [[**]]

>   paths graph node
>   =   paths' [] node []
>       where paths' top node rest
>             =   rest, if member top node
>             =   top':cond def (foldr (paths' top') rest args) rest, otherwise
>                 where (def,(sym,args)) = nodecontents graph node
>                       top' = node:top


>   extgraph :: graph * ** -> graph * *** -> [***] -> pfun *** ** -> graph * ** -> graph * **
>   extgraph sgraph pattern pnodes matching graph
>   =   foldr addnode graph pnodes
>       where addnode pnode
>             =   total id (postcomp addnode' matching) pnode, if fst (nodecontents pattern pnode)
>             =   id, otherwise
>             addnode' snode
>             =   updategraph snode scont, if sdef
>             =   id, otherwise
>||           =   error "extgraph: closed node mapped to open node", otherwise
>                 ||  Could have used id, but let's report error when there is one...
>                 where (sdef,scont) = nodecontents sgraph snode

*/
