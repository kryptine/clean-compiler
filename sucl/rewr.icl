implementation module rewr

// $Id$

import rule
import graph
import pfun
import basic
import StdEnv

/*

Rewriting of graphs

Exported identifiers:
\begin{description}
\item[\tt unfold]      Apply a rewrite rule to a graph
\item[\tt xunfold]     As {\tt unfold}, but also provides full matching
		       from the applied rule to the (resulting) subject
		       graph
\item[\tt fold]        Apply a rewrite rule in reverse to a graph
\item[\tt instantiate] Instantiate a graph with a pattern
\end{description}

Temporarily hidden:
\begin{description}
\item[\tt build] Build a copy of a graph
\end{description}

Temporarily not exported:
\begin{description}
\item[\tt getmap]   Determine mapping from one graph to another
\item[\tt existmap] Determine if a mapping from one graph to another exists
\end{description}

>   %export foldfn getmapping instantiate xunfold

    unfold
        ::  pfun *** ** ->           ||  Mapping as result from match of lhs
            rule * *** ->            ||  Rule to unfold
            ([**],graph * **,**) ->  ||  Heap,graph,node
            ([**],graph * **,**)     ||  New heap,graph,node

>   xunfold
>   ::  ** ->            ||  Root of the redex to unfold
>       rule * *** ->    ||  Rule to unfold by
>       (   [**],        ||  Unused heap
>           **,          ||  Root of subject
>           graph * **,  ||  Subject graph
>           pfun *** **  ||  Matching of pattern from rule to subject
>       ) ->
>       (   [**],        ||  Remaining heap
>           **,          ||  Possibly redirected root of subject
>           graph * **,  ||  Extended subject graph
>           pfun *** **  ||  Extended matching from rule to subject
>       )

    fold
        ::  pfun *** ** ->           ||  Mapping as result from match of rhs
            rule * *** ->            ||  Rule to fold
            ([**],graph * **,**) ->  ||  Heap,graph,node
            ([**],graph * **,**)     ||  New heap,graph,node

>   build
>       ::  graph * *** -> *** ->                  ||  Graph,root to be copied
>           ([**],[**],graph * **,pfun *** **) ->  ||  Heap,init nodes,init graph,init mapping
>           ([**],[**],graph * **,pfun *** **)     ||  New heap,new nodes,new graph,new mapping

>   getmap :: graph * *** -> *** -> graph * **  -> ** -> pfun *** **

>   existmap :: graph * *** -> *** -> graph * ** -> ** -> bool


Implementation

>   %include "basic.lit"
>   %include "pfun.lit"
>   %include "graph.lit" -instantiate
>   %include "rule.lit"

*/

xunfold
 :: var
    (Rule sym pvar)
   !(   [var]
    ,   var
    ,   Graph sym var
    ,   Pfun pvar var
    )
 -> (   [var]
    ,   var
    ,   Graph sym var
    ,   Pfun pvar var
    ) | == var & == pvar

xunfold redexroot rule (heap,root,subject,matching)
= (heap`,redirection root,redirectgraph redirection subject`,matching`)
  where (heap`,[rhs`:_],subject`,matching`)
        = build (rulegraph rule) (ruleroot rule) (heap,[],subject,matching)
        redirection = adjust redexroot rhs` id

instantiate
 :: .(Graph sym pvar)       // Pattern to instantiate with
    pvar                    // Root of the pattern
    var                     // Open node to instantiate
    (.[var],.Graph sym var) // Heap,graph
 -> .([var],Graph sym var)  // New heap,graph
 |  == var
 &  == pvar

instantiate pattern proot node (heap,graph)
| not closed
= (heap,graph)
= (heap``,graph``)
  where (heap``,params``,graph``,_)
        = foldr (build pattern) (heap,[],graph`,extend proot node emptypfun) params
        (closed,(f,params)) = varcontents pattern proot
        graph` = updategraph node (f,params``) graph

build
 :: (Graph sym pvar)
    pvar
    (   [var]
    ,   [var]
    ,   Graph sym var
    ,  !Pfun pvar var
    )
 -> (   [var]
    ,   [var]
    ,   Graph sym var
    ,   Pfun pvar var
    ) | == var & == pvar

build pattern node (heap,nodes,graph,mapping)
| seen
= (heap,[seenas:nodes],graph,mapping)
| not closed
= (heap`,[node`:nodes],graph,mapping`)
= (heap``,[node`:nodes],graph``,mapping``)
  where (seen,seenas) = apply mapping node
        [node`:heap`] = heap
        mapping` = extend node node` mapping
        (closed,(f,params)) = varcontents pattern node
        (heap``,params``,graph``,mapping``)
        = foldr (build pattern) (heap`,[],graph`,mapping`) params
        graph` = updategraph node` (f,params``) graph

/*
Mapping

>   getmap pattern patnode graph node
>       = getmapping nomatch pattern graph (patnode,node) id emptypfun
>         where nomatch = error "getmap: pattern and graph do not match"

>   existmap pattern patnode graph node
>       = getmapping False pattern graph (patnode,node) (const True) emptypfun
*/

getmapping
 :: tsym
    (Graph sym pvar)
    (Graph sym var)
    !(pvar,var)
    ((Pfun pvar var) -> tsym)
    !(Pfun pvar var)
 -> tsym
 |  == sym
 &  == var
 &  == pvar

getmapping failure patgraph graph (patnode,node) success mapping
| seen
= if (seenas==node) (success mapping) failure
| not patdef
= success mapping`
| not (def && patfunc==func && eqlen patargs args)
= failure
= foldr (getmapping failure patgraph graph) success (zip2 patargs args) mapping`
  where (seen,seenas) = apply mapping patnode
        (patdef,(patfunc,patargs)) = varcontents patgraph patnode
        (def,(func,args)) = varcontents graph node
        mapping` = extend patnode node mapping

/*
The foldfn operation folds an area of a graph back to a  function  call.
The  following  two  conditions must be satisfied in order not to need a
heap of fresh nodes:

 1: At least one node is freed by the fold operation to hold the root of
    the  redex.  This is the root of the reduct; since it must be freed,
    the rule that is folded by must not be a projection function;

 2: No other new nodes are  necessary.   Therefore,  all  nodes  of  the
    pattern of the rule that is folded by  except  the  root  must  also
    occur in the replacement.

Furthermore, the pattern of the rule is only given by  its  root  symbol
and its arguments; the arguments are open nodes.

*/

foldfn
 :: (Pfun pvar var)     // Matching of replacement
    sym                 // Symbol at root of pattern
    [pvar]              // Arguments of pattern
    pvar                // Root of replacement
    (Graph sym var)     // Subject graph
 -> Graph sym var       // Folded subject
 |  == pvar

foldfn matching symbol arguments replacementroot sgraph
= updategraph (domatching replacementroot) (symbol,map domatching arguments) sgraph
  where domatching = total nomatching matching
        nomatching = abort "foldfn: no matching of argument of pattern"
