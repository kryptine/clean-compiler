implementation module pretty

// $Id$

import StdEnv

:: Layout
   = Line String            // A single line
   | Indent String [Layout] // A sequence of lines, the first of which is indented by a string (and the rest by an equivalent number of spaces)

class Pretty t
where pretty :: t -> Layout

instance Pretty {#Char}
where pretty s = Line s

instance <<< Layout
where <<< f l
      = printlayout l cont True [] f
        where cont first prefixes f = f

printlayout (Line s) cont first is f
= cont False (if first (asspaces is) is) ((printindents is f) <<< s)
printlayout (Indent i ls) cont first is f
= foldr printlayout cont` ls True [i:is] f
  where cont` first` is` f`
        = cont first is f`

asspaces is = [toString (spaces (sum (map size is)))]

printindents is f
= foldr printindent f is
printindent i f = f<<<i

/*

>   %include "basic.lit"
>   %include "graph.lit" -extgraph
>   %include "rule.lit"
>   %include "clean.lit" -cleanrule -cleantyperule -coretyperule -symbolmodule -typesymbolmodule

------------------------------------------------------------------------

Get the Select nodes from a graph.

>   getselectnodes :: graph symbol ** -> ** -> [((**,num),(num,**))]

>   getselectnodes graph root
>   =   foldr (withmeta (nodecontents graph) addselectnode) [] (nodelist graph [root])
>       where addselectnode (True,(Select arity index,[tuplenode])) selectnode
>             =   (((tuplenode,arity),(index,selectnode)):)
>             addselectnode contents node = id

Distribute the Select nodes over their indexes.

>   splitselectnodes :: ((**,num),[(num,**)]) -> (**,[[**]])

>   splitselectnodes ((tuplenode,arity),selects)
>   =   (tuplenode,foldr dist (rep arity []) selects)
>       where dist (1,selectnode) (ns:nss) = (selectnode:ns):nss
>             dist (index,selectnode) (ns:nss) = ns:dist (index-1,selectnode) nss

Make left hand sides.

>   makelhss :: [**] -> [[**]] -> ([**],[[**]])

>   makelhss heap nss
>   =   (heap,[]), if empty
>   =   (heap'',ns':nss''), otherwise
>       where (heap'',nss'') = makelhss heap' nss'
>             (empty,ns',heap',nss') = heads heap nss
>             heads heap [] = (True,[],heap,[])
>             heads (node:heap) ([]:nss)
>             =   (empty,node:ns',heap',[]:nss')
>                 where (empty,ns',heap',nss') = heads heap nss
>             heads heap ((n:ns):nss)
>             =   (False,n:ns',heap',ns:nss')
>                 where (empty,ns',heap',nss') = heads heap nss

>   makenodedefs :: [**] -> [(**,[[**]])] -> [(**,[**])]

>   makenodedefs heap []
>   =   []
>   makenodedefs heap ((tuplenode,nss):rest)
>   =   map (pair tuplenode) lhss++nodedefs
>       where (heap',lhss) = makelhss heap nss
>             nodedefs = makenodedefs heap' rest



>   pretty :: symbol -> rule symbol node -> [[char]]

>   pretty symbol rule
>   =   (showsymbol symbol++' ':concat (map ((++" ").fst) argreprs)++"-> "++snd rootrepr):
>       map2 shownodedef nodedefs (map snd tuplereprs)
>       where args = lhs rule; root = rhs rule; graph = rulegraph rule
>             nodedefs = makenodedefs (heap--nodelist graph (root:args)) tupleselections
>             tupleselections
>             =   (   map splitselectnodes.
>                     partition fst snd
>                 ) (getselectnodes graph root)
>             tuplenodes = map fst tupleselections
>             prunedgraph = foldr prunegraph graph tuplenodes

>             [argreprs,[rootrepr],tuplereprs]
>             =   hof (foldgraph prettyref (issafe.shownode) prettydef prunedgraph) [args,[root],map fst nodedefs]
>                 where prettyref node (saferef,unsaferef) = issafe (shownode node++':':saferef)

>             shownodedef (tuplenode,selectnodes) tuplerepr
>             =   ",   ("++join ',' (map shownode selectnodes)++"): "++tuplerepr

>issafe::[char]->([char],[char])
>prettydef::symbol->[([char],[char])]->([char],[char])

------------------------------------------------------------------------
Useful (higher order) functions.

>   withmeta :: (*->**) -> (**->*->***) -> * -> ***
>   withmeta meta f x = f (meta x) x

>   pair :: * -> ** -> (*,**)
>   pair x y = (x,y)

>   hof :: ([*]->[**]) -> [[*]] -> [[**]]
>   hof f xss
>   =   claims xss (f (concat xss))

>   claims :: [[*]] -> [**] -> [[**]]
>   claims [] ys = []
>   claims (xs:xss) ys
>   =   zs:claims xss ys'
>       where (zs,ys') = claim xs ys

*/
