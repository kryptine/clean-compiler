implementation module history

import spine
import rule
import graph
import basic
import StdEnv

:: History sym var
   :== [(var,[Rgraph sym var])]

/*

>   history * ** == [(**,[rgraph * **])]

>   showhistory :: (*->[char]) -> (**->[char]) -> history * ** -> [char]
>   showhistory showa showb = showlist (showpair showb (showlist (showrgraph showa showb)))

>   printhistory :: (*->[char]) -> (**->[char]) -> history * ** -> [[char]]
>   printhistory showa showb
>   =   concat.map print
>       where print (node,rgraphs)
>             =   showb node:map2 (++) ("<=  ":repeat "    ") (map (printrgraph showa showb) rgraphs)

*/

extendhistory
 :: (Graph sym var)
    (var -> var)
    (Spine sym var pvar)
    (History sym var)
 -> History sym var

extendhistory sgraph redirection spine history
= snd (foldspine (extendpair sgraph redirection) d d id d (const d) (extendpartial sgraph) (const d) (extendredex sgraph history) d spine)
  where d = (emptygraph,history)

/*

>   extendpair :: graph * ** -> (**->**) -> ** -> (graph * **,history * **) -> (graph * **,history * **)
>   extendpair sgraph redirect snode (hgraph,history)
>   =   (hgraph',remap (redirect snode) (mkrgraph snode hgraph':foldmap id [] history snode) (forget snode history))
>       where hgraph' = cond sdef (updategraph snode scont hgraph) hgraph
>             (sdef,scont) = dnc (const "in extendpair") sgraph snode

*/

extendpair
 :: (Graph sym var)
    (var->var)
    var
    (Graph sym var,History sym var)
 -> (Graph sym var,History sym var)

extendpair _ _ _ _ = undef

/*

>   extendpartial :: graph * ** -> rule * *** -> pfun *** ** -> (graph * **,history * **) -> (graph * **,history * **)
>   extendpartial sgraph rule matching (hgraph,history)
>   =   (extgraph' sgraph rule matching hgraph,history)

*/

extendpartial
 :: (Graph sym var)
    (Rule sym pvar)
    (Pfun pvar var)
    (Graph sym var,History sym var)
 -> (Graph sym var,History sym var)

extendpartial _ _ _ _ = undef

/*

>   extendredex :: graph * ** -> history * ** -> rule * *** -> pfun *** ** -> (graph * **,history * **)
>   extendredex sgraph history rule matching
>   =   (extgraph' sgraph rule matching emptygraph,history)

*/

extendredex
 :: (Graph sym var)
    (History sym var)
    (Rule sym pvar)
    (Pfun pvar var)
 -> (Graph sym var,History sym var)

extendredex _ _ _ _ = undef

/*

>   extgraph' sgraph rule
>   =   extgraph sgraph rgraph (nodelist rgraph (lhs rule))
>       where rgraph = rulegraph rule

*/
