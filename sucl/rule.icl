implementation module rule

// $Id$

import graph
import basic
import StdEnv

:: Rule sym var
    = RuleAlias [var] var (Graph sym var)

:: Rgraph sym var
    = RgraphAlias var (Graph sym var)

/*

rule.lit - Rooted graphs and rules
==================================

Description
-----------

This module implements abstract  types  for  rooted  graphs  and  rules,
together  with  some  useful  functions  on  them.   Though  very simple
definitions, it greatly helps  the  readability  of  error  messages  if
rooted graphs or rules occur in them.

A rooted graph is a tuple consisting of a root  and  an  unrooted  graph
(how obvious).

The implementation of a rule is less obvious.  Instead of simply using a
graph  with  two  roots,  the  root  of  the  pattern and its associated
function symbol  have  been  taken  out.   Hence  the  pattern  is  only
accessibly  by  its  arguments.   The  root  of the replacement is still
accessible.  The reason for this is twofold: the root  must  be  defined
anyway,  and  if  the  rule  is  a type rule, we are now able to use two
different domains for (normal) symbols and type symbols.

------------------------------------------------------------

Interface
---------

Exported identifiers:

>   %export
>       compilerule  ||  Compile a rule from all loose parts
>       emptyrgraph  ||  Creates an empty rooted graph
>       lhs          ||  Determines the left root of a rule
>       mkrgraph     ||  Composes a rooted graph from a root and a graph
>       mkrule       ||  Composes a rule from left and right roots and a graph
>       printrgraph  ||  Makes a readable representation of a rooted graph
>       printrule    ||  Makes a readable representation of a rule
>       prunergraph  ||  Undefines the contents of a node of a rooted graph
>       rgraph       ||  Type of rooted graph over functorspace * and nodespace **
>       rgraphgraph  ||  Determines the (unrooted) graph of a rooted graph
>       rgraphroot   ||  Determines the root of a rooted graph
>       rhs          ||  Determines the right root of a rule
>       rule         ||  Type of rules over functorspace * and nodespace **
>       rulegraph    ||  Determines the graph of a rule
>       showrgraph   ||  Make a representation of a rooted graph
>       showrule     ||  Make a representation of a rule
>       updatergraph ||  Updates the contents of a node of a rooted graph

Required types:

    mkrgraph     - graph@graph.lit
    mkrule       - graph@graph.lit
    rgraphgraph  - graph@graph.lit
    rulegraph    - graph@graph.lit

------------------------------------------------------------

Includes
--------

>   %include "basic.lit"
>   %include "graph.lit" -extgraph

------------------------------------------------------------

Implementation
--------------

>   abstype rgraph * **
>      with emptyrgraph  :: ** -> rgraph * **
>           updatergraph :: ** -> (*,[**]) -> rgraph * ** -> rgraph * **
>           prunergraph  :: ** -> rgraph * ** -> rgraph * **
>           rgraphroot   :: rgraph * ** -> **
>           rgraphgraph  :: rgraph * ** -> graph * **
>           mkrgraph     :: ** -> graph * ** -> rgraph * **
>           showrgraph   :: (*->[char]) -> (**->[char]) -> rgraph * ** -> [char]
>           printrgraph  :: (*->[char]) -> (**->[char]) -> rgraph * ** -> [char]

>   abstype rule * **
>      with mkrule    :: [**] -> ** -> graph * ** -> rule * **
>           lhs       :: rule * ** -> [**]
>           rhs       :: rule * ** -> **
>           rulegraph :: rule * ** -> graph * **
>           showrule  :: (*->[char]) -> (**->[char]) -> rule * ** -> [char]
>           printrule :: (*->[char]) -> (**->[char]) -> rule * ** -> [char]


Rooted graphs

>   emptyrgraph root = (root,emptygraph)
>   updatergraph node contents (root,graph) = (root,updategraph node contents graph)
>   prunergraph node (root,graph) = (root,prunegraph node graph)
>   rgraphroot (root,graph) = root
>   rgraphgraph (root,graph) = graph
>   mkrgraph root graph = (root,graph)
*/

emptyrgraph :: var -> .Rgraph sym var
emptyrgraph root = RgraphAlias root emptygraph

updatergraph :: var .(Node sym var) !.(Rgraph sym var) -> .Rgraph sym var
updatergraph var node rgraph = maprgraph (mapsnd (updategraph var node)) rgraph

prunergraph  :: var !.(Rgraph sym var) -> .Rgraph sym var
prunergraph var rgraph = maprgraph (mapsnd (prunegraph var)) rgraph

rgraphroot   :: !.(Rgraph sym var) -> var
rgraphroot (RgraphAlias root _) = root

rgraphgraph  :: !.(Rgraph sym var) -> Graph sym var
rgraphgraph (RgraphAlias _ graph) = graph

mkrgraph :: var (Graph sym var) -> .Rgraph sym var
mkrgraph root graph = RgraphAlias root graph

maprgraph :: (.(var1,Graph sym1 var1) -> .(var2,Graph sym2 var2)) !.(Rgraph sym1 var1) -> .Rgraph sym2 var2
maprgraph f (RgraphAlias root1 graph1) = RgraphAlias root2 graph2
   where (root2,graph2) = f (root1,graph1)

instance toString (Rgraph sym var) | toString sym & toString var & Eq var
where toString rgraph = showrgraph toString toString rgraph

showrgraph ::
    (sym->String)
    (var->String)
    (Rgraph sym var)
 -> String
 |  == var

showrgraph showsym showvar (RgraphAlias root graph)
= "("+++snd (showsubgraph root ([],"emptyrgraph) "))+++showvar root
  where showsubgraph node (seen,repr)
        | not def || isMember node seen
          = (seen,repr)
        = (seen``,repr``)
          where (def,(f,args)) = varcontents graph node
                (seen``,repr`) = foldlr showsubgraph (seen`,repr) args
                seen` = [node:seen]
                repr`` = "updatergraph "+++showvar node+++" ("+++showsym f+++","+++showlist showvar args+++") o "+++repr`

/*
>   printrgraph showfunc shownode (root,graph)
>       = hd (printgraph showfunc shownode graph [root])
*/

instance <<< (Rgraph sym var) | toString sym & toString var & == var
where (<<<) file (RgraphAlias root graph)
      = file <<< hd (printgraph graph [root])

/*
Rules

>   mkrule lroots rroot graph = (lroots,rroot,graph)
>   lhs (lroots,rroot,graph) = lroots
>   rhs (lroots,rroot,graph) = rroot
>   rulegraph (lroots,rroot,graph) = graph
*/

mkrule :: .[var] var (Graph sym var) -> .Rule sym var
mkrule args root graph = RuleAlias args root graph

arguments :: !.(Rule sym var) -> [var]
arguments (RuleAlias args _ _) = args

ruleroot :: !.(Rule sym var) -> var
ruleroot (RuleAlias _ root _) = root

rulegraph :: !.(Rule sym var) -> Graph sym var
rulegraph (RuleAlias _ _ graph) = graph

/*
>   printrule showfunc shownode (lroots,rroot,graph)
>       = (concat.map (++" ").init) reprs++"-> "++last reprs
>         where reprs = printgraph showfunc shownode graph (lroots++[rroot])

>   compilerule :: [**] -> ** -> [(**,(*,[**]))] -> rule * **
>   compilerule args root = mkrule args root.compilegraph

*/

instance == (Rgraph sym var) | == sym & == var
where (==) (RgraphAlias root1 graph1) (RgraphAlias root2 graph2)
       = root1==root2 && graph1==graph2

instance toString (Rule sym var) | toString sym & toString var & == var
where toString rule = showrule toString toString rule

showrule ::
    (sym->String)
    (var->String)
    (Rule sym var)
 -> String
 |  == var

showrule showsym showvar (RuleAlias lroots rroot graph)
= "((mkrule "+++showlist showvar lroots+++" "+++showvar rroot+++repr`+++") emptygraph)"
  where (seen,repr`) = foldlr showsubgraph ([],repr) lroots
        (seen`,repr) = showsubgraph rroot (seen,"")
        showsubgraph node (seen,repr)
        | not def || isMember node seen
          = (seen,repr)
        = (seen``,repr``)
          where (def,(f,args)) = varcontents graph node
                (seen``,repr`) = foldlr showsubgraph (seen`,repr) args
                seen` = [node:seen]
                repr`` = " o updategraph "+++showvar node+++" ("+++showsym f+++","+++showlist showvar args+++")"+++repr`

ruleToString :: (sym->.String) .(Rule sym var) -> String | Eq,toString var
ruleToString symToString (RuleAlias lroots rroot graph)
/*
= if def ("<rule with root "+++symToString sym+++">") "<rule with no root>"
  where (def,(sym,args)) = varcontents graph rroot
*/
= "((mkrule "+++showlist toString lroots+++" "+++toString rroot+++repr`+++") emptygraph)"
  where (seen,repr`) = foldlr showsubgraph ([],repr) lroots
        (seen`,repr) = showsubgraph rroot (seen,"")
        showsubgraph node (seen,repr)
        | not def || isMember node seen
          = (seen,repr)
        = (seen``,repr``)
          where (def,(f,args)) = varcontents graph node
                (seen``,repr`) = foldlr showsubgraph (seen`,repr) args
                seen` = [node:seen]
                repr`` = " o updategraph "+++toString node+++" ("+++symToString f+++","+++showlist toString args+++")"+++repr`

instance <<< (Rule sym var) | toString sym & toString,== var
where (<<<) file rule = file <<< toString rule

(writergraph) infixl :: *File .(Rgraph sym var) -> .File | toString sym & ==,toString var
(writergraph) file rgraph = file <<< rgraph

(writerule) infixl :: *File .(Rule sym var) -> .File | toString sym & ==,toString var
(writerule) file rule = file <<< rule

showruleanch ::
    (sym->String)
    (var->String)
    [Bool]
    (Rule sym var)
    [var]
 -> String
 |  == var

showruleanch showsym showvar stricts rule anchors
= foldr (+++) "" (map2 annot stricts argreprs)+++"-> "+++rootrepr
  where graph = rulegraph rule; args = arguments rule; root = ruleroot rule
        (argreprs,[rootrepr:anchorreprs]) = claim args reprs
        reprs = printgraphBy showsym showvar graph (args++[root:anchors])
        annot strict repr = (if strict ((+++) "!") id) (repr+++" ")
