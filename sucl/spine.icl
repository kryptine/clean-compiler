implementation module spine

// $Id$

import history
import rule
import dnc
import graph
import pfun
import basic
from general import No,Yes
import StdEnv

/*

spine.lit - The extended functional strategy
============================================

Description
-----------

This script implements the strategy answer, and a function to compute it
for a given graph in a rewrite system.

The  strategy  answer  is  a  spine  --  in principle a colon of partial
matches from patterns of rewrite rules to the graph, with at the  bottom
the insteresting part: a redex, an open node or something else.  See the
definition of subspine for that.

The strategy function attempts to find a redex to reduce  the  graph  to
normal  form  instead  of  root normal form.  This is done by applying a
root normal form strategy recursively in preorder  over  the  graph  (of
course  ignoring  cycles).   The  node  at  which  the  root normal form
strategy was applied is returned in the strategy answer, so laziness can
be preserved.

------------------------------------------------------------

Interface
---------

Exported identifiers:

>   %export
>       answer          ||  Strategy answer type
>       foldspine       ||  Higher order general spine folding
>       ifopen          ||  Check for answer indicating Open
>       printanswer     ||  Make a human-readable representation of an answer
>       printspine      ||  Make a human-readable representation of a spine
>       showanswer      ||  Make a representation of an answer
>       showspine       ||  Make a representation of a spine
>       showsubspine    ||  Make a representation of a subspine
>       spine           ||  Colon of partial matches
>       spinenodes      ||  Determine nodes in a spine
>       spinetip        ||  Determine bottom of spine
>       subspine        ||  Bottom of spine

>       history         ||  Symbolic reduction history type
>       printhistory    ||  Make a human-readable representation of a history
>       showhistory     ||  Make a representation of a history

Required types:

    subspine - rule@rule.lit,rgraph@rule.lit,pfun@pfun.lit

------------------------------------------------------------

Includes
--------

>   %include "basic.lit"    ||  optional
>   %include "pfun.lit"     ||  pfun
>   %include "graph.lit"    ||  graph
>   %include "rule.lit"     ||  rgraph rule

------------------------------------------------------------

Implementation
--------------


Answer describes the answer of a strategy.  Absence of a  spine  implies
that the node was in root normal form.

>   answer * ** *** == optional (spine * ** ***)

>   showanswer showa showb showc = showoptional (showspine showa showb showc)
>   printanswer printa printb printc = foldoptional ["Rnf"] (printspine printa printb printc)

*/

:: Answer sym var pvar
   :== Optional (Spine sym var pvar)

printanswer ::
    (sym->String)
    (var->String)
    (pvar->String)
    String
 -> (Answer sym var pvar)
    *File
 -> .File
 |  == var
 &  == pvar

printanswer showsym showvar showpvar indent
= foldoptional (printrnf indent) (printspine showsym showvar showpvar indent)

printrnf indent file = file <<< indent <<< "RNF" <<< nl

/*

Spine  describes the spine returned by a strategy.  It contains the node
at which the strategy was applied, and the result for that node.

>   spine * ** *** == (**,subspine * ** ***)

>   showspine showa showb showc = showpair showb (showsubspine showa showb showc)

>   printspine printa printb printc
>   =   foldspine pair cycle delta force missingcase open partial unsafe redex strict
>       where pair node (line,lines) = (printb node++" => "++line):lines
>             cycle = ("Cycle",[])
>             delta = ("Delta",[])
>             force lines = ("Force",lines)
>             missingcase = ("MissingCase",[])
>             open rgraph = ("Open "++printrgraph printa printc rgraph,[])
>             partial rule matching lines = ("Partial <fn> "++printrule printa printc rule++' ':printpfun printc printb matching,lines)
>             unsafe rgraph = ("Unsafe "++printrgraph printa printb rgraph,[])
>             redex rule matching = ("Redex <fn> "++printrule printa printc rule++' ':printpfun printc printb matching,[])
>             strict = ("Strict",[])

*/

:: Spine sym var pvar
   :== (var,Subspine sym var pvar)

printspine ::
    (sym->String)
    (var->String)
    (pvar->String)
    String
 -> (Spine sym var pvar)
    *File
 -> .File
 |  == var
 &  == pvar

printspine showsym showvar showpvar indent
= foldspine pair cycle delta force missingcase open partial unsafe redex strict
  where pair node (line,printrest) file = printrest (file <<< indent <<< showvar node <<< ": " <<< line <<< nl)
        cycle = ("Cycle",id)
        delta = ("Delta",id)
        force argno printrest = ("Force argument "+++toString argno,printrest)
        missingcase = ("MissingCase",id)
        open rgraph = ("Open "+++hd (printgraphBy showsym showpvar (rgraphgraph rgraph) [rgraphroot rgraph]),id)
        partial rule matching pvar printrest = ("Partial <fn> "+++showruleanch showsym showpvar (repeat False) rule [pvar]+++" <"+++showpvar pvar+++"> "+++showpfun showpvar showvar matching,printrest)
        unsafe rgraph = ("Unsafe "+++hd (printgraphBy showsym showvar (rgraphgraph rgraph) [rgraphroot rgraph]),id)
        redex rule matching = ("Redex <fn> "+++showruleanch showsym showpvar (repeat False) rule []+++" "+++showpfun showpvar showvar matching,id)
        strict = ("Strict",id)

/*

Subspine describes what was the result of the strategy applied to a node
in a graph.

>   subspine * ** ***
>   ::= Cycle                                               | ||  The spine contains a cycle
>       Delta                                               | ||  An imported (delta) rule was found
>       Force (spine * ** ***)                              | ||  Global strictness annotation forced evaluation of a subgraph
>       MissingCase                                         | ||  All alternatives failed for a function symbol
>       Open (rgraph * ***)                                 | ||  Need root normal form of open node for matching
>       Partial (rule * ***) (pfun *** **) (spine * ** ***) | ||  A rule was strictly partially matched
>       Unsafe (rgraph * **)                                | ||  Terminated due to immininent recursion
>       Redex (rule * ***) (pfun *** **)                    | ||  Total match
>       Strict                                                ||  Need root normal form due to strictness

>   showsubspine showa showb showc
>   =   sh
>       where sh Cycle = "Cycle"
>             sh Delta = "Delta"
>             sh (Force spine) = "(Force "++showspine showa showb showc spine++")"
>             sh MissingCase = "MissingCase"
>             sh (Open rgraph) = "(Open "++showrgraph showa showc rgraph++")"
>             sh (Partial rule matching spine) = "(Partial "++showrule showa showc rule++' ':showpfun showc showb matching++' ':showspine showa showb showc spine++")"
>             sh (Unsafe rgraph) = "(Unsafe "++showrgraph showa showb rgraph++")"
>             sh (Redex rule matching) = "(Redex "++showrule showa showc rule++' ':showpfun showc showb matching++")"
>             sh Strict = "Strict"

    printsubspine printa printb printc
    =   pr
        where pr Cycle = "Cycle"
              pr Delta = "Delta"
              pr (Force argno spine) = "(Force <argno> "++printspine printa printb printc spine++")"
              pr MissingCase = "MissingCase"
              pr (Open rgraph) = "(Open "++printrgraph printa printc rgraph++")"
              pr (Partial rule matching spine) = "(Partial "++printrule printa printc rule++' ':printpfun printc printb matching++' ':printspine printa printb printc spine++")"
              pr (Unsafe rgraph) = "(Unsafe "++printrgraph printa printb rgraph++")"
              pr (Redex rule matching) = "(Redex "++printrule printa printc rule++' ':printpfun printc printb matching++")"
              pr Strict = "Strict"

*/

:: Subspine sym var pvar
   = Cycle                                                              // The spine contains a cycle
   | Delta                                                              // An imported (delta) rule was found
   | Force Int (Spine sym var pvar)                                     // Global strictness annotation forced evaluation of a subgraph at specified argument position
   | MissingCase                                                        // All alternatives failed for a function symbol
   | Open (Rgraph sym pvar)                                             // Need root normal form of open node for matching
   | Partial (Rule sym pvar) (Pfun pvar var) pvar (Spine sym var pvar)  // A rule was strictly partially matched
   | Unsafe (HistoryPattern sym var)                                    // Terminated due to immininent recursion
   | Redex (Rule sym pvar) (Pfun pvar var)                              // Total match
   | Strict                                                             // Need root normal form due to strictness

/*

>   foldspine
>   ::  (**->****->*****) ->
>       **** ->
>       **** ->
>       (*****->****) ->
>       **** ->
>       (rgraph * ***->****) ->
>       (rule * ***->pfun *** **->*****->****) ->
>       (rgraph * **->****) ->
>       (rule * ***->pfun *** **->****) ->
>       **** ->
>       spine * ** *** ->
>       *****

>   foldspine pair cycle delta force missingcase open partial unsafe redex strict
>   =   fold
>       where fold (node,subspine) = pair node (foldsub subspine)
>             foldsub Cycle = cycle
>             foldsub Delta = delta
>             foldsub (Force spine) = force (fold spine)
>             foldsub MissingCase = missingcase
>             foldsub (Open rgraph) = open rgraph
>             foldsub (Partial rule matching spine) = partial rule matching (fold spine)
>             foldsub (Unsafe rgraph) = unsafe rgraph
>             foldsub (Redex rule matching) = redex rule matching
>             foldsub Strict = strict

*/

foldspine
 :: !(var .subresult -> .result)                                    // Fold the spine itself
    .subresult                                                      // Fold a Cycle subspine
    .subresult                                                      // Fold a Delta subspine
    (Int .result -> .subresult)                                     // Fold a Force subspine
    .subresult                                                      // Fold a MissingCase subspine
    ((Rgraph sym pvar) -> .subresult)                               // Fold an Open subspine
    ((Rule sym pvar) (Pfun pvar var) pvar .result -> .subresult)    // Fold a Partial subspine
    ((HistoryPattern sym var) -> .subresult)                        // Fold an Unsafe subspine
    ((Rule sym pvar) (Pfun pvar var) -> .subresult)                 // Fold a Redex subspine
    .subresult                                                      // Fold a Strict subspine
    .(Spine sym var pvar)                                           // The spine to fold
 -> .result                                                         // The final result

foldspine pair cycle delta force missingcase open partial unsafe redex strict spine
= fold spine
  where fold spine
        = pair node (foldsub subspine)
          where (node,subspine) = spine
        foldsub Cycle = cycle
        foldsub Delta = delta
        foldsub (Force argno spine) = force argno (fold spine)
        foldsub MissingCase = missingcase
        foldsub (Open rgraph) = open rgraph
        foldsub (Partial rule matching rnode spine) = partial rule matching rnode (fold spine)
        foldsub (Unsafe histpat) = unsafe histpat
        foldsub (Redex rule matching) = redex rule matching
        foldsub Strict = strict

spinetip :: !(Spine sym var pvar) -> Spine sym var pvar
spinetip (_,Force argno spine) = spinetip spine
spinetip (_,Partial _ _ pnode spine) = spinetip spine
spinetip spine = spine

spinenodes :: .(Spine sym var pvar) -> [var]
spinenodes spine
= nodes
  where partial _ _ _ = id
        redex _ _ = []
        nodes = foldspine cons [] [] (const id) [] (const []) partial (const []) redex [] spine

ifopen :: result result !.(Answer sym var pvar) -> result
ifopen open other spine
= foldoptional other (checkopen o spinetip) spine
  where checkopen (onode,Open pattern) = open
        checkopen tip = other


/*********************************************
* Extending the history according to a spine *
*********************************************/

// A function that associates specific patterns with extensible nodes
// To be used for extending history patterns
:: LinkExtender sym var
   :== (Link var)               // The extensible link to look for
    -> HistoryPattern sym var   // The associated pattern

extendhistory
 :: (Graph sym var)
    (var -> var)
    (Spine sym var pvar)
    (History sym var)
 -> History sym var
 |  == var
 &  == pvar

extendhistory sgraph redirection spine history
= snd (foldspine (extendpair sgraph redirection) d d (const id) d (const d) (extendpartial sgraph) (const d) (extendredex sgraph history) d spine)
  where d = (emptygraph,history)


extendpair
 :: (Graph sym var)
    (var->var)
    var
    (Graph sym var,History sym var)
 -> (Graph sym var,History sym var)
 |  == var

extendpair sgraph redirect snode (hgraph,history)
= (hgraph`,remap (redirect snode) [mkrgraph snode hgraph`:foldmap id [] history snode] (forget snode history))
  where hgraph` = if sdef (updategraph snode scont hgraph) hgraph
        (sdef,scont) = dnc (const "in extendpair") sgraph snode

extendpartial
 :: (Graph sym var)
    (Rule sym pvar)
    (Pfun pvar var)
    pvar
    (Graph sym var,History sym var)
 -> (Graph sym var,History sym var)
 |  == var
 &  == pvar

extendpartial sgraph rule matching rnode (hgraph,history)
= (extgraph` sgraph rule matching hgraph,history)

extendredex
 :: (Graph sym var)
    (History sym var)
    (Rule sym pvar)
    (Pfun pvar var)
 -> (Graph sym var,History sym var)
 |  == var
 &  == pvar

extendredex sgraph history rule matching
= (extgraph` sgraph rule matching emptygraph,history)

extgraph` :: (Graph sym var) (Rule sym pvar) -> (Pfun pvar var) (Graph sym var) -> Graph sym var | == var & == pvar
extgraph` sgraph rule
= extgraph sgraph rgraph (varlist rgraph (arguments rule))
  where rgraph = rulegraph rule

(writeanswer) infixl :: *File (Answer sym var pvar) -> .File | toString sym & ==,toString,<<< var // & ==,toString,<<< pvar
(writeanswer) file No = file <<< "<root-normal-form>" <<< nl
(writeanswer) file (Yes spine) = file writespine spine <<< nl

(writespine) infixl :: *File (Spine sym var pvar) -> .File | toString sym & ==,toString,<<< var // & ==,toString,<<< pvar
(writespine) file (var,subspine) = file <<< "(" <<< var <<< "," <<< subspine <<< ")"

instance <<< (Subspine sym var pvar) | toString sym & ==,toString,<<< var // & ==,toString,<<< pvar
where
/*
      (<<<) file _ = file <<< "<subspine>"
*/
      (<<<) file Cycle = file <<< "Cycle"
      (<<<) file Delta = file <<< "Delta"
      (<<<) file (Force argno spine) = file <<< "Force " <<< argno <<< " " writespine spine
      (<<<) file MissingCase = file <<< "MissingCase"
      (<<<) file (Open pattern) = file <<< "Open <rgraph>"
      (<<<) file (Partial rule matching focus spine) = file <<< "Partial {rule=<Rule sym pvar>, matching=<Pfun pvar var>, focus=<pvar>, spine=" writespine spine <<< "}"
      (<<<) file (Unsafe pattern) = file <<< "Unsafe " writergraph pattern
      (<<<) file (Redex rule matching) = file <<< "Redex {rule=<Rule sym pvar>, matching=<Pfun pvar var>}"
      (<<<) file Strict = file <<< "Strict"
