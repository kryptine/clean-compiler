definition module spine

from rule import Rgraph,Rule
from pfun import Pfun
from basic import Optional

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
              pr (Force spine) = "(Force "++printspine printa printb printc spine++")"
              pr MissingCase = "MissingCase"
              pr (Open rgraph) = "(Open "++printrgraph printa printc rgraph++")"
              pr (Partial rule matching spine) = "(Partial "++printrule printa printc rule++' ':printpfun printc printb matching++' ':printspine printa printb printc spine++")"
              pr (Unsafe rgraph) = "(Unsafe "++printrgraph printa printb rgraph++")"
              pr (Redex rule matching) = "(Redex "++printrule printa printc rule++' ':printpfun printc printb matching++")"
              pr Strict = "Strict"

*/

:: Subspine sym var pvar
   = Cycle                                                        // The spine contains a cycle
   | Delta                                                        // An imported (delta) rule was found
   | Force (Spine sym var pvar)                                   // Global strictness annotation forced evaluation of a subgraph
   | MissingCase                                                  // All alternatives failed for a function symbol
   | Open (Rgraph sym pvar)                                       // Need root normal form of open node for matching
   | Partial (Rule sym pvar) (Pfun pvar var) (Spine sym var pvar) // A rule was strictly partially matched
   | Unsafe (Rgraph sym var)                                      // Terminated due to immininent recursion
   | Redex (Rule sym pvar) (Pfun pvar var)                        // Total match
   | Strict                                                       // Need root normal form due to strictness

// Fold up a spine using a function for each constructor
foldspine
 :: !(var .subresult -> .result)
    .subresult
    .subresult
    (.result -> .subresult)
    .subresult
    ((Rgraph sym pvar) -> .subresult)
    ((Rule sym pvar) (Pfun pvar var) .result -> .subresult)
    ((Rgraph sym var) -> .subresult)
    ((Rule sym pvar) (Pfun pvar var) -> .subresult)
    .subresult
    .(Spine sym var pvar)
 -> .result

// Get the tip of a spine,
// i.e. the last part when all Partial's and Force's are stripped.
spinetip :: !(Spine sym var pvar) -> Spine sym var pvar

// Get the main nodes of a spine,
// i.e. where the spine constructors are applied
// (not the matched nodes of partial matchings)
spinenodes :: .(Spine sym var pvar) -> [var]

// Make a decision (continuation based) on whether a spine ends in Open
ifopen :: result result !.(Answer sym var pvar) -> result
