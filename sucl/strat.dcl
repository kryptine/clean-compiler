definition module strat

// $Id$

from history import History
from spine import Answer
from rule import Rule
from graph import Graph,Node
from StdOverloaded import ==

from spine import Spine    // for Answer
from spine import Subspine // for Spine
from rule import Rgraph    // for History
from basic import Optional // for Spine

:: Strategy sym var pvar result
   :== (Substrategy sym var pvar result)
       (Graph sym var)
       ((Subspine sym var pvar) -> result)
       result
       (Node sym var)
   ->  result

:: Substrategy sym var pvar result
   :== ((Spine sym var pvar) -> result)
       result
       var
   ->  result

:: Law sym var pvar result
   :== (Substrategy sym var pvar result)
       (Graph sym var)
       ((Subspine sym var pvar) -> result)
       result
       [var]
       result
   ->  result

// Apply a strategy recursively to a graph
// by deriving the substrategy from it and feeding it back to it
// Think Y operator
makernfstrategy
 :: .(History sym var)                            // History of previous rooted graphs attached to nodes
    (Strategy sym var pvar (Answer sym var pvar)) // Strategy for a defined node
    .[var]                                        // List of nodes known in RNF (closed pattern nodes of subject rule+strict args)
    var                                           // Root of replacement
    .(Graph sym var)                              // Subject graph
 -> Answer sym var pvar
 |  == sym
 &  == var
 &  == pvar


/* ------------------------------------------------------------------------
STRATEGY TRANSFORMERS
The funcions below tranform (simpler) strategies into more complicated ones
------------------------------------------------------------------------ */

// A strategy transformer that checks for constructor applications
checkconstr
 :: (sym->.Bool)
    (Strategy sym .var .pvar .result)
    (Substrategy sym .var .pvar .result)
    (Graph sym .var)
    ((Subspine sym .var .pvar) -> .result)
    .result
    (Node sym .var)
 -> .result

// A strategy transformer that checks for primitive symbol applications
checkimport
 :: !(sym->.Bool)
    (Strategy sym .var .pvar .result)
    (Substrategy sym .var .pvar .result)
    (Graph sym .var)
    ((Subspine sym .var .pvar) -> .result)
    .result
    (Node sym .var)
 -> .result

// A strategy transformer that checks (hard coded) laws
checklaws
 :: [(sym,Law sym var pvar result)]
    (Strategy sym var pvar result)
    (Substrategy sym var pvar result)
    (Graph sym var)
    ((Subspine sym var pvar) -> result)
    result
    (Node sym var)
 -> result
 |  == sym

// A strategy transformere that checks a list of rewrite rules
// This is the real thing that characterises the functional strategy
checkrules
 :: ((Graph sym pvar) pvar var -> .Bool)
    (sym -> [.Rule sym pvar])
    (Strategy sym var pvar result)
    (Substrategy sym var pvar result)
    (Graph sym var)
    ((Subspine sym var pvar) -> result)
    result
    (Node sym var)
 -> result
 |  == sym
 &  == var
 &  == pvar

// A strategy transformer that checks a type rule
// for curried applications and strict arguments
checktype
 :: !(sym -> (Rule .tsym tvar,[.Bool]))
    (Strategy sym var .pvar .result)
    (Substrategy sym var .pvar .result)
    .(Graph sym var)
    ((Subspine sym var .pvar) -> .result)
    .result
    !.(Node sym var)
 -> .result

/* ------------------------------------------------------------------------
USEFUL AIDS FOR DEFINING STRATEGY TRANSFORMERS
The functions below are useful for inspecting a graph
such as done by a strategy transformer.
------------------------------------------------------------------------ */

// Force evaluation of stricts arguments of a node in the graph
forcenodes
 :: (Substrategy .sym .var .pvar .result)
    ((Subspine .sym .var .pvar) -> .result)
    .result
    ![.var]
 -> .result

// Try to apply a transformation rule (that doesn't need evaluated arguments)
rulelaw
 :: .(Rule sym pvar)
 -> Law sym var pvar result
 |  == sym
 &  == var
 &  == pvar

// Try to apply a law
trylaw
 :: .(Graph sym var)
    (.(Subspine sym var pvar) -> result)
    .[var]
    .(Rule sym pvar)
    result
 -> result
 |  == sym
 &  == var
 &  == pvar

// Try a list of rewrite rules
// Requires argument evaluation for closed patterns
tryrules
 :: ((Graph sym pvar) pvar var -> .Bool)
    (Substrategy sym var pvar result)
    .(Graph sym var)
    ((Subspine sym var pvar) -> result)
    .[var]
 -> result
    [.Rule sym pvar]
 -> result
 |  == sym
 &  == var
 &  == pvar
