implementation module strat

import history
import spine
import dnc
import rule
import graph
import pfun
import basic
import StdEnv

/*

strat.lit - Extended functional strategy
========================================

Description
-----------

Describe in a few paragraphs what this module defines.

------------------------------------------------------------

Interface
---------

Exported identifiers:

>   %export

>       law
>       strategy
>       substrategy

>       makernfstrategy

>       checkconstr
>       checkimport
>       checklaws
>       checkrules
>       checktype

>       forcenodes
>       rulelaw
>       trylaw
>       tryrules

Required types:

    identifier - type@source.lit type@source.lit
    ...

------------------------------------------------------------

Includes
--------

>   %include "dnc.lit"

>   %include "../src/basic.lit"
>   %include "../src/pfun.lit"
>   %include "../src/graph.lit" -instantiate
>   %include "../src/rule.lit"
>   %include "../src/spine.lit"

------------------------------------------------------------

Types
-----

*/

:: Substrategy sym var pvar result
   :== ((Spine sym var pvar) -> result)
       result
       var
   ->  result

:: Strategy sym var pvar result
   :== (Substrategy sym var pvar result)
       (Graph sym var)
       ((Subspine sym var pvar) -> result)
       result
       (Node sym var)
   ->  result

:: Law sym var pvar result
   :== (Substrategy sym var pvar result)
       (Graph sym var)
       ((Subspine sym var pvar) -> result)
       result
       [var]
       result
   ->  result

//------------------------------------------------------------------------

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

makernfstrategy hist strat rnfnodes node graph
= substrat [] spinecont rnfanswer node
  where spinecont spine = Present spine
        rnfanswer = Absent

        substrat spinenodes spinecont rnfanswer node
        | isMember node spinenodes
        = subspinecont Cycle
        | isMember node rnfnodes
        = rnfanswer
        | not def
        = subspinecont Strict
        = strat` (substrat spinenodes`) graph subspinecont rnfanswer cnt
          where (def,cnt) = dnc (const "in makernfstrategy") graph node
                spinenodes` = [node:spinenodes]

                subspinecont subspine = spinecont (node,subspine)

                strat` = checkinstance (graph,node) histpatts strat
                histpatts = foldr (foldmap (++) id hist) [] spinenodes`

/*

------------------------------------------------------------------------
NORMAL REWRITE RULE STRATEGY

*/

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

tryrules matchable substrat subject found sargs
= foldr (matchrule matchable substrat subject found sargs)

matchrule
 :: ((Graph sym pvar) pvar var -> .Bool)
    (Substrategy sym var pvar result)
    .(Graph sym var)
    ((Subspine sym var pvar) -> result)
    .[var]
    .(Rule sym pvar)
    result
 -> result
 |  == sym
 &  == var
 &  == pvar

matchrule matchable substrat subject found sargs rule fail
| eqlen pargs sargs
= matchnodes matchable` subject substrat foundsub fail pattern foundmatch pairs emptypfun
= fail
  where pargs = arguments rule
        pattern = rulegraph rule
        pairs = zip2 pargs sargs
        matchable` = matchable pattern
        foundsub matching spine = found (Partial rule matching spine)
        foundmatch matching = found (Redex rule matching)

matchnodes
 :: (pvar var -> .Bool)
    .(Graph sym var)
    (Substrategy sym var pvar result)
    ((Pfun pvar var) (Spine sym var pvar) -> result)
    result
    .(Graph sym pvar)
 -> ((Pfun pvar var) -> result)
    [.(pvar,var)]
    (Pfun pvar var)
 -> result
 |  == sym
 &  == var
 &  == pvar

matchnodes matchable subject substrat found fail pattern
= foldr matchpair
  where matchpair (pnode,snode) match matching
        | not (matchable pnode snode)
        = fail
        | not pdef
        = match (extend pnode snode matching)
        | not sdef
        = found matching openspine
        = substrat (found matching) rnfanswer snode
          where openspine = (snode,Open (mkrgraph pnode pattern))
                rnfanswer
                | psym==ssym && eqlen pargs sargs
                = foldr matchpair match` psargs matching
                = fail
                match` matching = match (extend pnode snode matching)
                psargs = zip2 pargs sargs
                (pdef,(psym,pargs)) = (dnc (const "in matchnodes (pattern)")) pattern pnode
                (sdef,(ssym,sargs)) = (dnc (const "in matchnodes (subject)")) subject snode

/*

------------------------------------------------------------------------
SPECIAL LAW STRATEGY

Does not try to reduce arguments before matching.

>   rulelaw
>   ::  rule * *** ->
>       law * ** *** ****

>   rulelaw rule substrat subject found rnf snids fail
>   =   trylaw subject found snids rule fail

>   trylaw
>   ::  graph * ** ->
>       (subspine * ** ***->****) ->
>       [**] ->
>       rule * *** ->
>       **** ->
>       ****

>   trylaw graph found sargs rule fail
>   =   lawmatch pattern graph fail found' pairs emptypfun, if eqlen pargs sargs
>   =   fail, otherwise
>       where pargs = lhs rule; pattern = rulegraph rule
>             found' matching = found (Redex rule matching)
>             pairs = zip2 pargs sargs

>   lawmatch
>   ::  graph * *** ->
>       graph * ** ->
>       **** ->
>       (pfun *** **->****) ->
>       [(***,**)] ->
>       pfun *** ** -> ****

>   lawmatch pattern subject fail
>   =   foldr lawmatch'
>       where lawmatch' (pnode,snode) success matching
>             =   success matching', if ~pdef
>             =   fail, if ~sdef \/ ssym~=psym \/ ~eqlen pargs sargs
>             =   foldr lawmatch' success (zip2 pargs sargs) matching', otherwise
>                 where matching' = extend pnode snode matching
>                       (pdef,(psym,pargs)) = (dnc (const "in lawmatch/1")) pattern pnode
>                       (sdef,(ssym,sargs)) = (dnc (const "in lawmatch/2")) subject snode

*/

rulelaw
 :: .(Rule sym pvar)
 -> Law sym var pvar result
 |  == sym
 &  == var
 &  == pvar

rulelaw rule
= law
where law substrat subject found rnf snids fail
      = trylaw subject found snids rule fail

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

trylaw graph found sargs rule fail
| eqlen pargs sargs
= lawmatch pattern graph fail found` pairs emptypfun
= fail
  where pargs = arguments rule; pattern = rulegraph rule
        found` matching = found (Redex rule matching)
        pairs = zip2 pargs sargs

lawmatch
 :: .(Graph sym pvar)
    .(Graph sym var)
    result
 -> ((Pfun pvar var) -> result)
    [.(pvar,var)]
    (Pfun pvar var)
 -> result
 |  == sym
 &  == var
 &  == pvar

lawmatch pattern subject fail
= foldr lawmatch`
  where lawmatch` (pnode,snode) success matching
        | not pdef
        = success matching`
        | not sdef || ssym <> psym || not (eqlen pargs sargs)
        = fail
        = foldr lawmatch` success (zip2 pargs sargs) matching`
          where matching` = extend pnode snode matching
                (pdef,(psym,pargs)) = (dnc (const "in lawmatch (pattern)")) pattern pnode
                (sdef,(ssym,sargs)) = (dnc (const "in lawmatch (subject)")) subject snode

/*

------------------------------------------------------------------------
FORCING EVALUATION OF (STRICT) ARGUMENTS

*/

forcenodes
 :: (Substrategy .sym .var .pvar .result)
    ((Subspine .sym .var .pvar) -> .result)
    .result
    ![.var]
 -> .result

forcenodes substrat found rnf nodes
= foldr forcenode rnf nodes
  where forcenode nid rnfrest = substrat foundforce rnfrest nid
        foundforce spine = found (Force spine)

/*

------------------------------------------------------------------------
STRATEGY COMPOSITION

Check for an instance in the termination history.

*/

checkinstance
 :: (.Graph sym var,var)
    [.Rgraph sym var]
    (Strategy sym var .pvar result)
 -> Strategy sym var .pvar result
 |  == sym
 &  == var
 &  == pvar

checkinstance (graph,node) history defaultstrategy
= foldr check defaultstrategy history
  where check hrgraph defaultstrategy substrat subject found rnf (ssym,sargs)
        | isinstance (hgraph,hroot) (graph,node)
        = found (Unsafe hrgraph)
        = defaultstrategy substrat subject found rnf (ssym,sargs)
          where hgraph = rgraphgraph hrgraph; hroot = rgraphroot hrgraph


// Check a type rule for curried applications and strict arguments

checktype
 :: !(sym -> (Rule .tsym tvar,[.Bool]))
    (Strategy sym var .pvar .result)
    (Substrategy sym var .pvar .result)
    .(Graph sym var)
    ((Subspine sym var .pvar) -> .result)
    .result
    !.(Node sym var)
 -> .result

checktype typeinfo defaultstrategy substrat subject found rnf (ssym,sargs)
| shorter targs sargs
= rnf
| eqlen targs sargs
= forcenodes substrat found rnf` strictnodes
= abort "checktype: symbol occurrence with arity greater than its type"
  where rnf` = defaultstrategy substrat subject found rnf (ssym,sargs)
        (trule,tstricts) = typeinfo ssym
        targs = arguments trule
        strictnodes = [sarg\\(True,sarg)<-zip2 tstricts sargs]


// Check (hard coded) laws

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

checklaws laws defaultstrategy substrat subject found rnf (ssym,sargs)
= foldr checklaw (defaultstrategy substrat subject found rnf (ssym,sargs)) laws
  where checklaw (lsym,law) fail
        | lsym==ssym
        = law substrat subject found rnf sargs fail
        = fail


// Check a list of rewrite rules (this is the real thing)

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

checkrules matchable ruledefs defstrat substrat subject found rnf (ssym,sargs)
= tryrules matchable substrat subject found sargs fail (ruledefs ssym)
  where fail = defstrat substrat subject found rnf (ssym,sargs)


// Check for delta/imported/abstract/black-box (whatever) symbols

checkimport
 :: !(sym->.Bool)
    (Strategy sym .var .pvar .result)
    (Substrategy sym .var .pvar .result)
    (Graph sym .var)
    ((Subspine sym .var .pvar) -> .result)
    .result
    (Node sym .var)
 -> .result

checkimport local defstrat substrat subject found rnf (ssym,sargs)
| not (local ssym)
= found Delta
= defstrat substrat subject found rnf (ssym,sargs)


// Check for constructors

checkconstr
 :: (sym->.Bool)
    (Strategy sym .var .pvar .result)
    (Substrategy sym .var .pvar .result)
    (Graph sym .var)
    ((Subspine sym .var .pvar) -> .result)
    .result
    (Node sym .var)
 -> .result

checkconstr isconstr defstrat substrat subject found rnf (ssym,sargs)
| isconstr ssym
= rnf
= defstrat substrat subject found rnf (ssym,sargs)
