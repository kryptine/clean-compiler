implementation module law

/*

>   %export
>       cleanlaws
>       corestrategy

>   %include "dnc.lit"

>   %include "../src/basic.lit"
>   %include "../src/pfun.lit"
>   %include "../src/graph.lit"
>   %include "../src/complete.lit"
>   %include "../src/rule.lit"
>   %include "../src/spine.lit"
>   %include "strat.lit"
>   %include "../src/clean.lit"

>   intmullaw :: law symbol ** node ****

>   intmullaw substrat subject found rnf sargs fail

>   =   rulelaw (leftunitrule (Int 1)) substrat subject found rnf sargs fail'
>       where fail' = rulelaw (rightunitrule (Int 1)) substrat subject found rnf sargs fail''
>             fail'' = primlaw (intop product) substrat subject found rnf sargs fail

>   mullaws
>   =   [   rulelaw (leftunitrule (Int 1))
>       ,   rulelaw (rightunitrule (Int 1))
>       ,   primlaw (intop product)
>       ]

>   intaddlaw :: law symbol ** node ****

>   intaddlaw substrat subject found rnf sargs fail
>   =   trylaw subject found' sargs (leftunitrule (Int 0)) fail'
>       where fail' = trylaw subject found' sargs (rightunitrule (Int 0)) fail''
>             fail'' = strictprimop (intop sum) substrat subject found sargs fail
>             found' subspine = found subspine

>   addlaws
>   =   [   rulelaw (leftunitrule (Int 0))
>       ,   rulelaw (rightunitrule (Int 0))
>       ,   primlaw (intop sum)
>       ]

>   intsublaw :: law symbol ** node ****

>   intsublaw substrat subject found rnf sargs fail
>   =   trylaw subject found' sargs (rightunitrule (Int 0)) fail'
>       where fail' = strictprimop (intop sublist) substrat subject found sargs fail
>             found' subspine = found subspine
>             sublist [x,y] = x-y

>   sublaws
>   =   [   rulelaw (rightunitrule (Int 0))
>       ,   primlaw (intop sublist)
>       ]
>       where sublist [x,y] = x-y

>   intop :: ([num]->num) -> [symbol] -> symbol
>   intop op symbols = Int (op [i|Int i<-symbols])

>   leftunitrule leftunit
>   =   mkrule [Named "leftarg",Named "rightarg"] (Named "rightarg") (updategraph (Named "leftarg") (leftunit,[]) emptygraph)

>   rightunitrule rightunit
>   =   mkrule [Named "leftarg",Named "rightarg"] (Named "leftarg") (updategraph (Named "rightarg") (rightunit,[]) emptygraph)

>   strictprimop
>   ::  ([*]->*) ->
>       substrategy * ** node **** ->
>       graph * ** ->
>       (subspine * ** node->****) ->
>       [**] ->
>       **** ->
>       ****

>   strictprimop op substrat subject found sargs fail
>   =   forcenodes substrat found foundredex sargs, if and (map fst conts)
>   =   fail, otherwise
>       where conts = map (dnc (const "in strictprimop") subject) sargs
>             result = op (map (fst.snd) conts)
>             primrule = mkrule primargs primroot primgraph
>             primargs = map snd (zip2 sargs heap)
>             primroot = Named "primresult"
>             primgraph = updategraph primroot (result,[]) emptygraph
>             matching = foldr (uncurry extend) emptypfun (zip2 primargs sargs)
>             foundredex = found (Redex primrule matching)

>   primlaw
>   ::  ([*]->*) ->
>       law * ** node ****

>   primlaw op substrat subject found rnf sargs fail
>   =   strictprimop op substrat subject found sargs fail

------------------------------------------------------------------------

>   cleanlaws :: [(symbol,law symbol ** node ****)]

>   cleanlaws
>   =   [(User "deltaI" "*",law) | law <- mullaws] ++
>       [(User "deltaI" "+",law) | law <- addlaws] ++
>       [(User "deltaI" "-",law) | law <- sublaws] ++
>       [(User "deltaI" "++",primlaw inc)] ++
>       [(User "deltaI" "--",primlaw dec)]

>   inc [Int n] = Int (n+1)
>   dec [Int n] = Int (n-1)

------------------------------------------------------------------------

>   corestrategy :: (graph symbol node->node->**->bool) -> strategy symbol ** node ****

Forcing arguments has already been done by the type rule
Also, using trylaw is easier

>   corestrategy matchable substrat subject found rnf (Apply,snodes)
>   =   trylaw subject found snodes (applyrule nc) (found Delta)
>       where nc = dnc (const "in corestrategy") subject (hd snodes)

>   corestrategy matchable substrat subject found rnf (If,snodes)
>   =   tryrules matchable substrat subject found snodes (found MissingCase) ifrules

>   corestrategy matchable substrat subject found rnf (Select a i,snodes)
>   =   tryrules matchable substrat subject found snodes (found MissingCase) [selectrule a i]

>   corestrategy matchable substrat subject found rnf (User module id,snodes)
>   =   found MissingCase

>   corestrategy matchable substrat subject found rnf (ssym,snodes)
>   =   rnf

>   applyrule :: (bool,(*,[**])) -> rule * node
>   applyrule (sdef,scont)
>   =   aprule (anode,(sym,aargs)) [enode] aroot
>       where (aargs,anode:aroot:enode:heap') = claim sargs heap
>             (sym,sargs)
>             =   scont, if sdef
>             =   (nosym,[]), otherwise
>             nosym = error "applyrule: no function symbol available"

>   aprule :: (***,(*,[***])) -> [***] -> *** -> rule * ***
>   aprule (anode,(sym,aargs)) anodes aroot
>   =   mkrule (anode:anodes) aroot agraph
>       where agraph
>             =   (   updategraph aroot (sym,aargs++anodes)
>                 .   updategraph anode (sym,aargs)
>                 ) emptygraph

>   apmatching :: [**] -> [***] -> pfun *** **
>   apmatching snodes anodes
>   =   foldr (uncurry extend) emptypfun nodepairs
>       where nodepairs = zip2 anodes snodes

>   claims :: [[*]] -> [**] -> ([[**]],[**])
>   claims [] heap = ([],heap)
>   claims (nodes:nodess) heap
>   =   (nodes':nodess',heap'')
>       where (nodes',heap') = claim nodes heap
>             (nodess',heap'') = claims nodess heap'

>   ifrules :: [rule symbol node]

>   ifrules
>   =   [ifrule True then,ifrule False else]
>       where ifrule bool branch = mkrule [cond,then,else] branch (updategraph cond (Bool bool,[]) emptygraph)
>             cond = Named "cond"; then = Named "then"; else = Named "else"

>   selectrule :: num -> num -> rule symbol node

>   selectrule a i
>   =   mkrule [tuple] (args!(i-1)) (updategraph tuple (Tuple a,args) emptygraph)
>       where tuple = Named "tuple"
>             args = take a (tl heap)

*/
