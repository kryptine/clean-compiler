implementation module newtest

// $Id$

import cli
import coreclean
import newfold
import complete
import trd
import loop
import trace
import rule
import graph
import canon
import basic
import StdEnv

/*

newtest.lit - Testing the new trace implementation
==================================================

Description
-----------

Describe in a few paragraphs what this module defines.

------------------------------------------------------------

Interface
---------

Exported identifiers:

>   %export
>       all       ||  List of all clasp modules
>       list      ||  List a clean module
>       listopt   ||  List rules with introduction
>       listfull  ||  List full processing of optimization
>||     listtrace ||  List the trace for a clean module
>       optfiles  ||  Optimize files obeying a pattern
>       optimize  ||  Optimize a clean module

Required types:

    identifier - type@source.lit type@source.lit
    ...

------------------------------------------------------------

Includes
--------

>   %include "dnc.lit"

>   %include "../src/basic.lit"
>   %include "../src/hunt.lit"
>   %include "../src/pfun.lit"
>   %include "../src/graph.lit"
>   %include "../src/rule.lit"
>   %include "../src/trd.lit"
>   %include "../src/spine.lit"
>   %include "strat.lit"
>   %include "trace.lit"
>   %include "loop.lit"
>   %include "../src/clean.lit"
>   %include "../src/module.lit"
>   %include "cli.lit"
>   %include "../src/complete.lit"
>|| %include "fold.lit"
>   %include "newfold.lit"
>   %include "../src/canon.lit"

------------------------------------------------------------

Implementation
--------------

------------------------------------------------------------------------

>   optfiles :: [char] -> [sys_message]
>   optfiles
>   =   optimize.foldr addmodule [].glob.join ' '.expand [".cli"] (getpath ["."] "CLIPATH")

>   addmodule filename modules
>   =   subcli scont filename
>       where subcli success ".cli" = success ""
>             subcli success ('/':cs) = subcli scont cs
>             subcli success (c:cs) = subcli (success.(c:)) cs
>             subcli success cs = modules
>             scont = (:modules)

>   all = (foldr addmodule [].glob.join ' '.expand [".cli"] (getpath ["."] "CLIPATH")) "*"

>   optimize :: [[char]] -> [sys_message]

>   optimize modules
>   =   complaints++loads++concat (map optone goodnames)++[Stdout "Done.\n",Exit (#complaints)]
>       where allnames = [(module,findfiles readable [".cli"] (getpath ["."] "CLIPATH") module)|module<-modules]
>             badnames = [module|(module,[])<-allnames]
>             goodnames = [(module,cliname,init cliname++"o")|(module,cliname:clinames)<-allnames]
>             complaints
>             =   [], if badnames=[]
>             =   [Stderr ("Warning: cannot find module"++showmodules badnames++" (ignored).\n")], otherwise
>                 where showmodules [module]
>                       =   ": "++showstring module
>                       showmodules modules
>                       =   "s: "++join ',' (map showstring modules)
>             loads
>             =   [], if goodnames=[]
>             =   [Stdout ("Loaded modules: "++join ',' [module|(module,cli,clo)<-goodnames]++".\n")], otherwise
>             cli = loadclis (map snd3 goodnames)
>             optone (module,cliname,cloname)
>             =   [   Stdout ("Optimizing "++module++" ("++showstring cliname++") to "++show cloname++"..."),
>                     Tofile cloname (listnew module cli),
>                     Stdout "\n"
>                 ]

------------------------------------------------------------------------

`Newfunction' is the  type  of  a  new  function  produced  by  symbolic
reduction  applied  to a cli module.  Symbolic reduction on a cli module
actually produces a list of new functions.

>   newfunction * ** **** *****
>   ==  (   *,                ||  Assigned symbol of the new function
>           rule * **,        ||  Initial rule of the new function
>           [bool],           ||  Strictness annotations
>           rule **** *****,  ||  Type rule
>           bool,             ||  Export annotation
>           [rule * **],      ||  Rewrite rules
>           bool              ||  Import annotation
>       )

`Symredresult' is the output produced by symbolic reduction  applied  to
an  area.   Symbolic  reduction  on  an area actually produces a list of
these tuples.

>   symredresult * ** **** *****
>   ==  (   rgraph * **,      ||  The initial area in canonical form
>           *,                ||  The assigned symbol
>           [bool],           ||  Strictness annotations
>           rule **** *****,  ||  Type rule
>           trace * ** **,    ||  Truncated and folded trace
>           [rule * **],      ||  Resulting rewrite rules
>           [rgraph * **]     ||  New areas for further symbolic reduction (not necessarily canonical)
>       )
*/

:: Symredresult sym var tsym tvar
   :== ( Rgraph sym var    // The initial area in canonical form
       , sym               // The assigned symbol
       , [Bool]            // Strictness annotations
       , Rule tsym tvar    // Type rule
       , Trace sym var var // Truncated and folded trace
       , [Rule sym var]    // Resulting rewrite rules
       , [Rgraph sym var]  // New areas for further symbolic reduction (not necessarily canonical)
       )

/*
>   listopt :: [char] -> [[char]] -> [char]

>   listopt main = listnew main.loadclis

>   listnew :: [char] -> cli -> [char]

>   listnew main cli = (lay.printnew cli.map (makenew cli).filter hasusersym.fullsymred main.stripexports main) cli

>   printnew
>   ::  cli ->
>       [newfunction symbol node typesymbol typenode] ->
>       [[char]]

>   printnew cli results
>   =   (implementation exports++"MODULE "++modulename++";"):
>       prefix [""] (showimports [symbol|(symbol,initialrule,stricts,trule,exported,rules,True)<-results])++
>       showtypes ((map (uncurry cleanalias).aliases) cli) (map (printalgebra (typerule cli)) (constrs cli))++
>       prefix ["","MACRO"] ((concat.map (uncurry cleanmacro).macros) cli)++
>       concat (map (shownewrules cli) [(symbol,initialrule,(trule,stricts),rules)|(symbol,initialrule,stricts,trule,exported,rules,imported)<-results;rules~=[]])
>       where exports = [symbol|(symbol,initialrule,stricts,trule,True,rules,imported)<-results]
>             implementation [User module "Start"] = ""
>             implementation exports = "IMPLEMENTATION "
>             getmodule (User module ident) = module
>             modulename = hd (map getmodule exports++["empty"])

>   showimports symbols
>   =   map showblock (partition getmodule getident symbols)
>       where getmodule (User module ident) = module
>             getident (User module ident) = ident
>             showblock (module,idents)
>             =   "FROM "++module++" IMPORT "++join ',' idents++";"

>   showtypes aliastexts algebralines
>   =   prefix ["","TYPE"] (prefix [""] (concat aliastexts)++prefix [""] algebralines)

>   prefix xs [] = []
>   prefix xs ys = xs++ys

>   shownewrules cli (symbol,initialrule,tinfo,rules)
>   =   prefix ("":"<<":cleanrule symbol initialrule++[">>","RULE"]) (cleantyperule symbol tinfo:concat (map (cleanrule symbol) rules))

>   makenew
>   ::  cli ->
>       symredresult symbol node typesymbol typenode ->
>       newfunction symbol node typesymbol typenode

>   makenew cli (area,symbol,stricts,trule,Trace initialstricts initialrule answer history results,rules,areas)
>   =   (symbol,initialrule,stricts,trule,exported,rules',imported)
>       where exported = member (exports cli) symbol
>             imported = member (imports cli) symbol
>             rules' = filter ((~).unchanged) rules
>             unchanged rule
>             =   def & root=initialroot & sym=symbol
>                 where root = rhs rule; graph = rulegraph rule
>                       (def,(sym,args')) = dnc (const "in makenew") graph root
>             initialroot = rhs initialrule

>   hasusersym
>   ::  symredresult symbol node typesymbol typenode ->
>       bool

>   hasusersym (area,symbol,stricts,trule,trace,rules,areas) = usersym symbol

------------------------------------------------------------------------

>   listfull :: [char] -> [[char]] -> [char]
>   listfull main filenames
>   =   (lay.map (showfull cli).fullsymred main) cli
>       where cli = stripexports main (loadclis (main:filenames))

>   showfull
>   ::  cli ->
>       symredresult symbol node typesymbol typenode ->
>       [char]

>   showfull cli (area,symbol,stricts,trule,trace,rules,areas)
>   =   hline++
>       "::: AREA :::\n"++
>       printrgraph showsymbol shownode area++
>       "\n\n::: ASSIGNED SYMBOL :::\n"++
>       showsymbol symbol++
>       "\n\n::: DERIVED TYPE RULE :::\n"++
>       printrule showtypesymbol showtypenode trule++
>       "\n\n::: TRACE :::\n"++
>       lay (printtrace symbol showsymbol shownode shownode trace)++
>       "\n\n::: DERIVED STRICTNESS :::\n"++
>       map strictchar stricts++
>       "\n::: RULES :::\n"++
>       lay (map (((showsymbol symbol++" ")++).printrule showsymbol shownode) rules)++
>       "\n::: NEW AREAS :::\n"++
>       lay (map (printrgraph showsymbol shownode) areas)++
>       hline

>   hline = rep 72 '='++"\n"

>   fullsymred
>   ::  [char] ->
>       cli ->
>       [symredresult symbol node typesymbol typenode]

>   fullsymred main cli
>   =   results
>       where results = depthfirst generate process (initareas cli)
>             generate result = map canonise' (getareas result)
>             process area = symredarea foldarea' cli area

>             foldarea' = foldarea (labelarea'.canonise')
>             labelarea' = labelarea (map getinit results) (newsymbols main)
>             canonise' = canonise (typerule cli) heap
*/

fullsymred ::
    [SuclSymbol]    // Fresh function symbols
    Cli             // Module to optimise
 -> [Symredresult SuclSymbol SuclVariable SuclTypeSymbol SuclTypeVariable]

fullsymred freshsymbols cli
 = results
   where results = depthfirst generate process (initareas cli)
         generate result = map canonise` (getareas result)
         process area = symredarea foldarea` cli area

         foldarea` = foldarea (labelarea` o canonise`)
         labelarea` = labelarea (map getinit results) freshsymbols
         canonise` = canonise (typerule cli) suclheap

/*
`Initareas cli' is the list  of  initial  rooted  graphs  that  must  be
symbolically  reduced.  An initial rooted graph is formed by applying an
exported symbol to its full complement of open  arguments  according  to
its type rule.

>   initareas :: cli -> [rgraph symbol node]

>   initareas cli
>   =   map (initialise heap) (exports cli)
>       where initialise (root:nodes) symbol
>             =   mkrgraph root (updategraph root (symbol,args) emptygraph)
>                 where args = map2 const nodes targs
>                       targs = lhs (typerule cli symbol)

>   getinit :: symredresult * ** **** ***** -> rgraph * **
>   getinit (area,symbol,stricts,trule,trace,rules,areas) = area

>   getareas :: symredresult * ** **** ***** -> [rgraph * **]
>   getareas (area,symbol,stricts,trule,trace,rules,areas) = areas
*/

initareas :: Cli -> [Rgraph SuclSymbol SuclVariable]
initareas cli
= map (initialise suclheap) (exports cli)
  where initialise [root:nodes] symbol
        = mkrgraph root (updategraph root (symbol,args) emptygraph)
          where args = map2 const nodes targs
                targs = arguments (typerule cli symbol)

getinit :: (Symredresult sym var tsym tvar) -> Rgraph sym var
getinit (area,symbol,stricts,trule,trace,rules,areas) = area

getareas :: (Symredresult sym var tsym tvar) -> [Rgraph sym var]
getareas (area,symbol,stricts,trule,trace,rules,areas) = areas

/*
`Symredarea' is the function that does symbolic reduction  of  a  single
area.

>   symredarea
>   ::  (rgraph symbol node->(symbol,[node])) ->
>       cli ->
>       rgraph symbol node ->
>       symredresult symbol node typesymbol typenode

>   symredarea foldarea cli area
>   =   (area,symbol,stricts,trule,trace,rules,areas)
>       where agraph = rgraphgraph area; aroot = rgraphroot area
>             (symbol,aargs) = foldarea area
>             arule = mkrule aargs aroot agraph
>             trule = ruletype typeheap (ctyperule FN typeheap (typerule cli)) arule
>             trace = loop strategy' complete' matchable' (heap--nodelist agraph [aroot],arule)
>             (stricts,rules,areas) = fullfold (trc symbol) foldarea symbol trace
>             complete' = (~).converse matchable' (mkrgraph () emptygraph)
>             matchable' = matchable (complete cli)
>             strategy' = clistrategy cli
*/

:: Unit = Unit

symredarea ::
    ((Rgraph SuclSymbol SuclVariable)->(SuclSymbol,[SuclVariable]))
    Cli
    (Rgraph SuclSymbol SuclVariable)
 -> Symredresult SuclSymbol SuclVariable SuclTypeSymbol SuclTypeVariable

symredarea foldarea cli area
= (area,symbol,stricts,trule,trace,rules,areas)
  where agraph = rgraphgraph area; aroot = rgraphroot area
        (symbol,aargs) = foldarea area
        arule = mkrule aargs aroot agraph
        trule = ruletype sucltypeheap (ctyperule SuclFN sucltypeheap (typerule cli)) arule
        trace = loop strategy` matchable` (removeMembers suclheap (varlist agraph [aroot]),arule)
        (stricts,rules,areas) = fullfold (trc symbol) foldarea symbol trace
        matchable` = matchable (complete cli)
        strategy` = clistrategy cli

/*
>   trc :: symbol -> trace symbol node node -> rgraph symbol node -> bool -> bool

>   trc symbol trace area recursive
>   =   error (lay ("Trace is recursive in area":printrgraph showsymbol shownode area:printtrace symbol showsymbol shownode shownode trace)), if esymbol symbol & recursive
>   =   recursive, otherwise
*/

trc symbol trace area recursive = recursive

/*
>   esymbol (User m "E") = True
>   esymbol symbol = False

------------------------------------------------------------------------

>   printelem symbol (result,optsra)
>   =   (   indent "subtrace: " (printresult symbol showsymbol shownode shownode result)++
>           foldoptional [] printsra optsra
>       )

>   printsra (stricts,rules,areas)
>   =   (   ("stricts: "++map strictchar stricts):
>           indent "rules: " (map (showrule showsymbol shownode) rules)++
>           indent "areas: " (map (showrgraph showsymbol shownode) areas)
>       )

>   printsras (strictss,rules,areas)
>   =   (   showlist (showstring.map strictchar) strictss:
>           indent "rules: " (map (showrule showsymbol shownode) rules)++
>           indent "areas: " (map (showrgraph showsymbol shownode) areas)
>       )

>   trsym (User module "New_ab") = True
>   trsym = const False

>   looping :: * -> rule * ** -> bool
>   looping symbol rule
>   =   rdef & rsym=symbol & rargs=args
>       where args = lhs rule; root = rhs rule; graph = rulegraph rule
>             (rdef,(rsym,rargs)) = dnc (const "in looping") graph root

------------------------------------------------------------------------

    listtrace :: [char] -> [[char]] -> [char]
    listtrace main = lay.map clitraces.mktraces.stripexports main.loadclis.(main:)

>   clitraces :: (symbol,(trace symbol node node,[rule symbol node])) -> [char]
>   clitraces (sym,(trace,rules)) = lay (printtrace sym showsymbol shownode shownode trace)

    mktraces :: cli -> [(symbol,(trace symbol node node,[rule symbol node]))]
    mktraces cli
    =   depthfirst
        (   foldr addsymbols [].
            snd.
            snd
        )
        (pairwith clisymred')
        (exports cli)
        where clisymred' symbol
              =   clisymred ((~=hd heap).rhs) cli symbol (initrule heap (lhs.typerule cli) symbol)

>   addsymbols :: rule * *** -> [*] -> [*]
>   addsymbols rule rest
>   =   foldr (addsymbol.dnc (const "in addsymbols") rgraph) rest nodes
>       where nodes = nodelist rgraph (rroot:lroots)
>             rgraph = rulegraph rule
>             rroot = rhs rule
>             lroots = lhs rule
>             addsymbol (def,(sym,args)) = cond def (sym:) id

------------------------------------------------------------------------

>   list :: [char] -> [[char]] -> [char]

>   list main = showcli.stripexports main.loadclis.(main:)

------------------------------------------------------------------------

    clisymred :: (rule symbol **->bool) -> cli -> symbol -> ([**],rule symbol **) -> (trace symbol ** node,[rule symbol **])

    clisymred unchanged cli symbol rule
    =   (   mapsnd (filter unchanged)
        .   pairwith tips
        .   onresults (foldtrace symbol)
        .   loop strategy' complete' matchable'
        ) rule
        where complete'
              =   (~).converse matchable' (mkrgraph () emptygraph)
              matchable' = matchable (complete cli)
              strategy' = clistrategy cli

>   matchable :: ([*]->bool)->[rgraph * ***]->rgraph * **->bool

>   matchable complete patterns rgraph
>   =   ~coveredby complete (rgraphgraph rgraph) [(rgraphgraph pattern,[rgraphroot pattern])|pattern<-patterns] [rgraphroot rgraph]
*/

matchable ::
    ([sym]->Bool)
    [Rgraph sym pvar]
    (Rgraph sym var)
 -> Bool
 |  == sym
 &  == var
 &  == pvar
matchable complete patterns rgraph
= not (coveredby complete (rgraphgraph rgraph) [(rgraphgraph pattern,[rgraphroot pattern]) \\ pattern<-patterns] [rgraphroot rgraph])

/*
------------------------------------------------------------------------

`Ctyperule' cli (sym,args)' is the typerule of an occurrence  of  symbol
sym with the given arguments, curried if there are too few.

>   ctyperule
>   ::  **** ->
>       [*****] ->
>       (*->rule **** *****) ->
>       (*,[**]) ->
>       rule **** *****

>   ctyperule fn typeheap typerule (sym,args)
>   =   mkrule targs' troot' tgraph'
>       where targs = lhs trule; troot = rhs trule; tgraph = rulegraph trule
>             trule = typerule sym
>             (targs',targs'') = claim args targs
>             (troot',tgraph',theap') = foldr build (troot,tgraph,typeheap--nodelist tgraph (troot:targs)) targs''
>             build targ (troot,tgraph,tnode:tnodes)
>             =   (tnode,updategraph tnode (fn,[targ,troot]) tgraph,tnodes)
*/

ctyperule ::
    (Int -> tsym)           // The arrow type symbol for functions of given arity
    [tvar]                  // Fresh type variables
    (sym->Rule tsym tvar)   // Type rule of a symbol
    (sym,[var])             // Node to abstract
 -> Rule tsym tvar
 |  == tvar

ctyperule fn typeheap typerule (sym,args)
= mkrule targs` troot` tgraph`
  where targs = arguments trule; troot = ruleroot trule; tgraph = rulegraph trule
        trule = typerule sym
        (targs`,targs``) = claim args targs
        (troot`,tgraph`,_) = foldr build (troot,tgraph,removeMembers typeheap (varlist tgraph [troot:targs])) targs``
        build targ (troot,tgraph,[tnode:tnodes])
        = (tnode,updategraph tnode (fn 1,[targ,troot]) tgraph,tnodes)

/*
>   newsymbols main = map (User main.("New_"++)) identifiers
*/
