implementation module cli

// $Id$

import law
import coreclean
import strat
import absmodule
import rule
import dnc
import basic
import general
import StdEnv

/*

cli.lit - Clean implementation modules
======================================

Description
-----------

This script implements Clean modules (type  module)  and  partial  Clean
programs (type cli), which are essentially sets of Clean modules.

------------------------------------------------------------

Interface
---------

Exported identifiers:

>   %export
>       cli
>       readcli
>       loadclis
>       exports
>       typerule
>       imports
>       clistrategy
>       constrs
>       complete
>       showcli
>       printcli
>       aliases
>       macros
>       stripexports

>       printalgebra

Required types:

    identifier - type@source.lit type@source.lit
    ...

------------------------------------------------------------

Includes
--------

>   %include "dnc.lit"

>   %include "../src/basic.lit"
>   %include "../src/pfun.lit"
>   %include "../src/graph.lit"
>   %include "../src/rule.lit"
>   %include "../src/spine.lit"
>   %include "strat.lit"
>   %include "law.lit"
>   %include "../src/clean.lit"
>   %include "../src/module.lit"


------------------------------------------------------------

Implementation
--------------

Implementation of identifier

    identifier
    ::  type

    identifierone arguments
    =   body

...

------------------------------------------------------------------------

Abstype implementation.

>   abstype cli
>   with readcli :: [char] -> cli
>        loadclis :: [[char]] -> cli
>        exports :: cli -> [symbol]
>        typerule :: cli -> symbol -> rule typesymbol typenode
>        rules :: cli -> symbol -> optional [rule symbol node]
>        imports :: cli -> [symbol]
>        clistrategy :: cli -> (graph symbol node->node->**->bool) -> strategy symbol ** node ****
>        constrs :: cli -> [(typesymbol,[symbol])]
>        complete :: cli -> [symbol] -> bool
>        showcli :: cli -> [char]
>        aliases :: cli -> [(typesymbol,rule typesymbol typenode)]
>        macros :: cli -> [(symbol,rule symbol node)]
>        stripexports :: [char] -> cli -> cli
*/

:: Cli = CliAlias (Module SuclSymbol SuclVariable SuclTypeSymbol SuclTypeVariable)

/*
>   cli == module symbol node typesymbol typenode

>   readcli = compilecli.readcleanparts

>   loadclis
>   =   compilecli.concat.map readcleanparts

>   stripexports main (tdefs,(es,as,ts,rs)) = (tdefs,([User m i|User m i<-es;m=main],as,ts,rs))

>   exports (tdefs,(es,as,ts,rs)) = es
*/

exports :: Cli -> [SuclSymbol]
exports (CliAlias m) = m.exportedsymbols

// Determine the arity of a core clean symbol
arity :: Cli SuclSymbol -> Int
arity (CliAlias m) sym
= extendfn m.arities (length o arguments o (extendfn m.typerules (coretyperule--->"coreclean.coretyperule begins from cli.arity"))) sym

/*
>   typerule (tdefs,(es,as,ts,rs)) = maxtyperule ts
*/

typerule :: Cli SuclSymbol -> Rule SuclTypeSymbol SuclTypeVariable
typerule (CliAlias m) sym
= maxtyperule m.typerules sym

/*
>   rules (tdefs,(es,as,ts,rs)) = foldmap Present Absent rs

>   imports (tdefs,(es,as,ts,rs)) = [sym|(sym,tdef)<-ts;~member (map fst rs) sym]

>   aliases ((tes,tas,tcs),defs) = tas
>   macros (tdefs,(es,as,ts,rs)) = as

>   clistrategy ((tes,tas,tcs),(es,as,ts,rs)) matchable
>   =   (   checktype (maxtypeinfo ts).    ||  Checks curried occurrences and strict arguments
>           checklaws cleanlaws.           ||  Checks for special (hard coded) rules (+x0=x /y1=y ...)
>           checkrules matchable (foldmap id [] rs).
>                                          ||  Checks normal rewrite rules
>           checkimport islocal.           ||  Checks for delta symbols
>           checkconstr (member (concat (map snd tcs)))
>                                          ||  Checks for constructors
>       ) (corestrategy matchable)         ||  Checks rules for symbols in the language core (IF, _AP, ...)
>       where islocal (User m i) = member (map fst rs) (User m i)
>             islocal rsym = True ||  Symbols in the language core are always completely known
*/

clistrategy :: Cli ((Graph SuclSymbol SuclVariable) SuclVariable var -> Bool) -> Strategy SuclSymbol var SuclVariable answer | == var
clistrategy (CliAlias {arities=as,typeconstructors=tcs,typerules=ts,rules=rs}) matchable
 = ( checkarity (extendfn as (typearity o maxtyperule ts))        // Checks curried occurrences and strict arguments
   o checklaws cleanlaws                            // Checks for special (hard coded) rules (+x0=x /y1=y ...)
   o checkrules matchable (foldmap id [] rs)        // Checks normal rewrite rules
   o checkimport islocal                            // Checks for delta symbols
   o ( checkconstr toString (flip isMember (flatten (map snd tcs))) // Checks for constructors
        ---> ("cli.clistrategy.checkconstr",tcs)
     )
   ) (corestrategy matchable)                       // Checks rules for symbols in the language core (IF, _AP, ...)
   where islocal rsym=:(SuclUser s) = isMember rsym (map fst rs)// User-defined symbols can be imported, so they're known if we have a list of rules for them
         islocal rsym               = True                      // Symbols in the language core (the rest) are always completely known
                                                                // This includes lifted case symbols; we lifted them ourselves, after all

typearity :: (Rule SuclTypeSymbol SuclTypeVariable) -> Int
typearity ti = length (arguments ti)

//maxtypeinfo :: [(SuclSymbol,(Rule SuclTypeSymbol SuclTypeVariable,[Bool]))] SuclSymbol -> (Rule SuclTypeSymbol SuclTypeVariable,[Bool])
//maxtypeinfo defs sym = extendfn defs coretypeinfo sym

maxtyperule :: [(SuclSymbol,Rule SuclTypeSymbol SuclTypeVariable)] SuclSymbol -> Rule SuclTypeSymbol SuclTypeVariable
maxtyperule defs sym = extendfn defs (coretyperule--->"cli.coretyperule begins from cli.maxtyperule") sym

maxstricts :: [(SuclSymbol,[Bool])] SuclSymbol -> [Bool]
maxstricts defs sym = extendfn defs corestricts sym

/*
>   constrs ((tes,tas,tcs),defs) = tcs

>   complete ((tes,tas,tcs),(es,as,ts,rs)) = mkclicomplete tcs (fst.maxtypeinfo ts)
*/

complete :: Cli -> [SuclSymbol] -> Bool
complete (CliAlias m) = mkclicomplete m.typeconstructors (maxtyperule m.typerules)

/*
>   showcli = printcli

>   mkclicomplete
>   ::  [(typesymbol,[symbol])] ->
>       (symbol->rule typesymbol *****) ->
>       [symbol] ->
>       bool

>   mkclicomplete tcs typerule [] = False
>   mkclicomplete tcs typerule syms
>   =   False, if ~tdef
>   =   foldmap superset (corecomplete tsym) tcs tsym syms, otherwise
>       where trule = typerule (hd syms)
>             (tdef,(tsym,targs)) = dnc (const "in mkclicomplete") (rulegraph trule) (rhs trule)
*/

mkclicomplete ::
    [(SuclTypeSymbol,[SuclSymbol])]
    (SuclSymbol->Rule SuclTypeSymbol tvar)
    [SuclSymbol]
 -> Bool
 |  == tvar

mkclicomplete tcs typerule [] = False
mkclicomplete tcs typerule syms
| not tdef
  = False
= foldmap superset (corecomplete tsym) tcs tsym syms
  where trule = typerule (hd syms)
        (tdef,(tsym,_)) = dnc (const "in mkclicomplete") (rulegraph trule) (ruleroot trule)

/*
------------------------------------------------------------------------

>   printcli :: module symbol node typesymbol typenode -> [char]
>   printcli ((tes,tas,tcs),(es,as,ts,rs))
>   =   lay
>       (   (implementation++"MODULE "++thismodule++";"):
>           "":
>           "<<  EXPORT":
>           map cleandef es++
>           ">>":
>           "":
>           map showimport (partition fst snd (itypesyms++isyms))++
>           concat (map cleanalg tcs)++
>           concat (map cleanimp [(sym,plookup showsymbol ts sym,rules)|(sym,rules)<-rs;usersym sym])
>       )
>       where cleandef sym = "    "++cleantyperule sym (maxtypeinfo ts sym)
>             cleanalg constr
>             =   ["","TYPE",printalgebra (fst.maxtypeinfo ts) constr], if typesymbolmodule (fst constr)=Present thismodule
>             =   [], otherwise
>             cleanimp (sym,tinfo,rules)
>             =   prepend (trulelines++concat (map (cleanrule sym) rules))
>                 where trulelines
>                       =   [], if member (concat (map snd tcs)) sym
>                       =   [cleantyperule sym tinfo], otherwise
>                       prepend [] = []
>                       prepend lines = "":"RULE":lines
>             implementation
>             =   "", if showsymbol (hd es)="Start"
>             =   "IMPLEMENTATION ", otherwise
>             isyms = [(module,ident)|((User module ident),tinfo)<-ts;~member (map fst rs) (User module ident)]
>             itypesyms
>             =   foldr add [] tcs
>                 where add (USER module ident,constrs) rest
>                       =   (module,ident):foldr addc rest constrs, if module~=thismodule
>                       add typesymbol = id
>                       addc (User module ident) rest
>                       =   (module,ident):rest
>                       addc symbol = id
>             thismodule = foldoptional undef id (symbolmodule (hd es))

>   showimport :: ([char],[[char]]) -> [char]
>   showimport (module,idents) = "FROM "++module++" IMPORT "++join ',' idents++";"

>   printalgebra :: (symbol->rule typesymbol typenode) -> (typesymbol,[symbol]) -> [char]
>   printalgebra typerule (tsym,syms)
>   =   "::  "++
>       showtypesymbol tsym++
>       concat (map ((' ':).showtypenode) trargs)++
>       concat (map2 (++) (" -> ":repeat " | ") alts)++
>       ";"
>       where symtrules = map (pairwith typerule) syms
>             trule = snd (hd symtrules)
>             trroot = rhs trule
>             (trdef,trcont) = dnc (const "in printalgebra") (rulegraph trule) trroot
>             (trsym,trargs)
>             =   trcont, if trdef
>             =   (notrsym,notrargs), otherwise
>             notrsym = error ("printalgebra: no type symbol for typenode "++showtypenode trroot)
>             notrargs = error ("printalgebra: no type arguments for typenode "++showtypenode trroot)
>             alts = map (printalt trargs) symtrules

>   printalt :: [typenode] -> (symbol,rule typesymbol typenode) -> [char]
>   printalt trargs' (sym,trule)
>   =   showsymbol sym++concat (map (' ':) (printgraph showtypesymbol showtypenode tgraph' targs'))
>       where targs = lhs trule; troot = rhs trule; tgraph = rulegraph trule
>             (trdef,(trsym,trargs)) = dnc (const "in printalt") tgraph troot
>             tnodes = trargs++(nodelist tgraph targs--trargs)
>             tnodes' = trargs'++(typeheap--trargs')
>             redirection = foldr (uncurry adjust) noredir (zip2 tnodes tnodes')
>             noredir tnode = error ("printalt: no redirection for typenode "++showtypenode tnode)
>             targs' = map redirection targs
>             tgraph' = movegraph redirection tnodes tgraph

Compiling clean parts into module information...

>   compilecli
>   ::  [cleanpart] ->
>       module symbol node typesymbol typenode

>   compilecli parts
>   =   ((typeexports,aliases,typedefs),(exports,macros,typerules,locals))
>       where typeexports = [tsym|Typeexport tsym<-parts]
>             aliases = [(tsym,compilerule targs troot tnodedefs)|Alias tsym targs troot tnodedefs<-parts]
>             typedefs = [(tsym,syms)|Algebra tsym syms<-parts]
>             exports = [sym|Export sym<-parts]
>             macros = [(sym,compilerule args root nodedefs)|Macro sym args root nodedefs<-parts]
>             typerules = [(sym,(compilerule targs troot tnodedefs,map (='!') stricts))|Type sym targs troot tnodedefs stricts<-parts]
>             locals = [(sym,rules sym)|Rules sym<-parts]
>             rules lsym = [compilerule args root nodedefs|Rule sym args root nodedefs<-parts;sym=lsym]

>   currytrule :: **** -> [*****] -> rule **** ***** -> rule **** *****
>   currytrule fn theap trule
>   =   mkrule ctargs ctroot ctgraph
>       where targs = lhs trule; troot = rhs trule; tgraph = rulegraph trule
>             ctargs = init targs
>             ctroot = hd (theap--nodelist tgraph (troot:targs))
>             ctgraph = updategraph ctroot (fn,[last targs,troot]) tgraph

*/

mkcli ::
    [(SuclSymbol,Rule SuclTypeSymbol SuclTypeVariable)]
    [(SuclSymbol,[Bool])]
    [SuclSymbol]
    [(SuclTypeSymbol,[(SuclSymbol,(Rule SuclTypeSymbol SuclTypeVariable,[Bool]))])]
    [(SuclSymbol,(Int,[Rule SuclSymbol SuclVariable]))]
 -> Cli

mkcli typerules stricts exports constrs bodies
= CliAlias
  { arities          = map (mapsnd fst) bodies
  , typeconstructors = map (mapsnd (map fst)) constrs
  , exportedsymbols  = exports
  , typerules        = typerules++flatten ((map (map (mapsnd fst) o snd)) constrs)
  , stricts          = stricts++flatten ((map (map (mapsnd snd) o snd)) constrs)
  , rules            = map (mapsnd snd) bodies
  }

instance <<< Cli
where (<<<) file (CliAlias m)
      = file <<< "=== Arities ===" <<< nl
             writeList m.arities
             <<< "=== Type Rules ===" <<< nl
             writeList m.typerules
             <<< "=== Rules ===" <<< nl
             writeList m.rules
