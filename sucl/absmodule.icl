implementation module absmodule

import rule

/*

------------------------------------------------------------------------
Exports.

>   %export
>       module
>       addtalias
>       addtsymdef
>       addalias
>       addsymdef
>       newmodule

------------------------------------------------------------------------
Includes.

>   %include "basic.lit"
>   %include "graph.lit" -extgraph
>   %include "rule.lit"

------------------------------------------------------------------------
Module implementation.

>   module * *** **** *****
>   ==  (   (   [****],                         ||  Exported types
>               [(****,rule **** *****)],       ||  Type alias rules
>               [(****,[*])]                    ||  Constructor symbols for algebraic type symbol
>           ),
>           (   [*],                            ||  Exported symbols
>               [(*,rule * ***)],               ||  Alias rules
>               [(*,(rule **** *****,[bool]))], ||  Typerule for symbol
>               [(*,[rule * ***])]              ||  Rewrite rules for symbol, absent if imported
>           )
>       )

*/

:: Module sym pvar tsym tvar
   = { exportedtypesymbols :: [tsym]                        // Exported type symbols (from DCL)
     , typealias           :: [(tsym,Rule tsym tvar)]       // Alias types
     , typeconstructors    :: [(tsym,[sym])]                // All constructor symbols of each declared algebraic type
     , exportedsymbols     :: [sym]                         // Exported function/constructor symbols
     , aliases             :: [(sym,Rule sym pvar)]         // Macros
     , typerules           :: [(sym,Rule tsym tvar,[Bool])] // Info from type rules (actual type and argument strictnesses)
     , rules               :: [(sym,[Rule sym pvar])]       // Rewrite rules of each symbol, absent if imported
     }

/*

>   newmodule :: module * *** **** *****
>   newmodule = (([],[],[]),([],[],[],[]))

>   addtalias :: **** -> bool -> rule **** ***** -> module * *** **** ***** -> module * *** **** *****
>   addtalias ts exp tr ((tes,tas,tcs),defs)
>   =   ((cond exp (ts:tes) tes,(ts,tr):tas,tcs),defs)

>   addtsymdef :: **** -> bool -> [*] -> module * *** **** ***** -> module * *** **** *****
>   addtsymdef ts exp ss ((tes,tas,tcs),defs)
>   =   ((cond exp (ts:tes) tes,tas,(ts,ss):tcs),defs)

>   addalias :: * -> bool -> rule * *** -> module * *** **** ***** -> module * *** **** *****
>   addalias s exp r (tdefs,(es,as,ts,rs))
>   =   (tdefs,(cond exp (s:es) es,(s,r):as,ts,rs))

>   addsymdef :: * -> bool -> rule **** ***** -> bool -> [rule * ***] -> module * *** **** ***** -> module * *** **** *****
>   addsymdef s exp t imp rr (tdefs,(es,as,ts,rs))
>   =   (tdefs,(cond exp (s:es) es,as,(s,(t,[])):ts,cond imp rs ((s,rr):rs)))

*/
