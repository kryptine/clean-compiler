implementation module absmodule

// $Id$

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

*/

:: Module sym pvar tsym tvar
   = { typeconstructors    :: [(tsym,[sym])]            // All constructor symbols of each declared algebraic type
     , exportedsymbols     :: [sym]                     // Exported function/constructor symbols
     , typerules           :: [(sym,Rule tsym tvar)]    // Principal types of symbols
     , stricts             :: [(sym,[Bool])]            // Strict arguments of functions
     , rules               :: [(sym,[Rule sym pvar])]   // Rewrite rules of each symbol, absent if imported
     }
