definition module absmodule

// $Id$

from rule import Rule

:: Module sym pvar tsym tvar
   = { //exportedtypesymbols :: [tsym]                            // Exported type symbols (from DCL)
   //, typealias           :: [(tsym,Rule tsym tvar)]           // Alias types
       typeconstructors    :: [(tsym,[sym])]                    // All constructor symbols of each declared algebraic type
     , exportedsymbols     :: [sym]                             // Exported function/constructor symbols
   //, aliases             :: [(sym,Rule sym pvar)]             // Macros
     , typerules           :: [(sym,(Rule tsym tvar,[Bool]))]   // Info from type rules (actual type and argument strictnesses)
     , rules               :: [(sym,[Rule sym pvar])]           // Rewrite rules of each symbol, absent if imported
     }
