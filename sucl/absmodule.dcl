definition module absmodule

// $Id$

from rule import Rule

:: Module sym pvar tsym tvar
   = { arities             :: [(sym,Int)]               // Arity of each symbol
     , typeconstructors    :: [(tsym,[sym])]            // All constructor symbols of each declared algebraic type
     , exportedsymbols     :: [sym]                     // Exported function/constructor symbols
     , typerules           :: [(sym,Rule tsym tvar)]    // Principal types of symbols
     , stricts             :: [(sym,[Bool])]            // Strict arguments of functions
     , rules               :: [(sym,[Rule sym pvar])]   // Rewrite rules of each symbol, absent if imported
     }
