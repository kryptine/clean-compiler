implementation module convert

// $Id$

import coreclean
import rule
import syntax
import StdEnv

// $Id$

// Cocl to Sucl for functions
cts_function
 :: {#FunDef}
 -> ( [(SuclSymbol,Rule SuclTypeSymbol SuclTypeVariable)]//Type rule (derives arity)
    , [(SuclSymbol,[Bool])]                             // Strict arguments (just main args for now)
    , [(SuclSymbol,[Rule SuclSymbol SuclVariable])]     // Rewrite rules
    , [(SuclSymbol,SuclSymbolKind)]                     // Kind of symbol
    )

cts_function _ = abort "cts_function: not implemented"

// SuclSymbolKind distinguishes functions, constructors, and primitives
// SuclSymbol are the Sucl symbols, such as SuclInt Int, etc.
