definition module newtest

// $Id$

from cli import Cli
from coreclean import SuclTypeSymbol,SuclTypeVariable,SuclSymbol,SuclVariable
from trace import Trace,Transformation
from spine import Answer,Spine,Subspine
from history import History,HistoryAssociation,HistoryPattern
from rule import Rgraph,Rule
from general import Optional

:: Symredresult sym var tsym tvar
   :== ( Rgraph sym var    // The initial area in canonical form
       , sym               // The assigned symbol
       , [Bool]            // Strictness annotations
       , Rule tsym tvar    // Type rule
       , Trace sym var var // Truncated and folded trace
       , [Rule sym var]    // Resulting rewrite rules
       , [Rgraph sym var]  // New areas for further symbolic reduction (not necessarily canonical)
       )

fullsymred ::
    [SuclSymbol]    // Fresh function symbols
    Cli             // Module to optimise
 -> [Symredresult SuclSymbol SuclVariable SuclTypeSymbol SuclTypeVariable]
