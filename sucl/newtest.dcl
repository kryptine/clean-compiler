definition module newtest

// $Id$

from cli import Cli
from coreclean import SuclTypeSymbol,SuclTypeVariable,SuclSymbol,SuclVariable
from newfold import FuncDef,FuncBody
from trace import Trace,Transformation
from spine import Answer,Spine,Subspine
from history import History,HistoryAssociation,HistoryPattern
from rule import Rgraph,Rule
from general import Optional
from StdFile import <<<
from StdString import toString
from StdOverloaded import ==
from StdClass import Eq
from cleanversion import String

:: Symredresult sym var tsym tvar
   = { srr_task_expression :: Rgraph sym var    // The initial area in canonical form
     , srr_assigned_symbol :: sym               // The assigned symbol
     , srr_strictness      :: [Bool]            // Strictness annotations
     , srr_arity           :: Int               // Arity
     , srr_typerule        :: Rule tsym tvar    // Type rule
     , srr_trace           :: Trace sym var var // Truncated and folded trace
     , srr_function_def    :: FuncDef sym var   // Resulting rewrite rules
     , srr_areas           :: [Rgraph sym var]  // New areas for further symbolic reduction (not necessarily canonical)
     }

instance toString (Symredresult sym var tsym tvar) | toString sym & toString var & Eq var
instance <<< (Symredresult sym var tsym tvar) | toString sym & <<<,==,toString var

fullsymred ::
    (SuclSymbol->String) // Get the (readable) string representation of a symbol
    [SuclSymbol]    // Fresh function symbols
    Cli             // Module to optimise
 -> [Symredresult SuclSymbol SuclVariable SuclTypeSymbol SuclTypeVariable]
