definition module expand

from newtest import Symredresult
from StdOverloaded import ==

// Transitive necessities

from newtest import FuncDef,FuncBody
from trace import Trace,Transformation
from spine import Answer,Spine,Subspine
from history import History,HistoryAssociation,HistoryPattern
from rule import Rgraph,Rule
from cleanversion import String
from general import Optional

/*

   Expand macro rules where possible.

   The optimisation algorithm generates too many closures, many of which appear
   to be just macros that rewrite to another rule.  This module unfolds such
   macros.

   Macro rules do not have pattern matches (in pattern match representation)
   and can in principle always be unfolded.  The only catch is that they could
   be (mutually) recursive by themselves, but the optimiser must be able to
   handle that.  Being mutually recursive doesn't mean evaluation never
   terminates, as the occurrences can be at lazy positions.

   What to expand: expand (non-partial) applications of functions for which all
   of the following hold:

   [1] The function is a macro (doesn't have a pattern match aka case
       statement).

   [2] The function is not on a cycle of non-partial applications of macro
       functions.

       Exception: if there is only a single application (including partial
       applications, applications inside case functions, and exported
       functions) of the macro function, it can be expanded.

   Due to the expansion, some functions may become unused, if all their
   occurrences are unfolded.  Removal of unused functions -dead code
   elimination- is a separate matter and not handled here.

*/

:: Reference sym = Reference Bool sym sym

expand_macros ::
    (sym->String)
    (var->String)
    [var]                               // Heap of node-ids for rule expansion
    (sym->Bool)                         // Whether the function is exported.
    [Symredresult sym var tsym tvar]    // Symbolic reduction results of all functions
 -> [Symredresult sym var tsym tvar]    // Expanded symbolic reduction results
 |  == sym
 &  == var
