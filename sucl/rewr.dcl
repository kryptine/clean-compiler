definition module rewr

from rule import Rule
from graph import Graph
from pfun import Pfun
from StdOverloaded import ==

// Unfold a rewrite rule
xunfold
 :: var
    (Rule sym pvar)
   !(   [var]
    ,   var
    ,   Graph sym var
    ,   Pfun pvar var
    )
 -> (   [var]
    ,   var
    ,   Graph sym var
    ,   Pfun pvar var
    ) | == var & == pvar

foldfn
 :: (Pfun pvar var)     // Matching of replacement
    sym                 // Symbol at root of pattern
    [pvar]              // Arguments of pattern
    pvar                // Root of replacement
    (Graph sym var)     // Subject graph
 -> Graph sym var       // Folded subject
 |  == pvar

getmapping
 :: tsym
    (Graph sym pvar)
    (Graph sym var)
    !(pvar,var)
    ((Pfun pvar var) -> tsym)
    !(Pfun pvar var)
 -> tsym
 |  == sym
 &  == var
 &  == pvar

instantiate
 :: .(Graph sym pvar)       // Pattern to instantiate with
    pvar                    // Root of the pattern
    var                     // Open node to instantiate
    (.[var],.Graph sym var) // Heap,graph
 -> .([var],Graph sym var)  // New heap,graph
 |  == var
 &  == pvar
