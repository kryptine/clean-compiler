definition module canon

// $Id$

from rule import Rule,Rgraph
from graph import Node
from StdOverloaded import ==

// Canonises area into task expression
// so equivalent ones can be detected through '==' comparison.
canonise ::
    (sym -> Int)        // Get arity of a symbol (for eta expansion)
    [var2]              // Heap (nodespace) for consistent relabeling
    (Rgraph sym var1)   // Input rooted graph
 -> Rgraph sym var2     // Canonised rooted graph
 |  == var1

// Fold an area in a subject graph
foldarea ::
    ((Rgraph sym var) -> sym)   // Labeling function, assigning names to areas
    (Rgraph sym var)            // Area to fold
 -> Node sym var                // Resulting function application
 |  == var

labelarea ::
    (sym->Bool)         // Whether a function symbol can be reused for a generated function
    [Rgraph sym var]    // List of areas to be labeled
    [sym]               // List of symbols to assign to them
    (Rgraph sym var)    // Rooted graph to label
 -> sym                 // Assigned symbol
 |  == sym
 &  == var
