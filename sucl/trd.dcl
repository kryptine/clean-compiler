definition module trd

// $Id$

from rule import Rule
from graph import Node
from StdOverloaded import ==

/*
`Ruletype theap symtype rule' determines the type of `rule'.
`Theap' must be an endless supply of type variables.
`Symtype' associates type rules with the symbols that occur in `rule'.

If typing does not succeed, the function aborts.
*/

ruletype
 :: .[tvar]
    ((Node sym var) -> Rule tsym trvar)
    (Rule sym var)
 -> .Rule tsym tvar
 |  == var
 &  == tsym
 &  == tvar
 &  == trvar
