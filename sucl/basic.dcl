definition module basic

// $Id$

/*

Basic definitions
=================

Description
-----------

Basic types and functions.

*/

from general import Optional
import StdOverloaded
import StdString

/*

Implementation
--------------

*/

// The optional type of type t is a type like t
// where the actual t value may be present or absent.
//:: Optional t = Absent | Present t
//Now using Optional from cocl's general module

instance == (Optional a) | == a


// Adjust a function for a single argument
adjust :: !arg res (arg->res) !arg -> res | == arg

// Claim a list of nodes from a heap
claim :: ![.param] u:[.cell] -> ([.cell],v:[.cell]), [u<=v]

// Cons prepends an element to a list
cons :: .elem u:[.elem] -> v:[.elem], [u <= v]

// Depthfirst does depth first enumeration of a search process
/* Depthfirst collects results of a function (called process), applied to a
   given  list  of  inputs  and  other  inputs which are generated from the
   results recursively, and so on.  Duplicates are removed.
*/
depthfirst :: (res->.[elem]) (elem->res) !.[elem] -> .[res] | == elem

// `Disjoint xs ys' checks whether xs and ys are disjoint.
disjoint :: .[elem] !.[elem] -> Bool | == elem

// `Eqlen xs ys' determines whether `xs' and `ys' are equally long.
eqlen :: ![.elem1] ![.elem2] -> .Bool

// Extend a function using the elements of a mapping
extendfn :: [(src,dst)] (src->dst) src -> dst | == src

// `Foldlm' is a combination of foldl and map.
foldlm :: ((.collect,.elem) -> (.collect,.elem`)) !(.collect,![.elem]) -> (.collect,[.elem`])

// Foldlr combines foldl and foldr:
// Information flows both forward and backward through the list.
foldlr :: (.elem -> .((.lrinfo,.rlinfo) -> (.lrinfo,.rlinfo))) !(.lrinfo,.rlinfo) ![.elem] -> (.lrinfo,.rlinfo)

// Foldmap is the fold function for a map type (from arg to res) given by a list,
// deriving a total function from it giving res`.
foldmap :: (x:res -> w:res`) w:res` -> u:(![(arg,x:res)] -> v:(arg -> w:res`)) | == arg, [v u <= w, v <= x]

// Foldoptional is the standard fold for the optional type.
foldoptional :: .res .(.t -> .res) !(Optional .t) -> .res

// Forget drops a mapped value from a map given by a list.
forget :: val -> .(![.(val,res)] -> .[(val,res)]) | == val

// Indent a list of strings with spaces,
// except the first which is indented with a specific string.
indent :: .String -> .([.String] -> .[String])

// `Identifiers' is the list of all identifiers
identifiers :: [String]

// `Intersect xs ys' is the intersection of list `ys' with list `xs'.
intersect :: ![elem] [elem] -> .[elem] | == elem

// `Join x xss' is the join of the list of lists `xss', separated by `x'.
join :: a ![.[a]] -> .[a]

/* `Kleene xs' determines the kleene closure of the list `xs'  of  symbols,
   i.e.   all strings over that list in standard order.  The implementation
   is designed for maximum sharing.
*/
kleene :: !.[symbol] -> .[[symbol]]

// Lookup finds a value mapped in a list mapping.
lookup :: u:([(arg,w:res)] -> v:(arg -> w:res)) | == arg, [v u <= w]

// Map a function onto the zip of two lists.
map2 :: (.a -> .(.b -> .c)) ![.a] [.b] -> [.c]

// Map a function on the first element of a 2-tuple.
mapfst :: v:(.a -> .b) -> u:((.a,.c) -> (.b,.c)), [u <= v]

// Map a function on the first element of a triple.
mapfst3 :: v:(.a -> .b) -> u:((.a,.c,.d) -> (.b,.c,.d)), [u <= v]

// Map a function onto the head of a list.
maphd :: .(.a -> .a) !u:[.a] -> v:[.a], [u <= v]

// Map a function onto an optional value.
mapoptional :: .(.a -> .b) !(Optional .a) -> Optional .b

// Map two functions onto a pair.
mappair :: .(.a -> .b) .(.c -> .d) !(.a,.c) -> (.b,.d)

// Map a function onto the second element of a 2-tuple.
mapsnd :: v:(.a -> .b) -> u:((.c,.a) -> (.c,.b)), [u <= v]

// Map a function onto the tail of a list.
maptl :: .(x:[.a] -> u:[.a]) !w:[.a] -> v:[.a], [u <= v, w <= x]

// Map three functions onto a triple.
maptriple :: x:(.a -> .b) w:(.c -> .d) v:(.e -> .f) -> u:((.a,.c,.e) -> (.b,.d,.f)), [u <= v, u <= w, u <= x]

// Pairwith pairs a value with its result under a given function
pairwith :: .(arg -> .res) arg -> (arg,.res)

// Partition a list.
// The first argument is a representer function that defines partition blocks.
// The second argument is a selector function that is applied to each element of each block.
partition :: (a -> b) (a -> .c) -> .(!.[a] -> [(b,[.c])]) | == b

// Plookup is a printable lookup with a more readable error message for the not found case.
plookup :: .(arg -> String) ![(arg,.res)] arg -> .res | == arg

// Power applies a function a number of times to a value.
power :: !Int (.t -> .t) -> .(.t -> .t)

// Printoptional produces a printable representation of an optional type.
printoptional :: .(.t -> String) !(Optional .t) -> String

// Proc is an argument-permuted variant of foldr
proc :: .((w:elem -> .(.res -> .res)) -> v:(![w:elem] -> u:(.res -> .res))), [u <= v, u <= w]

// `Relimg rel x' is the relational image of `x' in relation `rel' (represented by a table).
relimg :: ![(a,.b)] a -> [.b] | == a

// `Remap x y mapping' alters the mapping by associating y with x, removing the old values.
remap :: a b [.(a,b)] -> .[(a,b)] | == a

// `Shorter xs' determines whether a list is shorter than list `xs'.
shorter :: ![.a] [.b] -> .Bool

// `Showbool b' is the string representation of boolean `b'.
showbool :: .(!.Bool -> a) | fromBool a

// `Showoptional showa opt' is the string representation of optional value `opt',
// where `showa' determines the string representation of the inner value.
showoptional :: .(.a -> .String) !(Optional .a) -> String

// `Showpair showa showb pair' is the string representation of a pair,
// where showa and showb represent the internal types.
showpair :: !.(.a -> .String) !.(.b -> .String) !(.a,.b) -> String

// `Showstring s' represents a string as a string.
showstring :: .(!.String -> a) | fromString a

// `Showtriple' determines the string representation of a triple.
showtriple :: !.(.a -> .String) !.(.b -> .String) !.(.c -> .String) !(.a,.b,.c) -> String

// `Split sep' splits a list into a list of sublists which are separated by `sep'.
split :: a -> .(.[a] -> [.[a]]) | == a

// `Superset xs ys' determines whether ys is a superset (actually, super-multi-set or super-list) of xs.
superset :: .[a] -> .(.[a] -> Bool) | == a
