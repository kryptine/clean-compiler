implementation module basic

// $Id$

/*

Basic definitions
=================

Description
-----------

Basic types and functions.

*/

import StdEnv

/*

Implementation
--------------

*/

//:: Optional t = Absent | Present t
// Now using Optional type from cocl's general module
from general import Optional,No,Yes

instance == (Optional a) | == a
 where (==) No No = True
       (==) (Yes x1) (Yes x2) = x1==x2
       (==) _ _ = False


// Adjust a function for a single argument

adjust :: !arg res (arg->res) !arg -> res | == arg
adjust a r f x
    | x==a = r
           = f x


// Claim a list of nodes from a heap
claim :: ![.param] u:[.cell] -> ([.cell],v:[.cell]), [u<=v]

claim [] heap = ([],heap)
claim [pnode:pnodes] [snode:heap]
=   ([snode:snodes],heap`)
    where (snodes,heap`) = claim pnodes heap
claim pnodes emptyheap = abort "claim: out of heap" // Just in case. Should be used with an infinite heap.

/* Depthfirst collects results of a function (called process), applied to a
given  list  of  inputs  and  other  inputs which are generated from the
results recursively, and so on.  Duplicates are removed. */

depthfirst :: (res->.[elem]) (elem->res) !.[elem] -> .[res] | == elem
depthfirst generate process xs
=   snd (collect xs ([],[]))
    where collect [] seenrest = seenrest
          collect [x:xs] (seen,rest)
          | isMember x seen
          =   collect xs (seen,rest)
          =   (seen``,[y:rest``])
              where (seen`,rest``) = collect (generate y) ([x:seen],rest`)
                    (seen``,rest`) = collect xs           (   seen`,rest)
                    y = process x

// `Disjoint xs ys' checks whether xs and ys are disjoint.

disjoint :: .[elem] !.[elem] -> Bool | == elem
disjoint xs ys = not (or (map (flip isMember xs) ys))

eqlen :: ![.elem1] ![.elem2] -> .Bool
eqlen [x:xs] [y:ys] = eqlen xs ys
eqlen [] [] = True
eqlen xs ys = False

// Extend a function using the elements of a mapping
extendfn :: [(src,dst)] (src->dst) src -> dst | == src
extendfn mapping f x = foldmap id (f x) mapping x

// `Foldlm' is a combination of foldl and map.
foldlm :: ((.collect,.elem) -> (.collect,.elem`)) !(.collect,![.elem]) -> (.collect,[.elem`])
foldlm f (l,[]) = (l,[])
foldlm f (l,[m:ms])
=   (l``,[m`:ms`])
    where (l`,m`) = f (l,m)
          (l``,ms`) = foldlm f (l`,ms)

foldlr :: (.elem -> .((.lrinfo,.rlinfo) -> (.lrinfo,.rlinfo))) !(.lrinfo,.rlinfo) ![.elem] -> (.lrinfo,.rlinfo)
foldlr f (l,r) []
    = (l,r)
foldlr f (l,r) [x:xs]
    = (l``,r``)
      where (l``,r`) = foldlr f (l`,r) xs
            (l`,r``) = f x (l,r`)

foldmap :: (x:res -> w:res`) w:res` -> u:(![(arg,x:res)] -> v:(arg -> w:res`)) | == arg, [v u <= w, v <= x]
foldmap f d
=   foldr foldmap` (const d)
    where foldmap` (x,y) g v = if (x==v) (f y) (g v)

foldoptional :: .res .(.t -> .res) !(Optional .t) -> .res
foldoptional no yes No = no
foldoptional no yes (Yes x) = yes x

forget :: val -> .(![.(val,res)] -> .[(val,res)]) | == val
forget x = filter (neq x o fst)
neq x y = x <> y

indent :: .String -> .([.String] -> .[String])
indent first = map2 (+++) [first:repeat (createArray (size first) ' ')]

map2 :: (.a -> .(.b -> .c)) ![.a] [.b] -> [.c]
map2 f [x:xs] [y:ys] = [f x y:map2 f xs ys]
map2 f _ _ = []

// `Identifiers' is the list of all identifiers
identifiers :: [String]
identifiers =: map toString (tl (kleene ['abcdefghijklmnopqrstuvwxyz']))

// `Intersect xs ys' is the intersection of list `ys' with list `xs'.
intersect :: ![elem] [elem] -> .[elem] | == elem
intersect []     _  = []
intersect [y:ys] xs = elim (cons y o intersect ys) (intersect ys xs) y xs

// Elim removes a given element from a list.
// There are two continuations, one for failure and one for success.
elim :: .(v:[elem] -> .res) .res elem u:[elem] -> .res | == elem, [u <= v]
elim found notfound y []
=   notfound
elim found notfound y [x:xs]
| x==y
=   found xs
=   elim (found o cons x) notfound y xs

// Cons prepends an element to a list
cons :: .elem u:[.elem] -> v:[.elem], [u <= v]
cons x xs = [x:xs]

// `Join x xss' is the join of the list of lists `xss', separated by `x'.
join :: a ![.[a]] -> .[a]
join sep [] = []
join sep [x:xs] = x++flatten (map (cons sep) xs)

/* `Kleene xs' determines the kleene closure of the list `xs'  of  symbols,
   i.e.   all strings over that list in standard order.  The implementation
   is designed for maximum sharing.
*/
kleene :: !.[symbol] -> .[[symbol]]
kleene [] = [[]]
kleene symbols
=   flatten (iterate prefix [[]])
    where prefix strings
          =   flatten (map appendstrings symbols)
              where appendstrings symbol = map (cons symbol) strings

lookup :: u:([(arg,w:res)] -> v:(arg -> w:res)) | == arg, [v u <= w]
lookup = foldmap id (abort "lookup: not found")

pairwith :: .(arg -> .res) arg -> (arg,.res)
pairwith f x = (x,f x)

plookup :: .(arg -> String) ![(arg,.res)] arg -> .res | == arg
plookup showa tbl a = foldmap id (abort (showa a+++": not found")) tbl a

power :: !Int (.t -> .t) -> .(.t -> .t)
power n f
| n <= 0
=   id
=   f o power (n-1) f

printoptional :: .(.t -> String) !(Optional .t) -> String
printoptional printa  No     = ""
printoptional printa (Yes a) = printa a

proc :: .((w:elem -> .(.res -> .res)) -> v:(![w:elem] -> u:(.res -> .res))), [u <= v, u <= w]
proc = flip o foldr

mapfst :: v:(.a -> .b) -> u:((.a,.c) -> (.b,.c)), [u <= v]
mapfst f = app2 (f,id)

mapfst3 :: v:(.a -> .b) -> u:((.a,.c,.d) -> (.b,.c,.d)), [u <= v]
mapfst3 f = app3 (f,id,id)

maphd :: .(.a -> .a) !u:[.a] -> v:[.a], [u <= v]
maphd f []     = []
maphd f [x:xs] = [f x:xs]

mapoptional :: .(.a -> .b) !(Optional .a) -> Optional .b
mapoptional f No      = No
mapoptional f (Yes x) = Yes (f x)

mappair :: .(.a -> .b) .(.c -> .d) !(.a,.c) -> (.b,.d)
mappair f g (x,y) = (f x,g y)

mapsnd :: v:(.a -> .b) -> u:((.c,.a) -> (.c,.b)), [u <= v]
mapsnd f = app2 (id,f)

maptl :: .(x:[.a] -> u:[.a]) !w:[.a] -> v:[.a], [u <= v, w <= x]
maptl f []     = []
maptl f [x:xs] = [x:f xs]

maptriple :: x:(.a -> .b) w:(.c -> .d) v:(.e -> .f) -> u:((.a,.c,.e) -> (.b,.d,.f)), [u <= v, u <= w, u <= x]
maptriple f g h = app3 (f,g,h)

partition :: (a -> b) (a -> .c) -> .(!.[a] -> [(b,[.c])]) | == b
partition f g
=   h
    where h [] = []
          h [x:xs]
          =   [((r,[g x:ins])):h outs]
              where ins = [g x\\x<-xs|f x==r]
                    outs = [x\\x<-xs|f x<>r]
                    r = f x

relimg :: ![(a,.b)] a -> [.b] | == a
relimg rel x` = [y\\(x,y)<-rel|x==x`]

remap :: a b [.(a,b)] -> .[(a,b)] | == a
remap x y xys = [(x,y):forget x xys]

shorter :: ![.a] [.b] -> .Bool
shorter []     yys    = False
shorter [x:xs] []     = True
shorter [x:xs] [y:ys] = shorter xs ys

showbool :: .(!.Bool -> a) | fromBool a
showbool = fromBool

showoptional :: .(.a -> .String) !(Optional .a) -> String
showoptional showa No      = "No"
showoptional showa (Yes a) = "(Yes "+++showa a+++")"

showpair :: !.(.a -> .String) !.(.b -> .String) !(.a,.b) -> String
showpair showa showb (a,b) = "("+++showa a+++","+++showb b+++")"

showstring :: .(!.String -> a) | fromString a
showstring = fromString

showtriple :: !.(.a -> .String) !.(.b -> .String) !.(.c -> .String) !(.a,.b,.c) -> String
showtriple showa showb showc (a,b,c) = "("+++showa a+++","+++showb b+++","+++showc c+++")"

split :: a -> .(.[a] -> [.[a]]) | == a
split sep
=   uncurry cons o spl
    where spl [] = ([],[])
          spl [x:xs]
          | x==sep
          =   ([],[ys:yss])
          =   ([x:ys],yss)
              where (ys,yss) = spl xs

superset :: .[a] -> .(.[a] -> Bool) | == a
superset set = isEmpty o (removeMembers set)
