definition module pfun

// $Id$

from StdString import toString
from StdOverloaded import ==

// Partial function abstract type
:: Pfun dom ran

// The empty partial function
emptypfun :: .Pfun .dom .ran

// Extend a partial function
extend :: .dom .ran (Pfun .dom .ran) -> Pfun .dom .ran

// Restrict a partial function (take away one mapping)
restrict :: .dom (Pfun .dom .ran) -> Pfun .dom .ran

// Overwrite partial function with a new one
// first arg is the new p.f.
// second arg is overwritten
overwrite :: !(Pfun .dom .ran) (Pfun .dom .ran) -> (Pfun .dom .ran)

// Modify a partial function by applying a function to all its results
postcomp :: (.ran1 -> .ran2) !(Pfun .dom .ran1) -> Pfun .dom .ran2

// Build a total function from a partial one by supplying a default value
total :: .ran !(Pfun dom .ran) dom -> .ran | == dom

// Apply partial function with a default value
foldpfun :: (.ran1 -> .ran2) .ran2 !(Pfun dom .ran1) dom -> .ran2 | == dom

// Domain restriction of a partial function
domres :: !.[dom] .(Pfun dom ran) -> Pfun dom ran | == dom

// Apply a partial function to an argument
// getting a result that may fail
apply :: !(Pfun dom .ran) dom -> (.Bool,.ran) | == dom

// Partial functions are printable
instance toString (Pfun dom ran) | toString dom & toString ran & == dom
(writepfun) infixl :: *File .(Pfun dom ran) -> .File | ==,toString dom & toString ran

/* `Idpfun dom pfun' checks whether partial function `pfun' is the identity
   on the nodes in `dom' for which it is defined.
*/
idpfun :: !.[dom] .(Pfun dom dom) -> Bool | == dom

instance == (Pfun dom ran) | == dom & == ran
