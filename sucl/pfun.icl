implementation module pfun

// $Id$

import basic
import StdEnv

/*

pfun.lit - Partial functions
============================

Description
-----------

This script implements an abstract type for partial functions and useful
operations on them.

Implementation
--------------

*/

:: Pfun dom ran
   = EmptyPfun
   | Extend dom ran (Pfun dom ran)
   | Restrict dom (Pfun dom ran)

emptypfun :: .Pfun .dom .ran
emptypfun = EmptyPfun

extend :: .dom .ran (Pfun .dom .ran) -> Pfun .dom .ran
extend arg res pfun = Extend arg res pfun

restrict :: .dom (Pfun .dom .ran) -> Pfun .dom .ran
restrict arg pfun = Restrict arg pfun

overwrite :: !(Pfun .dom .ran) (Pfun .dom .ran) -> (Pfun .dom .ran)
overwrite EmptyPfun old = old
overwrite (Extend org img new) old = Extend org img (overwrite new old)
overwrite (Restrict org new) old = Restrict org (overwrite new old)

postcomp :: (.ran1 -> .ran2) !(Pfun .dom .ran1) -> Pfun .dom .ran2
postcomp f EmptyPfun = EmptyPfun
postcomp f (Extend x y p) = Extend x (f y) (postcomp f p)
postcomp f (Restrict x p) = Restrict x (postcomp f p)

total :: .ran !(Pfun dom .ran) dom -> .ran | == dom
total def EmptyPfun arg = def
total def (Extend x y p) arg
| arg==x = y
         = total def p arg
total def (Restrict x p) arg
| arg==x = def
         = total def p arg

// Apply partial function with a default value
foldpfun :: (.ran1 -> .ran2) .ran2 !(Pfun dom .ran1) dom -> .ran2 | == dom
foldpfun found notfound pfun arg
 = total notfound (postcomp found pfun) arg

domres :: !.[dom] .(Pfun dom ran) -> Pfun dom ran | == dom
domres domain oldpfun
= foldr adddom emptypfun domain
  where adddom org = total id (postcomp (extend org) oldpfun) org

apply :: !(Pfun dom .ran) dom -> (.Bool,.ran) | == dom
apply pfun arg
= total (False,baddomain) (postcomp s pfun) arg
  where s x = (True,x)
        baddomain = abort "apply: partial function applied outside domain"

instance toString Pfun dom ran | toString dom & toString ran & == dom
where toString pfun
      = toString ['{':drop 1 (flatten (map ((cons ',') o printlink) (pfunlist pfun)))++['}']]
        where printlink (arg,res) = fromString (toString arg)++['|->']++fromString (toString res)

pfunlist :: (Pfun dom res) -> [(dom,res)] | == dom
pfunlist EmptyPfun = []
pfunlist (Extend x y pf) = [(x,y):pfunlist (Restrict x pf)]
pfunlist (Restrict x pf) = [xxyy \\ xxyy=:(xx,yy) <- pfunlist pf | xx<>x]

idpfun :: !.[dom] .(Pfun dom dom) -> Bool | == dom
idpfun domain pfun
= all idelem domain
  where idelem x = total True (postcomp ((==) x) pfun) x

instance == (Pfun dom ran) | == dom & == ran
where (==) EmptyPfun EmptyPfun = True
      (==) (Extend x1 y1 pf1) (Extend x2 y2 pf2)
            = x1==x2 && y1==y2 && pf1==pf2
      (==) (Restrict x1 pf1) (Restrict x2 pf2)
            = x1==x2 && pf1==pf2
      (==) _ _ = False

(writepfun) infixl :: *File .(Pfun dom ran) -> .File | ==,toString dom & toString ran
(writepfun) file pfun = file <<< toString pfun
