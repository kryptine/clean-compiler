implementation module complete

import graph
import StdEnv

/*

To check completeness of patterns, we need to know whether, given a list
of (constructor) symbols, this list completely covers a type.

    complete :: [sym] -> Bool

It is assumed that a type can never  be  empty,  so  an  empty  list  of
constructors   can   never  cover  a  type.   Otherwise,  separate  type
information would be needed to determine the completeness  of  an  empty
list of constructors.


The algorithm uses /multipatterns/, which are lists of simple patterns.  A
multipattern is used to match at multiple node-ids in a graph in parallel.
This is necessary in the case of matching of product types.

*/

:: Pattern sym var
   :== (Graph sym var,[var])

/*

Coveredby checks  whether  a  multipattern  is  covered  by  a  list  of
multipatterns.  There are five cases to consider.

    First, if the multipattern is not the empty list, then to  cover  it
    some  multipattern  must  exist,  so if the list of multipatterns is
    empty, then the multipattern is not covered.

    Second, if the multipattern is  the  empty  list,  it  is  trivially
    covered by any list of multipatterns, including the empty.

    Third, if the first pattern of the multipattern is closed, we select
    only the multipatterns that it can match,  then  continue  with  the
    arguments, and then the rest of the multipattern.

    Fourth,  if  the  first pattern of the multipattern is open, and all
    its type constructors are present  in  the  first  patterns  of  the
    multipatterns  in  the list of multipatterns, then the first pattern
    of the multipattern is split according to all constructors, and  all
    possibilities must be covered.

    Fifth,  if  not all constructors are present, then the multipatterns
    of which the first pattern is open must cover the multipattern.   So
    those   are   selected  and  we  continue  with  the  tails  of  the
    multipatterns in this list.

To understand the order of the first two cases, check how a single  open
integer  pattern  is  covered  by  a  list  of  integer  patterns either
containing or not containing an open pattern.

*/

coveredby
 :: ([sym]->Bool)
    (Graph sym var)
    ![Pattern sym pvar]
    [var]
 -> Bool
 |  == sym
 &  == var
 &  == pvar

coveredby complete subject [] svars = False
coveredby complete subject pvarss [] = True
coveredby complete subject pvarss [svar:svars]
| sdef
= coveredby complete subject tmpvalue (sargs++svars)
| complete (map fst3 closeds)
= and (map covered closeds)
= coveredby complete subject opens svars
  where (opens,closeds) = split pvarss
        covered (sym,repvar`,pvarss`) = coveredby complete subject pvarss` (repvar (repvar` undef) svar++svars)
        (sdef,(ssym,sargs)) = varcontents subject svar
        tmpvalue = (fst (foldr (spl (repvar sargs) ssym) ([],[]) pvarss))

repvar pvars svar = map (const svar) pvars

/*

Split splits a list of multipatterns into parts; on one hand,  those  of
which  the  first  pattern  is  open,  and  on the other hand, for every
constructor, the list of applicable multipatterns,  in  which  case  the
multipatterns with an open pattern are expanded and added as well.

*/

split
 :: [Pattern sym var]
 -> (   [Pattern sym var]
    ,   [   (   sym
            ,   var->[var]
            ,   [Pattern sym var]
            )
        ]
    )
 |  == sym
 &  == var

split [] = ([],[])
split [(subject,[svar:svars]):svarss]
| not sdef
= ([(subject,svars):opens`],map add closeds`)
= (opens,[(ssym,repvar,[(subject,sargs++svars):ins]):closeds])
  where (opens`,closeds`) = split svarss
        add (sym,repvar,svarss`) = (sym,repvar,[(subject,repvar svar++svars):svarss`])
        (opens,closeds) = split outs
        (ins,outs) = foldr (spl repvar ssym) ([],[]) svarss
        repvar svar = map (const svar) sargs
        (sdef,(ssym,sargs)) = varcontents subject svar

/*

Spl, given a symbol, derives two lists of multipatterns  from  one.  The
first  are  the  multipatterns  of which the first pattern can match the
symbol, i.e. open ones and closed ones with  the  correct  symbol.   The
second  are  the  multipatterns  that can match other symbols, i.e. also
open ones, and closed ones with the wrong symbol.

*/

spl
 :: (var -> [var])
    sym
    (Pattern sym var)
    ([Pattern sym var],[Pattern sym var])
 -> ([Pattern sym var],[Pattern sym var])
 |  == sym
 &  == var

spl repvar sym (subject,[svar:svars]) (ins,outs)
| not sdef
= ([(subject,repvar svar++svars):ins],[(subject,[svar:svars]):outs])
| ssym==sym
= ([(subject,sargs++svars):ins],outs)
= (ins,[(subject,[svar:svars]):outs])
  where (sdef,(ssym,sargs)) = varcontents subject svar
