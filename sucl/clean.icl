implementation module clean

// $Id$

/*

clean.lit - Clean core language
===============================

Description
-----------

This script contains  the  implementation  of  the  core  of  the  Clean
language.

------------------------------------------------------------

Interface
---------

Exported identifiers:

>   %export            ||  law.lit cli.lit test.lit

>       cleanpart      ||     +       +        -
>       node           ||     +       +        +
>       symbol         ||     +       +        +
>       typenode       ||     +       +        +
>       typesymbol     ||     +       +        +

>       cleantyperule  ||     -       +        -
>       corecomplete   ||     +       +        -
>       coretypeinfo
>       coretyperule   ||     -       +        -
>       readcleanparts ||     -       +        -
>       showcleanpart
>       shownode       ||     -       -        +
>       showsymbol     ||     +       +        +
>       showtypenode   ||     -       +        -
>       showtypesymbol ||     -       +        -
>       symbolmodule
>       typesymbolmodule
>       usersym

>       cleanalias
>       cleanmacro
>       cleantype
>       cleanrule

>       heap     ||  Infinite list of anonymous nodes
>       typeheap ||  Infinite list of anonymous type nodes

------------------------------------------------------------

Includes
--------

>   %include "basic.lit"
>   %include "hunt.lit"
>   %include "graph.lit" -extgraph
>   %include "rule.lit"

------------------------------------------------------------

Implementation
--------------

Implementation of identifier

>   typesymbol
>   ::= INT              | ||  Integer
>       BOOL             | ||  Boolean
>       CHAR             | ||  Character
>       STRING           | ||  String
>       REAL             | ||  Real
>       FILE             | ||  File
>       FN               | ||  Function
>       LIST             | ||  List
>       TUPLE num        | ||  Tuple of specific arity
>       USER [char] [char] ||  User-defined type <module.ident>

>   typenode
>   ::= NAMED [char] | ||  A type node with an explicit nodeid
>       ANONYMOUS num  ||  A type node without an explicit nodeid

>   symbol
>   ::= Int num          | ||  A specific integer
>       Bool bool        | ||  A specific boolean
>       Char char        | ||  A specific character
>       String [char]    | ||  A specific string
>       Real num         | ||  A specific real
>       Tuple num        | ||  The tuple constructor of specific arity
>       Cons             | ||  The list constructor
>       Nil              | ||  The empty list
>       Apply            | ||  The curried function application symbol
>       If               | ||  The predefined if symbol
>       Select num num   | ||  The tuple element selector for tuple arity and element number
>       User [char] [char] ||  A user-defined symbol <module.ident>

>   node
>   ::= Named [char] | ||  A node with an explicit nodeid
>       Anonymous num  ||  A node without an explicit nodeid

>   cleanpart
>   ::= Typeexport typesymbol |
>       Alias typesymbol [typenode] typenode [(typenode,(typesymbol,[typenode]))] |
>       Algebra typesymbol [symbol] |
>       Export symbol |
>       Macro symbol [node] node [(node,(symbol,[node]))] |
>       Type symbol [typenode] typenode [(typenode,(typesymbol,[typenode]))] [char] |
>       Rules symbol |
>       Rule symbol [node] node [(node,(symbol,[node]))] |
>       Constructor symbol

>   showcleanpart :: cleanpart -> [char]
>   showcleanpart = show

>   ct = printrule show show.coretyperule

>   coreconstructor :: symbol -> bool

>   coreconstructor (Int    i) = True
>   coreconstructor (Bool   b) = True
>   coreconstructor (Char   c) = True
>   coreconstructor (String s) = True
>   coreconstructor (Real   r) = True
>   coreconstructor (Tuple  a) = True
>   coreconstructor (Cons    ) = True
>   coreconstructor (Nil     ) = True
>   coreconstructor (Apply   ) = True
>   coreconstructor (If      ) = False
>   coreconstructor (Select a i) = False
>   coreconstructor (User m n) = False

>   coreexports :: [symbol]

>   coreexports = []

>   coreimported :: symbol -> bool

>   coreimported (Int    i) = False
>   coreimported (Bool   b) = False
>   coreimported (Char   c) = False
>   coreimported (String s) = False
>   coreimported (Real   r) = False
>   coreimported (Tuple  a) = False
>   coreimported (Cons    ) = False
>   coreimported (Nil     ) = False
>   coreimported (Apply   ) = True
>   coreimported (If      ) = False
>   coreimported (Select a i) = False
>   coreimported (User m n) = False

>   corerules :: symbol -> [rule symbol node]

>   corerules (Int    i) = []
>   corerules (Bool   b) = []
>   corerules (Char   c) = []
>   corerules (String s) = []
>   corerules (Real   r) = []
>   corerules (Tuple  a) = []
>   corerules (Cons    ) = []
>   corerules (Nil     ) = []
>   corerules (Apply   ) = []
>   corerules (If      )
>   =   [   mkrule [Named "cond",Named "then",Named "else"] (Named "else") (updategraph (Named "cond") (Bool False,[]) emptygraph)
>       ,   mkrule [Named "cond",Named "then",Named "else"] (Named "then") (updategraph (Named "cond") (Bool True ,[]) emptygraph)
>       ]
>   corerules (Select a i) = [mkrule [Named "tuple"] (Anonymous i) (updategraph (Named "tuple") (Tuple a,map Anonymous [1..a]) emptygraph)]
>   corerules (User m n) = []

    coresymbols :: [symbol]

    coresymbols = [If,Select a i]

>   coretyperule (Int    i) = mkrule [] (NAMED "int"   ) (updategraph (NAMED "int"   ) (INT   ,[]) emptygraph)
>   coretyperule (Bool   b) = mkrule [] (NAMED "bool"  ) (updategraph (NAMED "bool"  ) (BOOL  ,[]) emptygraph)
>   coretyperule (Char   c) = mkrule [] (NAMED "char"  ) (updategraph (NAMED "char"  ) (CHAR  ,[]) emptygraph)
>   coretyperule (String s) = mkrule [] (NAMED "string") (updategraph (NAMED "string") (STRING,[]) emptygraph)
>   coretyperule (Real   r) = mkrule [] (NAMED "real"  ) (updategraph (NAMED "real"  ) (REAL  ,[]) emptygraph)
>   coretyperule (Tuple  a)
>   =   mkrule args (NAMED "tuple") (updategraph (NAMED "tuple") (TUPLE a,args) emptygraph)
>       where args = take a (map ANONYMOUS [1..])
>   coretyperule Cons = mkrule [NAMED "element",NAMED "list"] (NAMED "list") (updategraph (NAMED "list") (LIST,[NAMED "element"]) emptygraph)
>   coretyperule Nil = mkrule [] (NAMED "list") (updategraph (NAMED "list") (LIST,[NAMED "element"]) emptygraph)
>   coretyperule Apply = mkrule [NAMED "fn",NAMED "arg"] (NAMED "res") (updategraph (NAMED "fn") (FN,[NAMED "arg",NAMED "res"]) emptygraph)
>   coretyperule If = mkrule [NAMED "bool",NAMED "res",NAMED "res"] (NAMED "res") (updategraph (NAMED "bool") (BOOL,[]) emptygraph)
>   coretyperule (Select a i) = mkrule [NAMED "tuple"] (ANONYMOUS i) (updategraph (NAMED "tuple") (TUPLE a,map ANONYMOUS [1..a]) emptygraph)
>   coretyperule (User m n) = error ("coretyperule: untyped user symbol "++m++'.':n)

>   coretypeinfo :: symbol -> (rule typesymbol typenode,[bool])
>   coretypeinfo sym
>   =   (trule,corestricts sym)
>       where corestricts Apply = [True,False]
>             corestricts If    = [True,False,False]
>             corestricts (Select a i) = [True]
>             corestricts sym = map (const False) (lhs trule)
>             trule = coretyperule sym

>   readcleanparts :: [char] -> [cleanpart]
>   readcleanparts = readvals.findclean

>   findclean :: [char] -> [char]
>   findclean base
>   =   foldr const (error ("findclean: "++show base++" not found.")) files
>       where files = findfiles readable ["",".cli"] (getpath ["."] "CLIPATH") base

>   corecomplete :: typesymbol -> [symbol] -> bool

>   corecomplete INT = const False
>   corecomplete BOOL = superset (map Bool [False,True])
>   corecomplete CHAR = superset (map (Char.decode) [0..255])
>   corecomplete STRING = const False
>   corecomplete REAL = const False
>   corecomplete FILE = const False
>   corecomplete FN = const False
>   corecomplete LIST = superset [Nil,Cons]
>   corecomplete (TUPLE arity) = superset [Tuple arity]
>   corecomplete (USER module identifier) = const False

>   showtypesymbol INT = "INT"
>   showtypesymbol BOOL = "BOOL"
>   showtypesymbol CHAR = "CHAR"
>   showtypesymbol STRING = "STRING"
>   showtypesymbol REAL = "REAL"
>   showtypesymbol FILE = "FILE"
>   showtypesymbol FN = "=>"
>   showtypesymbol LIST = "_LIST"
>   showtypesymbol (TUPLE a) = "_TUPLE"++shownum a
>   showtypesymbol (USER module ident) = ident

>   showtypenode (NAMED ident) = ident
>   showtypenode (ANONYMOUS n) = "type"++shownum n

>   showtypenodedef :: typesymbol -> [([char],[char])] -> ([char],[char])
>   showtypenodedef (TUPLE a) [] = issafe "()"
>   showtypenodedef (TUPLE a) [arg] = arg
>   showtypenodedef (TUPLE a) ((safearg,unsafearg):args)
>   =   issafe ('(':unsafearg++f args)
>       where f [] = ")"
>             f ((safearg,unsafearg):args) = ',':unsafearg++f args
>   showtypenodedef LIST [(safearg,unsafearg)] = issafe ('[':unsafearg++"]")
>   showtypenodedef symbol [] = issafe (showtypesymbol symbol)
>   showtypenodedef symbol args = showappl (showtypesymbol symbol) args

>   showsymbol :: symbol -> [char]
>   showsymbol (Int i) = shownum i
>   showsymbol (Bool False) = "FALSE"
>   showsymbol (Bool True) = "TRUE"
>   showsymbol (Char c) = show c
>   showsymbol (String s) = show s
>   showsymbol (Real r) = show (r+0.0)
>   showsymbol (Tuple a) = "_Tuple"++show a
>   showsymbol Cons = "_CONS"
>   showsymbol Nil = "[]"
>   showsymbol Apply = "_AP"
>   showsymbol If = "IF"
>   showsymbol (Select a i) = "_Select"++show a++'.':show i
>   showsymbol (User module ident) = ident

>   shownode (Named ident) = ident
>   shownode (Anonymous n) = "node"++shownum n

>   shownodedef :: symbol -> [([char],[char])] -> ([char],[char])
>   shownodedef (Tuple a) [] = issafe "()"
>   shownodedef (Tuple a) [arg] = arg
>   shownodedef (Tuple a) ((safearg,unsafearg):args)
>   =   issafe ('(':unsafearg++f args)
>       where f [] = ")"
>             f ((safearg,unsafearg):args) = ',':unsafearg++f args
>   shownodedef Cons [(safehead,unsafehead),(safetail,unsafetail)]
>   =   issafe ('[':unsafehead++f unsafetail)
>       where f "[]" = "]"
>             f ('[':ttail) = ',':ttail
>             f unsafetail = '|':unsafetail++"]"
>   shownodedef Apply [fn] = fn
>   shownodedef Apply ((safefn,unsafefn):args) = showappl unsafefn args
>   shownodedef symbol [] = issafe (showsymbol symbol)
>   shownodedef symbol args = showappl (showsymbol symbol) args

>   showappl sym args = mksafe (sym++concat (map ((' ':).fst) args))
>   mksafe unsafe = ('(':unsafe++")",unsafe)
>   issafe safe = (safe,safe)

>   cleantyperule :: symbol -> (rule typesymbol typenode,[bool]) -> [char]

>   cleantyperule sym (trule,tstricts)
>   =   "::  "++showsymbol sym++concat (map2 printarg tstricts targs)++" -> "++snd (lookup' troot)++";"
>       where targs = lhs trule; troot = rhs trule; tgraph = rulegraph trule
>             lookup' = lookup table
>             table = map (pairwith printunraveled) (nodelist tgraph (troot:targs))
>             printunraveled tnode
>             =   showtypenodedef tsym (map lookup' targs), if tdef
>             =   issafe (showtypenode tnode), otherwise
>                 where (tdef,(tsym,targs)) = nodecontents tgraph tnode
>             printarg tstrict targ = ' ':cond tstrict ('!':) id (fst (lookup' targ))

>   prettyrule :: (**->[char]) -> (*->[([char],[char])]->([char],[char])) -> rule * ** -> [char]
>   prettyrule shownode shownodedef rule
>   =   concat (map ((++" ").fst) (init shownnodes))++"-> "++snd (last shownnodes)
>       where shownnodes = foldgraph prettydef (issafe.shownode) shownodedef graph (args++[root])
>             prettydef node (saferef,unsaferef) = issafe (shownode node++':':saferef)
>             graph = rulegraph rule
>             args = lhs rule
>             root = rhs rule

>   usersym :: symbol -> bool
>   usersym (User module name) = True
>   usersym sym = False

>   symbolmodule :: symbol -> optional [char]
>   symbolmodule (User module ident) = Present module
>   symbolmodule symbol = Absent

>   typesymbolmodule :: typesymbol -> optional [char]
>   typesymbolmodule (USER module ident) = Present module
>   typesymbolmodule symbol = Absent

========================================================================

Get the Select nodes from a graph.

>   getselectnodes :: graph symbol ** -> ** -> [((**,num),(num,**))]

>   getselectnodes graph root
>   =   foldr (withmeta (nodecontents graph) addselectnode) [] (nodelist graph [root])
>       where addselectnode (True,(Select arity index,[tuplenode])) selectnode
>             =   (((tuplenode,arity),(index,selectnode)):)
>             addselectnode contents node = id

Distribute the Select nodes over their indexes.

>   splitselectnodes :: ((**,num),[(num,**)]) -> (**,[[**]])

>   splitselectnodes ((tuplenode,arity),selects)
>   =   (tuplenode,foldr dist (rep arity []) selects)
>       where dist (1,selectnode) (ns:nss) = (selectnode:ns):nss
>             dist (index,selectnode) (ns:nss) = ns:dist (index-1,selectnode) nss

Make left hand sides.

>   makelhss :: [**] -> [[**]] -> ([**],[[**]])

>   makelhss heap nss
>   =   (heap,[]), if empty
>   =   (heap'',ns':nss''), otherwise
>       where (heap'',nss'') = makelhss heap' nss'
>             (empty,ns',heap',nss') = heads heap nss
>             heads heap [] = (True,[],heap,[])
>             heads (node:heap) ([]:nss)
>             =   (empty,node:ns',heap',[]:nss')
>                 where (empty,ns',heap',nss') = heads heap nss
>             heads heap ((n:ns):nss)
>             =   (False,n:ns',heap',ns:nss')
>                 where (empty,ns',heap',nss') = heads heap nss

>   maketuplenodedefs :: [**] -> [(**,[[**]])] -> [([**],**)]

>   maketuplenodedefs heap []
>   =   []
>   maketuplenodedefs heap ((tuplenode,nss):rest)
>   =   map (converse pair tuplenode) lhss++tuplenodedefs
>       where (heap',lhss) = makelhss heap nss
>             tuplenodedefs = maketuplenodedefs heap' rest

>   printtree :: graph symbol node -> node -> ([char],[char])
>   printtree = unravelwith (issafe.shownode) shownodedef

>   cleanalias sym = indent "::  ".totalpretty typeheap (const (const [])) showtypesymbol showtypenodedef showtypenode sym
>   cleanmacro sym = indent "    ".totalpretty heap (const (const [])) showsymbol shownodedef shownode sym
>   cleantype sym = indent "::  ".totalpretty typeheap (const (const [])) showsymbol showtypenodedef showtypenode sym
>   cleanrule sym = indent "    ".totalpretty heap getselectnodes showsymbol shownodedef shownode sym

>   heap = map Anonymous [0..]
>   typeheap = map ANONYMOUS [0..]

>   totalpretty
>   ::  [***] ->
>       (graph ** ***->***->[((***,num),(num,***))]) ->
>       (*->[char]) ->
>       (**->[([char],[char])]->([char],[char])) ->
>       (***->[char]) ->
>       * ->
>       rule ** *** ->
>       [[char]]

>   totalpretty heap getselectnodes showlhssymbol shownodedef shownode lhssymbol rule
>   =   punctuate "" "," "    " "" lhsheader lhsbody++
>       punctuate "->  " "," "    " ";" rhsheader rhsbody

>       where

>             args = lhs rule; root = rhs rule; graph = rulegraph rule
>             selectnodes = getselectnodes graph root
>             prunedgraph = foldr prunegraph graph (map (snd.snd) selectnodes)
>             tuplenodedefs
>             =   (   maketuplenodedefs (heap--nodelist graph (root:args)).
>                     map splitselectnodes.
>                     partition fst snd
>                 ) selectnodes
>             tuplenodes = map snd tuplenodedefs
>             count = refcount prunedgraph (args++root:tuplenodes)
>             sharednodes = [node|node<-nodelist prunedgraph (args++root:tuplenodes);count node>1;fst (nodecontents prunedgraph node)]
>             reprunedgraph = foldr prunegraph prunedgraph sharednodes
>             (argreprs:[rootrepr]:tuplereprs:sharedargreprs)
>             =   map (map (unravelwith (issafe.shownode) shownodedef reprunedgraph)) (args:[root]:tuplenodes:map (snd.snd.nodecontents prunedgraph) sharednodes)

>             showtupledef (selectnodes,tuplenode) tuplerepr
>             =   '(':join ',' (map shownode selectnodes)++"): "++snd tuplerepr
>             showshareddef (node,argreprs)
>             =   mapfst addline, if patnode node
>             =   mapsnd addline, otherwise
>                 where addline = ((shownode node++": "++snd (shownodedef (fst cont) argreprs)):)
>                       (True,cont) = nodecontents prunedgraph node

>             patnode = member (nodelist graph args)

>             lhsheader = showlhssymbol lhssymbol++concat (map ((' ':).fst) argreprs)
>             rhsheader = snd rootrepr
>             (lhslines,rhslines) = foldr showshareddef ([],[]) (zip2 sharednodes sharedargreprs)
>             lhsbody = lhslines
>             rhsbody = map2 showtupledef tuplenodedefs tuplereprs++rhslines

>   punctuate :: [char] -> [char] -> [char] -> [char] -> [char] -> [[char]] -> [[char]]

>   punctuate open endline beginline close l ls
>   =   (open++l++end):ls'
>       where (end,ls') = f ls
>             f [] = (close,[])
>             f (l:ls) = (endline,punctuate beginline endline beginline close l ls)

------------------------------------------------------------------------
Useful (higher order) functions.

>   withmeta :: (*->**) -> (**->*->***) -> * -> ***
>   withmeta meta f x = f (meta x) x

>   pair :: * -> ** -> (*,**)
>   pair x y = (x,y)

>   unravelwith :: (**->***) -> (*->[***]->***) -> graph * ** -> ** -> ***
>   unravelwith foldopen foldclosed graph
>   =   unravel
>       where unravel node
>             =   foldclosed sym (map unravel args), if def
>             =   foldopen node, otherwise
>                 where (def,(sym,args)) = nodecontents graph node

*/
