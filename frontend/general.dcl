definition module general

/*2.0
from StdEnv import instance <<< Int,class <<< (..),instance + Int,class + (..),instance ~ Int,class ~ (..)
0.2*/
//1.3
from StdEnv import <<<, +, ~
//3.1

instance ~ Bool

instance <<< Bool
instance <<< (a,b) | <<< a & <<< b
instance <<< (a,b,c) | <<< a & <<< b & <<< c
instance <<< (a,b,c,d) | <<< a & <<< b & <<< c & <<< d
instance <<< (a,b,c,d,e) | <<< a & <<< b & <<< c & <<< d & <<< e
instance <<< (a,b,c,d,e,f) | <<< a & <<< b & <<< c & <<< d & <<< e & <<< f
instance <<< (a,b,c,d,e,f,g) | <<< a & <<< b & <<< c & <<< d & <<< e & <<< f & <<< g
instance <<< [a] | <<< a

::	Bind a b =
	{	bind_src :: !a
	,	bind_dst :: !b
	}	

::	Env a b :== [.Bind a b]

::	Optional x = Yes !x | No

hasOption :: (Optional x) -> Bool

::	Choice a b  = Either a | Or b

(--->) infix :: .a !b -> .a | <<< b
(-?->) infix :: .a !(!Bool, !b) -> .a | <<< b

instance + {#Char}

cMAXINT :== 2147483647

::	BITVECT :== Int

