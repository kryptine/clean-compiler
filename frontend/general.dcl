definition module general

from StdEnv import <<<, +, ~

instance ~ Bool

instance <<< Bool
instance <<< (a,b) | <<< a & <<< b
instance <<< (a,b,c) | <<< a & <<< b & <<< c
instance <<< (a,b,c,d) | <<< a & <<< b & <<< c & <<< d
instance <<< (a,b,c,d,e) | <<< a & <<< b & <<< c & <<< d & <<< e
instance <<< [a] | <<< a

::	Bind a b =
	{	bind_src :: !a
	,	bind_dst :: !b
	}	

::	Env a b :== [Bind a b]

::	Optional x = Yes !x | No

(--->) infix :: .a !b -> .a | <<< b
(-?->) infix :: .a !(!Bool, !b) -> .a | <<< b

instance + {#Char}

cMAXINT :== 2147483647

::	BITVECT :== Int

