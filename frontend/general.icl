implementation module general

import StdEnv

::	Bind a b =
	{	bind_src :: !a
	,	bind_dst :: !b
	}	

::	Env a b :== [.Bind a b]

::	Optional x = Yes !x | No

cMAXINT :== 2147483647

::	BITVECT :== Int

instance ~ Bool
where ~ b = not b

instance <<< Bool
where
	(<<<) file bool = file <<< (toString bool)

instance <<< (a,b) | <<< a & <<< b
where
	(<<<) file (x,y) = file <<< '(' <<< x <<< ", " <<< y <<< ") "

instance <<< (a,b,c) | <<< a & <<< b & <<< c
where
	(<<<) file (x,y,z) = file <<< '(' <<< x <<< ", " <<< y <<< ", " <<< z <<< ") "

instance <<< (a,b,c,d) | <<< a & <<< b & <<< c & <<< d
where
	(<<<) file (w,x,y,z) = file <<< '(' <<< w <<< ", " <<< x <<< ", " <<< y <<< ", " <<< z <<< ") "

instance <<< (a,b,c,d,e) | <<< a & <<< b & <<< c & <<< d & <<< e
where
	(<<<) file (v,w,x,y,z) = file <<< '(' <<< v <<< ", " <<< w <<< ", " <<< x <<< ", " <<< y <<< ", " <<< z <<< ") "

instance <<< [a] | <<< a
where
	(<<<) file [] = file <<< "[]"
	(<<<) file l  = showTail (file <<< "[") l
	where
		showTail f [x]   = f <<< x <<< "] "
		showTail f [a:x] = showTail (f <<< a <<< ", ") x
		showTail f []    = f <<< "] "

(--->) infix :: .a !b -> .a | <<< b
(--->) val message
	| file_to_true (stderr <<< message <<< '\n')
		= val
		= halt

(-?->) infix :: .a !(!Bool, !b) -> .a | <<< b
(-?->) val (cond, message)  
	| cond
		| file_to_true (stderr <<< message <<< '\n')
			= val
			= halt
		= val

file_to_true :: !File -> Bool
file_to_true file = code {
  .inline file_to_true
          pop_b 2
          pushB TRUE
  .end
  }

halt :: .a
halt = code {
	halt
 }

instance + {#Char}
where
	(+) s t = s +++ t
