definition module backendsupport

//1.3
from StdArray import size, size_u
//3.1
/*2.0
from StdArray import size, usize
0.2*/
from StdFunc import `bind`
from StdInt import +, ==

import utilities

identity
	:==	\x -> x

// binding sugar
(==>) infix
(==>) f g
	:== f `bind` g

// o` :== flip o
(o`) infixr
(o`) f g
	:==	\x -> g (f x)

(:-) infixl
(:-) a f
	:== f a


foldState function list
	:== foldState list
	where
		foldState []
			=	identity
		foldState [hd:tl]
			=	function hd
			o`	foldState tl

foldStateA function array
	:== foldStateA 0
	where
		arraySize
			=	size array
		foldStateA index
			| index == arraySize
				=	identity
			// otherwise
				=	function array.[index]
				o`	foldStateA (index+1)

foldStateWithIndexA function array
	:== foldStateWithIndexA 0
	where
		arraySize
			=	size array
		foldStateWithIndexA index
			| index == arraySize
				=	identity
			// otherwise
				=	function index array.[index]
				o`	foldStateWithIndexA (index+1)

foldrA function result array
	:== foldrA result 0
	where
		arraySize
			=	size array
		foldrA result index
			| index == arraySize
				=	result
			// otherwise
				=	function array.[index] (foldrA result (index+1))
