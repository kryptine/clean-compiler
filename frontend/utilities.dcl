definition module utilities

from StdEnv import Eq, not, Ord, IncDec
import StdMisc, general

import _aconcat
   
/*
	For Strings
*/

//1.3
from StdString import String
//3.1

stringToCharList	:: !String -> [Char]
charListToString	:: ![Char] -> String
revCharListToString	:: !Int ![Char] -> String

isUpperCaseName :: ! String -> Bool
isLowerCaseName :: ! String -> Bool
isFunnyIdName 	:: ! String -> Bool
isSpecialChar	:: ! Char	-> Bool

/*
	For Lists
*/

isNotEmpty :: ![a] -> Bool

//mapSt :: !(.a -> (.st -> (.c,.st))) ![.a] !.st -> (![.c],!.st)

mapSt f l s :== map_st l s
where
	map_st [x : xs] s
	 	# (x, s) = f x s
		  mapSt_result = map_st xs s
		  (xs, _) = mapSt_result
		#! s = second_of_2_tuple mapSt_result
		= ([x : xs], s)
	map_st [] s
	 	= ([], s)
	
second_of_2_tuple t :== e2
	where
		(_,e2) = t

app2St :: !(!.(.a -> .(.st -> (.c,.st))),!.(.e -> .(.st -> (.f,.st)))) !(.a,.e) !.st -> (!(.c,.f),!.st)

mapAppendSt :: !(.a -> .(.b -> (.c,.b))) ![.a] !u:[.c] !.b -> !(!u:[.c],!.b)

strictMap :: !(.a -> .b) ![.a] -> [.b]

strictMapAppend :: !(.a -> .b) ![.a] !u:[.b] -> v:[.b], [u <= v]

mapAppend :: !(.a -> .b) ![.a] !u:[.b] -> u:[.b]

//zip2Append :: [.a] [.b] u:[w:(.a,.b)] -> v:[x:(.a,.b)], [w <= x, u <= v]

eqMerge :: ![a] ![a] -> [a] | Eq a

// foldl2 :: !(.c -> .(.a -> .(.b -> .c))) !.c ![.a] ![.b] -> .c
foldl2 op r l1 l2
	:== foldl2 r l1 l2
where
	foldl2 r [x : xs] [y : ys]
		= foldl2 (op r x y) xs ys
	foldl2 r [] []
		= r
//foldr2 :: !(.a -> .(.b -> .(.c -> .c))) !.c ![.a] ![.b] -> .c

foldr2 op r l1 l2
	:== foldr2 r l1 l2
where
	foldr2 r [x : xs] [y : ys]
		= op x y (foldr2 r xs ys)	
	foldr2 r [] []
		= r

fold2St op l1 l2 st
	:== fold_st2 l1 l2 st
where
	fold_st2 [x : xs] [y : ys] st
		= op x y (fold_st2 xs ys st)	
	fold_st2 [] [] st
		= st
	fold_st2 [] ys st
		= abort ("fold_st2: second argument list contains more elements")
	fold_st2 xs [] st
		= abort ("fold_st2: first argument list contains more elements")


// foldSt :: !(.a -> .(.st -> .st)) ![.a] !.st -> .st
foldSt op l st :== fold_st l st
	where
		fold_st [] st		= st
		fold_st [a:x] st	= fold_st x (op a st)

// iFoldSt :: (Int -> .(.b -> .b)) !Int !Int .b -> .b
iFoldSt op fr to st :== i_fold_st fr to st
	where
		i_fold_st fr to st
			| fr >= to
				= st
				= i_fold_st (inc fr) to (op fr st)

iterateSt op st :== iterate_st op st
	where
		iterate_st op st
			# (continue, st) = op st
			| continue
				= iterate_st op st
				= st

revAppend	:: ![a] ![a] -> [a]	//	Reverse the list using the second argument as accumulator.
revMap :: !(.a -> .b) ![.a] !u:[.b] -> u:[.b]

