implementation module utilities

import	StdEnv, general

from _aconcat import arrayConcat
    

/*
		Utility routines.
*/
StringToCharList`	:: !String !Int !Int -> [Char]
StringToCharList` string 0 index
		= 	[]
StringToCharList` string length index
		= [string.[index] : StringToCharList` string (dec length) (inc index)]
		
stringToCharList	:: !String ->	[Char]
stringToCharList string = StringToCharList` string (size string) 0

charListToString	:: ![Char] -> String
charListToString [hd:tl] = toString hd +++ charListToString tl 
charListToString []      = ""

revCharListToString	:: !Int ![Char] -> String
revCharListToString max_index l
	# string = createArray (max_index + 1) '\0'
	= fill_string max_index l string
where
	fill_string :: !Int ![Char] !*String -> *String
	fill_string n [ char : rest] string
		= fill_string (n - 1) rest { string & [n] = char }
	fill_string (-1) [] string
		= string
		  
/*
revCharListToString [hd:tl] = revCharListToString tl +++ toString hd 
revCharListToString []      = ""
*/

isUpperCaseName :: ! String -> Bool
isUpperCaseName id
	= ('A' <= c  &&  c <= 'Z') || c == '_' 
   	  where
   	  c =: id.[0]

isLowerCaseName :: ! String -> Bool
isLowerCaseName id
	= 'a' <= c  &&  c <= 'z' 
   	  where
   	  c =: id.[0]

isFunnyIdName :: ! String -> Bool
isFunnyIdName id
	= isSpecialChar id.[0]

isSpecialChar	:: !Char -> Bool
isSpecialChar '~'	= True
isSpecialChar '@'	= True
isSpecialChar '#'	= True
isSpecialChar '$'	= True
isSpecialChar '%'	= True
isSpecialChar '^'	= True
isSpecialChar '?'	= True
isSpecialChar '!'	= True
isSpecialChar '+'	= True
isSpecialChar '-'	= True
isSpecialChar '*'	= True
isSpecialChar '<'	= True
isSpecialChar '>'	= True
isSpecialChar '\\'	= True
isSpecialChar '/'	= True
isSpecialChar '|'	= True
isSpecialChar '&'	= True
isSpecialChar '='	= True
isSpecialChar ':'	= True
isSpecialChar '.'	= True
isSpecialChar c	= False

isNotEmpty :: ![a] -> Bool
isNotEmpty [] = False
isNotEmpty _  = True

strictMap :: !(.a -> .b) ![.a] -> [.b]
strictMap f [x : xs]
		#!	head = f x
			tail = strictMap f xs
		=	[head : tail]
strictMap f xs
		= []

strictMapAppend :: !(.a -> .b) ![.a] !u:[.b] -> v:[.b], [u <= v]
strictMapAppend f [x : xs] tail
	#! x = f x
	   xs = strictMapAppend f xs tail
	= [x : xs]
strictMapAppend f [] tail
	= tail

mapAppend :: !(.a -> .b) ![.a] !u:[.b] -> u:[.b]
mapAppend f [x : xs] tail
	#  x = f x
	   xs = mapAppend f xs tail
	= [x : xs]
mapAppend f [] tail
	= tail


mapAppendSt :: !(.a -> .(.b -> (.c,.b))) ![.a] !u:[.c] !.b -> !(!u:[.c],!.b)
mapAppendSt f [x : xs] tail s 
	# (x, s) = f x s
	  (xs, s) = mapAppendSt f xs tail s
	= ([x : xs], s)
mapAppendSt f [] tail s
	= (tail, s)

/*
mapSt :: !(.a -> (.st -> (.c,.st))) ![.a] !.st -> (![.c],!.st)
mapSt f [x : xs] s
 	# (x, s) = f x s
	  (xs, s) = mapSt f xs s
	= ([x : xs], s)
mapSt f [] s
 	= ([], s)
*/
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
app2St (f,g) (x,y) s
 	# (x, s) = f x s
	  (y, s) = g y s
	= ((x,y), s)


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
foldSt op r l :== fold_st r l
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

eqMerge :: ![a] ![a] -> [a] | Eq a
eqMerge [a : x] y
	| isMember a y
		= eqMerge x y
		= [a : eqMerge x y]
eqMerge x y
		= y

revAppend	:: ![a] ![a] -> [a]	//	Reverse the list using the second argument as accumulator.
revAppend [] acc = acc
revAppend [x : xs] acc = revAppend xs [x : acc]

revMap :: !(.a -> .b) ![.a] !u:[.b] -> u:[.b]
revMap f [] acc = acc
revMap f [x : xs] acc = revMap f xs [f x : acc]



/*		
zip2Append :: [.a] [.b] u:[w:(.a,.b)] -> v:[x:(.a,.b)], [w <= x, u <= v]
zip2Append [] [] tail
	= tail
zip2Append [x : xs] [y : ys] tail
	= [(x,y) : zip2Append xs ys tail]
*/

:: Bag x = Empty | Single !x | Pair !(Bag x) !(Bag x)

uniqueBagToList :: !*(Bag x) -> [x] // exploits reuse of unique nodes (if compiled with that option)
uniqueBagToList bag
	= accumulate_elements bag []
  where
	accumulate_elements :: !*(Bag x) [x] -> [x]
	accumulate_elements Empty accu
		= accu
	accumulate_elements (Single element) accu
		= [element : accu]
	accumulate_elements (Pair bag1 bag2) accu
		= accumulate_elements bag1 (accumulate_elements bag2 accu)
		
bagToList :: !(Bag x) -> [x]
bagToList bag
	= accumulate_elements bag []
  where
	accumulate_elements :: !(Bag x) [x] -> [x]
	accumulate_elements Empty accu
		= accu
	accumulate_elements (Single element) accu
		= [element : accu]
	accumulate_elements (Pair bag1 bag2) accu
		= accumulate_elements bag1 (accumulate_elements bag2 accu)
		
isEmptyBag :: !(Bag x) -> Bool
isEmptyBag Empty = True
isEmptyBag _ = False
