implementation module containers

import StdEnv, utilities, syntax

:: NumberSet = Numbers !Int !NumberSet | EndNumbers

inNumberSet :: !Int !NumberSet -> Bool
inNumberSet n EndNumbers
	= False;
inNumberSet n (Numbers module_numbers rest_module_numbers)
	| n<32
		= (module_numbers bitand (1<<n))<>0
		= inNumberSet (n-32) rest_module_numbers

nsFromTo :: !Int -> NumberSet
	// all numbers from 0 to (i-1)
nsFromTo i
	| i<=0
		= EndNumbers
	| i<=31
	 	= Numbers (bitnot ((-1)<<i)) EndNumbers
	= Numbers (-1) (nsFromTo (i-32))

addNr :: !Int !NumberSet -> NumberSet
addNr n EndNumbers
	| n<32
		= Numbers (1<<n) EndNumbers
		= Numbers 0 (addNr (n-32) EndNumbers)
addNr n (Numbers module_numbers rest_module_numbers)
	| n<32
		= Numbers (module_numbers bitor (1<<n)) rest_module_numbers
		= Numbers module_numbers (addNr (n-32) rest_module_numbers)

numberSetUnion :: !NumberSet !NumberSet -> NumberSet
numberSetUnion EndNumbers x
	= x
numberSetUnion x EndNumbers
	= x
numberSetUnion (Numbers i1 tail1) (Numbers i2 tail2)
	= Numbers (i1 bitor i2) (numberSetUnion tail1 tail2)

is_empty_module_n_set EndNumbers
	= True;
is_empty_module_n_set (Numbers 0 module_numbers)
	= is_empty_module_n_set module_numbers
is_empty_module_n_set _
	= False;

remove_first_module_number (Numbers 0 rest_module_numbers)
	# (bit_n,rest_module_numbers) = remove_first_module_number rest_module_numbers
	= (bit_n+32,Numbers 0 rest_module_numbers)
remove_first_module_number (Numbers module_numbers rest_module_numbers)
	# bit_n = first_one_bit module_numbers
	= (bit_n,Numbers (module_numbers bitand (bitnot (1<<bit_n))) rest_module_numbers)

first_one_bit module_numbers
	| module_numbers bitand 0xff<>0
		= first_one_bit_in_byte 0 module_numbers
	| module_numbers bitand 0xff00<>0
		= first_one_bit_in_byte 8 module_numbers
	| module_numbers bitand 0xff0000<>0
		= first_one_bit_in_byte 16 module_numbers
		= first_one_bit_in_byte 24 module_numbers

first_one_bit_in_byte n module_numbers
	| module_numbers bitand (1<<n)<>0
		= n
		= first_one_bit_in_byte (n+1) module_numbers

bitvectToNumberSet :: !LargeBitvect -> .NumberSet
bitvectToNumberSet a
	= loop a (size a - 1)
  where
	loop a (-1)
		= EndNumbers
	loop a i
		| a.[i]==0
			= loop a (i-1) 
		= loop2 a i EndNumbers
		
	loop2 a (-1) accu
		= accu
	loop2 a i accu
		= loop2 a (i-1) (Numbers a.[i] accu)

BITINDEX index :== index >> 5
BITNUMBER index :== index bitand 31

:: LargeBitvect :== {#Int}

bitvectSelect :: !Int !LargeBitvect -> Bool
bitvectSelect index a
	= a.[BITINDEX index] bitand (1 << BITNUMBER index) <> 0

bitvectSet :: !Int !*LargeBitvect -> .LargeBitvect 
bitvectSet index a
	#! bit_index = BITINDEX index
	   a_bit_index = a.[bit_index]
	= { a & [bit_index] = a_bit_index bitor (1 << BITNUMBER index)}

bitvectCreate :: !Int -> .LargeBitvect 
bitvectCreate 0 = {}
bitvectCreate n_elements = createArray ((BITINDEX (n_elements-1)+1)) 0

bitvectReset :: !*LargeBitvect -> .LargeBitvect 
bitvectReset arr
	#! size
			= size arr
	= { arr & [i] = 0 \\ i<-[0..size-1] } // list should be optimized away
bitvectOr :: !u:LargeBitvect !*LargeBitvect -> (!Bool, !u:LargeBitvect, !*LargeBitvect)
// Boolean result: whether the unique bitvect has changed
bitvectOr op1 op2
	#! size
		= size op1
	= iFoldSt word_or 0 size (False, op1, op2)
  where
	word_or i (has_changed, op1=:{[i]=op1_i}, op2=:{[i]=op2_i})
		# or = op1_i bitor op2_i
		| or==op2_i
			= (has_changed, op1, op2)
		= (True, op1, { op2 & [i] = or })

screw :== 80

:: IntKey :== Int

:: IntKeyHashtable a =
	{	ikh_rehash_threshold	:: !Int
	,	ikh_nr_of_entries		:: !Int
	,	ikh_bitmask				:: !Int
	,	ikh_entries				:: !.{!.IntKeyTree a}
	}
	
:: IntKeyTree a = IKT_Leaf | IKT_Node !IntKey a !.(IntKeyTree a) !.(IntKeyTree a)

ikhEmpty :: .(IntKeyHashtable a)
ikhEmpty = { ikh_rehash_threshold = 0, ikh_nr_of_entries = 0,
				ikh_bitmask = 0, ikh_entries = {} }

ikhInsert :: !Bool !IntKey a !*(IntKeyHashtable a) -> (!Bool, !.IntKeyHashtable a)
ikhInsert overide int_key value ikh=:{ ikh_rehash_threshold, ikh_nr_of_entries, ikh_bitmask, ikh_entries }
	| ikh_rehash_threshold<=ikh_nr_of_entries
		= ikhInsert overide int_key value (grow ikh_entries)
	#! hash_value
			= int_key bitand ikh_bitmask
	   (tree, ikh_entries)
			= replace ikh_entries hash_value IKT_Leaf
	   (is_new, tree)
	   		= iktUInsert overide int_key value tree 
	   ikh
	   		= { ikh & ikh_entries = { ikh_entries & [hash_value] = tree }}
	| is_new
		= (is_new, { ikh & ikh_nr_of_entries = ikh_nr_of_entries+1 })
	= (is_new, ikh)

grow :: !{!*(IntKeyTree a)} -> .(IntKeyHashtable a)
grow old_entries
	#! size
			= size old_entries
	   new_size
	   		= if (size==0) 2 (2*size)
	   new_entries
	   		= { IKT_Leaf \\ i<-[1..new_size] }
	   ikh
			= { ikh_rehash_threshold = (new_size*screw)/100, ikh_nr_of_entries = 0,
				ikh_bitmask = new_size-1, ikh_entries = new_entries }
	   (_, ikh)
	   		= iFoldSt rehashTree 0 size (old_entries, ikh)
	= ikh
  where
	rehashTree :: !Int (!{!*IntKeyTree a}, !*IntKeyHashtable a)
				-> (!{!*IntKeyTree a}, !*IntKeyHashtable a)
	rehashTree index (old_entries, ikh)
		#! (tree, old_entries)
				= replace old_entries index IKT_Leaf
		   list
		   		= iktFlatten tree
		   ikh
		   		= foldSt (\(key, value) ikh -> snd (ikhInsert False key value ikh)) list ikh
		= (old_entries, ikh)

ikhInsert` :: !Bool !IntKey a !*(IntKeyHashtable a) -> .IntKeyHashtable a
ikhInsert` overide int_key value ikh
	= snd (ikhInsert overide int_key value ikh)

ikhSearch :: !IntKey !(IntKeyHashtable a) -> .Optional a
ikhSearch int_key {	ikh_bitmask, ikh_entries }
	| size ikh_entries==0
		= No
	= iktSearch int_key ikh_entries.[int_key bitand ikh_bitmask]

ikhSearch` :: !IntKey !(IntKeyHashtable a) -> a
ikhSearch` int_key {ikh_bitmask, ikh_entries }
	| size ikh_entries==0
		= abort "ikhSearch`: key not found"
	= iktSearch` int_key ikh_entries.[int_key bitand ikh_bitmask]

ikhUSearch :: !IntKey !*(IntKeyHashtable a) -> (!.Optional a, !*IntKeyHashtable a)
ikhUSearch int_key ikh=:{ikh_bitmask, ikh_entries}
	| size ikh_entries==0
		= (No, ikh)
	# hash_value
			= int_key bitand ikh_bitmask
	  (ikt, ikh_entries)
			= replace ikh_entries hash_value IKT_Leaf
	  (opt_result, ikt)
			= iktUSearch int_key ikt
	  ikh_entries
	  		= { ikh_entries & [hash_value] = ikt }
	= (opt_result, { ikh & ikh_entries = ikh_entries })

iktUInsert :: !Bool !IntKey a !*(IntKeyTree a) -> (!Bool, !.IntKeyTree a)
iktUInsert overide int_key value IKT_Leaf
	= (True, IKT_Node int_key value IKT_Leaf IKT_Leaf)
iktUInsert overide int_key value (IKT_Node key2 value2 left right)
	| int_key<key2
		# (is_new, left`)
				= iktUInsert overide int_key value left
		= (is_new, IKT_Node key2 value2 left` right)
	| int_key>key2
		# (is_new, right`)
				= iktUInsert overide int_key value right
		= (is_new, IKT_Node key2 value2 left right`)
	| overide
		= (False, IKT_Node int_key value left right)
	= (False, IKT_Node key2 value2 left right)

iktFlatten :: !(IntKeyTree a) -> [(IntKey, a)]
iktFlatten ikt
	= flatten ikt []
  where
	flatten IKT_Leaf accu
		= accu
	flatten (IKT_Node int_key value left right) accu
		= flatten left [(int_key, value) : flatten right accu]

iktUSearch :: !IntKey !*(IntKeyTree a) -> (!.Optional a,.IntKeyTree a)
iktUSearch int_key leaf=:IKT_Leaf
	= (No, leaf)
iktUSearch int_key ikt=:(IKT_Node key2 value left right)
	| int_key<key2
		# (opt_result, left)
			= iktUSearch int_key left
		= (opt_result, IKT_Node key2 value left right)
	| int_key>key2
		# (opt_result, right)
			= iktUSearch int_key right
		= (opt_result, IKT_Node key2 value left right)
	= (Yes value, ikt)
		
iktSearch :: !IntKey !(IntKeyTree a) -> .Optional a
iktSearch int_key IKT_Leaf
	= No
iktSearch int_key (IKT_Node key2 value left right)
	| int_key<key2
		= iktSearch int_key left
	| int_key>key2
		= iktSearch int_key right
	= Yes value
		
iktSearch` :: !IntKey !(IntKeyTree a) -> a
iktSearch` int_key (IKT_Node key2 value left right)
	| int_key<key2
		= iktSearch` int_key left
	| int_key>key2
		= iktSearch` int_key right
	= value
iktSearch` int_key IKT_Leaf
	= abort "iktSearch`: key not found"
		
instance toString (IntKeyTree a) | toString a
  where
	toString ikt
		# list
			= iktFlatten ikt
		= listToString "," list


listToString _ []
	= "[]"
listToString del l
	= "["+++lts l
  where
	lts [a]
		= toString a+++"]"
	lts [h:t]
		= toString h+++del+++lts t

instance toString {!a} | toString a
  where
	toString arr
		# list
			= arrayToList arr
		= listToString " , " list
	  where
		arrayToList :: {!a} -> [a]
		arrayToList arr = [el \\ el<-:arr]
		
instance toString (IntKeyHashtable a) |toString a
  where
	toString { ikh_rehash_threshold, ikh_nr_of_entries, ikh_bitmask, ikh_entries }
		= "(IKH "+++toString ikh_rehash_threshold+++" "+++toString ikh_nr_of_entries
			+++" "+++toString ikh_bitmask+++" "+++toString ikh_entries

instance toString (a, b) | toString a & toString b
  where
	toString (a, b)
		= "("+++toString a+++","+++toString b+++")"
 