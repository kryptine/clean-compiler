definition module containers

from syntax import Optional
from StdOverloaded import toString

:: NumberSet = Numbers !Int !NumberSet | EndNumbers

addNr :: !Int !NumberSet -> NumberSet
inNumberSet :: !Int !NumberSet -> Bool
numberSetUnion :: !NumberSet !NumberSet -> NumberSet
nsFromTo :: !Int -> NumberSet
	// all numbers from 0 to (i-1)
bitvectToNumberSet :: !LargeBitvect -> .NumberSet

:: LargeBitvect :== {#Int}

bitvectSelect :: !Int !LargeBitvect -> Bool
bitvectSet :: !Int !*LargeBitvect -> .LargeBitvect 
bitvectReset :: !Int !*LargeBitvect -> .LargeBitvect
bitvectCreate :: !Int -> .LargeBitvect 
bitvectResetAll :: !*LargeBitvect -> .LargeBitvect 

:: IntKey :== Int

:: IntKeyHashtable a = IntKeyHashtable !Int !Int !Int !.{!.IntKeyTree a}
	
:: IntKeyTree a = IKT_Leaf | IKT_Node !IntKey a !.(IntKeyTree a) !.(IntKeyTree a)

ikhEmpty :: .(IntKeyHashtable a)
ikhInsert :: !Bool !IntKey a !*(IntKeyHashtable a) -> (!Bool, !.IntKeyHashtable a)
	// input bool: overide old value, output bool: a new element was inserted
ikhInsert` :: !Bool !IntKey a !*(IntKeyHashtable a) -> .IntKeyHashtable a
	// bool: overide old value
ikhSearch :: !IntKey !(IntKeyHashtable a) -> .Optional a
ikhSearch` :: !IntKey !(IntKeyHashtable a) -> a
ikhUSearch :: !IntKey !*(IntKeyHashtable a) -> (!.Optional a, !*IntKeyHashtable a)

iktUInsert :: !Bool !IntKey a !*(IntKeyTree a) -> (!Bool, !.IntKeyTree a)
	// input bool: overide old value, output bool: a new element was inserted
iktFlatten :: !(IntKeyTree a) -> [(IntKey, a)]
iktSearch :: !IntKey !(IntKeyTree a) -> .Optional a
iktSearch` :: !IntKey !(IntKeyTree a) -> a
iktUSearch :: !IntKey !*(IntKeyTree a) -> (!.Optional a,!.IntKeyTree a)

instance toString (IntKeyTree a) | toString a, (IntKeyHashtable a) | toString a
