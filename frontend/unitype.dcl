definition module unitype

import StdEnv
import syntax, analunitypes

::	CoercionPosition =
	{	cp_expression	:: !Expression
	}

AttrUni			:== 0
AttrMulti		:== 1
FirstAttrVar	:== 2

instance toInt TypeAttribute

::	CoercionTree	= CT_Node !Int !CoercionTree !CoercionTree | CT_Empty | CT_Unique | CT_NonUnique  /* | CT_Existential !Int */

::	Coercions		= { coer_demanded :: !.{! .CoercionTree}, coer_offered :: !.{! .CoercionTree }}

isNonUnique 	:: !CoercionTree -> Bool
isUnique		:: !CoercionTree -> Bool
// isExistential	:: !CoercionTree -> Bool

::	BOOLVECT :== Int

BITINDEX temp_var_id :== temp_var_id >> 5
BITNUMBER temp_var_id :== temp_var_id bitand 31

determineAttributeCoercions :: !AType !AType !Bool !CoercionPosition !u:{! Type} !*Coercions !{# CommonDefs } 
	!{# BOOLVECT } !*TypeDefInfos !*TypeHeaps !*ErrorAdmin
		-> (!u:{! Type}, !*Coercions, !*TypeDefInfos, !*TypeHeaps, !*ErrorAdmin) 

::	AttributePartition	:== {# Int}

partitionateAttributes :: !{! CoercionTree} !{! *CoercionTree} -> (!AttributePartition, !{! CoercionTree})

newInequality :: !Int !Int !*Coercions -> *Coercions

tryToMakeNonUnique :: !Int !*Coercions -> (!Bool, !*Coercions)

tryToMakeUnique :: !Int !*Coercions -> (!Bool, !*Coercions)

uniquenessError :: !CoercionPosition !String !*ErrorAdmin -> *ErrorAdmin

liftSubstitution :: !*{! Type} !{# CommonDefs } !Int !*TypeVarHeap !*TypeDefInfos -> (*{! Type}, !Int, !*TypeVarHeap, !*TypeDefInfos)

instance <<< CoercionPosition

