definition module typesupport

import checksupport, StdCompare

from unitype import Coercions, CoercionTree, AttributePartition

do_fusion :== False
// MW: this switch is used to en(dis)able the fusion algorithm which currently isn't ready

errorHeading :: !String !*ErrorAdmin -> *ErrorAdmin

class (<::) infixl a :: !*File (!Format, !a) -> *File

:: Format =
	{	form_properties :: !BITVECT
	,	form_position	:: ![Int]
	}

cNoProperties		:== 0
cAttributed			:== 4
cAnnotated			:== 8

instance <:: SymbolType, Type, AType, [a] | <:: a

::	AttributeEnv	:== {! TypeAttribute }
::	VarEnv 			:== {! Type }

cleanSymbolType :: !Int !*TypeHeaps -> (!SymbolType, !*TypeHeaps)
extendSymbolType :: !SymbolType !Int !*TypeHeaps -> (!SymbolType, !*TypeHeaps)

cleanUpSymbolType :: !TempSymbolType ![TypeContext] ![ExprInfoPtr] !{! CoercionTree} !AttributePartition
						!*VarEnv !*AttributeEnv !*TypeHeaps !*ExpressionHeap !*ErrorAdmin
							-> (!SymbolType, !*VarEnv, !*AttributeEnv, !*TypeHeaps, !*ExpressionHeap, !*ErrorAdmin)

expandTypeApplication :: ![ATypeVar] !TypeAttribute !Type ![AType] !TypeAttribute !*TypeHeaps -> (!Type, !*TypeHeaps)

equivalent :: !SymbolType  !TempSymbolType !{# CommonDefs} !*AttributeEnv !*TypeHeaps -> (!Bool, !*AttributeEnv, !*TypeHeaps) 

::	AttrCoercion =
	{	ac_demanded	:: !Int
	,	ac_offered	:: !Int
	}

::	TempSymbolType =
	{	tst_args		:: ![AType]
	,	tst_arity		:: !Int
	,	tst_lifted		:: !Int
	,	tst_result		:: !AType
	,	tst_context		:: ![TypeContext]
	,	tst_attr_env	:: ![AttrCoercion]
	}

class substitute a :: !a !u:TypeHeaps -> (!a, !u:TypeHeaps)

instance substitute AType, Type, TypeContext, AttrInequality, [a] | substitute a
instance <<< TempSymbolType
