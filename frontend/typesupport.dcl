definition module typesupport

import checksupport, StdCompare

from unitype import Coercions, CoercionTree, AttributePartition

// MW: this switch is used to en(dis)able the fusion algorithm
SwitchFusion fuse dont_fuse :== dont_fuse

errorHeading :: !String !*ErrorAdmin -> *ErrorAdmin

// MW4 was:class (<::) infixl a :: !*File (!Format, !a) -> *File
(<::) infixl :: !*File (!Format, !a, !Optional TypeVarBeautifulizer) -> *File | writeType a

class writeType a :: !*File !(Optional TypeVarBeautifulizer) (!Format, !a) -> (!*File, !Optional TypeVarBeautifulizer)

:: Format =
	{	form_properties 	:: !BITVECT
	,	form_attr_position	:: Optional ([Int], Coercions)
	}

cNoProperties		:== 0
cAttributed			:== 1
cAnnotated			:== 2
cMarkAttribute		:== 4

:: TypeVarBeautifulizer // MW++

instance writeType SymbolType, Type, AType, [a] | writeType a

initialTypeVarBeautifulizer :: TypeVarBeautifulizer // MW4++

::	AttributeEnv	:== {! TypeAttribute }
::	VarEnv 			:== {! Type }

cleanSymbolType :: !Int !*TypeHeaps -> (!SymbolType, !*TypeHeaps)
extendSymbolType :: !SymbolType !Int !*TypeHeaps -> (!SymbolType, !*TypeHeaps)

cSpecifiedType	:== True
cDerivedType	:== False

cleanUpSymbolType :: !Bool !Bool !TempSymbolType ![TypeContext] ![ExprInfoPtr] !{! CoercionTree} !AttributePartition
						!*VarEnv !*AttributeEnv !*TypeHeaps !*VarHeap !*ExpressionHeap !*ErrorAdmin
							-> (!SymbolType, !*VarEnv, !*AttributeEnv, !*TypeHeaps, !*VarHeap, !*ExpressionHeap, !*ErrorAdmin)

expandTypeApplication :: ![ATypeVar] !TypeAttribute !Type ![AType] !TypeAttribute !*TypeHeaps -> (!Type, !*TypeHeaps)

equivalent :: !SymbolType !TempSymbolType !Int !{# CommonDefs} !*AttributeEnv !*TypeHeaps -> (!Bool, !*AttributeEnv, !*TypeHeaps) 

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

::	FunctionType = CheckedType !SymbolType | SpecifiedType !SymbolType ![AType] !TempSymbolType
				 | UncheckedType !TempSymbolType | ExpandedType !SymbolType !TempSymbolType !TempSymbolType  | EmptyFunctionType


updateExpressionTypes :: !SymbolType !SymbolType ![ExprInfoPtr] !*TypeHeaps !*ExpressionHeap -> (!*TypeHeaps, !*ExpressionHeap)

class substitute a :: !a !*TypeHeaps -> (!a, !*TypeHeaps)

instance substitute AType, Type, TypeContext, AttrInequality, CaseType, [a] | substitute a

instance <<< TempSymbolType
