implementation module backendpreprocess

// assign sequence numbers to all variables in the syntax tree

import checksupport
import Heap
import backendsupport
import RWSDebug

backendPreprocess :: !Ident ![Index] !IclModule !*VarHeap -> *VarHeap
backendPreprocess aliasDummyId functionIndices iclModule varHeap
	=	preprocess aliasDummyId
					[iclModule.icl_functions.[i] \\ i <- functionIndices] varHeap

class preprocess a :: !Ident a -> Preprocessor
:: Preprocessor
	:==	*PreprocessState -> *PreprocessState
:: PreprocessState
	:==	VarHeap

//1.3
instance preprocess {#a} | preprocess a & ArrayElem a where
//3.1
/*2.0
instance preprocess {#a} | preprocess a & Array {#} a where
0.2*/
	preprocess aliasDummyId array
		=	foldStateA (preprocess aliasDummyId) array

instance preprocess [a] | preprocess a where
	preprocess aliasDummyId list
		=	foldState (preprocess aliasDummyId) list

// +++ this assigns sequence numbers per function, should be per alternative and move to backendconvert
instance preprocess FunDef where
	preprocess aliasDummyId funDef
		=	fromSequencerToPreprocessor aliasDummyId (sequence funDef.fun_body)

class sequence a :: a -> Sequencer
:: Sequencer
	:== *SequenceState -> *SequenceState
:: SequenceState
	=	{ss_sequenceNumber :: !Int, ss_varHeap :: .VarHeap, ss_aliasDummyId :: !Ident}

toSequenceState aliasDummyId varHeap
	:==	{ss_sequenceNumber = 0, ss_varHeap = varHeap, ss_aliasDummyId = aliasDummyId}
fromSequenceState sequenceState
	:==	sequenceState.ss_varHeap

fromSequencerToPreprocessor aliasDummyId sequencer
	:==	toSequenceState aliasDummyId
	o`	sequencer
	o`	fromSequenceState

assignSequenceNumber varInfoPtr sequenceState
	:==	{	sequenceState
		&	ss_varHeap = writePtr varInfoPtr (VI_SequenceNumber sequenceState.ss_sequenceNumber) sequenceState.ss_varHeap
		,	ss_sequenceNumber = sequenceState.ss_sequenceNumber + 1
		}

instance sequence [a] | sequence a where
	sequence list
		=	foldState sequence list

instance sequence (Optional a) | sequence a where
	sequence (Yes x)
		=	sequence x
	sequence No
		=	identity

// +++ this assigns sequence numbers per function, should be per alternative and moved to backendconvert
instance sequence FunctionBody where
	sequence (BackendBody backEndBodies)
		=	sequence backEndBodies
	sequence body
		=	abort "preprocess (FunctionBody): unknown body" <<- body

instance sequence BackendBody where
	sequence body
		=	sequence body.bb_args
		o`	sequence body.bb_rhs

instance sequence FreeVar where
	sequence freeVar
		=	sequence freeVar.fv_info_ptr

instance sequence Expression where
	sequence (Let {let_strict_binds, let_lazy_binds, let_expr})
		=	sequence let_strict_binds
		o`	sequence let_lazy_binds
		o`	sequence let_expr
	sequence (Conditional {if_then, if_else})
		=	sequence if_then
		o`	sequence if_else
	sequence (App {app_args})
		=	sequence app_args
	sequence (f @ arg)
		=	sequence f
		o`	sequence arg
	sequence (Selection _ exp selections)
		=	sequence exp
		o`	sequence selections
	sequence (AnyCodeExpr _ outParams _)
		=	foldState (\{bind_dst}->sequence bind_dst) outParams
	sequence _
		=	identity

instance sequence Selection where
	sequence (RecordSelection _ _)
		=	identity
	sequence (ArraySelection _ _ index)
		=	sequence index
	sequence (DictionarySelection dictionaryVar dictionarySelections _ index)
		=	sequence index

instance sequence (Bind Expression FreeVar) where
	sequence {bind_src=App app , bind_dst}
		= sequence` app bind_dst
	  where
	  	sequence` {app_symb, app_args} bind_dst sequenceState=:{ss_aliasDummyId}
			| app_symb.symb_name==ss_aliasDummyId
				// the compiled source was a strict alias like "#! x = y"
				= case hd app_args of
					Var bound_var=:{var_info_ptr}
						# (vi, ss_varHeap) = readPtr var_info_ptr sequenceState.ss_varHeap
						  non_alias_bound_var = case vi of
													VI_SequenceNumber _		-> bound_var
													VI_Alias alias_bound_var-> alias_bound_var
						  ss_varHeap = writePtr bind_dst.fv_info_ptr (VI_Alias non_alias_bound_var) ss_varHeap
						-> { sequenceState & ss_varHeap = ss_varHeap }
					_
						-> sequence bind_dst sequenceState
		= sequence bind_dst sequenceState
	sequence bind
		=	sequence bind.bind_dst

instance sequence FunctionPattern where
	sequence (FP_Algebraic _ subpatterns optionalVar)
		=	sequence subpatterns
		o`	sequence optionalVar
	sequence (FP_Variable freeVar)
		=	sequence freeVar
	sequence (FP_Basic _ optionalVar)
		=	sequence optionalVar
	sequence FP_Empty
		=	identity

instance sequence (Ptr VarInfo) where
	sequence varInfoPtr
		=	assignSequenceNumber varInfoPtr
