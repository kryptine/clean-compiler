implementation module comparedefimp

/*	compare definition and implementation module

	Difficulty: The icl module's type definitions have been tranformed during checking while
	the dcl module's type definitions have not. When the root of the rhs of a (icl) type definition was
	originally an application of a synonym type then this type will have been expanded. The comparision
	algorithm performs expansion of _dcl_ synonym types 'on the fly' by binding lhs argument type variables
	to the types of the actual type application. e.g.
		
		dcl:						icl:
		
		:: T1 :== T2 Int			:: T1 :== Int  // previously expanded, was originally :: T1 :== T2 Int
		:: T2 x :== x				:: T2 y :== y
	
	causes x to be bound to Int while processing type T1.
	
	While T2 is processed x and y will be bound to a correspondence number to abstract from variable names
	(see type HeapWithNumber). The same happens with attribute variables and variables in macros/functions.
*/

import syntax, checksupport, compare_constructor, utilities, StdCompare
import RWSDebug

:: TypesCorrespondState =
		{	tc_type_vars
				:: !.HeapWithNumber TypeVarInfo
		,	tc_attr_vars
				:: !.HeapWithNumber AttrVarInfo
		,	tc_dcl_modules
				:: !.{#DclModule}
		,	tc_icl_type_defs
				:: !{CheckedTypeDef}
		,	tc_type_conversions
				:: !Conversions
		, 	tc_visited_syn_types	// to detect cycles in type synonyms
				:: !.{#Bool}
		}

:: TypesCorrespondMonad
		:==	!*TypesCorrespondState -> (!Bool, !*TypesCorrespondState)

:: ExpressionsCorrespondState =
		{	ec_correspondences	// ec_correspondences.[i]==j <=> (functions i and j are already compared 
				::	!.{# Int }	//									|| j==cNoCorrespondence)
		,	ec_var_heap
				::	!.HeapWithNumber VarInfo
		,	ec_expr_heap
				::	!.ExpressionHeap
		,	ec_icl_functions
				::	!.{# FunDef }
		,	ec_error_admin
				::	!.ErrorAdmin
		,	ec_tc_state
				::	!.TypesCorrespondState
		,	ec_untransformed
				::	!(!Int, !{ FunDef })
		}
		
:: ExpressionsCorrespondMonad
		:== !*ExpressionsCorrespondState -> *ExpressionsCorrespondState

:: Conversions :== {#Index}

:: HeapWithNumber a
	=	{	hwn_heap
				::	!.Heap a
		,	hwn_number
				::	!Int
		}

:: OptionalCorrespondenceNumber = CorrespondenceNumber !Int | Bound | Unbound

class t_corresponds a :: !a !a -> *TypesCorrespondMonad
	// whether two types correspond
class e_corresponds a :: !a !a -> ExpressionsCorrespondMonad
	// check for correspondence of expressions

class getIdentPos a :: a -> IdentPos

class CorrespondenceNumber a where
	toCorrespondenceNumber :: .a -> OptionalCorrespondenceNumber
	fromCorrespondenceNumber :: Int -> .a

initial_hwn hwn_heap = { hwn_heap = hwn_heap, hwn_number = 0 }

compareDefImp :: !(!Int, !{FunDef}) !*{# DclModule} !*IclModule !*Heaps !*ErrorAdmin 
				-> (!.{# DclModule}, !.IclModule,!.Heaps,!.ErrorAdmin)
compareDefImp untransformed dcl_modules icl_module heaps error_admin
	# (main_dcl_module, dcl_modules) = dcl_modules![cIclModIndex]
	= case main_dcl_module.dcl_conversions of
		No	-> (dcl_modules, icl_module, heaps, error_admin)
		Yes conversion_table
			# {dcl_functions, dcl_macros, dcl_common, dcl_instances} = main_dcl_module
			  {icl_common, icl_functions}
					= icl_module
			  {hp_var_heap, hp_expression_heap, hp_type_heaps={th_vars, th_attrs}}
			  		= heaps
			  { com_type_defs=icl_com_type_defs, com_cons_defs=icl_com_cons_defs,
				com_selector_defs=icl_com_selector_defs, com_class_defs=icl_com_class_defs,
				com_member_defs=icl_com_member_defs, com_instance_defs = icl_com_instance_defs }
					= icl_common
			  (icl_type_defs, icl_com_type_defs) = memcpy icl_com_type_defs
			  tc_state
			  		=	{ tc_type_vars = initial_hwn th_vars
						, tc_attr_vars = initial_hwn th_attrs
						, tc_dcl_modules = dcl_modules
						, tc_icl_type_defs = icl_type_defs
						, tc_type_conversions = conversion_table.[cTypeDefs]
						, tc_visited_syn_types = createArray (size dcl_common.com_type_defs) False
						}
			  (icl_com_type_defs, tc_state, error_admin)
					= compareWithConversions conversion_table.[cTypeDefs]
						dcl_common.com_type_defs icl_com_type_defs tc_state error_admin
			  (icl_com_cons_defs, tc_state, error_admin)
					= compareWithConversions conversion_table.[cConstructorDefs]
						dcl_common.com_cons_defs icl_com_cons_defs tc_state error_admin
			  (icl_com_selector_defs, tc_state, error_admin)
					= compareWithConversions conversion_table.[cSelectorDefs]
						dcl_common.com_selector_defs icl_com_selector_defs tc_state error_admin
			  (icl_com_class_defs, tc_state, error_admin)
					= compareWithConversions conversion_table.[cClassDefs]
						dcl_common.com_class_defs icl_com_class_defs tc_state error_admin
			  (icl_com_member_defs, tc_state, error_admin)
					= compareWithConversions conversion_table.[cMemberDefs]
						dcl_common.com_member_defs icl_com_member_defs tc_state error_admin
			  (icl_com_instance_defs, tc_state, error_admin)
					= compareWithConversions conversion_table.[cInstanceDefs]
						dcl_common.com_instance_defs icl_com_instance_defs tc_state error_admin
			  (icl_functions, hp_var_heap, hp_expression_heap, tc_state, error_admin)
					= compareMacrosWithConversion conversion_table.[cMacroDefs] dcl_macros untransformed
								 				 icl_functions hp_var_heap hp_expression_heap tc_state error_admin

			  (icl_functions, tc_state, error_admin)
			  		= compareFunctionTypesWithConversions conversion_table.[cFunctionDefs]
			  			dcl_functions icl_functions tc_state error_admin
			  { tc_type_vars, tc_attr_vars, tc_dcl_modules }
			  		= tc_state
			  icl_common
			  		= { icl_common & com_type_defs=icl_com_type_defs, com_cons_defs=icl_com_cons_defs,
			  			com_selector_defs=icl_com_selector_defs, com_class_defs=icl_com_class_defs,
			  			com_member_defs=icl_com_member_defs, com_instance_defs = icl_com_instance_defs }
			  heaps
			  		= { hp_var_heap = hp_var_heap, hp_expression_heap = hp_expression_heap,
			  			hp_type_heaps = { th_vars = tc_type_vars.hwn_heap, th_attrs = tc_attr_vars.hwn_heap}}
			-> ( tc_dcl_modules, { icl_module & icl_common = icl_common, icl_functions = icl_functions },
					heaps, error_admin )
  where
	memcpy :: !*{#CheckedTypeDef} -> (!.{CheckedTypeDef}, !.{#CheckedTypeDef})
	memcpy original
		#! size = size original
		# new = createArray size (abort "don't make that array strict !")
		= iFoldSt (\i (dst, src=:{[i]=src_i}) -> ({ dst & [i] = src_i }, src)) 0 size (new, original)

compareWithConversions conversions dclDefs iclDefs tc_state error_admin 
	= iFoldSt (compareWithConversion conversions dclDefs) 0 (size conversions) (iclDefs, tc_state, error_admin)

compareWithConversion :: !w:(a x:Int) !.(b c) !Int !(!u:(d c), !*TypesCorrespondState, !*ErrorAdmin)
						-> (!v:(d c), !.TypesCorrespondState, !.ErrorAdmin)
						| Array .b & getIdentPos , select_u , t_corresponds , uselect_u c & Array .d & Array .a, [u <= v, w <= x];
compareWithConversion conversions dclDefs dclIndex (iclDefs, tc_state, error_admin)
	# icl_index = conversions.[dclIndex]
	| icl_index==dclIndex
		= (iclDefs, tc_state, error_admin)
	# (iclDef, iclDefs) = iclDefs![icl_index]
	  (corresponds, tc_state) = t_corresponds dclDefs.[dclIndex] iclDef tc_state
	| corresponds
		= (iclDefs, tc_state, error_admin)
	= generate_error error_message iclDef iclDefs tc_state error_admin

compareFunctionTypesWithConversions conversions	dcl_fun_types icl_functions tc_state error_admin
	= iFoldSt (compareTwoFunctionTypes conversions dcl_fun_types) 0 (size conversions)
				(icl_functions, tc_state, error_admin)

compareTwoFunctionTypes :: !w:(a x:Int) !.(b FunType) !.Int !(!u:(c FunDef),!*TypesCorrespondState,!*ErrorAdmin)
						-> (!v:(c FunDef),!.TypesCorrespondState,!.ErrorAdmin)
						| Array .b & Array .c & Array .a, [u <= v, w <= x];
compareTwoFunctionTypes conversions	dcl_fun_types dclIndex (icl_functions, tc_state, error_admin)
	# (fun_def=:{fun_type}, icl_functions) = icl_functions![conversions.[dclIndex]]
	= case fun_type of
		No	-> generate_error "type of exported function is missing" fun_def icl_functions tc_state error_admin
		Yes icl_symbol_type
			# dcl_symbol_type = dcl_fun_types.[dclIndex].ft_type
			  tc_state = init_attr_vars (dcl_symbol_type.st_attr_vars++icl_symbol_type.st_attr_vars)
			  							tc_state
			  tc_state = init_type_vars (dcl_symbol_type.st_vars++icl_symbol_type.st_vars) tc_state
			  (corresponds, tc_state)
					= t_corresponds dcl_symbol_type icl_symbol_type tc_state
			| corresponds
				-> (icl_functions, tc_state, error_admin)
			-> generate_error error_message fun_def icl_functions tc_state error_admin

init_type_vars type_vars tc_state=:{tc_type_vars}
	# tc_type_vars = init_type_vars` type_vars tc_type_vars
	= { tc_state & tc_type_vars = tc_type_vars }
  where
	init_type_vars` type_vars tc_type_vars=:{hwn_heap}
		# hwn_heap = foldSt init_type_var type_vars hwn_heap
		= { tc_type_vars & hwn_heap = hwn_heap }
	init_type_var {tv_info_ptr} heap
		= writePtr tv_info_ptr TVI_Empty heap
	
generate_error message iclDef iclDefs tc_state error_admin
	# ident_pos = getIdentPos iclDef
	  error_admin = pushErrorAdmin ident_pos error_admin
	  error_admin = checkError ident_pos.ip_ident message error_admin
	= (iclDefs, tc_state, popErrorAdmin error_admin)

compareMacrosWithConversion conversions macro_range untransformed icl_functions var_heap expr_heap tc_state error_admin
	#! nr_of_functions = size icl_functions
	# correspondences = createArray nr_of_functions cNoCorrespondence
	  ec_state = { ec_correspondences = correspondences, ec_var_heap = initial_hwn var_heap, 
	  				ec_expr_heap = expr_heap, ec_icl_functions = icl_functions,
	  				ec_error_admin = error_admin, ec_tc_state = tc_state,
	  				ec_untransformed = untransformed }
	  ec_state = iFoldSt (compareMacroWithConversion conversions macro_range.ir_from) macro_range.ir_from macro_range.ir_to
	  						ec_state
	  {ec_icl_functions, ec_var_heap, ec_expr_heap, ec_error_admin, ec_tc_state} = ec_state
	= (ec_icl_functions, ec_var_heap.hwn_heap, ec_expr_heap, ec_tc_state, ec_error_admin)
	
compareMacroWithConversion conversions ir_from dclIndex ec_state
	= compareTwoMacroFuns dclIndex conversions.[dclIndex-ir_from] ec_state

compareTwoMacroFuns :: !.Int !.Int !*ExpressionsCorrespondState -> .ExpressionsCorrespondState;
compareTwoMacroFuns dclIndex iclIndex
					ec_state=:{ec_correspondences, ec_icl_functions, ec_untransformed}
	| dclIndex==iclIndex
		= ec_state
	# (dcl_function, ec_icl_functions) = ec_icl_functions![dclIndex]
	  (icl_function, ec_icl_functions) = ec_icl_functions![iclIndex]
	  ec_correspondences = { ec_correspondences & [dclIndex]=iclIndex, [iclIndex]=dclIndex }
	  ec_state = { ec_state & ec_correspondences = ec_correspondences, ec_icl_functions = ec_icl_functions }
	  need_to_be_compared
	  		= case (dcl_function.fun_body, icl_function.fun_body) of
	  			(TransformedBody _, CheckedBody _)
					// the macro definition in the icl module is not used, so we don't need to compare
	  				-> False
	  			_	-> True
	| not need_to_be_compared
		= ec_state
	# adjusted_icl_function
	  		= case (dcl_function.fun_body, icl_function.fun_body) of
	  			(CheckedBody _, TransformedBody _)
					// the macro definition in the icl module is has been transformed but not the dcl
					// module's definition: use the untransformed icl original for comparision
	  				# (offset, untransformed_icl_functions) = ec_untransformed
	  				-> untransformed_icl_functions.[iclIndex-offset]
	  			_	-> icl_function
	  ident_pos = getIdentPos dcl_function
	  ec_error_admin = pushErrorAdmin ident_pos ec_state.ec_error_admin
	  ec_state = e_corresponds dcl_function adjusted_icl_function { ec_state & ec_error_admin = ec_error_admin }
	= { ec_state & ec_error_admin = popErrorAdmin ec_state.ec_error_admin }

instance getIdentPos (TypeDef a) where
	getIdentPos {td_name, td_pos}
		= newPosition td_name td_pos

instance getIdentPos ConsDef where
	getIdentPos {cons_symb, cons_pos}
		= newPosition cons_symb cons_pos

instance getIdentPos SelectorDef where
	getIdentPos {sd_symb, sd_pos}
		= newPosition sd_symb sd_pos

instance getIdentPos ClassDef where
	getIdentPos {class_name, class_pos}
		= newPosition class_name class_pos

instance getIdentPos MemberDef where
	getIdentPos {me_symb, me_pos}
		= newPosition me_symb me_pos

instance getIdentPos ClassInstance where
	getIdentPos {ins_ident, ins_pos}
		= newPosition ins_ident ins_pos

instance getIdentPos FunDef where
	getIdentPos {fun_symb, fun_pos}
		= newPosition fun_symb fun_pos

instance CorrespondenceNumber VarInfo where
	toCorrespondenceNumber (VI_CorrespondenceNumber number)
		=	CorrespondenceNumber number
	toCorrespondenceNumber _
		// VarInfoPtrs are not initialized in this module. This doesnt harm because VI_CorrespondenceNumber should
		// not be used outside this module 
		=	Unbound
		
	fromCorrespondenceNumber number
		=	VI_CorrespondenceNumber number

instance CorrespondenceNumber TypeVarInfo where
	toCorrespondenceNumber (TVI_CorrespondenceNumber number)
		=	CorrespondenceNumber number
	toCorrespondenceNumber TVI_Empty
		=	Unbound
	toCorrespondenceNumber (TVI_AType _)
		=	Bound

	fromCorrespondenceNumber number
		=	TVI_CorrespondenceNumber number

instance CorrespondenceNumber AttrVarInfo where
	toCorrespondenceNumber (AVI_CorrespondenceNumber number)
		=	CorrespondenceNumber number
	toCorrespondenceNumber AVI_Empty
		=	Unbound

	fromCorrespondenceNumber number
		=	AVI_CorrespondenceNumber number

assignCorrespondenceNumber ptr1 ptr2 {hwn_heap, hwn_number}
	=	let var_info = fromCorrespondenceNumber hwn_number
		in	{	hwn_heap
					=	writePtr ptr1 var_info (writePtr ptr2 var_info hwn_heap)
			,	hwn_number
					=	hwn_number + 1
			}

tryToUnifyVars ptr1 ptr2 heapWithNumber
	#! info1 = sreadPtr ptr1 heapWithNumber.hwn_heap
	   info2 = sreadPtr ptr2 heapWithNumber.hwn_heap
	=	case (toCorrespondenceNumber info1, toCorrespondenceNumber info2) of
			(CorrespondenceNumber number1, CorrespondenceNumber number2)
				->	(number1==number2, heapWithNumber)
			(Unbound, Unbound)
 				->	(True, assignCorrespondenceNumber ptr1 ptr2 heapWithNumber)
			_	->	(False, heapWithNumber)

instance t_corresponds [a] | t_corresponds a where 
	t_corresponds [] []
		=	return True
	t_corresponds [dclDef:dclDefs] [iclDef:iclDefs]
		=	t_corresponds dclDef iclDef
		&&&	t_corresponds dclDefs iclDefs
	t_corresponds _ _
		=	return False

instance t_corresponds {# a} | t_corresponds , select_u , size_u a where 
	t_corresponds dclArray iclArray
		# size_dclArray = size dclArray
		| size_dclArray<>size iclArray
			= return False
		= loop (size_dclArray-1) dclArray iclArray
	  where
		loop i dclArray iclArray
			| i<0
				= return True
			=	t_corresponds dclArray.[i] iclArray.[i]
			&&& loop (i-1) dclArray iclArray
		
instance t_corresponds (Optional a) | t_corresponds a where 
	t_corresponds No No
		= return True
	t_corresponds (Yes dclYes) (Yes iclYes)
		= t_corresponds dclYes iclYes
	t_corresponds _ _
		= return False

instance t_corresponds (Global DefinedSymbol) where
	t_corresponds dclDef iclDef
		=	t_corresponds dclDef.glob_object iclDef.glob_object
		&&&	equal dclDef.glob_module iclDef.glob_module

instance t_corresponds (TypeDef TypeRhs) where
	t_corresponds dclDef iclDef
		= t_corresponds_TypeDef dclDef iclDef
	  where
		t_corresponds_TypeDef dclDef iclDef tc_state
			# tc_state = { tc_state & tc_visited_syn_types.[dclDef.td_index] = True }
			  tc_state = init_attr_vars dclDef.td_attrs tc_state 
			  tc_state = init_attr_vars iclDef.td_attrs tc_state 
			  tc_state = init_atype_vars dclDef.td_args tc_state
			  tc_state = init_atype_vars iclDef.td_args tc_state
			  (corresponds, tc_state) = t_corresponds dclDef.td_args iclDef.td_args tc_state
			| not corresponds
				= (corresponds, tc_state)
			# icl_root_has_anonymous_attr = root_has_anonymous_attr iclDef.td_attribute iclDef.td_rhs
			| icl_root_has_anonymous_attr<>root_has_anonymous_attr dclDef.td_attribute dclDef.td_rhs
			  && isnt_abstract dclDef.td_rhs
				= (False, tc_state)
			# coerced_icl_rhs = if icl_root_has_anonymous_attr (coerce iclDef.td_rhs) iclDef.td_rhs
			  (corresponds, tc_state) = t_corresponds dclDef.td_rhs coerced_icl_rhs tc_state
			  tc_state = { tc_state & tc_visited_syn_types.[dclDef.td_index] = False }
			| not corresponds
				= (corresponds, tc_state)
			# (corresponds, tc_state) = t_corresponds dclDef.td_context iclDef.td_context tc_state
			| not corresponds
				= (corresponds, tc_state)
			= t_corresponds dclDef.td_attribute iclDef.td_attribute tc_state

		root_has_anonymous_attr (TA_Var lhs_attr_var) syn_type=:(SynType a_type=:{at_attribute=TA_Var rhs_attr_var})
			= rhs_attr_var.av_info_ptr==lhs_attr_var.av_info_ptr
		root_has_anonymous_attr _ _
			= False
		
		coerce (SynType atype)
			= SynType { atype & at_attribute = TA_Anonymous }
		
		isnt_abstract (AbstractType _) = False
		isnt_abstract _ = True
		
instance t_corresponds TypeContext where
	t_corresponds dclDef iclDef
		=	t_corresponds dclDef.tc_class iclDef.tc_class
		&&& t_corresponds dclDef.tc_types iclDef.tc_types

instance t_corresponds DefinedSymbol where
	t_corresponds dclDef iclDef
		=	equal dclDef.ds_ident iclDef.ds_ident

instance t_corresponds ATypeVar where
	t_corresponds dclDef iclDef
		=	t_corresponds dclDef.atv_attribute iclDef.atv_attribute
		&&&	equal dclDef.atv_annotation iclDef.atv_annotation
		&&&	t_corresponds dclDef.atv_variable iclDef.atv_variable

instance t_corresponds AType where
	t_corresponds dclDef iclDef
		= t_corresponds_at_type dclDef iclDef
	  where
		t_corresponds_at_type dclDef iclDef tc_state
			| dclDef.at_annotation<>iclDef.at_annotation
				= (False, tc_state)
			# (corresponds, tc_state) = simple_corresponds dclDef iclDef tc_state
			| corresponds
				= (corresponds, tc_state)
			= case dclDef.at_type of
				TA dcl_type_symb dcl_args
					-> corresponds_with_expanded_syn_type dcl_type_symb.type_index dcl_args iclDef tc_state
				TV {tv_info_ptr}
					#! x = sreadPtr tv_info_ptr tc_state.tc_type_vars.hwn_heap
					-> case x of
						TVI_AType dcl_atype
							-> t_corresponds { dcl_atype & at_annotation = dclDef.at_annotation } iclDef tc_state
						_	-> (False, tc_state)
				_	-> (False, tc_state)
		  where

			simple_corresponds dclDef iclDef
				=	t_corresponds dclDef.at_attribute iclDef.at_attribute
				&&&	t_corresponds dclDef.at_type iclDef.at_type

			corresponds_with_expanded_syn_type {glob_module, glob_object} dclArgs icl_atype
												tc_state
				# is_defined_in_main_dcl = glob_module==cIclModIndex
				| is_defined_in_main_dcl && tc_state.tc_visited_syn_types.[glob_object]
					= (False, tc_state) // cycle in synonym types in main dcl
				# ({dcl_common}, tc_state) = tc_state!tc_dcl_modules.[glob_module]
				  type_def = dcl_common.com_type_defs.[glob_object]
				= case type_def.td_rhs of
					SynType {at_type=TV type_var, at_attribute}
						// a "projection" type. attributes are treated in a special way
						# arg_pos = get_arg_pos type_var type_def.td_args 0
						  dcl_arg = dclArgs!!arg_pos
						  coerced_dcl_arg = { dcl_arg & at_attribute = determine_type_attribute type_def.td_attribute }
						-> t_corresponds coerced_dcl_arg icl_atype tc_state
					SynType atype
						# tc_state = { tc_state & tc_type_vars
						  							= bind_type_vars type_def.td_args dclArgs tc_state.tc_type_vars }
						  tc_state = init_attr_vars type_def.td_attrs tc_state
						  tc_state = opt_set_visited_bit is_defined_in_main_dcl glob_object True tc_state
						  atype = { atype & at_attribute = determine_type_attribute type_def.td_attribute }
						  (corresponds, tc_state) = t_corresponds atype icl_atype tc_state
						  tc_state = opt_set_visited_bit is_defined_in_main_dcl glob_object False tc_state
						-> (corresponds, tc_state) 
					AbstractType _
						#! icl_type_def = tc_state.tc_icl_type_defs.[tc_state.tc_type_conversions.[glob_object]]
						# tc_state = { tc_state & tc_type_vars
				  							= bind_type_vars icl_type_def.td_args dclArgs tc_state.tc_type_vars }
						  tc_state = init_attr_vars icl_type_def.td_attrs tc_state
						-> case icl_type_def.td_rhs of
							SynType atype
								# atype = { atype & at_attribute = determine_type_attribute type_def.td_attribute }
								-> t_corresponds atype icl_atype tc_state
							_	-> (False, tc_state)
					_	-> (False, tc_state)
			  where

				bind_type_vars formal_args actual_args tc_type_vars
					# hwn_heap = bind_type_vars` formal_args actual_args tc_type_vars.hwn_heap
					= { tc_type_vars & hwn_heap = hwn_heap }
			
				bind_type_vars` [{atv_variable}:formal_args] [actual_arg:actual_args] type_var_heap
					# (actual_arg, type_var_heap) = possibly_dereference actual_arg type_var_heap
					= bind_type_vars` formal_args actual_args
							(writePtr atv_variable.tv_info_ptr (TVI_AType actual_arg) type_var_heap)
//								--->("binding", atv_variable.tv_name,"to",actual_arg)
				bind_type_vars` _ _ type_var_heap
					= type_var_heap
				
				possibly_dereference atype=:{at_type=TV {tv_info_ptr}} type_var_heap
					#! dereferenced = sreadPtr tv_info_ptr type_var_heap
					= case dereferenced of
						TVI_AType atype2
							-> (atype2, type_var_heap)
						_	-> (atype, type_var_heap)
				possibly_dereference atype type_var_heap
					= (atype, type_var_heap)
			
				opt_set_visited_bit True glob_object bit tc_state
					= { tc_state & tc_visited_syn_types.[glob_object] = bit }
				opt_set_visited_bit False _ _ tc_state
					= tc_state

				determine_type_attribute TA_Unique	= TA_Unique
				determine_type_attribute _			= TA_Multi
				
				get_arg_pos x [h:t] count
					| x==h.atv_variable	= count
										= get_arg_pos x t (inc count)

instance t_corresponds TypeAttribute where
	t_corresponds TA_Unique TA_Unique
		=	return True
	t_corresponds TA_Multi TA_Multi
		=	return True
	t_corresponds (TA_Var dclDef) (TA_Var iclDef)
		=	t_corresponds dclDef iclDef
	t_corresponds (TA_RootVar dclDef) (TA_RootVar iclDef)
		= SwitchUniquenessBug (return True) (t_corresponds dclDef iclDef)
	t_corresponds _ TA_Anonymous
		=	return True
	t_corresponds TA_None icl
		= case icl of
			TA_Multi-> return True
			TA_None	-> return True
			_		-> return False
	t_corresponds TA_Multi icl
		= case icl of
			TA_Multi-> return True
			TA_None	-> return True
			_		-> return False
	t_corresponds _ _
		=	return False

instance t_corresponds AttributeVar where
	t_corresponds dclDef iclDef
		=	corresponds` dclDef iclDef
	  where
		corresponds` dclDef iclDef tc_state=:{tc_attr_vars}
			# (unifiable, tc_attr_vars) = tryToUnifyVars dclDef.av_info_ptr iclDef.av_info_ptr tc_attr_vars
			= (unifiable, { tc_state & tc_attr_vars = tc_attr_vars })

instance t_corresponds Type where
	t_corresponds (TA dclIdent dclArgs) icl_type=:(TA iclIdent iclArgs)
		=	equal dclIdent.type_name iclIdent.type_name
		&&& equal dclIdent.type_index.glob_module iclIdent.type_index.glob_module
		&&& t_corresponds dclArgs iclArgs
	t_corresponds (dclFun --> dclArg) (iclFun --> iclArg)
		=	t_corresponds dclFun iclFun
		&&&	t_corresponds dclArg iclArg
	t_corresponds (dclVar :@: dclArgs) (iclVar :@: iclArgs)
		=	t_corresponds dclVar iclVar
		&&&	t_corresponds dclArgs iclArgs
	t_corresponds (TB dclDef) (TB iclDef)
		=	equal dclDef iclDef
	t_corresponds (TV dclDef) (TV iclDef)
		=	t_corresponds dclDef iclDef
	t_corresponds (GTV dclDef) (GTV iclDef)
		=	t_corresponds dclDef iclDef
	t_corresponds _ _
		= return False
		
instance t_corresponds ConsVariable where
	t_corresponds (CV dclVar) (CV iclVar)
		=	t_corresponds dclVar iclVar
		
instance t_corresponds TypeVar where
	t_corresponds dclDef iclDef
		=	corresponds_TypeVar dclDef iclDef
	  where
		corresponds_TypeVar dclDef iclDef tc_state=:{tc_type_vars}
			# (unifiable, tc_type_vars) = tryToUnifyVars dclDef.tv_info_ptr iclDef.tv_info_ptr tc_type_vars
			= (unifiable, { tc_state & tc_type_vars = tc_type_vars })

instance t_corresponds TypeRhs where
	t_corresponds (AlgType dclConstructors) (AlgType iclConstructors)
		=	t_corresponds dclConstructors iclConstructors
	t_corresponds (SynType dclType) (SynType iclType)
		=	t_corresponds dclType iclType
	t_corresponds (RecordType dclRecord) (RecordType iclRecord)
		=	t_corresponds dclRecord iclRecord
	t_corresponds (AbstractType _) _
		=	return True
// sanity check ...
	t_corresponds UnknownType _
		=	undef <<- "t_corresponds (TypeRhs): dclDef == UnknownType" 
	t_corresponds _ UnknownType
		=	undef <<- "t_corresponds (TypeRhs): iclDef == UnknownType"
// ... sanity check
	t_corresponds _ _
		=	return False

instance t_corresponds RecordType where
	t_corresponds dclRecord iclRecord
		=	t_corresponds dclRecord.rt_constructor iclRecord.rt_constructor
		&&& t_corresponds dclRecord.rt_fields iclRecord.rt_fields

instance t_corresponds FieldSymbol where
	t_corresponds dclField iclField
		=	equal dclField.fs_name iclField.fs_name

instance t_corresponds ConsDef where
	t_corresponds dclDef iclDef
		=	do (init_atype_vars (dclDef.cons_exi_vars++iclDef.cons_exi_vars))
		&&&	t_corresponds dclDef.cons_type iclDef.cons_type
		&&& equal dclDef.cons_symb iclDef.cons_symb
		&&& equal dclDef.cons_priority iclDef.cons_priority

instance t_corresponds SelectorDef where
	t_corresponds dclDef iclDef
		=	do (init_atype_vars (dclDef.sd_exi_vars++iclDef.sd_exi_vars))
		&&&	t_corresponds dclDef.sd_type iclDef.sd_type
		&&& equal dclDef.sd_field_nr iclDef.sd_field_nr

init_atype_vars atype_vars
					tc_state=:{tc_type_vars}
	# type_heap = foldSt init_type_var atype_vars tc_type_vars.hwn_heap
	  tc_type_vars = { tc_type_vars & hwn_heap = type_heap }
	= { tc_state & tc_type_vars = tc_type_vars }
  where
	init_type_var {atv_variable} type_heap = writePtr atv_variable.tv_info_ptr TVI_Empty type_heap

instance t_corresponds SymbolType where
	t_corresponds dclDef iclDef
		=	t_corresponds dclDef.st_args iclDef.st_args
		&&&	t_corresponds dclDef.st_result iclDef.st_result
		&&&	t_corresponds dclDef.st_context iclDef.st_context
		&&&	t_corresponds dclDef.st_attr_env iclDef.st_attr_env

instance t_corresponds AttrInequality where
	t_corresponds dclDef iclDef
		=	t_corresponds dclDef.ai_demanded iclDef.ai_demanded
		&&&	t_corresponds dclDef.ai_offered iclDef.ai_offered

instance t_corresponds ClassDef where
	t_corresponds dclDef iclDef
		=	do (init_type_vars (dclDef.class_args++iclDef.class_args))
		&&&	equal dclDef.class_name iclDef.class_name
		&&&	t_corresponds dclDef.class_args iclDef.class_args
		&&&	t_corresponds dclDef.class_context iclDef.class_context
		&&&	t_corresponds dclDef.class_members iclDef.class_members

instance t_corresponds MemberDef where
	t_corresponds dclDef iclDef
		=	do (init_type_vars (dclDef.me_type.st_vars++iclDef.me_type.st_vars))
		&&&	do (init_attr_vars (dclDef.me_type.st_attr_vars++iclDef.me_type.st_attr_vars))
		&&& equal dclDef.me_symb iclDef.me_symb
		&&&	equal dclDef.me_offset iclDef.me_offset
		&&&	equal dclDef.me_priority iclDef.me_priority
		&&&	t_corresponds dclDef.me_type iclDef.me_type

instance t_corresponds ClassInstance where
	t_corresponds dclDef iclDef
		= t_corresponds` dclDef.ins_type iclDef.ins_type
	  where
		t_corresponds` dclDef iclDef tc_state
			# tc_state
					= init_attr_vars (dclDef.it_attr_vars++iclDef.it_attr_vars) tc_state
			  tc_state
			  		= init_type_vars (dclDef.it_vars++iclDef.it_vars) tc_state
			  (corresponds, tc_state)
			  		=  t_corresponds dclDef.it_types iclDef.it_types tc_state
			| not corresponds
				= (corresponds, tc_state)
			=  t_corresponds dclDef.it_context iclDef.it_context tc_state

instance t_corresponds DynamicType where
	t_corresponds dclDef iclDef
		= t_corresponds dclDef.dt_type iclDef.dt_type

instance e_corresponds (Optional a) | e_corresponds a where 
	e_corresponds No No
		= do_nothing
	e_corresponds (Yes dclYes) (Yes iclYes)
		= e_corresponds dclYes iclYes
	e_corresponds _ _
		= give_error ""

instance e_corresponds (a, b) | e_corresponds a & e_corresponds b where 
	e_corresponds (a1, b1) (a2, b2)
		=	(e_corresponds a1 a2)
		o`	(e_corresponds b1 b2)

instance e_corresponds [a] | e_corresponds a where 
	e_corresponds [] []
		=	do_nothing
	e_corresponds [dclDef:dclDefs] [iclDef:iclDefs]
		=	e_corresponds dclDef iclDef
		o`	e_corresponds dclDefs iclDefs
	e_corresponds _ _
		=	give_error ""

instance e_corresponds (Global a) | e_corresponds a where
	e_corresponds dclDef iclDef
		=	equal2 dclDef.glob_module iclDef.glob_module
		o`	e_corresponds dclDef.glob_object iclDef.glob_object

instance e_corresponds DefinedSymbol where
	e_corresponds dclDef iclDef
		= equal2 dclDef.ds_ident iclDef.ds_ident

instance e_corresponds FunDef where
	// both bodies are either CheckedBodies or TransformedBodies
	e_corresponds dclDef iclDef
//		| False--->("compare", dclDef, iclDef)
//			= undef
		=	e_corresponds (from_body dclDef.fun_body) (from_body iclDef.fun_body)
	  where
		from_body (TransformedBody {tb_args, tb_rhs}) = (tb_args, [tb_rhs])
		from_body (CheckedBody {cb_args, cb_rhs}) = (cb_args, cb_rhs)

instance e_corresponds TransformedBody where
	e_corresponds dclDef iclDef
		=	e_corresponds dclDef.tb_args iclDef.tb_args
		o`	e_corresponds dclDef.tb_rhs iclDef.tb_rhs

instance e_corresponds FreeVar where
	e_corresponds dclVar iclVar
		=	e_corresponds_VarInfoPtr iclVar.fv_name dclVar.fv_info_ptr iclVar.fv_info_ptr

instance e_corresponds Expression where
	// the following alternatives don't occur anymore: Lambda, Conditional, WildCard
	e_corresponds (Var dcl) (Var icl)
		= 	e_corresponds dcl icl
	e_corresponds (App dcl_app) (App icl_app)
		=	e_corresponds_app_symb dcl_app.app_symb icl_app.app_symb
		o`	e_corresponds dcl_app.app_args icl_app.app_args
	e_corresponds (dclFun @ dclArgs) (iclFun @ iclArgs)
		=	e_corresponds dclFun iclFun
		o`	e_corresponds dclArgs iclArgs
	e_corresponds (Let dcl) (Let icl)
		= 	e_corresponds dcl icl
	e_corresponds (Case dcl) (Case icl)
		= 	e_corresponds dcl icl
	e_corresponds (Selection dcl_is_unique dcl_expr dcl_selections) (Selection icl_is_unique icl_expr icl_selections)
		| not (equal_constructor dcl_is_unique icl_is_unique)
			= give_error "" 
		=	e_corresponds dcl_expr icl_expr
		o`	e_corresponds dcl_selections icl_selections
	e_corresponds (Update dcl_expr_1 dcl_selections dcl_expr_2) (Update icl_expr_1 icl_selections icl_expr_2)
		=	e_corresponds dcl_expr_1 icl_expr_1
		o`	e_corresponds dcl_selections icl_selections
		o`	e_corresponds dcl_expr_2 icl_expr_2
	e_corresponds (RecordUpdate dcl_type dcl_expr dcl_selections) (RecordUpdate icl_type icl_expr icl_selections)
		=	e_corresponds dcl_type icl_type
		o`	e_corresponds dcl_expr icl_expr
		o`	e_corresponds dcl_selections icl_selections
	e_corresponds (TupleSelect dcl_ds dcl_field_nr dcl_expr) (TupleSelect icl_ds icl_field_nr icl_expr)
		=	e_corresponds dcl_ds icl_ds
		o`	equal2 dcl_field_nr icl_field_nr
		o`	e_corresponds dcl_expr icl_expr
	e_corresponds (BasicExpr dcl_value dcl_type) (BasicExpr icl_value icl_type)
		=	equal2 dcl_value icl_value
		o`	equal2 dcl_type icl_type
	e_corresponds (AnyCodeExpr dcl_ins dcl_outs dcl_code_sequence) (AnyCodeExpr icl_ins icl_outs icl_code_sequence)
		=	e_corresponds dcl_ins icl_ins
		o`	e_corresponds dcl_outs icl_outs
		o`	equal2 dcl_code_sequence icl_code_sequence
	e_corresponds (ABCCodeExpr dcl_lines dcl_do_inline) (ABCCodeExpr icl_lines icl_do_inline)
		=	equal2 dcl_lines icl_lines
		o`	equal2 dcl_do_inline icl_do_inline
	e_corresponds (MatchExpr dcl_opt_tuple_type dcl_cons_symbol dcl_src_expr)
				 (MatchExpr icl_opt_tuple_type icl_cons_symbol icl_src_expr)
		= 	e_corresponds dcl_opt_tuple_type icl_opt_tuple_type
		o`	e_corresponds dcl_cons_symbol icl_cons_symbol
		o`	e_corresponds dcl_src_expr icl_src_expr
	e_corresponds (FreeVar dcl) (FreeVar icl)
		= e_corresponds dcl icl
	e_corresponds (DynamicExpr dcl) (DynamicExpr icl)
		= e_corresponds dcl icl
	e_corresponds (TypeCodeExpression dcl) (TypeCodeExpression icl)
		= e_corresponds dcl icl
	e_corresponds EE EE
		= do_nothing
	e_corresponds _ _
		= give_error ""


instance e_corresponds Let where
	e_corresponds dclLet iclLet
		=	e_corresponds dclLet.let_strict_binds iclLet.let_strict_binds
		o`	e_corresponds dclLet.let_lazy_binds iclLet.let_lazy_binds
		o`	e_corresponds dclLet.let_expr iclLet.let_expr

instance e_corresponds (Bind a b) | e_corresponds a & e_corresponds b where
	e_corresponds dcl icl
		=	e_corresponds dcl.bind_src icl.bind_src
		o`	e_corresponds dcl.bind_dst icl.bind_dst

instance e_corresponds Case where
	e_corresponds dclCase iclCase
		=	e_corresponds dclCase.case_expr iclCase.case_expr
		o`	e_corresponds dclCase.case_guards iclCase.case_guards
		o`	e_corresponds dclCase.case_default iclCase.case_default

instance e_corresponds CasePatterns where
	e_corresponds (AlgebraicPatterns dcl_alg_type dcl_patterns) (AlgebraicPatterns icl_alg_type icl_patterns)
		=	e_corresponds dcl_patterns icl_patterns
	e_corresponds (BasicPatterns dcl_basic_type dcl_patterns) (BasicPatterns icl_basic_type icl_patterns)
		=	equal2 dcl_basic_type icl_basic_type
		o`	e_corresponds dcl_patterns icl_patterns
	e_corresponds (DynamicPatterns dcl_patterns) (DynamicPatterns icl_patterns)
		=	e_corresponds dcl_patterns icl_patterns
	e_corresponds NoPattern NoPattern
		=	do_nothing
	e_corresponds _ _
		=	give_error ""

instance e_corresponds AlgebraicPattern where
	e_corresponds dcl icl
		=	e_corresponds dcl.ap_symbol icl.ap_symbol
		o`	e_corresponds dcl.ap_vars icl.ap_vars
		o`	e_corresponds dcl.ap_expr icl.ap_expr

instance e_corresponds BasicPattern where
	e_corresponds dcl icl
		=	equal2 dcl.bp_value icl.bp_value
		o`	e_corresponds dcl.bp_expr icl.bp_expr

instance e_corresponds DynamicPattern where
	e_corresponds dcl icl
		=	e_corresponds dcl.dp_var icl.dp_var
		o`	e_corresponds dcl.dp_rhs icl.dp_rhs
		o`	e_corresponds_dp_type dcl.dp_type icl.dp_type
	  where
		e_corresponds_dp_type dcl_expr_ptr icl_expr_ptr ec_state=:{ec_expr_heap, ec_tc_state}
			#! dcl_type
					= sreadPtr dcl_expr_ptr ec_expr_heap
			   icl_type 
			   		= sreadPtr icl_expr_ptr ec_expr_heap
			# (EI_DynamicTypeWithVars _ dcl_dyn_type _)
					= dcl_type
			  (EI_DynamicTypeWithVars _ icl_dyn_type _)
			  		= icl_type
			  (corresponds, ec_tc_state) 
					= t_corresponds dcl_dyn_type icl_dyn_type ec_tc_state
			  ec_state
				  	= { ec_state & ec_tc_state = ec_tc_state }
			| corresponds
				= ec_state
			= give_error "" ec_state

instance e_corresponds Selection where
	e_corresponds (RecordSelection dcl_selector dcl_field_nr) (RecordSelection icl_selector icl_field_nr)
		=	e_corresponds dcl_selector icl_selector
		o`	equal2 dcl_field_nr icl_field_nr
	e_corresponds (ArraySelection dcl_selector _ dcl_index_expr) (ArraySelection icl_selector _ icl_index_expr)
		=	e_corresponds dcl_selector icl_selector
		o`	e_corresponds dcl_index_expr icl_index_expr
	e_corresponds (DictionarySelection dcl_dict_var dcl_selections _ dcl_index_expr)
				(DictionarySelection icl_dict_var icl_selections _ icl_index_expr)
		=	e_corresponds dcl_dict_var icl_dict_var
		o`	e_corresponds dcl_selections icl_selections
		o`	e_corresponds dcl_index_expr icl_index_expr
		
instance e_corresponds DynamicExpr where
	e_corresponds dcl icl
		=	e_corresponds_dyn_opt_type dcl.dyn_opt_type icl.dyn_opt_type
		o`	e_corresponds dcl.dyn_expr icl.dyn_expr
	  where		
		e_corresponds_dyn_opt_type dcl icl ec_state
			# (corresponds, ec_tc_state) = t_corresponds dcl icl ec_state.ec_tc_state
			  ec_state = { ec_state & ec_tc_state = ec_tc_state }
			| corresponds
				= ec_state
			= give_error "" ec_state

instance e_corresponds TypeCodeExpression where
	e_corresponds TCE_Empty TCE_Empty
		= do_nothing
	e_corresponds _ _
		= abort "comparedefimp:e_corresponds (TypeCodeExpression): currently only TCE_Empty can appear"
	
instance e_corresponds {#Char} where
	e_corresponds s1 s2
		= equal2 s1 s2

instance e_corresponds BoundVar where
	e_corresponds dcl icl
		= e_corresponds_VarInfoPtr icl.var_name dcl.var_info_ptr icl.var_info_ptr

instance e_corresponds FieldSymbol where
	e_corresponds dclField iclField
		= equal2 dclField.fs_name iclField.fs_name

e_corresponds_VarInfoPtr ident dclPtr iclPtr ec_state=:{ec_var_heap}
	# (unifiable, ec_var_heap) = tryToUnifyVars dclPtr iclPtr ec_var_heap
	  ec_state = { ec_state & ec_var_heap = ec_var_heap }
	| not unifiable
		= { ec_state & ec_error_admin = checkError ident error_message ec_state.ec_error_admin }
	= ec_state

/*	e_corresponds_app_symb checks correspondence of the function symbols in an App expression.
	The problem: also different symbols can correspond with each other, because for macros
	all local functions (also lambda functions) will be generated twice.
*/
e_corresponds_app_symb dcl_app_symb=:{symb_kind=SK_Function dcl_glob_index} 
					icl_app_symb=:{symb_kind=SK_Function icl_glob_index}
					ec_state
	= continuation_for_possibly_twice_defined_funs dcl_app_symb dcl_glob_index icl_app_symb icl_glob_index
													ec_state
e_corresponds_app_symb dcl_app_symb=:{symb_kind=SK_OverloadedFunction dcl_glob_index}
					icl_app_symb=:{symb_kind=SK_OverloadedFunction icl_glob_index}
					ec_state
	= continuation_for_possibly_twice_defined_funs dcl_app_symb dcl_glob_index icl_app_symb icl_glob_index
													ec_state
e_corresponds_app_symb {symb_name=dcl_symb_name, symb_kind=SK_Constructor dcl_glob_index}
						{symb_name=icl_symb_name, symb_kind=SK_Constructor icl_glob_index}
						ec_state
	| dcl_glob_index.glob_module==icl_glob_index.glob_module && dcl_symb_name.id_name==icl_symb_name.id_name
		= ec_state
	= give_error icl_symb_name ec_state
e_corresponds_app_symb {symb_name} _ ec_state
	= give_error symb_name ec_state

continuation_for_possibly_twice_defined_funs dcl_app_symb dcl_glob_index icl_app_symb icl_glob_index
											ec_state
	| dcl_glob_index==icl_glob_index
		= ec_state
	| dcl_glob_index.glob_module<>cIclModIndex || icl_glob_index.glob_module<>cIclModIndex
		= give_error icl_app_symb.symb_name ec_state
	// two different functions from the main module were referenced. Check their correspondence
	# dcl_index = dcl_glob_index.glob_object
	  icl_index = icl_glob_index.glob_object
	#! dcl_is_macro_fun = get_is_macro_fun dcl_index ec_state.ec_icl_functions
	   icl_is_macro_fun = get_is_macro_fun icl_index ec_state.ec_icl_functions
	| not dcl_is_macro_fun || not icl_is_macro_fun
		// at least one function was not locally defined in a macro.
		= give_error icl_app_symb.symb_name ec_state
	// two functions that are local to a macro definition were referencend.
	| not (names_are_compatible dcl_index icl_index ec_state.ec_icl_functions)
		= give_error icl_app_symb.symb_name ec_state
	| both_funs_have_not_been_checked_before dcl_index icl_index ec_state.ec_correspondences
		// going into recursion is save
		= compareTwoMacroFuns dcl_index icl_index ec_state
	| both_funs_correspond dcl_index icl_index ec_state.ec_correspondences
		= ec_state
	= give_error icl_app_symb.symb_name ec_state
  where
	names_are_compatible dcl_index icl_index icl_functions
		# dcl_function = icl_functions.[dcl_index]
		  icl_function = icl_functions.[icl_index]
		  dcl_is_lambda = get_is_lambda dcl_function.fun_kind
		  icl_is_lambda = get_is_lambda icl_function.fun_kind
		=	(dcl_is_lambda==icl_is_lambda)
		 && (implies (not dcl_is_lambda) (dcl_function.fun_symb.id_name==icl_function.fun_symb.id_name))
		// functions that originate from lambda expressions can correspond although their names differ
	  where
		get_is_lambda (FK_Function is_lambda)
			= is_lambda
		get_is_lambda _
		 	= False
		 	
	both_funs_have_not_been_checked_before dcl_index icl_index correspondences
		= correspondences.[dcl_index]==cNoCorrespondence && correspondences.[icl_index]==cNoCorrespondence

	both_funs_correspond dcl_index icl_index correspondences
		= correspondences.[dcl_index]==icl_index && correspondences.[icl_index]==dcl_index
	
	get_is_macro_fun fun_nr icl_functions
		= icl_functions.[fun_nr].fun_info.fi_is_macro_fun

init_attr_vars attr_vars tc_state=:{tc_attr_vars}
	# hwn_heap = foldSt init_attr_var attr_vars tc_attr_vars.hwn_heap
	  tc_attr_vars = { tc_attr_vars & hwn_heap = hwn_heap }
	= { tc_state & tc_attr_vars = tc_attr_vars }
  where
	init_attr_var {av_info_ptr} attr_heap
		= writePtr av_info_ptr AVI_Empty attr_heap

error_message		:== "definition in the impl module conflicts with the def module"
cNoCorrespondence	:== -1
implies a b 		:== not a || b
	
(==>) infix 0 // :: w:(St .s .a) v:(.a -> .(St .s .b)) -> u:(St .s .b), [u <= v, u <= w]
(==>) f g :== \st0 -> let (r,st1) = f st0 in g r st1

(o`) infixr 0
(o`) f g :== \state -> g (f state)

do f = \state -> (True, f state)

// XXX should be a macro (but this crashes the 1.3.2 compiler)
(&&&) infixr
(&&&) m1 m2
	=	m1 ==> \b
		->	if b
				m2
				(return False)

equal a b
	=	return (a == b)

equal2 a b
	| a<>b
		= give_error ""
	= do_nothing

do_nothing ec_state
	= ec_state

give_error s ec_state
	= { ec_state & ec_error_admin = checkError s error_message ec_state.ec_error_admin }

