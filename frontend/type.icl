implementation module type

import StdEnv
import syntax, typesupport, check, analtypes, overloading, unitype, refmark, predef, utilities, compare_constructor // , RWSDebug
import compilerSwitches
import generics // AA

::	TypeInput =
	{	ti_common_defs	:: !{# CommonDefs }
	,	ti_functions	:: !{# {# FunType }}
	,	ti_main_dcl_module_n :: !Int
	}

::	TypeState =
	{	ts_fun_env			:: !.{! FunctionType}
	,	ts_var_store		:: !TempVarId
	,	ts_attr_store		:: !TempAttrId
	,	ts_var_heap			:: !.VarHeap 
	,	ts_type_heaps		:: !.TypeHeaps
	,	ts_expr_heap		:: !.ExpressionHeap 
	,	ts_td_infos			:: !.TypeDefInfos
	,	ts_cons_variables	:: ![TempVarId]
	,	ts_exis_variables	:: ![(CoercionPosition, [TempAttrId])]
	,	ts_error			:: !.ErrorAdmin
	,	ts_out				:: !.File
	}

::	TypeCoercion =
	{	tc_demanded		:: !AType
	,	tc_offered		:: !AType
	,	tc_position		:: !CoercionPosition
	,	tc_coercible	:: !Bool
	}

::	SharedAttribute = 
	{	sa_attr_nr	:: !Int
	,	sa_position	:: !Expression
	}

::	Requirements =
	{	req_overloaded_calls	:: ![ExprInfoPtr]
	,	req_type_coercions		:: ![TypeCoercion]
	,	req_type_coercion_groups:: ![TypeCoercionGroup]
	,	req_attr_coercions		:: ![AttrCoercion]
	,	req_case_and_let_exprs	:: ![ExprInfoPtr]
	}

::	TypeCoercionGroup =
	{	tcg_type_coercions	:: ![TypeCoercion]
	,	tcg_position		:: !Position
	}

instance toString BoundVar
where
	toString varid = varid.var_name.id_name

class arraySubst type :: !type !u:{!Type} -> (!Bool,!type, !u:{! Type})

instance arraySubst AType
where
	arraySubst atype=:{at_type} subst
		# (changed, at_type, subst) = arraySubst at_type subst
		| changed
			= (True, { atype & at_type = at_type }, subst)
			= (False, atype, subst)
		
instance arraySubst Type
where
	arraySubst tv=:(TempV tv_number) subst
		# (type, subst) = subst![tv_number]
		= case type of
			TE	-> (False,tv, subst)
			_
				# (_, type, subst) = arraySubst type subst
				-> (True, type, subst)
	arraySubst type=:(arg_type --> res_type) subst
		# (changed, (arg_type, res_type), subst) = arraySubst (arg_type, res_type) subst
		| changed
			= (changed, arg_type --> res_type, subst)
			= (False, type, subst)
	arraySubst type=:(TA cons_id cons_args) subst
		# (changed, cons_args, subst) = arraySubst cons_args subst
		| changed
			= (True, TA cons_id cons_args, subst) 
			= (False,type, subst) 
	arraySubst tcv=:(TempCV tv_number :@: types) subst
		# (type, subst) = subst![tv_number]
		= case type of
			TE
				# (changed,types, subst) = arraySubst types subst
				| changed
					-> (True, TempCV tv_number :@: types, subst)
					-> (False, tcv, subst)
			_
				# (_, (type, types), subst) = arraySubst (type, types) subst
				  (ok, simplified_type) = simplifyTypeApplication type types
				| ok
					-> (True, simplified_type, subst)
					-> (False, tcv, subst)
//AA..					
	arraySubst type=:(TArrow1 arg_type) subst
		# (changed, arg_type, subst) = arraySubst arg_type subst
		| changed
			= (changed, TArrow1 arg_type, subst)
			= (False, type, subst)
//..AA					

	arraySubst tfa_type=:(TFA vars type) subst
		# (changed, type, subst) = arraySubst type subst
		| changed
			= (changed, TFA vars type, subst)
			= (False, tfa_type, subst)

	arraySubst type subst
		= (False, type, subst)

instance arraySubst (a,b) | arraySubst a & arraySubst b
where
	arraySubst (x,y) subst
		# (changed_x, x, subst) =  arraySubst x subst
		  (changed_y, y, subst) =  arraySubst y subst
		= (changed_x || changed_y, (x,y), subst)
		
instance arraySubst [a] | arraySubst a
where
	arraySubst [] subst
		= (False, [], subst)
	arraySubst t=:[type : types ] subst
		# (changed, (type, types), subst) = arraySubst (type, types) subst
		| changed
			= (True, [type : types ], subst)
			= (False, t, subst)
	
instance arraySubst TempSymbolType
where
	arraySubst tst=:{tst_args,tst_result,tst_context} subst
		# (changed, (tst_args, (tst_result, tst_context)), subst) = arraySubst (tst_args, (tst_result, tst_context)) subst
		| changed
			= (True, {tst & tst_args = tst_args, tst_result = tst_result, tst_context = tst_context}, subst)
			= (False, tst, subst)

instance arraySubst TypeContext
where
	arraySubst tc=:{tc_types} subst
		# (changed, tc_types, subst) = arraySubst tc_types subst
		| changed
			= (True,{ tc & tc_types = tc_types}, subst)
			= (False, tc, subst)

instance arraySubst CaseType
where
	arraySubst ct=:{ct_pattern_type, ct_result_type, ct_cons_types} subst
		# (changed, (ct_pattern_type, (ct_result_type, ct_cons_types)), subst) = arraySubst (ct_pattern_type, (ct_result_type, ct_cons_types)) subst
		| changed
			= (True,{ ct & ct_pattern_type = ct_pattern_type, ct_result_type = ct_result_type, ct_cons_types = ct_cons_types }, subst)
			= (False, ct, subst)

class containsTypeVariable a :: !Int !a !{!Type} -> Bool

instance containsTypeVariable [a] | containsTypeVariable a
where
	containsTypeVariable var_id [elem:list] subst
		= containsTypeVariable var_id elem subst || containsTypeVariable var_id list subst
	containsTypeVariable var_id [] _
		= False

instance containsTypeVariable AType
where
	containsTypeVariable var_id {at_type} subst = containsTypeVariable var_id at_type subst

instance containsTypeVariable Type
where
	containsTypeVariable var_id (TempV tv_number) subst
		# type = subst.[tv_number]
		| isIndirection type
			= containsTypeVariable var_id type subst 
			= tv_number == var_id
	containsTypeVariable var_id (arg_type --> res_type) subst
		= containsTypeVariable var_id arg_type subst || containsTypeVariable var_id res_type subst
//AA..
	containsTypeVariable var_id (TArrow1 arg_type) subst
		= containsTypeVariable var_id arg_type subst
//..AA
	containsTypeVariable var_id (TA cons_id cons_args) subst
		= containsTypeVariable var_id cons_args subst
	containsTypeVariable var_id (type :@: types) subst
		= containsTypeVariable var_id type subst || containsTypeVariable var_id types subst
	containsTypeVariable _ _ _
		= False

instance containsTypeVariable ConsVariable
where
	containsTypeVariable var_id (TempCV tv_number) subst
		# type = subst.[tv_number]
		| isIndirection type
			= containsTypeVariable var_id type subst 
			= tv_number == var_id
	containsTypeVariable var_id _ _
		= False

type_error =: "Type error"
type_error_format =: { form_properties = cNoProperties, form_attr_position = No }

cannotUnify t1 t2 position=:(CP_Expression expr) err=:{ea_loc=[ip:_]} 
	= case tryToOptimizePosition expr of
		Yes (id_name, line)
			# err = pushErrorAdmin { ip & ip_ident.id_name = id_name, ip_line = line } err
			  err = errorHeading type_error err
			  err = popErrorAdmin err
//			-> { err & ea_file = err.ea_file <<< " cannot unify " <:: (type_error_format, t1, Yes initialTypeVarBeautifulizer) 
//											<<< " with " <:: (type_error_format, t2, Yes initialTypeVarBeautifulizer) <<< '\n' }
			-> { err & ea_file = err.ea_file <<< " cannot unify " <:: (type_error_format, t1, No) 
											<<< " with " <:: (type_error_format, t2, No) <<< '\n' }
		_
			-> cannot_unify t1 t2 position err 
cannotUnify t1 t2 position err 
	= cannot_unify t1 t2 position err 

cannot_unify t1 t2 position err
	# (err=:{ea_file}) = errorHeading type_error err
	  ea_file = case position of
				CP_FunArg _ _
					-> ea_file <<< "\"" <<< position <<< "\""
				_
					-> ea_file
	  ea_file = ea_file <<< " cannot unify " <:: (type_error_format, t1, No) 
						<<< " with " <:: (type_error_format, t2, No)
//	  ea_file = ea_file <<< " cannot unify " <:: (type_error_format, t1, Yes initialTypeVarBeautifulizer) 
//						<<< " with " <:: (type_error_format, t2, Yes initialTypeVarBeautifulizer)
	  ea_file = case position of
	  			CP_FunArg _ _
	  				-> ea_file
  				_
	  				-> ea_file <<< " near " <<< position
	= { err & ea_file = ea_file <<< '\n' }


existentialError position=:(CP_Expression expr) err=:{ea_loc=[ip:_]} 
	= case tryToOptimizePosition expr of
		Yes (id_name, line)
			# err = pushErrorAdmin { ip & ip_ident.id_name = id_name, ip_line = line } err
			  err = errorHeading type_error err
			  err = popErrorAdmin err
			-> { err & ea_file = err.ea_file <<< " attribute variable could not be universally quantified"<<< '\n' }
		_
			# err = errorHeading type_error err
			-> { err & ea_file = err.ea_file <<< " attribute variable could not be universally quantified"<<< '\n' }
			

tryToOptimizePosition (Case {case_ident=Yes {id_name}})
	= optBeautifulizeIdent id_name
tryToOptimizePosition (App {app_symb={symb_name}})
	= optBeautifulizeIdent symb_name.id_name
tryToOptimizePosition (fun @ _)
	= tryToOptimizePosition fun
tryToOptimizePosition _
	= No

isIndirection TE	= False
isIndirection type	= True

class unify a :: !a !a !TypeInput !*{! Type} !*TypeHeaps -> (!Bool, !*{! Type}, !*TypeHeaps)

instance unify (a, b) | unify a & unify b
where
	unify (t1x, t1y) (t2x, t2y) modules subst heaps
		# (succ, subst, heaps) =  unify t1y t2y modules subst heaps
		| succ
	      = unify t1x t2x modules subst heaps
	      = (False, subst, heaps)

instance unify [a] | unify a
where
	unify [t1 : ts1] [t2 : ts2] modules subst heaps
		= unify (t1,ts1) (t2,ts2) modules subst heaps
	unify [] [] modules subst heaps
		= (True, subst, heaps)
	unify _ _ modules subst heaps
		= (False, subst, heaps)

instance unify AType
where
	unify t1 t2 modules subst heaps = unifyTypes t1.at_type t1.at_attribute t2.at_type t2.at_attribute modules subst heaps

unifyTypes :: !Type !TypeAttribute !Type !TypeAttribute !TypeInput !*{! Type} !*TypeHeaps -> (!Bool, !*{! Type}, !*TypeHeaps)
unifyTypes tv=:(TempV tv_number) attr1 type2 attr2 modules subst heaps
	# (type1, subst) = subst![tv_number]
	| isIndirection type1
		= unifyTypes type1 attr1 type2 attr2 modules subst heaps
		# (succ, subst) = unify_variable_with_type tv_number type2 subst
		= (succ, subst, heaps)
	where	
		unify_variable_with_type tv_number1 tv=:(TempV tv_number2) subst
			# (type2, subst) = subst![tv_number2]
			| isIndirection type2
				= unify_variable_with_type tv_number type2 subst
			| tv_number1 == tv_number2
				= (True, subst)
				= (True, { subst & [tv_number1] = tv})
		unify_variable_with_type tv_number type subst
			| containsTypeVariable tv_number type subst
				= (False, subst)
//					---> "unify_variable_with_type"
				= (True, { subst & [tv_number] = type})
unifyTypes type attr1 tv=:(TempV _) attr2 modules subst heaps
	= unifyTypes tv attr2 type attr1 modules subst heaps
unifyTypes t1=:(TB tb1) attr1 t2=:(TB tb2) attr2 modules subst heaps
	| tb1 == tb2
		= (True, subst, heaps)
		= (False, subst, heaps)
unifyTypes (arg_type1 --> res_type1) attr1 (arg_type2 --> res_type2) attr2 modules subst heaps
	= unify (arg_type1,res_type1) (arg_type2,res_type2) modules subst heaps
//AA..	
unifyTypes TArrow attr1 TArrow attr2 modules subst heaps
	= (True, subst, heaps)	
unifyTypes (TArrow1 t1) attr1 (TArrow1 t2) attr2 modules subst heaps
	= unify t1 t2 modules subst heaps	
//..AA
unifyTypes t1=:(TA cons_id1 cons_args1) attr1 t2=:(TA cons_id2 cons_args2) attr2 modules subst heaps
	| cons_id1 == cons_id2
		= unify cons_args1 cons_args2 modules subst heaps
		# (succ1, t1, heaps) = tryToExpand t1 attr1 modules.ti_common_defs heaps
		  (succ2, t2, heaps) = tryToExpand t2 attr2 modules.ti_common_defs heaps
		| succ1 || succ2
			= unifyTypes t1 attr1 t2 attr2 modules subst heaps
			= (False, subst, heaps)
//				---> "unifyTypes1"
unifyTypes (cons_var :@: types) attr1 type2 attr2 modules subst heaps
	# (_, type2, heaps) = tryToExpand type2 attr2 modules.ti_common_defs heaps
	= unifyTypeApplications cons_var attr1 types type2 attr2 modules subst heaps
unifyTypes type1 attr1 (cons_var :@: types) attr2 modules subst heaps
	# (_, type1, heaps) = tryToExpand type1 attr1 modules.ti_common_defs heaps
	= unifyTypeApplications cons_var attr2 types type1 attr1 modules subst heaps
unifyTypes t1=:(TempQV qv_number1) attr1 t2=:(TempQV qv_number2) attr2 modules subst heaps
	= (qv_number1 == qv_number2, subst, heaps)
unifyTypes (TempQV qv_number) attr1 type attr2 modules subst heaps
	= (False, subst, heaps)
unifyTypes type attr1 (TempQV qv_number1) attr2 modules subst heaps
	= (False, subst, heaps)
unifyTypes type1 attr1 type2 attr2 modules subst heaps
	# (succ1, type1, heaps) = tryToExpand type1 attr1 modules.ti_common_defs heaps
	  (succ2, type2, heaps) = tryToExpand type2 attr2 modules.ti_common_defs heaps
	| succ1 || succ2
		= unifyTypes type1 attr1 type2 attr2 modules subst heaps
		= (False, subst, heaps)

tryToExpand :: !Type !TypeAttribute !{# CommonDefs} !*TypeHeaps -> (!Bool, !Type, !*TypeHeaps)
tryToExpand type=:(TA {type_index={glob_object,glob_module}} type_args) type_attr ti_common_defs type_heaps
	#! type_def = ti_common_defs.[glob_module].com_type_defs.[glob_object]
	= case type_def.td_rhs of
		SynType {at_type}
			# (_, expanded_type, type_heaps) = substituteType type_def.td_attribute type_attr type_def.td_args type_args at_type type_heaps
			-> (True, expanded_type, type_heaps)
		_
			-> (False, type, type_heaps)
tryToExpand type type_attr modules type_heaps
	= (False, type, type_heaps)

toTV is_exist temp_var_id
	| is_exist
		= TempQV temp_var_id
		= TempV temp_var_id

toCV is_exist temp_var_id
	| is_exist
		= TempQCV temp_var_id
		= TempCV temp_var_id

simplifyTypeApplication :: !Type ![AType] -> (!Bool, !Type)
simplifyTypeApplication (TA type_cons=:{type_arity} cons_args) type_args
	= (True, TA { type_cons & type_arity = type_arity + length type_args } (cons_args ++ type_args))
simplifyTypeApplication (cons_var :@: types) type_args
	= (True, cons_var :@: (types ++ type_args))
simplifyTypeApplication (TempV tv_number) type_args
	= (True, TempCV tv_number :@: type_args)
simplifyTypeApplication (TempQV tv_number) type_args
	= (True, TempQCV tv_number :@: type_args)
//AA..
simplifyTypeApplication TArrow [type1, type2] 
	= (True, type1 --> type2)
simplifyTypeApplication TArrow [type] 
	= (True, TArrow1 type)
simplifyTypeApplication (TArrow1 type1) [type2] 
	= (True, type1 --> type2)
//..AA
simplifyTypeApplication type type_args
	= (False, type)

unifyTypeApplications (TempCV tv_number) attr1 type_args type2 attr2 modules subst heaps
	# (type1, subst) = subst![tv_number]
	| isIndirection type1
		# (ok, simplified_type) = simplifyTypeApplication type1 type_args
		| ok
			= unifyTypes simplified_type attr1 type2 attr2 modules subst heaps
			= (False, subst, heaps)
		= unifyCVwithType False tv_number type_args type2 modules subst heaps
unifyTypeApplications (TempQCV tv_number) attr1 type_args type2 attr2 modules subst heaps
	= unifyCVwithType True tv_number type_args type2 modules subst heaps
		
unifyCVwithType is_exist tv_number1 type_args1 type=:(cv :@: type_args2) modules subst heaps
	= case cv of
		TempCV tv_number2
			# (type2, subst) = subst![tv_number2]
			| isIndirection type2
				# (ok, simplified_type) = simplifyTypeApplication type2 type_args2
				| ok
					-> unifyCVwithType is_exist tv_number1 type_args1 simplified_type modules subst heaps
					-> (False, subst, heaps)
				-> unifyCVApplicationwithCVApplication is_exist tv_number1 type_args1 False tv_number2 type_args2 modules subst heaps
		TempQCV tv_number2
				-> unifyCVApplicationwithCVApplication is_exist tv_number1 type_args1 True tv_number2 type_args2 modules subst heaps

unifyCVwithType is_exist tv_number type_args type=:(TA type_cons cons_args) modules subst heaps
	# diff = type_cons.type_arity - length type_args
	| diff >= 0 
		# (succ, subst, heaps) = unify type_args (drop diff cons_args) modules subst heaps
		| succ
			= unifyTypes (toTV is_exist tv_number) TA_Multi (TA { type_cons & type_arity = diff } (take diff cons_args)) TA_Multi modules subst heaps
		    = (False, subst, heaps)
		= (False, subst, heaps)

// AA..
unifyCVwithType is_exist tv_number [type_arg1, type_arg2] type=:(atype1 --> atype2) modules subst heaps
	# (succ, subst, heaps) = unify (type_arg1, type_arg2) (atype1, atype2) modules subst heaps
	| succ
		= unifyTypes (toTV is_exist tv_number) TA_Multi TArrow TA_Multi modules subst heaps
		= (False, subst, heaps)		
unifyCVwithType is_exist tv_number [type_arg] type=:(atype1 --> atype2) modules subst heaps
	# (succ, subst, heaps) = unify type_arg atype2 modules subst heaps
	| succ
		= unifyTypes (toTV is_exist tv_number) TA_Multi (TArrow1 atype1) TA_Multi modules subst heaps
		= (False, subst, heaps)
unifyCVwithType is_exist tv_number [] type=:(atype1 --> atype2) modules subst heaps
	= unifyTypes (toTV is_exist tv_number) TA_Multi type TA_Multi modules subst heaps
		
unifyCVwithType is_exist tv_number [type_arg] type=:(TArrow1 atype) modules subst heaps
	# (succ, subst, heaps) = unify type_arg atype modules subst heaps
	| succ
		= unifyTypes (toTV is_exist tv_number) TA_Multi TArrow TA_Multi modules subst heaps
		= (False, subst, heaps)
unifyCVwithType is_exist tv_number [] type=:(TArrow1 atype) modules subst heaps
	= unifyTypes (toTV is_exist tv_number) TA_Multi type TA_Multi modules subst heaps

unifyCVwithType is_exist tv_number [] TArrow modules subst heaps
	= unifyTypes (toTV is_exist tv_number) TA_Multi TArrow TA_Multi modules subst heaps
// ..AA 		

unifyCVwithType is_exist tv_number type_args type modules subst heaps
	= (False, subst, heaps)

unifyCVApplicationwithCVApplication is_exist1 tv_number1 type_args1 is_exist2 tv_number2 type_args2 modules subst heaps
	# arity1 = length type_args1
	  arity2 = length type_args2
	  diff = arity1 - arity2
	| diff == 0
		# (succ, subst) = unify_cv_with_cv is_exist1 tv_number1 is_exist2 tv_number2 subst
		| succ
		    = unify type_args1 type_args2 modules subst heaps
			= (False, subst, heaps)
	| diff < 0
		# diff = 0 - diff
		  (succ, subst, heaps) = unifyTypes (toTV is_exist1 tv_number1) TA_Multi (toCV is_exist2 tv_number2 :@: take diff type_args2) TA_Multi modules subst heaps
		| succ
		    = unify type_args1 (drop diff type_args2) modules subst heaps
			= (False, subst, heaps)
//	| otherwise
		# (succ, subst, heaps) = unifyTypes (toCV is_exist1 tv_number1 :@: take diff type_args1) TA_Multi (toTV is_exist2 tv_number2) TA_Multi modules subst heaps
		| succ
		    = unify (drop diff type_args1) type_args2 modules subst heaps
			= (False, subst, heaps)
	where
		unify_cv_with_cv is_exist1 tv_number1 is_exist2 tv_number2 subst
			| tv_number1 == tv_number2
				= (True, subst)
			| is_exist1
				| is_exist2
					= (False, subst)
					= (True, { subst & [tv_number2] = TempQV tv_number1})
				| is_exist2
					= (True, { subst & [tv_number1] = TempQV tv_number2})
					= (True, { subst & [tv_number1] = TempV tv_number2})
		
	
instance fromInt TypeAttribute
where
	fromInt AttrUni		= TA_Unique
	fromInt AttrMulti	= TA_Multi
	fromInt av_number	= TA_TempVar av_number

class freshCopy a :: !a !*TypeHeaps -> (!a, !*TypeHeaps)

instance freshCopy [a] | freshCopy a
where
	freshCopy l ls = mapSt freshCopy l ls

freshCopyOfAttributeVar {av_name,av_info_ptr} attr_var_heap
	# (av_info, attr_var_heap) = readPtr av_info_ptr attr_var_heap
	= case av_info of
		AVI_Attr attr
			-> (attr, attr_var_heap)
		_
			-> abort ("freshCopyOfAttributeVar (type,icl)" ---> av_name)


freshCopyOfTypeAttribute (TA_Var avar) attr_var_heap
	= freshCopyOfAttributeVar avar attr_var_heap

/* A temporary hack to handle the new Object IO lib */
/* Should be removed !!!!!!!!!! */

freshCopyOfTypeAttribute (TA_RootVar avar) attr_var_heap
	= PA_BUG (TA_PA_BUG, attr_var_heap) (freshCopyOfAttributeVar avar attr_var_heap)
freshCopyOfTypeAttribute TA_None attr_var_heap
	= (TA_Multi, attr_var_heap)
freshCopyOfTypeAttribute TA_Unique attr_var_heap
	= (TA_Unique, attr_var_heap)
freshCopyOfTypeAttribute attr attr_var_heap
	= (attr, attr_var_heap)


cIsExistential 		:== True
cIsNotExistential	:== False

freshCopyOfTypeVariable {tv_name,tv_info_ptr} type_heaps=:{th_vars}
	# (TVI_Type fresh_var, th_vars)	= readPtr tv_info_ptr th_vars
	= (fresh_var, { type_heaps & th_vars = th_vars })

freshConsVariable {tv_info_ptr} type_var_heap
	# (tv_info, type_var_heap) = readPtr tv_info_ptr type_var_heap
	= (to_constructor_variable tv_info, type_var_heap)
	where
		to_constructor_variable (TVI_Type (TempV temp_var_id))
			= TempCV temp_var_id
		to_constructor_variable (TVI_Type (TempQV temp_var_id))
			= TempQCV temp_var_id

instance freshCopy AType
where 	
	freshCopy type=:{at_type = cv :@: types, at_attribute} type_heaps=:{th_attrs}
		# (fresh_attribute, th_attrs)	= freshCopyOfTypeAttribute at_attribute th_attrs
		# (fresh_types, type_heaps)		= freshCopy types { type_heaps & th_attrs = th_attrs }
		= case cv of
			CV tv
				# (fresh_cons_var, th_vars)	= freshConsVariable tv type_heaps.th_vars
				-> ({type & at_type = fresh_cons_var :@: fresh_types, at_attribute = fresh_attribute }, { type_heaps & th_vars = th_vars })
			_
				-> ({type & at_type = cv :@: fresh_types, at_attribute = fresh_attribute}, type_heaps)
	freshCopy type=:{at_type, at_attribute} type_heaps=:{th_attrs}
		# (fresh_attribute, th_attrs)	= freshCopyOfTypeAttribute at_attribute th_attrs
		  (fresh_type, type_heaps)		= freshCopy at_type { type_heaps & th_attrs = th_attrs }
		= ({ type & at_type = fresh_type, at_attribute = fresh_attribute }, type_heaps)

instance freshCopy Type
where
	freshCopy (TV tv) type_heaps
		= freshCopyOfTypeVariable tv type_heaps
	freshCopy (TA cons_id=:{type_index={glob_object,glob_module}} cons_args)  type_heaps
		# (cons_args, type_heaps) = freshCopy cons_args type_heaps
		= (TA cons_id cons_args, type_heaps)
	freshCopy (arg_type --> res_type) type_heaps
		# (arg_type, type_heaps) = freshCopy arg_type type_heaps
		  (res_type, type_heaps) = freshCopy res_type type_heaps
		= (arg_type --> res_type, type_heaps)
//AA..
	freshCopy (TArrow1 arg_type) type_heaps
		# (arg_type, type_heaps) = freshCopy arg_type type_heaps
		= (TArrow1 arg_type, type_heaps)
//..AA		
	freshCopy (TFA vars type) type_heaps
		# type_heaps = foldSt bind_var_and_attr vars type_heaps
		  (type, type_heaps) = freshCopy type type_heaps
		# type_heaps = clearBindings vars type_heaps
		= (TFA vars type, type_heaps)
	where
		bind_var_and_attr {atv_attribute, atv_variable = tv=:{tv_info_ptr}} type_heaps=:{th_vars,th_attrs}
			= { type_heaps & th_vars = th_vars <:= (tv_info_ptr, TVI_Type (TV tv)), th_attrs = bind_attr atv_attribute th_attrs }
		where
			bind_attr var=:(TA_Var {av_info_ptr}) attr_heap
				= attr_heap <:= (av_info_ptr, AVI_Attr var)
			bind_attr attr attr_heap
				= attr_heap
	freshCopy type type_heaps
		= (type, type_heaps)

freshExistentialVariables type_variables state
	= foldSt fresh_existential_variable type_variables state 
where
	fresh_existential_variable {atv_variable={tv_info_ptr}} (var_heap, var_store)
		= (var_heap <:= (tv_info_ptr, TVI_Type (TempQV var_store)), inc var_store)

fresh_type_variables :: [ATypeVar] *(*Heap TypeVarInfo,Int) -> *(!*Heap TypeVarInfo,!Int);
fresh_type_variables type_variables state
	= foldSt (\{atv_variable={tv_info_ptr}} (var_heap, var_store) -> (var_heap <:= (tv_info_ptr, TVI_Type (TempV var_store)), inc var_store))
				type_variables state

fresh_attributes :: [AttributeVar] *(*Heap AttrVarInfo,Int) -> *(!*Heap AttrVarInfo,!Int);
fresh_attributes attributes state
	= foldSt (\{av_info_ptr} (attr_heap, attr_store) -> (attr_heap <:= (av_info_ptr, AVI_Attr (TA_TempVar attr_store)), inc attr_store))
		attributes state

fresh_environment :: [AttrInequality] [AttrCoercion] *(Heap AttrVarInfo) -> *(![AttrCoercion],!*Heap AttrVarInfo);
fresh_environment inequalities attr_env attr_heap
	= foldSt fresh_inequality inequalities (attr_env, attr_heap)
	where
		fresh_inequality {ai_demanded,ai_offered} (attr_env, attr_heap)
			# (AVI_Attr dem_temp_attr, attr_heap) = readPtr ai_demanded.av_info_ptr attr_heap
			  (AVI_Attr off_temp_attr, attr_heap) = readPtr ai_offered.av_info_ptr attr_heap
			= case dem_temp_attr of
				TA_TempVar dem_attr_var
					-> case off_temp_attr of
						TA_TempVar off_attr_var
							| is_new_ineqality  dem_attr_var off_attr_var attr_env
								-> ([{ac_demanded = dem_attr_var, ac_offered = off_attr_var} : attr_env ], attr_heap)
								-> (attr_env, attr_heap)
						_
							-> (attr_env, attr_heap)
				_
					-> (attr_env, attr_heap)
			
		is_new_ineqality dem_attr_var off_attr_var [{ac_demanded, ac_offered} : attr_env]
			= (dem_attr_var <> ac_demanded || off_attr_var <> ac_offered) && is_new_ineqality dem_attr_var off_attr_var  attr_env
		is_new_ineqality dem_attr_var off_attr_var []
			= True

fresh_symbol_types [{ap_symbol={glob_object}}] cons_defs var_store type_heaps
	# {cons_type = {st_args,st_attr_env,st_result}, cons_index, cons_exi_vars} = cons_defs.[glob_object.ds_index]
	  (th_vars, var_store)		= freshExistentialVariables  cons_exi_vars (type_heaps.th_vars, var_store)
  	  (attr_env, th_attrs) 		= fresh_environment st_attr_env [] type_heaps.th_attrs
  	  (result_type, type_heaps)	= freshCopy st_result { type_heaps & th_attrs = th_attrs, th_vars = th_vars }
  	  (fresh_args, type_heaps)	= freshCopy st_args type_heaps
	= ([fresh_args], result_type, var_store, attr_env, type_heaps)
fresh_symbol_types [{ap_symbol={glob_object}} : patterns] cons_defs var_store type_heaps
	# (cons_types, result_type, var_store, attr_env, type_heaps)
			= fresh_symbol_types patterns cons_defs var_store type_heaps
	  {cons_type = {st_args,st_attr_env}, cons_index, cons_exi_vars} = cons_defs.[glob_object.ds_index]
	  (th_vars, var_store)		= freshExistentialVariables cons_exi_vars (type_heaps.th_vars, var_store)
	  (attr_env, th_attrs) 		= fresh_environment st_attr_env attr_env type_heaps.th_attrs
  	  (fresh_args, type_heaps) 	= freshCopy st_args { type_heaps & th_attrs = th_attrs, th_vars = th_vars }
	= ([fresh_args : cons_types], result_type, var_store, attr_env, type_heaps)

freshUniversalVariables type_variables state
	= foldSt fresh_universal_variable type_variables state 
where
	fresh_universal_variable {atv_variable={tv_info_ptr}} (var_heap, var_store)
		= (var_heap <:= (tv_info_ptr, TVI_Type (TempQV var_store)), inc var_store)

freshAlgebraicType :: !(Global Int) ![AlgebraicPattern] !{#CommonDefs} !*TypeState -> (![[AType]],!AType,![AttrCoercion],!*TypeState)
freshAlgebraicType {glob_module, glob_object} patterns common_defs ts=:{ts_var_store,ts_attr_store,ts_type_heaps,ts_td_infos}
	# {td_rhs,td_args,td_attrs,td_name,td_attribute} = common_defs.[glob_module].com_type_defs.[glob_object]
	# (th_vars, ts_var_store)		= fresh_type_variables td_args (ts_type_heaps.th_vars, ts_var_store)
	  (th_attrs, ts_attr_store)		= fresh_attributes td_attrs (ts_type_heaps.th_attrs, ts_attr_store)
	  type_heaps					= { ts_type_heaps & th_vars = th_vars, th_attrs = th_attrs }
	  (cons_types, alg_type, ts_var_store, attr_env, type_heaps)
	  		= fresh_symbol_types patterns common_defs.[glob_module].com_cons_defs ts_var_store type_heaps
	= (cons_types, alg_type, attr_env, { ts & ts_var_store = ts_var_store, ts_attr_store = ts_attr_store, ts_type_heaps = type_heaps })
//		---> ("freshAlgebraicType", alg_type, cons_types)

fresh_overloaded_list_type [{ap_symbol}:patterns] pd_cons_symbol pd_nil_symbol decons_u_index nil_u_index stdStrictLists_index pos functions common_defs ts
	| ap_symbol.glob_module==cPredefinedModuleIndex
		| ap_symbol.glob_object.ds_index==pd_cons_symbol-FirstConstructorPredefinedSymbolIndex
			# (argument_types,result_type,tst_context,tst_attr_env,ts) = make_cons_type_from_decons_type stdStrictLists_index decons_u_index common_defs ts
			= case patterns of
				[]
					-> ([argument_types],result_type,tst_context,tst_attr_env,ts)
				[pattern=:{ap_symbol}]
					| ap_symbol.glob_module==cPredefinedModuleIndex && ap_symbol.glob_object.ds_index==pd_nil_symbol-FirstConstructorPredefinedSymbolIndex
						-> ([argument_types,[]],result_type,tst_context,tst_attr_env,ts)
		| ap_symbol.glob_object.ds_index==pd_nil_symbol-FirstConstructorPredefinedSymbolIndex
			= case patterns of
				[]
					# {ft_type,ft_symb,ft_type_ptr,ft_specials} = functions.[stdStrictLists_index].[nil_u_index]
					# (fun_type_copy, ts) = determineSymbolTypeOfFunction pos ft_symb 0/*symb_arity*/ ft_type ft_type_ptr common_defs ts
					  {tst_args,tst_result,tst_context,tst_attr_env}=fun_type_copy
					-> ([tst_args],tst_result,tst_context,tst_attr_env,ts)
				[pattern=:{ap_symbol}]
					| ap_symbol.glob_module==cPredefinedModuleIndex && ap_symbol.glob_object.ds_index==pd_cons_symbol-FirstConstructorPredefinedSymbolIndex
						# (argument_types,result_type,tst_context,tst_attr_env,ts) = make_cons_type_from_decons_type stdStrictLists_index decons_u_index common_defs ts
						-> ([[],argument_types],result_type,tst_context,tst_attr_env,ts)
			= abort "fresh_overloaded_list_type"
	where
		make_cons_type_from_decons_type stdStrictLists_index decons_u_index common_defs ts
			# {me_symb,me_type,me_type_ptr} = common_defs.[stdStrictLists_index].com_member_defs.[decons_u_index]
			  (fun_type_copy,ts) = determineSymbolTypeOfFunction pos me_symb 1/*symb_arity*/ me_type me_type_ptr common_defs ts
			  {tst_args,tst_arity,tst_lifted,tst_result,tst_context,tst_attr_env}=fun_type_copy						  
			# result_type = case tst_args of [t] -> t
			# argument_types = case tst_result.at_type of (TA _ args=:[arg1,arg2]) ->args
			= (argument_types,result_type,tst_context,tst_attr_env,ts)

freshOverloadedListType :: !OverloadedListType !CoercionPosition ![AlgebraicPattern] !{#CommonDefs} !{#{#FunType }} !*TypeState -> (![[AType]],!AType,![TypeContext],![AttrCoercion],!*TypeState)
freshOverloadedListType (UnboxedList _ stdStrictLists_index decons_u_index nil_u_index) pos patterns common_defs functions ts
	= fresh_overloaded_list_type patterns PD_UnboxedConsSymbol PD_UnboxedNilSymbol decons_u_index nil_u_index stdStrictLists_index pos functions common_defs ts
freshOverloadedListType (UnboxedTailStrictList _ stdStrictLists_index decons_u_index nil_u_index) pos patterns common_defs functions ts
	= fresh_overloaded_list_type patterns PD_UnboxedTailStrictConsSymbol PD_UnboxedTailStrictNilSymbol decons_u_index nil_u_index stdStrictLists_index pos functions common_defs ts
freshOverloadedListType (OverloadedList _ stdStrictLists_index decons_u_index nil_u_index) pos patterns common_defs functions ts
	= fresh_overloaded_list_type patterns PD_OverloadedConsSymbol PD_OverloadedNilSymbol decons_u_index nil_u_index stdStrictLists_index pos functions common_defs ts

cWithFreshContextVars 		:== True
cWithoutFreshContextVars 	:== False

freshSymbolType :: !(Optional CoercionPosition) !Bool !SymbolType {#u:CommonDefs} !*TypeState -> (!TempSymbolType,!*TypeState)
freshSymbolType is_appl fresh_context_vars st=:{st_vars,st_args,st_result,st_context,st_attr_vars,st_attr_env,st_arity} common_defs
				ts=:{ts_var_store,ts_attr_store,ts_type_heaps,ts_td_infos,ts_var_heap,ts_cons_variables,ts_exis_variables}
	# (th_vars, ts_var_store)	= fresh_type_variables st_vars (ts_type_heaps.th_vars, ts_var_store)
	  (th_attrs, ts_attr_store)	= fresh_attributes st_attr_vars (ts_type_heaps.th_attrs, ts_attr_store)
	  (attr_env, th_attrs)		= freshEnvironment st_attr_env th_attrs 
	  type_heaps 				= { ts_type_heaps & th_vars = th_vars, th_attrs = th_attrs }
	  (tst_args, (ts_var_store, ts_attr_store, ts_exis_variables, type_heaps))
	  							= fresh_arg_types is_appl st_args (ts_var_store, ts_attr_store, ts_exis_variables, type_heaps)
	  (tst_result, type_heaps)	= freshCopy st_result type_heaps
	  (tst_context, (type_heaps, ts_var_heap)) 	= freshTypeContexts fresh_context_vars st_context (type_heaps, ts_var_heap)
	  cons_variables			= foldSt (collect_cons_variables_in_tc common_defs) tst_context [] 
	= ({ tst_args = tst_args, tst_result = tst_result, tst_context = tst_context, tst_attr_env = attr_env, tst_arity = st_arity, tst_lifted = 0 },
	   { ts & ts_var_store = ts_var_store, ts_attr_store = ts_attr_store, ts_type_heaps = type_heaps, ts_var_heap = ts_var_heap,
	   				ts_cons_variables = cons_variables ++ ts_cons_variables, ts_exis_variables = ts_exis_variables })
		//---> ("freshSymbolType", st, tst_args, tst_result, tst_context)
	where
		fresh_type_variables :: .[TypeVar] *(*Heap TypeVarInfo,.Int) -> (!.Heap TypeVarInfo,!Int);
		fresh_type_variables type_variables state
			= foldr (\{tv_info_ptr} (var_heap, var_store) -> (writePtr tv_info_ptr (TVI_Type (TempV var_store)) var_heap, inc var_store))
							state type_variables

		fresh_attributes :: .[AttributeVar] *(*Heap AttrVarInfo,.Int) -> (!.Heap AttrVarInfo,!Int);
		fresh_attributes attributes state
			= foldr (\{av_info_ptr} (attr_heap, attr_store) -> (writePtr av_info_ptr (AVI_Attr (TA_TempVar attr_store)) attr_heap, inc attr_store))
							state attributes

		collect_cons_variables_in_tc common_defs tc=:{tc_class={glob_module,glob_object={ds_index}}, tc_types} collected_cons_vars
			# {class_cons_vars} = common_defs.[glob_module].com_class_defs.[ds_index]
			= collect_cons_variables tc_types class_cons_vars collected_cons_vars
		
		collect_cons_variables [] class_cons_vars collected_cons_vars
			= collected_cons_vars
		collect_cons_variables [type : tc_types] class_cons_vars collected_cons_vars
			| class_cons_vars bitand 1 == 0
				= collect_cons_variables tc_types (class_cons_vars >> 1) collected_cons_vars
				= case type of
					TempV temp_var_id 
						-> collect_cons_variables tc_types (class_cons_vars >> 1) (add_variable temp_var_id collected_cons_vars)
//							---> ("collect_cons_variables", temp_var_id)
					_
						-> collect_cons_variables tc_types (class_cons_vars >> 1) collected_cons_vars
						
		add_variable new_var_id []
			= [new_var_id]
		add_variable new_var_id vars=:[var_id : var_ids]
			| new_var_id == var_id
				= vars
				= [var_id : add_variable new_var_id var_ids]
				
		fresh_arg_types No arg_types (var_store, attr_store, exis_variables, type_heaps)
			# (arg_types, type_heaps) = freshArgumentsOfSymbolType arg_types type_heaps
			= (arg_types, (var_store, attr_store, exis_variables, type_heaps))
		fresh_arg_types (Yes pos) arg_types (var_store, attr_store, exis_variables, type_heaps)
			= mapSt (fresh_arg_type pos) arg_types (var_store, attr_store, exis_variables, type_heaps)
		where
			fresh_arg_type pos at=:{at_attribute, at_type = TFA vars type} (var_store, attr_store, exis_variables, type_heaps)
				# (fresh_attribute, th_attrs)	= freshCopyOfTypeAttribute at_attribute type_heaps.th_attrs
				# (var_store, attr_store, new_exis_variables, type_heaps)
						= foldSt fresh_var_and_attr vars (var_store, attr_store, [], { type_heaps & th_attrs = th_attrs })
				  (fresh_type, type_heaps)				= freshCopy type type_heaps
				  type_heaps							= clearBindings vars type_heaps
				= ({ at &  at_attribute = fresh_attribute, at_type = fresh_type },
						(var_store, attr_store, add_exis_variables pos new_exis_variables exis_variables, type_heaps))
			fresh_arg_type _ at (var_store, attr_store, exis_variables, type_heaps)
				# (fresh_at, type_heaps) = freshCopy at type_heaps
				= (fresh_at, (var_store, attr_store, exis_variables, type_heaps))

			fresh_var_and_attr {atv_attribute, atv_variable = tv=:{tv_info_ptr}} (var_store, attr_store, exis_variables, type_heaps)
				# (attr_store, exis_variables, th_attrs) = fresh_attr atv_attribute (attr_store, exis_variables, type_heaps.th_attrs)
				= (inc var_store,  attr_store, exis_variables, { type_heaps & th_vars = type_heaps.th_vars <:= (tv_info_ptr, TVI_Type (TempQV var_store)), th_attrs = th_attrs })
			where
				fresh_attr var=:(TA_Var {av_info_ptr}) (attr_store, exis_variables, attr_heap)
					= (inc attr_store, [attr_store : exis_variables], attr_heap <:= (av_info_ptr, AVI_Attr (TA_TempVar attr_store)))
				fresh_attr attr state
					= state
			
			add_exis_variables pos [] exis_variables
				= exis_variables
			add_exis_variables pos new_exis_variables exis_variables
				= [(pos, new_exis_variables) : exis_variables]

freshArgumentsOfSymbolType :: ![AType] !*TypeHeaps -> (![AType], !*TypeHeaps)
freshArgumentsOfSymbolType atypes type_heaps = mapSt fresh_arg_type atypes type_heaps
where
	fresh_arg_type at=:{at_attribute, at_type = TFA vars type} type_heaps
		# (fresh_attribute, th_attrs)			= freshCopyOfTypeAttribute at_attribute type_heaps.th_attrs
		# type_heaps							= foldSt bind_var_and_attr vars { type_heaps & th_attrs = th_attrs }
		  (fresh_type, type_heaps)				= freshCopy type type_heaps
		  type_heaps							= clearBindings vars type_heaps
		= ({ at &  at_attribute = fresh_attribute, at_type = TFA vars fresh_type }, type_heaps)
	where
		bind_var_and_attr {atv_attribute, atv_variable = tv=:{tv_info_ptr}} type_heaps=:{th_vars,th_attrs}
			= { type_heaps & th_vars = th_vars <:= (tv_info_ptr, TVI_Type (TV tv)), th_attrs = bind_attr atv_attribute th_attrs }
		where
			bind_attr var=:(TA_Var {av_info_ptr}) attr_heap
				= attr_heap <:= (av_info_ptr, AVI_Attr var)
			bind_attr attr attr_heap
				= attr_heap
	fresh_arg_type at type_heaps
		= freshCopy at type_heaps
	
freshInequality :: AttrInequality *(Heap AttrVarInfo) -> (!AttrCoercion,!.Heap AttrVarInfo);
freshInequality {ai_demanded,ai_offered} attr_heap
	# (av_dem_info, attr_heap) = readPtr ai_demanded.av_info_ptr attr_heap
	  (av_off_info, attr_heap) = readPtr ai_offered.av_info_ptr attr_heap
	  (AVI_Attr (TA_TempVar dem_attr_var)) = av_dem_info
	  (AVI_Attr (TA_TempVar off_attr_var)) = av_off_info
	= ({ac_demanded = dem_attr_var, ac_offered = off_attr_var}, attr_heap) // <<- (av_dem_info,av_off_info)
	
freshEnvironment [ineq : ineqs] attr_heap
	# (fresh_ineq, attr_heap) = freshInequality ineq attr_heap
	  (fresh_env, attr_heap) = freshEnvironment ineqs attr_heap
	= ([fresh_ineq : fresh_env], attr_heap)
freshEnvironment [] attr_heap
	= ([], attr_heap)

freshTypeContexts fresh_context_vars tcs cs_and_var_heap
	= mapSt (fresh_type_context fresh_context_vars) tcs cs_and_var_heap
where	
	fresh_type_context fresh_context_vars tc=:{tc_types} (type_heaps, var_heap)
		# (tc_types, type_heaps) = mapSt fresh_context_type tc_types type_heaps
		| fresh_context_vars
			# (new_info_ptr, var_heap) = newPtr VI_Empty var_heap
			= ({ tc & tc_types = tc_types, tc_var = new_info_ptr }, (type_heaps, var_heap))
			= ({ tc & tc_types = tc_types}, (type_heaps, var_heap))

	fresh_context_type (CV tv :@: types) type_heaps=:{th_vars}
		# (fresh_cons_var, th_vars)		= freshConsVariable tv th_vars
		  (types, type_heaps) = freshCopy types { type_heaps & th_vars = th_vars }
		= (fresh_cons_var :@: types, type_heaps)
	fresh_context_type type type_heaps
		= freshCopy type type_heaps

freshAttributedVariable :: !u:TypeState -> (!AType, !u:TypeState)
freshAttributedVariable ts=:{ts_var_store,ts_attr_store}
	= ({ at_attribute = TA_TempVar ts_attr_store, at_annotation = AN_None, at_type = TempV ts_var_store },
	     {ts & ts_var_store = inc ts_var_store, ts_attr_store = inc ts_attr_store})

freshNonUniqueVariable :: !u:TypeState -> (!AType, !u:TypeState)
freshNonUniqueVariable ts=:{ts_var_store}
	= ({ at_attribute = TA_Multi, at_annotation = AN_None, at_type = TempV ts_var_store },
	     {ts & ts_var_store = inc ts_var_store})

freshAttribute :: !u:TypeState -> (!TypeAttribute, !u:TypeState)
freshAttribute ts=:{ts_attr_store}
	= (TA_TempVar ts_attr_store, {ts & ts_attr_store = inc ts_attr_store})


::	PropState =
	{	prop_type_heaps	:: !.TypeHeaps
	,	prop_td_infos	:: !.TypeDefInfos
	,	prop_attr_vars	:: ![AttributeVar]
	,	prop_attr_env	:: ![AttrInequality]
	,	prop_error		:: !.Optional .ErrorAdmin
	}

attribute_error type_attr No
	= No // XXX abort ("sanity check nr 723 failed in module type"--->("type_attr", type_attr))
attribute_error type_attr (Yes err)
	# err = errorHeading "Type error" err
	= Yes { err & ea_file = err.ea_file <<< "* attribute expected instead of " <<< type_attr <<< '\n' }

addPropagationAttributesToAType :: {#CommonDefs} !AType !*PropState -> *(!AType,Int,!*PropState);
addPropagationAttributesToAType modules type=:{at_type = TA cons_id=:{type_index={glob_object,glob_module},type_name} cons_args, at_attribute} ps
	# (cons_args, props, ps=:{prop_td_infos,prop_type_heaps,prop_attr_vars,prop_attr_env,prop_error})
			= add_propagation_attributes_to_atypes modules cons_args ps
	  (prop_class, th_vars, prop_td_infos) = propClassification glob_object glob_module props modules prop_type_heaps.th_vars prop_td_infos
	  (at_attribute, prop_class, th_attrs, prop_attr_vars, prop_attr_env, prop_error)
	  		= determine_attribute_of_cons modules at_attribute cons_args prop_class prop_type_heaps.th_attrs prop_attr_vars prop_attr_env prop_error
	= ({ type & at_type = TA cons_id cons_args, at_attribute = at_attribute }, prop_class,  { ps & prop_attr_vars = prop_attr_vars,
			prop_td_infos = prop_td_infos, prop_attr_env = prop_attr_env,
				prop_type_heaps = { prop_type_heaps & th_vars = th_vars, th_attrs = th_attrs}, prop_error = prop_error })
	where
		add_propagation_attributes_to_atypes modules [] ps
			= ([], [], ps) 
		add_propagation_attributes_to_atypes modules [atype : atypes] ps
			# (atype, prop_class, ps) = addPropagationAttributesToAType modules atype ps
			  (atypes, prop_classes, ps) = add_propagation_attributes_to_atypes modules atypes ps
			= ([atype : atypes], [prop_class : prop_classes], ps)
	
		determine_attribute_of_cons modules TA_Unique cons_args prop_class attr_var_heap attr_vars attr_env ps_error
			= (TA_Unique, prop_class >> length cons_args, attr_var_heap, attr_vars, attr_env, ps_error)
		determine_attribute_of_cons modules cons_attr cons_args prop_class attr_var_heap attr_vars attr_env ps_error
			# (cumm_attr, prop_attrs, prop_class) = determine_cummulative_attribute cons_args TA_Multi [] prop_class
			  (comb_attr, attr_var_heap, attr_vars, attr_env, ps_error)
			  		= combine_attributes cons_attr cumm_attr prop_attrs attr_var_heap attr_vars attr_env ps_error
			= (comb_attr, prop_class, attr_var_heap, attr_vars, attr_env, ps_error)
			  
		determine_cummulative_attribute [] cumm_attr attr_vars prop_class
			= (cumm_attr, attr_vars, prop_class)
		determine_cummulative_attribute [{at_attribute} : types ] cumm_attr attr_vars prop_class
			| prop_class bitand 1 == 0
				= determine_cummulative_attribute types cumm_attr attr_vars (prop_class >> 1)
				= case at_attribute of
					TA_Unique
						-> (TA_Unique, [], prop_class >> length types)
					TA_Multi
						-> determine_cummulative_attribute types cumm_attr attr_vars (prop_class >> 1)
					TA_Var attr_var
						-> determine_cummulative_attribute types at_attribute [attr_var : attr_vars] (prop_class >> 1)
					TA_MultiOfPropagatingConsVar
						-> determine_cummulative_attribute types cumm_attr attr_vars (prop_class >> 1)

		combine_attributes (TA_Var attr_var) cumm_attr prop_vars attr_var_heap attr_vars attr_env ps_error
			= case cumm_attr of
				TA_Unique
					-> (TA_Unique, attr_var_heap, attr_vars, attr_env, attribute_error attr_var ps_error)
				
				TA_Multi
					-> (TA_Var attr_var, attr_var_heap, attr_vars, attr_env, ps_error)
				TA_Var _
					-> (TA_Var attr_var, attr_var_heap, attr_vars, foldSt (new_inequality attr_var) prop_vars attr_env, ps_error)
		where
			new_inequality off_attr_var dem_attr_var [] 
				= [{ ai_demanded = dem_attr_var, ai_offered = off_attr_var }]
			new_inequality off_attr_var dem_attr_var ins=:[ inequal : iequals ]
				 | dem_attr_var.av_info_ptr == inequal.ai_demanded.av_info_ptr && off_attr_var.av_info_ptr == inequal.ai_offered.av_info_ptr
				 	= ins
				 	= [ inequal : new_inequality off_attr_var dem_attr_var iequals ]
	
		combine_attributes _ (TA_Var var) prop_vars attr_var_heap attr_vars attr_env ps_error
			# (new_attr_ptr, attr_var_heap) = newPtr AVI_Empty attr_var_heap
			  new_attr_var = { var & av_info_ptr = new_attr_ptr }
			= (TA_Var new_attr_var, attr_var_heap, [new_attr_var : attr_vars],
					mapAppend (\ai_demanded -> { ai_demanded = ai_demanded, ai_offered = new_attr_var }) prop_vars attr_env, ps_error)
		combine_attributes cons_attr TA_Unique _ attr_var_heap attr_vars attr_env ps_error
			= (TA_Unique, attr_var_heap, attr_vars, attr_env, ps_error)
		combine_attributes cons_attr _ _ attr_var_heap attr_vars attr_env ps_error
			= (cons_attr, attr_var_heap, attr_vars, attr_env, ps_error)

addPropagationAttributesToAType modules type=:{at_type} ps
	# (at_type, ps) = addPropagationAttributesToType modules at_type ps
	= ({ type & at_type = at_type }, NoPropClass, ps)

addPropagationAttributesToType modules (arg_type --> res_type) ps
	# (arg_type, prop_class, ps) = addPropagationAttributesToAType modules arg_type ps
	  (res_type, prop_class, ps) = addPropagationAttributesToAType modules res_type ps
	= (arg_type --> res_type, ps)
addPropagationAttributesToType modules (type_var :@: types) ps
	# (types, ps) = addPropagationAttributesToATypes modules types ps
	= (type_var :@: types, ps)
//AA..
addPropagationAttributesToType modules (TArrow1 arg_type) ps
	# (arg_type, prop_class, ps) = addPropagationAttributesToAType modules arg_type ps
	= (TArrow1 arg_type, ps)
//..AA
addPropagationAttributesToType modules type ps
	= (type, ps)

addPropagationAttributesToATypes :: {#CommonDefs} ![AType] !*PropState -> (![AType],!*PropState)
addPropagationAttributesToATypes modules types ps
	= mapSt (add_propagation_attributes_to_atype modules) types ps
where
	add_propagation_attributes_to_atype modules type ps
		# (type, prop_class, ps) = addPropagationAttributesToAType modules type ps
		= (type, ps)

:: Base :== {! AType}

currySymbolType st=:{tst_args,tst_arity,tst_result,tst_attr_env} req_arity ts=:{ts_attr_store}
	| tst_arity == req_arity
		= (st, ts)
	# (tst_args, rest_args, is_unique) = split_args req_arity tst_args 
	| is_unique
		# (type, _, _) = buildCurriedType rest_args tst_result TA_Unique [] 0
		= ({ st & tst_args = tst_args, tst_arity = req_arity, tst_result = type }, ts)
		# (type, tst_attr_env, ts_attr_store) = buildCurriedType rest_args tst_result (TA_TempVar ts_attr_store)
		  		(build_attr_env ts_attr_store tst_args tst_attr_env) (inc ts_attr_store)
		= ({ st & tst_args = tst_args, tst_arity = req_arity, tst_result = type, tst_attr_env = tst_attr_env }, { ts & ts_attr_store = ts_attr_store })
where
	split_args 0 args = ([], args, False)
	split_args n [atype=:{at_attribute} : args]
		# (left, right, is_unique) = split_args (dec n) args
		= ([ atype : left ], right, is_unique || attr_is_unique at_attribute)
	
	attr_is_unique TA_Unique = True
	attr_is_unique _ = False
	
	build_attr_env cum_attr_var [] attr_env
		= attr_env
	build_attr_env cum_attr_var [{at_attribute=(TA_TempVar attr_var)} : args] attr_env
		= build_attr_env cum_attr_var args [{ ac_demanded = attr_var, ac_offered = cum_attr_var } : attr_env]
	build_attr_env cum_attr_var [_ : args] attr_env
		= build_attr_env cum_attr_var args attr_env


emptyIdent =: { id_name = "", id_info = nilPtr }

buildCurriedType [] type cum_attr attr_env attr_store
	= (type, attr_env, attr_store)
buildCurriedType [at=:{at_attribute}:ats] type cum_attr attr_env attr_store
	# (next_cum_attr, attr_env, attr_store) = combine_attributes at_attribute cum_attr attr_env attr_store
	  (res_type, attr_env, attr_store) = buildCurriedType ats type next_cum_attr attr_env attr_store
	= ({at_annotation = AN_None, at_attribute = cum_attr , at_type = at --> res_type }, attr_env, attr_store)
where
	combine_attributes TA_Unique cum_attr attr_env attr_store
		= (TA_Unique, attr_env, attr_store)
	combine_attributes (TA_TempVar attr_var) (TA_TempVar cum_attr_var) attr_env attr_store
		= (TA_TempVar attr_store, [{ ac_demanded = cum_attr_var,ac_offered = attr_store },{ ac_demanded = attr_var,ac_offered = attr_store }:attr_env], inc attr_store)
	combine_attributes (TA_TempVar _) cum_attr attr_env attr_store
		= (cum_attr, attr_env, attr_store)
	combine_attributes _ (TA_TempVar cum_attr_var) attr_env attr_store
		= (TA_TempVar attr_store, [{ ac_demanded = cum_attr_var,ac_offered = attr_store }:attr_env], inc attr_store)
	combine_attributes _ cum_attr attr_env attr_store
		= (cum_attr, attr_env, attr_store)

determineSymbolTypeOfFunction :: CoercionPosition Ident Int SymbolType (Ptr VarInfo) {#CommonDefs} *TypeState -> *(!TempSymbolType,!*TypeState);
determineSymbolTypeOfFunction pos ident act_arity st=:{st_args,st_result,st_attr_vars,st_attr_env} type_ptr common_defs ts=:{ts_var_heap}
	# (type_info, ts_var_heap) = readPtr type_ptr ts_var_heap
	  ts = { ts & ts_var_heap = ts_var_heap }
	= case type_info of
		VI_PropagationType symb_type
	   		# (copy_symb_type, ts) = freshSymbolType (Yes pos) cWithFreshContextVars symb_type common_defs ts 
			-> currySymbolType copy_symb_type act_arity ts
		_	
			# (st_args, ps) = addPropagationAttributesToATypes common_defs st_args
					{ prop_type_heaps = ts.ts_type_heaps, prop_td_infos = ts.ts_td_infos,
					  prop_attr_vars = st_attr_vars, prop_attr_env = st_attr_env, prop_error = Yes ts.ts_error}
			  (st_result, _, {prop_type_heaps,prop_td_infos,prop_attr_vars,prop_error = Yes ts_error,prop_attr_env})
			  			= addPropagationAttributesToAType common_defs st_result ps
			  st = { st & st_args = st_args, st_result = st_result, st_attr_vars = prop_attr_vars, st_attr_env = prop_attr_env }
	   		# (copy_symb_type, ts) = freshSymbolType (Yes pos) cWithFreshContextVars st common_defs { ts &
	   										ts_type_heaps = prop_type_heaps, ts_td_infos = prop_td_infos, ts_error = ts_error,
											ts_var_heap = ts.ts_var_heap <:= (type_ptr, VI_PropagationType st) }
			-> currySymbolType copy_symb_type act_arity ts

standardFieldSelectorType pos {glob_object={ds_ident,ds_index},glob_module} {ti_common_defs} ts=:{ts_var_store,ts_type_heaps}
	#! {sd_type,sd_exi_vars} = ti_common_defs.[glob_module].com_selector_defs.[ds_index]
	# (th_vars, ts_var_store) = freshExistentialVariables sd_exi_vars (ts_type_heaps.th_vars, ts_var_store)
	= freshSymbolType (Yes pos) cWithFreshContextVars sd_type ti_common_defs { ts & ts_type_heaps = { ts_type_heaps & th_vars = th_vars }, ts_var_store = ts_var_store }
//		 ---> ("standardFieldSelectorType", ds_ident, inst)

standardTupleSelectorType pos {ds_index} arg_nr {ti_common_defs} ts
	#! {cons_type} = ti_common_defs.[cPredefinedModuleIndex].com_cons_defs.[ds_index]
	= freshSymbolType (Yes pos) cWithFreshContextVars { cons_type & st_args = [cons_type.st_result], st_result = cons_type.st_args !! arg_nr } ti_common_defs ts

standardRhsConstructorType pos index mod arity {ti_common_defs} ts
	#! {cons_symb, cons_type, cons_exi_vars } = ti_common_defs.[mod].com_cons_defs.[index]
	# cons_type = { cons_type & st_vars = mapAppend (\{atv_variable} -> atv_variable) cons_exi_vars cons_type.st_vars }
	  (fresh_type, ts) = freshSymbolType (Yes pos) cWithFreshContextVars cons_type ti_common_defs ts
	= currySymbolType fresh_type arity ts
//		 ---> ("standardRhsConstructorType", cons_symb, fresh_type)

standardLhsConstructorType index mod arity {ti_common_defs} ts=:{ts_var_store,ts_type_heaps}
	#! {cons_symb, cons_type, cons_exi_vars } = ti_common_defs.[mod].com_cons_defs.[index]
	# (th_vars, ts_var_store) = freshExistentialVariables cons_exi_vars (ts_type_heaps.th_vars, ts_var_store)
	= freshSymbolType No cWithFreshContextVars cons_type ti_common_defs { ts & ts_type_heaps = { ts_type_heaps & th_vars = th_vars }, ts_var_store = ts_var_store }
//		 ---> ("standardLhsConstructorType", cons_symb, fresh_type)

:: ReferenceMarking :== Bool

cIsRecursive :== True
cIsNotRecursive :== False

storeAttribute (Yes expt_ptr) type_attribute symbol_heap
	= symbol_heap <:=  (expt_ptr, EI_Attribute (toInt type_attribute))
storeAttribute No type_attribute symbol_heap
	= symbol_heap

getSymbolType :: CoercionPosition TypeInput SymbIdent *TypeState -> *(!TempSymbolType,![Special],!*TypeState);
getSymbolType pos ti=:{ti_functions,ti_common_defs,ti_main_dcl_module_n} {symb_kind = SK_Function {glob_module,glob_object}, symb_arity, symb_name} ts
	| glob_module == ti_main_dcl_module_n
		| glob_object>=size ts.ts_fun_env
			= abort symb_name.id_name;
		# (fun_type, ts) = ts!ts_fun_env.[glob_object]
		= case fun_type of
			UncheckedType fun_type
				# (fun_type_copy, ts) = currySymbolType fun_type symb_arity ts
				-> (fun_type_copy, [], ts)
			SpecifiedType fun_type lifted_arg_types _ 
				# (fun_type_copy=:{tst_args,tst_arity}, ts) = freshSymbolType (Yes pos) cWithoutFreshContextVars fun_type ti_common_defs ts
				  (fun_type_copy, ts) = currySymbolType { fun_type_copy & tst_args = lifted_arg_types ++ fun_type_copy.tst_args,
				  										  tst_arity = tst_arity + length lifted_arg_types } symb_arity ts
				-> (fun_type_copy, [], ts)
			CheckedType fun_type
				# (fun_type_copy, ts) = freshSymbolType (Yes pos) cWithFreshContextVars fun_type ti_common_defs ts
				  (fun_type_copy,ts) = currySymbolType fun_type_copy symb_arity ts
				-> (fun_type_copy, [], ts)
			_
				-> abort ("getSymbolType: SK_Function "+++toString symb_name+++" "+++toString glob_object)
//				-> abort "getSymbolType (type.icl)" ---> (symb_name, glob_object, fun_type)
		# {ft_type,ft_type_ptr,ft_specials} = ti_functions.[glob_module].[glob_object]
		| glob_module>=size ti_functions || glob_object>=size ti_functions.[glob_module]
			= abort (toString glob_module+++" "+++toString glob_object+++" "+++toString ti_main_dcl_module_n+++" "+++symb_name.id_name);
		# (fun_type_copy, ts) = determineSymbolTypeOfFunction pos symb_name symb_arity ft_type ft_type_ptr ti_common_defs ts
		= (fun_type_copy, get_specials ft_specials, ts)
	where
		get_specials (SP_ContextTypes specials) = specials
		get_specials SP_None 					= []
getSymbolType pos ti {symb_kind = SK_Constructor {glob_module,glob_object}, symb_arity} ts
	# (fresh_cons_type, ts) = standardRhsConstructorType pos glob_object glob_module symb_arity ti ts
	= (fresh_cons_type, [], ts) 
getSymbolType pos ti=:{ti_functions,ti_common_defs,ti_main_dcl_module_n} {symb_kind = SK_LocalMacroFunction glob_object, symb_arity, symb_name} ts
	| glob_object>=size ts.ts_fun_env
		= abort symb_name.id_name;
	# (fun_type, ts) = ts!ts_fun_env.[glob_object]
	= case fun_type of
		UncheckedType fun_type
			# (fun_type_copy, ts) = currySymbolType fun_type symb_arity ts
			-> (fun_type_copy, [], ts)
		SpecifiedType fun_type lifted_arg_types _ 
			# (fun_type_copy=:{tst_args,tst_arity}, ts) = freshSymbolType (Yes pos) cWithoutFreshContextVars fun_type ti_common_defs ts
			  (fun_type_copy, ts) = currySymbolType { fun_type_copy & tst_args = lifted_arg_types ++ fun_type_copy.tst_args,
			  										  tst_arity = tst_arity + length lifted_arg_types } symb_arity ts
			-> (fun_type_copy, [], ts)
		CheckedType fun_type
			# (fun_type_copy, ts) = freshSymbolType (Yes pos) cWithFreshContextVars fun_type ti_common_defs ts
			  (fun_type_copy,ts) = currySymbolType fun_type_copy symb_arity ts
			-> (fun_type_copy, [], ts)
		_
			-> abort ("getSymbolType SK_LocalMacroFunction: "+++toString symb_name+++" " +++toString glob_object)
//			-> abort "getSymbolType (type.icl)" ---> (symb_name, glob_object, fun_type)
getSymbolType pos ti=:{ti_common_defs} {symb_kind = SK_OverloadedFunction {glob_module,glob_object}, symb_arity} ts
	# {me_symb, me_type,me_type_ptr} = ti_common_defs.[glob_module].com_member_defs.[glob_object]
	  (fun_type_copy, ts) = determineSymbolTypeOfFunction pos me_symb symb_arity me_type me_type_ptr ti_common_defs ts
	= (fun_type_copy, [], ts)
// AA..	
getSymbolType pos ti=:{ti_common_defs} symbol=:{symb_kind = SK_Generic gen_glob kind} ts
	# (found, member_glob) = getGenericMember gen_glob kind ti_common_defs
	| not found
		= abort "getSymbolType: no class for kind"	
 		= getSymbolType pos ti {symbol & symb_kind = SK_OverloadedFunction member_glob} ts  		
// ..AA	

class requirements a :: !TypeInput !a !(!u:Requirements, !*TypeState) -> (!AType, !Optional ExprInfoPtr, !(!u:Requirements, !*TypeState))

instance requirements BoundVar
where
	requirements ti {var_name,var_info_ptr,var_expr_ptr} (reqs, ts)
		# (var_info, ts_var_heap) = readPtr var_info_ptr ts.ts_var_heap
		  ts = { ts & ts_var_heap = ts_var_heap }
		= case var_info of
			VI_Type type _
				-> (type, Yes var_expr_ptr, (reqs, ts))
			VI_FAType vars type _
				# ts = foldSt bind_var_and_attr vars ts
		  		  (fresh_type, ts_type_heaps) = freshCopy type ts.ts_type_heaps
		  		-> (fresh_type, Yes var_expr_ptr, (reqs, { ts & ts_type_heaps = ts_type_heaps }))
		  	_
				-> abort "requirements BoundVar " // ---> (var_name <<- var_info))
		where
			bind_var_and_attr {atv_attribute, atv_variable = {tv_info_ptr}} ts=:{ts_var_store, ts_attr_store, ts_type_heaps}
				# (ts_attr_store, th_attrs) = bind_attr atv_attribute (ts_attr_store, ts_type_heaps.th_attrs)				
				= { ts & ts_var_store = inc ts_var_store, ts_attr_store = ts_attr_store, ts_type_heaps = 
					{ ts_type_heaps & th_vars	= ts_type_heaps.th_vars <:= (tv_info_ptr, TVI_Type (TempV ts_var_store)),
									  th_attrs	= th_attrs }}
			where
				bind_attr (TA_Var {av_info_ptr}) (attr_store, attr_heap)
					= (inc attr_store, attr_heap <:= (av_info_ptr, AVI_Attr (TA_TempVar attr_store)))
				bind_attr attr attr_heap
					= attr_heap

instance requirements App
where
	requirements ti app=:{app_symb,app_args,app_info_ptr} (reqs=:{req_attr_coercions}, ts)
		# (tst=:{tst_attr_env,tst_args,tst_result,tst_context}, specials, ts) = getSymbolType (CP_Expression (App app)) ti app_symb ts
	  	  reqs = { reqs & req_attr_coercions = tst_attr_env ++ req_attr_coercions }
	      (reqs, ts) = requirements_of_args ti app_symb.symb_name 1 app_args tst_args (reqs, ts)
		| isEmpty tst_context
			= (tst_result, No, (reqs, ts))
			= (tst_result, No, ({ reqs & req_overloaded_calls = [app_info_ptr : reqs.req_overloaded_calls ]}, 
					{ ts & ts_expr_heap = ts.ts_expr_heap <:= (app_info_ptr,
							EI_Overloaded { oc_symbol = app_symb, oc_context = tst_context, oc_specials = specials })}))
	where
		requirements_of_args :: !TypeInput !Ident !Int ![Expression] ![AType] !(!u:Requirements, !*TypeState) -> (!u:Requirements, !*TypeState)
		requirements_of_args ti _ _ [] [] reqs_ts
			= reqs_ts
		requirements_of_args ti fun_ident arg_nr [expr:exprs] [lt:lts] reqs_ts
			# (e_type, opt_expr_ptr, (reqs, ts)) = requirements ti expr reqs_ts
			  req_type_coercions = [{ tc_demanded = lt, tc_offered = e_type, tc_position = CP_FunArg fun_ident arg_nr, tc_coercible = True } : reqs.req_type_coercions ]
			  ts_expr_heap = storeAttribute opt_expr_ptr lt.at_attribute ts.ts_expr_heap
			= requirements_of_args ti fun_ident (arg_nr+1) exprs lts ({ reqs & req_type_coercions = req_type_coercions}, { ts & ts_expr_heap = ts_expr_heap })

instance requirements Case
where
	requirements ti {case_expr,case_guards,case_default,case_info_ptr, case_default_pos} reqs_ts
		# (expr_type, opt_expr_ptr, (reqs, ts)) = requirements ti case_expr reqs_ts
		  (fresh_v, ts) = freshAttributedVariable ts
		  (cons_types, reqs_ts) = requirements_of_guarded_expressions case_guards ti case_expr expr_type opt_expr_ptr fresh_v (reqs, ts)
		  (reqs, ts) = requirements_of_default ti case_default case_default_pos fresh_v reqs_ts
		  ts_expr_heap =  ts.ts_expr_heap <:= (case_info_ptr, EI_CaseType { ct_pattern_type = expr_type, ct_result_type = fresh_v, ct_cons_types = cons_types })
		= (fresh_v, No, ({ reqs & req_case_and_let_exprs = [case_info_ptr : reqs.req_case_and_let_exprs]},
				{ ts & ts_expr_heap = ts_expr_heap }))
	where
		requirements_of_guarded_expressions (AlgebraicPatterns alg_type patterns) ti=:{ti_common_defs} match_expr pattern_type opt_pattern_ptr
						goal_type (reqs, ts)
			# (cons_types, result_type, new_attr_env, ts) = freshAlgebraicType alg_type patterns ti_common_defs ts
			  (used_cons_types, (reqs, ts)) = requirements_of_algebraic_patterns ti patterns cons_types goal_type [] (reqs, ts)
			  ts_expr_heap = storeAttribute opt_pattern_ptr result_type.at_attribute ts.ts_expr_heap
			  (position, ts_var_heap) = getPositionOfExpr match_expr ts.ts_var_heap
			= (reverse used_cons_types,  ({ reqs & req_type_coercions = [{tc_demanded = result_type,tc_offered = pattern_type, tc_position = position,
					tc_coercible = True} : reqs.req_type_coercions],
						req_attr_coercions = new_attr_env ++ reqs.req_attr_coercions }, { ts & ts_expr_heap = ts_expr_heap, ts_var_heap = ts_var_heap }))
	
		requirements_of_guarded_expressions (BasicPatterns bas_type patterns) ti match_expr pattern_type opt_pattern_ptr goal_type (reqs, ts)
			# (attr_bas_type, ts) = attributedBasicType bas_type ts
			  (reqs, ts) = requirements_of_basic_patterns ti patterns goal_type (reqs, ts)
			  ts_expr_heap = storeAttribute opt_pattern_ptr attr_bas_type.at_attribute ts.ts_expr_heap
			= ([], ({ reqs & req_type_coercions = [{tc_demanded = attr_bas_type,tc_offered = pattern_type, tc_position = CP_Expression match_expr, tc_coercible = True} :
						reqs.req_type_coercions]}, { ts & ts_expr_heap = ts_expr_heap }))

		requirements_of_guarded_expressions (OverloadedListPatterns alg_type decons_expr=:(App {app_symb,app_info_ptr}) patterns) ti=:{ti_common_defs,ti_functions} match_expr pattern_type opt_pattern_ptr goal_type (reqs, ts)
			# (position, ts_var_heap) = getPositionOfExpr match_expr ts.ts_var_heap
			# ts = {ts & ts_var_heap = ts_var_heap}
			# (cons_types, result_type, context, new_attr_env, ts) = freshOverloadedListType alg_type position patterns ti_common_defs ti_functions ts
			  (used_cons_types, (reqs, ts)) = requirements_of_algebraic_patterns ti patterns cons_types goal_type [] (reqs, ts)
			  ts_expr_heap = storeAttribute opt_pattern_ptr result_type.at_attribute ts.ts_expr_heap
			  type_coercions = [{tc_demanded = result_type,tc_offered = pattern_type, tc_position = position,tc_coercible = True} : reqs.req_type_coercions]
			  ts_expr_heap = writePtr app_info_ptr (EI_Overloaded {oc_symbol = app_symb, oc_context = context, oc_specials = []/*specials*/ }) ts_expr_heap			  
			= (reverse used_cons_types,({ reqs & req_type_coercions = type_coercions,req_attr_coercions = new_attr_env ++ reqs.req_attr_coercions,
												 req_overloaded_calls = [app_info_ptr : reqs.req_overloaded_calls ] },
										{ ts & ts_expr_heap = ts_expr_heap }))

		requirements_of_guarded_expressions (DynamicPatterns dynamic_patterns) ti match_expr pattern_type opt_pattern_ptr goal_type reqs_ts
			# dyn_type = { at_type = TB BT_Dynamic, at_attribute = TA_Multi, at_annotation = AN_None }
			  (used_dyn_types, (reqs, ts)) = requirements_of_dynamic_patterns ti goal_type dynamic_patterns [] reqs_ts
			  ts_expr_heap = storeAttribute opt_pattern_ptr TA_Multi ts.ts_expr_heap
			= (reverse used_dyn_types, ({ reqs & req_type_coercions = [{tc_demanded = dyn_type, tc_offered = pattern_type, tc_position = CP_Expression match_expr, tc_coercible = True} :
						reqs.req_type_coercions] }, { ts & ts_expr_heap = ts_expr_heap }))
	
		requirements_of_algebraic_patterns ti [] cons_types goal_type used_cons_types reqs_ts
			= (used_cons_types, reqs_ts)
		requirements_of_algebraic_patterns ti [alg_pattern=:{ap_position}:alg_patterns] [ cons_arg_types : cons_types] 
											goal_type used_cons_types reqs_ts
			= requirements_of_algebraic_patterns ti alg_patterns cons_types goal_type [ cons_arg_types : used_cons_types ]
					(possibly_accumulate_reqs_in_new_group 
						ap_position
						(requirements_of_algebraic_pattern ti alg_pattern cons_arg_types goal_type) 
						reqs_ts
					) 

		requirements_of_algebraic_pattern ti {ap_symbol, ap_vars, ap_expr} cons_arg_types goal_type (reqs, ts)
			# (res_type, opt_expr_ptr, (reqs, ts)) 
					= requirements ti ap_expr (reqs, { ts & ts_var_heap = makeBase ap_symbol.glob_object.ds_ident 1 ap_vars cons_arg_types ts.ts_var_heap})
			  ts_expr_heap = storeAttribute opt_expr_ptr res_type.at_attribute ts.ts_expr_heap
			= ({ reqs & req_type_coercions = [ { tc_demanded = goal_type, tc_offered = res_type, tc_position = CP_Expression ap_expr, tc_coercible = True } : reqs.req_type_coercions] },
					  { ts & ts_expr_heap = ts_expr_heap })
	
		requirements_of_basic_patterns _ [] goal_type reqs_ts
			= reqs_ts
		requirements_of_basic_patterns ti [{bp_expr, bp_position}:gs] goal_type reqs_ts
			= requirements_of_basic_patterns ti gs goal_type
				(possibly_accumulate_reqs_in_new_group
					bp_position
					(requirements_of_basic_pattern ti bp_expr goal_type)
					reqs_ts
				)

		requirements_of_basic_pattern ti bp_expr goal_type reqs_ts
		  	# (res_type, opt_expr_ptr, (reqs, ts)) = requirements ti bp_expr reqs_ts
			  ts_expr_heap = storeAttribute opt_expr_ptr res_type.at_attribute ts.ts_expr_heap
			= ({ reqs & req_type_coercions = [ { tc_demanded = goal_type, tc_offered = res_type, tc_position = CP_Expression bp_expr, tc_coercible = True } : reqs.req_type_coercions] },
						 { ts & ts_expr_heap = ts_expr_heap })

		requirements_of_dynamic_patterns ti goal_type [] used_dyn_types reqs_ts
			= (used_dyn_types, reqs_ts)
		requirements_of_dynamic_patterns ti goal_type [dp=:{dp_position, dp_type} : dps] used_dyn_types (reqs, ts=:{ts_expr_heap})
			# (EI_TempDynamicPattern _ _ _ _ dyn_type dyn_context dyn_expr_ptr type_code_symbol, ts_expr_heap)
					= readPtr dp_type ts_expr_heap
			  (reqs_ts) 
			  		= possibly_accumulate_reqs_in_new_group
			  				dp_position
							(requirements_of_dynamic_pattern dyn_type dyn_context dyn_expr_ptr type_code_symbol ti goal_type dp)
							(reqs, { ts & ts_expr_heap = ts_expr_heap})
			= requirements_of_dynamic_patterns ti goal_type dps [ [dyn_type] : used_dyn_types ] reqs_ts
	
		requirements_of_dynamic_pattern dyn_type dyn_context dyn_expr_ptr type_code_symbol 
										ti goal_type {dp_var={fv_info_ptr},dp_rhs} (reqs, ts=:{ts_expr_heap, ts_var_heap})
			# ts_var_heap = addToBase fv_info_ptr dyn_type No ts_var_heap
			  (dp_rhs_type, opt_expr_ptr, (reqs, ts)) = requirements ti dp_rhs (reqs, { ts & ts_expr_heap = ts_expr_heap, ts_var_heap = ts_var_heap })
			  ts_expr_heap = storeAttribute opt_expr_ptr dp_rhs_type.at_attribute ts.ts_expr_heap
			  type_coercion = { tc_demanded = goal_type, tc_offered = dp_rhs_type, tc_position = CP_Expression dp_rhs, tc_coercible = True }
			| isEmpty dyn_context
				# reqs = {reqs & req_type_coercions = [ type_coercion : reqs.req_type_coercions]}
				= (reqs, { ts &  ts_expr_heap = ts_expr_heap })
				# reqs = { reqs & req_type_coercions = [ type_coercion : reqs.req_type_coercions], req_overloaded_calls = [dyn_expr_ptr : reqs.req_overloaded_calls ]}
				= (reqs, { ts & ts_expr_heap = ts_expr_heap <:=
						(dyn_expr_ptr,  EI_Overloaded {  oc_symbol = type_code_symbol, oc_context = dyn_context, oc_specials = [] }) })	
	
		requirements_of_default ti (Yes expr) case_default_pos goal_type reqs_ts
	  		= possibly_accumulate_reqs_in_new_group
	  				case_default_pos
					(reqs_of_default ti expr goal_type)
					reqs_ts
		requirements_of_default ti No _ goal_type reqs_ts
			= reqs_ts

		reqs_of_default ti expr goal_type reqs_ts
			# (res_type, opt_expr_ptr, (reqs,  ts)) = requirements ti expr reqs_ts
			  ts_expr_heap = storeAttribute opt_expr_ptr res_type.at_attribute ts.ts_expr_heap
			= ({ reqs & req_type_coercions = [ { tc_demanded = goal_type, tc_offered = res_type, tc_position = CP_Expression expr, tc_coercible = True } : reqs.req_type_coercions] },
					{ ts & ts_expr_heap = ts_expr_heap })

instance requirements Let
where
	requirements ti {let_lazy_binds, let_strict_binds, let_expr, let_info_ptr, let_expr_position } (reqs, ts)
		# let_binds = let_strict_binds ++ let_lazy_binds
		  (rev_var_types, ts) = make_base let_binds [] ts
		  var_types = reverse rev_var_types
		  (reqs, ts) = requirements_of_binds let_binds var_types NoPos [] reqs ts
		  (res_type, opt_expr_ptr, (reqs, ts)) = requirements_of_let_expr let_expr_position ti let_expr (reqs, ts)
		  ts_expr_heap = writePtr let_info_ptr (EI_LetType var_types) ts.ts_expr_heap
		= ( res_type, opt_expr_ptr, ({ reqs & req_case_and_let_exprs = [let_info_ptr : reqs.req_case_and_let_exprs]},{ ts & ts_expr_heap = ts_expr_heap }))
	where
	
		make_base [{lb_src, lb_dst={fv_name, fv_info_ptr}}:bs] var_types ts=:{ts_var_heap}
			# (v, ts) = freshAttributedVariable ts
			  optional_position = if (is_rare_name fv_name) (Yes (CP_Expression lb_src)) No
			= make_base bs [v:var_types] { ts & ts_var_heap = writePtr fv_info_ptr (VI_Type v optional_position) ts.ts_var_heap }
		make_base [] var_types ts
			= (var_types, ts)
	
		requirements_of_binds [] bts last_position new_type_coercions reqs ts
			# reqs=add_new_group last_position new_type_coercions reqs
			= (reqs,ts)
		requirements_of_binds [{lb_src, lb_position}:bs] [b_type:bts] last_position new_type_coercions reqs ts
			| is_same_position lb_position last_position
				# (new_type_coercions,reqs,ts) = add_requirements_of_bind_to_group lb_src b_type new_type_coercions reqs ts
				= requirements_of_binds bs bts last_position new_type_coercions reqs ts
				# reqs=add_new_group last_position new_type_coercions reqs
				# new_type_coercions=[]
				# (new_type_coercions,reqs,ts) = add_requirements_of_bind_to_group_or_list lb_position lb_src b_type new_type_coercions reqs ts
				= requirements_of_binds bs bts lb_position new_type_coercions reqs ts
		  where
			is_same_position (LinePos _ line_nr1) (LinePos _ line_nr2)
				= line_nr1==line_nr2
			is_same_position (FunPos _ line_nr1 _) (FunPos _ line_nr2 _)
				= line_nr1==line_nr2
			is_same_position _ _
				= False

			add_requirements_of_bind_to_group_or_list NoPos lb_src b_type new_type_coercions reqs ts
				# (reqs,ts) = requirements_of_bind b_type ti lb_src (reqs,ts)
				= (new_type_coercions,reqs,ts)
			add_requirements_of_bind_to_group_or_list _ lb_src b_type new_type_coercions reqs ts
				= add_requirements_of_bind_to_group lb_src b_type new_type_coercions reqs ts
			
			add_requirements_of_bind_to_group lb_src b_type new_type_coercions reqs ts
				# old_req_type_coercions=reqs.req_type_coercions
				# reqs = {reqs & req_type_coercions=new_type_coercions}
				# (reqs,ts) = requirements_of_bind b_type ti lb_src (reqs,ts)
				# new_type_coercions=reqs.req_type_coercions
				# reqs = {reqs & req_type_coercions=old_req_type_coercions}
				= (new_type_coercions,reqs,ts)
	
			requirements_of_bind b_type ti lb_src reqs_ts
				# (exp_type, opt_expr_ptr, (reqs, ts))
						= requirements ti lb_src reqs_ts
				  ts_expr_heap = storeAttribute opt_expr_ptr b_type.at_attribute ts.ts_expr_heap
				  req_type_coercions = [ { tc_demanded = b_type, tc_offered = exp_type, tc_position = CP_Expression lb_src, tc_coercible = True }
				  		: reqs.req_type_coercions ]
				= ({ reqs & req_type_coercions = req_type_coercions }, { ts & ts_expr_heap = ts_expr_heap })

		add_new_group position [] reqs
			= reqs
		add_new_group position new_type_coercions reqs 
			= { reqs & req_type_coercion_groups = [{ tcg_type_coercions = new_type_coercions,	tcg_position = position } : reqs.req_type_coercion_groups]}

		requirements_of_let_expr NoPos ti let_expr reqs_ts
			= requirements ti let_expr reqs_ts
		requirements_of_let_expr let_expr_position ti let_expr (reqs=:{req_type_coercions=old_req_type_coercions}, ts)
			# reqs_with_empty_accu
					= { reqs & req_type_coercions = [] }
			  (res_type, opt_expr_ptr, (reqs_with_new_group_in_accu, ts))
			  		= requirements ti let_expr (reqs_with_empty_accu, ts)
			  new_group 
			  		= { tcg_type_coercions = reqs_with_new_group_in_accu.req_type_coercions,
			  			tcg_position = let_expr_position }
			  reqs_with_new_group
			  		= { reqs_with_new_group_in_accu & 
			  				req_type_coercion_groups = [new_group:reqs_with_new_group_in_accu.req_type_coercion_groups],
				  			req_type_coercions = old_req_type_coercions }
			= (res_type, opt_expr_ptr, (reqs_with_new_group, ts))


instance requirements DynamicExpr
where
	requirements ti {dyn_expr,dyn_info_ptr} (reqs, ts=:{ts_expr_heap})
		# (EI_TempDynamicType _ dyn_type dyn_context dyn_expr_ptr type_code_symbol, ts_expr_heap) = readPtr dyn_info_ptr ts_expr_heap
		  (dyn_expr_type, opt_expr_ptr, (reqs, ts)) = requirements ti dyn_expr (reqs, { ts & ts_expr_heap = ts_expr_heap })
		  ts_expr_heap = storeAttribute opt_expr_ptr dyn_expr_type.at_attribute ts.ts_expr_heap
		  type_coercion = { tc_demanded = dyn_type, tc_offered = dyn_expr_type, tc_position = CP_Expression dyn_expr, tc_coercible = True }
		| isEmpty dyn_context
			= ({ at_type = TB BT_Dynamic, at_attribute = TA_Multi, at_annotation = AN_None }, No, 
					({reqs & req_type_coercions = [ type_coercion : reqs.req_type_coercions]}, 
						{ ts &  ts_expr_heap = ts_expr_heap }))
			= ({ at_type = TB BT_Dynamic, at_attribute = TA_Multi, at_annotation = AN_None }, No,
					({ reqs & req_type_coercions = [ type_coercion : reqs.req_type_coercions], req_overloaded_calls = [dyn_expr_ptr : reqs.req_overloaded_calls ]},
						{ ts & ts_expr_heap = ts_expr_heap <:= (dyn_expr_ptr, EI_Overloaded {
								oc_symbol = type_code_symbol, oc_context = dyn_context, oc_specials = []}) }))

instance requirements Expression
where
	requirements ti (Var var) reqs_ts
		= requirements ti var reqs_ts
	requirements ti (App app) reqs_ts
		= requirements ti app reqs_ts

	requirements ti (function @ args) reqs_ts
		# (off_fun_type, opt_fun_expr_ptr, reqs_ts) = requirements ti function reqs_ts
		  (rev_off_arg_types, (reqs, ts)) = requirements_of_list ti args [] reqs_ts
		  (alpha, ts) = freshAttributedVariable ts
		  (fun_type, req_type_coercions, ts) = apply_type rev_off_arg_types alpha reqs.req_type_coercions function ts
		  ts_expr_heap = storeAttribute opt_fun_expr_ptr fun_type.at_attribute ts.ts_expr_heap
		= (alpha, No, ({ reqs & req_type_coercions = [{ tc_demanded = fun_type, tc_offered = off_fun_type, tc_position = CP_Expression function, tc_coercible = True } : req_type_coercions ]}, { ts & ts_expr_heap = ts_expr_heap }))
	where
		requirements_of_list _ [] rev_list_types reqs_ts
			= (rev_list_types, reqs_ts)
		requirements_of_list ti [expr:exprs] rev_list_types reqs_ts
			# (e_type, opt_expr_ptr, reqs_ts) = requirements ti expr reqs_ts
			= requirements_of_list ti exprs [(opt_expr_ptr,e_type) : rev_list_types] reqs_ts
	
		apply_type [] res_type type_coercions function ts
			= (res_type, type_coercions, ts)
		apply_type [(opt_expr_ptr,type) : types] res_type type_coercions function ts
			# (type, type_coercions, ts) = determine_demanded_type type opt_expr_ptr type_coercions function ts
			  (u, ts) = freshAttribute ts
			= apply_type types { at_annotation = AN_None, at_attribute = u, at_type = type --> res_type } type_coercions function ts
		
		determine_demanded_type :: !AType !(Optional ExprInfoPtr) ![TypeCoercion] !Expression !*TypeState
			-> (!AType, ![TypeCoercion], !*TypeState)
		determine_demanded_type type (Yes expr_ptr) type_coercions expr ts
			# (dem_type, ts) = freshAttributedVariable ts
			  ts_expr_heap = writePtr expr_ptr (EI_Attribute (toInt dem_type.at_attribute)) ts.ts_expr_heap
			= (dem_type, [ { tc_demanded = dem_type, tc_offered = type, tc_position = CP_Expression expr, tc_coercible = True } : type_coercions ],
				{ ts & ts_expr_heap = ts_expr_heap })
		determine_demanded_type type No type_coercions expr ts
			= (type, type_coercions, ts) 

	requirements ti (Case kees) reqs_ts
		= requirements ti kees reqs_ts
		
	requirements ti (Let lad) reqs_ts
		= requirements ti lad reqs_ts

	requirements ti (DynamicExpr dienamic) reqs_ts
		= requirements ti dienamic reqs_ts

	requirements ti (Selection result_type_symb expr selectors) reqs_ts
		# (expr_type, opt_expr_ptr, (reqs, ts)) = requirements ti expr reqs_ts
		= case result_type_symb of
			Yes {glob_object={ds_ident,ds_index,ds_arity}, glob_module}
				# (var, ts) = freshAttributedVariable ts
			  	  (_, result_type, (reqs, ts)) =  requirementsOfSelectors ti No expr selectors False var expr (reqs, ts)
				  tuple_type = MakeTypeSymbIdent { glob_object = ds_index, glob_module = glob_module } ds_ident ds_arity
				  non_unique_type_var = { at_attribute = TA_Multi, at_annotation = AN_None, at_type = TempV ts.ts_var_store }
				  req_type_coercions
						= [ { tc_demanded = non_unique_type_var, tc_offered = result_type, tc_position = CP_Expression expr, tc_coercible = False },
							{ tc_demanded = var, tc_offered = expr_type, tc_position = CP_Expression expr, tc_coercible = True } :
	 								reqs.req_type_coercions]
				  result_type = { at_type = TA tuple_type [non_unique_type_var,var], at_attribute = TA_Unique, at_annotation = AN_None }
				-> (result_type, No, ({ reqs & req_type_coercions = req_type_coercions }, 
						{ts & ts_var_store = inc ts.ts_var_store, ts_expr_heap = storeAttribute opt_expr_ptr TA_Multi ts.ts_expr_heap}))
			_
				# (_, result_type, reqs_ts) =  requirementsOfSelectors ti No expr selectors True expr_type expr (reqs, ts)
				-> (result_type, opt_expr_ptr, reqs_ts)
	requirements ti (Update composite_expr selectors elem_expr) reqs_ts
		# (composite_expr_type, opt_composite_expr_ptr, reqs_ts) = requirements ti composite_expr reqs_ts
		  (has_array_selection, result_type, (reqs, ts))
		  		= requirementsOfSelectors ti (Yes elem_expr) composite_expr selectors True composite_expr_type composite_expr reqs_ts
		| has_array_selection
			# ts = { ts & ts_expr_heap = storeAttribute opt_composite_expr_ptr TA_Unique ts.ts_expr_heap }
			= (composite_expr_type, No, (reqs, ts))
			= (composite_expr_type, opt_composite_expr_ptr, (reqs, ts))

	requirements ti (RecordUpdate {glob_module,glob_object={ds_index,ds_arity}} expression expressions) (reqs, ts)
		# (lhs, ts) = standardLhsConstructorType ds_index glob_module ds_arity ti ts	
		  (rhs, ts) = standardRhsConstructorType (CP_Expression expression) ds_index glob_module ds_arity ti ts	
		  (expression_type, opt_expr_ptr, reqs_ts) = requirements ti expression (reqs, ts)
		  (reqs, ts) = requirements_of_fields ti expression expressions rhs.tst_args lhs.tst_args reqs_ts
		  ts = { ts & ts_expr_heap = storeAttribute opt_expr_ptr lhs.tst_result.at_attribute ts.ts_expr_heap }
		  coercion = { tc_demanded = lhs.tst_result, tc_offered = expression_type, tc_position = CP_Expression expression, tc_coercible = True }
		= (rhs.tst_result, No, ({ reqs & req_attr_coercions = rhs.tst_attr_env ++ lhs.tst_attr_env ++ reqs.req_attr_coercions,
										 req_type_coercions = [ coercion : reqs.req_type_coercions ]}, ts))
	where 
		requirements_of_fields ti expression [] _ _ reqs_ts
			= reqs_ts
		requirements_of_fields ti expression [field : fields] [dem_type : dem_types] [off_type : off_types] reqs_ts
			# reqs_ts = requirements_of_field ti expression field dem_type off_type reqs_ts
			= requirements_of_fields ti expression fields dem_types off_types reqs_ts
	
		requirements_of_field ti expression {bind_src=NoBind expr_ptr} dem_field_type off_field_type (reqs=:{req_type_coercions}, ts)
			# ts = { ts & ts_expr_heap = ts.ts_expr_heap <:= (expr_ptr, EI_Attribute (toInt dem_field_type.at_attribute)) }
			  coercion = { tc_demanded = dem_field_type, tc_offered = off_field_type, tc_position = CP_Expression expression, tc_coercible = True }
			= ({ reqs & req_type_coercions = [ coercion : req_type_coercions ]}, ts)
		requirements_of_field ti _ {bind_src} dem_field_type _ reqs_ts
			# (expr_type, opt_expr_ptr, (reqs, ts)) = requirements ti bind_src reqs_ts
			  ts = { ts & ts_expr_heap = storeAttribute opt_expr_ptr dem_field_type.at_attribute ts.ts_expr_heap }
			  coercion = { tc_demanded = dem_field_type, tc_offered = expr_type, tc_position = CP_Expression bind_src, tc_coercible = True }
			= ({ reqs & req_type_coercions = [ coercion : reqs.req_type_coercions ]}, ts)

	requirements ti (TupleSelect tuple_symbol arg_nr expr) (reqs=:{req_attr_coercions}, ts)
		# (position, ts_var_heap) = getPositionOfExpr expr ts.ts_var_heap
		  ({tst_args = [argtype:_], tst_result, tst_attr_env}, ts) = standardTupleSelectorType position tuple_symbol arg_nr ti { ts & ts_var_heap = ts_var_heap }
		  (e_type, opt_expr_ptr, (reqs, ts)) = requirements ti expr ({ reqs & req_attr_coercions = tst_attr_env ++ req_attr_coercions }, ts)
		  req_type_coercions = [{ tc_demanded = argtype, tc_offered = e_type, tc_position = position, tc_coercible = True } : reqs.req_type_coercions ]
		  ts_expr_heap = storeAttribute opt_expr_ptr argtype.at_attribute ts.ts_expr_heap
		= (tst_result, No, ({ reqs & req_type_coercions = req_type_coercions }, { ts & ts_expr_heap = ts_expr_heap }))
	
	
	requirements _ (BasicExpr basic_val basic_type) (reqs, ts)
		# (type, ts) = attributedBasicType basic_type ts
	 	= (type, No, (reqs, ts))


	requirements ti (MatchExpr opt_tuple_type {glob_object={ds_arity, ds_index},glob_module} expr) (reqs, ts)
		# ({tst_result,tst_args,tst_attr_env}, ts) = standardLhsConstructorType ds_index glob_module ds_arity ti ts	
		  (e_type, opt_expr_ptr, (reqs, ts)) = requirements ti expr (reqs, ts)
		  reqs = { reqs & req_attr_coercions =  tst_attr_env ++ reqs.req_attr_coercions,
		  				  req_type_coercions = [{ tc_demanded = tst_result, tc_offered = e_type, tc_position = CP_Expression expr, tc_coercible = True } : reqs.req_type_coercions ] }
		  ts = { ts & ts_expr_heap = storeAttribute opt_expr_ptr tst_result.at_attribute ts.ts_expr_heap }
		= case opt_tuple_type of
			Yes {glob_object={ds_ident,ds_index,ds_arity}, glob_module}
				# tuple_type = MakeTypeSymbIdent { glob_object = ds_index, glob_module = glob_module } ds_ident ds_arity
				-> ({ at_type = TA tuple_type tst_args, at_attribute = TA_Unique, at_annotation = AN_None }, No, (reqs, ts))
			No
				-> ( hd tst_args, No, (reqs, ts))
		
	requirements _ (AnyCodeExpr _ _ _) (reqs, ts)
		# (fresh_v, ts) = freshAttributedVariable ts
		= (fresh_v, No, (reqs, ts))
	requirements _ (ABCCodeExpr _ _) (reqs, ts)
		# (fresh_v, ts) = freshAttributedVariable ts
		= (fresh_v, No, (reqs, ts))
	
	requirements _ expr reqs_ts
		= (abort ("Error in requirements\n" ---> expr), No, reqs_ts)


requirementsOfSelectors ti opt_expr expr [selector] tc_coercible sel_expr_type sel_expr reqs_ts 
	= requirementsOfSelector ti opt_expr expr selector tc_coercible sel_expr_type sel_expr reqs_ts
requirementsOfSelectors ti opt_expr expr [selector : selectors] tc_coercible sel_expr_type sel_expr reqs_ts 
	# (has_array_selection, result_type, reqs_ts) = requirementsOfSelector ti No expr selector tc_coercible sel_expr_type sel_expr reqs_ts
	# (have_array_selection, result_type, reqs_ts) = requirementsOfSelectors ti opt_expr expr selectors tc_coercible result_type sel_expr reqs_ts 
	= (has_array_selection || have_array_selection, result_type, reqs_ts)

requirementsOfSelector ti _ expr (RecordSelection field _) tc_coercible sel_expr_type sel_expr (reqs, ts )
	# ({tst_args, tst_result, tst_attr_env}, ts) = standardFieldSelectorType (CP_Expression sel_expr) field ti ts
	  req_type_coercions = [{ tc_demanded = hd tst_args, tc_offered = sel_expr_type, tc_position = CP_Expression sel_expr, tc_coercible = tc_coercible } : 
	  			reqs.req_type_coercions ]
	= (False, tst_result, ({ reqs & req_type_coercions = req_type_coercions }, ts))
requirementsOfSelector ti opt_expr expr (ArraySelection {glob_object = {ds_ident,ds_index,ds_arity},glob_module} expr_ptr index_expr) tc_coercible sel_expr_type sel_expr (reqs, ts) 
	# {me_type} = ti.ti_common_defs.[glob_module].com_member_defs.[ds_index]
	  ({tst_attr_env,tst_args,tst_result,tst_context}, ts) = freshSymbolType (Yes (CP_Expression expr)) cWithFreshContextVars me_type ti.ti_common_defs ts
	  (dem_array_type, dem_index_type, rest_type) = array_and_index_type tst_args
	  reqs ={ reqs & req_attr_coercions = tst_attr_env ++ reqs.req_attr_coercions}
	  (index_type, opt_expr_ptr, (reqs, ts)) = requirements ti index_expr (reqs, ts)
	  ts_expr_heap = storeAttribute opt_expr_ptr dem_index_type.at_attribute ts.ts_expr_heap
      reqs = { reqs & req_type_coercions = [{ tc_demanded = dem_index_type, tc_offered = index_type, tc_position = CP_Expression expr, tc_coercible = True },
      			{ tc_demanded = dem_array_type, tc_offered = sel_expr_type, tc_position = CP_Expression sel_expr, tc_coercible = tc_coercible } : reqs.req_type_coercions ]}
	  (reqs, ts) = requirements_of_update ti opt_expr rest_type (reqs, { ts & ts_expr_heap = ts_expr_heap })
	| isEmpty tst_context
		= (True, tst_result, (reqs, ts))
		= (True, tst_result, ({ reqs & req_overloaded_calls = [expr_ptr : reqs.req_overloaded_calls ]}, { ts & ts_expr_heap =
				ts.ts_expr_heap <:= (expr_ptr, EI_Overloaded { oc_symbol = 
					{ symb_name = ds_ident, symb_kind = SK_OverloadedFunction {glob_module = glob_module, glob_object = ds_index}, symb_arity = ds_arity },
						oc_context = tst_context, oc_specials = [] })}))
where
	array_and_index_type [array_type, index_type : rest_type ]
		= (array_type, index_type, rest_type)

	requirements_of_update ti No _ reqs_ts
		= reqs_ts
	requirements_of_update ti (Yes elem_expr) [ elem_type : _ ] reqs_ts
		# (elem_expr_type, opt_elem_expr_ptr, (reqs, ts)) = requirements ti elem_expr reqs_ts
		  ts = { ts & ts_expr_heap = storeAttribute opt_elem_expr_ptr elem_type.at_attribute ts.ts_expr_heap }
	      reqs = { reqs & req_type_coercions = [{ tc_demanded = elem_type, tc_offered = elem_expr_type,
						tc_position = CP_Expression elem_expr, tc_coercible = True } : reqs.req_type_coercions ]}
		= (reqs, ts)

possibly_accumulate_reqs_in_new_group position state_transition reqs_ts
	:== possibly_accumulate_reqs position reqs_ts
  where
	possibly_accumulate_reqs NoPos reqs_ts
		= state_transition reqs_ts
	possibly_accumulate_reqs position (reqs=:{req_type_coercions=old_req_type_coercions}, ts)
		# reqs_with_empty_accu
				= { reqs & req_type_coercions = [] }
		  (reqs_with_new_group_in_accu, ts)
		  		= state_transition (reqs_with_empty_accu, ts)
		  new_group 
		  		= { tcg_type_coercions = reqs_with_new_group_in_accu.req_type_coercions,
		  			tcg_position = position }
		  reqs_with_new_group
		  		= { reqs_with_new_group_in_accu & 
		  				req_type_coercion_groups = [new_group:reqs_with_new_group_in_accu.req_type_coercion_groups],
			  			req_type_coercions = old_req_type_coercions }
		= (reqs_with_new_group, ts)

makeBase _ _ [] [] ts_var_heap
	= ts_var_heap
makeBase fun_or_cons_ident arg_nr [{fv_name, fv_info_ptr} : vars] [type : types] ts_var_heap
	| is_rare_name fv_name
		= makeBase fun_or_cons_ident (arg_nr+1) vars types (addToBase fv_info_ptr type (Yes (CP_FunArg fun_or_cons_ident arg_nr)) ts_var_heap)
		= makeBase fun_or_cons_ident (arg_nr+1) vars types (addToBase fv_info_ptr type No ts_var_heap)

addToBase info_ptr atype=:{at_type = TFA atvs type} optional_position ts_var_heap 
	= ts_var_heap  <:= (info_ptr, VI_FAType atvs { atype & at_type = type} optional_position)
addToBase info_ptr type optional_position ts_var_heap
	= ts_var_heap  <:= (info_ptr, VI_Type type optional_position)
	
attributedBasicType (BT_String string_type) ts=:{ts_attr_store}
	= ({ at_annotation = AN_None, at_attribute = TA_TempVar ts_attr_store, at_type = string_type}, {ts & ts_attr_store = inc ts_attr_store})
attributedBasicType bas_type ts=:{ts_attr_store}
	= ({ at_annotation = AN_None, at_attribute = TA_TempVar ts_attr_store, at_type = TB bas_type}, {ts & ts_attr_store = inc ts_attr_store})

unify_coercions [{tc_demanded,tc_offered,tc_position}:coercions] modules subst heaps err
	# (succ, subst, heaps) = unify tc_demanded tc_offered modules subst heaps
	| succ
		= unify_coercions coercions modules subst heaps err
		# (_, subst_demanded, subst)	= arraySubst tc_demanded subst
		  (_, subst_offered, subst)		= arraySubst tc_offered subst
		= (subst, heaps, cannotUnify subst_demanded subst_offered tc_position err)
//			---> ("unify_coercions", subst_demanded, subst_offered)
unify_coercions [] modules subst heaps err
	= (subst, heaps, err)

InitFunEnv :: !Int -> *{! FunctionType}
InitFunEnv nr_of_fun_defs
	= createArray nr_of_fun_defs EmptyFunctionType

CreateInitialSymbolTypes start_index common_defs [] defs_and_state
	= defs_and_state
CreateInitialSymbolTypes start_index common_defs [fun : funs] (fun_defs, pre_def_symbols, ts)
	# (fd, fun_defs) = fun_defs![fun]
	  (pre_def_symbols, ts) = initial_symbol_type (start_index == fun) common_defs fd (pre_def_symbols, ts)
	= CreateInitialSymbolTypes start_index common_defs funs (fun_defs, pre_def_symbols, ts)
where
	initial_symbol_type is_start_rule common_defs 
				{fun_symb, fun_type = Yes ft=:{st_arity,st_args,st_result,st_attr_vars,st_attr_env},fun_lifted,
				 fun_info = {fi_dynamics}, fun_pos }
				(pre_def_symbols, ts=:{ts_type_heaps,ts_expr_heap,ts_td_infos,ts_error})
		# fe_location = newPosition fun_symb fun_pos
		  ts_error = setErrorAdmin fe_location ts_error
		  (st_args, ps) = addPropagationAttributesToATypes common_defs st_args
				{ prop_type_heaps = ts_type_heaps, prop_td_infos = ts_td_infos,
				  prop_attr_vars = st_attr_vars, prop_attr_env = st_attr_env, prop_error = Yes ts_error}
		  (st_result, _, {prop_type_heaps,prop_td_infos,prop_attr_vars,prop_error = Yes ts_error,prop_attr_env})
		  		= addPropagationAttributesToAType common_defs st_result ps
		  ft_with_prop = { ft & st_args = st_args, st_result = st_result, st_attr_vars = prop_attr_vars, st_attr_env = prop_attr_env }
		  (th_vars, ts_expr_heap) = clear_dynamics fi_dynamics (prop_type_heaps.th_vars, ts.ts_expr_heap)
		  (fresh_fun_type, ts) = freshSymbolType No cWithoutFreshContextVars ft_with_prop common_defs { ts & ts_type_heaps = { prop_type_heaps & th_vars = th_vars }, ts_expr_heap = ts_expr_heap,
		  		 ts_td_infos = prop_td_infos, ts_error = ts_error }
		  (lifted_args, ts) = fresh_non_unique_type_variables fun_lifted [] ts
		  (ts_var_store, ts_type_heaps, ts_var_heap, ts_expr_heap, pre_def_symbols)
		  		= fresh_dynamics fi_dynamics (ts.ts_var_store, ts.ts_type_heaps, ts.ts_var_heap, ts.ts_expr_heap, pre_def_symbols)
		= (pre_def_symbols,
				{ ts & ts_fun_env = { ts.ts_fun_env & [fun] = SpecifiedType ft_with_prop lifted_args
					{ fresh_fun_type & tst_arity = st_arity + fun_lifted, tst_args = lifted_args ++ fresh_fun_type.tst_args, tst_lifted = fun_lifted }},
						ts_var_heap = ts_var_heap, ts_var_store = ts_var_store, ts_expr_heap = ts_expr_heap, ts_type_heaps = ts_type_heaps })
	initial_symbol_type is_start_rule common_defs {fun_arity, fun_lifted, fun_info = {fi_dynamics}} (pre_def_symbols, ts)
		# (st_gen, ts) = create_general_symboltype is_start_rule fun_arity fun_lifted ts
		  ts_type_heaps = ts.ts_type_heaps 
		  (th_vars, ts_expr_heap) = clear_dynamics fi_dynamics (ts_type_heaps.th_vars, ts.ts_expr_heap)
		  (ts_var_store, ts_type_heaps, ts_var_heap, ts_expr_heap, pre_def_symbols)
		  		= fresh_dynamics fi_dynamics (ts.ts_var_store, { ts_type_heaps & th_vars = th_vars },
		  				ts.ts_var_heap, ts_expr_heap, pre_def_symbols)
		= (pre_def_symbols, { ts & ts_fun_env = { ts.ts_fun_env & [fun] = UncheckedType st_gen }, ts_var_store = ts_var_store,
					ts_expr_heap = ts_expr_heap, ts_type_heaps = ts_type_heaps, ts_var_heap = ts_var_heap})


	create_general_symboltype :: !Bool !Int !Int !*TypeState -> (!TempSymbolType, !*TypeState)
	create_general_symboltype is_start_rule nr_of_args nr_of_lifted_args ts
		| is_start_rule && nr_of_args > 0
			# (tst_args, ts) = fresh_attributed_type_variables (nr_of_args - 1) [{at_attribute = TA_Unique, at_annotation = AN_Strict, at_type = TB BT_World }] ts
			  (tst_result, ts) = freshAttributedVariable ts
			= ({ tst_args = tst_args, tst_arity = 1, tst_result = tst_result, tst_context = [], tst_attr_env = [], tst_lifted = 0 }, ts)
			# (tst_args, ts) = fresh_attributed_type_variables nr_of_args [] ts
			  (tst_args, ts) = fresh_attributed_type_variables nr_of_lifted_args tst_args ts
			  (tst_result, ts) = freshAttributedVariable ts
			= ({ tst_args = tst_args, tst_arity = nr_of_args + nr_of_lifted_args, tst_result = tst_result, tst_context = [], tst_attr_env = [], tst_lifted = 0 }, ts)

	fresh_attributed_type_variables :: !Int ![AType] !*TypeState -> (![AType], !*TypeState)
	fresh_attributed_type_variables n vars ts
		| n == 0
			= (vars, ts)
			# (var, ts) = freshAttributedVariable ts
			= fresh_attributed_type_variables (dec n) [var : vars] ts

	fresh_non_unique_type_variables :: !Int ![AType] !*TypeState -> (![AType], !*TypeState)
	fresh_non_unique_type_variables n vars ts
		| n == 0
			= (vars, ts)
			# (var, ts) = freshNonUniqueVariable ts
			= fresh_non_unique_type_variables (dec n) [var : vars] ts

	fresh_dynamics dyn_ptrs state
		= foldSt fresh_dynamic dyn_ptrs state

	fresh_dynamic dyn_ptr (var_store, type_heaps, var_heap, expr_heap, predef_symbols)
		# (dyn_info, expr_heap) = readPtr dyn_ptr expr_heap
		= case dyn_info of
			EI_Dynamic opt_dyn_type=:(Yes {dt_uni_vars,dt_type,dt_global_vars}) _
				# (th_vars, var_store)		= fresh_existential_attributed_variables dt_uni_vars (type_heaps.th_vars, var_store)
				  (th_vars, var_store)		= fresh_type_variables dt_global_vars (th_vars, var_store)
				  (tdt_type, type_heaps)	= freshCopy dt_type { type_heaps & th_vars = th_vars }
				  (contexts, expr_ptr, type_code_symbol, (var_heap, expr_heap, type_var_heap, predef_symbols))
				  		= determine_context_and_expr_ptr dt_global_vars (var_heap, expr_heap, type_heaps.th_vars, predef_symbols)
				-> (var_store, { type_heaps & th_vars = type_var_heap }, var_heap,
						expr_heap <:= (dyn_ptr, EI_TempDynamicType opt_dyn_type tdt_type contexts expr_ptr type_code_symbol), predef_symbols)
			EI_Dynamic No _ 
				# fresh_var = TempV var_store
				  tdt_type = { at_attribute = TA_Multi, at_annotation = AN_None, at_type = fresh_var }

				# ({pds_ident,pds_module,pds_def},predef_symbols) = predef_symbols![PD_TypeCodeClass]
		  		  tc_class_symb = {glob_module = pds_module, glob_object = {ds_ident = pds_ident, ds_arity = 1, ds_index = pds_def }}
 				  (pds, predef_symbols) = predef_symbols![PD_TypeCodeMember]
		  		  ({pds_ident,pds_module,pds_def},predef_symbols) = predef_symbols![PD_TypeCodeMember]
				  tc_member_symb = { symb_name = pds_ident, symb_kind = SK_OverloadedFunction {glob_module = pds_module, glob_object = pds_def }, symb_arity = 0}
		 		  (new_var_ptr, var_heap) = newPtr VI_Empty var_heap
				  context = {tc_class = tc_class_symb, tc_types = [fresh_var], tc_var = new_var_ptr}
		  		  (expr_ptr, expr_heap) = newPtr EI_Empty expr_heap //---> ("^EI_Dynamic No=" +++ toString var_store)
				-> (inc var_store, type_heaps, var_heap,
						expr_heap <:= (dyn_ptr, EI_TempDynamicType No tdt_type [context] expr_ptr tc_member_symb), predef_symbols)
			EI_DynamicTypeWithVars loc_type_vars dt=:{dt_uni_vars,dt_type,dt_global_vars} loc_dynamics
				# (fresh_vars, (th_vars, var_store)) = fresh_existential_variables loc_type_vars (type_heaps.th_vars, var_store)
//					---> ("fresh_dynamic (EI_DynamicTypeWithVars)", dt_uni_vars)
				  (th_vars, var_store) = fresh_type_variables dt_global_vars (th_vars, var_store)
				  (tdt_type, type_heaps) = freshCopy (add_universal_vars_to_type dt_uni_vars dt_type) { type_heaps & th_vars = th_vars }
				  (contexts, expr_ptr, type_code_symbol, (var_heap, expr_heap, type_var_heap, predef_symbols))
				  		= determine_context_and_expr_ptr dt_global_vars (var_heap, expr_heap, type_heaps.th_vars, predef_symbols)
				-> fresh_local_dynamics loc_dynamics (var_store, { type_heaps & th_vars = type_var_heap }, var_heap,
						expr_heap <:= (dyn_ptr, EI_TempDynamicPattern loc_type_vars dt loc_dynamics fresh_vars tdt_type contexts expr_ptr type_code_symbol), predef_symbols)

	fresh_local_dynamics loc_dynamics state
		= foldSt fresh_dynamic loc_dynamics state

	clear_dynamics dyn_ptrs heaps
		= foldSt clear_dynamic dyn_ptrs heaps
		
	clear_dynamic dyn_ptr (var_heap, expr_heap)
		# (dyn_info, expr_heap) = readPtr dyn_ptr expr_heap
		= case dyn_info of
			EI_Dynamic (Yes {dt_global_vars}) _
				-> (clear_type_vars dt_global_vars var_heap, expr_heap)
			EI_Dynamic No _
				-> (var_heap, expr_heap)
			EI_DynamicTypeWithVars loc_type_vars {dt_global_vars} loc_dynamics
				-> clear_local_dynamics loc_dynamics (clear_type_vars dt_global_vars var_heap, expr_heap)

	clear_local_dynamics loc_dynamics state
		= foldSt clear_dynamic loc_dynamics state
		
	clear_type_vars type_vars var_heap
		= foldSt (\{tv_info_ptr} -> writePtr tv_info_ptr TVI_Empty) type_vars var_heap 
		
	fresh_existential_attributed_variables type_variables state
		= foldSt (\{atv_variable={tv_info_ptr}} (var_heap, var_store) -> (var_heap <:= (tv_info_ptr, TVI_Type (TempQV var_store)), inc var_store))
							type_variables state 
	fresh_existential_variables type_variables state
		= mapSt (\{tv_info_ptr} (var_heap, var_store) -> (var_store, (var_heap <:= (tv_info_ptr, TVI_Type (TempQV var_store)), inc var_store)))
							type_variables state 
	fresh_type_variables type_variables state
		= foldSt fresh_type_variable type_variables state 

	fresh_type_variable {tv_info_ptr} (var_heap, var_store)
		# (var_info, var_heap) = readPtr tv_info_ptr var_heap
		= case var_info of
			TVI_Empty
				-> (var_heap <:= (tv_info_ptr, TVI_Type (TempV var_store)), inc var_store)
			_
				-> (var_heap, var_store)
	
	determine_context_and_expr_ptr global_vars (var_heap, expr_heap, type_var_heap, predef_symbols)
		# ({pds_ident,pds_module,pds_def},predef_symbols) = predef_symbols![PD_TypeCodeClass]
		  tc_class_symb = {glob_module = pds_module, glob_object = {ds_ident = pds_ident, ds_arity = 1, ds_index = pds_def }}
		  ({pds_ident,pds_module,pds_def},predef_symbols) = predef_symbols![PD_TypeCodeMember]
		  tc_member_symb = { symb_name	= pds_ident, symb_kind = SK_TypeCode, symb_arity = 0}
		  (contexts, (var_heap, type_var_heap)) = mapSt (build_type_context tc_class_symb) global_vars (var_heap, type_var_heap)
		  (expr_ptr, expr_heap) = newPtr EI_Empty expr_heap
		= (contexts, expr_ptr, tc_member_symb, (var_heap, expr_heap, type_var_heap, predef_symbols))

	build_type_context tc_class_symb {tv_info_ptr} (var_heap, type_var_heap)
		# (TVI_Type fresh_var, type_var_heap) = readPtr tv_info_ptr type_var_heap
		  (new_var_ptr, var_heap) = newPtr VI_Empty var_heap
		= ({tc_class = tc_class_symb, tc_types = [fresh_var], tc_var = new_var_ptr}, (var_heap, type_var_heap))

	add_universal_vars_to_type [] at
		= at
	add_universal_vars_to_type uni_vars at=:{at_type}
		= { at & at_type = TFA uni_vars at_type }

specification_error type type1 err
	# err = errorHeading "Type error" err
	  format = { form_properties = cAttributed, form_attr_position = No}
	= { err & ea_file = err.ea_file <<< " specified type " 	 
									<:: (format, type1, Yes initialTypeVarBeautifulizer) 
									<<< " conflicts with derived type "
									<:: (format, type, Yes initialTypeVarBeautifulizer) 
									<<< '\n' }


cleanUpAndCheckFunctionTypes [] _ _ start_index _ defs type_contexts coercion_env attr_partition type_var_env attr_var_env (fun_defs, ts)
	= (fun_defs, ts)
cleanUpAndCheckFunctionTypes [fun : funs] [ {fe_requirements = {req_case_and_let_exprs}} : reqs] dict_types start_index list_inferred_types defs type_contexts coercion_env
				attr_partition type_var_env attr_var_env (fun_defs, ts)
	# (fd, fun_defs) = fun_defs![fun]
	  dict_ptrs = get_dict_ptrs fun dict_types
	  (type_var_env, attr_var_env, ts) = clean_up_and_check_function_type fd fun (start_index == fun) list_inferred_types defs type_contexts
													(dict_ptrs ++ req_case_and_let_exprs) coercion_env attr_partition type_var_env attr_var_env ts
	= cleanUpAndCheckFunctionTypes funs reqs dict_types start_index list_inferred_types defs type_contexts coercion_env attr_partition type_var_env attr_var_env (fun_defs, ts)
where
	get_dict_ptrs fun_index []
		= []
	get_dict_ptrs fun_index [(index, ptrs) : dict_types]
		| fun_index == index
			= ptrs
			= get_dict_ptrs fun_index dict_types
		
	clean_up_and_check_function_type {fun_symb,fun_pos,fun_type = opt_fun_type} fun is_start_rule list_inferred_types defs type_contexts type_ptrs
					coercion_env attr_partition type_var_env attr_var_env ts
		# (env_type, ts) = ts!ts_fun_env.[fun]
		# ts = { ts & ts_error = setErrorAdmin (newPosition fun_symb fun_pos) ts.ts_error}
		= case env_type of
			ExpandedType fun_type tmp_fun_type exp_fun_type
				# (clean_fun_type, type_var_env, attr_var_env, ts_type_heaps, ts_var_heap, ts_expr_heap, ts_error)
					= cleanUpSymbolType is_start_rule cSpecifiedType exp_fun_type type_contexts type_ptrs coercion_env 
										attr_partition type_var_env attr_var_env ts.ts_type_heaps ts.ts_var_heap ts.ts_expr_heap ts.ts_error
				| ts_error.ea_ok
					# (ts_fun_env, attr_var_env, ts_type_heaps, ts_expr_heap, ts_error)
			  			= check_function_type fun_type tmp_fun_type clean_fun_type type_ptrs defs ts.ts_fun_env attr_var_env ts_type_heaps ts_expr_heap ts_error
					-> (type_var_env, attr_var_env, { ts & ts_type_heaps = ts_type_heaps, ts_var_heap = ts_var_heap, ts_expr_heap = ts_expr_heap, ts_fun_env = ts_fun_env, ts_error = ts_error })
					-> (type_var_env, attr_var_env, { ts & ts_type_heaps = ts_type_heaps, ts_var_heap = ts_var_heap, ts_expr_heap = ts_expr_heap, ts_error = ts_error })
		  	UncheckedType exp_fun_type
				# (clean_fun_type, type_var_env, attr_var_env, ts_type_heaps, ts_var_heap, ts_expr_heap, ts_error)
					= cleanUpSymbolType is_start_rule cDerivedType exp_fun_type type_contexts type_ptrs coercion_env
										attr_partition type_var_env attr_var_env ts.ts_type_heaps ts.ts_var_heap ts.ts_expr_heap ts.ts_error
				  ts_out = ts.ts_out
				  th_attrs = ts_type_heaps.th_attrs
				  (ts_out, th_attrs)
				  		= case list_inferred_types of
				  			No
				  				-> (ts_out, th_attrs)
				  			Yes show_attributes
								# form = { form_properties = if show_attributes cAttributed cNoProperties, form_attr_position = No }
//								  ts_out = ts_out <<< show_attributes <<< "\n"
				  				  (printable_type, th_attrs)
				  				  		= case show_attributes of
				  				  			True
				  				  				-> beautifulizeAttributes clean_fun_type th_attrs
				  				  			_
				  				  				-> (clean_fun_type, th_attrs)	
				  				-> (ts_out <<< fun_symb <<< " :: " 
				  						<:: (form, printable_type, Yes initialTypeVarBeautifulizer) <<< '\n', th_attrs)
				  ts_fun_env = { ts.ts_fun_env & [fun] = CheckedType clean_fun_type }
				-> (type_var_env, attr_var_env, { ts & ts_type_heaps = { ts_type_heaps & th_attrs = th_attrs }, ts_var_heap = ts_var_heap, ts_expr_heap = ts_expr_heap, ts_fun_env = ts_fun_env, ts_error = ts_error, ts_out = ts_out })

	check_function_type fun_type tmp_fun_type=:{tst_lifted} clean_fun_type=:{st_arity, st_args, st_vars, st_attr_vars, st_context} type_ptrs
						defs fun_env attr_var_env type_heaps expr_heap error
		# (equi, attr_var_env, type_heaps) = equivalent clean_fun_type tmp_fun_type (length fun_type.st_context) defs attr_var_env type_heaps
		| equi
			# type_with_lifted_arg_types = addLiftedArgumentsToSymbolType fun_type tst_lifted st_args st_vars st_attr_vars st_context
			  (type_heaps, expr_heap) = updateExpressionTypes clean_fun_type type_with_lifted_arg_types type_ptrs type_heaps expr_heap
			= ({ fun_env & [fun] = CheckedType type_with_lifted_arg_types}, attr_var_env, type_heaps, expr_heap, error)
					// ---> ("check_function_type", clean_fun_type, fun_type, type_with_lifted_arg_types)
			# (printable_type, th_attrs) = beautifulizeAttributes clean_fun_type type_heaps.th_attrs
			# (printable_type1, th_attrs) = beautifulizeAttributes fun_type th_attrs
			
			= (fun_env, attr_var_env, { type_heaps & th_attrs = th_attrs }, expr_heap, specification_error printable_type printable_type1 error)
	where
		add_lifted_arg_types arity_diff args1 args2
			| arity_diff > 0
				= take arity_diff args2 ++ args1
				= args1

addLiftedArgumentsToSymbolType st=:{st_arity,st_args,st_vars,st_attr_vars,st_context} nr_of_lifted_arguments new_args new_vars new_attrs new_context
	= { st & st_args = take nr_of_lifted_arguments new_args ++ st_args, st_vars = st_vars ++ drop (length st_vars) new_vars,
			st_attr_vars = (take (length new_attrs - length st_attr_vars) new_attrs) ++ st_attr_vars, st_arity = st_arity + nr_of_lifted_arguments,
				st_context = take (length new_context - length st_context) new_context ++ st_context }

::	FunctionRequirements =
	{	fe_requirements	:: !Requirements
	,	fe_context		:: !Optional [TypeContext]
	,	fe_index		:: !Index
	,	fe_location		:: !IdentPos
	}
/*
ste_kind_to_string s
	= case s of
		(STE_FunctionOrMacro _)
			-> "STE_FunctionOrMacro"
		STE_Type
			-> "STE_Type"	
		STE_Constructor
			-> "STE_Constructor"
		(STE_Selector _)
			-> "STE_Selector"
		STE_Class
			-> "STE_Class"
		(STE_Field _)
			-> "STE_Field"
		STE_Member
			-> "STE_Member"
		(STE_Instance _)
			-> "STE_Instance"
		(STE_Variable _) 
			-> "STE_Variable"
		(STE_TypeVariable _) 
			-> "STE_TypeVariable"
		(STE_TypeAttribute _)
			-> "STE_TypeAttribute"
		(STE_BoundTypeVariable _)
			-> "STE_BoundTypeVariable"
		(STE_Imported a b)
			-> "STE_Imported "+++ ste_kind_to_string a
		STE_DclFunction
			-> "STE_DclFunction"
		(STE_Module _)
			-> "STE_Module"	
		STE_ClosedModule
			-> "STE_ClosedModule"
		STE_Empty 
			-> "STE_Empty"	
		_ 
			-> "STE_???"
*/

typeProgram ::!{! Group} !Int !*{# FunDef} !IndexRange  !(Optional Bool) !CommonDefs ![Declaration] !{# DclModule} !NumberSet !*TypeDefInfos !*Heaps !*PredefinedSymbols !*File !*File !{# DclModule} 
	-> (!Bool, !*{# FunDef}, !ArrayAndListInstances, {! GlobalTCType}, !{# CommonDefs}, !{# {# FunType} }, !*TypeDefInfos, !*Heaps, !*PredefinedSymbols, !*File, !*File)
typeProgram comps main_dcl_module_n fun_defs specials list_inferred_types icl_defs imports modules used_module_numbers td_infos heaps=:{hp_var_heap, hp_expression_heap, hp_type_heaps} predef_symbols file out dcl_modules

	#! fun_env_size = size fun_defs

	# ts_error = {ea_file = file, ea_loc = [], ea_ok = True }
	  ti_common_defs = {{dcl_common \\ {dcl_common} <-: modules } & [main_dcl_module_n] = icl_defs }
	  ti_functions	 = {dcl_functions \\ {dcl_functions} <-: modules }	  

	  type_def_sizes =  [ size com_type_defs \\ {com_type_defs} <-: ti_common_defs ]
      class_def_sizes = [ size com_class_defs \\ {com_class_defs} <-: ti_common_defs ]
      class_instances = { {  IT_Empty \\ i <- [0 .. dec size] } \\ size <- class_def_sizes }
	  state = collect_imported_instances imports ti_common_defs {} ts_error class_instances hp_type_heaps.th_vars td_infos 
	  (_, ts_error, class_instances, th_vars, td_infos) = collect_and_check_instances (size icl_defs.com_instance_defs) ti_common_defs state
	  
	  ts = { ts_fun_env = InitFunEnv fun_env_size, ts_var_heap = hp_var_heap, ts_expr_heap = hp_expression_heap, ts_var_store = 0, ts_attr_store = FirstAttrVar, ts_cons_variables = [], ts_exis_variables = [],
	  		 ts_type_heaps = { hp_type_heaps & th_vars = th_vars }, ts_td_infos = td_infos, ts_error = ts_error, ts_out = out }
	  ti = { ti_common_defs = ti_common_defs, ti_functions = ti_functions,ti_main_dcl_module_n=main_dcl_module_n }
	  special_instances = { si_next_array_member_index = fun_env_size, si_array_instances = [], si_list_instances = [], si_tail_strict_list_instances = [], si_next_TC_member_index = 0, si_TC_instances = [] }
	# (type_error, fun_defs, predef_symbols, special_instances, ts) = type_components list_inferred_types 0 comps class_instances ti (False, fun_defs, predef_symbols, special_instances, ts)
	  (fun_defs,ts_fun_env) = update_function_types 0 comps ts.ts_fun_env fun_defs
	  (type_error, fun_defs, predef_symbols, special_instances, {ts_td_infos,ts_fun_env,ts_error,ts_var_heap, ts_expr_heap, ts_type_heaps, ts_out})
			= type_instances list_inferred_types specials.ir_from specials.ir_to class_instances ti (type_error, fun_defs, predef_symbols, special_instances,
							{ ts & ts_fun_env = ts_fun_env })
	  (array_first_instance_indices,list_first_instance_indices,tail_strict_list_first_instance_indices,fun_defs,type_code_instances,predef_symbols,ts_type_heaps,ts_error)
	  		= create_special_instances special_instances fun_env_size ti_common_defs fun_defs predef_symbols ts_type_heaps ts_error
	  array_and_list_instances = {
		  	ali_array_first_instance_indices=array_first_instance_indices,
			ali_list_first_instance_indices=list_first_instance_indices,
			ali_tail_strict_list_first_instance_indices=tail_strict_list_first_instance_indices,
			ali_instances_range={ ir_from = fun_env_size, ir_to = special_instances.si_next_array_member_index }
		}
	= (not type_error, fun_defs, array_and_list_instances, type_code_instances, ti_common_defs, ti_functions,
			ts_td_infos, {hp_var_heap = ts_var_heap, hp_expression_heap = ts_expr_heap, hp_type_heaps = ts_type_heaps },
			predef_symbols, ts_error.ea_file, ts_out)
//				---> ("typeProgram", array_inst_types)
where
	collect_imported_instances imports common_defs dummy error class_instances type_var_heap td_infos
		= foldSt (collect_imported_instance common_defs) imports (dummy, error, class_instances, type_var_heap, td_infos)

	collect_imported_instance common_defs (Declaration {decl_kind = STE_Imported (STE_Instance _) mod_index, decl_index }) state
		= update_instances_of_class common_defs mod_index decl_index state
	collect_imported_instance common_defs _ state
		= state

	collect_and_check_instances nr_of_instances common_defs state
		= iFoldSt (update_instances_of_class common_defs main_dcl_module_n) 0 nr_of_instances state

	update_instances_of_class common_defs mod_index ins_index (dummy, error, class_instances, type_var_heap, td_infos)
		#!{ins_class={glob_object={ds_ident={id_name}, ds_index},glob_module},ins_type={it_types},ins_pos} = common_defs.[mod_index].com_instance_defs.[ins_index]
		  (mod_instances, class_instances) = replace class_instances glob_module dummy 
		  (instances, mod_instances) = replace mod_instances ds_index IT_Empty
		  (error, instances) = insert it_types ins_index mod_index common_defs error instances
		  (_, mod_instances) = replace mod_instances ds_index instances
		  (dummy, class_instances) = replace class_instances glob_module mod_instances
		  (error, type_var_heap, td_infos)
					= check_types_of_instances ins_pos common_defs glob_module ds_index it_types (error, type_var_heap, td_infos)
		= (dummy, error, class_instances, type_var_heap, td_infos)

	check_types_of_instances ins_pos common_defs class_module class_index types state
		# {class_arity,class_cons_vars} = common_defs.[class_module].com_class_defs.[class_index]
		= check_instances_of_constructor_variables ins_pos common_defs class_cons_vars (dec class_arity) types state
	where
		check_instances_of_constructor_variables ins_pos common_defs cons_vars arg_nr [type : types] state
			| cons_vars bitand (1 << arg_nr) <> 0
				# state = check_type_of_constructor_variable ins_pos common_defs type state
				= check_instances_of_constructor_variables ins_pos common_defs cons_vars (dec arg_nr) types state
				= check_instances_of_constructor_variables ins_pos common_defs cons_vars (dec arg_nr) types state
		check_instances_of_constructor_variables ins_pos common_defs cons_vars arg_nr [] state
			= state

		check_type_of_constructor_variable ins_pos common_defs type=:(TA {type_index={glob_module,glob_object},type_arity} types) (error, type_var_heap, td_infos)
			# {td_arity,td_name} = common_defs.[glob_module].com_type_defs.[glob_object]
			  ({tdi_properties,tdi_cons_vars}, td_infos) = td_infos![glob_module].[glob_object]
			| tdi_properties bitand cIsNonCoercible == 0
				# ({sc_neg_vect}, type_var_heap, td_infos)
					= signClassification glob_object glob_module [TopSignClass \\ cv <- tdi_cons_vars ] common_defs type_var_heap td_infos
				= (check_sign type (sc_neg_vect >> type_arity) (td_arity - type_arity) error, type_var_heap, td_infos)							
				= (checkErrorWithIdentPos (newPosition empty_id ins_pos)
					 " instance type should be coercible" error, type_var_heap, td_infos)
		where
			check_sign type neg_signs arg_nr error
				| arg_nr == 0
					= error
					| neg_signs bitand 1 == 0
						= check_sign type (neg_signs >> 1) (dec arg_nr) error
						= checkError type " all arguments of an instance type should have a non-negative sign" error
		check_type_of_constructor_variable ins_pos common_defs type=:(arg_type --> result_type) (error, type_var_heap, td_infos)
			= (checkErrorWithIdentPos (newPosition empty_id ins_pos) " instance type should be coercible" error,
				type_var_heap, td_infos)
//AA..
/*
		// ??? not sure if it is correct
		check_type_of_constructor_variable ins_pos common_defs TArrow (error, type_var_heap, td_infos)
			= (checkErrorWithIdentPos (newPosition empty_id ins_pos) " instance type should be coercible" error,
				type_var_heap, td_infos)		
		check_type_of_constructor_variable ins_pos common_defs type=:(TArrow1 arg_type) (error, type_var_heap, td_infos)
			= (checkErrorWithIdentPos (newPosition empty_id ins_pos) " instance type should be coercible" error,
				type_var_heap, td_infos)		
*/
//..AA				
		check_type_of_constructor_variable ins_pos common_defs type=:(cv :@: types) (error, type_var_heap, td_infos)
			= (checkError (newPosition empty_id ins_pos) " instance type should be coercible" error,
				type_var_heap, td_infos)
		check_type_of_constructor_variable ins_pos common_defs type state
			= state
			
	insert ::  ![Type] !Index !Index !{# CommonDefs } !*ErrorAdmin !*InstanceTree -> (!*ErrorAdmin, !*InstanceTree)
	insert ins_types new_ins_index new_ins_module modules error IT_Empty
		=  (error, IT_Node {glob_object = new_ins_index,glob_module = new_ins_module}  IT_Empty IT_Empty)
	insert ins_types new_ins_index new_ins_module modules error (IT_Node ins=:{glob_object,glob_module} it_less it_greater)
		#! {ins_type={it_types}} = modules.[glob_module].com_instance_defs.[glob_object]
		# cmp = ins_types =< it_types
		| cmp == Smaller
			# (error, it_less) = insert ins_types new_ins_index new_ins_module modules error it_less
			= (error, IT_Node ins it_less it_greater)
		| cmp == Greater
			# (error, it_greater) = insert ins_types new_ins_index new_ins_module modules error it_greater
			= (error, IT_Node ins it_less it_greater)
			= (checkError ins_types " instance is overlapping" error, IT_Node ins it_less it_greater)

	type_instances list_inferred_types ir_from ir_to class_instances ti funs_and_state
		| ir_from == ir_to
			= funs_and_state
			# funs_and_state = type_component list_inferred_types [ir_from] class_instances ti funs_and_state
			= type_instances list_inferred_types (inc ir_from) ir_to class_instances ti funs_and_state

	type_components list_inferred_types group_index comps class_instances ti funs_and_state
		| group_index == size comps
			= funs_and_state
			#! comp = comps.[group_index]	
			# funs_and_state = type_component list_inferred_types comp.group_members  class_instances ti funs_and_state
			= type_components list_inferred_types (inc group_index) comps class_instances ti funs_and_state

	show_component comp fun_defs
		= foldSt show_fun comp ([], fun_defs)
	where
		show_fun fun_index (names, fun_defs)
			# ({fun_symb}, fun_defs) = fun_defs![fun_index]
			= ([fun_symb : names], fun_defs)
	
	get_index_of_start_rule predef_symbols
		# ({pds_def, pds_module}, predef_symbols) = predef_symbols![PD_Start]
		| pds_def <> NoIndex && pds_module == main_dcl_module_n
			= (pds_def, predef_symbols)
			= (NoIndex, predef_symbols)
	
	type_component list_inferred_types comp class_instances ti=:{ti_common_defs} (type_error, fun_defs, predef_symbols, special_instances, ts)
		# (start_index, predef_symbols) = get_index_of_start_rule predef_symbols
//		# (functions, fun_defs) = show_component comp fun_defs
		# (fun_defs, predef_symbols, ts) = CreateInitialSymbolTypes start_index ti_common_defs comp (fun_defs, predef_symbols, ts)
		| not ts.ts_error.ea_ok  // ---> ("typing", functions)
			= (True, fun_defs, predef_symbols, special_instances, create_erroneous_function_types comp
					{ ts & ts_var_store = 0, ts_attr_store = FirstAttrVar, ts_cons_variables = [], ts_exis_variables = [],
								ts_error = { ts.ts_error & ea_ok = True } })
		# (fun_reqs, (fun_defs, ts)) = type_functions comp ti fun_defs ts
		#! nr_of_type_variables = ts.ts_var_store 
		# (subst, ts_type_heaps, ts_error)
		  		= unify_requirements_of_functions fun_reqs ti (createArray nr_of_type_variables TE) ts.ts_type_heaps ts.ts_error
		| not ts_error.ea_ok
			= (True, fun_defs, predef_symbols, special_instances, create_erroneous_function_types comp
				{ ts & ts_type_heaps = ts_type_heaps, ts_error = { ts_error & ea_ok = True },
					ts_var_store = 0, ts_attr_store = FirstAttrVar, ts_cons_variables = [], ts_exis_variables = []})
		# {ts_attr_store,ts_var_heap,ts_var_store,ts_expr_heap,ts_td_infos,ts_cons_variables,ts_exis_variables} = ts
		  (cons_var_vects, subst) = determine_cons_variables ts_cons_variables (createArray (inc (BITINDEX nr_of_type_variables)) 0, subst)
		  (subst, nr_of_attr_vars, ts_type_heaps, ts_td_infos) = liftSubstitution subst ti_common_defs cons_var_vects ts_attr_store ts_type_heaps ts_td_infos
		  coer_demanded ={{ CT_Empty \\ i <- [0 .. nr_of_attr_vars - 1] } & [AttrUni] = CT_Unique }
		  coer_offered = {{ CT_Empty \\ i <- [0 .. nr_of_attr_vars - 1] } & [AttrMulti] = CT_NonUnique }
		  coercion_env = build_initial_coercion_env fun_reqs {coer_demanded = coer_demanded, coer_offered = coer_offered }
		  (over_info, (subst, ts_expr_heap)) = collect_and_expand_overloaded_calls fun_reqs [] (subst, ts_expr_heap)
		  (contexts, coercion_env, local_pattern_variables, dict_types,
		  	{ os_type_heaps, os_var_heap, os_symbol_heap, os_predef_symbols, os_special_instances, os_error })
		  		= tryToSolveOverloading over_info main_dcl_module_n ti_common_defs class_instances coercion_env
		  			{	os_type_heaps = ts_type_heaps, os_var_heap = ts_var_heap, os_symbol_heap = ts_expr_heap,
		  				os_predef_symbols = predef_symbols, os_error = ts_error, os_special_instances = special_instances } modules
		| not os_error.ea_ok
			= (True, fun_defs, os_predef_symbols, os_special_instances, create_erroneous_function_types comp { ts & ts_type_heaps = os_type_heaps,
					ts_error = { os_error & ea_ok = True }, ts_var_store = 0, ts_attr_store = FirstAttrVar, ts_cons_variables = [], ts_exis_variables = [], 
					ts_td_infos = ts_td_infos, ts_expr_heap = os_symbol_heap, ts_var_heap = os_var_heap })
		# (fun_defs, coercion_env, subst, ts_td_infos, os_var_heap, os_symbol_heap, os_error)
		  		= makeSharedReferencesNonUnique comp fun_defs coercion_env subst ts_td_infos os_var_heap os_symbol_heap os_error
		  (subst, coercions, ts_td_infos, ts_type_heaps, ts_error)
		  		= build_coercion_env fun_reqs subst coercion_env ti_common_defs cons_var_vects ts_td_infos os_type_heaps os_error
		  (subst, ts_fun_env) = expand_function_types comp subst ts.ts_fun_env
		  (ts_fun_env, {coer_offered,coer_demanded})
		  		= foldSt (add_unicity_of_essentially_unique_types_for_function ti_common_defs)
		  				comp (ts_fun_env, coercions)
		  (attr_partition, coer_demanded) = partitionateAttributes coer_offered coer_demanded
		  (coer_demanded, ts_error) = check_existential_attributes ts_exis_variables attr_partition coer_demanded ts_error
		  attr_var_env = createArray nr_of_attr_vars TA_None
		  var_env = { subst & [i] = TE \\ i <- [0..dec ts_var_store]}
		  (fun_defs, ts) = cleanUpAndCheckFunctionTypes comp fun_reqs dict_types start_index list_inferred_types ti_common_defs contexts coer_demanded attr_partition var_env attr_var_env
									(fun_defs,  { ts &	ts_error = ts_error, ts_fun_env = ts_fun_env, ts_type_heaps = ts_type_heaps,
		  												ts_td_infos = ts_td_infos, ts_var_heap = os_var_heap, ts_expr_heap = os_symbol_heap })
		| not ts.ts_error.ea_ok
			= (True, fun_defs, os_predef_symbols, os_special_instances, create_erroneous_function_types comp
					{ ts & ts_var_store = 0, ts_attr_store = FirstAttrVar, ts_cons_variables = [], ts_exis_variables = [], ts_error = { ts.ts_error & ea_ok = True } })
		| isEmpty over_info 
			# ts_type_heaps = ts.ts_type_heaps
			  type_code_info = {	tci_next_index = os_special_instances.si_next_TC_member_index, tci_instances = os_special_instances.si_TC_instances,
									tci_type_var_heap = ts_type_heaps.th_vars,  tci_dcl_modules = dcl_modules } 
			  (fun_defs, ts_fun_env, ts_expr_heap, {tci_next_index,tci_instances,tci_type_var_heap}, ts_var_heap, ts_error, os_predef_symbols)
			  		= updateDynamics comp local_pattern_variables main_dcl_module_n fun_defs ts.ts_fun_env ts.ts_expr_heap type_code_info ts.ts_var_heap ts.ts_error os_predef_symbols
			= (	type_error || not ts_error.ea_ok, 
				fun_defs, os_predef_symbols, { os_special_instances & si_next_TC_member_index = tci_next_index, si_TC_instances = tci_instances },
				{ ts & ts_var_store = 0, ts_attr_store = FirstAttrVar, ts_cons_variables = [], ts_exis_variables = [],
						ts_expr_heap = ts_expr_heap, ts_error = { ts_error & ea_ok = True },
					  	ts_var_heap = ts_var_heap, ts_type_heaps = { ts_type_heaps & th_vars =  tci_type_var_heap }, ts_fun_env = ts_fun_env})
			# ts_type_heaps = ts.ts_type_heaps
			  type_code_info = {	tci_next_index = os_special_instances.si_next_TC_member_index, tci_instances = os_special_instances.si_TC_instances,
									tci_type_var_heap = ts_type_heaps.th_vars, tci_dcl_modules = dcl_modules } 
			  (fun_defs, ts_fun_env, ts_expr_heap, {tci_next_index,tci_instances,tci_type_var_heap}, ts_var_heap, ts_error, os_predef_symbols)
			  		= removeOverloadedFunctions comp local_pattern_variables main_dcl_module_n fun_defs ts.ts_fun_env
			  								ts.ts_expr_heap type_code_info ts.ts_var_heap ts.ts_error os_predef_symbols
			= (	type_error || not ts_error.ea_ok,
				fun_defs, os_predef_symbols, { os_special_instances & si_next_TC_member_index = tci_next_index, si_TC_instances = tci_instances },
				{ ts & ts_var_store = 0, ts_attr_store = FirstAttrVar, ts_cons_variables = [], ts_exis_variables = [],
						ts_expr_heap = ts_expr_heap, ts_error = { ts_error & ea_ok = True },
					  	ts_var_heap = ts_var_heap, ts_type_heaps = { ts_type_heaps & th_vars =  tci_type_var_heap }, ts_fun_env = ts_fun_env})

	add_unicity_of_essentially_unique_types_for_function ti_common_defs fun (ts_fun_env, coercions)
		# (env_type, ts_fun_env) = ts_fun_env![fun]
		= case env_type of
			ExpandedType _ _ _
				-> (ts_fun_env, coercions)
		  	UncheckedType {tst_args, tst_result}
				-> ( ts_fun_env
				   , foldSt (foldATypeSt (add_unicity_of_essentially_unique_type ti_common_defs) (\x st -> st)) 
							[tst_result:tst_args] coercions
				   )
	  where
		add_unicity_of_essentially_unique_type common_defs 
								{at_attribute=TA_TempVar av_number, at_type=TA {type_index} _} coercions
			# {td_attribute} = common_defs.[type_index.glob_module].com_type_defs.[type_index.glob_object]
			= case td_attribute of
				TA_Unique
					// the type is essentially unique
					-> snd (tryToMakeUnique av_number coercions)
				_
					-> coercions
		add_unicity_of_essentially_unique_type _ _ coercions
			= coercions

	unify_requirements_of_functions :: ![FunctionRequirements] !TypeInput !*{!Type} !*TypeHeaps !*ErrorAdmin -> (!*{!Type},!*TypeHeaps,!*ErrorAdmin)
	unify_requirements_of_functions [{fe_requirements={req_type_coercion_groups},fe_location={ip_ident}} : reqs_list] ti subst heaps ts_error
		# (subst, heaps, ts_error) = foldSt (unify_requirements_within_one_position ip_ident ti) req_type_coercion_groups (subst, heaps, ts_error)
		= unify_requirements_of_functions reqs_list ti subst heaps ts_error
	unify_requirements_of_functions [] ti subst heaps ts_error
		= (subst, heaps, ts_error)

  	unify_requirements_within_one_position :: !Ident !TypeInput !TypeCoercionGroup !(*{!Type}, !*TypeHeaps, !*ErrorAdmin)
 						-> (*{!Type}, !*TypeHeaps, !*ErrorAdmin)
	unify_requirements_within_one_position _ ti {tcg_type_coercions, tcg_position=NoPos} (subst, heaps, ts_error)
		= unify_coercions tcg_type_coercions ti subst heaps ts_error
	unify_requirements_within_one_position fun_symb ti {tcg_type_coercions, tcg_position} (subst, heaps, ts_error)
		# ts_error = setErrorAdmin (newPosition fun_symb tcg_position) ts_error
		= unify_coercions tcg_type_coercions ti subst heaps ts_error

	build_initial_coercion_env [{fe_requirements={req_attr_coercions},fe_location} : reqs_list] coercion_env
		= build_initial_coercion_env reqs_list (add_to_initial_coercion_env req_attr_coercions coercion_env)
	build_initial_coercion_env [] coercion_env
		= coercion_env

	add_to_initial_coercion_env [{ac_offered,ac_demanded} : attr_coercions] coercion_env
		= add_to_initial_coercion_env attr_coercions (newInequality ac_offered ac_demanded coercion_env)
	add_to_initial_coercion_env [] coercion_env
		= coercion_env

	determine_cons_variables variables vect_and_subst
		= foldSt determine_cons_variable variables vect_and_subst
	where	
		determine_cons_variable tv_number (bitvects, subst)
			# (type, subst) = subst![tv_number]
			= case type of
				TE
					-> (set_bit tv_number bitvects, subst)	// ---> ("determine_cons_variable1", tv_number)
				TempV var_number
					-> (set_bit var_number bitvects, subst)	// ---> ("determine_cons_variable2", var_number)
				_
					-> (bitvects, subst)

	build_coercion_env :: [.FunctionRequirements] v:{!Type} *Coercions {#CommonDefs} {#Int} *{#*{#TypeDefInfo}} *TypeHeaps !*ErrorAdmin -> (!w:{!Type},!.Coercions,!u:{#u:{#TypeDefInfo}},!.TypeHeaps,!.ErrorAdmin), [v <= w];
	build_coercion_env [{fe_requirements={req_type_coercion_groups},fe_location={ip_ident}} : reqs_list] subst coercion_env common_defs cons_var_vects type_signs type_var_heap error
		# (subst, coercion_env, type_signs, type_var_heap, error)
			= foldSt (build_coercion_env_for_alternative ip_ident common_defs cons_var_vects)
					req_type_coercion_groups
					(subst, coercion_env, type_signs, type_var_heap, error)
		= build_coercion_env reqs_list subst coercion_env common_defs cons_var_vects  type_signs type_var_heap error
	build_coercion_env []  subst coercion_env common_defs cons_var_vects type_signs type_var_heap error
		= (subst, coercion_env, type_signs, type_var_heap, error)

	build_coercion_env_for_alternative fun_symb common_defs cons_var_vects {tcg_position, tcg_type_coercions}
										(subst, coercion_env, type_signs, type_var_heap, error)
		# error = setErrorAdmin (newPosition fun_symb tcg_position) error
		= add_to_coercion_env tcg_type_coercions subst coercion_env common_defs cons_var_vects type_signs type_var_heap error

	add_to_coercion_env [{tc_offered,tc_demanded,tc_coercible,tc_position} : attr_coercions] subst coercion_env common_defs cons_var_vects type_signs type_var_heap error
		# (opt_error_info, subst, coercion_env, type_signs, type_var_heap)
				= determineAttributeCoercions tc_offered tc_demanded tc_coercible
						subst coercion_env common_defs cons_var_vects type_signs
						type_var_heap
		  (coercion_env, error)
			= case opt_error_info of
				No
					-> (coercion_env, error)
				Yes (positions, exp_off_type)
					# (error=:{ea_file})
							= errorHeading "Uniqueness error" error
					  (coercion_env, copy_coercion_env)
					  		= uniqueCopy coercion_env
					  format
					  		= { form_properties = cMarkAttribute,
					  			form_attr_position = Yes (reverse positions, copy_coercion_env) }			
					  ea_file = 
					  	case tc_position of
					  		CP_FunArg _ _
					  			-> ea_file <<< "\"" <<< tc_position <<< "\" "
					  		_
					  			-> ea_file
					  ea_file = ea_file	<<< "attribute at indicated position could not be coerced "
					  					 <:: (format, exp_off_type, Yes initialTypeVarBeautifulizer) <<< '\n'
					-> (coercion_env, { error & ea_file = ea_file })
		= add_to_coercion_env attr_coercions subst coercion_env common_defs cons_var_vects type_signs type_var_heap error
	add_to_coercion_env []  subst coercion_env common_defs cons_var_vects type_signs type_var_heap error
		= (subst, coercion_env, type_signs, type_var_heap, error)

	check_existential_attributes ts_exis_variables partition coercions ts_error
		= foldSt (check_existential_attributes_at_pos partition) ts_exis_variables (coercions, ts_error)
	where
		check_existential_attributes_at_pos partition (pos, attr_vars) (coercions, ts_error)
			# (ok, coercions) = checkExistentionalAttributeVars attr_vars partition coercions
			| ok
				= (coercions, ts_error)
				= (coercions, existentialError pos ts_error)

	collect_and_expand_overloaded_calls [] calls subst_and_heap
		= (calls, subst_and_heap)

	collect_and_expand_overloaded_calls [{ fe_context=Yes context, fe_requirements={req_overloaded_calls,req_case_and_let_exprs}, fe_location, fe_index}:reqs] calls (subst, expr_heap)
		# (_, context, subst) = arraySubst context subst
		  subst_expr_heap = expand_case_or_let_types req_case_and_let_exprs (subst, expr_heap)
		= collect_and_expand_overloaded_calls reqs [(Yes context, req_overloaded_calls, fe_location, fe_index) : calls]
				(foldSt expand_type_contexts req_overloaded_calls subst_expr_heap) 	
	collect_and_expand_overloaded_calls [{fe_context, fe_requirements={req_overloaded_calls,req_case_and_let_exprs}, fe_location, fe_index}:reqs] calls subst_expr_heap
		# subst_expr_heap = expand_case_or_let_types req_case_and_let_exprs subst_expr_heap
		= collect_and_expand_overloaded_calls reqs [(fe_context, req_overloaded_calls, fe_location, fe_index) : calls]
				(foldSt expand_type_contexts req_overloaded_calls subst_expr_heap) 

	expand_type_contexts over_info_ptr (subst, expr_heap)
		# (EI_Overloaded info, expr_heap) = readPtr over_info_ptr expr_heap
		  (changed, oc_context, subst) = arraySubst info.oc_context subst
		| changed
			= (subst, expr_heap <:= (over_info_ptr, EI_Overloaded { info & oc_context = oc_context }))
			= (subst, expr_heap)

	expand_case_or_let_types info_ptrs subst_expr_heap
		= foldSt expand_case_or_let_type info_ptrs subst_expr_heap

	expand_case_or_let_type info_ptr (subst, expr_heap)
		= case (readPtr info_ptr expr_heap) of
			(EI_CaseType case_type, expr_heap)
				# (changed, case_type, subst) = arraySubst case_type subst
				| changed
					-> (subst, expr_heap <:= (info_ptr, EI_CaseType case_type))
					-> (subst, expr_heap)
			(EI_LetType let_type, expr_heap)
				# (changed, let_type, subst) = arraySubst let_type subst
				| changed
					-> (subst, expr_heap <:= (info_ptr, EI_LetType let_type))
					-> (subst, expr_heap)

	expand_function_types :: ![Int] !*{!Type} *{! FunctionType} -> (!*{!Type}, *{! FunctionType})
	expand_function_types [fun : funs] subst ts_fun_env
		# (fun_type, ts_fun_env) = ts_fun_env![fun]
		= case fun_type of
			UncheckedType tst
				# (_, exp_tst, subst) = arraySubst tst subst
				-> expand_function_types funs subst { ts_fun_env & [fun] = UncheckedType exp_tst}
			SpecifiedType ft _ tst
				# (_, exp_tst, subst) = arraySubst tst subst
				-> expand_function_types funs subst { ts_fun_env & [fun] = ExpandedType ft tst exp_tst}
//						---> ("expand_function_types", tst, exp_tst)
	expand_function_types [] subst ts_fun_env
		= (subst, ts_fun_env)
			

	update_function_types :: !Index !{!Group} !*{!FunctionType} !*{#FunDef} -> (!*{#FunDef}, !*{!FunctionType})
	update_function_types group_index comps fun_env fun_defs
		| group_index == size comps
			= (fun_defs, fun_env)
			#! comp = comps.[group_index]	
			# (fun_defs, fun_env) = update_function_types_in_component comp.group_members fun_env fun_defs
			= update_function_types (inc group_index) comps fun_env fun_defs

	where
		update_function_types_in_component :: ![Index] !*{!FunctionType} !*{#FunDef} -> (!*{#FunDef}, !*{!FunctionType})
		update_function_types_in_component [ fun_index : funs ] fun_env fun_defs
			# (CheckedType checked_fun_type, fun_env) = fun_env![fun_index]
			# (fd, fun_defs) = fun_defs![fun_index]
			= case fd.fun_type of
				No
					-> update_function_types_in_component funs fun_env { fun_defs & [fun_index] = { fd & fun_type = Yes checked_fun_type }}
				Yes fun_type
					# nr_of_lifted_arguments = checked_fun_type.st_arity - fun_type.st_arity
					| nr_of_lifted_arguments > 0
						# fun_type = addLiftedArgumentsToSymbolType fun_type nr_of_lifted_arguments
									checked_fun_type.st_args checked_fun_type.st_vars checked_fun_type.st_attr_vars checked_fun_type.st_context
						-> update_function_types_in_component funs fun_env { fun_defs & [fun_index] = { fd & fun_type = Yes fun_type }}
						-> update_function_types_in_component funs fun_env fun_defs
		update_function_types_in_component [] fun_env fun_defs
			= (fun_defs, fun_env)
	
	type_functions group ti fun_defs ts
		= mapSt (type_function ti) group (fun_defs, ts) 

	type_function ti fun_index (fun_defs, ts=:{ts_fun_env, ts_var_heap, ts_expr_heap, ts_error})
		# (fd, fun_defs) = fun_defs![fun_index]
		  (type, ts_fun_env) = ts_fun_env![fun_index]
		  {fun_symb,fun_arity,fun_body=TransformedBody {tb_args,tb_rhs},fun_pos, fun_info, fun_type} = fd
		  temp_fun_type = type_of type
		  ts_var_heap = makeBase fun_symb 1 tb_args temp_fun_type.tst_args ts_var_heap
		  fe_location = newPosition fun_symb fun_pos
		  ts_error = setErrorAdmin fe_location ts_error
		  reqs = { req_overloaded_calls = [], req_type_coercion_groups = [], req_type_coercions = [],
		  			 req_attr_coercions = [], req_case_and_let_exprs = [] }
		  ( rhs_type, rhs_expr_ptr, (rhs_reqs, ts)) = requirements ti tb_rhs (reqs,
		  		{ ts & ts_var_heap = ts_var_heap, ts_expr_heap = ts_expr_heap, ts_error = ts_error, ts_fun_env = ts_fun_env })
		  req_type_coercions = [{tc_demanded = temp_fun_type.tst_result,tc_offered = rhs_type, tc_position = CP_Expression tb_rhs, tc_coercible = True} :
		  		rhs_reqs.req_type_coercions ]
		  ts_expr_heap = storeAttribute rhs_expr_ptr temp_fun_type.tst_result.at_attribute ts.ts_expr_heap
		  type_coercion_group_from_accu = { tcg_type_coercions = req_type_coercions, tcg_position = fun_pos }
		  req_type_coercion_groups = [type_coercion_group_from_accu:rhs_reqs.req_type_coercion_groups]
		= ( { fe_location = fe_location, fe_context = if (has_option fun_type) (Yes temp_fun_type.tst_context) No, fe_index = fun_index,
			  fe_requirements = { rhs_reqs & req_type_coercions = [], req_type_coercion_groups = req_type_coercion_groups }
		    },
		    (fun_defs, { ts & ts_expr_heap = ts_expr_heap }))
//					 ---> ("type_function", fun_symb, tb_args, tb_rhs, fun_info.fi_local_vars)
	where
		has_option (Yes _)	= True
		has_option No 		= False
		 
		type_of (UncheckedType tst)		= tst
		type_of (SpecifiedType _ _ tst) = tst

	create_special_instances {si_array_instances,si_list_instances,si_tail_strict_list_instances,si_next_array_member_index,si_next_TC_member_index,si_TC_instances} fun_env_size common_defs fun_defs predef_symbols type_heaps error
		# fun_defs = add_extra_elements_to_fun_def_array (si_next_array_member_index-fun_env_size) fun_defs
		  	with
		  		add_extra_elements_to_fun_def_array n_new_elements fun_defs
		  			| n_new_elements==0
		  				= fun_defs
			  			# dummy_fun_def = { fun_symb = {id_name="",id_info=nilPtr},fun_arity=0,fun_priority=NoPrio,fun_body=NoBody,fun_type=No,fun_pos=NoPos,
										  				fun_kind=FK_DefOrImpUnknown,fun_lifted=0,fun_info = {fi_calls=[],fi_group_index=0,fi_def_level=NotALevel,fi_free_vars=[],fi_local_vars=[],fi_dynamics=[],fi_properties=0}}
			  			= {createArray (size fun_defs+n_new_elements) dummy_fun_def & [i]=fun_defs.[i] \\ i<-[0..size fun_defs-1]}
		  (array_first_instance_indices,fun_defs, predef_symbols, type_heaps, error)
		  		= convert_array_instances si_array_instances common_defs fun_defs predef_symbols type_heaps	error  
		  (list_first_instance_indices,fun_defs, predef_symbols, type_heaps, error)
		  		= convert_list_instances si_list_instances PD_UListClass common_defs fun_defs predef_symbols type_heaps error
		  (tail_strict_list_first_instance_indices,fun_defs, predef_symbols, type_heaps, error)
		  		= convert_list_instances si_tail_strict_list_instances PD_UTSListClass common_defs fun_defs predef_symbols type_heaps error
		  type_code_instances = {createArray si_next_TC_member_index GTT_Function & [gtci_index] = gtci_type \\ {gtci_index, gtci_type} <- si_TC_instances}
		  array_first_instance_indices = first_instance_indices si_array_instances
		= (array_first_instance_indices,list_first_instance_indices,tail_strict_list_first_instance_indices,fun_defs,type_code_instances,predef_symbols,type_heaps,error)
	where
		convert_array_instances array_instances common_defs fun_defs predef_symbols type_heaps error
			| isEmpty array_instances
				= ([],fun_defs, predef_symbols, type_heaps, error)
				# ({pds_ident,pds_module,pds_def},predef_symbols) = predef_symbols![PD_UnboxedArrayType]
				  unboxed_array_type = TA (MakeTypeSymbIdent { glob_object = pds_def, glob_module = pds_module } pds_ident 0) []
				  ({pds_module,pds_def},predef_symbols) = predef_symbols![PD_ArrayClass]
				  {class_members} = common_defs.[pds_module].com_class_defs.[pds_def]
				  array_members = common_defs.[pds_module].com_member_defs
				  (offset_table, _, predef_symbols) = arrayFunOffsetToPD_IndexTable array_members predef_symbols
				  (fun_defs, type_heaps, error) = foldSt (convert_array_instance class_members array_members unboxed_array_type offset_table) array_instances (fun_defs, type_heaps, error)
		  		  array_first_instance_indices = first_instance_indices array_instances
				= (array_first_instance_indices,fun_defs, predef_symbols, type_heaps, error)
		where
			convert_array_instance class_members array_members unboxed_array_type offset_table {ai_record,ai_members} funs_heaps_and_error
				= create_instance_types class_members array_members unboxed_array_type offset_table (TA ai_record []) (size class_members) funs_heaps_and_error
			where
				first_instance_index=ai_members.[0].ds_index
				
				create_instance_types :: {#DefinedSymbol} {#MemberDef} Type {#Int} Type !Int !(!*{#FunDef}, !*TypeHeaps, !*ErrorAdmin)
					-> (!*{#FunDef}, !*TypeHeaps, !*ErrorAdmin);
				create_instance_types members array_members unboxed_array_type offset_table record_type member_index funs_heaps_and_error
					| member_index == 0
						= funs_heaps_and_error
						# member_index = dec member_index
						  funs_heaps_and_error = create_instance_type members array_members unboxed_array_type offset_table record_type member_index funs_heaps_and_error
						= create_instance_types members array_members unboxed_array_type offset_table record_type member_index funs_heaps_and_error
		
				create_instance_type members array_members unboxed_array_type offset_table record_type member_index (fun_defs, type_heaps, error)
					# {me_type,me_symb,me_class_vars,me_pos} = array_members.[members.[member_index].ds_index]
					  (instance_type, _, type_heaps, _, error) = determineTypeOfMemberInstance me_type me_class_vars {it_vars = [], it_attr_vars = [], it_context = [],
															it_types = [unboxed_array_type, record_type]} SP_None type_heaps No error
					  instance_type = makeElemTypeOfArrayFunctionStrict instance_type member_index offset_table
					  fun_index = first_instance_index+member_index
					  fun = 
						{	fun_symb		= me_symb
						,	fun_arity		= me_type.st_arity
						,	fun_priority	= NoPrio
						,	fun_body		= NoBody
						,	fun_type		= Yes instance_type
						,	fun_pos			= me_pos
						,	fun_kind		= FK_DefOrImpUnknown
						,	fun_lifted		= 0
						,	fun_info		= EmptyFunInfo
						}
					= ({fun_defs & [fun_index]=fun}, type_heaps, error)

		convert_list_instances list_instances predef_list_class_index common_defs fun_defs predef_symbols type_heaps error
			| isEmpty list_instances
				= ([],fun_defs, predef_symbols, type_heaps, error)
				# ({pds_module,pds_def},predef_symbols) = predef_symbols![predef_list_class_index]
				  {class_members} = common_defs.[pds_module].com_class_defs.[pds_def]
				  list_members = common_defs.[pds_module].com_member_defs
				  (fun_defs, type_heaps, error) = foldSt (convert_list_instance class_members list_members) list_instances (fun_defs, type_heaps, error)
		  		  list_first_instance_indices = first_instance_indices list_instances
				= (list_first_instance_indices,fun_defs, predef_symbols, type_heaps, error)
		where
			convert_list_instance class_members list_members {ai_record,ai_members} funs_heaps_and_error
				= create_instance_types class_members list_members (TA ai_record []) (size class_members) funs_heaps_and_error
			where
				first_instance_index=ai_members.[0].ds_index
				
				create_instance_types :: {#DefinedSymbol} {#MemberDef} Type !Int !(!*{#FunDef}, !*TypeHeaps, !*ErrorAdmin)
					-> (!*{#FunDef}, !*TypeHeaps, !*ErrorAdmin)
				create_instance_types members list_members record_type member_index funs_heaps_and_error
					| member_index == 0
						= funs_heaps_and_error
						# member_index = dec member_index
						  funs_heaps_and_error = create_instance_type members list_members record_type member_index funs_heaps_and_error
						= create_instance_types members list_members record_type member_index funs_heaps_and_error

				create_instance_type members list_members record_type member_index (fun_defs, type_heaps, error)
					# {me_type,me_symb,me_class_vars,me_pos} = list_members.[members.[member_index].ds_index]
					  (instance_type, _, type_heaps, _, error) = determineTypeOfMemberInstance me_type me_class_vars {it_vars = [], it_attr_vars = [], it_context = [],
															it_types = [record_type]} SP_None type_heaps No error
					  fun_index = first_instance_index+member_index
					  fun = 
						{	fun_symb		= me_symb
						,	fun_arity		= me_type.st_arity
						,	fun_priority	= NoPrio
						,	fun_body		= NoBody
						,	fun_type		= Yes instance_type
						,	fun_pos			= me_pos
						,	fun_kind		= FK_DefOrImpUnknown
						,	fun_lifted		= 0
						,	fun_info		= EmptyFunInfo
						}
					= ({fun_defs & [fun_index]=fun}, type_heaps, error)
	
		first_instance_indices instances
			= [ai_members.[0].ds_index \\ {ai_members}<-instances]
	
	create_erroneous_function_types group ts
		= foldSt create_erroneous_function_type group ts
		
	create_erroneous_function_type fun ts
		# (env_type, ts) = ts!ts_fun_env.[fun]
		= case env_type of
			ExpandedType fun_type tmp_fun_type exp_fun_type
				# (fun_type, ts_type_heaps) = extendSymbolType fun_type tmp_fun_type.tst_lifted ts.ts_type_heaps
				-> { ts & ts_type_heaps = ts_type_heaps, ts_fun_env = { ts.ts_fun_env & [fun] = CheckedType fun_type }}
		  	UncheckedType tmp_fun_type
		  		# (clean_fun_type, ts_type_heaps) = cleanSymbolType tmp_fun_type.tst_arity ts.ts_type_heaps
				-> { ts & ts_type_heaps = ts_type_heaps, ts_fun_env = { ts.ts_fun_env & [fun] = CheckedType clean_fun_type }}
			SpecifiedType fun_type _ tmp_fun_type
				# (fun_type, ts_type_heaps) = extendSymbolType fun_type tmp_fun_type.tst_lifted ts.ts_type_heaps
				-> { ts & ts_type_heaps = ts_type_heaps, ts_fun_env = { ts.ts_fun_env & [fun] = CheckedType fun_type }}
			CheckedType _
				-> ts

uniqueCopy :: !*a -> (!*a, !*a)
uniqueCopy x =
	code
	{	.inline uniqueCopy
			push_a 0
		.end
	}
is_rare_name {id_name}
	= id_name.[0]=='_'

getPositionOfExpr expr=:(Var {var_info_ptr}) var_heap
	= case readPtr var_info_ptr var_heap of
		(VI_Type _ (Yes position), var_heap)
			-> (position, var_heap)
		(VI_FAType _ _ (Yes position), var_heap)
			-> (position, var_heap)
		(_, var_heap)
			-> (CP_Expression expr, var_heap)
getPositionOfExpr expr var_heap
	= (CP_Expression expr, var_heap)

empty_id =: { id_name = "", id_info = nilPtr }

instance <<< AttrCoercion
where
	(<<<) file {ac_demanded,ac_offered} = file <<< "AttrCoercion: " <<< ac_demanded <<< '~' <<< ac_offered

instance <<< TypeCoercion
where
	(<<<) file {tc_demanded,tc_offered} = file <<< "TypeCoercion: " <<< tc_demanded <<< '~' <<< tc_offered

instance <<< TypeContext
where
	(<<<) file co = file <<< "TypeContext:  (tc_class)=" <<< co.tc_class <<< " (tc_var)=" <<< ptrToInt co.tc_var <<< " (tc_types)=" <<< " " <<< co.tc_types 
	
instance <<< DefinedSymbol
where
	(<<<) file {ds_ident}
		= file <<< "DefinedSymbol: " <<< ds_ident

instance <<< FunctionType
where
	(<<<) file (CheckedType _)
		= file <<< "CheckedType"
	(<<<) file (SpecifiedType _ _ _)
		= file <<< "SpecifiedType"
	(<<<) file (UncheckedType _)
		= file <<< "UncheckedType"
	(<<<) file (ExpandedType _ _ _)
		= file <<< "ExpandedType"
	(<<<) file EmptyFunctionType
		= file <<< "EmptyFunctionType"
