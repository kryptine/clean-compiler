implementation module typesupport

import StdEnv, StdCompare
import syntax, parse, check, unitype, utilities, RWSDebug

do_fusion :== False
// MW: this switch is used to en(dis)able the fusion algorithm which currently isn't ready

::	Store	:== Int

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


simplifyTypeApplication :: !Type ![AType] -> Type
simplifyTypeApplication (TA type_cons=:{type_arity} cons_args) type_args
	= TA { type_cons & type_arity = type_arity + length type_args } (cons_args ++ type_args)
simplifyTypeApplication (TV tv) type_args
	= CV tv :@: type_args
simplifyTypeApplication (CV tv :@: type_args1) type_args2
	= CV tv :@: (type_args1 ++ type_args2)

::	AttributeEnv	:== {! TypeAttribute }
::	VarEnv 			:== {! Type }

::	CleanUpState =
	{	cus_var_env		:: !.VarEnv
	,	cus_attr_env	:: !.AttributeEnv
	,	cus_heaps		:: !.TypeHeaps
	,	cus_var_store	:: !Int
	,	cus_attr_store	:: !Int
	,	cus_error		:: !.ErrorAdmin
	}

::	CleanUpInput =
	{	cui_coercions	:: !{! CoercionTree}
	,	cui_attr_part	:: !AttributePartition
	,	cui_top_level	:: !Bool
	}

class clean_up a ::  !CleanUpInput !a !*CleanUpState -> (!a, !*CleanUpState)

instance clean_up AType
where
	clean_up cui atype=:{at_attribute,at_type} cus
		# (at_attribute, cus) = clean_up cui at_attribute cus 
		  (at_type, cus) = clean_up cui at_type cus
		= ({atype & at_attribute = at_attribute, at_type = at_type}, cus)

attrIsUndefined TA_None = True
attrIsUndefined _ 		= False

varIsDefined TE		= False
varIsDefined _ 		= True

instance clean_up TypeAttribute
where
	clean_up cui TA_Unique cus
		= (TA_Unique, cus)
	clean_up cui TA_Multi cus
		= (TA_Multi, cus)
	clean_up cui tv=:(TA_TempVar av_number) cus=:{cus_attr_env,cus_heaps,cus_attr_store,cus_error}
		| cui.cui_top_level
			# av_group_nr = cui.cui_attr_part.[av_number]
			  coercion_tree = cui.cui_coercions.[av_group_nr]
			| isNonUnique coercion_tree
				= (TA_Multi, cus)
			| isUnique coercion_tree
				= (TA_Unique, cus)
			#! attr = cus_attr_env.[av_group_nr]
			| attrIsUndefined attr
				# (av_info_ptr, th_attrs) = newPtr AVI_Empty cus_heaps.th_attrs
				  new_attr_var = TA_Var { av_name = NewAttrVarId cus_attr_store, av_info_ptr = av_info_ptr }
				= (new_attr_var, { cus & cus_attr_env = { cus_attr_env & [av_group_nr] = new_attr_var},
						 cus_heaps = { cus_heaps & th_attrs = th_attrs }, cus_attr_store = inc cus_attr_store})
				= (attr, cus)
			= (TA_Multi, cus)
			
instance clean_up Type
where
	clean_up cui (TempV tv_number) cus=:{cus_var_env}
		#! type = cus_var_env.[tv_number]
		= cleanUpVariable cui.cui_top_level type tv_number cus
	clean_up cui (TA tc types) cus
		# (types, cus) = clean_up cui types cus
		= (TA tc types, cus)
	clean_up cui (argtype --> restype) cus
		# (argtype, cus) = clean_up cui argtype cus
		  (restype, cus) = clean_up cui restype cus
		=  (argtype --> restype, cus)
	clean_up cui t=:(TB _) cus
		=  (t, cus)
	clean_up cui (TempCV tempvar :@: types) cus
		#! type = cus.cus_var_env.[tempvar]
		# (type, cus) = cleanUpVariable cui.cui_top_level type tempvar cus
		  (types, cus) = clean_up cui types cus
		= (simplifyTypeApplication type types, cus)
	clean_up cui (TempQV qv_number) cus=:{cus_var_env,cus_error}
		#! type = cus_var_env.[qv_number]
		| cui.cui_top_level
			= cleanUpVariable True type qv_number {cus & cus_error = existentialError cus_error}
			= cleanUpVariable False type qv_number cus
	clean_up cui TE cus
		= abort "unknown pattern in function clean_up"
				
instance clean_up [a] | clean_up a
where
	clean_up cui l cus = mapSt (clean_up cui) l cus

cleanUpVariable _ TE tv_number cus=:{cus_heaps,cus_var_store,cus_var_env}
	# (tv_info_ptr, th_vars) = newPtr TVI_Empty cus_heaps.th_vars
	  new_var = TV { tv_name = NewVarId cus_var_store, tv_info_ptr = tv_info_ptr }
	= (new_var, { cus & cus_var_env = { cus_var_env & [tv_number] = new_var},
				cus_heaps = { cus_heaps & th_vars = th_vars }, cus_var_store = inc cus_var_store})
cleanUpVariable top_level (TLifted var) tv_number cus=:{cus_error}
	| top_level
		= (TV var, { cus & cus_error = liftedError var cus_error})
		= (TV var, cus)
cleanUpVariable _ type tv_number cus
	= (type, cus)

class cleanUpClosed a :: !a !u:VarEnv -> (!Bool, !a, !u:VarEnv)

instance cleanUpClosed AType
where
	cleanUpClosed atype=:{at_type} env
		# (ok, at_type, env) = cleanUpClosed at_type env
		= (ok, { atype & at_type = at_type}, env)

instance cleanUpClosed Type
where
	cleanUpClosed (TempV tv_number) env
		#! type = env.[tv_number]
		= (varIsDefined type, type, env)
	cleanUpClosed (TA tc types) env
		# (ok, types, env) = cleanUpClosed types env
		= (ok, TA tc types, env)
	cleanUpClosed (argtype --> restype) env
		# (ok, (argtype,res_type), env) = cleanUpClosed (argtype,restype) env
		= (ok, argtype --> restype, env)
	cleanUpClosed (TempCV tv_number :@: types) env
		#! type = env.[tv_number]
		| varIsDefined type
			# (ok, types, env) = cleanUpClosed types env
            = (ok, simplifyTypeApplication type types, env)
			= (False, TempCV tv_number :@: types, env)
	cleanUpClosed t env
		= (True, t, env)

instance cleanUpClosed (a,b) | cleanUpClosed a & cleanUpClosed b
where
	cleanUpClosed (x,y) env
		# (ok_x, x, env) = cleanUpClosed x env
		| ok_x
			# (ok_y, y, env) = cleanUpClosed y env
			= (ok_y, (x,y), env)
		= (False, (x,y), env)

instance cleanUpClosed [a] | cleanUpClosed a
where
	cleanUpClosed [] env
		= (True, [], env)
	cleanUpClosed [t:ts] env
		# (ok, (t,ts), env) = cleanUpClosed (t,ts) env
		= (ok, [t:ts], env)

errorHeading :: !String !*ErrorAdmin -> *ErrorAdmin
errorHeading  error_kind err=:{ea_file,ea_loc = []}
	= { err & ea_file = ea_file <<< error_kind <<< ':', ea_ok = False }
errorHeading  error_kind err=:{ea_file,ea_loc = [ loc : _ ]}
	= { err & ea_file = ea_file <<< error_kind <<< ' ' <<< loc <<< ':', ea_ok = False }

overloadingError class_symb err
	# err = errorHeading "Type error" err
	= { err & ea_file = err.ea_file <<< "internal overloading of class " <<< class_symb <<< " is unsolvable\n" }

existentialError err
	# err = errorHeading "Type error" err
	= { err & ea_file = err.ea_file <<< "existential type variable appears in the derived type specification\n" }

liftedError var err
	# err = errorHeading "Type error" err
	= { err & ea_file = err.ea_file <<< "type variable of type of lifted argument " <<< var <<< " appears in the specified type\n" }

clean_up_type_contexts [] env error
	= ([], env, error)
clean_up_type_contexts [tc:tcs] env error
	# (tcs, env, error) = clean_up_type_contexts tcs env error
	  (ok_tc_types, tc_types, env) = cleanUpClosed tc.tc_types env
	| ok_tc_types
		= ([{ tc & tc_types = tc_types } : tcs], env, error)
		= (tcs, env, overloadingError tc.tc_class.glob_object.ds_ident error)

extendSymbolType :: !SymbolType !Int !*TypeHeaps -> (!SymbolType, !*TypeHeaps)
extendSymbolType st=:{st_arity,st_args,st_vars,st_attr_vars} nr_of_extra_args type_heaps
	| nr_of_extra_args > 0
		# (st_args, (st_vars, st_attr_vars, type_heaps))
			= newAttributedVariables nr_of_extra_args st_args (st_vars, st_attr_vars, type_heaps)
		= ({ st & st_args = st_args, st_vars = st_vars, st_attr_vars = st_attr_vars, st_arity = st_arity + nr_of_extra_args }, type_heaps)
		= (st, type_heaps)

cleanSymbolType :: !Int !*TypeHeaps -> (!SymbolType, !*TypeHeaps)
cleanSymbolType arity type_heaps
	# (st_result, clean_state) = newAttributedVariable 0 ([], [], type_heaps)
	  (st_args, (st_vars, st_attr_vars, type_heaps)) = newAttributedVariables arity [] clean_state
	= ({ st_arity = arity, st_vars = st_vars , st_args = st_args, st_result = st_result, st_context = [],
			st_attr_env = [], st_attr_vars = st_attr_vars }, type_heaps)

newAttributedVariables var_number attributed_variables clean_state=:(_,_,_) /* Temporary hack */
	| var_number == 0
		= (attributed_variables, clean_state)
		# (attributed_variable, clean_state) = newAttributedVariable var_number clean_state
		= newAttributedVariables (dec var_number) [ attributed_variable : attributed_variables ] clean_state

newAttributedVariable var_number (variables, attributes, type_heaps=:{th_vars,th_attrs})
	# (tv_info_ptr, th_vars) = newPtr TVI_Empty th_vars
	  new_var = { tv_name = NewVarId var_number, tv_info_ptr = tv_info_ptr }
	  (av_info_ptr, th_attrs) = newPtr AVI_Empty th_attrs
	  new_attr_var = { av_name = NewAttrVarId var_number, av_info_ptr = av_info_ptr }
	= ({ at_annotation = AN_None, at_attribute = TA_Var new_attr_var, at_type = TV new_var},
		([ new_var : variables ], [ new_attr_var : attributes ], { type_heaps & th_vars = th_vars, th_attrs = th_attrs }))

cleanUpSymbolType :: !TempSymbolType ![TypeContext] ![ExprInfoPtr] !{! CoercionTree} !AttributePartition
						!*VarEnv !*AttributeEnv !*TypeHeaps !*ExpressionHeap !*ErrorAdmin
							-> (!SymbolType, !*VarEnv, !*AttributeEnv, !*TypeHeaps, !*ExpressionHeap, !*ErrorAdmin)
cleanUpSymbolType tst=:{tst_arity,tst_args,tst_result,tst_context,tst_lifted} context case_and_let_exprs
		coercions attr_part var_env attr_var_env heaps expr_heap error
	#! nr_of_temp_vars = size var_env
	#! max_attr_nr = size attr_var_env
	# cus = { cus_var_env = var_env, cus_attr_env = attr_var_env, cus_heaps = heaps,
			  cus_var_store = 0, cus_attr_store = 0, cus_error = error }
	  cui = { cui_coercions = coercions, cui_attr_part = attr_part, cui_top_level = True }
	  (lifted_args, cus=:{cus_var_env}) = clean_up cui (take tst_lifted tst_args) cus
	  (lifted_vars, cus_var_env) = determine_type_vars nr_of_temp_vars [] cus_var_env
	  (st_args, cus) = clean_up cui (drop tst_lifted tst_args) { cus & cus_var_env = cus_var_env }
	  (st_result, cus) = clean_up cui tst_result cus
	  (st_context, cus_var_env, cus_error) = clean_up_type_contexts (tst_context ++ context) cus.cus_var_env cus.cus_error
	  (st_vars, cus_var_env) = determine_type_vars nr_of_temp_vars lifted_vars cus_var_env
	  (cus_attr_env, st_attr_vars, st_attr_env) = build_attribute_environment 0 max_attr_nr coercions cus.cus_attr_env [] []
	  (expr_heap, {cus_var_env,cus_attr_env,cus_heaps,cus_error}) = update_expression_types { cui & cui_top_level = False } case_and_let_exprs
				expr_heap { cus & cus_var_env = cus_var_env, cus_attr_env = cus_attr_env, cus_error = cus_error }
	  st = {  st_arity = tst_arity, st_vars = st_vars , st_args = lifted_args ++ st_args, st_result = st_result, st_context = st_context,
			st_attr_env = st_attr_env, st_attr_vars = st_attr_vars }
	= (st,			{ cus_var_env & [i] = TE \\ i <- [0..nr_of_temp_vars - 1]},
					{ cus_attr_env & [i] = TA_None \\ i <- [0..max_attr_nr - 1]}, cus_heaps, expr_heap, cus_error)
where
	determine_type_vars to_index all_vars var_env
		= iFoldSt determine_type_var 0 to_index (all_vars, var_env)
	where
		determine_type_var var_index (all_vars, var_env)
			#! type = var_env.[var_index]
			= case type of
				TV var
					-> ([var : all_vars], { var_env & [var_index] = TLifted var})
				_
					-> (all_vars, var_env)


	determine_type_var var_index (all_vars, var_env)
		#! type = var_env.[var_index]
		= case type of
			TV var
				-> ([var : all_vars], var_env)
			_
				-> (all_vars, var_env)

	
	build_attribute_environment :: !Index !Index !{! CoercionTree} !*AttributeEnv ![AttributeVar] ![AttrInequality]
		-> (!*AttributeEnv, ![AttributeVar], ![AttrInequality])
	build_attribute_environment attr_group_index max_attr_nr coercions attr_env attr_vars inequalities
		| attr_group_index == max_attr_nr
			= (attr_env, attr_vars, inequalities)
		#! attr = attr_env.[attr_group_index]
		= case attr of
			TA_Var attr_var
				# (attr_env, inequalities) = build_inequalities attr_var coercions.[attr_group_index] coercions attr_env inequalities
				-> build_attribute_environment (inc attr_group_index) max_attr_nr coercions attr_env [attr_var : attr_vars] inequalities
			TA_None
				-> build_attribute_environment (inc attr_group_index) max_attr_nr coercions attr_env attr_vars inequalities
	
	build_inequalities off_var (CT_Node dem_attr left right) coercions attr_env inequalities
		# (attr_env, inequalities) = build_inequalities off_var left coercions attr_env inequalities
		  (attr_env, inequalities) = build_inequalities off_var right coercions attr_env inequalities
		#! attr = attr_env.[dem_attr]
		= case attr of
			TA_Var attr_var
				| is_new_inequality attr_var off_var inequalities
					-> (attr_env, [{ ai_demanded = attr_var, ai_offered = off_var } : inequalities]) 
					-> (attr_env, inequalities)
			TA_None
				-> build_inequalities off_var coercions.[dem_attr] coercions attr_env inequalities
	build_inequalities off_var tree coercions attr_env inequalities
		= (attr_env, inequalities)

	is_new_inequality dem_var off_var []
		= True
	is_new_inequality dem_var off_var [{ ai_demanded, ai_offered } : inequalities]
		= (dem_var <> ai_demanded || off_var <> ai_offered) && is_new_inequality dem_var off_var inequalities

	update_expression_types :: !CleanUpInput ![ExprInfoPtr] !*ExpressionHeap !*CleanUpState -> (!*ExpressionHeap,!*CleanUpState);
	update_expression_types cui expr_ptrs expr_heap cus
		= (expr_heap, cus)
//		= foldSt (update_expression_type cui) expr_ptrs (expr_heap, cus)

	update_expression_type cui expr_ptr (expr_heap, cus)
		# (info, expr_heap) = readPtr expr_ptr expr_heap
		= case info of
			EI_CaseType case_type
				# (case_type, cus) = clean_up cui case_type cus
				-> (expr_heap <:= (expr_ptr, EI_CaseType case_type), cus)
			EI_LetType let_type
				# (let_type, cus) = clean_up cui let_type cus
				-> (expr_heap <:= (expr_ptr, EI_LetType let_type), cus)

instance clean_up CaseType
where
	clean_up cui ctype=:{ct_pattern_type,ct_result_type, ct_cons_types} cus
		# (ct_pattern_type, cus) = clean_up cui ct_pattern_type cus 
		  (ct_result_type, cus) = clean_up cui ct_result_type cus
		  (ct_cons_types, cus) = clean_up cui ct_cons_types cus
		= ({ctype & ct_pattern_type = ct_pattern_type, ct_cons_types = ct_cons_types, ct_result_type = ct_result_type}, cus)

	
class bind_and_unify_types a :: a a !*TypeVarHeap -> *TypeVarHeap

instance bind_and_unify_types Type
  where
	bind_and_unify_types (TV tv_1) (TV tv_2) type_var_heap
		# (root_1, type_var_heap) = get_root tv_1 type_var_heap
		  (root_2, type_var_heap) = get_root tv_2 type_var_heap
		  maybe_root_tv_1 = only_tv root_1
		  maybe_root_tv_2 = only_tv root_2
		= case (maybe_root_tv_1, maybe_root_tv_2) of
			(Yes root_tv_1, No)
				-> bind_root_variable_to_type root_tv_1 root_2 type_var_heap
			(No, Yes root_tv_2)
				-> bind_root_variable_to_type root_tv_2 root_1 type_var_heap
			(Yes root_tv_1, Yes root_tv_2)
				| root_tv_1.tv_info_ptr==root_tv_2.tv_info_ptr
					-> type_var_heap
				-> bind_roots_together root_tv_1 root_2 type_var_heap
			(No, No)
				-> type_var_heap
	  where
		bind_roots_together :: TypeVar Type *(Heap TypeVarInfo) -> .Heap TypeVarInfo;
		bind_roots_together root_tv_1 root_type_2 type_var_heap
			= type_var_heap <:= (root_tv_1.tv_info_ptr, TVI_Type root_type_2)

	bind_and_unify_types (TV tv_1) type type_var_heap
		| not (is_non_variable_type type)
			= abort "compiler error in typesupport.icl: assertion failed (1)"
		= bind_variable_to_type tv_1 type type_var_heap 
	bind_and_unify_types type (TV tv_1) type_var_heap
		| not (is_non_variable_type type)
			= abort "compiler error in typesupport.icl: assertion failed (2)"
		= bind_variable_to_type tv_1 type type_var_heap
	bind_and_unify_types (TA _ arg_types1) (TA _ arg_types2) type_var_heap
		= bind_and_unify_types arg_types1 arg_types2 type_var_heap
	bind_and_unify_types (l1 --> r1) (l2 --> r2) type_var_heap
		= bind_and_unify_types r1 r2 (bind_and_unify_types l1 l2 type_var_heap)
	bind_and_unify_types (TB _) (TB _) type_var_heap
		= type_var_heap
	bind_and_unify_types ((CV l1) :@: r1) ((CV l2) :@: r2) type_var_heap
		= bind_and_unify_types r1 r2 (bind_and_unify_types (TV l1) (TV l2) type_var_heap)

instance bind_and_unify_types [a] | bind_and_unify_types a
  where
	bind_and_unify_types [] [] type_var_heap
		= type_var_heap
	bind_and_unify_types [x:xs] [y:ys] type_var_heap
		= bind_and_unify_types xs ys (bind_and_unify_types x y type_var_heap)
	
instance bind_and_unify_types AType
  where
	bind_and_unify_types {at_type=t1} {at_type=t2} type_var_heap
			= bind_and_unify_types t1 t2 type_var_heap

only_tv :: u:Type -> Optional u:TypeVar;
only_tv (TV tv) = Yes tv
only_tv _ = No
	
is_non_variable_type :: !Type -> Bool
is_non_variable_type (TA _ _)	= True
is_non_variable_type (_ --> _)	= True
is_non_variable_type (_ :@: _)	= True
is_non_variable_type (TB _)		= True
is_non_variable_type _			= False
	
bind_variable_to_type tv type type_var_heap
	# (root, type_var_heap) = get_root tv type_var_heap
	= case (only_tv root) of
		(Yes tv)	-> bind_root_variable_to_type tv type type_var_heap
		No 			-> type_var_heap
	
bind_root_variable_to_type {tv_info_ptr} type type_var_heap
	= type_var_heap <:= (tv_info_ptr, TVI_Type type)
	
get_root :: TypeVar *(Heap TypeVarInfo) -> (Type,.Heap TypeVarInfo);
get_root this_tv type_var_heap
	# (tv_info, type_var_heap) = readPtr this_tv.tv_info_ptr type_var_heap
	= case tv_info of
		TVI_Empty
			-> (TV this_tv, type_var_heap)
		(TVI_Type type)
			| is_non_variable_type type
				 -> (type, type_var_heap)
			-> case type of
				(TV next_tv) -> get_root next_tv type_var_heap

class substitute a :: !a !u:TypeHeaps -> (!a, !u:TypeHeaps)

instance substitute AType
where
	substitute atype=:{at_attribute,at_type} heaps
		# ((at_attribute,at_type), heaps)  = substitute (at_attribute,at_type) heaps
		= ({ atype & at_attribute = at_attribute, at_type = at_type }, heaps)

instance substitute TypeAttribute
where
	substitute (TA_Var {av_name, av_info_ptr}) heaps=:{th_attrs}
/* MW: was:
		#! av_info = sreadPtr av_info_ptr th_attrs
		# (AVI_Attr attr) = av_info
		= (attr, heaps)
*/
// XXX this alternative's code can be replaced with the original again, when the fusion algorithm becomes able to
// infer correct type attributes
		#! av_info = sreadPtr av_info_ptr th_attrs
		= case av_info of
			 (AVI_Attr attr)	-> (attr, heaps)
			 _ | do_fusion		-> (TA_Multi, heaps)
								-> abort "compiler bug nr 7689 in module typesupport"
	substitute TA_None heaps
		= (TA_Multi, heaps)
	substitute attr heaps
		= (attr, heaps)

instance substitute (a,b) | substitute a & substitute b
where
	substitute (x,y) heaps
		# (x, heaps) = substitute x heaps
		  (y, heaps) = substitute y heaps
		= ((x,y), heaps)
	
instance substitute [a] | substitute a
where
	substitute [] heaps
		= ([], heaps)
	substitute [t:ts] heaps
		# (t, heaps) = substitute t heaps
		  (ts, heaps) = substitute ts heaps
		= ([t:ts], heaps)


instance substitute TypeContext
where
	substitute tc=:{tc_types} heaps
		# (tc_types, heaps) = substitute tc_types heaps
		= ({ tc & tc_types = tc_types }, heaps)

substituteTypeVariable {tv_name,tv_info_ptr} heaps=:{th_vars}
	#! tv_info = sreadPtr tv_info_ptr th_vars
	= case tv_info of
		TVI_Type type
			-> (type, heaps)
		_
			-> abort ("Error in substitute (Type)" ---> (tv_info, tv_name))

instance substitute Type
where
	substitute (TV tv) heaps
		= substituteTypeVariable tv heaps
	substitute (arg_type --> res_type)  heaps
		# ((arg_type, res_type), heaps) = substitute (arg_type, res_type) heaps
		= (arg_type --> res_type, heaps)
	substitute (TA cons_id cons_args)  heaps
		# (cons_args, heaps) = substitute cons_args heaps
		= (TA cons_id cons_args,  heaps)
	substitute (CV type_var :@: types)  heaps
		# (type, heaps) = substituteTypeVariable type_var heaps
		  (types, heaps) = substitute types heaps
		= (simplifyTypeApplication type types, heaps)
	substitute type heaps
		= (type, heaps)

instance substitute AttributeVar
where
	substitute {av_info_ptr} heaps=:{th_attrs}
		#! av_info = sreadPtr av_info_ptr th_attrs
		# (AVI_Attr (TA_Var attr_var)) = av_info
		= (attr_var, heaps)

instance substitute AttrInequality
where
	substitute {ai_demanded,ai_offered} heaps
		# ((ai_demanded, ai_offered), heaps) = substitute (ai_demanded, ai_offered) heaps
		= ({ai_demanded = ai_demanded, ai_offered = ai_offered}, heaps)

instance substitute CaseType
where
	substitute {ct_pattern_type, ct_result_type, ct_cons_types} heaps 
		# (ct_pattern_type, heaps) = substitute ct_pattern_type heaps
		  (ct_result_type, heaps) = substitute ct_result_type heaps
		  (ct_cons_types, heaps) = substitute ct_cons_types heaps
		= ({ct_pattern_type = ct_pattern_type, ct_result_type = ct_result_type, ct_cons_types = ct_cons_types}, heaps)

expandTypeApplication :: ![ATypeVar] !TypeAttribute !Type ![AType] !TypeAttribute !*TypeHeaps -> (!Type, !*TypeHeaps)
expandTypeApplication type_args form_attr type_rhs arg_types act_attr type_heaps=:{th_attrs}
	# th_attrs = bind_attr form_attr act_attr th_attrs 
	= substitute type_rhs (fold2St bind_type_and_attr type_args arg_types { type_heaps & th_attrs = th_attrs })
where
	bind_type_and_attr {atv_attribute = TA_Var {av_name,av_info_ptr}, atv_variable={tv_info_ptr}} {at_attribute,at_type} {th_vars,th_attrs}
		= { th_vars = th_vars <:= (tv_info_ptr, TVI_Type at_type), th_attrs = th_attrs <:= (av_info_ptr, AVI_Attr at_attribute) }
	bind_type_and_attr {atv_variable={tv_info_ptr}} {at_type} type_heaps=:{th_vars}
		= { type_heaps & th_vars = th_vars <:= (tv_info_ptr, TVI_Type at_type) }

	bind_attr (TA_Var {av_name,av_info_ptr}) attr th_attrs
		= th_attrs <:= (av_info_ptr, AVI_Attr attr) 
	bind_attr _ attr th_attrs
		= th_attrs
		

VarIdTable :: {# String}
VarIdTable =: { "a", "b", "c", "d", "e", "f", "g", "h", "i", "j" }

newIdent id_name
	:== { id_name = id_name, id_info = nilPtr }
	
NewVarId var_store
	| var_store < size VarIdTable
		= newIdent VarIdTable.[var_store]
		= newIdent ("v" +++ toString var_store)
 
AttrVarIdTable :: {# String}
AttrVarIdTable =: { "u", "v", "w", "x", "y", "z" }

NewAttrVarId attr_var_store
	| attr_var_store < size AttrVarIdTable
 		= newIdent AttrVarIdTable.[attr_var_store]
		= newIdent ("u" +++ toString attr_var_store)



instance == AttributeVar
where
	(==) av1 av2 = av1.av_info_ptr == av2.av_info_ptr 



class equiv a :: !a !a !*TypeHeaps -> (!Bool, !*TypeHeaps)

instance equiv AType
where
	equiv atype1 atype2 heaps=:{th_attrs}
		# (ok, th_attrs) = equi_attrs atype1.at_attribute atype2.at_attribute th_attrs
		| ok
			= equiv atype1.at_type atype2.at_type { heaps & th_attrs = th_attrs }
			= (False, { heaps & th_attrs = th_attrs })

	where
		equi_attrs attr=:(TA_Var {av_info_ptr}) (TA_TempVar av_number) attr_var_heap
			#! av_info = sreadPtr av_info_ptr attr_var_heap
			= case av_info of
				AVI_Forward forw_var_number
					-> (forw_var_number == av_number, attr_var_heap)
				_
					-> (True, writePtr av_info_ptr (AVI_Forward av_number) attr_var_heap)
		equi_attrs attr1 attr2 attr_env
			= (attr1 == attr2, attr_env)

equivTypeVars :: !TypeVar !TempVarId !*TypeHeaps -> (!Bool, !*TypeHeaps)
equivTypeVars {tv_info_ptr} var_number heaps=:{th_vars}
	#! tv_info = sreadPtr tv_info_ptr th_vars
	= case tv_info of
		TVI_Forward forw_var_number
			-> (forw_var_number == var_number, heaps)
		_
			-> (True, { heaps & th_vars = writePtr tv_info_ptr (TVI_Forward var_number) heaps.th_vars })
	

instance equiv Type
where
	equiv (TV tv) (TempV var_number) heaps
		= equivTypeVars tv var_number heaps
	equiv (arg_type1 --> restype1) (arg_type2 --> restype2) heaps
		= equiv (arg_type1,restype1) (arg_type2,restype2) heaps
	equiv (TA tc1 types1) (TA tc2 types2) heaps
		| tc1 == tc2
			= equiv types1 types2 heaps
			= (False, heaps)
	equiv (TB basic1) (TB basic2) heaps
		= (basic1 == basic2, heaps)
	equiv (CV tv :@: types1) (TempCV var_number :@: types2) heaps
		# (equi_vars, heaps) =  equivTypeVars tv var_number heaps
		| equi_vars
			= equiv types1 types2 heaps
			= (False, heaps)
/*	equiv (TFA vars type1) type2 heaps
		= equiv type1 type2 heaps
	equiv type1 (TFA vars type2) heaps
		= equiv type1 type2 heaps
	equiv (TQV _) (TV _) heaps
		= (True, heaps)
*/
	equiv type1 type2 heaps
		= (False, heaps)

instance equiv (a,b) | equiv a & equiv b
where
	equiv (x1,y1) (x2,y2) heaps
		# (equi_x, heaps) =  equiv x1 x2 heaps
		| equi_x
			= equiv y1 y2 heaps
			= (False, heaps)

instance equiv [a] | equiv a
where
	equiv [x:xs] [y:ys] heaps
		# (equi, heaps) = equiv x y heaps
		| equi
		  	= equiv xs ys heaps
			= (False, heaps)
	equiv [] [] heaps
		= (True, heaps)
	equiv _ _ heaps
		= (False, heaps)

equivalent :: !SymbolType  !TempSymbolType !{# CommonDefs}  !*AttributeEnv !*TypeHeaps -> (!Bool, !*AttributeEnv, !*TypeHeaps) 
equivalent {st_args,st_result,st_context,st_attr_env} {tst_args,tst_result,tst_context,tst_attr_env,tst_lifted} defs attr_env heaps
	#! nr_of_temp_attrs = size attr_env
	# (ok, heaps) = equiv (drop tst_lifted st_args,st_result) (drop tst_lifted tst_args,tst_result) heaps
	| ok
		# (ok, heaps) = equivalent_list_of_contexts st_context tst_context defs heaps
		| ok
			# (ok, attr_env, attr_var_heap) = equivalent_environments st_attr_env (fill_environment tst_attr_env attr_env) heaps.th_attrs
			= (ok, clear_environment tst_attr_env attr_env, { heaps & th_attrs = attr_var_heap })
			= (False, attr_env, heaps)
		= (False, attr_env, heaps)
where
	equivalent_list_of_contexts [] contexts defs heaps 
		= (True, heaps)
	equivalent_list_of_contexts [tc : tcs] contexts defs heaps 
		# (ok, heaps) = contains_context tc contexts defs heaps
		| ok
			= equivalent_list_of_contexts tcs contexts defs heaps
			= (False, heaps)

	contains_context tc1 [tc2 : tcs] defs heaps
		# (ok, heaps) = equivalent_contexts tc1 tc2 defs heaps
		| ok
			= (True, heaps)
			= contains_context tc1 tcs defs heaps
	contains_context tc1 [] defs heaps
		= (False, heaps)
	
	equivalent_contexts tc {tc_class,tc_types} defs heaps
		| tc_class == tc.tc_class
			= equiv tc.tc_types tc_types heaps
		# {glob_object={ds_index},glob_module} = tc_class
		#! class_def = defs.[glob_module].com_class_defs.[ds_index]
		# {class_context,class_args} = class_def
		| isEmpty class_context
			= (False, heaps)
		# th_vars = bind_class_args class_args tc_types heaps.th_vars
		= equivalent_superclasses class_context tc defs { heaps & th_vars = th_vars }
	where	
		bind_class_args [{tv_info_ptr} : vars] [type : types] type_var_heap
			= bind_class_args vars types (writePtr tv_info_ptr (TVI_Type type) type_var_heap)
		bind_class_args [] [] type_var_heap
			= type_var_heap
	
		equivalent_superclasses [] tc defs heaps
			= (False, heaps)
		equivalent_superclasses [super_tc=:{tc_types} : tcs] tc defs heaps=:{th_vars}
			# (tc_types, th_vars) = retrieve_types tc_types th_vars
			  (ok, heaps) = equivalent_contexts { super_tc & tc_types = tc_types } tc defs { heaps & th_vars = th_vars }
			| ok
				= (True, heaps)
				= equivalent_superclasses tcs tc defs heaps
		where
			retrieve_types [TV {tv_info_ptr} : types] type_var_heap
				#! (tv_info, type_var_heap) = readPtr tv_info_ptr type_var_heap
				#  (TVI_Type type) = tv_info
				#! (types, type_var_heap) = retrieve_types types type_var_heap
				= ([type : types], type_var_heap)
			retrieve_types [type : types] type_var_heap
				#! (types, type_var_heap) = retrieve_types types type_var_heap
				= ([type : types], type_var_heap)
			retrieve_types [] type_var_heap
				= ([], type_var_heap)
		

	fill_environment :: ![AttrCoercion] !*{! TypeAttribute} -> *{! TypeAttribute}
	fill_environment [] attr_env
		= attr_env
	fill_environment [{ac_demanded,ac_offered} : coercions ] attr_env
		#! offered = attr_env.[ac_demanded]
		=  fill_environment coercions { attr_env & [ac_demanded] = TA_List ac_offered offered }

	clear_environment :: ![AttrCoercion] !*{! TypeAttribute} -> *{! TypeAttribute}
	clear_environment [] attr_env
		= attr_env
	clear_environment [{ac_demanded,ac_offered} : coercions ] attr_env
		= clear_environment coercions { attr_env & [ac_demanded] = TA_None }
	
	equivalent_environments :: ![AttrInequality] !u:{!TypeAttribute} !v:AttrVarHeap -> (!Bool, !u:{!TypeAttribute}, !v:AttrVarHeap)
	equivalent_environments [] attr_env attr_heap
		= (True, attr_env, attr_heap)
	equivalent_environments [{ai_demanded,ai_offered} : coercions ] attr_env attr_heap
		#! av_info = sreadPtr ai_demanded.av_info_ptr attr_heap
		# (AVI_Forward demanded_var_number) = av_info
		#! av_info = sreadPtr ai_offered.av_info_ptr attr_heap
		# (AVI_Forward offered_var_number) = av_info
		#! offered_of_demanded = attr_env.[demanded_var_number]
		# (succ, attr_env) = contains_coercion offered_var_number offered_of_demanded attr_env
		| succ
			= equivalent_environments coercions attr_env attr_heap
			= (False, attr_env, attr_heap)

	contains_coercion :: !Int !TypeAttribute !u:{! TypeAttribute} -> (!Bool,!u:{!TypeAttribute});
	contains_coercion offered TA_None attr_env
		= (False, attr_env)
	contains_coercion offered (TA_List this_offered next_offered) attr_env
		| offered == this_offered
			= (True, attr_env)
		#! offered_of_offered = attr_env.[this_offered]
		# (succ, attr_env) = contains_coercion offered offered_of_offered attr_env
		| succ
			= (True, attr_env)
			= contains_coercion offered next_offered attr_env

:: Format =
	{	form_properties 	:: !BITVECT
	,	form_attr_position	:: Optional ([Int], Coercions)
	}

cNoProperties		:== 0
cAttributed			:== 1
cAnnotated			:== 2
cMarkAttribute		:== 4

cBrackets			:== 8
cCommaSeparator		:== 16
cArrowSeparator		:== 32

checkProperty	form property	:== not (form.form_properties bitand property == 0)
setProperty		form property	:== {form & form_properties = form.form_properties bitor property}
clearProperty	form property	:== {form & form_properties = form.form_properties bitand (bitnot property)}

class (<::) infixl a :: !*File (!Format, !a) -> *File

instance <:: SymbolType
where
	(<::) file (form, {st_args, st_arity, st_result, st_context, st_attr_env})
		| st_arity > 0
			= show_environment form (show_context form (file <:: (form, st_args) <<< " -> " <:: (form, st_result)) st_context) st_attr_env
			= show_environment form ((show_context form (file <:: (form, st_result))) st_context) st_attr_env
	where
		show_context form file []
			= file
		show_context form file contexts
			= file <<<  " | " <:: (setProperty form cCommaSeparator, contexts)
	
		show_environment form file []
			= file
		show_environment form file environ
			= file <<<  ", " <:: (setProperty form cCommaSeparator, environ)

instance <:: TypeContext
where
	(<::) file (form, {tc_class={glob_object={ds_ident}}, tc_types})
		= file <<< ds_ident <<< ' ' <:: (form, tc_types)

instance <:: AttrInequality
where
	(<::) file (form, {ai_demanded, ai_offered})
		= file <<< ai_offered <<< " <= " <<< ai_demanded

instance <:: AType
where
	(<::) file (form, {at_attribute, at_annotation, at_type})
		| checkProperty form cAnnotated
			= show_attributed_type (file <<< at_annotation) form at_attribute at_type
			= show_attributed_type file form at_attribute at_type
	where
		show_attributed_type file form TA_Multi type
			= file <:: (form, type) 
		show_attributed_type file form attr type
			| checkProperty form cAttributed
				= file <<< attr <:: (setProperty form cBrackets, type)
			| checkProperty form cMarkAttribute
				= show_marked_attribute attr form file <:: (setProperty form cBrackets, type)
				= file <:: (form, type)

		show_marked_attribute attr {form_attr_position = Yes (positions, coercions)} file
			| isEmpty positions
				= show_attribute attr coercions (file <<< "^ ") 
				= show_attribute attr coercions file 

		show_attribute TA_Unique coercions file 
			= file <<< '*' 
		show_attribute TA_Multi coercions file 
			= file 
		show_attribute (TA_TempVar av_number) coercions file 
			| isUniqueAttribute av_number coercions
				= file <<< '*' 
			| isNonUniqueAttribute av_number coercions
				= file 
				= file <<< '.' 

instance <:: Type
where
	(<::) file (form, TV varid)
		= file <<< varid
	(<::) file (form, TempV tv_number)
		= file  <<< 'v' <<< tv_number
	(<::) file (form, TA {type_name,type_index,type_arity} types)
		| is_predefined type_index
			| is_list type_name
				= file <<< '[' <:: (setProperty form cCommaSeparator, types) <<< ']'
			| is_lazy_array type_name
				= file <<< '{' <:: (setProperty form cCommaSeparator, types) <<< '}'
			| is_strict_array type_name
				= file <<< "{!" <:: (setProperty form cCommaSeparator, types) <<< '}'
			| is_unboxed_array type_name
				= file <<< "{#" <:: (setProperty form cCommaSeparator, types) <<< '}'
			| is_tuple type_name type_arity
				= file <<< '(' <:: (setProperty form cCommaSeparator, types) <<< ')'
			| type_arity == 0
				= file <<< type_name
			| checkProperty form cBrackets
				= file <<< '(' <<< type_name <<< ' ' <:: (form, types) <<< ')'
				= file <<< type_name <<< ' ' <:: (setProperty form cBrackets, types)
		| type_arity == 0
			= file <<< type_name
		| checkProperty form cBrackets
			= file <<< '(' <<< type_name <<< ' ' <:: (form, types) <<< ')'
			= file <<< type_name <<< ' ' <:: (setProperty form cBrackets, types)
	where
			is_predefined {glob_module} 	= glob_module == cPredefinedModuleIndex

			is_list {id_name}				= id_name == "_list"
			is_tuple {id_name} tup_arity	= id_name == "_tuple" +++ toString tup_arity
			is_lazy_array {id_name} 		= id_name == "_array"
			is_strict_array {id_name} 		= id_name == "_!array"
			is_unboxed_array {id_name} 		= id_name == "_#array"

	(<::) file (form, arg_type --> res_type)
		| checkProperty form cBrackets
			= file  <<< '(' <:: (clearProperty (setProperty form cArrowSeparator) cBrackets, [arg_type, res_type])  <<< ')'
			= file  <:: (setProperty form (cBrackets bitor cArrowSeparator), [arg_type, res_type])
	(<::) file (form, type :@: types)
		| checkProperty form cBrackets
			= file <<< '(' <<< type <<< ' ' <:: (form, types)  <<< ')'
			= file <<< type <<< ' ' <:: (setProperty form cBrackets, types) 
	(<::) file (form, TB tb)
		= file <<< tb
	(<::) file (form, TQV varid)
		= file <<< "E." <<< varid
	(<::) file (form, TempQV tv_number)
		= file  <<< "E." <<< tv_number <<< ' ' 
	(<::) file (form, TE)
		= file <<< "__"


cNoPosition :== -1
	 
instance <:: [a] | <:: a
where
	(<::) file (form, types)
		= show_list 0 form types file
	where
		show_list elem_number form [type] file
			| checkProperty form cCommaSeparator
				= show_elem elem_number (clearProperty form cCommaSeparator) type file
			| checkProperty form cArrowSeparator
				= show_elem elem_number (clearProperty form cArrowSeparator) type file
				= show_elem elem_number (setProperty form cBrackets) type file
		show_list elem_number form [type : types] file
			| checkProperty form cCommaSeparator
				= show_list (inc elem_number) form types (show_elem elem_number (clearProperty form cCommaSeparator) type file <<< ',')
			| checkProperty form cArrowSeparator
				= show_list (inc elem_number) form types (show_elem elem_number (clearProperty form cArrowSeparator) type file <<< " -> ")
				= show_list (inc elem_number) form types (show_elem elem_number (setProperty form cBrackets) type file <<< ' ')
		show_list elem_number form [] file
			= file

		show_elem elem_nr form=:{form_attr_position = No} type file
			= file <:: (form, type)
		show_elem elem_nr form=:{form_attr_position = Yes ([pos : positions], coercions)} type file
			| elem_nr == pos
				= file <:: ({form & form_attr_position = Yes (positions, coercions)}, type)
			| pos == cNoPosition
				= file <:: (form, type)
				= file <:: ({form & form_attr_position = Yes ([cNoPosition], coercions)}, type)
		show_elem elem_nr form=:{form_attr_position = Yes ([], coercions)} type file
			= file <:: ({form & form_attr_position = Yes ([cNoPosition], coercions)}, type)


from compare_constructor import equal_constructor	

instance == Format
where
	(==) form1 form2 = equal_constructor form1 form2

instance <<< TypeContext
where
	(<<<) file tc = file <<< tc.tc_class.glob_object.ds_ident <<< ' ' <<< tc.tc_types

instance <<< AttrCoercion
where
	(<<<) file {ac_demanded,ac_offered} = file <<< ac_demanded <<< " <= " <<< ac_offered
	
instance <<< TempSymbolType
where
	(<<<) file {tst_args, tst_result, tst_context, tst_attr_env }
		| isEmpty tst_args
			= file <<< tst_result <<< " | " <<< tst_context <<< " [" <<< tst_attr_env <<< ']'
			= file <<< tst_args <<< " -> " <<< tst_result <<< " | " <<< tst_context <<< " [" <<< tst_attr_env <<< ']'

