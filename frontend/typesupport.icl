implementation module typesupport

import StdEnv, StdCompare
import syntax, parse, check, unitype, utilities, checktypes // , RWSDebug

// MW: this switch is used to en(dis)able the fusion algorithm
SwitchFusion fuse dont_fuse :== dont_fuse

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

::	FunctionType = CheckedType !SymbolType | SpecifiedType !SymbolType ![AType] !TempSymbolType
				 | UncheckedType !TempSymbolType | ExpandedType !SymbolType !TempSymbolType !TempSymbolType  | EmptyFunctionType


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
	clean_up cui TA_TempExVar cus
		= PA_BUG (TA_Multi, cus) (abort "clean_up cui (TA_TempExVar)")
			
instance clean_up Type
where
	clean_up cui (TempV tv_number) cus
		# (type, cus) = cus!cus_var_env.[tv_number]
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
		# (type, cus) = cus!cus_var_env.[tempvar]
		# (type, cus) = cleanUpVariable cui.cui_top_level type tempvar cus
		  (types, cus) = clean_up cui types cus
		= (simplifyTypeApplication type types, cus)
	clean_up cui (TempQV qv_number) cus=:{cus_error}
		# (type, cus) = cus!cus_var_env.[qv_number]
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


::	CleanUpResult :== BITVECT

cClosed				:== 0
cDefinedVar			:== 1
cUndefinedVar		:== 2
cLiftedVar			:== 4

cleanUpClosedVariable TE env
	= (cUndefinedVar, TE, env)
cleanUpClosedVariable (TLifted tvar) env
	= (cLiftedVar, TV tvar, env)
cleanUpClosedVariable tvar env
	= (cDefinedVar, tvar, env)

combineCleanUpResults cur1 cur2 :== cur1 bitor cur2

checkCleanUpResult cur prop :== not (cur bitand prop == 0)

class cleanUpClosed a :: !a !u:VarEnv -> (!CleanUpResult, !a, !u:VarEnv)

instance cleanUpClosed AType
where
	cleanUpClosed atype=:{at_type} env
		# (cur, at_type, env) = cleanUpClosed at_type env
		= (cur, { atype & at_attribute = TA_Multi, at_type = at_type}, env)

instance cleanUpClosed Type
where
	cleanUpClosed (TempV tv_number) env
		# (type, env) = env![tv_number]
		= cleanUpClosedVariable type env
	cleanUpClosed (TA tc types) env
		# (cur, types, env) = cleanUpClosed types env
		= (cur, TA tc types, env)
	cleanUpClosed (argtype --> restype) env
		# (cur, (argtype,restype), env) = cleanUpClosed (argtype,restype) env
		= (cur, argtype --> restype, env)
	cleanUpClosed (TempCV tv_number :@: types) env
		# (type, env) = env![tv_number]
		# (cur1, type, env) = cleanUpClosedVariable type env
		| checkCleanUpResult cur1 cUndefinedVar
			= (cur1, TempCV tv_number :@: types, env)
			# (cur2, types, env) = cleanUpClosed types env
            = (combineCleanUpResults cur1 cur2, simplifyTypeApplication type types, env)
	cleanUpClosed t env
		= (cClosed, t, env)

instance cleanUpClosed (a,b) | cleanUpClosed a & cleanUpClosed b
where
	cleanUpClosed (x,y) env
		# (cur1, x, env) = cleanUpClosed x env
		| checkCleanUpResult cur1 cUndefinedVar
			= (cur1, (x,y), env)
			# (cur2, y, env) = cleanUpClosed y env
			= (combineCleanUpResults cur1 cur2, (x,y), env)

instance cleanUpClosed [a] | cleanUpClosed a
where
	cleanUpClosed [] env
		= (cClosed, [], env)
	cleanUpClosed [t:ts] env
		# (cur, (t,ts), env) = cleanUpClosed (t,ts) env
		= (cur, [t:ts], env)

errorHeading :: !String !*ErrorAdmin -> *ErrorAdmin
errorHeading  error_kind err=:{ea_file,ea_loc = []}
	= { err & ea_file = ea_file <<< error_kind <<< ':', ea_ok = False }
errorHeading  error_kind err=:{ea_file,ea_loc = [ loc : _ ]}
	= { err & ea_file = ea_file <<< error_kind <<< ' ' <<< loc <<< ':', ea_ok = False }

overloadingError class_symb err
	# err = errorHeading "Overloading error" err
	= { err & ea_file = err.ea_file <<< " internal overloading of class \"" <<< class_symb <<< "\" is unsolvable\n" }

contextError class_symb err
	# err = errorHeading "Overloading error" err
	= { err & ea_file = err.ea_file <<< " unresolved class \"" <<< class_symb <<< "\" not occurring in specified type\n"}

liftedContextError class_symb err
	# err = errorHeading "Overloading error" err
	= { err & ea_file = err.ea_file <<< " type variable of type of lifted argument appears in class \"" <<< class_symb <<< "\"\n"}

existentialError err
	# err = errorHeading "Type error" err
	= { err & ea_file = err.ea_file <<< "existential type variable appears in the derived type specification\n" }

liftedError var err
	# err = errorHeading "Type error" err
	= { err & ea_file = err.ea_file <<< "type variable of type of lifted argument " <<< var <<< " appears in the specified type\n" }

startRuleError mess err
	# err = errorHeading "Type error" err
	= { err & ea_file = err.ea_file <<< mess }

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

cSpecifiedType	:== True
cDerivedType	:== False

cleanUpSymbolType :: !Bool !Bool !TempSymbolType ![TypeContext] ![ExprInfoPtr] !{! CoercionTree} !AttributePartition
						!*VarEnv !*AttributeEnv !*TypeHeaps !*VarHeap !*ExpressionHeap !*ErrorAdmin
							-> (!SymbolType, !*VarEnv, !*AttributeEnv, !*TypeHeaps, !*VarHeap, !*ExpressionHeap, !*ErrorAdmin)
cleanUpSymbolType is_start_rule spec_type tst=:{tst_arity,tst_args,tst_result,tst_context,tst_lifted} derived_context case_and_let_exprs
		coercions attr_part var_env attr_var_env heaps var_heap expr_heap error
	#! nr_of_temp_vars = size var_env
	#! max_attr_nr = size attr_var_env
	# cus = { cus_var_env = var_env, cus_attr_env = attr_var_env, cus_heaps = heaps,
			  cus_var_store = 0, cus_attr_store = 0, cus_error = error }
	  cui = { cui_coercions = coercions, cui_attr_part = attr_part, cui_top_level = True }
	  (lifted_args, cus=:{cus_var_env}) = clean_up cui (take tst_lifted tst_args) cus
	  (lifted_vars, cus_var_env) = determine_type_vars nr_of_temp_vars [] cus_var_env
	  (st_args, cus) = clean_up cui (drop tst_lifted tst_args) { cus & cus_var_env = cus_var_env }
	  (st_result, cus) = clean_up cui tst_result cus
	  (st_context, cus_var_env, var_heap, cus_error) = clean_up_type_contexts spec_type tst_context derived_context cus.cus_var_env var_heap cus.cus_error
	  (st_vars, cus_var_env) = determine_type_vars nr_of_temp_vars lifted_vars cus_var_env
	  (cus_attr_env, st_attr_vars, st_attr_env) = build_attribute_environment 0 max_attr_nr coercions cus.cus_attr_env [] []
	  (expr_heap, {cus_var_env,cus_attr_env,cus_heaps,cus_error}) = update_expression_types { cui & cui_top_level = False } case_and_let_exprs
				expr_heap { cus & cus_var_env = cus_var_env, cus_attr_env = cus_attr_env, cus_error = cus_error }
	  st = {  st_arity = tst_arity, st_vars = st_vars , st_args = lifted_args ++ st_args, st_result = st_result, st_context = st_context,
			st_attr_env = st_attr_env, st_attr_vars = st_attr_vars }
	  cus_error = check_type_of_start_rule is_start_rule st cus_error
	= (st,			{ cus_var_env & [i] = TE \\ i <- [0..nr_of_temp_vars - 1]},
					{ cus_attr_env & [i] = TA_None \\ i <- [0..max_attr_nr - 1]}, cus_heaps, var_heap, expr_heap, cus_error)
//					---> ("cleanUpSymbolType", st)
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

	clean_up_type_contexts spec_type spec_context derived_context env var_heap error
		|  spec_type
			# var_heap = foldSt (mark_specified_context derived_context) spec_context var_heap
			  (rev_contexts, env, error) = foldSt clean_up_lifted_type_context derived_context ([], env, error)
			  (rev_contexts, env, error) = foldSt clean_up_type_context spec_context (rev_contexts, env, error)
			= (reverse rev_contexts, env, var_heap, error)
			# (rev_contexts, env, error) = foldSt clean_up_type_context derived_context ([], env, error)
			= (reverse rev_contexts, env, var_heap, error)

	mark_specified_context [] spec_tc var_heap
		= var_heap
	mark_specified_context [tc=:{tc_var} : tcs] spec_tc var_heap
		| spec_tc == tc
			| spec_tc.tc_var == tc_var
				= var_heap
				= var_heap <:= (spec_tc.tc_var, VI_ForwardClassVar tc_var)
			= mark_specified_context tcs spec_tc var_heap
				
	clean_up_type_context tc=:{tc_types} (collected_contexts, env, error)
		# (cur, tc_types, env) = cleanUpClosed tc.tc_types env
		| checkCleanUpResult cur cUndefinedVar
//			= ([{ tc & tc_types = tc_types } : collected_contexts], env, overloadingError tc.tc_class.glob_object.ds_ident error)
			= (collected_contexts, env, error)
		| checkCleanUpResult cur cLiftedVar
			= ([{ tc & tc_types = tc_types } : collected_contexts ], env, liftedContextError tc.tc_class.glob_object.ds_ident error)
			= ([{ tc & tc_types = tc_types } : collected_contexts ], env, error)

	clean_up_lifted_type_context tc=:{tc_types,tc_var} (collected_contexts, env, error)
		# (cur, tc_types, env) = cleanUpClosed tc.tc_types env
		| checkCleanUpResult cur cLiftedVar
			| checkCleanUpResult cur cDefinedVar
				= (collected_contexts, env, liftedContextError tc.tc_class.glob_object.ds_ident error)
				= ([{ tc & tc_types = tc_types } : collected_contexts], env, error)
		| otherwise
			= (collected_contexts, env, error)
				
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
//		= (expr_heap, cus)
		= foldSt (update_expression_type cui) expr_ptrs (expr_heap, cus)

	update_expression_type cui expr_ptr (expr_heap, cus)
		# (info, expr_heap) = readPtr expr_ptr expr_heap
		= case info of
			EI_CaseType case_type
				# (case_type, cus) = clean_up cui case_type cus
				-> (expr_heap <:= (expr_ptr, EI_CaseType case_type), cus)
			EI_LetType let_type
				# (let_type, cus) = clean_up cui let_type cus
				-> (expr_heap <:= (expr_ptr, EI_LetType let_type), cus)
			EI_DictionaryType dict_type
				# (dict_type, cus) = clean_up cui dict_type cus
				-> (expr_heap <:= (expr_ptr, EI_DictionaryType dict_type), cus)


 	check_type_of_start_rule is_start_rule {st_context,st_arity,st_args} cus_error
 		| is_start_rule
 			| isEmpty st_context
	 			| st_arity > 0
	 				| st_arity == 1
		 				= case st_args of
		 					[{at_type = TB BT_World} : _]
		 						-> cus_error
		 					_
		 						-> startRuleError "argument of Start rule should have type World.\n" cus_error
						= startRuleError "Start rule has too many arguments.\n" cus_error						
					= cus_error						
	 			= startRuleError "Start rule cannot be overloaded.\n" cus_error
	 		= cus_error
	 		
instance clean_up CaseType
where
	clean_up cui ctype=:{ct_pattern_type,ct_result_type, ct_cons_types} cus
		# (ct_pattern_type, cus) = clean_up cui ct_pattern_type cus 
		  (ct_result_type, cus) = clean_up cui ct_result_type cus
		  (ct_cons_types, cus) = clean_up cui ct_cons_types cus
		= ({ctype & ct_pattern_type = ct_pattern_type, ct_cons_types = ct_cons_types, ct_result_type = ct_result_type}, cus)

/*
	In 'bindInstances t1 t2' type variables of t1 are bound to the corresponding subtypes of t2, provided that
	t2 is a substitution instance of t1. Binding is done by setting the 'tv_info_ptr' of the variables of t1
	to 'TVI_Type t' were t is the subtype to which the type variable is matched.
	Be careful with calling 'bindInstances': all the 'tv_info_ptr'-info's should be cleaned first, unless one 
	is sure that t1 does not contain any 'tv_info_ptr' with value  'TVI_Type ...'.
	

	instance bindInstances AType, Type, [a] | bindInstances a
*/ 

updateExpressionTypes :: !SymbolType !SymbolType ![ExprInfoPtr] !*TypeHeaps !*ExpressionHeap -> (!*TypeHeaps, !*ExpressionHeap)
updateExpressionTypes {st_args,st_vars,st_result,st_attr_vars} st_copy type_ptrs heaps=:{th_vars,th_attrs} expr_heap
	# th_vars = foldSt (\{tv_info_ptr} var_heap -> var_heap <:= (tv_info_ptr, TVI_Empty)) st_vars th_vars
	  th_attrs = foldSt (\{av_info_ptr} attr_heap -> attr_heap <:= (av_info_ptr, AVI_Empty)) st_attr_vars th_attrs
	  th_vars = bindInstances st_args st_copy.st_args th_vars
	  th_vars = bindInstances st_result st_copy.st_result th_vars
	= foldSt update_expression_type type_ptrs ({heaps & th_vars = th_vars, th_attrs = th_attrs}, expr_heap)
where
	update_expression_type expr_ptr (type_heaps, expr_heap)
		# (info, expr_heap) = readPtr expr_ptr expr_heap
		= case info of
			EI_CaseType case_type
				# (case_type, type_heaps) = substitute case_type type_heaps
				-> (type_heaps, expr_heap <:= (expr_ptr, EI_CaseType case_type))
			EI_LetType let_type
				# (let_type, type_heaps) = substitute let_type type_heaps
				-> (type_heaps, expr_heap <:= (expr_ptr, EI_LetType let_type))
			EI_DictionaryType dict_type
				# (dict_type, type_heaps) = substitute dict_type type_heaps
				-> (type_heaps, expr_heap <:= (expr_ptr, EI_DictionaryType dict_type))


class bindInstances a :: !a !a !*TypeVarHeap -> *TypeVarHeap

instance bindInstances Type
  where
	bindInstances (TV {tv_info_ptr}) type type_var_heap
		# (tv_info, type_var_heap) = readPtr tv_info_ptr type_var_heap
		= case tv_info of
			TVI_Type ind_type
				-> type_var_heap
			_
				-> type_var_heap <:= (tv_info_ptr, TVI_Type type)
	bindInstances (TA _ arg_types1) (TA _ arg_types2) type_var_heap
		= bindInstances arg_types1 arg_types2 type_var_heap
	bindInstances (l1 --> r1) (l2 --> r2) type_var_heap
		= bindInstances r1 r2 (bindInstances l1 l2 type_var_heap)
	bindInstances (TB _) (TB _) type_var_heap
		= type_var_heap
	bindInstances (CV l1 :@: r1) (CV l2 :@: r2) type_var_heap
		= bindInstances r1 r2 (bindInstances (TV l1) (TV l2) type_var_heap)

instance bindInstances [a] | bindInstances a
  where
	bindInstances [] [] type_var_heap
		= type_var_heap
	bindInstances [x:xs] [y:ys] type_var_heap
		= bindInstances xs ys (bindInstances x y type_var_heap)
	
instance bindInstances AType
  where
	bindInstances {at_type=t1} {at_type=t2} type_var_heap
			= bindInstances t1 t2 type_var_heap


class substitute a :: !a !*TypeHeaps -> (!a, !*TypeHeaps)

instance substitute AType
where
	substitute atype=:{at_attribute,at_type} heaps
		# ((at_attribute,at_type), heaps)  = substitute (at_attribute,at_type) heaps
		= ({ atype & at_attribute = at_attribute, at_type = at_type }, heaps)

instance substitute TypeAttribute
where
	substitute (TA_Var {av_name, av_info_ptr}) heaps=:{th_attrs}
/* 
	This alternative's code can be replaced with the original again, when the fusion algorithm becomes able to
    infer correct type attributes
*/
		#! av_info = sreadPtr av_info_ptr th_attrs
		= case av_info of
			AVI_Attr attr
				-> (attr, heaps)
			_
				-> (TA_Multi, heaps)
/* Sjaak ...				-> SwitchFusion
						(TA_Multi, heaps)
						(abort "compiler bug nr 7689 in module typesupport")
... Sjaak */
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

substituteTypeVariable tv=:{tv_name,tv_info_ptr} heaps=:{th_vars}
	# (tv_info, th_vars) = readPtr tv_info_ptr th_vars
	  heaps = { heaps & th_vars = th_vars }
	= case tv_info of
		TVI_Type type
			-> (type, heaps)
		_
			-> (TV tv, heaps)

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
	substitute av=:{av_info_ptr} heaps=:{th_attrs}
		#! av_info = sreadPtr av_info_ptr th_attrs
		= case av_info of
			AVI_Attr (TA_Var attr_var)
				-> (attr_var, heaps)
			_
				-> (av, heaps)

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
	# type_heaps = bindTypeVarsAndAttributes form_attr act_attr type_args arg_types type_heaps 
	  (exp_type, type_heaps) = substitute type_rhs type_heaps
	= (exp_type, clearBindingsOfTypeVarsAndAttributes form_attr type_args type_heaps)

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

equivalent :: !SymbolType !TempSymbolType !Int !{# CommonDefs}  !*AttributeEnv !*TypeHeaps -> (!Bool, !*AttributeEnv, !*TypeHeaps) 
equivalent st=:{st_args,st_result,st_context,st_attr_env} tst=:{tst_args,tst_result,tst_context,tst_attr_env,tst_lifted} nr_of_contexts defs attr_env heaps
	# nr_of_lifted_contexts = length st_context - nr_of_contexts
	# (ok, heaps) = equiv (drop tst_lifted st_args,st_result) (drop tst_lifted tst_args,tst_result) heaps
	| ok
		# (ok, heaps) = equivalent_list_of_contexts (drop nr_of_lifted_contexts st_context) (drop nr_of_lifted_contexts tst_context) defs heaps
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
		#  (offered, attr_env) = attr_env![ac_demanded]
		=  fill_environment coercions { attr_env & [ac_demanded] = TA_List ac_offered offered }

	clear_environment :: ![AttrCoercion] !*{! TypeAttribute} -> *{! TypeAttribute}
	clear_environment [] attr_env
		= attr_env
	clear_environment [{ac_demanded,ac_offered} : coercions ] attr_env
		= clear_environment coercions { attr_env & [ac_demanded] = TA_None }
	
//	equivalent_environments :: ![AttrInequality] !u:{!TypeAttribute} !v:AttrVarHeap -> (!Bool, !u:{!TypeAttribute}, !v:AttrVarHeap)
	equivalent_environments [] attr_env attr_heap
		= (True, attr_env, attr_heap)
	equivalent_environments [{ai_demanded,ai_offered} : coercions ] attr_env attr_heap
		# (AVI_Forward demanded_var_number, attr_heap) = readPtr ai_demanded.av_info_ptr attr_heap
		  (AVI_Forward offered_var_number, attr_heap) = readPtr ai_offered.av_info_ptr attr_heap
		# (offered_of_demanded, attr_env) = attr_env![demanded_var_number]
		  attr_env = { attr_env & [demanded_var_number] = TA_Locked offered_of_demanded }
		# (succ, locked_attributes, attr_env) = contains_coercion offered_var_number offered_of_demanded [demanded_var_number] attr_env
		| succ
			= equivalent_environments coercions (foldSt unlock_attribute locked_attributes attr_env) attr_heap
			= (False, attr_env, attr_heap)

//	contains_coercion :: !Int !TypeAttribute ![Int] !u:{! TypeAttribute} -> (!Bool, ![Int], !u:{!TypeAttribute})
	contains_coercion offered TA_None locked_attributes attr_env
		= (False, locked_attributes, attr_env)
	contains_coercion offered (TA_List this_offered next_offered) locked_attributes attr_env
		| offered == this_offered
			= (True, locked_attributes, attr_env)
		# (succ, locked_attributes, attr_env) = contains_coercion offered next_offered locked_attributes attr_env
		| succ
			= (True, locked_attributes, attr_env)
		# (offered_of_offered, attr_env) = attr_env![this_offered]
		| is_locked offered_of_offered
			= (False, locked_attributes, attr_env)
			= contains_coercion offered offered_of_offered [this_offered : locked_attributes] { attr_env & [this_offered] = TA_Locked offered_of_offered }
	contains_coercion offered (TA_Locked _) locked_attributes attr_env
		= (False, locked_attributes, attr_env)

	
	unlock_attribute attr_number attr_env
		# (TA_Locked attr, attr_env) = attr_env![attr_number]
		= { attr_env & [attr_number] = attr }
	
	is_locked (TA_Locked _) = True
	is_locked _ 			= False
	
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

(<::) infixl :: !*File (!Format, !a, !Optional TypeVarBeautifulizer) -> *File | writeType a
(<::) file (format, a, opt_beautifulizer)
	# (file, _) = writeType file opt_beautifulizer (format, a)
	= file
	
class writeType a :: !*File !(Optional TypeVarBeautifulizer) (!Format, !a) -> (!*File, !Optional TypeVarBeautifulizer)

instance writeType SymbolType
where
	writeType file opt_beautifulizer (form, {st_args, st_arity, st_result, st_context, st_attr_env})
		# file_opt_beautifulizer
				= case st_arity of
					0
						-> writeType file opt_beautifulizer (form, st_result)
					_
						# (file, opt_beautifulizer)
								= writeType file opt_beautifulizer (form, st_args)
						-> writeType (file <<< " -> ") opt_beautifulizer (form, st_result)
		  (file, opt_beautifulizer)
				= show_context form st_context file_opt_beautifulizer
		= case isEmpty st_attr_env || not (checkProperty form cAttributed) of
			True
				-> (file, opt_beautifulizer)
			False
				# (file, opt_beautifulizer)
					= writeType (file <<< ", [") opt_beautifulizer 
								(setProperty form cCommaSeparator, st_attr_env)
				-> (file <<< ']', opt_beautifulizer)
	where
		show_context form [] file_opt_beautifulizer
			= file_opt_beautifulizer
		show_context form contexts (file, opt_beautifulizer)
			= writeType (file <<< " | ") opt_beautifulizer (setProperty form cCommaSeparator, contexts)

instance writeType TypeContext
where
	writeType file opt_beautifulizer (form, {tc_class={glob_object={ds_ident}}, tc_types})
		= writeType (file <<< ds_ident <<< ' ') opt_beautifulizer (form, tc_types)

instance writeType AttrInequality
where
	writeType file opt_beautifulizer (form, {ai_demanded, ai_offered})
		= (file <<< ai_offered <<< " <= " <<< ai_demanded, opt_beautifulizer)

instance writeType AType
where
	writeType file opt_beautifulizer (form, {at_attribute, at_annotation, at_type})
		| checkProperty form cAnnotated
			= show_attributed_type (file <<< at_annotation) opt_beautifulizer form at_attribute at_type
			= show_attributed_type file opt_beautifulizer form at_attribute at_type
	where
		show_attributed_type file opt_beautifulizer form TA_Multi type
			| checkProperty form cMarkAttribute
				# (file, opt_beautifulizer)
					= show_marked_attribute TA_Multi form file opt_beautifulizer
				= writeType file opt_beautifulizer (form, type)
				= writeType file opt_beautifulizer (form, type) 
		show_attributed_type file opt_beautifulizer form attr type
			| checkProperty form cAttributed
				= writeType (file <<< attr) opt_beautifulizer (setProperty form cBrackets, type)
			| checkProperty form cMarkAttribute
				# (file, opt_beautifulizer)
					= show_marked_attribute attr form file opt_beautifulizer
				= writeType file opt_beautifulizer (setProperty form cBrackets, type)
				= writeType file opt_beautifulizer (form, type)

		show_marked_attribute attr {form_attr_position = Yes (positions, coercions)} file opt_beautifulizer
			| isEmpty positions
				= show_attribute attr coercions (file <<< "^ ") opt_beautifulizer
				= show_attribute attr coercions file opt_beautifulizer
					 

		show_attribute TA_Unique coercions file opt_beautifulizer
			= (file <<< '*' , opt_beautifulizer)
		show_attribute TA_Multi coercions file opt_beautifulizer
			= (file, opt_beautifulizer)
		show_attribute (TA_TempVar av_number) coercions file opt_beautifulizer
			| isUniqueAttribute av_number coercions
				= (file <<< '*', opt_beautifulizer)
			| isNonUniqueAttribute av_number coercions
				= (file, opt_beautifulizer)
				= (file <<< '.' <<< "[[" <<< av_number <<< "]]", opt_beautifulizer)
		show_attribute TA_TempExVar coercions file opt_beautifulizer
			= PA_BUG (file <<< "(E)", opt_beautifulizer) (abort "show_attribute TA_TempExVar")

instance writeType Type
where
	writeType file No (form, TV varid)
		= (file <<< varid, No)
	writeType file No (form, TempV tv_number)
		= (file  <<< 'v' <<< tv_number, No)
	writeType file opt_beautifulizer (form, TA {type_name,type_index,type_arity} types)
		| is_predefined type_index
			| is_list type_name
				= writeWithinBrackets "[" "]" file opt_beautifulizer (setProperty form cCommaSeparator, types)
			| is_lazy_array type_name
				= writeWithinBrackets "{" "}" file opt_beautifulizer (setProperty form cCommaSeparator, types)
			| is_strict_array type_name
				= writeWithinBrackets "{!" "}" file opt_beautifulizer (setProperty form cCommaSeparator, types)
			| is_unboxed_array type_name
				= writeWithinBrackets "{#" "}" file opt_beautifulizer (setProperty form cCommaSeparator, types)
			| is_tuple type_name type_arity
				= writeWithinBrackets "(" ")" file opt_beautifulizer (setProperty form cCommaSeparator, types)
			| type_arity == 0
				= (file <<< type_name, opt_beautifulizer)
			| checkProperty form cBrackets
				# (file, opt_beautifulizer)
						= writeType (file <<< '(' <<< type_name <<< ' ') opt_beautifulizer (form, types)
				= (file <<< ')', opt_beautifulizer)
				= writeType (file <<< type_name <<< ' ') opt_beautifulizer (setProperty form cBrackets, types)
		| type_arity == 0
			= (file <<< type_name, opt_beautifulizer)
		| checkProperty form cBrackets
			# (file, opt_beautifulizer)
					= writeType (file <<< '(' <<< type_name <<< ' ') opt_beautifulizer (form, types)
			= (file <<< ')', opt_beautifulizer)
			= writeType (file <<< type_name <<< ' ') opt_beautifulizer (setProperty form cBrackets, types)
	where
			is_predefined {glob_module} 	= glob_module == cPredefinedModuleIndex

			is_list {id_name}				= id_name == "_list"
			is_tuple {id_name} tup_arity	= id_name == "_tuple" +++ toString tup_arity
			is_lazy_array {id_name} 		= id_name == "_array"
			is_strict_array {id_name} 		= id_name == "_!array"
			is_unboxed_array {id_name} 		= id_name == "_#array"

// MW4 was:	writeType file (form, arg_type --> res_type)
	writeType file opt_beautifulizer (form, arg_type --> res_type)
		| checkProperty form cBrackets
			= writeWithinBrackets "(" ")" file opt_beautifulizer
									(clearProperty (setProperty form cArrowSeparator) cBrackets, [arg_type, res_type])
			= writeType file opt_beautifulizer (setProperty form (cBrackets bitor cArrowSeparator), [arg_type, res_type])
	writeType file opt_beautifulizer (form, type :@: types)
		| checkProperty form cBrackets
			# (file, opt_beautifulizer)
					= writeType (file <<< '(' <<< type <<< ' ') opt_beautifulizer (form, types)
			= (file <<< ')', opt_beautifulizer)
			= writeType (file <<< type <<< ' ') opt_beautifulizer (setProperty form cBrackets, types) 
	writeType file opt_beautifulizer (form, TB tb)
		= (file <<< tb, opt_beautifulizer)
	writeType file No (form, TQV varid)
		= (file <<< "E." <<< varid, No)
	writeType file No (form, TempQV tv_number)
		= (file  <<< "E." <<< tv_number <<< ' ', No)
	writeType file opt_beautifulizer (form, TE)
		= (file <<< "__", opt_beautifulizer)
	writeType file (Yes beautifulizer) (form, type_variable)
		= writeBeautifulTypeVar file beautifulizer type_variable
	writeType file _ (form, type)
		= abort ("<:: (Type) (typesupport.icl)" ---> type)

writeWithinBrackets br_open br_close file opt_beautifulizer (form, types)
	# (file, opt_beautifulizer) 
			= writeType (file <<< br_open) opt_beautifulizer (form, types)
	= (file <<< br_close, opt_beautifulizer)

writeBeautifulTypeVar file beautifulizer=:{tvb_visited, tvb_fresh_vars} type_variable
	| sanity_check_failed type_variable
		= abort "bug nr 12345 in module typesupport"
	= case lookup type_variable tvb_visited of
		No
			-> (file <<< hd tvb_fresh_vars, Yes { tvb_visited = [(type_variable, hd tvb_fresh_vars):tvb_visited],
													tvb_fresh_vars = tl tvb_fresh_vars })
		Yes (_, beautiful_var_name)
			-> (file <<< beautiful_var_name, Yes beautifulizer)
  where
	lookup _ [] = No
	lookup t1 [hd=:(t2, _):tl]
		| t1==t2
			= Yes hd
		= lookup t1 tl

	sanity_check_failed (GTV _)		= False
	sanity_check_failed (TV _)		= False
	sanity_check_failed (TempV _)	= False
	sanity_check_failed (TQV _)		= False
	sanity_check_failed (TempQV _)	= False
	sanity_check_failed (TLifted _)	= False
	sanity_check_failed _			= True
	
cNoPosition :== -1
	 
instance writeType [a] | writeType a
where
	writeType file opt_beautifulizer (form, types)
		= show_list 0 form types (file, opt_beautifulizer)
	where
		show_list elem_number form [type] file_opt_beautifulizer
			| checkProperty form cCommaSeparator
				= show_elem elem_number (clearProperty form cCommaSeparator) type file_opt_beautifulizer
			| checkProperty form cArrowSeparator
				= show_elem elem_number (clearProperty form cArrowSeparator) type file_opt_beautifulizer
				= show_elem elem_number (setProperty form cBrackets) type file_opt_beautifulizer
		show_list elem_number form [type : types] file_opt_beautifulizer
			# (elem_format, seperator)
					= if (checkProperty form cCommaSeparator) (clearProperty form cCommaSeparator, ",")
						(if (checkProperty form cArrowSeparator) (clearProperty form cArrowSeparator, " -> ")
							(setProperty form cBrackets, " "))
			  (file, opt_beautifulizer)
			  		= show_elem elem_number elem_format type file_opt_beautifulizer
			= show_list (inc elem_number) form types (file <<< seperator, opt_beautifulizer)
		show_list elem_number form [] file
			= file

		show_elem elem_nr form=:{form_attr_position = No} type (file, opt_beautifulizer)
			= writeType file opt_beautifulizer (form, type)
		show_elem elem_nr form=:{form_attr_position = Yes ([pos : positions], coercions)} type (file, opt_beautifulizer)
			| elem_nr == pos
				= writeType file opt_beautifulizer ({form & form_attr_position = Yes (positions, coercions)}, type)
			| pos == cNoPosition
				= writeType file opt_beautifulizer (form, type)
				= writeType file opt_beautifulizer ({form & form_attr_position = Yes ([cNoPosition], coercions)}, type)
		show_elem elem_nr form=:{form_attr_position = Yes ([], coercions)} type (file, opt_beautifulizer)
			= writeType file opt_beautifulizer ({form & form_attr_position = Yes ([cNoPosition], coercions)}, type)

from compare_constructor import equal_constructor	

instance == Format
where
	(==) form1 form2 = equal_constructor form1 form2

instance <<< TypeContext
where
	(<<<) file co = file <<< co.tc_class.glob_object.ds_ident <<< " <" <<< ptrToInt co.tc_var <<< '>' <<< " " <<< co.tc_types
	

instance <<< AttrCoercion
where
	(<<<) file {ac_demanded,ac_offered} = file <<< ac_demanded <<< " <= " <<< ac_offered
	
instance <<< TempSymbolType
where
	(<<<) file {tst_args, tst_result, tst_context, tst_attr_env }
		| isEmpty tst_args
			= file <<< tst_result <<< " | " <<< tst_context <<< " [" <<< tst_attr_env <<< ']'
			= file <<< tst_args <<< " -> " <<< tst_result <<< " | " <<< tst_context <<< " [" <<< tst_attr_env <<< ']'

// MW4..
:: TypeVarBeautifulizer =
	{	tvb_visited 	:: ![(Type, String)]
			// associates type variables with strings, the type should be only GTV, TV, TempV, TQV, TempQV, TLifted.
			// (associations lists are slow but cool)
	,	tvb_fresh_vars	::	![String]
	}

initialTypeVarBeautifulizer :: TypeVarBeautifulizer
initialTypeVarBeautifulizer 
	= {	tvb_visited = [], tvb_fresh_vars = fresh_vars 'a' (-1) }
  where
	fresh_vars 'i' i
		= fresh_vars 'a' (i+1)
	fresh_vars ch i
		= [if (i==(-1)) (toString ch) (toString ch+++toString i): fresh_vars (inc ch) i]
