implementation module typesupport

import StdEnv, StdCompare
import syntax, parse, check, unitype, utilities, RWSDebug

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

class emptyValue a :: a

instance emptyValue TypeAttribute
where
	emptyValue = TA_None
	
instance emptyValue Type
where
	emptyValue = TE


lookUp :: !a !(Env a b) -> (!Bool, !b) | ==, toString a & emptyValue b
lookUp elem_id [] 
		= (False, emptyValue)
lookUp elem_id [b : bs]
	| elem_id == b.bind_src
		= (True, b.bind_dst)
		= lookUp elem_id bs

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


class clean_up a ::  !(!{! CoercionTree}, !AttributePartition) !a !*CleanUpState -> (!a, !*CleanUpState)

instance clean_up AType
where
	clean_up coercions atype=:{at_attribute,at_type} cus
		# (at_attribute, cus) = clean_up coercions at_attribute cus 
		  (at_type, cus) = clean_up coercions at_type cus
		= ({atype & at_attribute = at_attribute, at_type = at_type}, cus)

attrIsUndefined TA_None = True
attrIsUndefined _ 		= False

varIsDefined TE		= False
varIsDefined _ 		= True

instance clean_up TypeAttribute
where
	clean_up coercions TA_Unique cus
		= (TA_Unique, cus)
	clean_up coercions TA_Multi cus
		= (TA_Multi, cus)
	clean_up (coercions, attr_part) tv=:(TA_TempVar av_number) cus=:{cus_attr_env,cus_heaps,cus_attr_store,cus_error}
		# av_group_nr = attr_part.[av_number]
		  coercion_tree = coercions.[av_group_nr]
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
				
instance clean_up Type
where
	clean_up coercions (TempV tv_number) cus=:{cus_var_env}
		#! type = cus_var_env.[tv_number]
		= cleanUpVariable type tv_number cus
	clean_up coercions (TA tc types) cus
		# (types, cus) = clean_up coercions types cus
		= (TA tc types, cus)
	clean_up coercions (argtype --> restype) cus
		# (argtype, cus) = clean_up coercions argtype cus
		  (restype, cus) = clean_up coercions restype cus
		=  (argtype --> restype, cus)
	clean_up coercions t=:(TB _) cus
		=  (t, cus)
	clean_up coercions (TempCV tempvar :@: types) cus
		#! type = cus.cus_var_env.[tempvar]
		# (type, cus) = cleanUpVariable type tempvar cus
		  (types, cus) = clean_up coercions types cus
		= (simplifyTypeApplication type types, cus)
	clean_up coercions (TempQV qv_number) cus=:{cus_var_env,cus_error}
		#! type = cus_var_env.[qv_number]
		= cleanUpVariable type qv_number {cus & cus_error = existentialError cus_error}
	clean_up coercions TE cus
		= abort "unknown pattern in function clean_up"
				
instance clean_up [a] | clean_up a
where
	clean_up coercions l cus = mapSt (clean_up coercions) l cus

cleanUpVariable TE tv_number cus=:{cus_heaps,cus_var_store,cus_var_env}
	# (tv_info_ptr, th_vars) = newPtr TVI_Empty cus_heaps.th_vars
	  new_var = TV { tv_name = NewVarId cus_var_store, tv_info_ptr = tv_info_ptr }
	= (new_var, { cus & cus_var_env = { cus_var_env & [tv_number] = new_var},
				cus_heaps = { cus_heaps & th_vars = th_vars }, cus_var_store = inc cus_var_store})
cleanUpVariable (TLifted var) tv_number cus=:{cus_error}
	= (TV var, { cus & cus_error = liftedError var cus_error})
cleanUpVariable type tv_number cus
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

TypeError :: !String !mess !String !*ErrorAdmin -> *ErrorAdmin | <<< mess
TypeError err_pref err_msg err_post err=:{ea_file,ea_loc}
	| isEmpty ea_loc
		# ea_file =  ea_file <<< "Type error: " <<< err_pref <<< ' ' <<< err_msg <<< ' ' <<< err_post <<< '\n'
		= { err & ea_file = ea_file, ea_ok = False}
		# ea_file =  ea_file <<< "Type error " <<< hd ea_loc <<< ": " <<< err_pref <<< ' ' <<< err_msg <<< ' ' <<< err_post <<< '\n'
		= { err & ea_file = ea_file, ea_ok = False}
		

overloadingError class_symb err
	= TypeError "internal overloading of class" class_symb "is unsolvable" err

existentialError err
	= TypeError "existential" "type variable" "appears in the derived type specification" err

liftedError var err
	= TypeError "type variable of type of lifted argument" var "appears in the specified type" err

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

cleanUpSymbolType :: !TempSymbolType ![TypeContext] !{! CoercionTree} !AttributePartition !*VarEnv !*AttributeEnv !*TypeHeaps !*ErrorAdmin
	-> (!SymbolType, !*VarEnv, !*AttributeEnv, !*TypeHeaps, !*ErrorAdmin)
cleanUpSymbolType tst=:{tst_arity,tst_args,tst_result,tst_context,tst_lifted} context coercions attr_part var_env attr_var_env heaps error
	#! nr_of_temp_vars = size var_env
	#! max_attr_nr = size attr_var_env
	# cus = { cus_var_env = var_env, cus_attr_env = attr_var_env, cus_heaps = heaps,
			  cus_var_store = 0, cus_attr_store = 0, cus_error = error }
	  (lifted_args, cus=:{cus_var_env}) = clean_up (coercions,attr_part) (take tst_lifted tst_args) cus
	  (lifted_vars, cus_var_env) = determine_type_vars nr_of_temp_vars [] cus_var_env
	  (st_args, cus) = clean_up (coercions,attr_part) (drop tst_lifted tst_args) { cus & cus_var_env = cus_var_env }
	  (st_result, {cus_var_env,cus_attr_env,cus_heaps,cus_error}) = clean_up (coercions,attr_part) tst_result cus
	  (st_context, cus_var_env, error) = clean_up_type_contexts (tst_context ++ context) cus_var_env cus_error
	  (st_vars, var_env) = determine_type_vars nr_of_temp_vars lifted_vars cus_var_env
	  (attr_env, st_attr_vars, st_attr_env) = build_attribute_environment 0 max_attr_nr coercions cus_attr_env [] []
	  st = {  st_arity = tst_arity, st_vars = st_vars , st_args = lifted_args ++ st_args, st_result = st_result, st_context = st_context,
			st_attr_env = st_attr_env, st_attr_vars = st_attr_vars }
	= (st,{ var_env & [i] = TE \\ i <- [0..nr_of_temp_vars - 1]}, { attr_env & [i] = TA_None \\ i <- [0..max_attr_nr - 1]}, cus_heaps, error)
//			---> (tst, st)
where
	determine_type_var var_index (all_vars, var_env)
		#! type = var_env.[var_index]
		= case type of
			TV var
				-> ([var : all_vars], { var_env & [var_index] = TLifted var})
			_
				-> (all_vars, var_env)

	determine_type_vars to_index all_vars var_env
		= iFoldSt determine_type_var 0 to_index (all_vars, var_env)
	
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
	

		
/*
	build_inequalities :: !AttributeVar !(Env Int TypeAttribute) !Int !{# Bool} !Int !Int ![AttrInequality] -> [AttrInequality]
	build_inequalities off_var attr_var_env next_var_number dem_vars skip size inequalities
		| next_var_number == size
			= inequalities
		| dem_vars.[next_var_number] && next_var_number <> skip
			# (found, TA_Var dem_var) = lookUp next_var_number attr_var_env
			| found
				# inequalities = [ { ai_demanded = dem_var, ai_offered = off_var } : inequalities]
				= build_inequalities off_var attr_var_env (inc next_var_number) dem_vars skip size inequalities
				= build_inequalities off_var attr_var_env (inc next_var_number) dem_vars skip size inequalities
			= build_inequalities off_var attr_var_env (inc next_var_number) dem_vars skip size inequalities

clean_up_symbol_type :: !SymbolType ![TypeContext] !*ErrorAdmin -> (!SymbolType, !*ErrorAdmin)
clean_up_symbol_type st=:{st_args,st_result,st_context} context error
	# (st_args, var_env, attr_var_env, var_store, error) = clean_up_argument_types st_args [] [] 0 error
	  (st_result, var_env, attr_var_env, var_store, error) = clean_up_result_type st_result var_env attr_var_env var_store error
	  new_env = attr_var_env ++ var_env 
	  (st_context, error) = clean_up_type_contexts (st_context ++ context) new_env error
	= ({ st & st_vars = map (\bind=:{bind_dst = TV tv} -> tv) new_env, st_args = st_args, st_result = st_result, st_context = st_context }, error)


clean_up_type type var_binds uq_var_binds var_store error
	# (type, var_binds, new_uq_var_binds, var_store) = clean_up type var_binds [] var_store
 	  error = check_uq_vars new_uq_var_binds uq_var_binds error
 	| isEmpty new_uq_var_binds
		= (type, var_binds, new_uq_var_binds ++ uq_var_binds, var_store, error)
		= (TFA [ var \\ {bind_dst=TV var} <- new_uq_var_binds ] type, var_binds, new_uq_var_binds ++ uq_var_binds, var_store, error)
		

quantifiction_error err=:{ea_file}
	# ea_file = ea_file <<< "Type error: Introduction of universal quantifier failed\n"
	= { err & ea_file = ea_file}

check_uq_vars [] uq_var_binds error = error
check_uq_vars [b:bs] uq_var_binds error
	# (found, var) = lookUp b.bind_src uq_var_binds 
	| found 
		= quantifiction_error error
		= check_uq_vars bs uq_var_binds error

clean_up_argument_types [] var_binds uq_var_binds var_store error
	= ([], var_binds, uq_var_binds, var_store, error)
clean_up_argument_types [t:ts] var_binds uq_var_binds var_store error
	# (t, var_binds, uq_var_binds, var_store, error) = clean_up_type t var_binds uq_var_binds var_store error
 	  (ts, var_binds, uq_var_binds, var_store, error) = clean_up_argument_types ts var_binds uq_var_binds var_store error
	= ([t:ts], var_binds, uq_var_binds, var_store, error)

clean_up_result_type (argtype --> restype) var_binds uq_var_binds var_store error
	# (argtype, var_binds, uq_var_binds, var_store, error) = clean_up_type argtype var_binds uq_var_binds var_store error
	  (restype, var_binds, uq_var_binds, var_store, error) = clean_up_result_type restype var_binds uq_var_binds var_store error
	= (argtype --> restype, var_binds, uq_var_binds, var_store, error)
clean_up_result_type type var_binds uq_var_binds var_store error
	# (type, var_binds, new_uq_var_binds, var_store) = clean_up type var_binds [] var_store
 	  error = check_uq_vars new_uq_var_binds uq_var_binds error
	= (type, var_binds, new_uq_var_binds, var_store, error)

*/

	
class substitute a :: !a !u:TypeHeaps -> (!a, !u:TypeHeaps)

instance substitute AType
where
	substitute atype=:{at_attribute,at_type} heaps
		# ((at_attribute,at_type), heaps)  = substitute (at_attribute,at_type) heaps
		= ({ atype & at_attribute = at_attribute, at_type = at_type }, heaps)

instance substitute TypeAttribute
where
	substitute (TA_Var {av_name, av_info_ptr}) heaps=:{th_attrs}
		#! av_info = sreadPtr av_info_ptr th_attrs
		# (AVI_Attr attr) = av_info
		= (attr, heaps)
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


/*	
class equiv a :: !a !a !*VarEnv !*AttributeEnv  -> (!Bool, !*VarEnv, !*AttributeEnv)

instance equiv AType
where
	equiv atype1 atype2 var_env attr_env
		# (ok, attr_env) = equi_attrs atype1.at_attribute atype2.at_attribute attr_env
		| ok
			= equiv atype1.at_type atype2.at_type var_env attr_env
			= (False, var_env, attr_env)
	where
		equi_attrs (TA_TempVar av_number) attr=:(TA_Var attr_var) attr_env
			#! forw_attr = attr_env.[av_number]
			= case forw_attr of
				TA_None
					-> (True, { attr_env & [av_number] = attr})
			  	TA_Var forw_var
			  		-> (forw_var == attr_var, attr_env)
			  	_
			  		-> abort "Error in equiv (AType)"
		equi_attrs attr1 attr2 attr_env
			= (attr1 == attr2, attr_env)
		
instance equiv Type
where
	equiv (TempV tv_number) type=:(TV var) var_env attr_env
		#! forw_type = var_env.[tv_number]
		= case forw_type of
			TE
				-> (True, { var_env & [tv_number] = type }, attr_env)
			TV forw_var
				-> (forw_var == var, var_env, attr_env)
			_
				-> abort "Error in equiv (Type)"
	equiv (arg_type1 --> restype1) (arg_type2 --> restype2) var_env attr_env
		= equiv (arg_type1,restype1) (arg_type2,restype2) var_env attr_env
	equiv (TA tc1 types1) (TA tc2 types2) var_env attr_env
		| tc1 == tc2
			= equiv types1 types2 var_env attr_env
			= (False, var_env, attr_env)
	equiv (TB basic1) (TB basic2) var_env attr_env
		= (basic1 == basic2, var_env, attr_env)
	equiv (type1 :@: types1) (type2 :@: types2) var_env attr_env
		= equiv (type1,types1) (type2,types2) var_env attr_env
/*	equiv (TFA vars type1) type2 var_env attr_env
		= equiv type1 type2 var_env attr_env
	equiv type1 (TFA vars type2) var_env attr_env
		= equiv type1 type2 var_env attr_env
	equiv (TQV _) (TV _) var_env attr_env
		= (True, var_env attr_env)
*/
	equiv type1 type2 var_env attr_env
		= (False, var_env, attr_env)

instance equiv (a,b) | equiv a & equiv b
where
	equiv (x1,y1) (x2,y2) var_env attr_env
		# (equi_x, var_env, attr_env) =  equiv x1 x2 var_env attr_env
		| equi_x
			= equiv y1 y2 var_env attr_env
			= (False, var_env, attr_env)

instance equiv [a] | equiv a
where
	equiv [x:xs] [y:ys] var_env attr_env
		# (equi, var_env, attr_env) = equiv x y var_env attr_env
		| equi
		  	= equiv xs ys var_env attr_env
			= (False, var_env, attr_env)
	equiv [] [] var_env attr_env
		= (True, var_env, attr_env)
	equiv _ _ var_env attr_env
		= (False, var_env, attr_env)
*/

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

