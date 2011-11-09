implementation module expand_types

import StdEnv
import syntax,predef,containers,utilities

simplifyTypeApplication :: !Type ![AType] -> Type
simplifyTypeApplication type type_args
	# (ok, type)
		=	simplifyAndCheckTypeApplication type type_args
	| not ok
		=	abort "expand_types.simplifyTypeApplication: unexpected error"
	=	type

simplifyAndCheckTypeApplication :: !Type ![AType] -> (!Bool, !Type)
simplifyAndCheckTypeApplication (TA type_cons=:{type_arity} cons_args) type_args
	= (True, TA { type_cons & type_arity = type_arity + length type_args } (cons_args ++ type_args))
simplifyAndCheckTypeApplication (TAS type_cons=:{type_arity} cons_args strictness) type_args
	= (True, TAS { type_cons & type_arity = type_arity + length type_args } (cons_args ++ type_args) strictness)
simplifyAndCheckTypeApplication (CV tv :@: type_args1) type_args2
	= (True, CV tv :@: (type_args1 ++ type_args2))
simplifyAndCheckTypeApplication TArrow [type1, type2] 
	= (True, type1 --> type2)
simplifyAndCheckTypeApplication TArrow [type] 
	= (True, TArrow1 type)
simplifyAndCheckTypeApplication (TArrow1 type1) [type2] 
	= (True, type1 --> type2)
simplifyAndCheckTypeApplication (TV tv) type_args
	= (True, CV tv :@: type_args)
simplifyAndCheckTypeApplication (TempV i) type_args
	= (True, TempCV i :@: type_args)
simplifyAndCheckTypeApplication type type_args
	= (False, type)

readVarInfo :: VarInfoPtr *VarHeap -> (VarInfo, !*VarHeap)
readVarInfo var_info_ptr var_heap
	# (var_info, var_heap) = readPtr var_info_ptr var_heap
	= case var_info of
		VI_Extended _ original_var_info	-> (original_var_info, var_heap)
		_								-> (var_info, var_heap)

writeVarInfo :: VarInfoPtr VarInfo *VarHeap -> *VarHeap
writeVarInfo var_info_ptr new_var_info var_heap
	# (old_var_info, var_heap) = readPtr var_info_ptr var_heap
	= case old_var_info of
		VI_Extended extensions _	-> writePtr var_info_ptr (VI_Extended extensions new_var_info) var_heap
		_							-> writePtr var_info_ptr new_var_info var_heap

RemoveAnnotationsMask:==1
ExpandAbstractSynTypesMask:==2
DontCollectImportedConstructors:==4

convertSymbolType :: !Bool !{#CommonDefs} !SymbolType !Int !*ImportedTypes !ImportedConstructors !*TypeHeaps !*VarHeap 
										  -> (!SymbolType, !*ImportedTypes,!ImportedConstructors,!*TypeHeaps,!*VarHeap)
convertSymbolType rem_annots common_defs st main_dcl_module_n imported_types collected_imports type_heaps var_heap
	# (st, ets_contains_unexpanded_abs_syn_type,ets_type_defs, ets_collected_conses, ets_type_heaps, ets_var_heap)
		= convertSymbolType_  (if rem_annots (RemoveAnnotationsMask bitor ExpandAbstractSynTypesMask) ExpandAbstractSynTypesMask) common_defs st main_dcl_module_n imported_types collected_imports type_heaps var_heap
	= (st, ets_type_defs, ets_collected_conses, ets_type_heaps, ets_var_heap)

convertSymbolTypeWithoutExpandingAbstractSynTypes :: !Bool !{#CommonDefs} !SymbolType !Int
							!*ImportedTypes !ImportedConstructors !*TypeHeaps !*VarHeap 
	-> (!SymbolType, !Bool, !*ImportedTypes,!ImportedConstructors,!*TypeHeaps,!*VarHeap)
convertSymbolTypeWithoutExpandingAbstractSynTypes rem_annots common_defs st main_dcl_module_n imported_types collected_imports type_heaps var_heap
	= convertSymbolType_  (if rem_annots (RemoveAnnotationsMask) 0) common_defs st main_dcl_module_n imported_types collected_imports type_heaps var_heap

convertSymbolTypeWithoutCollectingImportedConstructors :: !Bool !{# CommonDefs} !SymbolType !Int !*ImportedTypes !*TypeHeaps !*VarHeap 
																				-> (!SymbolType, !*ImportedTypes,!*TypeHeaps,!*VarHeap)
convertSymbolTypeWithoutCollectingImportedConstructors rem_annots common_defs st main_dcl_module_n imported_types type_heaps var_heap
	# (st, ets_contains_unexpanded_abs_syn_type,ets_type_defs, ets_collected_conses, ets_type_heaps, ets_var_heap)
		= convertSymbolType_  (if rem_annots (RemoveAnnotationsMask bitor ExpandAbstractSynTypesMask bitor DontCollectImportedConstructors) (ExpandAbstractSynTypesMask bitor DontCollectImportedConstructors)) common_defs st main_dcl_module_n imported_types [] type_heaps var_heap
	= (st, ets_type_defs, ets_type_heaps, ets_var_heap)

convertSymbolType_ :: !Int !{# CommonDefs} !SymbolType !Int !*ImportedTypes !ImportedConstructors !*TypeHeaps !*VarHeap 
	-> (!SymbolType, !Bool,!*ImportedTypes, !ImportedConstructors, !*TypeHeaps, !*VarHeap)
convertSymbolType_  rem_annots common_defs st main_dcl_module_n imported_types collected_imports type_heaps var_heap
	# ets	=	{ ets_type_defs			= imported_types
				, ets_collected_conses	= collected_imports
				, ets_type_heaps		= type_heaps
				, ets_var_heap			= var_heap
				, ets_main_dcl_module_n	= main_dcl_module_n 
				, ets_contains_unexpanded_abs_syn_type = False
				}
	# {st_args,st_result,st_context,st_args_strictness} = st
	#! (_,(st_args,st_result), ets)		= expandSynTypes rem_annots common_defs (st_args,st_result) ets
	# new_st_args						= addTypesOfDictionaries common_defs st_context st_args
	  new_st_arity						= length new_st_args
	  st	=	{ st
	  			& st_args				= new_st_args
	  			, st_result				= st_result
	  			, st_arity				= new_st_arity
	  			, st_args_strictness	= insert_n_strictness_values_at_beginning (new_st_arity-length st_args) st_args_strictness
	  			, st_context			= []
	  			}
	# {ets_type_defs, ets_collected_conses, ets_type_heaps, ets_var_heap,ets_contains_unexpanded_abs_syn_type} = ets
	= (st, ets_contains_unexpanded_abs_syn_type, ets_type_defs, ets_collected_conses, ets_type_heaps, ets_var_heap)

addTypesOfDictionaries :: !{#CommonDefs} ![TypeContext] ![AType] -> [AType]
addTypesOfDictionaries common_defs type_contexts type_args
	= mapAppend (add_types_of_dictionary common_defs) type_contexts type_args
where
	add_types_of_dictionary common_defs {tc_class = TCGeneric {gtc_generic_dict={gi_module,gi_index}}, tc_types}
		#! generict_dict_ident = predefined_idents.[PD_TypeGenericDict]
		/*
			AA HACK:
			Generic classes are always generated locally, 
			and therefore the their dictionaries are also generated localy. 
			Overloaded functions in DCL modules can have generic context restrictions, i.e. they will 
			get generic class dictionaries. 
			Problem: DCL function types refer to ICL type defs of dictionaries.
			Solution: plug a dummy dictinary type, defined in StdGeneric.
			It is possible because all generic class have one class argument and one member.
		*/
		# dict_type_symb = MakeTypeSymbIdent {glob_object = gi_index, glob_module = gi_module} generict_dict_ident 1
		# type_arg = {at_attribute = TA_Multi, at_type=hd tc_types}
		= {at_attribute = TA_Multi, at_type = TA dict_type_symb [type_arg]}

	add_types_of_dictionary common_defs {tc_class = TCClass {glob_module, glob_object={ds_index,ds_ident}}, tc_types}
		# {class_arity, class_dictionary={ds_ident,ds_index}, class_cons_vars}
				= common_defs.[glob_module].com_class_defs.[ds_index]
		  dict_type_symb
		  		= MakeTypeSymbIdent {glob_object = ds_index, glob_module = glob_module} ds_ident class_arity
		  (dict_args,_) = mapSt (\type class_cons_vars
								-> let at_attribute = if (class_cons_vars bitand 1<>0) TA_MultiOfPropagatingConsVar TA_Multi
							   		in ({at_attribute = at_attribute, at_type = type}, class_cons_vars>>1)
						   	) tc_types class_cons_vars
		= {at_attribute = TA_Multi, /* at_annotation = AN_Strict, */ at_type = TA dict_type_symb dict_args}

::	ExpandTypeState =
	{	ets_type_defs			:: !.{#{#CheckedTypeDef}}
	,	ets_collected_conses	:: !ImportedConstructors
	,	ets_type_heaps			:: !.TypeHeaps
	,	ets_var_heap			:: !.VarHeap
	,	ets_main_dcl_module_n :: !Int
	,	ets_contains_unexpanded_abs_syn_type :: !Bool
	}

class expandSynTypes a :: !Int !{# CommonDefs} !a !*ExpandTypeState -> (!Bool,!a, !*ExpandTypeState)

instance expandSynTypes Type
where
	expandSynTypes rem_annots common_defs type=:(arg_type --> res_type) ets
		# (changed,(arg_type, res_type), ets) = expandSynTypes rem_annots common_defs (arg_type, res_type) ets
		| changed
			= (True,arg_type --> res_type, ets)
			= (False,type, ets)
	expandSynTypes rem_annots common_defs type=:(TB _) ets
		= (False,type, ets)
	expandSynTypes rem_annots common_defs type=:(cons_var :@: types) ets
		# (changed,types, ets) = expandSynTypes rem_annots common_defs types ets
		| changed
			= (True,cons_var :@: types, ets)
			= (False,type, ets)
	expandSynTypes rem_annots common_defs type=:(TA type_symb types) ets
		= expand_syn_types_in_TA rem_annots common_defs type TA_Multi ets
	expandSynTypes rem_annots common_defs type=:(TAS type_symb types _) ets
		= expand_syn_types_in_TA rem_annots common_defs type TA_Multi ets
	expandSynTypes rem_annots common_defs tfa_type=:(TFA vars type) ets
		# (changed,type, ets) = expandSynTypes rem_annots common_defs type ets
		| changed
			= (True,TFA vars type, ets)
			= (False,tfa_type, ets)
	expandSynTypes rem_annots common_defs type ets
		= (False,type, ets)

instance expandSynTypes [a] | expandSynTypes a
where
	expandSynTypes rem_annots common_defs [] ets
		= (False,[],ets)
	expandSynTypes rem_annots common_defs t=:[type:types] ets
		#! (changed_type,type,ets)		= expandSynTypes rem_annots common_defs type ets
		   (changed_types,types,ets)	= expandSynTypes rem_annots common_defs types ets
		| changed_type || changed_types
			= (True,[type:types],ets)
			= (False,t,ets)

instance expandSynTypes (a,b) | expandSynTypes a & expandSynTypes b
where
	expandSynTypes rem_annots common_defs (type1,type2) ets
		#! (changed_type1,type1,ets) = expandSynTypes rem_annots common_defs type1 ets
		   (changed_type2,type2,ets) = expandSynTypes rem_annots common_defs type2 ets
		= (changed_type1 || changed_type2,(type1,type2),ets)

instance expandSynTypes AType
where
	expandSynTypes rem_annots common_defs atype ets
		= expand_syn_types_in_a_type rem_annots common_defs atype ets
	where
		expand_syn_types_in_a_type :: !.Int !{#.CommonDefs} !.AType !*ExpandTypeState -> (!.Bool,!AType,!.ExpandTypeState)
		expand_syn_types_in_a_type rem_annots common_defs atype=:{at_type = at_type=: TA type_symb types,at_attribute} ets
			# (changed,at_type, ets) = expand_syn_types_in_TA rem_annots common_defs at_type at_attribute ets
			| changed
				= (True,{ atype & at_type = at_type }, ets)
				= (False,atype,ets)
		expand_syn_types_in_a_type rem_annots common_defs atype=:{at_type = at_type=: TAS type_symb types _,at_attribute} ets
			# (changed,at_type, ets) = expand_syn_types_in_TA rem_annots common_defs at_type at_attribute ets
			| changed
				= (True,{ atype & at_type = at_type }, ets)
				= (False,atype,ets)
		expand_syn_types_in_a_type rem_annots common_defs atype ets
			# (changed,at_type, ets) = expandSynTypes rem_annots common_defs atype.at_type ets
			| changed
				= (True,{ atype & at_type = at_type }, ets)
				= (False,atype,ets)

expand_syn_types_in_TA :: !.Int !{#.CommonDefs} !.Type !.TypeAttribute !*ExpandTypeState -> (!Bool,!Type,!.ExpandTypeState)
expand_syn_types_in_TA rem_annots common_defs ta_type attribute ets=:{ets_type_defs}
	# (glob_object,glob_module,types)	= case ta_type of
		(TA type_symb=:{type_index={glob_object,glob_module},type_ident} types)				-> (glob_object,glob_module,types)
		(TAS type_symb=:{type_index={glob_object,glob_module},type_ident} types strictness)	-> (glob_object,glob_module,types)
	# ({td_rhs,td_ident,td_args,td_attribute},ets_type_defs) = ets_type_defs![glob_module].[glob_object]
	  ets = { ets & ets_type_defs = ets_type_defs }
	= case td_rhs of
		SynType rhs_type
			# (type,ets_type_heaps) = bind_and_substitute_before_expand types td_args td_attribute rhs_type rem_annots attribute ets.ets_type_heaps
			# (_,type,ets) = expandSynTypes rem_annots common_defs type { ets & ets_type_heaps = ets_type_heaps }
			-> (True,type,ets)
		AbstractSynType _ rhs_type
			| (rem_annots bitand ExpandAbstractSynTypesMask)<>0
				# (type,ets_type_heaps) = bind_and_substitute_before_expand types td_args td_attribute rhs_type rem_annots attribute ets.ets_type_heaps
				# (_,type,ets) = expandSynTypes rem_annots common_defs type { ets & ets_type_heaps = ets_type_heaps }
				-> (True,type,ets)

				# ets = {ets & ets_contains_unexpanded_abs_syn_type=True }
				#! (changed,types, ets) = expandSynTypes rem_annots common_defs types ets
				# ta_type = if changed
								( case ta_type of
									TA  type_symb _				-> TA  type_symb types
									TAS type_symb _ strictness	-> TAS type_symb types strictness
								) ta_type
				| glob_module == ets.ets_main_dcl_module_n
					-> (changed,ta_type, ets)
					-> (changed,ta_type, collect_imported_constructors common_defs glob_module td_rhs ets)
		NewType {ds_index}
			# {cons_type={st_args=[arg_type:_]}} = common_defs.[glob_module].com_cons_defs.[ds_index];
			# (type,ets_type_heaps) = bind_and_substitute_before_expand types td_args td_attribute arg_type rem_annots attribute ets.ets_type_heaps
			# (_,type,ets) = expandSynTypes rem_annots common_defs type { ets & ets_type_heaps = ets_type_heaps }
			-> (True,type,ets)
		_
			#! (changed,types, ets) = expandSynTypes rem_annots common_defs types ets
			# ta_type = if changed
							( case ta_type of
								TA  type_symb _				-> TA  type_symb types
								TAS type_symb _ strictness	-> TAS type_symb types strictness
							) ta_type
			| glob_module == ets.ets_main_dcl_module_n || (rem_annots bitand DontCollectImportedConstructors)<>0
				-> (changed,ta_type, ets)
				-> (changed,ta_type, collect_imported_constructors common_defs glob_module td_rhs ets)
where
	bind_and_substitute_before_expand types td_args td_attribute rhs_type rem_annots attribute ets_type_heaps
		# ets_type_heaps = bind_attr td_attribute attribute ets_type_heaps
		  ets_type_heaps = fold2St bind_var_and_attr td_args types ets_type_heaps
		= substitute_rhs rem_annots rhs_type.at_type ets_type_heaps
		where
			bind_var_and_attr {	atv_attribute = TA_Var {av_info_ptr},  atv_variable = {tv_info_ptr} } {at_attribute,at_type} type_heaps=:{th_vars,th_attrs}
				= { type_heaps & th_vars = th_vars <:= (tv_info_ptr, TVI_Type at_type), th_attrs = th_attrs <:= (av_info_ptr, AVI_Attr at_attribute) }
			bind_var_and_attr { atv_variable  = {tv_info_ptr}} {at_type} type_heaps=:{th_vars}
				= { type_heaps & th_vars = th_vars <:= (tv_info_ptr, TVI_Type at_type) }
	
			bind_attr (TA_Var {av_info_ptr}) attribute type_heaps=:{th_attrs}
				= { type_heaps & th_attrs = th_attrs <:= (av_info_ptr, AVI_Attr attribute) }
			bind_attr _ attribute type_heaps
				= type_heaps
	
			substitute_rhs rem_annots rhs_type type_heaps
				| (rem_annots bitand RemoveAnnotationsMask)<>0
					# (_, rhs_type) = removeAnnotations rhs_type
				  	= substitute rhs_type type_heaps
				  	= substitute rhs_type type_heaps

	collect_imported_constructors :: !{#.CommonDefs} !.Int !.TypeRhs !*ExpandTypeState -> .ExpandTypeState
	collect_imported_constructors common_defs mod_index (RecordType {rt_constructor}) ets=:{ets_collected_conses,ets_var_heap}
		# (ets_collected_conses, ets_var_heap)
				= collect_imported_constructor mod_index common_defs.[mod_index].com_cons_defs rt_constructor (ets_collected_conses, ets_var_heap)
		= { ets & ets_collected_conses = ets_collected_conses, ets_var_heap = ets_var_heap }
	collect_imported_constructors common_defs mod_index (AlgType constructors) ets=:{ets_collected_conses,ets_var_heap}
		# (ets_collected_conses, ets_var_heap) 
				= foldSt (collect_imported_constructor mod_index common_defs.[mod_index].com_cons_defs) constructors (ets_collected_conses, ets_var_heap)
		= { ets & ets_collected_conses = ets_collected_conses, ets_var_heap = ets_var_heap }
	collect_imported_constructors common_defs mod_index _ ets
		= ets
	
	collect_imported_constructor :: !.Int !{#.ConsDef} !.DefinedSymbol !*(!u:[v:(Global .Int)],!*(Heap VarInfo)) -> (!w:[x:(Global Int)],!.(Heap VarInfo)), [u <= w,v <= x]
	collect_imported_constructor mod_index cons_defs {ds_index} (collected_conses, var_heap)
		# {cons_type_ptr} = cons_defs.[ds_index]
		  (type_info, var_heap) = readVarInfo cons_type_ptr var_heap
		| has_been_collected type_info
			= (collected_conses, var_heap)
			= ([{ glob_module = mod_index, glob_object = ds_index } : collected_conses ], writeVarInfo cons_type_ptr VI_Used var_heap)
	where
		has_been_collected VI_Used				= True
		has_been_collected (VI_ExpandedType _)	= True
		has_been_collected _					= False

class substitute a :: !a !*TypeHeaps -> (!a, !*TypeHeaps)

instance substitute AType
where
	substitute atype=:{at_attribute,at_type} heaps
		# ((at_attribute,at_type), heaps)  = substitute (at_attribute,at_type) heaps
		= ({ atype & at_attribute = at_attribute, at_type = at_type }, heaps)

instance substitute TypeAttribute
where
	substitute (TA_Var {av_ident, av_info_ptr}) heaps=:{th_attrs}
		#! av_info = sreadPtr av_info_ptr th_attrs
		= case av_info of
			AVI_Attr attr
				-> (attr, heaps)
			_
				-> (TA_Multi, heaps)
	substitute (TA_RootVar {av_info_ptr}) heaps=:{th_attrs}
		#! av_info = sreadPtr av_info_ptr th_attrs
		= case av_info of
			AVI_Attr attr
				-> (attr, heaps)
			_
				-> (TA_Multi, heaps)
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
		= ( [], heaps)
	substitute [t:ts] heaps
		# (t, heaps) = substitute t heaps
		  ( ts, heaps) = substitute ts heaps
		= ([t:ts], heaps)

instance substitute TypeContext
where
	substitute tc=:{tc_types} heaps
		# (tc_types, heaps) = substitute tc_types heaps
		= ({ tc & tc_types = tc_types }, heaps)

instance substitute Type
where
	substitute tv=:(TV {tv_info_ptr}) heaps=:{th_vars}
		# (tv_info, th_vars) = readPtr tv_info_ptr th_vars
		  heaps = {heaps & th_vars = th_vars}
		= case tv_info of
			TVI_Type type
				-> (type, heaps)
			_
				-> (tv, heaps)
	substitute (arg_type --> res_type) heaps
		# ((arg_type, res_type), heaps) = substitute (arg_type, res_type) heaps
		= (arg_type --> res_type, heaps)
	substitute (TArrow1 arg_type) heaps
		# (arg_type, heaps) = substitute arg_type heaps
		= (TArrow1 arg_type, heaps)
	substitute (TA cons_id cons_args) heaps
		# (cons_args, heaps) = substitute cons_args heaps
		= (TA cons_id cons_args,  heaps)
	substitute (TAS cons_id cons_args strictness) heaps
		# (cons_args, heaps) = substitute cons_args heaps
		= (TAS cons_id cons_args strictness,  heaps)
	substitute (CV type_var :@: types) heaps=:{th_vars}
		# (tv_info, th_vars) = readPtr type_var.tv_info_ptr th_vars
		  heaps = {heaps & th_vars = th_vars}
		  (types, heaps) = substitute types heaps
		= case tv_info of
			TVI_Type type
				#  (ok, simplified_type) = simplifyAndCheckTypeApplication type types
				| ok
					-> (simplified_type, heaps)
				// otherwise
					// this will lead to a kind check error later on
					-> 	(CV type_var :@: types, heaps)
			-> 	(CV type_var :@: types, heaps)
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
		= ({ct_pattern_type = ct_pattern_type, ct_result_type = ct_result_type, 
								ct_cons_types = ct_cons_types}, heaps)

class removeAnnotations a :: !a  -> (!Bool, !a)

instance removeAnnotations (a,b) | removeAnnotations a & removeAnnotations b
where
	removeAnnotations t=:(x,y)
		# (rem_x, x) = removeAnnotations x
		  (rem_y, y) = removeAnnotations y
		| rem_x || rem_y
			= (True, (x,y))
			= (False, t)
	
instance removeAnnotations [a] | removeAnnotations a
where
	removeAnnotations l=:[x:xs]
		# (rem_x, x) = removeAnnotations x
		  (rem_xs, xs) = removeAnnotations xs
		| rem_x || rem_xs
			= (True, [x:xs])
			= (False, l)
	removeAnnotations el
		= (False, el)

instance removeAnnotations Type
where
	removeAnnotations t=:(arg_type --> res_type)
		# (rem, (arg_type, res_type)) = removeAnnotations (arg_type, res_type)
		| rem 
			= (True, arg_type --> res_type)
			= (False, t)
	removeAnnotations t=:(TA cons_id cons_args)
		# (rem, cons_args) = removeAnnotations cons_args
		| rem 
			= (True, TA cons_id cons_args)
			= (False, t)
	removeAnnotations t=:(TAS cons_id cons_args _)
		# (rem, cons_args) = removeAnnotations cons_args
		| rem 
			= (True, TA cons_id cons_args)
			= (False, t)
	removeAnnotations t=:(TArrow1 arg_type)
		# (rem, arg_type) = removeAnnotations arg_type
		| rem 
			= (True, TArrow1 arg_type)
			= (False, t)
	removeAnnotations t=:(cv :@: types)
		# (rem, types) = removeAnnotations types
		| rem 
			= (True, cv :@: types)
			= (False, t)
	removeAnnotations type
		= (False, type)

instance removeAnnotations AType
where
	removeAnnotations atype=:{at_type}
		# (rem, at_type) = removeAnnotations at_type
		| rem
			= (True, { atype & at_type = at_type })
			= (False, atype)

instance removeAnnotations SymbolType
where
	removeAnnotations st=:{st_args,st_result,st_args_strictness}
		# (rem, (st_args,st_result)) = removeAnnotations (st_args,st_result)
		| rem
			= (True, { st & st_args = st_args, st_args_strictness=NotStrict, st_result = st_result })
		| is_not_strict st_args_strictness
			= (False, st)
			= (True, { st & st_args_strictness=NotStrict })
