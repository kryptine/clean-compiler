implementation module comparedefimp

import syntax, checksupport, compare_constructor, utilities, StdCompare, compilerSwitches

::	CompareState =
	{	comp_type_var_heap	:: !.TypeVarHeap
	,	comp_attr_var_heap	:: !.AttrVarHeap
	,	comp_error			:: !.ErrorAdmin
	}
	
type_def_error		= "type definition in the impl module conflicts with the def module"
class_def_error		= "class definition in the impl module conflicts with the def module"
instance_def_error	= "instance definition in the impl module conflicts with the def module"

compareError message pos error_admin
	= popErrorAdmin (checkError "" message (pushErrorAdmin pos error_admin))

compareTypeDefs ::  !{# Int} !{#Bool} !{# CheckedTypeDef} !{# ConsDef} !u:{# CheckedTypeDef} !v:{# ConsDef} !*CompareState
	-> (!u:{# CheckedTypeDef}, !v:{# ConsDef}, !*CompareState) 
compareTypeDefs dcl_sizes copied_from_dcl dcl_type_defs dcl_cons_defs icl_type_defs icl_cons_defs comp_st
	# nr_of_dcl_types = dcl_sizes.[cTypeDefs]
	= iFoldSt (compare_type_defs copied_from_dcl dcl_type_defs dcl_cons_defs) 0 nr_of_dcl_types (icl_type_defs, icl_cons_defs, comp_st)
where
	compare_type_defs :: !{# Bool} !{# CheckedTypeDef} !{# ConsDef} !Index (!u:{# CheckedTypeDef}, !v:{# ConsDef}, !*CompareState)
		-> (!u:{# CheckedTypeDef}, !v:{# ConsDef}, !*CompareState) 
	compare_type_defs copied_from_dcl dcl_type_defs dcl_cons_defs type_index (icl_type_defs, icl_cons_defs, comp_st=:{comp_type_var_heap,comp_attr_var_heap})
		| not copied_from_dcl.[type_index]
			# dcl_type_def = dcl_type_defs.[type_index]
			  (icl_type_def, icl_type_defs) = icl_type_defs![type_index]
			  comp_type_var_heap = initialyseATypeVars dcl_type_def.td_args comp_type_var_heap
			  comp_type_var_heap = initialyseATypeVars icl_type_def.td_args comp_type_var_heap
			  comp_attr_var_heap = initialyseAttributeVars dcl_type_def.td_attrs comp_attr_var_heap
			  comp_attr_var_heap = initialyseAttributeVars icl_type_def.td_attrs comp_attr_var_heap
			  comp_st = { comp_st & comp_type_var_heap = comp_type_var_heap, comp_attr_var_heap = comp_attr_var_heap }
			  (ok, icl_cons_defs, comp_st) = compare_rhs_of_types dcl_type_def.td_rhs icl_type_def.td_rhs dcl_cons_defs icl_cons_defs comp_st
			| ok
				= (icl_type_defs, icl_cons_defs, comp_st)
				# comp_error = compareError type_def_error (newPosition icl_type_def.td_name icl_type_def.td_pos) comp_st.comp_error
				= (icl_type_defs, icl_cons_defs, { comp_st & comp_error = comp_error })
//						 ---> ("compare_type_defs", dcl_type_def.td_name, dcl_type_def.td_rhs, icl_type_def.td_name, icl_type_def.td_rhs)
			= (icl_type_defs, icl_cons_defs, comp_st)

	compare_rhs_of_types (AlgType dclConstructors) (AlgType iclConstructors) dcl_cons_defs icl_cons_defs comp_st
		= compare_constructor_lists dclConstructors iclConstructors dcl_cons_defs icl_cons_defs comp_st
	where
		compare_constructor_lists [ dcl_cons : dcl_conses ][icl_cons : icl_conses] dcl_cons_defs icl_cons_defs comp_st
			| dcl_cons.ds_index == icl_cons.ds_index
				# last_cons = isEmpty dcl_conses
				# (ok, icl_cons_defs, comp_st) = compare_constructors last_cons dcl_cons.ds_index dcl_cons_defs icl_cons_defs comp_st
				| ok
					| last_cons
						= (isEmpty icl_conses, icl_cons_defs, comp_st) 
						= compare_constructor_lists dcl_conses icl_conses dcl_cons_defs icl_cons_defs comp_st
					= (False, icl_cons_defs, comp_st)	
				= (False, icl_cons_defs, comp_st)	

	compare_rhs_of_types (SynType dclType) (SynType iclType) dcl_cons_defs icl_cons_defs comp_st
		# (ok, comp_st) = compare dclType iclType comp_st
		= (ok, icl_cons_defs, comp_st)
	compare_rhs_of_types (RecordType dclRecord) (RecordType iclRecord) dcl_cons_defs icl_cons_defs comp_st
		= compare_records dclRecord iclRecord dcl_cons_defs icl_cons_defs comp_st
	where
		compare_records dcl_rec icl_rec dcl_cons_defs icl_cons_defs comp_st
			# nr_of_dcl_fields = size dcl_rec.rt_fields
			| nr_of_dcl_fields == size icl_rec.rt_fields && compare_fields nr_of_dcl_fields dcl_rec.rt_fields icl_rec.rt_fields
				= compare_constructors True dcl_rec.rt_constructor.ds_index dcl_cons_defs icl_cons_defs comp_st
				= (False, icl_cons_defs, comp_st)
		
		compare_fields field_nr dcl_fields icl_fields
			| field_nr == 0
				= True
				# field_nr = dec field_nr
				= dcl_fields.[field_nr].fs_index == icl_fields.[field_nr].fs_index && compare_fields field_nr dcl_fields icl_fields

	compare_rhs_of_types (AbstractType _) icl_type dcl_cons_defs icl_cons_defs comp_st
		= (True, icl_cons_defs, comp_st)
	compare_rhs_of_types dcl_type icl_type dcl_cons_defs icl_cons_defs comp_st
		= (False, icl_cons_defs, comp_st)
	
	compare_constructors do_compare_result_types cons_index dcl_cons_defs icl_cons_defs comp_st=:{comp_type_var_heap}
		# dcl_cons_def = dcl_cons_defs.[cons_index]
		  (icl_cons_def, icl_cons_defs) = icl_cons_defs![cons_index]
		  dcl_cons_type = dcl_cons_def.cons_type
		  icl_cons_type = icl_cons_def.cons_type
		  comp_type_var_heap = initialyseATypeVars dcl_cons_def.cons_exi_vars comp_type_var_heap
		  comp_type_var_heap = initialyseATypeVars icl_cons_def.cons_exi_vars comp_type_var_heap
		  comp_st = { comp_st & comp_type_var_heap = comp_type_var_heap }
		  (ok, comp_st) = compare dcl_cons_type.st_args icl_cons_type.st_args comp_st
		| dcl_cons_def.cons_priority == icl_cons_def.cons_priority
			| ok && do_compare_result_types
				# (ok, comp_st) = compare dcl_cons_type.st_result icl_cons_type.st_result comp_st
				= (ok, icl_cons_defs, comp_st)
				= (ok, icl_cons_defs, comp_st)
			= (False, icl_cons_defs, comp_st)


compareClassDefs :: !{#Int} {#Bool} !{# ClassDef} !{# MemberDef} !u:{# ClassDef} !v:{# MemberDef} !*CompareState
	-> (!u:{# ClassDef}, !v:{# MemberDef}, !*CompareState)
compareClassDefs dcl_sizes copied_from_dcl dcl_class_defs dcl_member_defs icl_class_defs icl_member_defs comp_st
	# nr_of_dcl_classes = dcl_sizes.[cClassDefs]
	= iFoldSt (compare_class_defs copied_from_dcl dcl_class_defs dcl_member_defs) 0 nr_of_dcl_classes (icl_class_defs, icl_member_defs, comp_st)
where	  	
	compare_class_defs ::  !{# Bool} {# ClassDef} {# MemberDef} !Index (!u:{# ClassDef}, !v:{# MemberDef}, !*CompareState)
		-> (!u:{# ClassDef}, v:{# MemberDef}, !*CompareState)
	compare_class_defs copied_from_dcl dcl_class_defs dcl_member_defs class_index (icl_class_defs, icl_member_defs, comp_st)
		| not copied_from_dcl.[class_index]
			# dcl_class_def = dcl_class_defs.[class_index]
			  (icl_class_def, icl_class_defs) = icl_class_defs![class_index]
			# (ok, icl_member_defs, comp_st) = compare_classes dcl_class_def dcl_member_defs icl_class_def icl_member_defs comp_st
			| ok // ---> ("compare_class_defs",  dcl_class_def.class_name, icl_class_def.class_name)
				= (icl_class_defs, icl_member_defs, comp_st)
				# comp_error = compareError class_def_error (newPosition icl_class_def.class_name icl_class_def.class_pos) comp_st.comp_error
				= (icl_class_defs, icl_member_defs, { comp_st & comp_error = comp_error })
			= (icl_class_defs, icl_member_defs, comp_st)

	compare_classes dcl_class_def dcl_member_defs icl_class_def icl_member_defs comp_st=:{comp_type_var_heap}
		# comp_type_var_heap = initialyseTypeVars dcl_class_def.class_args comp_type_var_heap
		  comp_type_var_heap = initialyseTypeVars icl_class_def.class_args comp_type_var_heap
		  comp_st = { comp_st & comp_type_var_heap = comp_type_var_heap }
		# (ok, comp_st) = compare dcl_class_def.class_context icl_class_def.class_context comp_st
		| ok
			# nr_of_dcl_members = size dcl_class_def.class_members
			| nr_of_dcl_members == size icl_class_def.class_members
				= compare_array_of_class_members nr_of_dcl_members dcl_class_def.class_members icl_class_def.class_members dcl_member_defs icl_member_defs comp_st
				= (False, icl_member_defs, comp_st)
			= (False, icl_member_defs, comp_st)

	compare_array_of_class_members loc_member_index dcl_members icl_members dcl_member_defs icl_member_defs comp_st
		| loc_member_index == 0
			= (True, icl_member_defs, comp_st)
		# loc_member_index = dec loc_member_index 
		# dcl_member = dcl_members.[loc_member_index]
		# icl_member = icl_members.[loc_member_index]
		| dcl_member == icl_member
			# glob_member_index = dcl_member.ds_index
			# dcl_member_def = dcl_member_defs.[glob_member_index]
			  (icl_member_def, icl_member_defs) = icl_member_defs![glob_member_index]
			  (ok, comp_st) = compare dcl_member_def.me_type icl_member_def.me_type comp_st
			| ok && dcl_member_def.me_priority == icl_member_def.me_priority
				= compare_array_of_class_members loc_member_index dcl_members icl_members dcl_member_defs icl_member_defs comp_st
				= (False, icl_member_defs, comp_st)
			= (False, icl_member_defs, comp_st)

compareInstanceDefs :: !{# Int} !{# ClassInstance} !u:{# ClassInstance} !*CompareState -> (!u:{# ClassInstance}, !*CompareState)
compareInstanceDefs dcl_sizes dcl_instance_defs icl_instance_defs comp_st
	# nr_of_dcl_instances = dcl_sizes.[cInstanceDefs]
	= iFoldSt (compare_instance_defs dcl_instance_defs) 0 nr_of_dcl_instances (icl_instance_defs, comp_st)
where
	compare_instance_defs ::  !{# ClassInstance} !Index (!u:{# ClassInstance}, !*CompareState) -> (!u:{# ClassInstance}, !*CompareState)
	compare_instance_defs dcl_instance_defs instance_index (icl_instance_defs, comp_st)
		# dcl_instance_def = dcl_instance_defs.[instance_index]
		  (icl_instance_def, icl_instance_defs) = icl_instance_defs![instance_index]
		  (ok, comp_st) = compare dcl_instance_def.ins_type icl_instance_def.ins_type comp_st
		| ok
			= (icl_instance_defs, comp_st)
			# comp_error = compareError instance_def_error (newPosition icl_instance_def.ins_ident icl_instance_def.ins_pos) comp_st.comp_error
			= (icl_instance_defs, { comp_st & comp_error = comp_error })
//				---> ("compare_instance_defs", dcl_instance_def.ins_ident, dcl_instance_def.ins_type, icl_instance_def.ins_ident, icl_instance_def.ins_type)
		  

class compare a :: !a !a !*CompareState -> (!Bool, !*CompareState)


instance compare (a,b) | compare a & compare b
where
	compare (x1, y1) (x2, y2) comp_st
		# (ok, comp_st) = compare x1 x2 comp_st
		| ok
			= compare y1 y2 comp_st
			= (False, comp_st)

instance compare (Global a) | == a
where
	compare g1 g2 comp_st
		= (g1.glob_module == g2.glob_module && g1.glob_object == g2.glob_object, comp_st)

instance compare [a] | compare a
where
	compare [x:xs] [y:ys] comp_st
		= compare (x, xs) (y, ys) comp_st
	compare [] [] comp_st
		= (True, comp_st)
	compare _ _ comp_st
		= (False, comp_st)
		
instance compare Type
where
	compare (TA dclIdent dclArgs) (TA iclIdent iclArgs) comp_st
		= compare (dclIdent.type_index, dclArgs) (iclIdent.type_index, iclArgs) comp_st
	compare (dclFun --> dclArg) (iclFun --> iclArg) comp_st
		= compare (dclFun, dclArg) (iclFun, iclArg) comp_st
	compare (CV dclVar :@: dclArgs) (CV iclVar :@: iclArgs) comp_st
		= compare (dclVar, dclArgs) (iclVar, iclArgs) comp_st
	compare (TB dclDef) (TB iclDef) comp_st
		= (dclDef == iclDef, comp_st)
	compare (GTV dclDef) (GTV iclDef) comp_st
		= compare dclDef iclDef comp_st
	compare (TV dclVar) (TV iclVar) comp_st
		= compare dclVar iclVar comp_st
	compare _ _ comp_st
		= (False, comp_st)

instance compare AType
where
	compare at1 at2 comp_st
		= compare (at1.at_attribute, (at1.at_annotation,  at1.at_type)) (at2.at_attribute, (at2.at_annotation, at2.at_type)) comp_st

instance compare TypeAttribute
where
	compare ta1 ta2 comp_st
		| equal_constructor ta1 ta2
			= compare_equal_constructor ta1 ta2 comp_st
			= (False, comp_st)
	where
		compare_equal_constructor (TA_Var dclDef) (TA_Var iclDef) comp_st
			= compare dclDef iclDef comp_st
		compare_equal_constructor (TA_RootVar dclDef) (TA_RootVar iclDef) comp_st
			= compare dclDef iclDef comp_st
		compare_equal_constructor _ _ comp_st
			= (True, comp_st)
	
instance compare Annotation
where
	compare an1 an2 comp_st
		= (equal_constructor an1 an2, comp_st)
	
instance compare AttributeVar
where
	compare {av_info_ptr = dcl_info_ptr} {av_info_ptr = icl_info_ptr} comp_st=:{comp_attr_var_heap}
		# (dcl_info, comp_attr_var_heap) = readPtr dcl_info_ptr comp_attr_var_heap
		  (icl_info, comp_attr_var_heap) = readPtr icl_info_ptr comp_attr_var_heap
		  (ok, comp_attr_var_heap) = compare_vars dcl_info icl_info dcl_info_ptr icl_info_ptr comp_attr_var_heap
		= (ok, { comp_st & comp_attr_var_heap = comp_attr_var_heap })
	where
		compare_vars AVI_Empty AVI_Empty dcl_av_info_ptr icl_av_info_ptr comp_attr_var_heap
			= (True, comp_attr_var_heap <:= (dcl_av_info_ptr, AVI_AttrVar icl_av_info_ptr) <:= (icl_av_info_ptr, AVI_AttrVar dcl_av_info_ptr))
		compare_vars (AVI_AttrVar dcl_forward) (AVI_AttrVar icl_forward) dcl_av_info_ptr icl_av_info_ptr comp_attr_var_heap
			= (dcl_forward == icl_av_info_ptr && icl_forward == dcl_av_info_ptr, comp_attr_var_heap)
		compare_vars dcl_info icl_info dcl_av_info_ptr icl_av_info_ptr comp_attr_var_heap
			= (True, comp_attr_var_heap)

instance compare TypeVar
where
	compare {tv_info_ptr = dcl_info_ptr} {tv_info_ptr = icl_info_ptr} comp_st=:{comp_type_var_heap}
		# (dcl_info, comp_type_var_heap) = readPtr dcl_info_ptr comp_type_var_heap
		  (icl_info, comp_type_var_heap) = readPtr icl_info_ptr comp_type_var_heap
		  (ok, comp_type_var_heap) = compare_vars dcl_info icl_info dcl_info_ptr icl_info_ptr comp_type_var_heap
		= (ok, { comp_st & comp_type_var_heap = comp_type_var_heap })
	where
		compare_vars TVI_Empty TVI_Empty dcl_tv_info_ptr icl_tv_info_ptr type_var_heap
			= (True, type_var_heap <:= (dcl_tv_info_ptr, TVI_TypeVar icl_tv_info_ptr) <:= (icl_tv_info_ptr, TVI_TypeVar dcl_tv_info_ptr))
		compare_vars (TVI_TypeVar dcl_forward) (TVI_TypeVar icl_forward) dcl_tv_info_ptr icl_tv_info_ptr type_var_heap
			= (dcl_forward == icl_tv_info_ptr && icl_forward == dcl_tv_info_ptr, type_var_heap)
		compare_vars dcl_info icl_info dcl_tv_info_ptr icl_tv_info_ptr type_var_heap
			= (True, type_var_heap)
		
instance compare AttrInequality
where
	compare dcl_ineq icl_ineq comp_st
		= compare (dcl_ineq.ai_demanded, dcl_ineq.ai_offered) (icl_ineq.ai_demanded, icl_ineq.ai_offered) comp_st

instance compare SymbolType
where
	compare dcl_st icl_st comp_st=:{comp_type_var_heap,comp_attr_var_heap}
		# comp_type_var_heap = initialyseTypeVars dcl_st.st_vars comp_type_var_heap
		  comp_type_var_heap = initialyseTypeVars icl_st.st_vars comp_type_var_heap
		  comp_attr_var_heap = initialyseAttributeVars dcl_st.st_attr_vars comp_attr_var_heap
		  comp_attr_var_heap = initialyseAttributeVars icl_st.st_attr_vars comp_attr_var_heap
		  comp_st = { comp_st & comp_type_var_heap = comp_type_var_heap, comp_attr_var_heap = comp_attr_var_heap }
		= compare	(dcl_st.st_args, (dcl_st.st_result, (dcl_st.st_context, dcl_st.st_attr_env)))
					(icl_st.st_args, (icl_st.st_result, (icl_st.st_context, icl_st.st_attr_env))) comp_st
//						---> ("compare SymbolType", dcl_st, icl_st)

instance compare InstanceType
where
	compare dcl_it icl_it comp_st=:{comp_type_var_heap,comp_attr_var_heap}
		# comp_type_var_heap = initialyseTypeVars dcl_it.it_vars comp_type_var_heap
		  comp_type_var_heap = initialyseTypeVars icl_it.it_vars comp_type_var_heap
		  comp_attr_var_heap = initialyseAttributeVars dcl_it.it_attr_vars comp_attr_var_heap
		  comp_attr_var_heap = initialyseAttributeVars icl_it.it_attr_vars comp_attr_var_heap
		  comp_st = { comp_st & comp_type_var_heap = comp_type_var_heap, comp_attr_var_heap = comp_attr_var_heap }
		= compare (dcl_it.it_types, dcl_it.it_context) (icl_it.it_types, icl_it.it_context) comp_st
//						---> ("compare InstanceType", dcl_it, icl_it)

instance compare TypeContext
where
	compare dcl_tc icl_tc comp_st
		| dcl_tc.tc_class == icl_tc.tc_class
			= compare dcl_tc.tc_types icl_tc.tc_types comp_st
			= (False, comp_st)


initialyseTypeVars type_vars type_var_heap
	= foldSt init_type_var type_vars type_var_heap
where
	init_type_var {tv_info_ptr} type_var_heap
		= type_var_heap <:= (tv_info_ptr, TVI_Empty)

initialyseATypeVars atype_vars type_var_heap
	= foldSt init_atype_var atype_vars type_var_heap
where
	init_atype_var {atv_variable={tv_info_ptr}} type_var_heap
		= type_var_heap <:= (tv_info_ptr, TVI_Empty)

initialyseAttributeVars attr_vars attr_var_heap
	= foldSt init_attr_var attr_vars attr_var_heap
where
	init_attr_var {av_info_ptr} attr_var_heap
		= attr_var_heap <:= (av_info_ptr, AVI_Empty)
	
:: TypesCorrespondState =
		{	tc_type_vars :: !.HeapWithNumber TypeVarInfo
		,	tc_attr_vars :: !.HeapWithNumber AttrVarInfo
		,	tc_ignore_strictness :: !Bool
		}

:: TypesCorrespondMonad
		:==	!*TypesCorrespondState -> *(!Bool, !*TypesCorrespondState)

:: ExpressionsCorrespondState =
		{	ec_icl_correspondences ::	!.{# Int },
			ec_dcl_correspondences ::	!.{# Int }
		,	ec_var_heap ::	!.HeapWithNumber VarInfo
		,	ec_expr_heap ::	!.ExpressionHeap
		,	ec_icl_functions :: !.{#FunDef}
		,	ec_macro_defs :: !.{#.{#FunDef}}
		,	ec_error_admin ::	!.ErrorAdmin
		,	ec_tc_state ::	!.TypesCorrespondState
		,	ec_main_dcl_module_n ::	!Int
		}
		
:: ExpressionsCorrespondMonad
		:== !*ExpressionsCorrespondState -> *ExpressionsCorrespondState

:: Conversions :== {#Index}

:: HeapWithNumber a
	=	{	hwn_heap ::	!.Heap a
		,	hwn_number ::	!Int
		}

:: OptionalCorrespondenceNumber = CorrespondenceNumber !Int | Unbound
	
:: ComparisionErrorCode :== Int
// arg n not ok: n
CEC_ResultNotOK :== 0
CEC_Ok :== -1
CEC_ArgNrNotOk :== -2
CEC_ContextNotOK :== -3
CEC_AttrEnvNotOK :== -4

class t_corresponds a :: !a !a -> *TypesCorrespondMonad
class e_corresponds a :: !a !a -> ExpressionsCorrespondMonad
	// check for correspondence of expressions
	// whether two types correspond

class getIdentPos a :: a -> IdentPos

class CorrespondenceNumber a where
	toCorrespondenceNumber :: .a -> OptionalCorrespondenceNumber
	fromCorrespondenceNumber :: Int -> .a

initial_hwn hwn_heap = { hwn_heap = hwn_heap, hwn_number = 0 }

compareDefImp :: !Int !DclModule !Int !*IclModule !*{#*{#FunDef}} !*Heaps !*ErrorAdmin 
								  -> (!.IclModule,!.{#.{#FunDef}},!.Heaps,!.ErrorAdmin)
compareDefImp main_dcl_module_n main_dcl_module=:{dcl_macro_conversions=No} n_exported_global_functions icl_module macro_defs heaps error_admin
	= (icl_module, macro_defs,heaps, error_admin)
compareDefImp main_dcl_module_n main_dcl_module=:{dcl_macro_conversions=Yes macro_conversion_table} n_exported_global_functions icl_module macro_defs heaps error_admin
//	| Trace_array icl_module.icl_functions
//		&& Trace_array macro_defs.[main_dcl_module_n]

	# {dcl_functions,dcl_macros,dcl_common} = main_dcl_module
	  {icl_common, icl_functions, icl_copied_from_dcl = {copied_type_defs,copied_class_defs}}
			= icl_module
	  {hp_var_heap, hp_expression_heap, hp_type_heaps={th_vars, th_attrs}}
	  		= heaps
	  { com_cons_defs=icl_com_cons_defs, com_type_defs = icl_com_type_defs,
		com_selector_defs=icl_com_selector_defs, com_class_defs = icl_com_class_defs,
		com_member_defs=icl_com_member_defs, com_instance_defs = icl_com_instance_defs }
			= icl_common
	  comp_st
	  	=	{	comp_type_var_heap	= th_vars
	  		,	comp_attr_var_heap	= th_attrs
	  		,	comp_error			= error_admin
	  		}

	  (icl_com_type_defs, icl_com_cons_defs, comp_st)
	  		= compareTypeDefs main_dcl_module.dcl_sizes copied_type_defs	dcl_common.com_type_defs dcl_common.com_cons_defs
	  																		icl_com_type_defs icl_com_cons_defs comp_st
	  (icl_com_class_defs, icl_com_member_defs, comp_st)
	  		= compareClassDefs main_dcl_module.dcl_sizes copied_class_defs 	dcl_common.com_class_defs dcl_common.com_member_defs
	  																		icl_com_class_defs icl_com_member_defs comp_st

	  (icl_com_instance_defs, comp_st)
	  		= compareInstanceDefs main_dcl_module.dcl_sizes dcl_common.com_instance_defs icl_com_instance_defs comp_st

	  {	comp_type_var_heap = th_vars, comp_attr_var_heap = th_attrs, comp_error = error_admin } = comp_st

	  tc_state
	  		=	{ tc_type_vars = initial_hwn th_vars
				, tc_attr_vars = initial_hwn th_attrs
				, tc_ignore_strictness = False
				}
	  (icl_functions, macro_defs, hp_var_heap, hp_expression_heap, tc_state, error_admin)
			= compareMacrosWithConversion main_dcl_module_n macro_conversion_table dcl_macros icl_functions macro_defs hp_var_heap hp_expression_heap tc_state error_admin
	  (icl_functions, tc_state, error_admin)
	  		= compareFunctionTypes n_exported_global_functions dcl_functions icl_functions tc_state error_admin
	  { tc_type_vars, tc_attr_vars } 
	   		= tc_state
	  icl_common
	  		= { icl_common & com_cons_defs=icl_com_cons_defs, com_type_defs = icl_com_type_defs,
	  			com_selector_defs=icl_com_selector_defs, com_class_defs=icl_com_class_defs,
	  			com_member_defs=icl_com_member_defs, com_instance_defs = icl_com_instance_defs }
	  heaps
	  		= { hp_var_heap = hp_var_heap, hp_expression_heap = hp_expression_heap,
	  			hp_type_heaps = { th_vars = tc_type_vars.hwn_heap, th_attrs = tc_attr_vars.hwn_heap}}
	= ({ icl_module & icl_common = icl_common, icl_functions = icl_functions },macro_defs,heaps, error_admin )

compareFunctionTypes n_exported_global_functions dcl_fun_types icl_functions tc_state error_admin
	= iFoldSt (compareTwoFunctionTypes dcl_fun_types) 0 n_exported_global_functions (icl_functions, tc_state, error_admin)

compareTwoFunctionTypes :: /*!{#Int}*/ !{#FunType} !Int !*(!u:{#FunDef},!*TypesCorrespondState,!*ErrorAdmin) 
						-> (!v:{#FunDef},!.TypesCorrespondState,!.ErrorAdmin) , [u <= v]
compareTwoFunctionTypes /*conversions*/	dcl_fun_types dclIndex (icl_functions, tc_state, error_admin)
	# (fun_def=:{fun_type, fun_priority}, icl_functions) = icl_functions![dclIndex]
	= case fun_type of
		No	-> generate_error "type of exported function is missing" fun_def icl_functions tc_state error_admin
		Yes icl_symbol_type
			# {ft_type=dcl_symbol_type, ft_priority,ft_symb} = dcl_fun_types.[dclIndex]			
			# tc_state = init_symbol_type_vars dcl_symbol_type icl_symbol_type tc_state
			  (corresponds, tc_state)
					= t_corresponds dcl_symbol_type icl_symbol_type tc_state // --->("comparing:", dcl_symbol_type ,icl_symbol_type)
			| corresponds && fun_priority==ft_priority
				-> (icl_functions, tc_state, error_admin)
			-> generate_error ErrorMessage fun_def icl_functions tc_state error_admin

symbolTypesCorrespond :: !SymbolType !SymbolType !*TypeHeaps -> (!ComparisionErrorCode, !.TypeHeaps)
symbolTypesCorrespond symbol_type_1 symbol_type_2 type_heaps=:{th_vars, th_attrs}
	| length symbol_type_1.st_args<>length symbol_type_2.st_args
		= (CEC_ArgNrNotOk, type_heaps)
	# tc_state
			= { tc_type_vars = initial_hwn th_vars
			  , tc_attr_vars = initial_hwn th_attrs
			  , tc_ignore_strictness = True
			  }
	  tc_state
	  		= init_symbol_type_vars symbol_type_1 symbol_type_2 tc_state
	  (correspond_list, tc_state)
	  		= map2St t_corresponds
	  				[symbol_type_1.st_result:symbol_type_1.st_args]
	  				[symbol_type_2.st_result:symbol_type_2.st_args]
	  		        tc_state
	  err_code
	  		= firstIndex not correspond_list
	| err_code<>CEC_Ok
		= (err_code, tc_state_to_type_heaps tc_state)
	# (context_corresponds, tc_state)
			= t_corresponds symbol_type_1.st_context symbol_type_2.st_context tc_state
	| not context_corresponds
		= (CEC_ContextNotOK, tc_state_to_type_heaps tc_state)
	# (attr_env_corresponds, tc_state)
			= t_corresponds symbol_type_1.st_attr_env symbol_type_2.st_attr_env tc_state
	| not attr_env_corresponds
		= (CEC_AttrEnvNotOK, tc_state_to_type_heaps tc_state)
	= (CEC_Ok, tc_state_to_type_heaps tc_state)
  where
	tc_state_to_type_heaps {tc_type_vars, tc_attr_vars}
		= { th_vars = tc_type_vars.hwn_heap, th_attrs = tc_attr_vars.hwn_heap}

init_symbol_type_vars symbol_type_1 symbol_type_2 tc_state
	# tc_state = init_attr_vars (symbol_type_1.st_attr_vars++symbol_type_2.st_attr_vars)
								tc_state
	  tc_state = init_type_vars (symbol_type_1.st_vars++symbol_type_2.st_vars) tc_state
	= tc_state

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

compareMacrosWithConversion main_dcl_module_n conversions macro_range icl_functions macro_defs var_heap expr_heap tc_state error_admin
	#! n_icl_functions = size icl_functions
	#! n_dcl_macros_and_functions = size macro_defs.[main_dcl_module_n]
	# ec_state = {	ec_icl_correspondences = createArray n_icl_functions cNoCorrespondence,
	  				ec_dcl_correspondences = createArray n_dcl_macros_and_functions cNoCorrespondence,
	  				ec_var_heap = initial_hwn var_heap, 
	  				ec_expr_heap = expr_heap, ec_icl_functions = icl_functions,ec_macro_defs=macro_defs,
	  				ec_error_admin = error_admin, ec_tc_state = tc_state,
					ec_main_dcl_module_n = main_dcl_module_n }
	  ec_state = iFoldSt (compareMacroWithConversion conversions macro_range.ir_from) macro_range.ir_from macro_range.ir_to ec_state
	  	with
	  		compareMacroWithConversion conversions ir_from dclIndex ec_state=:{ec_main_dcl_module_n}
				= compareTwoMacroFuns ec_main_dcl_module_n dclIndex conversions.[dclIndex-ir_from] ec_state
	  {ec_icl_functions,ec_macro_defs,ec_var_heap, ec_expr_heap, ec_error_admin, ec_tc_state} = ec_state
	= (ec_icl_functions,ec_macro_defs, ec_var_heap.hwn_heap, ec_expr_heap, ec_tc_state, ec_error_admin)

compareTwoMacroFuns :: !Int !Int !Int !*ExpressionsCorrespondState -> .ExpressionsCorrespondState;
compareTwoMacroFuns macro_module_index dclIndex iclIndex ec_state=:{ec_icl_functions,ec_macro_defs,ec_main_dcl_module_n}
	| macro_module_index<>ec_main_dcl_module_n
		# (dcl_function,ec_macro_defs) = ec_macro_defs![macro_module_index,dclIndex]
		= { ec_state & ec_macro_defs=ec_macro_defs,ec_error_admin = checkErrorWithIdentPos (getIdentPos dcl_function) ErrorMessage ec_state.ec_error_admin }
	| iclIndex==NoIndex
		= ec_state
	# (dcl_function, ec_macro_defs) = ec_macro_defs![macro_module_index,dclIndex]
	  (icl_function, ec_icl_functions) = ec_icl_functions![iclIndex]
	  ec_state = { ec_state & ec_icl_correspondences.[iclIndex]=dclIndex, ec_dcl_correspondences.[dclIndex]=iclIndex,
	  						  ec_icl_functions = ec_icl_functions,ec_macro_defs=ec_macro_defs }
	  need_to_be_compared
	  		= case (dcl_function.fun_body, icl_function.fun_body) of
	  			(TransformedBody _, CheckedBody _)
					// the macro definition in the icl module is not used, so we don't need to compare
	  				-> False
	  			_	-> True
	| not need_to_be_compared
		= ec_state
	# ident_pos = getIdentPos dcl_function
	  ec_error_admin = pushErrorAdmin ident_pos ec_state.ec_error_admin
	  ec_state = { ec_state & ec_error_admin = ec_error_admin }
	| dcl_function.fun_info.fi_properties bitand FI_IsMacroFun <> icl_function.fun_info.fi_properties bitand FI_IsMacroFun ||
	  dcl_function.fun_priority<>icl_function.fun_priority
		# ec_state = give_error dcl_function.fun_symb ec_state
		= { ec_state & ec_error_admin = popErrorAdmin ec_state.ec_error_admin } 
	# ec_state = e_corresponds dcl_function.fun_body icl_function.fun_body ec_state
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

instance t_corresponds (a, b) | t_corresponds a & t_corresponds b where 
	t_corresponds (a1, b1) (a2, b2)
		=	t_corresponds a1 a2
		&&&	t_corresponds b1 b2


/*2.0
instance t_corresponds {# a} | t_corresponds a & Array {#} a
0.2*/
//1.3
instance t_corresponds {# a} | ArrayElem , t_corresponds a
//3.1
where 
	t_corresponds dclArray iclArray
		# size_dclArray = size dclArray
		| size_dclArray<>size iclArray
			= return False
			= loop (size_dclArray-1) dclArray iclArray
	  where
/*2.0
		loop :: !Int !{# a} !{# a} -> *TypesCorrespondMonad | t_corresponds a & Array {#} a // 2.0
0.2*/
//1.3
		loop :: !Int !{# a} !{# a} -> *TypesCorrespondMonad | t_corresponds, select_u a
//3.1
		loop i dclArray iclArray
			| i<0
				= return True
				= t_corresponds dclArray.[i] iclArray.[i]
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
//			| False--->("comparing:", dclDef, iclDef)
//				= undef
			# tc_state = init_attr_vars dclDef.td_attrs tc_state 
			  tc_state = init_attr_vars iclDef.td_attrs tc_state 
			  tc_state = init_atype_vars dclDef.td_args tc_state
			  tc_state = init_atype_vars iclDef.td_args tc_state
			= t_corresponds (dclDef.td_args, (dclDef.td_rhs, (dclDef.td_context, dclDef.td_attribute)))
			 				(iclDef.td_args, (iclDef.td_rhs, (iclDef.td_context, iclDef.td_attribute))) tc_state
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
		&&&	t_corresponds dclDef.atv_annotation iclDef.atv_annotation
		&&&	t_corresponds dclDef.atv_variable iclDef.atv_variable

instance t_corresponds Annotation where
	t_corresponds dcl_annotation icl_annotation 
		= t_corresponds` dcl_annotation icl_annotation
	  where
		t_corresponds` dcl_annotation icl_annotation tc_state=:{tc_ignore_strictness}
			= (tc_ignore_strictness || dcl_annotation==icl_annotation, tc_state)
			
instance t_corresponds AType where
	t_corresponds dclDef iclDef
		=	t_corresponds dclDef.at_attribute iclDef.at_attribute
		&&&	t_corresponds dclDef.at_annotation iclDef.at_annotation
		&&&	t_corresponds dclDef.at_type iclDef.at_type

instance t_corresponds TypeAttribute where
	t_corresponds TA_Unique TA_Unique
		=	return True
	t_corresponds TA_Multi TA_Multi
		=	return True
	t_corresponds (TA_Var dclDef) (TA_Var iclDef)
		=	t_corresponds dclDef iclDef
	t_corresponds (TA_RootVar dclDef) (TA_RootVar iclDef)
		= PA_BUG (return True) (t_corresponds dclDef iclDef)
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
		=	undef // <<- "t_corresponds (TypeRhs): dclDef == UnknownType" 
	t_corresponds _ UnknownType
		=	undef // <<- "t_corresponds (TypeRhs): iclDef == UnknownType"
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

instance e_corresponds FunctionBody where
	// both bodies are either CheckedBodies or TransformedBodies
	e_corresponds dclDef iclDef
		=	e_corresponds (from_body dclDef) (from_body iclDef)
	  where
		from_body (TransformedBody {tb_args, tb_rhs}) = (tb_args, [tb_rhs])
		from_body (CheckedBody {cb_args, cb_rhs}) = (cb_args, [ca_rhs \\ {ca_rhs} <- cb_rhs])
		
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
	e_corresponds (BasicExpr dcl_value) (BasicExpr icl_value)
		=	equal2 dcl_value icl_value
	e_corresponds (AnyCodeExpr dcl_ins dcl_outs dcl_code_sequence) (AnyCodeExpr icl_ins icl_outs icl_code_sequence)
		=	e_corresponds dcl_ins icl_ins
		o`	e_corresponds dcl_outs icl_outs
		o`	equal2 dcl_code_sequence icl_code_sequence
	e_corresponds (ABCCodeExpr dcl_lines dcl_do_inline) (ABCCodeExpr icl_lines icl_do_inline)
		=	equal2 dcl_lines icl_lines
		o`	equal2 dcl_do_inline icl_do_inline
	e_corresponds (MatchExpr dcl_cons_symbol dcl_src_expr)
				 (MatchExpr icl_cons_symbol icl_src_expr)
		=	e_corresponds dcl_cons_symbol icl_cons_symbol
		o`	e_corresponds dcl_src_expr icl_src_expr
	e_corresponds (FreeVar dcl) (FreeVar icl)
		= e_corresponds dcl icl
	e_corresponds (DynamicExpr dcl) (DynamicExpr icl)
		= e_corresponds dcl icl
	e_corresponds (TypeCodeExpression dcl) (TypeCodeExpression icl)
		= e_corresponds dcl icl
	e_corresponds EE EE
		= do_nothing
	e_corresponds (NoBind _) (NoBind _)
		= do_nothing
	e_corresponds _ _
		= give_error ""

instance e_corresponds Let where
	e_corresponds dclLet iclLet
		=	e_corresponds dclLet.let_strict_binds iclLet.let_strict_binds
		o`	e_corresponds dclLet.let_lazy_binds iclLet.let_lazy_binds
		o`	e_corresponds dclLet.let_expr iclLet.let_expr

instance e_corresponds LetBind where
	e_corresponds dcl icl
		=	e_corresponds dcl.lb_src icl.lb_src
		o`	e_corresponds dcl.lb_dst icl.lb_dst

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
	e_corresponds (OverloadedListPatterns dcl_alg_type _ dcl_patterns) (OverloadedListPatterns icl_alg_type _ icl_patterns)
		=	e_corresponds dcl_patterns icl_patterns
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
			#  (dcl_type, ec_expr_heap)
					= readPtr dcl_expr_ptr ec_expr_heap
			   (icl_type, ec_expr_heap) 
			   		= readPtr icl_expr_ptr ec_expr_heap
			# (EI_DynamicTypeWithVars _ dcl_dyn_type _)
					= dcl_type
			  (EI_DynamicTypeWithVars _ icl_dyn_type _)
			  		= icl_type
			  (corresponds, ec_tc_state) 
					= t_corresponds dcl_dyn_type icl_dyn_type ec_tc_state
			  ec_state
				  	= { ec_state & ec_tc_state = ec_tc_state, ec_expr_heap = ec_expr_heap }
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
		= { ec_state & ec_error_admin = checkError ident ErrorMessage ec_state.ec_error_admin }
	= ec_state

/*	e_corresponds_app_symb checks correspondence of the function symbols in an App expression.
	The problem: also different symbols can correspond with each other, because for macros
	all local functions (also lambda functions) will be generated twice.
*/
e_corresponds_app_symb dcl_app_symb=:{symb_name, symb_kind=SK_Function dcl_glob_index} 
					icl_app_symb=:{symb_kind=SK_Function icl_glob_index}
					ec_state
	#! main_dcl_module_n = ec_state.ec_main_dcl_module_n
	| dcl_glob_index.glob_module==main_dcl_module_n && icl_glob_index.glob_module==main_dcl_module_n
		| dcl_glob_index.glob_object<>icl_glob_index.glob_object
			= give_error symb_name ec_state
		= ec_state
	| dcl_glob_index<>icl_glob_index
		= give_error symb_name ec_state
	= ec_state
e_corresponds_app_symb dcl_app_symb=:{symb_name, symb_kind=SK_OverloadedFunction dcl_glob_index} 
					icl_app_symb=:{symb_kind=SK_OverloadedFunction icl_glob_index}
					ec_state
	| dcl_glob_index<>icl_glob_index
		= give_error symb_name ec_state
	= ec_state
e_corresponds_app_symb dcl_app_symb=:{symb_kind=SK_DclMacro dcl_glob_index} icl_app_symb=:{symb_kind=SK_IclMacro icl_index} ec_state
	= continuation_for_possibly_twice_defined_macros dcl_app_symb dcl_glob_index.glob_module dcl_glob_index.glob_object icl_app_symb icl_index ec_state
e_corresponds_app_symb dcl_app_symb=:{symb_name,symb_kind=SK_DclMacro dcl_glob_index} icl_app_symb=:{symb_kind=SK_DclMacro icl_glob_index} ec_state
	| dcl_glob_index==icl_glob_index
		= ec_state
		= give_error symb_name ec_state
e_corresponds_app_symb dcl_app_symb=:{symb_kind=SK_LocalDclMacroFunction dcl_glob_index} icl_app_symb=:{symb_kind=SK_LocalMacroFunction icl_index} ec_state
	= continuation_for_possibly_twice_defined_macros dcl_app_symb dcl_glob_index.glob_module dcl_glob_index.glob_object icl_app_symb icl_index ec_state
e_corresponds_app_symb {symb_name=dcl_symb_name, symb_kind=SK_Constructor dcl_glob_index} {symb_name=icl_symb_name, symb_kind=SK_Constructor icl_glob_index} ec_state
	| dcl_glob_index.glob_module==icl_glob_index.glob_module && dcl_symb_name.id_name==icl_symb_name.id_name
		= ec_state
		= give_error icl_symb_name ec_state
//e_corresponds_app_symb {symb_name} _ ec_state
e_corresponds_app_symb {symb_name,symb_kind} {symb_kind=symb_kind2} ec_state
	= give_error symb_name ec_state

continuation_for_possibly_twice_defined_macros dcl_app_symb dcl_module_index dcl_index icl_app_symb icl_index ec_state
	| icl_index==NoIndex
		= ec_state
	// two different functions were referenced. In case of macro functions they still could correspond
	| not (names_are_compatible dcl_index icl_index ec_state.ec_icl_functions ec_state.ec_macro_defs)
		= give_error icl_app_symb.symb_name ec_state
	| dcl_module_index<>ec_state.ec_main_dcl_module_n
		= give_error icl_app_symb.symb_name ec_state
	| ec_state.ec_dcl_correspondences.[dcl_index]==icl_index && ec_state.ec_icl_correspondences.[icl_index]==dcl_index
		= ec_state
	| ec_state.ec_dcl_correspondences.[dcl_index]==cNoCorrespondence && ec_state.ec_icl_correspondences.[icl_index]==cNoCorrespondence
		// going into recursion is save
		= compareTwoMacroFuns dcl_module_index dcl_index icl_index ec_state
	= give_error icl_app_symb.symb_name ec_state
  where
	names_are_compatible :: Int Int {#FunDef} {#{#FunDef}} -> Bool;
	names_are_compatible dcl_index icl_index icl_functions macro_defs
		# dcl_function = macro_defs.[dcl_module_index,dcl_index]
		  icl_function = icl_functions.[icl_index]
		  dcl_name_is_loc_dependent = name_is_location_dependent dcl_function.fun_kind
		  icl_name_is_loc_dependent = name_is_location_dependent icl_function.fun_kind
		=	(dcl_name_is_loc_dependent==icl_name_is_loc_dependent)
		 && (implies (not dcl_name_is_loc_dependent) (dcl_function.fun_symb.id_name==icl_function.fun_symb.id_name))
		// functions that originate from e.g. lambda expressions can correspond although their names differ
	  where
		name_is_location_dependent (FK_Function name_is_loc_dependent)
			= name_is_loc_dependent
		name_is_location_dependent _
		 	= False

init_attr_vars attr_vars tc_state=:{tc_attr_vars}
	# hwn_heap = foldSt init_attr_var attr_vars tc_attr_vars.hwn_heap
	  tc_attr_vars = { tc_attr_vars & hwn_heap = hwn_heap }
	= { tc_state & tc_attr_vars = tc_attr_vars }
  where
	init_attr_var {av_info_ptr} attr_heap
		= writePtr av_info_ptr AVI_Empty attr_heap

ErrorMessage = "definition in the impl module conflicts with the def module"
cNoCorrespondence	:== -1
implies a b 		:== not a || b
	
(==>) infix 0 // :: w:(St .s .a) v:(.a -> .(St .s .b)) -> u:(St .s .b), [u <= v, u <= w]
(==>) f g :== \st0 -> let (r,st1) = f st0 in g r st1

(o`) infixr 0
(o`) f g :== \state -> g (f state)

do f = \state -> (True, f state)

(&&&) infixr
(&&&) m1 m2
	:==	m1 ==> \b
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
	= { ec_state & ec_error_admin = checkError s ErrorMessage ec_state.ec_error_admin }

/*
instance <<< Priority
	where
		(<<<) file NoPrio = file <<< "NoPrio"		
		(<<<) file (Prio LeftAssoc i) = file <<< "Prio LeftAssoc " <<< i
		(<<<) file (Prio RightAssoc i) = file <<< "Prio RightAssoc " <<< i
		(<<<) file (Prio NoAssoc i) = file <<< "Prio NoAssoc " <<< i

Trace_array a
	= trace_array 0
	where
		trace_array i
			| i<size a
				= Trace_tn i && Trace_tn a.[i] && trace_array (i+1)
				= True;

Trace_tn d
	= file_to_true (stderr <<< d <<< '\n')

file_to_true :: !File -> Bool;
file_to_true file = code {
  .inline file_to_true
          pop_b 2
          pushB TRUE
  .end
 };
*/