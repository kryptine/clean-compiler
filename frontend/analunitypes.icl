implementation module analunitypes

import StdEnv
import syntax, checksupport, analtypes, check, typesupport, checktypes, utilities
	
instance + SignClassification
where
	(+) {sc_pos_vect=sc_pos_vect1,sc_neg_vect=sc_neg_vect1} {sc_pos_vect=sc_pos_vect2,sc_neg_vect=sc_neg_vect2}
		= {	sc_pos_vect = sc_pos_vect1 bitor sc_pos_vect2, sc_neg_vect = sc_neg_vect1 bitor sc_neg_vect2 }

(*+)  infixl 7 :: !Sign !SignClassification -> SignClassification
(*+) {pos_sign,neg_sign} {sc_pos_vect,sc_neg_vect}
	= {	sc_pos_vect = (if pos_sign sc_pos_vect 0) bitor (if neg_sign sc_neg_vect 0),
		sc_neg_vect = (if neg_sign sc_pos_vect 0) bitor (if pos_sign sc_neg_vect 0) }

sign_class_to_sign :: !SignClassification !Int -> Sign
sign_class_to_sign {sc_pos_vect,sc_neg_vect} index
	= { pos_sign = sc_pos_vect bitand (1 << index) <> 0, neg_sign = sc_neg_vect bitand (1 << index) <> 0}

set_sign_in_sign_class :: !Sign !Int !SignClassification -> SignClassification
set_sign_in_sign_class {pos_sign,neg_sign} index {sc_pos_vect,sc_neg_vect}
	= { sc_pos_vect = sc_pos_vect bitor (if pos_sign (1 << index) 0), sc_neg_vect = sc_neg_vect bitor (if neg_sign (1 << index) 0) }

typeProperties :: !Index  !Index ![SignClassification] ![PropClassification] !{# CommonDefs } !*TypeVarHeap !*TypeDefInfos
	-> (!TypeSymbProperties, !*TypeVarHeap, !*TypeDefInfos)
typeProperties type_index module_index hio_signs hio_props defs type_var_heap td_infos
	# {td_args} = defs.[module_index].com_type_defs.[type_index]
	  (td_info, td_infos) = td_infos![module_index].[type_index]
	  (tsp_sign, type_var_heap, td_infos) = determineSignClassOfTypeDef type_index module_index td_args td_info hio_signs defs type_var_heap td_infos
	  (tsp_propagation, type_var_heap, td_infos) = determinePropClassOfTypeDef type_index module_index td_args td_info hio_props defs type_var_heap td_infos
	  tsp_coercible = (td_info.tdi_properties bitand cIsNonCoercible) == 0
	= ({tsp_sign = tsp_sign, tsp_propagation = tsp_propagation, tsp_coercible = tsp_coercible }, type_var_heap, td_infos)

signClassification :: !Index !Index ![SignClassification] !{# CommonDefs } !*TypeVarHeap !*TypeDefInfos
	-> (!SignClassification, !*TypeVarHeap, !*TypeDefInfos)
signClassification type_index module_index hio_signs defs type_var_heap td_infos
	# {td_args} = defs.[module_index].com_type_defs.[type_index]
	  (td_info, td_infos) = td_infos![module_index].[type_index]
	= determineSignClassOfTypeDef type_index module_index td_args td_info hio_signs defs type_var_heap td_infos

removeTopClasses [cv : cvs] [tc : tcs] 
	| isATopConsVar cv
		= removeTopClasses cvs tcs
		= [tc : removeTopClasses cvs tcs] 
removeTopClasses _ _
	= []

determineSignClassOfTypeDef :: !Int !Int ![ATypeVar] !TypeDefInfo ![SignClassification] {# CommonDefs} !*TypeVarHeap !*TypeDefInfos
	-> (!SignClassification, !*TypeVarHeap, !*TypeDefInfos)
determineSignClassOfTypeDef type_index module_index td_args {tdi_classification,tdi_cons_vars,tdi_group_vars,tdi_group,tdi_group_nr}
			hio_signs ci type_var_heap td_infos
	# hio_signs = removeTopClasses tdi_cons_vars hio_signs
	  result = retrieveSignClassification hio_signs tdi_classification
	= case result of
		Yes {ts_type_sign}
			-> (ts_type_sign, type_var_heap, td_infos)
		No
			# type_var_heap = bind_type_vars_to_signs td_args tdi_group_vars tdi_cons_vars hio_signs type_var_heap
			  (sign_class, type_var_heap, td_infos)
			  		= newSignClassOfTypeDefGroup tdi_group_nr { glob_module = module_index, glob_object = type_index}
						tdi_group hio_signs ci type_var_heap td_infos
			-> (sign_class, foldSt restore_binds_of_type_var td_args type_var_heap, td_infos)

where
	bind_type_vars_to_signs [{atv_variable={tv_info_ptr}}: tvs] [gv : gvs] cons_vars hio_signs type_var_heap
		# sign = determine_classification gv cons_vars hio_signs BottomSignClass
		# (var_info, type_var_heap) = readPtr tv_info_ptr type_var_heap
		= bind_type_vars_to_signs tvs gvs cons_vars hio_signs (type_var_heap <:= (tv_info_ptr, TVI_SignClass gv sign var_info))
	bind_type_vars_to_signs [] group_vars cons_vars hio_signs type_var_heap
		= type_var_heap

	determine_classification gv [cv : cvs] hio_signs=:[tc : tcs] cumm_sign_class
		| isATopConsVar cv
			| gv == decodeTopConsVar cv
				= TopSignClass
				= determine_classification gv cvs tcs cumm_sign_class
		| gv == cv
			= determine_classification gv cvs tcs (tc + cumm_sign_class)
			= determine_classification gv cvs tcs cumm_sign_class
	determine_classification gv cons_vars [] cumm_sign_class
		= cumm_sign_class

	restore_binds_of_type_var {atv_variable={tv_info_ptr}} type_var_heap
		# (TVI_SignClass _ _ old_info, type_var_heap) = readPtr tv_info_ptr type_var_heap
		= type_var_heap <:= (tv_info_ptr, old_info)

newSignClassOfTypeDefGroup :: !Int !(Global Int) ![Global Int] ![SignClassification] !{#CommonDefs} !*TypeVarHeap !*TypeDefInfos
			-> *(!SignClassification,!*TypeVarHeap,!*TypeDefInfos)
newSignClassOfTypeDefGroup group_nr this_type group hio_signs ci type_var_heap td_infos
	# (cumm_sign_env, type_var_heap, td_infos) = collect_sign_class_of_type_defs group_nr group ci BottomSignClass type_var_heap td_infos 
	  (sign_class, td_infos) = update_sign_class_of_group this_type group cumm_sign_env hio_signs td_infos
	= (sign_class, type_var_heap, td_infos)
where
	update_sign_class_of_group my_index [] cumm_sign_env hio_signs td_infos
		= (BottomSignClass, td_infos)
	update_sign_class_of_group my_index [{glob_module,glob_object} : group] cumm_sign_env hio_signs td_infos
		# (tdi=:{tdi_classification, tdi_group_vars},td_infos) = td_infos![glob_module].[glob_object]
		  sign_class = determine_sign_class tdi_group_vars cumm_sign_env BottomSignClass 0
		  tdi_classification = addSignClassification hio_signs sign_class tdi_classification
		  td_infos = { td_infos & [glob_module].[glob_object] = { tdi & tdi_classification = tdi_classification }}
		  (my_sign_class, td_infos) = update_sign_class_of_group my_index group cumm_sign_env hio_signs td_infos
		= (if (my_index.glob_module == glob_module &&  my_index.glob_object == glob_object) sign_class my_sign_class, td_infos)

	determine_sign_class [gv : gvs] cumm_sign_env sign_class var_index
		# sign_class = set_sign_in_sign_class (sign_class_to_sign cumm_sign_env gv) var_index sign_class
		= determine_sign_class gvs cumm_sign_env sign_class (inc var_index)
	determine_sign_class [] cumm_sign_env sign_class var_index
		= sign_class

	collect_sign_class_of_type_defs group_nr [] ci cumm_sign_env type_var_heap td_infos
		= (cumm_sign_env, type_var_heap, td_infos)
	collect_sign_class_of_type_defs group_nr [{glob_module,glob_object} : group] ci cumm_sign_env type_var_heap td_infos 
		# {td_rhs} = ci.[glob_module].com_type_defs.[glob_object]
		# (cumm_sign_env, type_var_heap, td_infos) = sign_class_of_type_def glob_module td_rhs group_nr ci cumm_sign_env type_var_heap td_infos
		= collect_sign_class_of_type_defs group_nr group ci cumm_sign_env type_var_heap td_infos

	sign_class_of_type_def :: !Int !TypeRhs !Int !{#CommonDefs} !SignClassification !*TypeVarHeap *TypeDefInfos
		-> (!SignClassification,!*TypeVarHeap,!*TypeDefInfos)
	sign_class_of_type_def module_index (AlgType conses) group_nr ci cumm_sign_env type_var_heap td_infos
		= sign_class_of_type_conses module_index conses group_nr ci cumm_sign_env type_var_heap td_infos
	sign_class_of_type_def _ (SynType {at_type}) group_nr ci cumm_sign_env type_var_heap td_infos
		# (sign_class, _, type_var_heap, td_infos) = signClassOfType at_type group_nr ci type_var_heap td_infos
		= (cumm_sign_env + sign_class, type_var_heap, td_infos)
	sign_class_of_type_def module_index (RecordType {rt_constructor}) group_nr ci cumm_sign_env type_var_heap td_infos
		= sign_class_of_type_conses module_index [rt_constructor] group_nr ci cumm_sign_env type_var_heap td_infos
	sign_class_of_type_def _ (AbstractType properties) _ _ _ type_var_heap td_infos
		| properties bitand cIsNonCoercible == 0
			= (PosSignClass, type_var_heap, td_infos)
			= (TopSignClass, type_var_heap, td_infos)

	sign_class_of_type_conses module_index [{ds_index}:conses] group_nr ci cumm_sign_class type_var_heap td_infos
		#! cons_def = ci.[module_index].com_cons_defs.[ds_index]
		#  (cumm_sign_class, type_var_heap, td_infos) = sign_class_of_type_of_list cons_def.cons_type.st_args group_nr ci cumm_sign_class type_var_heap td_infos
		= sign_class_of_type_conses module_index conses group_nr ci cumm_sign_class type_var_heap td_infos
	sign_class_of_type_conses module_index [] _ _ cumm_sign_class type_var_heap td_infos
		= (cumm_sign_class, type_var_heap, td_infos)

	sign_class_of_type_of_list [{at_type} : types] group_nr ci cumm_sign_class type_var_heap td_infos
		# (sign_class, _, type_var_heap, td_infos) = signClassOfType at_type group_nr ci type_var_heap td_infos
		= sign_class_of_type_of_list types group_nr ci (cumm_sign_class + sign_class) type_var_heap td_infos
	sign_class_of_type_of_list [] _ _ cumm_sign_class type_var_heap td_infos
		= (cumm_sign_class, type_var_heap, td_infos)

IsAHioType		:== True
IsNotAHioType	:== False

IsArrowKind (KindArrow _) = True
IsArrowKind _ = False

signClassOfTypeVariable :: !TypeVar !{#CommonDefs} !*TypeVarHeap !*TypeDefInfos
	-> *(!SignClassification,!SignClassification,!*TypeVarHeap,!*TypeDefInfos);
signClassOfTypeVariable {tv_info_ptr} ci type_var_heap td_infos
	#! var_info = sreadPtr tv_info_ptr type_var_heap
	= case var_info of
		TVI_SignClass group_var_index var_class _ 
			-> (var_index_to_sign_class group_var_index, var_class, type_var_heap, td_infos)
		_
			-> (BottomSignClass, TopSignClass, type_var_heap, td_infos)
where
	var_index_to_sign_class :: !Int -> SignClassification
	var_index_to_sign_class var_index 
		= { sc_pos_vect = 1 << var_index, sc_neg_vect = 0}


signClassOfType :: !Type !Int !{#CommonDefs} !*TypeVarHeap !*TypeDefInfos -> *(!SignClassification,!SignClassification,!*TypeVarHeap,!*TypeDefInfos);
signClassOfType (TV tv) _ ci type_var_heap td_infos
	= signClassOfTypeVariable tv ci type_var_heap td_infos

signClassOfType (TA {type_index = {glob_module, glob_object}} types) group_nr ci type_var_heap td_infos
	# ({tdi_group_nr,tdi_kinds}, td_infos) = td_infos![glob_module].[glob_object]
	| tdi_group_nr == group_nr
		= sign_class_of_type_list_of_rec_type types BottomSignClass ci type_var_heap td_infos 
		# {td_args,td_arity} = ci.[glob_module].com_type_defs.[glob_object]
		  (td_info, td_infos) = td_infos![glob_module].[glob_object]
		  (sign_classes, hio_signs, type_var_heap, td_infos) = collect_sign_classes_of_type_list types tdi_kinds ci type_var_heap td_infos 
		  (type_class, type_var_heap, td_infos) = determineSignClassOfTypeDef glob_object glob_module td_args td_info hio_signs ci type_var_heap td_infos
		  sign_class = determine_cummulative_sign sign_classes type_class 0 BottomSignClass
		= (sign_class, adjust_sign_class type_class td_arity, type_var_heap, td_infos)
where

	sign_class_of_type_list_of_rec_type [t : ts] cumm_sign_class ci type_var_heap td_infos
		# (sign_class, type_class, type_var_heap, td_infos) = signClassOfType t.at_type group_nr ci type_var_heap td_infos
		  cumm_sign_class = { cumm_sign_class & sc_neg_vect = cumm_sign_class.sc_neg_vect bitor sign_class.sc_neg_vect }
		= sign_class_of_type_list_of_rec_type ts cumm_sign_class ci type_var_heap td_infos
	sign_class_of_type_list_of_rec_type [] cumm_sign_class ci type_var_heap td_infos
		= (cumm_sign_class, TopSignClass, type_var_heap, td_infos)

	collect_sign_classes_of_type_list [t : ts] [tk : tks] ci type_var_heap td_infos
		# (sign_class, type_class, type_var_heap, td_infos) = signClassOfType t.at_type group_nr ci type_var_heap td_infos
		  (sign_classes, hio_signs, type_var_heap, td_infos) = collect_sign_classes_of_type_list ts tks ci type_var_heap td_infos
		  sign_classes = [sign_class : sign_classes]
		| IsArrowKind tk
			= (sign_classes, [type_class:hio_signs], type_var_heap, td_infos)
			= (sign_classes, hio_signs, type_var_heap, td_infos)
	collect_sign_classes_of_type_list [] _ ci type_var_heap td_infos
		= ([], [], type_var_heap, td_infos)

	determine_cummulative_sign [sc : scs] sign_class type_index cumm_class
		# cumm_class = sign_class_to_sign sign_class type_index *+ sc + cumm_class
		= determine_cummulative_sign scs sign_class (inc type_index) cumm_class
	determine_cummulative_sign [] _ _ cumm_class
		= cumm_class
	
	adjust_sign_class {sc_pos_vect,sc_neg_vect} arity
		= { sc_pos_vect = sc_pos_vect >> arity, sc_neg_vect = sc_neg_vect >> arity }

signClassOfType (CV tv :@: types) group_nr ci type_var_heap td_infos
	# (sign_class, type_class, type_var_heap, td_infos) = signClassOfTypeVariable tv ci type_var_heap td_infos
	  (sign_class, type_var_heap, td_infos) = sign_class_of_type_list types group_nr type_class 0 sign_class ci type_var_heap td_infos
	= (sign_class, BottomSignClass, type_var_heap, td_infos)
where	  	
	sign_class_of_type_list [{at_type} : ts] group_nr cv_sign_class type_index cumm_class ci type_var_heap td_infos
		# (sign_class, _, type_var_heap, td_infos) = signClassOfType at_type group_nr ci type_var_heap td_infos
		  cumm_class = (sign_class_to_sign cv_sign_class type_index *+ sign_class) + cumm_class
		= sign_class_of_type_list ts group_nr sign_class (inc type_index) cumm_class ci type_var_heap td_infos
	sign_class_of_type_list [] _ _ _ cumm_class ci type_var_heap td_infos
		= (cumm_class, type_var_heap, td_infos)

signClassOfType (arg_type --> res_type) group_nr ci type_var_heap td_infos
	# (arg_class, _, type_var_heap, td_infos) = signClassOfType arg_type.at_type group_nr ci type_var_heap td_infos
	  (res_class, _, type_var_heap, td_infos) = signClassOfType res_type.at_type group_nr ci type_var_heap td_infos
	= (NegativeSign *+ arg_class + PositiveSign *+ res_class, BottomSignClass, type_var_heap, td_infos)

signClassOfType type _ _ type_var_heap td_infos
	= (BottomSignClass, BottomSignClass, type_var_heap, td_infos)

propClassification :: !Index !Index ![PropClassification] !{# CommonDefs } !*TypeVarHeap !*TypeDefInfos
	-> (!PropClassification, !*TypeVarHeap, !*TypeDefInfos)
propClassification type_index module_index hio_props defs type_var_heap td_infos
	# {td_args, td_name} = defs.[module_index].com_type_defs.[type_index]
	  (td_info, td_infos) = td_infos![module_index].[type_index]
	= determinePropClassOfTypeDef type_index module_index td_args td_info hio_props defs type_var_heap td_infos

determinePropClassOfTypeDef :: !Int !Int ![ATypeVar] !TypeDefInfo ![PropClassification] {# CommonDefs} !*TypeVarHeap !*TypeDefInfos
	-> (!PropClassification,!*TypeVarHeap, !*TypeDefInfos)
determinePropClassOfTypeDef type_index module_index td_args {tdi_classification, tdi_kinds, tdi_group, tdi_group_vars, tdi_cons_vars, tdi_group_nr}
			hio_props ci type_var_heap td_infos
	# hio_props = removeTopClasses tdi_cons_vars hio_props
	  result = retrievePropClassification hio_props tdi_classification
					// ---> (td_args, tdi_kinds, tdi_group_vars)
	= case result of
		Yes {ts_type_prop}
			-> (ts_type_prop, type_var_heap, td_infos)
		No
			# type_var_heap = bind_type_vars_to_props td_args tdi_group_vars tdi_cons_vars hio_props type_var_heap
			  (ts_type_prop, type_var_heap, td_infos) = newPropClassOfTypeDefGroup type_index module_index tdi_group hio_props
			  		tdi_group_nr ci type_var_heap td_infos
			-> (ts_type_prop, foldSt restore_binds_of_type_var td_args type_var_heap, td_infos)
//					---> ("determinePropClassOfTypeDef", ci.[module_index].com_type_defs.[type_index].td_name, ts_type_prop)
where
	bind_type_vars_to_props [{atv_variable={tv_info_ptr}} : tvs] [gv : gvs] cons_vars hio_props type_var_heap
		#! old_info = sreadPtr tv_info_ptr type_var_heap
		# sign = determine_classification gv cons_vars hio_props NoPropClass
		= bind_type_vars_to_props tvs gvs cons_vars hio_props (writePtr tv_info_ptr (TVI_PropClass gv sign old_info) type_var_heap)
	bind_type_vars_to_props [] group_vars cons_vars hio_props type_var_heap
		= type_var_heap

	determine_classification gv [cv : cvs] hio_props=:[tc : tcs] cumm_prop_class
		| isATopConsVar cv
			| gv == decodeTopConsVar cv
				= PropClass
				= determine_classification gv cvs tcs cumm_prop_class
		| gv == cv
			= determine_classification gv cvs tcs (tc bitor cumm_prop_class)
			= determine_classification gv cvs tcs cumm_prop_class
	determine_classification gv cons_vars [] cumm_prop_class
		= cumm_prop_class

	restore_binds_of_type_var {atv_variable={tv_info_ptr}} type_var_heap
		# (TVI_PropClass _ _ old_info, type_var_heap) = readPtr tv_info_ptr type_var_heap
		= type_var_heap <:= (tv_info_ptr, old_info)

newPropClassOfTypeDefGroup :: !Int !Int ![Global Int] ![PropClassification] !Int !{#CommonDefs} !*TypeVarHeap !*TypeDefInfos
			-> *(!PropClassification, !*TypeVarHeap, !*TypeDefInfos)
newPropClassOfTypeDefGroup type_index module_index group hio_props group_nr ci type_var_heap td_infos
	# (cumm_prop_env, type_var_heap, td_infos) = collect_prop_class_of_type_defs group group_nr ci NoPropClass type_var_heap td_infos 
	  (prop_class, td_infos) = update_prop_class_of_group type_index module_index group cumm_prop_env hio_props ci td_infos
//			 ---> ("newPropClassOfTypeDefGroup", (type_index, module_index), cumm_prop_env)
	= (prop_class, type_var_heap, td_infos)
where
	update_prop_class_of_group my_index module_index [] cumm_prop_env hio_props ci td_infos
		= (NoPropClass, td_infos)
	update_prop_class_of_group my_index module_index [{glob_module,glob_object} : group] cumm_prop_env hio_props ci td_infos
		# (tdi=:{tdi_group_vars,tdi_classification},td_infos) = td_infos![glob_module].[glob_object]
		  prop_class = determine_prop_class tdi_group_vars cumm_prop_env NoPropClass 0
		  tdi_classification = addPropClassification hio_props prop_class tdi_classification
		  td_infos = { td_infos & [glob_module].[glob_object] = { tdi & tdi_classification = tdi_classification }}
		  (my_prop_class, td_infos) = update_prop_class_of_group my_index module_index group cumm_prop_env hio_props ci td_infos
		| glob_module == module_index && my_index == glob_object
//			 ---> ("update_prop_class_of_group", (my_index, module_index), (glob_object, glob_module), prop_class)
			= (prop_class, td_infos)
			= (my_prop_class, td_infos)

	determine_prop_class [gv : gvs] cumm_prop_env prop_class var_index
		| IsPropagating cumm_prop_env gv
			= determine_prop_class gvs cumm_prop_env (prop_class bitor (IndexToPropClass var_index)) (inc var_index)
			= determine_prop_class gvs cumm_prop_env prop_class (inc var_index)
	determine_prop_class [] cumm_prop_env prop_class var_index
		= prop_class

	collect_prop_class_of_type_defs [] group_nr ci cumm_prop_env type_var_heap td_infos
		= (cumm_prop_env, type_var_heap, td_infos)
	collect_prop_class_of_type_defs [{glob_module,glob_object} : group] group_nr ci cumm_prop_env type_var_heap td_infos 
		# {td_rhs} = ci.[glob_module].com_type_defs.[glob_object]
		# (cumm_prop_env, type_var_heap, td_infos) = prop_class_of_type_def glob_module td_rhs group_nr ci cumm_prop_env type_var_heap td_infos
		= collect_prop_class_of_type_defs group group_nr ci cumm_prop_env type_var_heap td_infos

	prop_class_of_type_def :: !Int !TypeRhs !Int !{#CommonDefs} !PropClassification !*TypeVarHeap *TypeDefInfos
		-> (!PropClassification, !*TypeVarHeap, !*TypeDefInfos)
	prop_class_of_type_def module_index (AlgType conses) group_nr ci cumm_prop_env type_var_heap td_infos
		= prop_class_of_type_conses module_index conses group_nr ci cumm_prop_env type_var_heap td_infos
	prop_class_of_type_def module_index (SynType {at_type}) group_nr ci cumm_prop_env type_var_heap td_infos
		# (prop_class, _, type_var_heap, td_infos) = propClassOfType at_type group_nr ci type_var_heap td_infos
		= (cumm_prop_env bitor prop_class, type_var_heap, td_infos)
	prop_class_of_type_def module_index (RecordType {rt_constructor}) group_nr ci cumm_prop_env type_var_heap td_infos
		= prop_class_of_type_conses module_index [rt_constructor] group_nr ci cumm_prop_env type_var_heap td_infos
	prop_class_of_type_def module_index (AbstractType _) _ _ _ type_var_heap td_infos
		= (PropClass, type_var_heap, td_infos)

	prop_class_of_type_conses module_index [{ds_index}:conses] group_nr ci cumm_prop_class type_var_heap td_infos
		#! cons_def = ci.[module_index].com_cons_defs.[ds_index]
		#  (cumm_prop_class, type_var_heap, td_infos) = prop_class_of_type_of_list cons_def.cons_type.st_args group_nr ci cumm_prop_class type_var_heap td_infos
		= prop_class_of_type_conses module_index conses group_nr ci cumm_prop_class type_var_heap td_infos
	prop_class_of_type_conses module_index [] _ _ cumm_prop_class type_var_heap td_infos
		= (cumm_prop_class, type_var_heap, td_infos)

	prop_class_of_type_of_list [{at_type} : types] group_nr ci cumm_prop_class type_var_heap td_infos
		# (prop_class, _, type_var_heap, td_infos) = propClassOfType at_type group_nr ci type_var_heap td_infos
		= prop_class_of_type_of_list types group_nr ci (cumm_prop_class bitor prop_class) type_var_heap td_infos
	prop_class_of_type_of_list [] _ _ cumm_prop_class type_var_heap td_infos
		= (cumm_prop_class, type_var_heap, td_infos)


IndexToPropClass index :== 1 << index
IsPropagating prop_class_of_type type_index :== prop_class_of_type == (prop_class_of_type bitor IndexToPropClass type_index)
AdjustPropClass prop_class arity :== prop_class >> arity


propClassOfTypeVariable :: !TypeVar !{#CommonDefs} !*TypeVarHeap !*TypeDefInfos
	-> *(!PropClassification,!PropClassification, !*TypeVarHeap, !*TypeDefInfos)
propClassOfTypeVariable {tv_info_ptr} ci type_var_heap td_infos
	#! var_info = sreadPtr tv_info_ptr type_var_heap
	= case var_info of
		TVI_PropClass group_var_index var_class _
			-> (IndexToPropClass group_var_index, var_class, type_var_heap, td_infos)
		_
			-> (NoPropClass, PropClass, type_var_heap, td_infos)

propClassOfType :: !Type !Int !{#CommonDefs} !*TypeVarHeap !*TypeDefInfos -> *(!PropClassification,!PropClassification, !*TypeVarHeap, !*TypeDefInfos)
propClassOfType (TV tv) _ ci type_var_heap td_infos
	= propClassOfTypeVariable tv ci type_var_heap td_infos

propClassOfType (TA {type_name,type_index = {glob_module, glob_object}} types) group_nr ci type_var_heap td_infos
	# ({tdi_group_nr,tdi_kinds}, td_infos) = td_infos![glob_module].[glob_object]
	| tdi_group_nr == group_nr
		= (NoPropClass, PropClass, type_var_heap, td_infos )
		# {td_args,td_arity} = ci.[glob_module].com_type_defs.[glob_object]
		  (td_info, td_infos) = td_infos![glob_module].[glob_object]
		  (prop_classes, hio_signs, type_var_heap, td_infos) = collect_prop_classes_of_hio_types types tdi_kinds group_nr ci type_var_heap td_infos 
		  (type_class, type_var_heap, td_infos) = determinePropClassOfTypeDef glob_object glob_module td_args td_info hio_signs ci type_var_heap td_infos
		  (prop_class, type_var_heap, td_infos) = prop_classes_of_type_list types tdi_kinds prop_classes type_class 0 group_nr ci NoPropClass type_var_heap td_infos
		= (prop_class, AdjustPropClass type_class td_arity, type_var_heap, td_infos)
//			---> ("propClassOfType (TA ...)", type_name, prop_class)

where
	collect_prop_classes_of_hio_types [{at_type} : types] [ KindArrow _ : tks ] group_nr ci type_var_heap td_infos
		 # (prop_class, type_class, type_var_heap, td_infos) = propClassOfType at_type group_nr ci type_var_heap td_infos
		   (prop_classes, hio_signs, type_var_heap, td_infos) = collect_prop_classes_of_hio_types types tks group_nr ci type_var_heap td_infos
		 = ([prop_class : prop_classes], [type_class : hio_signs], type_var_heap, td_infos)
	collect_prop_classes_of_hio_types [_ : types] [ _ : tks ] _ _ type_var_heap td_infos
		= ([], [], type_var_heap, td_infos)
	collect_prop_classes_of_hio_types [] _ _ _ type_var_heap td_infos
		= ([], [], type_var_heap, td_infos)
	
	prop_classes_of_type_list [ _ : types ] [ KindArrow _ : tks] [pc : pcs] prop_class_of_type type_index group_nr ci cumm_class type_var_heap td_infos
		| IsPropagating prop_class_of_type type_index 
			= prop_classes_of_type_list types tks pcs prop_class_of_type (inc type_index) group_nr ci (cumm_class bitor pc) type_var_heap td_infos
			= prop_classes_of_type_list types tks pcs prop_class_of_type (inc type_index) group_nr ci cumm_class type_var_heap td_infos
	prop_classes_of_type_list [ {at_type} : types] [ _ : tks] pcs prop_class_of_type type_index group_nr ci cumm_class type_var_heap td_infos
		| IsPropagating prop_class_of_type type_index 
			# (pc, _, type_var_heap, td_infos) = propClassOfType at_type group_nr ci type_var_heap td_infos
			= prop_classes_of_type_list types tks pcs prop_class_of_type (inc type_index) group_nr ci (cumm_class bitor pc) type_var_heap td_infos
			= prop_classes_of_type_list types tks pcs prop_class_of_type (inc type_index) group_nr ci cumm_class type_var_heap td_infos
	prop_classes_of_type_list [] [] _ _ _ _ _ cumm_class type_var_heap td_infos
		= (cumm_class, type_var_heap, td_infos)

propClassOfType (CV tv :@: types) group_nr ci type_var_heap td_infos
	# (prop_class, type_class, type_var_heap, td_infos) = propClassOfTypeVariable tv ci type_var_heap td_infos
	  (prop_class, type_var_heap, td_infos) = prop_class_of_type_list types type_class 0 group_nr ci prop_class type_var_heap td_infos
	= (prop_class, NoPropClass, type_var_heap, td_infos)
where	  	
	prop_class_of_type_list [{at_type} : types] cv_prop_class type_index group_nr ci cumm_class type_var_heap td_infos
		| IsPropagating cv_prop_class type_index 
			# (pc, _, type_var_heap, td_infos) = propClassOfType at_type group_nr ci type_var_heap td_infos
			= prop_class_of_type_list types cv_prop_class (inc type_index) group_nr ci (cumm_class bitor pc) type_var_heap td_infos
			= prop_class_of_type_list types cv_prop_class (inc type_index) group_nr ci cumm_class type_var_heap td_infos
	prop_class_of_type_list [] _ _ _ _ cumm_class type_var_heap td_infos
		= (cumm_class, type_var_heap, td_infos)

propClassOfType _ _ _ type_var_heap td_infos
	= (NoPropClass, NoPropClass, type_var_heap, td_infos)

