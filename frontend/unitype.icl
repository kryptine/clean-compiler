implementation module unitype

import StdEnv

import syntax, analunitypes, type, utilities

::	CoercionPosition =
	{	cp_expression	:: !Expression
	}

AttrUni			:== 0
AttrMulti		:== 1
FirstAttrVar	:== 2

::	CoercionTree	= CT_Node !Int !CoercionTree !CoercionTree | CT_Empty | CT_Unique | CT_NonUnique /* | CT_Existential !Int */

::	Coercions		= { coer_demanded :: !.{! .CoercionTree}, coer_offered :: !.{! .CoercionTree }}

::	AttributePartition :== {# Int}

::	PartitioningInfo = 
	{	pi_marks :: 		!.AttributePartition
	,	pi_next_num ::		!Int
	,	pi_groups ::		![[Int]]
	,	pi_deps ::			![Int]
	}

uniquenessError :: !CoercionPosition !String !*ErrorAdmin -> *ErrorAdmin
uniquenessError position mess err=:{ea_file,ea_loc}
	# ea_file = ea_file <<< "Uniqueness error " <<< hd ea_loc <<< ": \"" <<<  position <<< '\"' <<< mess <<< '\n'
	= { err & ea_file = ea_file, ea_ok = False}

::	BOOLVECT :== Int

BITINDEX temp_var_id :== temp_var_id >> 5
BITNUMBER temp_var_id :== temp_var_id bitand 31

isPositive :: !TempVarId !{# BOOLVECT } -> Bool
isPositive var_id cons_vars
	= cons_vars.[BITINDEX var_id] bitand (1 << BITNUMBER var_id) <> 0

determineAttributeCoercions :: !AType !AType !Bool !CoercionPosition !u:{! Type} !*Coercions !{# CommonDefs } 
	!{# BOOLVECT } !*TypeDefInfos !*TypeHeaps !*ErrorAdmin
		-> (!u:{! Type}, !*Coercions, !*TypeDefInfos, !*TypeHeaps, !*ErrorAdmin) 
determineAttributeCoercions off_type dem_type coercible position subst coercions defs cons_vars td_infos type_heaps error
	# (exp_off_type, es) = expandType defs cons_vars off_type (subst, { es_type_heaps = type_heaps, es_td_infos = td_infos})
	  (exp_dem_type, (subst, {es_td_infos,es_type_heaps})) = expandType defs cons_vars dem_type es
	  (ok, {crc_type_heaps, crc_coercions, crc_td_infos}) = coerce defs cons_vars exp_off_type exp_dem_type (if coercible PositiveSign TopSign)
	  		 { crc_type_heaps = es_type_heaps, crc_coercions = coercions, crc_td_infos = es_td_infos}
	| ok
		= (subst, crc_coercions, crc_td_infos, crc_type_heaps, error)
//					---> ("OK", off_type, exp_off_type, dem_type, exp_dem_type)
		= (subst, crc_coercions, crc_td_infos, crc_type_heaps, uniquenessError position " invalid coercion" error)
					---> (off_type, exp_off_type, dem_type, exp_dem_type)

NotChecked :== -1	
DummyAttrNumber :== -1
::	AttributeGroups	:== {! [Int]}

partitionateAttributes :: !{! CoercionTree} !{! *CoercionTree} -> (!AttributePartition, !{! CoercionTree})
partitionateAttributes coer_offered coer_demanded
	#! max_attr_nr = size coer_offered
	# partitioning_info = { pi_marks = createArray max_attr_nr NotChecked, pi_deps = [], pi_next_num = 0, pi_groups = [] }
	# {pi_marks,pi_groups} = partitionate_attributes FirstAttrVar max_attr_nr coer_offered partitioning_info
	  (nr_of_groups, groups) = reverse_and_length pi_groups 0 []
	  partition = build_partition 0 groups pi_marks
	# demanded = { CT_Empty \\ i <- [0 .. nr_of_groups - 1] }
	= (partition, adjust_coercions 0 groups partition coer_offered coer_demanded demanded)
where
	visit_attributes :: !CoercionTree !Int !Int !{! CoercionTree} !*PartitioningInfo -> *(!Int, !*PartitioningInfo)
	visit_attributes (CT_Node attr left right) max_attr_nr min_dep coer_offered pi=:{pi_marks}
		#! mark = pi_marks.[attr]
		| mark == NotChecked
			# (mark, pi) = partitionate_attribute attr max_attr_nr coer_offered pi
			  (min_dep, pi) = visit_attributes left max_attr_nr (min min_dep mark)  coer_offered pi
			= visit_attributes right max_attr_nr min_dep coer_offered pi
		# (min_dep, pi) = visit_attributes left max_attr_nr (min min_dep mark) coer_offered pi
		= visit_attributes right max_attr_nr min_dep coer_offered pi
	visit_attributes tree max_attr_nr min_dep coer_offered pi
		= (min_dep, pi)
	
	reverse_and_length :: ![a] !Int ![a] -> (!Int, ![a])
	reverse_and_length [] length list = (length, list)
	reverse_and_length [ x : xs ] length list = reverse_and_length xs (inc length) [x : list]
	
 	partitionate_attributes :: !Int !Int !{!CoercionTree} !*PartitioningInfo -> *PartitioningInfo
	partitionate_attributes from_index max_attr_nr coer_offered pi=:{pi_marks}
		| from_index == max_attr_nr
			= pi
		| pi_marks.[from_index] == NotChecked
			# (_, pi) = partitionate_attribute from_index max_attr_nr coer_offered pi
			= partitionate_attributes (inc from_index) max_attr_nr coer_offered pi
		= partitionate_attributes (inc from_index) max_attr_nr coer_offered pi

	partitionate_attribute :: !Int !Int !{!CoercionTree} !*PartitioningInfo -> *(!Int, !*PartitioningInfo)
	partitionate_attribute attr max_attr_nr coer_offered=:{ [attr] = off_attributes } pi=:{pi_next_num}
		# (min_dep, pi) = visit_attributes off_attributes max_attr_nr max_attr_nr coer_offered (push_on_dep_stack attr pi)
		= try_to_close_group attr pi_next_num min_dep max_attr_nr pi
	where		
		push_on_dep_stack attr pi=:{pi_deps,pi_marks,pi_next_num}
			= { pi & pi_deps = [attr : pi_deps], pi_marks = { pi_marks & [attr] = pi_next_num }, pi_next_num = inc pi_next_num}

		try_to_close_group attr attr_nr min_dep max_attr_nr pi=:{pi_marks, pi_deps, pi_groups}
			| attr_nr <= min_dep
				# (pi_deps, pi_marks, group) = close_group attr pi_deps pi_marks [] max_attr_nr
				= (max_attr_nr, { pi & pi_deps = pi_deps, pi_marks = pi_marks, pi_groups = [group : pi_groups] })
				= (min_dep, pi)
		where
			close_group attr [d:ds] marks group max_attr_nr
				# marks = { marks & [d] = max_attr_nr }
				| d == attr
					= (ds, marks, [d : group])
					= close_group attr ds marks [d : group] max_attr_nr

	build_partition group_nr [] partition
		= partition
	build_partition group_nr [group : groups] partition
		= build_partition (inc group_nr) groups (build_partition_of_group group_nr group partition)
	where
		build_partition_of_group group_nr [attr : attrs] partition
			= build_partition_of_group group_nr attrs { partition & [attr] = group_nr }
		build_partition_of_group group_nr [] partition
			= partition

	adjust_coercions group_index [group : groups] partition coer_offered coer_demanded demanded
		# (combined_tree, coer_demanded) = combine_coercion_trees group_index group partition CT_Empty coer_offered coer_demanded
		= adjust_coercions (inc group_index) groups partition coer_offered coer_demanded { demanded & [ group_index ] = combined_tree }
	adjust_coercions group_index [] partition coer_offered coer_demanded demanded
		= demanded

	combine_coercion_trees group_index [ attr : attrs ] partition merged_tree coer_offered coer_demanded
		| isNonUnique coer_offered.[attr]
			= (CT_NonUnique, coer_demanded)
/*		| isExistential coer_offered.[attr]
			= (CT_Existential DummyAttrNumber, coer_demanded)
*/		# (next_tree, coer_demanded) = replace coer_demanded attr CT_Empty
		| isUnique next_tree
			= (CT_Unique, coer_demanded)
			# merged_tree = rebuild_tree group_index partition next_tree merged_tree
			= combine_coercion_trees group_index attrs partition merged_tree coer_offered coer_demanded
	combine_coercion_trees group_index [ ] partition merged_tree coer_offered coer_demanded
		= (merged_tree, coer_demanded)
		

	rebuild_tree :: !Index !AttributePartition !*CoercionTree !*CoercionTree -> *CoercionTree
	rebuild_tree group_index partition (CT_Node attr left right) tree
		# tree = rebuild_tree group_index partition left tree
		  tree = rebuild_tree group_index partition right tree
		#! attr_nr = partition.[attr]
		| attr_nr == group_index
			= tree
		# { tree } = insert partition.[attr] tree
		= tree	
	where
		insert ::  !Int !*CoercionTree -> *CoercionTreeRecord
		insert new_attr CT_Empty
			=  { tree = CT_Node new_attr CT_Empty CT_Empty }
		insert new_attr (CT_Node this_attr ct_less ct_greater)
			| new_attr < this_attr
				# { tree } = insert new_attr ct_less
				= { tree = CT_Node this_attr tree ct_greater }
			| new_attr > this_attr
				# { tree } = insert new_attr ct_greater
				= { tree = CT_Node this_attr ct_less tree }
				= { tree = CT_Node this_attr ct_less ct_greater }
	rebuild_tree group_index partition empty_tree tree
		= tree

::	CoercionTreeRecord = { tree :: !.CoercionTree }


liftSubstitution :: !*{! Type} !{# CommonDefs } !Int !*TypeVarHeap !*TypeDefInfos -> (*{! Type}, !Int, !*TypeVarHeap, !*TypeDefInfos)
liftSubstitution subst modules attr_store type_var_heap td_infos 
	# ls = { ls_next_attr = attr_store, ls_td_infos = td_infos, ls_type_var_heap = type_var_heap}
	= lift_substitution 0 modules subst ls
where
	lift_substitution var_index modules subst ls
		| var_index < size subst
			#! type = subst.[var_index]
			# (type, _, _, subst, ls) = lift modules type subst ls
			= lift_substitution (inc var_index) modules { subst & [var_index] = type } ls
			= (subst, ls.ls_next_attr, ls.ls_type_var_heap, ls.ls_td_infos)

adjustSignClass :: !SignClassification !Int -> SignClassification
adjustSignClass {sc_pos_vect,sc_neg_vect} arity
	= { sc_pos_vect = sc_pos_vect >> arity, sc_neg_vect = sc_neg_vect >> arity }

// adjustPropClass :: !PropClassification !Int -> PropClassification
adjustPropClass prop_class arity :== prop_class >> arity

::	LiftState = 
	{	ls_next_attr		:: !Int
	,	ls_type_var_heap	:: !.TypeVarHeap
	,	ls_td_infos			:: !.TypeDefInfos
	}


liftTempTypeVariable :: !{# CommonDefs } !TempVarId !*{! Type} !*LiftState
	-> (!Type, !SignClassification, !PropClassification, !*{! Type}, !*LiftState)
liftTempTypeVariable modules tv_number subst ls
	#! type = subst.[tv_number]
	= case type of
		TE	-> (TempV tv_number, TopSignClass, PropClass, subst, ls)
		_	-> lift modules type subst ls

class lift a :: !{# CommonDefs } !a !*{! Type} !*LiftState
	-> (!a, !SignClassification, !PropClassification, !*{! Type}, !*LiftState)


instance lift Type
where
	lift modules (TempV tv_number) subst ls
		= liftTempTypeVariable modules tv_number subst ls
	lift modules (arg_type --> res_type) subst ls
		# (arg_type, _, _, subst, ls) = lift modules arg_type subst ls
		  (res_type, _, _, subst, ls) = lift modules res_type subst ls
		= (arg_type --> res_type, BottomSignClass, NoPropClass, subst, ls)
	lift modules (TA cons_id=:{type_index={glob_object,glob_module},type_arity} cons_args) subst ls
		# (cons_args, sign_classes, prop_classes, subst, ls) = lift_list modules cons_args subst ls
		  (type_prop, ls_type_var_heap, ls_td_infos) = typeProperties glob_object glob_module sign_classes prop_classes modules ls.ls_type_var_heap ls.ls_td_infos
		= (TA  { cons_id & type_prop = type_prop } cons_args,
					adjustSignClass type_prop.tsp_sign type_arity, adjustPropClass type_prop.tsp_propagation type_arity,
			subst, { ls & ls_td_infos = ls_td_infos, ls_type_var_heap = ls_type_var_heap})
	lift modules (TempCV temp_var :@: types) subst ls
		# (type, sign_class, prop_class, subst, ls) = liftTempTypeVariable modules temp_var subst ls
		  (types, _, _, subst, ls) = lift_list modules types subst ls
		= case type of
			TA type_cons cons_args
				# nr_of_new_args = length types
				-> (TA { type_cons & type_arity = type_cons.type_arity + nr_of_new_args } (cons_args ++ types),
						adjustSignClass sign_class nr_of_new_args, adjustPropClass prop_class nr_of_new_args, subst, ls)
			TempV tv_number
				-> (TempCV tv_number :@: types, TopSignClass, PropClass, subst, ls)
			cons_var :@: cv_types
				-> (cons_var :@: (cv_types ++ types), TopSignClass, PropClass, subst, ls)
	lift modules type subst ls
		= (type, BottomSignClass, NoPropClass,  subst, ls)
	
instance lift AType
where
	lift modules attr_type=:{at_attribute,at_type} subst ls
		# (at_type, sign_class, prop_class, subst, ls) = lift modules at_type subst ls
		| type_is_non_coercible at_type
			= ({attr_type & at_type = at_type}, sign_class, prop_class, subst, ls)
			= ({attr_type & at_attribute = TA_TempVar ls.ls_next_attr, at_type = at_type},
					sign_class, prop_class, subst, {ls & ls_next_attr = inc ls.ls_next_attr})
	where
		type_is_non_coercible (TempV _)
			= True
		type_is_non_coercible (TempQV _)
			= True
		type_is_non_coercible (_ --> _)
			= True
		type_is_non_coercible (_ :@: _)
			= True
		type_is_non_coercible _
			= False


lift_list :: !{#CommonDefs} ![a] !*{!Type} !*LiftState
	-> (![a], ![SignClassification], ![PropClassification], !*{!Type}, !*LiftState) | lift a
lift_list modules [] subst ls
	= ([], [], [], subst, ls)
lift_list modules [t:ts] subst ls
	# (t, sign_class, prop_class, subst, ls) = lift modules t subst ls
	  (ts, sign_classes, prop_classes, subst, ls) = lift_list modules ts subst ls
	= ([t:ts], [sign_class : sign_classes], [prop_class : prop_classes], subst, ls)

::	ExpansionState = 
	{	es_type_heaps	:: !.TypeHeaps
	,	es_td_infos		:: !.TypeDefInfos
	}

class expandType a :: !{# CommonDefs } !{# BOOLVECT } !a !*(!u:{! Type}, !*ExpansionState) -> (!a, !*(!u:{! Type}, !*ExpansionState))

instance expandType AType
where
	expandType modules cons_vars attr_type=:{at_type, at_attribute} (subst, es=:{es_type_heaps})
		# (at_attribute, th_attrs) = expand_attribute at_attribute es_type_heaps.th_attrs
		  (at_type, subst_and_es) = expandType modules cons_vars at_type (subst, {es & es_type_heaps = { es_type_heaps & th_attrs = th_attrs }})
		= ({ attr_type & at_type = at_type, at_attribute = at_attribute }, subst_and_es)
	where
		expand_attribute (TA_Var {av_info_ptr}) attr_var_heap
			# (AVI_Attr attr, attr_var_heap) = readPtr av_info_ptr attr_var_heap
			= (attr, attr_var_heap)
		expand_attribute attr attr_var_heap
			= (attr, attr_var_heap)
	
expandTempTypeVariable :: !TempVarId !*(!u:{! Type}, !*ExpansionState) -> (!Type, !*(!u:{! Type}, !*ExpansionState))
expandTempTypeVariable tv_number (subst, es)
	#! type = subst.[tv_number]
	= case type of
		TE	-> (TempV tv_number, (subst, es))
		_	-> (type, (subst, es))

instance expandType Type
where
	expandType modules cons_vars (TempV tv_number) es
		= expandTempTypeVariable tv_number es
	expandType modules cons_vars (TV {tv_info_ptr}) (subst, es=:{es_type_heaps})
		# (TVI_Type type, th_vars) = readPtr tv_info_ptr es_type_heaps.th_vars
		= (type, (subst, {es & es_type_heaps = { es_type_heaps & th_vars = th_vars }}))
	expandType modules cons_vars (arg_type --> res_type) es
		# (arg_type, es) = expandType modules cons_vars arg_type es
		  (res_type, es) = expandType modules cons_vars res_type es
		= (arg_type --> res_type, es)
	expandType modules cons_vars (TA cons_id=:{type_index={glob_object,glob_module}} cons_args) es
		# (cons_args, sign_classes, prop_classes, (subst,es=:{es_td_infos,es_type_heaps})) = expand_type_list modules cons_vars cons_args es
		  (type_prop, th_vars, es_td_infos)
		  			= typeProperties glob_object glob_module sign_classes prop_classes modules es_type_heaps.th_vars es_td_infos
		= (TA { cons_id & type_prop = type_prop } cons_args,
				(subst, { es & es_td_infos = es_td_infos, es_type_heaps = { es_type_heaps & th_vars = th_vars }}))
	where
		expand_type_list ::  !{#CommonDefs} !{# BOOLVECT } ![AType] !*(!u:{!Type}, !*ExpansionState)
			-> (![AType], ![SignClassification], ![PropClassification], !*(!u:{!Type}, !*ExpansionState))
		expand_type_list modules cons_vars [] es
			= ([], [], [], es)
		expand_type_list modules cons_vars [t:ts]  es
			# (t, es) = expandType modules cons_vars t es
			  (ts, sign_classes, prop_classes, es) = expand_type_list modules cons_vars ts es
			= case t.at_type of 
				TA {type_arity,type_prop} _
					-> ([t:ts], [adjustSignClass type_prop.tsp_sign type_arity : sign_classes],
								[adjustPropClass type_prop.tsp_propagation type_arity : prop_classes], es)
				TempV tmp_var_id
					| isPositive tmp_var_id cons_vars
						-> ([t:ts], [PosSignClass : sign_classes], [PropClass : prop_classes], es)
						-> ([t:ts], [TopSignClass : sign_classes], [NoPropClass : prop_classes], es)
				_
					-> ([t:ts], [TopSignClass : sign_classes], [PropClass : prop_classes], es)
					
	expandType modules cons_vars (TempCV temp_var :@: types) es
		# (type, es) = expandTempTypeVariable temp_var es
		  (types, es) = expandType modules cons_vars types es
		= case type of
			TA type_cons=:{type_arity} cons_args
				# nr_of_new_args = length types
				-> (TA { type_cons & type_arity = type_arity + nr_of_new_args } (cons_args ++ types), es)
			TempV tv_number
				-> (TempCV tv_number :@: types, es)
			cons_var :@: cv_types
				-> (cons_var :@: (cv_types ++ types), es)
	expandType modules cons_vars type es
		= (type, es)

instance expandType [a] | expandType a
where
	expandType modules cons_vars l es = mapSt (expandType modules cons_vars) l es
	
instance toInt TypeAttribute
where
	 toInt TA_Unique 				= AttrUni
	 toInt (TA_TempVar av_number)	= av_number
//	 toInt (TA_TempExVar av_number)	= av_number
	 toInt TA_Multi 				= AttrMulti
	 toInt TA_None 					= AttrMulti


instance * Bool
where
	(*) b1 b2 = b1 && b2 || not b1 && not b2

instance * Sign
where
	(*) sign1 sign2
		= {	pos_sign = sign1.pos_sign * sign2.pos_sign || sign1.neg_sign * sign2.neg_sign,
			neg_sign = sign1.pos_sign * sign2.neg_sign || sign1.neg_sign * sign2.pos_sign }
		
::	CoercionState =
	{	crc_type_heaps	:: !.TypeHeaps
	,	crc_coercions	:: !.Coercions
	,	crc_td_infos	:: !.TypeDefInfos
	}


class coerce a :: !{# CommonDefs} !{# BOOLVECT} !a !a !Sign !*CoercionState -> (!Bool, !*CoercionState)

/*

'coerceAttributes offered_attribute offered_attribute sign coercions' coerce offered_attribute to
offered_attribute according to sign. Failure is indicated by returning False as a result.

*/

coerceAttributes TA_Unique dem_attr {neg_sign} coercions
	| not neg_sign
		= (True, coercions)
coerceAttributes off_attr TA_Unique {pos_sign} coercions
	| not pos_sign
		= (True, coercions)
coerceAttributes (TA_TempVar av_number) dem_attr {neg_sign} coercions=:{coer_demanded}
	| not neg_sign && isUnique coer_demanded.[av_number]
		= (True, coercions)
coerceAttributes off_attr (TA_TempVar av_number) {pos_sign} coercions=:{coer_demanded}
	| not pos_sign && isUnique coer_demanded.[av_number]
		= (True, coercions)
/*
coerceAttributes off_attr TA_Multi {neg_sign} coercions
	| not neg_sign
		= (True, coercions)
coerceAttributes TA_Multi dem_attr {pos_sign} coercions
	| not pos_sign
		= (True, coercions)
*/
coerceAttributes (TA_TempVar av_number1) (TA_TempVar av_number2) {pos_sign,neg_sign} coercions
	| av_number1 == av_number2
		= (True, coercions)
	| pos_sign
		| neg_sign
			# (ok, coercions) = new_inequality av_number1 av_number2 coercions
			| ok
				= new_inequality av_number2 av_number1 coercions
				= (False, coercions)
			= new_inequality av_number1 av_number2 coercions
	| neg_sign
		= new_inequality av_number2 av_number1 coercions
		= (True, coercions)
where
	new_inequality :: !Int !Int !*Coercions  -> (!Bool, !*Coercions)
	new_inequality off_attr dem_attr coercions=:{coer_demanded, coer_offered}
/*		| isExistential coer_offered.[off_attr]
			#! off_attr_tree = coer_offered.[off_attr]
			= coerce_to_existential_attribute off_attr_tree dem_attr coercions
		| isExistential coer_demanded.[dem_attr]
			#! dem_attr_tree = coer_demanded.[off_attr]
			= coerce_to_existential_attribute dem_attr_tree off_attr coercions
*/		| isNonUnique coer_offered.[off_attr]
			| isUnique coer_demanded.[dem_attr]
				= (False, coercions)
				= (True, makeNonUnique dem_attr coercions)
		| isUnique coer_demanded.[dem_attr]
			= (True, makeUnique off_attr coercions)
		| isNonUnique coer_offered.[dem_attr] || isUnique coer_demanded.[off_attr]
			= (True, coercions)
			= (True, newInequality off_attr dem_attr coercions)
/*	
	coerce_to_existential_attribute (CT_Existential exi_number) attr_number coercions
		= coerceToExistentialAttribute exi_number attr_number coercions
*/
					
coerceAttributes TA_Unique (TA_TempVar av_number) {neg_sign} coercions=:{coer_offered}
	| isNonUnique coer_offered.[av_number]
		= (False, coercions)
		= (True, makeUnique av_number coercions)// ---> "*** 1 ***"
coerceAttributes (TA_TempVar av_number) TA_Unique {pos_sign} coercions=:{coer_offered}
	| isNonUnique coer_offered.[av_number]
		= (False, coercions)
		= (True, makeUnique av_number coercions)// ---> "*** 2 ***"
coerceAttributes TA_Multi (TA_TempVar av_number) {pos_sign} coercions=:{coer_demanded}
	| pos_sign
		| isUnique coer_demanded.[av_number]
			= (False, coercions)
			= (True, makeNonUnique av_number coercions)
		= (True, coercions)
coerceAttributes (TA_TempVar av_number) TA_Multi {neg_sign} coercions=:{coer_demanded}
	| neg_sign
		| isUnique coer_demanded.[av_number]
			= (False, coercions)
			= (True, makeNonUnique av_number coercions)
		= (True, coercions)
coerceAttributes TA_Unique TA_Multi _ coercions
	= (False, coercions)
coerceAttributes off_attr dem_attr {pos_sign,neg_sign} coercions
/*
	| pos_sign || neg_sign // ---> ("coerceAttributes", off_attr, dem_attr)
		= case off_attr of
			TA_TempExVar eav_number
				-> case dem_attr of
					TA_TempVar av_number
						-> coerceToExistentialAttribute eav_number av_number coercions
					TA_TempExVar eav_number2
						-> (eav_number == eav_number2, coercions)
					_
						-> (False, coercions)
				
			TA_TempVar av_number
				-> case dem_attr of
					TA_TempExVar eav_number
						-> coerceToExistentialAttribute eav_number av_number coercions
					_
						-> (True, coercions)
			_
				-> case dem_attr of
					TA_TempExVar eav_number
						-> (False, coercions)
					_
						-> (True, coercions)
*/
		= (True, coercions)

/*
coerceToExistentialAttribute exi_attr_number attr_number coercions=:{coer_demanded, coer_offered}
	#! dem_attr_tree = coer_demanded.[attr_number]
	   off_attr_tree = coer_offered.[attr_number]
	= case dem_attr_tree ---> ("coerceToExistentialAttribute", exi_attr_number, attr_number, dem_attr_tree, off_attr_tree) of
		CT_Unique
			-> (False, coercions)
		CT_Existential exi_attr_number2
			-> (exi_attr_number == exi_attr_number2, coercions)
		_
			-> case off_attr_tree of
				CT_NonUnique
					-> (False, coercions)
				_
					-> (True, make_attr_existential attr_number exi_attr_number coercions)
	
where
	make_attr_existential :: !Int  !Int !*Coercions -> *Coercions
	make_attr_existential attr exi_attr {coer_demanded, coer_offered}
		# (dem_heaps_and_coercions, coer_demanded) = replace coer_demanded attr (CT_Existential exi_attr)
		  (off_heaps_and_coercions, coer_offered) = replace coer_offered attr (CT_Existential exi_attr)
		= make_existential off_heaps_and_coercions exi_attr (
			make_existential dem_heaps_and_coercions exi_attr {coer_offered = coer_offered, coer_demanded = coer_demanded})

	make_existential (CT_Node this_attr ct_less ct_greater) exi_attr coercions
		# coercions = make_attr_existential this_attr exi_attr coercions
		  coercions = make_existential ct_less exi_attr coercions
		  coercions = make_existential ct_greater exi_attr coercions
		= coercions
	make_existential tree exi_attr coercions
		= coercions
*/
newInequality :: !Int !Int !*Coercions -> *Coercions 
newInequality off_attr dem_attr coercions=:{coer_demanded, coer_offered}
	# (dem_coercions, coer_demanded) = replace coer_demanded off_attr CT_Empty
	  (succ, dem_coercions) = insert dem_attr dem_coercions
	  coer_demanded = { coer_demanded & [off_attr] = dem_coercions }
	| succ
		# (off_coercions, coer_offered) = replace coer_offered dem_attr CT_Empty
	  	  (succ, off_coercions) = insert off_attr off_coercions
	 	  coer_offered = { coer_offered & [dem_attr] = off_coercions }
		= {coer_demanded = coer_demanded, coer_offered = coer_offered}
		= {coer_demanded = coer_demanded, coer_offered = coer_offered}
where

	insert ::  !Int !*CoercionTree -> (!Bool, !*CoercionTree)
	insert new_attr CT_Empty
		=  (True, CT_Node new_attr CT_Empty CT_Empty)
	insert new_attr (CT_Node this_attr ct_less ct_greater)
		| new_attr < this_attr
			# (succ, ct_less) = insert new_attr ct_less
			= (succ, CT_Node this_attr ct_less ct_greater)
		| new_attr > this_attr
			# (succ, ct_greater) = insert new_attr ct_greater
			= (succ, CT_Node this_attr ct_less ct_greater)
			= (False, CT_Node this_attr ct_less ct_greater)
	
isNonUnique :: !CoercionTree -> Bool
isNonUnique CT_NonUnique	= True
isNonUnique _ 				= False

isUnique  :: !CoercionTree -> Bool
isUnique CT_Unique			= True
isUnique _					= False

/*
isExistential  :: !CoercionTree -> Bool
isExistential (CT_Existential exi_number)	= True
isExistential attr_tree						= False
*/
		
makeUnique :: !Int !*Coercions -> *Coercions
makeUnique attr {coer_demanded, coer_offered}
	# (off_coercions, coer_offered) = replace coer_offered attr CT_Empty
	  coer_demanded = { coer_demanded & [attr] = CT_Unique }
	= make_unique off_coercions {coer_offered = coer_offered, coer_demanded = coer_demanded}// ---> ("makeUnique :", attr)
where
	make_unique (CT_Node this_attr ct_less ct_greater) coercions
		# coercions = makeUnique this_attr coercions
		  coercions = make_unique ct_less coercions
		  coercions = make_unique ct_greater coercions
		= coercions
	make_unique tree coercions
		= coercions

tryToMakeUnique :: !Int !*Coercions -> (!Bool, !*Coercions)
tryToMakeUnique attr coercions=:{coer_offered}
	| isNonUnique coer_offered.[attr] // || isExistential coer_offered.[attr]
		= (False, coercions)
		= (True, makeUnique attr coercions)

makeNonUnique :: !Int !*Coercions -> *Coercions
makeNonUnique attr {coer_demanded, coer_offered}
	# (dem_coercions, coer_demanded) = replace coer_demanded attr CT_Empty
	  coer_offered = { coer_offered & [attr] = CT_NonUnique }
	= make_non_unique dem_coercions {coer_offered = coer_offered, coer_demanded = coer_demanded}
where
	make_non_unique (CT_Node this_attr ct_less ct_greater) coercions
		# coercions = makeNonUnique this_attr coercions
		  coercions = make_non_unique ct_less coercions
		  coercions = make_non_unique ct_greater coercions
		= coercions
	make_non_unique tree coercions
		= coercions

tryToMakeNonUnique :: !Int !*Coercions -> (!Bool, !*Coercions)
tryToMakeNonUnique attr coercions=:{coer_demanded}
	| isUnique coer_demanded.[attr] // || isExistential coer_demanded.[attr]
		= (False, coercions)
		= (True, makeNonUnique attr coercions)
//				---> ("tryToMakeNonUnique", attr)

instance coerce AType
where
	coerce defs cons_vars at1=:{at_attribute=attr1,at_type=type1} at2=:{at_attribute=attr2,at_type=type2} sign cs=:{crc_coercions}
		# sign = adjust_sign sign type1 cons_vars
		  (succ, crc_coercions) = coerceAttributes attr1 attr2 sign crc_coercions
		| succ
			# (succ, cs) = coerce defs cons_vars type1 type2 sign { cs & crc_coercions = crc_coercions }
			| succ
				# (succ1, crc_coercions) = add_propagation_inequalities attr1 type1 cs.crc_coercions
				  (succ2, crc_coercions) = add_propagation_inequalities attr2 type2 crc_coercions
				= (succ1 && succ2, { cs & crc_coercions = crc_coercions })
				= (False, cs)
			= (False, { cs & crc_coercions = crc_coercions })
				// ---> ("coerceAttributes", attr1, attr2, sign)

	where		

		adjust_sign :: !Sign !Type {# BOOLVECT} -> Sign
		adjust_sign sign (TempV _) cons_vars
			= TopSign
		adjust_sign sign (TempQV _) cons_vars
			= TopSign
		adjust_sign sign (_ --> _) cons_vars
			= TopSign
		adjust_sign sign (TempCV tmp_var_id :@: _) cons_vars
			| isPositive tmp_var_id cons_vars
				= sign
				= TopSign
		adjust_sign sign (_ :@: _) cons_vars
			= TopSign
		adjust_sign sign (TA {type_name, type_prop={tsp_coercible}} _) cons_vars
			| tsp_coercible
				= sign
				= TopSign
//					---> ("adjust_sign to top", type_name)
		adjust_sign sign _ cons_vars
			= sign

		add_propagation_inequalities attr (TA {type_prop={tsp_propagation}} cons_args) coercions
			= add_inequalities tsp_propagation attr cons_args coercions
		where
			add_inequalities prop_class attr _ coercions
				= (True, coercions)

			add_inequalities prop_class attr [] coercions
				= (True, coercions)
			add_inequalities prop_class attr [{at_attribute} : args] coercions
				| (prop_class bitand 1) == 0 //  || is_existential_attribute at_attribute coercions
					= add_inequalities (prop_class >> 1) attr args coercions
				# (succ, coercions) = coerceAttributes attr at_attribute PositiveSign coercions
				| succ
					= add_inequalities (prop_class >> 1) attr args coercions
					= (False, coercions)
							---> ("add_propagation_inequalities", attr, at_attribute)
/*
			is_existential_attribute (TA_TempExVar eav_number) coercions
				= True
			is_existential_attribute (TA_TempVar eav_number) {coer_offered}
				= isExistential coer_offered.[eav_number]
			is_existential_attribute _ {coer_offered}
				= False
*/ 
		add_propagation_inequalities attr type coercions
			= (True, coercions)
	
coercionsOfTypeList defs cons_vars [t1 : ts1] [t2 : ts2] sign_class type_index sign cs
	# arg_sign = sign * signClassToSign sign_class type_index
	  (ok, cs) = coerce defs cons_vars t1 t2 arg_sign cs
	| ok
		= coercionsOfTypeList defs cons_vars ts1 ts2 sign_class (inc type_index) sign cs
		= (False, cs)
coercionsOfTypeList defs cons_vars [] [] _ _ _ cs
	= (True, cs)

isSynonymType (SynType _)
	= True
isSynonymType type_rhs
	= False
	
tryToExpandTypeSyn defs cons_vars cons_id=:{type_index={glob_object,glob_module}} type_args type_heaps td_infos
	# {td_rhs,td_args} = defs.[glob_module].com_type_defs.[glob_object]
	| isSynonymType td_rhs
		# (SynType {at_type}) = td_rhs
		  type_heaps = fold2St bind_type_and_attr td_args type_args type_heaps
		  (expanded_type, (_, {es_type_heaps, es_td_infos}))
		  		= expandType defs cons_vars at_type ({}, { es_type_heaps = type_heaps, es_td_infos = td_infos })
		= (True, expanded_type, es_type_heaps, es_td_infos)
		= (False, TA cons_id type_args, type_heaps, td_infos)
where
	bind_type_and_attr {atv_attribute = TA_Var {av_info_ptr}, atv_variable={tv_info_ptr}} {at_attribute,at_type} {th_vars,th_attrs}
		= { th_vars = th_vars <:= (tv_info_ptr, TVI_Type at_type), th_attrs = th_attrs <:= (av_info_ptr, AVI_Attr at_attribute) }
	bind_type_and_attr {atv_variable={tv_info_ptr}} {at_type} type_heaps=:{th_vars}
		= { type_heaps & th_vars = th_vars <:= (tv_info_ptr, TVI_Type at_type) }
	
	
instance coerce Type
where
	coerce defs cons_vars (TA dem_cons dem_args) (TA off_cons off_args) sign cs=:{crc_type_heaps, crc_td_infos}
		| dem_cons == off_cons
			= coercionsOfTypeList defs cons_vars dem_args off_args dem_cons.type_prop.tsp_sign 0 sign cs
			# (_, dem_type, crc_type_heaps, crc_td_infos) = tryToExpandTypeSyn defs cons_vars dem_cons dem_args crc_type_heaps crc_td_infos
			  (_, off_type, crc_type_heaps, crc_td_infos) = tryToExpandTypeSyn defs cons_vars off_cons off_args crc_type_heaps crc_td_infos
			= coerce defs cons_vars dem_type off_type sign { cs & crc_type_heaps = crc_type_heaps, crc_td_infos = crc_td_infos }
	coerce defs cons_vars (TA dem_cons dem_args) off_type sign cs=:{crc_type_heaps, crc_td_infos}
		# (succ, dem_type, crc_type_heaps, crc_td_infos) = tryToExpandTypeSyn defs cons_vars dem_cons dem_args crc_type_heaps crc_td_infos
		| succ
			= coerce defs cons_vars dem_type off_type sign { cs & crc_type_heaps = crc_type_heaps, crc_td_infos = crc_td_infos }
			= (True, { cs & crc_type_heaps = crc_type_heaps, crc_td_infos = crc_td_infos })
	coerce defs cons_vars dem_type (TA off_cons off_args) sign cs=:{crc_type_heaps, crc_td_infos}
		# (succ, off_type, crc_type_heaps, crc_td_infos) = tryToExpandTypeSyn defs cons_vars off_cons off_args crc_type_heaps crc_td_infos
		| succ
			= coerce defs cons_vars dem_type off_type sign { cs & crc_type_heaps = crc_type_heaps, crc_td_infos = crc_td_infos }
			= (True, { cs & crc_type_heaps = crc_type_heaps, crc_td_infos = crc_td_infos })
	coerce defs cons_vars (arg_type1 --> res_type1) (arg_type2 --> res_type2) sign cs
		# (ok, cs) = coerce defs cons_vars arg_type1 arg_type2 (NegativeSign * sign) cs
		| ok
			= coerce defs cons_vars res_type1 res_type2 sign cs
			= (False, cs)
	coerce defs cons_vars (cons_var :@: types1) (_ :@: types2) sign cs
		= coercions_of_type_list defs cons_vars (determine_sign_of_arg_types cons_var cons_vars) types1 types2 cs
	where
		determine_sign_of_arg_types (TempCV tmp_var_id) cons_vars
			| isPositive tmp_var_id cons_vars
				= PositiveSign
				= TopSign
		determine_sign_of_arg_types _ cons_vars
				= TopSign
			
		coercions_of_type_list :: !{# CommonDefs} !{# BOOLVECT} !Sign ![a] ![a] !*CoercionState -> (!Bool,!*CoercionState) | coerce a
		coercions_of_type_list defs cons_vars sign [t1 : ts1] [t2 : ts2] cs
			# (ok, cs) = coerce defs cons_vars t1 t2 sign cs
			| ok
				= coercions_of_type_list defs cons_vars sign ts1 ts2 cs
				= (False, cs)
		coercions_of_type_list defs cons_vars sign [] [] cs
			= (True, cs)
	coerce defs cons_vars _ _ sign cs
		= (True, cs)

AttrRestricted :== 0

instance <<< CoercionTree
where
	(<<<) file (CT_Node attr left right) = file <<< left <<< ' ' <<< attr <<< ' ' <<< right
	(<<<) file CT_Unique = file <<< "CT_Unique"
	(<<<) file CT_NonUnique = file <<< "CT_NonUnique"
//	(<<<) file (CT_Existential int) = file <<< "CT_Existential:" <<< int
	(<<<) file CT_Empty = file <<< "##"

instance <<< CoercionPosition
where
	(<<<) file {cp_expression} = show_expression file cp_expression

	where
		show_expression file (Var {var_name})
			= file <<< var_name
		show_expression file (FreeVar {fv_name})
			= file <<< fv_name
		show_expression file (App {app_symb={symb_name}})
			= file <<< symb_name
		show_expression file (fun @ fun_args)
			= show_expression file fun
		show_expression file (Case {case_ident})
			= case case_ident of
				Yes {id_name}
					# (line, pos) = get_line_and_col "_c" id_name
					-> file <<< "case [" <<< line <<< ',' <<< pos <<< ']'
				No
					-> file <<< "(case ... )"
		show_expression file (Selection _ expr selectors)
			= file <<< "selection"
		show_expression file (Update expr1 selectors expr2)
			= file <<< "update"
		show_expression file (TupleSelect {ds_arity} elem_nr expr)
			= file <<< "argument" <<< (elem_nr + 1) <<< " of " <<< ds_arity <<< "-tuple"
		show_expression file (BasicExpr bv _)
			= file <<< bv
		show_expression file (MatchExpr _ _ expr)
			= file <<< "match expression"
		show_expression file _
			= file

		
		get_line_and_col prefix ident
			# ident = ident % (0, size prefix - 1)
			  del_pos = find_delimiter '_' 0 ident
			= (toInt (ident % (0, del_pos - 1)), toInt (ident % (del_pos + 1, size ident - 1)))
		where
			find_delimiter del_char del_pos ident
				| del_char == ident.[del_pos]
					= del_pos
					= find_delimiter del_char (inc del_pos) ident
			
