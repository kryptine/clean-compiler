implementation module generics

import StdEnv
import _aconcat
import hashtable
import checksupport
import checktypes
import check
import analtypes
/*2.0
from transform import ::Group
0.2*/
//1.3
from transform import Group
//3.1

// whether to generate CONS 
// (needed for function that use CONS, like toString) 
supportCons :== False

// whether to bind _cons_info to actual constructor info
// (needed for functions that create CONS, like fromString)			
supportConsInfo :== True && supportCons

// whether generate missing alternatives 		
supportPartialInstances :== False

:: *GenericState = 
	{	gs_modules				:: !*{#CommonDefs}
	,	gs_fun_defs				:: !*{# FunDef}
	,	gs_groups				:: !{!Group}
	,	gs_td_infos 			:: !*TypeDefInfos
	,	gs_gtd_infos			:: !*GenericTypeDefInfos
	,	gs_heaps				:: !*Heaps
	,	gs_main_dcl_module_n	:: !Index
	,	gs_first_fun			:: !Index
	,	gs_last_fun				:: !Index
	,	gs_first_group			:: !Index
	,	gs_last_group			:: !Index
	,	gs_predefs				:: !PredefinedSymbols
	,	gs_dcl_modules			:: !*{#DclModule}
	,	gs_opt_dcl_icl_conversions :: !*(Optional !*{#Index})
	,	gs_error 				:: !*ErrorAdmin	
	}

:: GenericTypeDefInfo  
	= GTDI_Empty 							// no generic rep needed
	| GTDI_Generic GenericTypeRep			// generic representataion

:: GenericTypeDefInfos :== {# .{GenericTypeDefInfo}}

:: GenericTypeRep = 
	{	gtr_type 				:: !AType			// generic type representation
	,	gtr_type_args			:: ![TypeVar]		// same as in td_info
	,	gtr_iso					:: !DefinedSymbol	// isomorphim function index 		
	,	gtr_isomap_group		:: !Index 			// isomap function group
	,	gtr_isomap				:: !DefinedSymbol	// isomap function for the type
 	,	gtr_isomap_from			:: !DefinedSymbol	// from-part of isomap
	,	gtr_isomap_to			:: !DefinedSymbol 	// to-part	
	,	gtr_type_info			:: !DefinedSymbol	// type def info
	,	gtr_cons_infos			:: ![DefinedSymbol] // constructor informations
	}

EmptyDefinedSymbol :== MakeDefinedSymbol {id_name="",id_info=nilPtr} NoIndex 0	
EmptyGenericType :== 
	{	gtr_type 		= makeAType TE TA_None
	,	gtr_type_args	= [] 
	,	gtr_iso 		= EmptyDefinedSymbol 
	,	gtr_isomap_group = NoIndex 
	,	gtr_isomap 		= EmptyDefinedSymbol
	,	gtr_isomap_from = EmptyDefinedSymbol
	,	gtr_isomap_to 	= EmptyDefinedSymbol
	,	gtr_type_info 	= EmptyDefinedSymbol
	,	gtr_cons_infos 	= []
	}

:: IsoDirection = IsoTo | IsoFrom

instance toBool GenericTypeDefInfo where
	toBool GTDI_Empty 		= False
	toBool (GTDI_Generic _) = True

convertGenerics :: !{!Group} !Int !{#CommonDefs} !*{# FunDef} !*TypeDefInfos !*Heaps !*HashTable !*PredefinedSymbols !u:{# DclModule} /*!(Optional {#Index})*/ !*ErrorAdmin 
	-> (!{!Group}, !{#CommonDefs}, !*{# FunDef}, !IndexRange, !*TypeDefInfos, !*Heaps, !*HashTable, !*PredefinedSymbols, !u:{# DclModule}, /*!(Optional {#Index}),*/ !*ErrorAdmin)
convertGenerics 
		groups main_dcl_module_n modules fun_defs td_infos heaps
		hash_table predefs dcl_modules 
		//opt_dcl_icl_conversions 
		error

	#! (fun_defs_size, fun_defs) = usize fun_defs 
	#! groups_size = size groups	

	#! (predef_size, predefs) = usize predefs
	#! (gs_predefs, predefs) = arrayCopyBegin predefs predef_size
	
	// determine sized of type def_infos:
	// ??? How to map 2-d unique array not so ugly ??? 
	#! (td_infos_sizes, td_infos) = get_sizes 0 td_infos
		with 
			get_sizes :: Int !*TypeDefInfos -> ([Int], !*TypeDefInfos)
			get_sizes n td_infos
				#! td_infos_size = size td_infos
				| n == td_infos_size = ([], td_infos)
				#! row_size = size td_infos.[n]
				# (row_sizes, td_infos) = get_sizes (n + 1) td_infos
				= ([row_size : row_sizes], td_infos)
	#! gtd_infos = { createArray s GTDI_Empty \\ s <- td_infos_sizes } 
								
	#! gs = 
		{	gs_modules = {m \\m <-: modules} // unique copy
		,	gs_groups = groups
		, 	gs_fun_defs = fun_defs 
		,	gs_td_infos = td_infos
		,	gs_gtd_infos = gtd_infos 
		,	gs_heaps = heaps
		,	gs_main_dcl_module_n = main_dcl_module_n
		,	gs_first_fun = fun_defs_size
		, 	gs_last_fun = fun_defs_size
		,	gs_first_group = groups_size
		, 	gs_last_group = groups_size
		,	gs_predefs = gs_predefs
		,	gs_dcl_modules = { x \\ x <-: dcl_modules } // unique copy
		,	gs_opt_dcl_icl_conversions = No
/*		
				case opt_dcl_icl_conversions of
				No -> No
				Yes xs -> Yes {x \\ x <-: xs} 	// unique copy
*/
		,	gs_error = error
		} 
	
	
	#! gs = collectInstanceKinds gs
		//---> "*** collect kinds used in generic instances and store them in the generics"
	#! (ok,gs) = gs!gs_error.ea_ok
	| not ok 
		= return gs predefs hash_table 
			
	#! gs = buildClasses gs
		//---> "*** build generic classes for all used kinds"
	#! (ok,gs) = gs!gs_error.ea_ok
	| not ok 
		= return gs predefs hash_table 

	#! (generic_types, gs) = collectGenericTypes gs
		//---> "*** collect types of generics (needed for generic representation)"
	#! (ok,gs) = gs!gs_error.ea_ok
	| not ok 
		= return gs predefs hash_table 

	#! (instance_types, gs) = convertInstances gs
		//---> "*** bind generic instances to classes and collect instance types"
	#! (ok,gs) = gs!gs_error.ea_ok
	| not ok 
		= return gs predefs hash_table 
	
	#! gs = checkConsInstances gs
		//---> "*** check that cons instances are provided for all generics"
	#! (ok,gs) = gs!gs_error.ea_ok
	| not ok 
		= return gs predefs hash_table 

	#! (cons_funs, cons_groups, gs) = buildConsInstances gs
	| not ok 
		//---> "*** bind function for CONS"
		= return gs predefs hash_table 
			
	#! (td_indexes, gs) = collectGenericTypeDefs generic_types instance_types gs	
		//---> "*** collect type definitions for which a generic representation must be created"
	#! (ok,gs) = gs!gs_error.ea_ok
	| not ok 
		= return gs predefs hash_table 

	#! (iso_funs, iso_groups, gs) = buildIsoFunctions td_indexes gs	
		//---> "*** build isomorphisms for type definitions"	
	#! (ok,gs) = gs!gs_error.ea_ok
	| not ok 
		= return gs predefs hash_table 

	#! (isomap_type_funs, isomap_type_groups, gs) = buildIsomapsForTypeDefs td_indexes gs	
		//---> "*** build maps for type definitions"	
	#! (ok,gs) = gs!gs_error.ea_ok
	| not ok 
		= return gs predefs hash_table 

	#! (isomap_gen_funs, isomap_gen_groups, gs) = buildIsomapsForGenerics gs 		
		//---> "*** build maps for generic function types"	
	#! (ok,gs) = gs!gs_error.ea_ok
	| not ok 
		= return gs predefs hash_table 

	#! (instance_funs, instance_groups, gs) = buildInstances gs
		//---> "*** build instances"	
	#! (ok,gs) = gs!gs_error.ea_ok
	| not ok 
		= return gs predefs hash_table 

	#! (star_funs, star_groups, gs) = buildKindConstInstances gs
		//---> "*** build shortcut instances for kind *"	
	#! (ok,gs) = gs!gs_error.ea_ok
	| not ok 
		= return gs predefs hash_table 
	
	// the order in the lists below is important! 
	// Indexes are allocated in that order.
	#! new_funs = cons_funs ++ iso_funs ++ isomap_type_funs ++ isomap_gen_funs ++ instance_funs ++ star_funs
	#! new_groups = cons_groups ++ iso_groups ++ isomap_type_groups ++ isomap_gen_groups ++ instance_groups ++ star_groups	

	#! gs = addFunsAndGroups new_funs new_groups gs	
		//---> "*** add geenrated functions"
	#! (ok,gs) = gs!gs_error.ea_ok
	| not ok 
		= return gs predefs hash_table 

	#! gs = determineMemberTypes 0 0 gs
		//---> "*** determine types of member instances"	
	#! (ok,gs) = gs!gs_error.ea_ok
	| not ok 
		= return gs predefs hash_table 
	
	//| True	= abort "-----------------\n"
				
	# {	gs_modules, gs_groups, gs_fun_defs, gs_td_infos, gs_heaps, gs_dcl_modules, 
		gs_opt_dcl_icl_conversions, 
		gs_error} 
			= gs	
	
	#! {hte_symbol_heap} = hash_table
	#! cs = 
		{	cs_symbol_table = hte_symbol_heap 
		,	cs_predef_symbols = predefs 
		,	cs_error = gs_error 
		,	cs_x = 
			{	x_needed_modules = 0
			,	x_main_dcl_module_n = main_dcl_module_n 
//			,	x_is_dcl_module = False
//			,	x_type_var_position = 0
			}
		}

	#! (gs_dcl_modules, gs_modules, gs_heaps, cs_symbol_table) = 
		create_class_dictionaries 0 gs_dcl_modules gs_modules gs_heaps cs.cs_symbol_table
//		create_class_dictionaries1 main_dcl_module_n dcl_modules gs_modules gs_heaps cs
			//---> "*** create class dictionaries"	

	# hash_table = { hash_table & hte_symbol_heap = cs_symbol_table }	
	
	#! index_range = {ir_from = gs.gs_first_fun, ir_to = gs.gs_last_fun}
		 			
	= (	gs_groups, gs_modules, gs_fun_defs, index_range, gs_td_infos, gs_heaps, hash_table, 
		cs.cs_predef_symbols, gs_dcl_modules, /*gs_opt_dcl_icl_conversions,*/ cs.cs_error)
where
	return {	gs_modules, gs_groups, gs_fun_defs, gs_td_infos, gs_gtd_infos, 
				gs_heaps, gs_main_dcl_module_n, gs_dcl_modules, gs_opt_dcl_icl_conversions, gs_error} 
				predefs hash_table  
		= (	gs_groups, gs_modules, gs_fun_defs, {ir_from=0,ir_to=0}, 
			gs_td_infos, gs_heaps, hash_table, predefs, gs_dcl_modules, 
			/*gs_opt_dcl_icl_conversions,*/ gs_error)

	create_class_dictionaries module_index dcl_modules  modules heaps symbol_table 
		#! size_of_modules = size modules
		| module_index == size_of_modules
			= (dcl_modules, modules, heaps, symbol_table)
			#! (dcl_modules, modules, heaps, symbol_table) = 
				create_class_dictionaries1 module_index dcl_modules  modules heaps symbol_table
			= create_class_dictionaries (inc module_index) dcl_modules modules heaps symbol_table		

	create_class_dictionaries1
			module_index dcl_modules modules 
			heaps=:{hp_type_heaps=hp_type_heaps=:{th_vars}, hp_var_heap}
			symbol_table 
		#! (common_defs, modules) = modules![module_index]
		#! class_defs = { x \\ x <-: common_defs.com_class_defs } // make unique copy
		#  type_defs = { x \\ x <-: common_defs.com_type_defs } // make unique copy
		#  cons_defs = { x \\ x <-: common_defs.com_cons_defs } // make unique copy
		#  selector_defs = { x \\ x <-: common_defs.com_selector_defs } // make unique copy
		#  (size_type_defs,type_defs) = usize type_defs 
		#! (new_type_defs, new_selector_defs, new_cons_defs,_,type_defs,selector_defs,cons_defs,class_defs, dcl_modules, th_vars, hp_var_heap, symbol_table) =
				createClassDictionaries
					False //(abort "create_class_dictionaries1 True or False ?")
					module_index 
					size_type_defs
					(size common_defs.com_selector_defs) 
					(size common_defs.com_cons_defs) 
					type_defs selector_defs cons_defs class_defs dcl_modules th_vars hp_var_heap symbol_table

		#! common_defs = { common_defs & 
			com_class_defs = class_defs, 
			com_type_defs = arrayPlusList type_defs new_type_defs,
			com_selector_defs = arrayPlusList selector_defs new_selector_defs,
			com_cons_defs = arrayPlusList cons_defs new_cons_defs}

		#! heaps = {heaps & hp_var_heap = hp_var_heap, hp_type_heaps = {hp_type_heaps & th_vars = th_vars}} 
		#! modules = { modules & [module_index] = common_defs } 		
		= (dcl_modules, modules, heaps, symbol_table)		
	
convertInstances :: !*GenericState	
	-> (![Global Index], !*GenericState)
convertInstances gs
	= convert_modules 0 gs 
where

	convert_modules module_index gs=:{gs_modules}
		#! num_modules = size gs_modules
		| module_index == num_modules
			= ([], gs)	
		#! (common_defs, gs_modules) = gs_modules ! [module_index] 
		#! instance_defs = {i \\ i <-: common_defs.com_instance_defs} // make unique copy		

		#! (new_types, instance_defs, gs) =
			convert_instances module_index 0 instance_defs {gs & gs_modules = gs_modules}
		#! (types, gs) = convert_modules (inc module_index) gs
		
		#! {gs_modules} = gs
		#! (common_defs, gs_modules) = gs_modules ! [module_index]
		#! gs_modules = { gs_modules & [module_index] = {common_defs & com_instance_defs = instance_defs}} 
		= (new_types ++ types, {gs & gs_modules = gs_modules})

	convert_instances module_index instance_index instance_defs gs
		#! num_instance_defs = size instance_defs
		| instance_index == num_instance_defs
			= ([], instance_defs, gs)													
		#! (new_types, instance_defs, gs) = convert_instance module_index instance_index instance_defs gs 			
		#! (types, instance_defs, gs) = convert_instances module_index (inc instance_index) instance_defs gs		
		= (new_types ++ types, instance_defs, gs)	
		
	convert_instance :: !Index !Index !*{#ClassInstance} !*GenericState
		-> (![Global Index], !*{#ClassInstance}, !*GenericState)	
	convert_instance 
			module_index instance_index instance_defs 
			gs=:{gs_td_infos, gs_modules, gs_error, gs_fun_defs, gs_predefs, gs_heaps}
//		= abort "generics; convert_instance"

		#! (instance_def=:{ins_class,ins_ident}, instance_defs) = instance_defs ! [instance_index]
		| not instance_def.ins_is_generic
			# gs = { gs 
				& 	gs_td_infos = gs_td_infos
				, 	gs_modules = gs_modules
				,	gs_fun_defs = gs_fun_defs
				, 	gs_heaps = gs_heaps
				, 	gs_error = gs_error }	
			= ([], instance_defs, gs)
		
		// determine the kind of the instance type
		#! it_type = hd instance_def.ins_type.it_types
		#! (kind, gs_td_infos) = kindOfType it_type gs_td_infos

		#! (generic_def, gs_modules) = getGenericDef ins_class.glob_module ins_class.glob_object.ds_index gs_modules
		#! (ok, class_ds) = getGenericClassForKind generic_def kind
		| not ok
			= abort ("no class " +++ ins_ident.id_name +++ "for kind" +++ toString kind) 

		// bind the instance to the class
		#! instance_def = 
			{ 	instance_def 
			& 	ins_class = {glob_module=ins_class.glob_module, glob_object=class_ds} 
			,	ins_ident = makeIdent ins_ident.id_name
			}
		#! (is_partial, gs_fun_defs) = check_if_partial instance_def gs_predefs gs_fun_defs
		 	
		# (ok, gs_modules, gs_error) = check_instance_args instance_def gs_modules gs_error
		| not ok
			#! instance_defs = { instance_defs & [instance_index] = instance_def}
			#! gs = { gs 
				& 	gs_td_infos = gs_td_infos
				, 	gs_modules = gs_modules
				,	gs_fun_defs = gs_fun_defs
				, 	gs_heaps = gs_heaps
				, 	gs_error = gs_error 
				}	
			= ([], instance_defs, gs)

		# gs_heaps = check_cons_instance generic_def instance_def it_type gs_predefs gs_heaps 
	
		# (maybe_td_index, instance_def, gs_modules, gs_error) = 
			determine_type_def_index it_type instance_def is_partial gs_modules gs_error
		# gs = { gs 
			& 	gs_td_infos = gs_td_infos
			, 	gs_modules = gs_modules
			,	gs_fun_defs = gs_fun_defs
			, 	gs_heaps = gs_heaps
			, 	gs_error = gs_error }	
		#! instance_defs = { instance_defs & [instance_index] = instance_def}
		= (maybe_td_index, instance_defs, gs)

	determine_type_def_index 
			(TA {type_index, type_name} _) 
			instance_def=:{ins_generate, ins_ident, ins_pos}
			is_partial 
			gs_modules gs_error
		#! ({td_rhs, td_index}, gs_modules) = getTypeDef type_index.glob_module type_index.glob_object gs_modules
		= determine_td_index td_rhs gs_modules gs_error
	where
		determine_td_index (AlgType _) gs_modules gs_error
			| ins_generate 
				= ([type_index], instance_def, gs_modules, gs_error)
			| supportPartialInstances && is_partial
				= ([type_index], {instance_def & ins_partial = True}, gs_modules, gs_error)
					//---> ("collected partial instance type", type_name, type_index)			
			| otherwise
				= ([], instance_def, gs_modules, gs_error)
		determine_td_index (RecordType _) gs_modules gs_error
			| ins_generate 
				= ([type_index], instance_def, gs_modules, gs_error)
			| supportPartialInstances && is_partial
				= ([type_index], {instance_def & ins_partial = True}, gs_modules, gs_error)			
					//---> ("collected partial instance type", type_name, type_index)			
			| otherwise
				= ([], instance_def, gs_modules, gs_error)
		determine_td_index (SynType _) gs_modules gs_error
			# gs_error = checkErrorWithIdentPos 
				(newPosition ins_ident ins_pos) 
				"generic instance type cannot be a synonym type" 
				gs_error 				 
			= ([], instance_def, gs_modules, gs_error)			
		determine_td_index (AbstractType _) gs_modules gs_error
			| ins_generate
				# gs_error = checkErrorWithIdentPos 
					(newPosition ins_ident ins_pos) 
					"cannot generate an instance for an abstract data type" 
					gs_error 				 
				= ([], instance_def, gs_modules, gs_error)									
				= ([], instance_def, gs_modules, gs_error)				
	determine_type_def_index TArrow instance_def=:{ins_generate,ins_ident,ins_pos} _ gs_modules gs_error
		| ins_generate
			# gs_error = checkErrorWithIdentPos 
					(newPosition ins_ident ins_pos) 
					"cannot generate an instance for arrow type" 
					gs_error 	
			= ([], instance_def, gs_modules, gs_error)
			= ([], instance_def, gs_modules, gs_error)
	determine_type_def_index (TArrow1 _) instance_def=:{ins_generate,ins_ident,ins_pos} _ gs_modules gs_error
		| ins_generate
			# gs_error = checkErrorWithIdentPos 
					(newPosition ins_ident ins_pos) 
					"cannot generate an instance for arrow type" 
					gs_error 	
			= ([], instance_def, gs_modules, gs_error)			
			= ([], instance_def, gs_modules, gs_error)		
	determine_type_def_index (TB _) instance_def=:{ins_generate,ins_ident,ins_pos} _ gs_modules gs_error
		| ins_generate
			# gs_error = checkErrorWithIdentPos 
					(newPosition ins_ident ins_pos) 
					"cannot generate an instance for a basic type" 
					gs_error 	
			= ([], instance_def, gs_modules, gs_error)			
			= ([], instance_def, gs_modules, gs_error)			
	determine_type_def_index _ instance_def=:{ins_ident,ins_pos} _ gs_modules gs_error
		#! gs_error = checkErrorWithIdentPos 
			(newPosition ins_ident ins_pos) 
			"generic instance type must be a type constructor or a primitive type" 
			gs_error 				 
		= ([], instance_def, gs_modules, gs_error)
	
	check_if_partial :: !ClassInstance !PredefinedSymbols !*{#FunDef} -> (!Bool, !*{#FunDef})
	check_if_partial instance_def=:{ins_members, ins_ident, ins_type, ins_generate} gs_predefs gs_fun_defs		
		= 	case supportPartialInstances of
			True
				| ins_generate
					-> (False, gs_fun_defs)
				| check_if_predef (hd ins_type.it_types) gs_predefs
					-> (False, gs_fun_defs) // PAIR, EITHER, CONS, UNIT
				#! ins_fun_ds = ins_members.[0]
				| ins_fun_ds.ds_index == NoIndex // can this happen?
					-> (False, gs_fun_defs)
				| otherwise					
					#! (fun_def, gs_fun_defs) = gs_fun_defs ! [ins_fun_ds.ds_index]
					#  (TransformedBody {tb_rhs}) = fun_def.fun_body  
					-> case tb_rhs of
						Case {case_default=No} 	-> (True, gs_fun_defs)
						_ 						-> (False, gs_fun_defs)
			False -> (False, gs_fun_defs)
		where
			check_if_predef (TA {type_index={glob_module, glob_object}} _) gs_predefs
			 	# {pds_module, pds_def} = gs_predefs.[PD_TypeUNIT]
			 	| glob_module == pds_module && glob_object == pds_def
			 		= True
			 	# {pds_module, pds_def} = gs_predefs.[PD_TypePAIR]
			 	| glob_module == pds_module && glob_object == pds_def
			 		= True
			 	# {pds_module, pds_def} = gs_predefs.[PD_TypeEITHER]
			 	| glob_module == pds_module && glob_object == pds_def
			 		= True
			 	# {pds_module, pds_def} = gs_predefs.[PD_TypeCONS]
			 	| glob_module == pds_module && glob_object == pds_def
			 		= True
				| otherwise
					= False				
			check_if_predef _ gs_predefs 
				= False						
								
	check_cons_instance 
			{gen_cons_ptr} {ins_members}
			(TA {type_index={glob_module, glob_object}} _) 
			predefs heaps
		| not supportConsInfo 
			= heaps	
		# {pds_module, pds_def} = predefs.[PD_TypeCONS]
		| glob_module <> pds_module || glob_object <> pds_def
			= heaps
		# {hp_type_heaps=hp_type_heaps=:{th_vars}}=heaps				
		# th_vars = writePtr gen_cons_ptr (TVI_ConsInstance ins_members.[0]) th_vars		
		= {heaps & hp_type_heaps = {hp_type_heaps & th_vars = th_vars}}	
	check_cons_instance _ _ _ _ heaps 
		= heaps	
				
	check_instance_args 
			instance_def=:{ins_class={glob_module,glob_object}, ins_ident, ins_pos, ins_type, ins_generate} 
			gs_modules gs_error
		| ins_generate 
			= (True, gs_modules, gs_error)
	
		# (class_def=:{class_members}, gs_modules) =  
			getClassDef glob_module glob_object.ds_index gs_modules
		# (member_def, gs_modules) = 
			getMemberDef glob_module class_def.class_members.[0].ds_index gs_modules
		| member_def.me_type.st_arity <> instance_def.ins_members.[0].ds_arity && instance_def.ins_members.[0].ds_arity <> (-1)	
			# gs_error = checkErrorWithIdentPos (newPosition ins_ident ins_pos) "generic instance function has incorrect arity" gs_error
			= (False, gs_modules, gs_error)	
			= (True, gs_modules, gs_error)	

// check that CONS instances are provided for all generics
checkConsInstances :: !*GenericState -> !*GenericState
checkConsInstances gs
	| supportConsInfo
		= check_cons_instances 0 0 gs
		= gs

where
	check_cons_instances module_index generic_index gs=:{gs_modules, gs_heaps, gs_error}
		#! size_gs_modules = size gs_modules
		| module_index == size_gs_modules 
			= {gs & gs_modules = gs_modules} 
		# (generic_defs, gs_modules) = gs_modules ! [module_index].com_generic_defs 
		#! size_generic_defs = size generic_defs
		| generic_index == size_generic_defs
			= check_cons_instances (inc module_index) 0 {gs & gs_modules = gs_modules}
		
		# (gs_heaps, gs_error) = check_generic generic_defs.[generic_index] gs_heaps gs_error
		= check_cons_instances 
			module_index (inc generic_index)
			{gs & gs_modules = gs_modules, gs_heaps = gs_heaps, gs_error = gs_error}
				
	check_generic 
			{gen_cons_ptr, gen_name, gen_pos} 
			gs_heaps=:{hp_type_heaps=hp_type_heaps=:{th_vars}}
			gs_error			
		# (info, th_vars) = readPtr gen_cons_ptr th_vars	
		# gs_error = case info of
			TVI_ConsInstance _ 	
				->  gs_error
			_					
				-> reportError gen_name gen_pos "instance on CONS must be provided" gs_error
		= ({gs_heaps & hp_type_heaps = {hp_type_heaps & th_vars = th_vars}}, gs_error)


collectGenericTypes :: !*GenericState -> (![Type], !*GenericState)
collectGenericTypes gs=:{gs_modules} 
	# (types, gs_modules) = collect_in_modules 0 0 gs_modules
	= (types, {gs & gs_modules = gs_modules})
where
	collect_in_modules module_index generic_index gs_modules
		#! size_gs_modules = size gs_modules 
		| module_index == size_gs_modules
			= ([], gs_modules) 
		# (generic_defs, gs_modules) = gs_modules ! [module_index].com_generic_defs 
		#! size_generic_defs = size generic_defs
		| generic_index == size_generic_defs
			= collect_in_modules (inc module_index) 0 gs_modules	
		# {gen_type={gt_type={st_args, st_result}}} = generic_defs . [generic_index]
		# (types, gs_modules) = collect_in_modules module_index (inc generic_index) gs_modules
		= ([at_type \\ {at_type} <- [st_result:st_args]] ++ types, gs_modules)	


buildConsInstances :: !*GenericState -> (![FunDef], ![Group], !*GenericState)
buildConsInstances gs 
	| supportConsInfo
		= build_cons_instances 0 0 gs
		= ([], [], gs)
where
	build_cons_instances module_index generic_index gs=:{gs_modules}
		#! size_gs_modules = size gs_modules 
		| module_index == size_gs_modules
			= ([], [], {gs & gs_modules = gs_modules}) 
		# (generic_defs, gs_modules) = gs_modules ! [module_index].com_generic_defs
		# gs = {gs & gs_modules = gs_modules} 
		#! size_generic_defs = size generic_defs
		| generic_index == size_generic_defs
			= build_cons_instances (inc module_index) 0 gs
		# (fun, group, gs) = build_cons_instance generic_defs.[generic_index] gs				
		# (funs, groups, gs) = build_cons_instances module_index (inc generic_index) gs
		= ([fun:funs], [group:groups], gs)	

	build_cons_instance generic_def gs
		#! (fun_index, group_index, gs) 	= newFunAndGroupIndex gs		
		#! (ins_fun_def_sym, gs) = get_cons_fun generic_def gs		
		#! {gs_fun_defs, gs_predefs, gs_heaps} = gs
		#! fun_def_sym = 
			{	ds_ident = makeIdent (ins_fun_def_sym.ds_ident.id_name +++ ":cons_info")
			,	ds_arity = ins_fun_def_sym.ds_arity + 1
			,	ds_index = fun_index
			}		
		#! gs_heaps = set_cons_fun generic_def fun_def_sym gs_heaps	

		#! (ins_fun_def, gs_fun_defs) = gs_fun_defs ! [ins_fun_def_sym.ds_index]		

		#! (fun_def, gs_heaps) = copyFunDef ins_fun_def fun_index group_index gs_heaps

		#! (fun_def, gs_heaps) = parametrize_with_cons_info fun_def gs_predefs gs_heaps
		
		#! group = {group_members = [fun_index]}
			
		= (fun_def, group, {gs & gs_fun_defs = gs_fun_defs, gs_heaps = gs_heaps})
			//---> ("build_cons_instance", ins_fun_def, fun_def)
	where 
		parametrize_with_cons_info fun_def=:{fun_arity, fun_body} predefs heaps		
			# (var_expr, var, heaps) = buildVarExpr "cons_info" heaps
			# (TransformedBody tb=:{tb_args, tb_rhs}) = fun_body
			# (tb_rhs, heaps) = mapExprSt (replace_cons_info var_expr) tb_rhs  heaps 	
			# fun_def = 
				{ fun_def 
				& fun_arity = fun_arity + 1
				, fun_body = TransformedBody {tb & tb_args = [var:tb_args], tb_rhs = tb_rhs}
				}				
			= (fun_def, heaps) 
		where
			{pds_module,pds_def} = predefs.[PD_cons_info]	
			replace_cons_info 
					var_expr 
					expr=:(App {app_symb={symb_kind=SK_Function {glob_object, glob_module}}}) 
					heaps
				| pds_module == glob_module && pds_def == glob_object			
					= (var_expr, heaps)
						//---> ("replace_cons_info", expr, var_expr)
					= (expr, heaps)
						//---> ("replace_cons_info: App expr1", expr)
							
			replace_cons_info var_expr expr=:(App app) heaps
				= (expr, heaps)
					//--->  ("replace_cons_info: App expr2", expr) 
						 
			replace_cons_info var_expr expr heaps
				= (expr, heaps)
	
	get_cons_fun 
			{gen_cons_ptr, gen_pos, gen_name} 
			gs=:{gs_heaps=gs_heaps=:{hp_type_heaps=hp_type_heaps=:{th_vars}}, gs_error}
		# (info, th_vars) = readPtr gen_cons_ptr th_vars
		# gs_heaps = { gs_heaps & hp_type_heaps = {hp_type_heaps & th_vars = th_vars }}	
		# (fun_def_sym, gs_error) = case info of		
			TVI_ConsInstance fun_def_sym
				-> (fun_def_sym, gs_error)				
			TVI_Empty
				-> (EmptyDefinedSymbol, reportError gen_name gen_pos "no CONS instance provided" gs_error)
		= (fun_def_sym, {gs & gs_heaps = gs_heaps, gs_error = gs_error})						

	set_cons_fun 
			{gen_cons_ptr} fun_def_sym
			gs_heaps=:{hp_type_heaps=hp_type_heaps=:{th_vars}}
		# th_vars = writePtr gen_cons_ptr (TVI_ConsInstance fun_def_sym) th_vars
		= { gs_heaps & hp_type_heaps = {hp_type_heaps & th_vars = th_vars }}	
							
collectInstanceKinds :: !*GenericState -> !*GenericState
collectInstanceKinds gs
	= collect_instance_kinds 0 0 gs
where
	collect_instance_kinds module_index instance_index gs=:{gs_modules}
		#! size_modules = size gs_modules
		| module_index == size_modules
			= gs
		#! (common_defs, gs_modules) = gs_modules ! [module_index]
		#! size_instance_defs = size common_defs.com_instance_defs
		| instance_index == size_instance_defs
			= collect_instance_kinds (inc module_index) 0 {gs & gs_modules = gs_modules} 
				
		#! gs = collect_instance module_index instance_index {gs & gs_modules = gs_modules}
		
		= collect_instance_kinds module_index (inc instance_index) gs

	collect_instance module_index instance_index gs=:{gs_heaps, gs_modules, gs_td_infos}
		
		#! (instance_def=:{ins_class, ins_is_generic, ins_type}, gs_modules) = 
			getInstanceDef module_index instance_index gs_modules
		| not instance_def.ins_is_generic 
			= {gs & gs_modules = gs_modules, gs_heaps = gs_heaps }

		#! (generic_def, gs_modules) = getGenericDef ins_class.glob_module ins_class.glob_object.ds_index gs_modules		
		#! (kind, gs_td_infos) = kindOfType (hd ins_type.it_types) gs_td_infos		
		#! gs_heaps = update_kind generic_def kind gs_heaps		
		= {gs & gs_modules = gs_modules, gs_heaps = gs_heaps, gs_td_infos = gs_td_infos}
		
	update_kind {gen_kinds_ptr} kind gs_heaps=:{hp_type_heaps=hp_type_heaps=:{th_vars}}
		#! (TVI_Kinds kinds, th_vars) = readPtr gen_kinds_ptr th_vars
		#! kinds = eqMerge [kind] kinds
		#! th_vars = writePtr gen_kinds_ptr (TVI_Kinds kinds) th_vars
		= {gs_heaps & hp_type_heaps = {hp_type_heaps & th_vars = th_vars}}

buildClasses :: !*GenericState -> !*GenericState
buildClasses gs 
	= build_modules 0 gs
where
	build_modules module_index gs=:{gs_modules}
		#! size_gs_modules = size gs_modules 
		| module_index == size_gs_modules
			= { gs & gs_modules = gs_modules }	 		

		#! common_defs = gs_modules . [module_index]
		#! (common_defs, gs=:{gs_modules}) = build_module module_index common_defs gs	
		#! gs = {gs & gs_modules = {gs_modules & [module_index] = common_defs}}					

		= build_modules (inc module_index) gs	
			
	build_module module_index common_defs gs		 

		#! {com_generic_defs,com_class_defs, com_member_defs} = common_defs 
		
		#! class_index = size com_class_defs
		#! member_index = size com_member_defs
		#! com_generic_defs = {x \\ x <-: com_generic_defs} // make unique copy
			
		# (new_class_defs, new_member_defs, com_generic_defs, _, _, gs) = 
			build_generics module_index 0 class_index member_index com_generic_defs gs	

		# common_defs = 
			{	common_defs 
			&	com_class_defs = arrayPlusRevList com_class_defs new_class_defs
			,	com_member_defs = arrayPlusRevList com_member_defs new_member_defs
			, 	com_generic_defs = com_generic_defs
			}
		= (common_defs, gs)
		
	build_generics module_index generic_index class_index member_index generic_defs gs
		#! size_generic_defs = size generic_defs
		| generic_index == size_generic_defs
			= ([], [], generic_defs, class_index, member_index, gs)
		#! (generic_def, generic_defs) = generic_defs ! [generic_index]	
		#! (new_class_defs, new_member_defs, generic_def, class_index, member_index, gs) = 
			build_generic module_index class_index member_index generic_def gs
		#! generic_defs = {generic_defs & [generic_index] = generic_def}
		#! (new_class_defs1, new_member_defs1, generic_defs, class_index, member_index, gs) = 
			build_generics module_index (inc generic_index) class_index member_index generic_defs gs
		= (new_class_defs ++ new_class_defs1, new_member_defs ++ new_member_defs1,
			generic_defs, class_index, member_index, gs)
		
	build_generic module_index class_index member_index generic_def gs		
		# (kinds, gs) = get_kinds generic_def gs
		= build_classes kinds generic_def module_index class_index member_index gs
	
	build_classes :: ![TypeKind] !GenericDef !Index !Index !Index !*GenericState
		-> (![ClassDef], ![MemberDef], !GenericDef, !Index, !Index, !*GenericState)
	build_classes [] generic_def module_index class_index member_index gs 
		= ([], [], generic_def, class_index, member_index, gs)
	build_classes [kind:kinds] generic_def module_index class_index member_index gs 	
		#! (class_def, member_def, generic_def, gs) = 
			buildClassDef module_index class_index member_index generic_def kind gs
		#! (class_defs, member_defs, generic_def, class_index, member_index, gs) = 
			build_classes kinds generic_def module_index (inc class_index) (inc member_index) gs
		= ([class_def:class_defs], [member_def:member_defs], generic_def, class_index, member_index, gs) 			 

	get_kinds {gen_kinds_ptr} gs=:{gs_heaps=gs_heaps=:{hp_type_heaps=hp_type_heaps=:{th_vars}}}
		#! (TVI_Kinds kinds, th_vars) = readPtr gen_kinds_ptr th_vars
		#! th_vars = writePtr gen_kinds_ptr TVI_Empty th_vars
		= (kinds, {gs & gs_heaps = {gs_heaps & hp_type_heaps = {hp_type_heaps & th_vars = th_vars}}})
		 				
// find all types whose generic representation is needed
collectGenericTypeDefs :: ![Type] [Global Index] !*GenericState
	-> (![Global Index], !*GenericState)
collectGenericTypeDefs generic_types instance_td_indexes gs
	# (td_indexes, gs) = collect_in_types generic_types gs
	# (td_indexes, gs) = add_instance_indexes td_indexes instance_td_indexes gs
	= (map fst td_indexes, gs)
where
	add_instance_indexes td_indexes [] gs 
		= (td_indexes, gs)
	add_instance_indexes 
			td_indexes 
			[type_index=:{glob_module, glob_object} : itdis] 
			gs=:{gs_gtd_infos, gs_td_infos}
		# (gtd_info, gs_gtd_infos) = gs_gtd_infos ! [glob_module, glob_object]
		# gs_gtd_infos = {gs_gtd_infos & [glob_module, glob_object] = GTDI_Generic EmptyGenericType}
		# (td_info, gs_td_infos) = gs_td_infos ! [glob_module, glob_object]
		# gs = {gs & gs_td_infos = gs_td_infos, gs_gtd_infos = gs_gtd_infos}
		| toBool gtd_info // already marked
			= add_instance_indexes td_indexes itdis gs
				//---> ("instance type already added", type_index)
			# gs_gtd_infos = {gs_gtd_infos & [glob_module, glob_object] = GTDI_Generic EmptyGenericType}
			= add_instance_indexes (merge_td_indexes [(type_index, td_info.tdi_group_nr)] td_indexes) itdis gs
				//---> ("add instance type index", type_index)

	collect_in_types :: ![Type] !*GenericState  
		-> (![(Global Index, Int)], !*GenericState)
	collect_in_types [] gs = ([], gs)
	collect_in_types [type:types] gs
		# (td_indexes1, gs) = collect_in_type type gs
		# (td_indexes2, gs) = collect_in_types types gs
		= (merge_td_indexes td_indexes1 td_indexes2, gs)
		
	collect_in_type :: !Type !*GenericState 
		-> (![(Global Index, Int)], !*GenericState)		
	collect_in_type (TA type_symb arg_types) gs
		# (td_indexes1, gs) = collect_in_atypes arg_types gs
		# (td_indexes2, gs) = collect_in_type_app type_symb gs 
		= (merge_td_indexes td_indexes1 td_indexes2, gs)
	where	
		collect_in_type_app {type_arity=0} gs 
			// types with no arguments do not need mapping to be built:
			// their mapping is identity
			= ([], gs)
		collect_in_type_app 
				{type_index=type_index=:{glob_module, glob_object}, type_name}    
				gs=:{gs_gtd_infos, gs_td_infos, gs_modules}
			# (gtd_info, gs_gtd_infos) = gs_gtd_infos ! [glob_module, glob_object]
			| toBool gtd_info // already marked
				= ([], {gs & gs_gtd_infos = gs_gtd_infos})
					//---> ("already marked type", type_name, type_index)
			| otherwise // not yet marked		
				# gs_gtd_infos = {gs_gtd_infos & [glob_module, glob_object] = GTDI_Generic EmptyGenericType}
				# (td_info, gs_td_infos) = gs_td_infos ! [glob_module, glob_object]
				# (type_def, gs_modules) = getTypeDef glob_module glob_object gs_modules				
				# gs = {gs & gs_td_infos = gs_td_infos, gs_gtd_infos = gs_gtd_infos, gs_modules = gs_modules}
				# (td_indexes1, gs) = collect_in_type_def_rhs glob_module type_def gs
				# td_indexes2 = [(type_index, td_info.tdi_group_nr)]		
				= (merge_td_indexes td_indexes1 td_indexes2, gs)
					//---> ("mark type", type_name, type_index)

	collect_in_type (arg_type --> res_type) gs
		#! (td_indexes1, gs) = collect_in_atype arg_type gs
		#! (td_indexes2, gs) = collect_in_atype res_type gs
		= (merge_td_indexes td_indexes1 td_indexes2, gs)
	collect_in_type (TArrow1 arg_type) gs
		= collect_in_atype arg_type gs	
	collect_in_type (cons_var :@: args) gs
		#! types = [ at_type \\ {at_type} <- args] 
		= collect_in_types types gs				
	collect_in_type _ gs
		= ([], gs)
	
	collect_in_atype :: !AType !*GenericState 
		-> (![(Global Index, Int)], !*GenericState)		
	collect_in_atype {at_type} gs = collect_in_type at_type gs	

	collect_in_atypes :: ![AType] !*GenericState 
		-> (![(Global Index, Int)], !*GenericState)		
	collect_in_atypes [] gs = ([], gs)
	collect_in_atypes [atype:atypes] gs
		# (td_indexes1, gs) = collect_in_atype atype gs
		# (td_indexes2, gs) = collect_in_atypes atypes gs
		# merged_td_indexes = merge_td_indexes td_indexes1 td_indexes2
		= (merged_td_indexes, gs)

	collect_in_type_def_rhs :: !Index !CheckedTypeDef !*GenericState 
		-> (![(Global Index, Int)], !*GenericState)		 
	collect_in_type_def_rhs mod {td_rhs=(AlgType cons_def_symbols)} gs
		= collect_in_conses mod cons_def_symbols gs
	collect_in_type_def_rhs mod {td_rhs=(RecordType {rt_constructor})}	gs
		= collect_in_conses mod [rt_constructor] gs				
	collect_in_type_def_rhs mod {td_rhs=(SynType {at_type})}	gs			
		= collect_in_type at_type gs 
	collect_in_type_def_rhs mod {td_rhs=(AbstractType _), td_name, td_pos} gs=:{gs_error}				
		#! gs_error = checkErrorWithIdentPos
				(newPosition td_name td_pos) 
				"cannot build generic type representation for an abstract type" 
				gs_error
		= ([], {gs & gs_error = gs_error})
		//= ([], {gs & gs_error = checkWarning td_name "abstract data type" gs_error})
					
	collect_in_conses :: !Index ![DefinedSymbol] !*GenericState 
		-> (![(Global Index, Int)], !*GenericState)
	collect_in_conses mod [] gs 
		= ([], gs)
	collect_in_conses mod [{ds_index, ds_ident} : cons_def_symbols] gs=:{gs_modules}
		#! ({cons_type={st_args}}, gs_modules) = getConsDef mod ds_index gs_modules
			//---> ("mark cons " +++ ds_ident.id_name)
		#! types = [ at_type \\ {at_type} <- st_args] 
		#! (td_indexes1, gs) = collect_in_types types {gs & gs_modules=gs_modules}
		#! (td_indexes2, gs) = collect_in_conses mod cons_def_symbols gs
		= (merge_td_indexes td_indexes1 td_indexes2, gs)

	collect_in_symbol_type {st_args, st_result} gs
		#! (td_indexes1, gs) = collect_in_types (map (\x->x.at_type) st_args)  gs
		#! (td_indexes2, gs) = collect_in_type st_result.at_type gs
		= (merge_td_indexes td_indexes1 td_indexes2, gs)
		 
	merge_td_indexes x y 
		= mergeBy (\(_,l) (_,r) ->l < r) x y 


buildIsoFunctions :: ![Global Index] !*GenericState
	-> (![FunDef], ![Group], !*GenericState)
buildIsoFunctions [] gs = ([], [], gs)
buildIsoFunctions [type_index:type_indexes] gs
	#! (iso_funs1, iso_groups1, gs) = build_function type_index gs
	#! (iso_funs2, iso_groups2, gs) = buildIsoFunctions type_indexes gs	 
	= (iso_funs1 ++ iso_funs2, iso_groups1 ++ iso_groups2, gs) 
where
	build_function {glob_module, glob_object} gs
	
		# (generic_rep_type, gs) = buildGenericRepType glob_module glob_object gs
	
		# (type_info_def_sym, cons_info_def_syms, info_fun_defs, info_groups, gs) = 
			build_cons_infos glob_module glob_object gs

		# (iso_def_sym, iso_fun_defs, iso_groups, gs) =
			build_isos glob_module glob_object cons_info_def_syms gs  

		# gs = fill_generic_type_info
			glob_module glob_object 
			generic_rep_type
			iso_def_sym
			type_info_def_sym cons_info_def_syms
			gs	
		
		= (info_fun_defs ++ iso_fun_defs, info_groups ++ iso_groups, gs)	

	fill_generic_type_info 
			module_index type_def_index
			generic_rep_type 
			iso_def_sym 
			type_info_def_sym
			cons_info_def_syms
			gs=:{gs_gtd_infos, gs_modules}

		# (type_def=:{td_args}, gs_modules) = getTypeDef module_index type_def_index gs_modules 
		# gtd_info = GTDI_Generic 
			{ 	gtr_type 		= generic_rep_type
			,	gtr_type_args	= [atv_variable \\ {atv_variable} <- td_args] 
			,	gtr_iso 		= iso_def_sym
			,	gtr_isomap_group= NoIndex
			,	gtr_isomap		= EmptyDefinedSymbol		
			,	gtr_isomap_from	= EmptyDefinedSymbol		
			,	gtr_isomap_to	= EmptyDefinedSymbol
			,	gtr_type_info	= type_info_def_sym		
			,	gtr_cons_infos 	= cons_info_def_syms
			}	
		# gs_gtd_infos = {gs_gtd_infos & [module_index, type_def_index] = gtd_info} 
		= {gs & gs_modules = gs_modules, gs_gtd_infos = gs_gtd_infos}	 	

	build_isos module_index type_def_index cons_infos gs

		# (from_fun_index, 	from_group_index, gs) 	= newFunAndGroupIndex gs
		# (to_fun_index, 	to_group_index, gs) 	= newFunAndGroupIndex gs
		# (iso_fun_index, 	iso_group_index, gs) 	= newFunAndGroupIndex gs		

		# {gs_modules} = gs
		# (type_def=:{td_name}, gs_modules) = getTypeDef module_index type_def_index gs_modules 
		# gs = {gs & gs_modules = gs_modules}

		# iso_def_sym = {
			ds_ident  = {id_name="iso_"+++type_def.td_name.id_name, id_info = nilPtr },
			ds_index  = iso_fun_index,
			ds_arity  = 0	
			}
	
		# from_def_sym = {
			ds_ident  = {id_name="iso_from_generic_to_"+++type_def.td_name.id_name, id_info = nilPtr },
			ds_index  = from_fun_index,
			ds_arity  = 1	
			}
	
		# to_def_sym = {
			ds_ident  = {id_name="iso_to_generic_from_"+++type_def.td_name.id_name, id_info = nilPtr },
			ds_index  = to_fun_index,
			ds_arity  = 1	
			}
		# (from_fun_def, gs) = buildIsoFrom from_def_sym from_group_index module_index type_def gs	
		# (to_fun_def, gs) = buildIsoTo to_def_sym to_group_index module_index type_def cons_infos gs	

		# (iso_fun_def, gs) = 
			//buildUndefFunction iso_fun_index iso_group_index iso_name 1 gs_predefs gs_heaps	
			buildIsoRecord iso_def_sym iso_group_index from_def_sym to_def_sym gs	
		
		# fun_defs = [from_fun_def, to_fun_def, iso_fun_def]
		# groups = 
			[	{group_members=[from_fun_index]}
			, 	{group_members=[to_fun_index]}
			,	{group_members=[iso_fun_index]}
			] 
		= (iso_def_sym, fun_defs, groups, gs)
		
	build_cons_infos module_index type_def_index gs
		= 	case supportCons of
			False -> (EmptyDefinedSymbol, [], [], [], gs)
			True  -> build_cons_infos1 module_index type_def_index gs		

	build_cons_infos1 module_index type_def_index gs=:{gs_modules}
		# (type_def=:{td_rhs}, gs_modules) = getTypeDef module_index type_def_index gs_modules				 
		# (common_defs, gs_modules) = gs_modules ! [module_index]				
		# gs = {gs & gs_modules = gs_modules}
		
		# (type_fun_index, group_index, gs) = newFunAndGroupIndex gs				
		# type_fun_sym = 
			{	ds_ident = makeIdent ("type_info_" +++ type_def.td_name.id_name)
			, 	ds_index = type_fun_index
			,	ds_arity = 0
			}
				
		# (cons_fun_syms, cons_fun_defs, gs) = case td_rhs of
			(AlgType alts) 
				-> build_alg_cons_infos alts 0 type_fun_sym group_index common_defs gs
			(RecordType {rt_constructor}) 
				-> build_alg_cons_infos [rt_constructor] 0 type_fun_sym group_index common_defs gs
			_ -> ([], [], gs)
			
		# (type_fun_def, gs) = 
			build_typedef_info type_def type_fun_sym group_index cons_fun_syms gs

		# group = 
			{	group_members = [type_fun_index : [ds_index \\ {ds_index} <- cons_fun_syms]]
			}
		= (type_fun_sym, cons_fun_syms, [type_fun_def:cons_fun_defs], [group], gs)
		
	build_alg_cons_infos [] cons_num type_info_def_sym group_index common_defs gs
		= ([], [], gs)  	
	build_alg_cons_infos [cons_def_sym:cons_def_syms] cons_num type_info_def_sym group_index common_defs	gs
		# (fi, fd, gs) = build_cons_info cons_def_sym cons_num type_info_def_sym group_index common_defs gs
		# (fis, fds, gs) = build_alg_cons_infos cons_def_syms (inc cons_num) type_info_def_sym group_index common_defs	gs
		= ([fi:fis], [fd:fds], gs) 

	build_cons_info {ds_index,ds_arity} cons_num type_info_def_sym group_index common_defs gs=:{gs_main_dcl_module_n}
		# {cons_symb, cons_pos, cons_type} = common_defs.com_cons_defs.[ds_index]		
		# (fun_index, gs) = newFunIndex gs		
		# def_sym = 
			{	ds_ident = makeIdent ("cons_info_" +++ cons_symb.id_name)
			, 	ds_index = fun_index
			,	ds_arity = 0
			}
		# {gs_modules,gs_heaps, gs_predefs, gs_main_dcl_module_n}	= gs
		# cons_name_expr = makeStringExpr ("\""+++cons_symb.id_name+++"\"") gs_predefs
		# cons_arity_expr = makeIntExpr ds_arity
		# cons_num_expr = makeIntExpr cons_num
		# (cons_type_expr, gs_heaps) = buildFunApp gs_main_dcl_module_n type_info_def_sym [] gs_heaps 

		# gs = {gs & gs_heaps = gs_heaps, gs_modules = gs_modules}
		# (cons_arg_type_exprs, gs=:{gs_heaps}) = build_type_infos cons_type.st_args gs
		# (cons_arg_types_expr, gs_heaps) = makeListExpr cons_arg_type_exprs gs_predefs gs_heaps	
		
		# (cons_info_expr, gs_heaps) = buildPredefConsApp 
				PD_ConsConsDefInfo 
				[	cons_name_expr
				, 	cons_arity_expr
				, 	cons_num_expr
				, 	cons_type_expr
				,	cons_arg_types_expr
				] 
				gs_predefs gs_heaps
		# fun_def = makeFunction def_sym group_index [] cons_info_expr No [] gs_main_dcl_module_n cons_pos
			
		//# (fun_def, gs_heaps) = buildUndefFunction def_sym group_index gs_predefs gs_heaps
		= (def_sym, fun_def, {gs & gs_heaps=gs_heaps})

	build_type_infos [] gs = ([], gs)
	build_type_infos [t:ts] gs 
		# (e, gs) = build_type_info t gs
		# (es, gs) = build_type_infos ts gs
		= ([e:es], gs)
		
	build_type_def name arity vars cons_info_def_syms gs=:{gs_main_dcl_module_n, gs_predefs, gs_heaps}		
		# name_expr = makeStringExpr ("\""+++name+++"\"") gs_predefs
		# kind_expr = makeIntExpr arity
		# var_exprs = [ makeStringExpr ("\""+++v+++"\"") gs_predefs \\ v <- vars] 
		# (var_list_expr, gs_heaps) = makeListExpr var_exprs gs_predefs gs_heaps

		# (cons_info_exprs, gs_heaps) = mapSt build_app cons_info_def_syms gs_heaps  
			with 
				build_app cons_info_def_sym h 
					//= buildUndefFunApp [] gs_predefs h
					= buildFunApp gs_main_dcl_module_n cons_info_def_sym [] h
		# (cons_info_list_expr, gs_heaps) = makeListExpr cons_info_exprs gs_predefs gs_heaps
				
		# (typedefinfo_expr, gs_heaps) = buildPredefConsApp 
			PD_ConsTypeDefInfo 
			[	name_expr
			, 	kind_expr
			,	var_list_expr
			,	cons_info_list_expr
			] 
			gs_predefs gs_heaps
		= (typedefinfo_expr, {gs & gs_heaps = gs_heaps})
	
	build_type_def_app name arity vars cons_info_def_syms arg_exprs gs=:{gs_predefs, gs_heaps}
		# (arg_list_expr, gs_heaps) = makeListExpr arg_exprs gs_predefs gs_heaps		
		# (type_def_expr, gs=:{gs_heaps}) =
			build_type_def name arity vars cons_info_def_syms {gs & gs_heaps = gs_heaps}
		# (type_app_expr, gs_heaps) = buildPredefConsApp 
			PD_ConsTypeApp 
			[	type_def_expr
			,	arg_list_expr
			]
			gs_predefs gs_heaps
		
		= (type_app_expr, { gs & gs_heaps = gs_heaps})
			
	build_type_info {at_type=TA {type_name,type_arity} ts} gs
 		# (arg_exprs, gs) = build_type_infos ts gs
		= build_type_def_app type_name.id_name type_arity [] [] arg_exprs gs

	build_type_info {at_type=arg --> res} gs
		# (arg_expr, gs) = build_type_info arg gs
		# (res_expr, gs) = build_type_info res gs
		= build_type_def_app "->" 2 ["a", "b"] [] [arg_expr, res_expr] gs		
		
	build_type_info {at_type=TB t} gs
	
		# name = case t of 
			BT_Int			-> "Int" 
			BT_Char			-> "Char"
			BT_Real			-> "Real"
			BT_Bool			-> "Bool" 
			BT_Dynamic		-> "Dynamic"
			BT_File			-> "File"
			BT_World		-> "World"
			BT_String _ 	-> "String"		
	
		= build_type_def_app name 0 [] [] [] gs		

	build_type_info {at_type=TV {tv_name}} gs=:{gs_heaps, gs_predefs}
		# name_expr = makeStringExpr ("\"" +++ tv_name.id_name +++ "\"") gs_predefs
		# (expr, gs_heaps) = buildPredefConsApp PD_ConsTypeVar [ name_expr ] gs_predefs gs_heaps
		= (expr, {gs & gs_heaps = gs_heaps})

	build_type_info {at_type} gs=:{gs_heaps, gs_predefs}
		# name_expr = makeStringExpr ("\"error\"") gs_predefs 
		# (expr, gs_heaps) = buildPredefConsApp PD_ConsTypeVar [ name_expr ] gs_predefs gs_heaps
		= (expr, {gs & gs_heaps = gs_heaps})
				
	build_typedef_info 
			{td_pos,td_name, td_args} 
			type_info_def_sym 
			group_index 
			cons_info_def_syms 
			gs=:{gs_main_dcl_module_n}
		
		# type_vars = [ atv.atv_variable.tv_name.id_name \\ atv <- td_args]			
		# (body_expr, gs) = build_type_def 
			td_name.id_name	type_info_def_sym.ds_arity type_vars cons_info_def_syms gs 			
		# fun_def = makeFunction type_info_def_sym group_index [] body_expr No [] gs_main_dcl_module_n td_pos				
		= (fun_def, gs)
			
buildIsomapsForTypeDefs :: ![Global Index] !*GenericState
	-> (![FunDef], ![Group], !*GenericState)
buildIsomapsForTypeDefs td_indexes gs=:{gs_last_group}
	# gs = foldSt fill_function_indexes td_indexes gs
	# first_group = gs_last_group
	# (funs, gs) = build_isomap_functions td_indexes gs
	# (last_group, gs) = gs ! gs_last_group
	# groups = createArray (last_group - first_group) []
		//---> ("created " +++ toString (last_group - first_group) +++ " isomap groups")
	# groups = collect_groups first_group funs groups
	# groups = [ {group_members = fs} \\ fs <-: groups ] 
	= (map snd funs, groups, gs)
where	

	fill_function_indexes :: !(Global Index) !*GenericState -> !*GenericState
	fill_function_indexes {glob_module, glob_object} gs

		# (kind, gs) = get_kind glob_module glob_object gs 
		| kind == KindConst
			// types of kind * do not need isomaps - they are identity
			= gs

		# (from_fun_index, gs) = newFunIndex gs
		# (to_fun_index, gs) = newFunIndex gs
		# (rec_fun_index, gs) = newFunIndex gs

		# (gs=:{gs_gtd_infos, gs_modules}) = gs
		# (type_def=:{td_name, td_arity}, gs_modules) = getTypeDef glob_module glob_object gs_modules
		# (GTDI_Generic gt, gs_gtd_infos) = gs_gtd_infos ! [glob_module, glob_object]

		# gtd_info = GTDI_Generic {gt & 
			gtr_isomap_from 	= { 
				ds_ident = {id_name="isomap_from_"+++td_name.id_name, id_info=nilPtr}, 
				ds_index = from_fun_index, 
				ds_arity = (td_arity + 1)
				},
			gtr_isomap_to 	= { 
				ds_ident = {id_name="isomap_to_"+++td_name.id_name, id_info=nilPtr}, 
				ds_index = to_fun_index, 
				ds_arity = (td_arity + 1)
				},
			gtr_isomap 		= { 
				ds_ident = {id_name="isomap_"+++td_name.id_name, id_info=nilPtr}, 
				ds_index = rec_fun_index, 
				ds_arity = td_arity
				}
			}		
		# gs_gtd_infos = {gs_gtd_infos & [glob_module, glob_object] = gtd_info}		
		= {gs & gs_gtd_infos = gs_gtd_infos, gs_modules = gs_modules}			

	get_kind module_index type_index gs=:{gs_td_infos}	
		# (kind, gs_td_infos) = kindOfTypeDef module_index type_index gs_td_infos 
		= (kind, {gs & gs_td_infos = gs_td_infos})

	build_isomap_functions :: ![Global Index] !*GenericState
		-> (![(Index, FunDef)], !*GenericState)		
	build_isomap_functions [] gs = ([], gs)
	build_isomap_functions [{glob_module, glob_object}:td_indexes] gs
		# (funs1, gs) = build_isomap_function glob_module glob_object gs
		# (funs2, gs) = build_isomap_functions td_indexes gs
		= (funs1 ++ funs2, gs)
	
	build_isomap_function module_index type_def_index gs

		# (kind, gs) = get_kind module_index type_def_index gs
		| kind == KindConst
			// types of kind * do not need isomaps - they are identity
			= ([], gs)
		# (group_index, gs)  = get_group module_index type_def_index gs

		# {gs_modules, gs_gtd_infos} = gs
		# (type_def=:{td_name}, gs_modules) = getTypeDef module_index type_def_index gs_modules
		
		# (GTDI_Generic {gtr_isomap, gtr_isomap_to, gtr_isomap_from}, gs_gtd_infos) 
			= gs_gtd_infos![module_index, type_def_index]
		
		# gs = { gs & gs_gtd_infos = gs_gtd_infos, gs_modules = gs_modules } 

		# (from_fun_def, from_fun_index, gs) = 
			buildIsomapFromTo IsoFrom gtr_isomap_from group_index module_index type_def_index gs
		# (to_fun_def, to_fun_index, gs) = 
			buildIsomapFromTo IsoTo gtr_isomap_to group_index module_index type_def_index gs
		# (rec_fun_def, rec_fun_index, gs) = 
			buildIsomapForTypeDef gtr_isomap group_index module_index type_def gtr_isomap_from gtr_isomap_to gs
		
		# funs = [ (from_fun_index, from_fun_def), (to_fun_index, to_fun_def), (rec_fun_index, rec_fun_def) ]		
		= (funs, gs)
			//---> from_fun_def 
			//---> ("build isomap for", td_name, module_index, type_def_index)
		
	collect_groups :: !Index ![(Index, FunDef)] !*{[Index]} -> !*{[Index]} 
	collect_groups first_group_index [] groups = groups
	collect_groups first_group_index [(fun_index, fun=:{fun_symb, fun_info={fi_group_index}}):funs] groups
		# (group, groups) = groups ! [fi_group_index - first_group_index]
		# groups = {groups & [fi_group_index - first_group_index] = [fun_index:group]}
			//---> ("add fun " +++ fun_symb.id_name +++ " "+++ toString fun_index +++ 
			//		" to group " +++ toString fi_group_index) 
		= collect_groups first_group_index funs groups 

	get_group :: !Index  !Index !*GenericState 
		-> (!Index, !*GenericState)
	get_group module_index type_def_index gs=:{gs_gtd_infos}
		#! (gtd_info,gs_gtd_infos) = gs_gtd_infos![module_index, type_def_index]
		#! gt = case gtd_info of 
			(GTDI_Generic gt) 	-> gt
			_ -> abort "no generic representation for a type\n"
		| gt.gtr_isomap_group <> NoIndex // group index already allocated
			= (gt.gtr_isomap_group, { gs & gs_gtd_infos = gs_gtd_infos})
				//---> ("group for type already exists", module_index, type_def_index, gt.gtr_isomap_group) 	
		# (group_index, gs=:{gs_td_infos, gs_gtd_infos}) 
			= newGroupIndex {gs & gs_gtd_infos = gs_gtd_infos}
				
		#! (type_def_info, gs_td_infos) = gs_td_infos ! [module_index, type_def_index]
		#! gs_gtd_infos = update_group group_index type_def_info.tdi_group gs_gtd_infos
		= (group_index, { gs & gs_gtd_infos = gs_gtd_infos, gs_td_infos = gs_td_infos})
			//---> ("type group of type ", module_index, type_def_index, type_def_info.tdi_group_nr)

// Sjaak ...
	update_group :: !Index ![GlobalIndex] !*GenericTypeDefInfos -> !*GenericTypeDefInfos
	update_group group_index [] gtd_infos = gtd_infos	
	update_group group_index [{gi_module, gi_index}:type_def_global_indexes] gtd_infos
		#! (gtd_info, gtd_infos) = gtd_infos ! [gi_module, gi_index]
		#! gtd_info = case gtd_info of 
			(GTDI_Generic gt) 
				| gt.gtr_isomap_group <> NoIndex 
					-> abort "sanity check: updating already updated group\n"					
					-> GTDI_Generic {gt & gtr_isomap_group = group_index }
			_ 	-> gtd_info
		#! gtd_infos = {gtd_infos & [gi_module, gi_index] = gtd_info}
		= update_group group_index type_def_global_indexes gtd_infos


buildIsomapsForGenerics :: !*GenericState
	-> (![FunDef], ![Group], !*GenericState)
buildIsomapsForGenerics gs
	= build_modules 0 gs
where
	build_modules module_index gs=:{gs_modules}
		#! num_modules = size gs_modules
		| module_index == num_modules
			= ([], [], gs)					
		# (common_defs, gs_modules) = gs_modules ! [module_index]
		#  {com_generic_defs} = common_defs
		# com_generic_defs = {g \\ g <-: com_generic_defs} // make unique copy		
		# (new_funs, new_groups, com_generic_defs, gs) =
			build_isomaps module_index 0 com_generic_defs {gs & gs_modules = gs_modules}
		# (funs, groups, gs) = build_modules (inc module_index) gs
		# {gs_modules} = gs
		# gs_modules = { gs_modules & [module_index] = {common_defs & com_generic_defs = com_generic_defs}} 
		= (new_funs ++ funs, new_groups ++ groups, {gs & gs_modules = gs_modules})

	build_isomaps module_index generic_index generic_defs gs		
		#! num_generic_defs = size generic_defs
		| generic_index == num_generic_defs
			= ([], [], generic_defs, gs)													
		# (new_funs, new_groups, generic_defs, gs) = build_isomap module_index generic_index generic_defs gs 			
		# (funs, groups, generic_defs, gs) = build_isomaps module_index (inc generic_index) generic_defs gs		
		= (new_funs ++ funs, new_groups ++ groups, generic_defs, gs)	

	build_isomap module_index generic_index generic_defs gs				
		# (generic_def=:{gen_name, gen_type}, generic_defs) = generic_defs ! [generic_index] 		
		# (fun_index, group_index, gs) = newFunAndGroupIndex gs 		
		# def_sym = {
			ds_ident = {id_name="isomap_"+++gen_name.id_name, id_info = nilPtr}, 
			ds_index = fun_index, 
			ds_arity = gen_type.gt_arity
			}
		# generic_defs = {generic_defs & [generic_index] = {generic_def & gen_isomap = def_sym}}				
		# (fun_def, _, gs) = buildIsomapForGeneric def_sym group_index generic_def gs
		//# (fun_def, gs) = build_undef_fun def_sym group_index gs	
		# group = {group_members = [fun_index]}			
		= ([fun_def], [group], generic_defs, gs)
	where
		build_undef_fun def_sym group gs=:{gs_heaps, gs_predefs}
			# (fun_def, gs_heaps) = buildUndefFunction def_sym group gs_predefs gs_heaps
			= (fun_def, {gs & gs_heaps = gs_heaps})
						
// generate instances  
buildInstances :: !*GenericState	
	-> (![FunDef], ![Group], !*GenericState)
buildInstances gs
	= build_modules 0 gs
where
	build_modules :: !Index !*GenericState 
		-> (![FunDef], ![Group], !*GenericState)
	build_modules module_index gs=:{gs_modules}
		#! num_modules = size gs_modules
		| module_index == num_modules
			= ([], [], gs)					
		# (common_defs, gs_modules) = gs_modules ! [module_index]
		#  {com_instance_defs} = common_defs
		# com_instance_defs = {i \\ i <-: com_instance_defs} // make unique copy		
		# (new_funs, new_groups, com_instance_defs, gs) =
			build_instances module_index 0 com_instance_defs {gs & gs_modules = gs_modules}
		# (funs, groups, gs) = build_modules (inc module_index) gs
		# {gs_modules} = gs
		# gs_modules = { gs_modules & [module_index] = {common_defs & com_instance_defs = com_instance_defs}} 
		= (new_funs ++ funs, new_groups ++ groups, {gs & gs_modules = gs_modules})

	build_instances :: !Index !Index !*{#ClassInstance} !*GenericState 
		-> (![FunDef], ![Group], !*{#ClassInstance}, !*GenericState)
	build_instances module_index instance_index instance_defs gs
		#! num_instance_defs = size instance_defs
		| instance_index == num_instance_defs
			= ([], [], instance_defs, gs)													
		# (new_funs, new_groups, instance_defs, gs) = build_instance module_index instance_index instance_defs gs 			
		# (funs, groups, instance_defs, gs) = build_instances module_index (inc instance_index) instance_defs gs		
		= (new_funs ++ funs, new_groups ++ groups, instance_defs, gs)	
	
	build_instance :: !Index !Index !*{#ClassInstance} !*GenericState 
		-> (![FunDef], ![Group], !*{#ClassInstance}, !*GenericState)	
	build_instance module_index instance_index instance_defs gs=:{gs_modules}
		# (instance_def, instance_defs) = instance_defs ! [instance_index]
		| not instance_def.ins_is_generic 
			= ([], [], instance_defs, gs)
		
		| instance_def.ins_generate
			#! (fun_def, fun_def_sym, gs) = build_instance_fun instance_def gs
			#! instance_def = { instance_def & ins_members = {fun_def_sym} }		
			#! instance_defs = {instance_defs & [instance_index] = instance_def} 
			# (dcl_fun_index, gs) = get_dcl_member_index instance_index gs
				with
			 		get_dcl_member_index icl_instance_index gs=:{gs_main_dcl_module_n}			 		
//			 			# ({dcl_common}, gs_dcl_modules) = gs_dcl_modules![gs_main_dcl_module_n] 
//						# gs = {gs & gs_dcl_modules = gs_dcl_modules}
//						# dcl_index = case dcl_conversions of
						# dcl_index = NoIndex
/*
			 				No 	-> NoIndex
			 				Yes conversion_table 
					 			# instance_table = conversion_table.[cInstanceDefs]
					 			# dcl_instance_index = find_dcl_instance_index icl_instance_index 0 instance_table
					 			| dcl_instance_index == NoIndex
					 				-> NoIndex
					 			| otherwise 
					 				# dcl_instance = dcl_common.com_instance_defs.[dcl_instance_index]
					 				# dcl_index = dcl_instance.ins_members.[0].ds_index			 			 				 			
					 				-> dcl_index
*/
					 	= (dcl_index, gs)						 				
			 		where
			 			find_dcl_instance_index icl_instance_index index instance_table
			 				| index == size instance_table
			 					= NoIndex
			 				| instance_table.[index] == icl_instance_index
			 					= index
			 				| otherwise
			 					= find_dcl_instance_index icl_instance_index (inc index) instance_table 	 

			# gs = case dcl_fun_index of
					NoIndex -> gs
					_ 
//						# gs = update_dcl_icl_conversions dcl_fun_index fun_def_sym.ds_index gs
//						# gs = update_dcl_fun_conversions module_index dcl_fun_index fun_def_sym.ds_index gs
						-> gs
/*			 	with
			 		update_dcl_icl_conversions dcl_index icl_index gs=:{gs_opt_dcl_icl_conversions=No}
			 			= gs
			 		update_dcl_icl_conversions dcl_index icl_index gs=:{gs_opt_dcl_icl_conversions=Yes cs}
			 			#! (table_size, cs) = usize cs
			 			| dcl_index < table_size
			 				= {gs & gs_opt_dcl_icl_conversions=Yes {cs & [dcl_index] = icl_index}}   
			 					//---> ("update dcl-to-icl conversion table", dcl_index, icl_index)
			 				= {gs & gs_opt_dcl_icl_conversions=Yes cs}
			 					//---> ("update dcl-to-icl conversion table: index does not fit", dcl_index, icl_index)
			 		
			 		update_dcl_fun_conversions module_index dcl_index icl_index gs=:{gs_dcl_modules}
			 			# (dcl_module=:{dcl_conversions}, gs_dcl_modules) = gs_dcl_modules ! [module_index]		 			
			 			# dcl_conversions = case dcl_conversions of
			 				No 		-> No
			 				Yes table
			 					# fun_table = table.[cFunctionDefs] 			 				 
			 					# (size_fun_table, fun_table) = usize fun_table
			 					| dcl_index < size_fun_table
			 						# fun_table = {x \\ x <-: fun_table}
			 						# fun_table = {fun_table & [dcl_index] = icl_index}
			 						-> Yes {{x\\x<-:table} & [cFunctionDefs] = fun_table}
			 					| otherwise
			 						-> Yes table
			 			# dcl_module = { dcl_module & dcl_conversions = dcl_conversions} 			 			
			 			= {gs & gs_dcl_modules = {gs_dcl_modules & [module_index] = dcl_module }}
*/			 					 						
			= ([fun_def], [{group_members = [fun_def_sym.ds_index]}], instance_defs, gs)

		| supportPartialInstances && instance_def.ins_partial			

			#! (fun_def, fun_def_sym, gs) = build_instance_fun instance_def gs 

			#! (instance_def, ins_fun_index, ins_fun_def, gs) 
				= move_instance instance_def gs
			#! instance_defs = {instance_defs & [instance_index] = instance_def} 

			#! (ins_fun_def, gs) = add_generic_alternative ins_fun_def fun_def_sym gs
			
			= (	[fun_def, ins_fun_def], 
				[{group_members = [fun_def_sym.ds_index]}, {group_members = [ins_fun_index]}], 
				instance_defs, gs)
					//---> ("build partial instance", instance_def.ins_ident, instance_def.ins_type)

		| otherwise
			= ([], [], instance_defs, gs)
			
	add_generic_alternative ins_fun_def gen_fun_ds gs=:{gs_heaps, gs_main_dcl_module_n}	
		# (TransformedBody tb) = ins_fun_def.fun_body
		# (Case cas) = tb.tb_rhs
		
		#! (arg_exprs, new_tb_args, gs_heaps) =  buildBoundVarExprs tb.tb_args gs_heaps
		
		#! (app_expr, gs_heaps) = buildFunApp gs_main_dcl_module_n gen_fun_ds arg_exprs gs_heaps 		
		#! case_expr = Case {cas & case_default = (Yes app_expr)}
		
		#! ins_fun_def = 
			{	ins_fun_def
			&	fun_body = TransformedBody {tb & tb_rhs=case_expr, tb_args = new_tb_args}
			, 	fun_info =
				{	ins_fun_def.fun_info 
				& 	fi_calls = 
					[	FunCall gen_fun_ds.ds_index NotALevel
					:	ins_fun_def.fun_info.fi_calls ]
				} 
			}

		= (ins_fun_def, {gs & gs_heaps = gs_heaps})
			//---> ("created generic alterntaive for " +++ ins_fun_def.fun_symb.id_name)

	move_instance instance_def=:{ins_members, ins_pos} gs=:{gs_main_dcl_module_n}
		# (new_fun_index, new_fun_group, gs=:{gs_fun_defs, gs_predefs, gs_heaps}) 
			= newFunAndGroupIndex gs
		# ins_fun_index = ins_members.[0].ds_index
		# (ins_fun_def, gs_fun_defs) = gs_fun_defs ! [ins_fun_index]

		// set new indexes in the function
		# new_ins_fun_def =
			{	ins_fun_def
			//&	fun_index = new_fun_index
			&	fun_info = {ins_fun_def.fun_info & fi_group_index = new_fun_group}	
			}							
		#! new_member = {ins_members.[0] & ds_index = new_fun_index}
		#! instance_def = {instance_def & ins_members = {new_member}}
		
		// build a dummy function and set it at the old position
		#! (undef_expr, gs_heaps) = buildUndefFunApp [] gs_predefs gs_heaps
		#! (arg_vars,  gs_heaps)  = 
			mapSt buildFreeVar0 ["v" +++ toString i \\ i <- [1..ins_fun_def.fun_arity]] gs_heaps
		# {fun_symb, fun_arity, fun_info, fun_type, fun_pos} = ins_fun_def
		#! dummy_def_sym = 
			{	ds_ident = fun_symb
			,	ds_arity = fun_arity
			,	ds_index = ins_fun_index
			}
		#! dummy_fun_def = 
			makeFunction dummy_def_sym fun_info.fi_group_index arg_vars undef_expr fun_type [] gs_main_dcl_module_n fun_pos					
		#! gs_fun_defs = {gs_fun_defs & [ins_fun_index] = dummy_fun_def}
				
		= (instance_def, new_fun_index, new_ins_fun_def, {gs & gs_fun_defs = gs_fun_defs, gs_heaps = gs_heaps})
								
	build_instance_fun instance_def gs=:{gs_modules}
		# {ins_class, ins_generic} = instance_def				
		# (class_def, gs_modules) = getClassDef ins_class.glob_module ins_class.glob_object.ds_index gs_modules
		# (member_def, gs_modules) = getMemberDef ins_class.glob_module class_def.class_members.[0].ds_index gs_modules
		# (generic_def, gs_modules) = getGenericDef ins_generic.glob_module ins_generic.glob_object gs_modules 
		# (fun_index, group_index, gs) = newFunAndGroupIndex {gs & gs_modules=gs_modules}
		# fun_def_sym = {
			ds_ident = instance_def.ins_ident, 
			ds_index = fun_index, 
			ds_arity = member_def.me_type.st_arity
			}
						
		//# (fun_def, gs) = build_dummy_instance fun_def_sym group_index gs	
		# (fun_def, gs) = buildInstance fun_def_sym group_index instance_def generic_def gs
		= (fun_def, fun_def_sym, gs)
			
	build_dummy_instance fun_def_sym group_index gs=:{gs_predefs, gs_heaps}
		# (fun_def, gs_heaps) = buildUndefFunction fun_def_sym group_index gs_predefs gs_heaps
		= (fun_def, {gs & gs_heaps = gs_heaps}) 

// generate kind star instances  
buildKindConstInstances :: !*GenericState	
	-> (![FunDef], ![Group], !*GenericState)
buildKindConstInstances gs
	= build_modules 0 gs
where
	build_modules :: !Index !*GenericState 
		-> (![FunDef], ![Group], !*GenericState)
	build_modules module_index gs=:{gs_modules, gs_main_dcl_module_n}

		#! num_modules = size gs_modules
		| module_index == num_modules
			= ([], [], {gs & gs_modules = gs_modules})					
		# (new_funs, new_groups, instance_defs, gs) =
			build_instances module_index 0 {gs & gs_modules = gs_modules}
		# (funs, groups, gs) = build_modules (inc module_index) gs
		# {gs_modules} = gs

		// add instances 
/*	
		# (common_defs=:{com_instance_defs}, gs_modules) = gs_modules ! [module_index]		
		# com_instance_defs = arrayPlusList com_instance_defs instance_defs		
		# gs_modules = { gs_modules & [module_index] = {common_defs & com_instance_defs = com_instance_defs}} 
*/
		# (common_defs=:{com_instance_defs}, gs_modules) = gs_modules ! [gs_main_dcl_module_n]		
		# com_instance_defs = arrayPlusList com_instance_defs instance_defs		
		# gs_modules = { gs_modules & [gs_main_dcl_module_n] = {common_defs & com_instance_defs = com_instance_defs}} 
			
		= (new_funs ++ funs, new_groups ++ groups, {gs & gs_modules = gs_modules})

	build_instances :: !Index !Index !*GenericState 
		-> (![FunDef], ![Group], ![ClassInstance], !*GenericState)
	build_instances module_index instance_index gs=:{gs_modules}
		# ({com_instance_defs}, gs_modules) = gs_modules ! [module_index]
		#! num_instance_defs = size com_instance_defs		
		# gs = { gs & gs_modules = gs_modules }		
		| instance_index == num_instance_defs
			= ([], [], [], gs)
																
		# (new_funs, new_groups, new_instance_defs, gs) = build_instance module_index instance_index gs 			
		# (funs, groups, instance_defs, gs) = build_instances module_index (inc instance_index) gs		
		= (new_funs ++ funs, new_groups ++ groups, new_instance_defs ++ instance_defs, gs)	
	build_instance :: !Index !Index !*GenericState 
		-> (![FunDef], ![Group], ![ClassInstance], !*GenericState)	
	build_instance module_index instance_index gs=:{gs_modules, gs_td_infos, gs_heaps}
		# (instance_def, gs_modules) = getInstanceDef module_index instance_index gs_modules		
		# {	ins_ident, ins_type, ins_pos,
			ins_generate, ins_is_generic, ins_generic} = instance_def
		
		| not (ins_is_generic)
			= ([], [], [], {gs & gs_td_infos = gs_td_infos, gs_modules = gs_modules, gs_heaps = gs_heaps})

		# it_type = hd ins_type.it_types
		#! (kind, gs_td_infos) = kindOfType it_type gs_td_infos
		| kind == KindConst
			= ([], [], [], { gs & gs_td_infos = gs_td_infos, gs_modules = gs_modules, gs_heaps = gs_heaps})

		# (KindArrow kind_args) = kind
		# (generic_def, gs_modules) = getGenericDef ins_generic.glob_module ins_generic.glob_object gs_modules
		# (ok, kind_star_class_def_sym) = getGenericClassForKind generic_def KindConst
		| not ok
			= abort "no class for kind *"
		
		# (oks, arg_class_def_syms) = unzip (map (getGenericClassForKind generic_def) kind_args)
		| not (and oks)
			= abort "no class for an agrument kind"
			
		# (kind_star_class_def, gs_modules) = getClassDef ins_generic.glob_module kind_star_class_def_sym.ds_index gs_modules 
		# (member_def, gs_modules) = getMemberDef ins_generic.glob_module kind_star_class_def.class_members.[0].ds_index gs_modules 	

		# glob_kind_star_class_def_sym = {glob_module=ins_generic.glob_module, glob_object=kind_star_class_def_sym}
		# glob_arg_class_def_syms = [{glob_module=ins_generic.glob_module, glob_object=c} \\ c <- arg_class_def_syms]
		
		# (new_ins_type, gs_heaps) = 
			//build_instance_type ins_type kind {glob_module=ins_generic.glob_module, glob_object=kind_star_class_def_sym} gs_heaps		
			build_instance_type1 
				ins_type 
				glob_arg_class_def_syms 
				glob_kind_star_class_def_sym 
				gs_heaps

		# gs = {gs & gs_modules=gs_modules, gs_td_infos = gs_td_infos, gs_heaps = gs_heaps}
		# (fun_index, group_index, gs) = newFunAndGroupIndex gs
		# fun_def_sym = {
			ds_ident = kind_star_class_def.class_name, // kind star name 
			ds_index = fun_index, 
			ds_arity = member_def.me_type.st_arity
			}
						
		//# (fun_def, gs) = build_dummy_instance fun_def_sym group_index gs	
		# generic_def_sym = {
			ds_ident=generic_def.gen_name, 
			ds_index=ins_generic.glob_object,
			ds_arity=0
			}
		# (fun_def, gs) = 
			//buildKindConstInstance fun_def_sym group_index ins_generic.glob_module generic_def_sym kind gs
			buildKindConstInstance1 fun_def_sym group_index ins_generic.glob_module generic_def_sym kind_args gs

		# new_instance_def = {
			ins_class 		= {glob_module = ins_generic.glob_module, glob_object = kind_star_class_def_sym},	
			ins_ident 		= kind_star_class_def.class_name,	
			ins_type  		= new_ins_type,
			ins_members 	= {fun_def_sym},
			ins_specials 	= SP_None,
			ins_pos			= ins_pos, 
			ins_is_generic	= True, 
			ins_generate	= False,
			ins_partial		= False,
			ins_generic 	= ins_generic
			}
			//---> fun_def

		= ([fun_def], [{group_members = [fun_index]}], [new_instance_def], gs)
		
	build_dummy_instance fun_def_sym group_index gs=:{gs_predefs, gs_heaps}
		# (fun_def, gs_heaps) = buildUndefFunction fun_def_sym group_index gs_predefs gs_heaps
		= (fun_def, {gs & gs_heaps = gs_heaps})
		
	build_instance_type ins_type=:{it_vars, it_types, it_context} (KindArrow kinds) class_glob_def_sym heaps		
		#! type_var_names = ["a" +++ toString i \\ i <- [1 .. (length kinds)]]
		#! (type_vars, heaps) = mapSt buildTypeVar type_var_names heaps
		#! type_var_types = [TV tv \\ tv <- type_vars] 	
		#! new_type_args = [makeAType t TA_Multi \\ t <- type_var_types]

		#! new_type = fill_type_args (hd it_types) new_type_args
			with 
				fill_type_args (TA type_symb_ident=:{type_arity} type_args) new_type_args
					#! type_arity = type_arity + length new_type_args 
					#! type_args = type_args ++ new_type_args
					= TA {type_symb_ident & type_arity = type_arity} type_args 
				fill_type_args TArrow [arg_type, res_type]
					= arg_type --> res_type
				fill_type_args (TArrow1 arg_type) [res_type]
					= arg_type --> res_type	 
		
		#! (new_contexts, heaps) = mapSt (build_type_context class_glob_def_sym) type_var_types heaps
		
		#! new_ins_type = { ins_type & 
			it_vars = it_vars ++ type_vars,
			it_types = [new_type],
			it_context = it_context ++ new_contexts
			}
		= (new_ins_type, heaps)
			//---> new_ins_type			

	build_instance_type1 ins_type=:{it_vars, it_types, it_context} arg_class_def_syms class_glob_def_sym heaps		
		#! type_var_names = ["a" +++ toString i \\ i <- [1 .. (length arg_class_def_syms)]]
		#! (type_vars, heaps) = mapSt buildTypeVar type_var_names heaps
		#! type_var_types = [TV tv \\ tv <- type_vars] 	
		#! new_type_args = [makeAType t TA_Multi \\ t <- type_var_types]

		#! new_type = fill_type_args (hd it_types) new_type_args
			with 
				fill_type_args (TA type_symb_ident=:{type_arity} type_args) new_type_args
					#! type_arity = type_arity + length new_type_args 
					#! type_args = type_args ++ new_type_args
					= TA {type_symb_ident & type_arity = type_arity} type_args 
				fill_type_args TArrow [arg_type, res_type]
					= arg_type --> res_type
				fill_type_args (TArrow1 arg_type) [res_type]
					= arg_type --> res_type	 
		
		#! (new_contexts, heaps) 
			= mapSt build_type_context1 (zip2 arg_class_def_syms type_var_types) heaps
		
		#! new_ins_type = { ins_type & 
			it_vars = it_vars ++ type_vars,
			it_types = [new_type],
			it_context = it_context ++ new_contexts
			}
		= (new_ins_type, heaps)
			//---> new_ins_type			
		
	build_type_var name heaps=:{hp_type_heaps=hp_type_heaps=:{th_vars}}
		# (tv_info_ptr, th_vars) = newPtr TVI_Empty th_vars
		# type_var = {
			tv_name = {id_name = name, id_info = nilPtr},
			tv_info_ptr = tv_info_ptr
			}
		= (	type_var, {heaps & hp_type_heaps = {hp_type_heaps & th_vars = th_vars}})
			
	build_type_context class_glob_def_sym type heaps=:{hp_var_heap}
		# (var_info_ptr, hp_var_heap) = newPtr VI_Empty hp_var_heap			
		# type_context =		
			{	tc_class = class_glob_def_sym
			,	tc_types = [type]
			,	tc_var	 = var_info_ptr
			}
		= (type_context, {heaps & hp_var_heap = hp_var_heap})	

	build_type_context1 (class_def_sym, type) heaps=:{hp_var_heap}
		# (var_info_ptr, hp_var_heap) = newPtr VI_Empty hp_var_heap			
		# type_context =		
			{	tc_class = class_def_sym
			,	tc_types = [type]
			,	tc_var	 = var_info_ptr
			}
		= (type_context, {heaps & hp_var_heap = hp_var_heap})	

									
// for all generic instances determine and set types
// of their functions
determineMemberTypes :: !Index !Index !*GenericState	
	-> !*GenericState
determineMemberTypes module_index ins_index 
		gs=:{gs_modules, gs_fun_defs, gs_heaps=gs_heaps=:{hp_var_heap, hp_type_heaps}, gs_dcl_modules, gs_main_dcl_module_n}
	#! (num_modules, gs_modules) = usize gs_modules
	| module_index == num_modules
		= {gs & gs_modules = gs_modules}
	#! (common_defs=:{com_instance_defs}, gs_modules) = gs_modules![module_index]		
	| ins_index == size com_instance_defs
		= determineMemberTypes (inc module_index) 0 {gs & gs_modules = gs_modules} 		
	#! (instance_def, com_instance_defs) = com_instance_defs![ins_index]
	| not instance_def.ins_is_generic		
		= determineMemberTypes module_index (inc ins_index) {gs & gs_modules = gs_modules}
	
	#! gs = determine_member_type module_index ins_index instance_def {gs & gs_modules = gs_modules}
	= determineMemberTypes module_index (inc ins_index) gs
where
	determine_member_type 
			module_index 
			ins_index 
			{ins_ident, ins_class, ins_type, ins_members} 
			gs=:{	gs_modules, 
					gs_fun_defs, 
					gs_heaps=gs_heaps=:{hp_var_heap, hp_type_heaps}, 
					gs_dcl_modules, 
					gs_main_dcl_module_n,
					gs_opt_dcl_icl_conversions,
					gs_error}
		
		#! (class_def, gs_modules) = getClassDef ins_class.glob_module ins_class.glob_object.ds_index gs_modules
		#! (member_def, gs_modules) = getMemberDef ins_class.glob_module class_def.class_members.[0].ds_index gs_modules
		#! {me_type, me_class_vars}  = member_def
					
		// determine type of the instance function		
		#! (symbol_type, _, hp_type_heaps, _, gs_error) = 
			determineTypeOfMemberInstance me_type me_class_vars ins_type SP_None hp_type_heaps No gs_error
		#! (st_context, hp_var_heap) = initializeContextVariables symbol_type.st_context hp_var_heap
		#! symbol_type = {symbol_type & st_context = st_context}			

		// determine the instance function index (in icl or dcl)
		#! fun_index = ins_members.[0].ds_index
		| fun_index == NoIndex
			= abort "no generic instance function\n"				
		
		// update the instance function
		| module_index == gs_main_dcl_module_n	// icl module
			#! (fun_def, gs_fun_defs) = gs_fun_defs![fun_index]
			#! fun_def = { fun_def & fun_type = Yes symbol_type } 		
			#! gs_fun_defs = {gs_fun_defs & [fun_index] = fun_def}
			
			// update corresponding DCL function type, which is empty at the moment
//			#! (gs_dcl_modules) = gs_dcl_modules ! [gs_main_dcl_module_n]  
			#! (dcl_fun_index, gs_opt_dcl_icl_conversions) 
				= find_dcl_fun_index fun_index gs_opt_dcl_icl_conversions// XXX
				with
					find_dcl_fun_index icl_fun_index No
						= (NoIndex /*abort "no dcl_icl conversions table\n"*/, No)
					find_dcl_fun_index icl_fun_index (Yes table)
						#! table1 = {x\\x<-:table} 
						= find_index 0 icl_fun_index table
					find_index i index table
						#! (size_table, table) = usize table
						| i == size_table
							= (NoIndex /*abort ("not found dcl function index " +++ toString index)*/, Yes table)
						#! (x, table) = table ! [i]
						| x == index 
							= (i /*abort ("found dcl function index " +++ toString index +++ " " +++ toString i)*/, Yes table) 
							= find_index (inc i) index table
					
									
			#! gs_dcl_modules = case dcl_fun_index of
				NoIndex -> gs_dcl_modules
				_		-> update_dcl_fun_type gs_main_dcl_module_n dcl_fun_index symbol_type gs_dcl_modules
						
			= 	{ 	gs 
				& 	gs_modules = gs_modules
				,	gs_fun_defs = gs_fun_defs
				,	gs_dcl_modules = gs_dcl_modules
				,	gs_opt_dcl_icl_conversions = gs_opt_dcl_icl_conversions  
				,	gs_heaps = {gs_heaps & hp_type_heaps = hp_type_heaps, hp_var_heap = hp_var_heap}
				,	gs_error = gs_error
				}

		| otherwise // dcl module
				//---> ("update dcl instance function", ins_ident, module_index, ins_index, symbol_type)
			#! gs_dcl_modules = update_dcl_fun_type module_index fun_index symbol_type gs_dcl_modules					
			= 	{ 	gs 
				& 	gs_modules = gs_modules
				,	gs_dcl_modules = gs_dcl_modules
				,	gs_heaps = {gs_heaps & hp_type_heaps = hp_type_heaps, hp_var_heap = hp_var_heap} 
				,	gs_error = gs_error
				}
				
	update_dcl_fun_type module_index fun_index symbol_type dcl_modules
		# (dcl_module=:{dcl_functions}, dcl_modules) = dcl_modules ! [module_index]  
		# (dcl_fun, dcl_functions) = dcl_functions ! [fun_index]
		# dcl_fun = 
			{ dcl_fun 
			& ft_arity = symbol_type.st_arity
			, ft_type = symbol_type
			}
		# dcl_functions = {{x \\ x <-: dcl_functions} & [fun_index] = dcl_fun}
		# dcl_module={dcl_module & dcl_functions = dcl_functions}
		= {dcl_modules & [module_index] = dcl_module}	
		 
		
kindOfTypeDef :: Index Index !*TypeDefInfos -> (!TypeKind, !*TypeDefInfos)
kindOfTypeDef module_index td_index td_infos 
	#! ({tdi_kinds}, td_infos) = td_infos![module_index, td_index] 
	| isEmpty tdi_kinds
		= (KindConst, td_infos)
		= (KindArrow (tdi_kinds/* ++ [KindConst]*/), td_infos)

kindOfType :: !Type !*TypeDefInfos -> (!TypeKind, !*TypeDefInfos)
kindOfType (TA type_cons args) td_infos
	#! {glob_object,glob_module} = type_cons.type_index
	#! ({tdi_kinds}, td_infos) = td_infos![glob_module,glob_object] 
	#! kinds = drop (length args) tdi_kinds	
	| isEmpty kinds 
		= (KindConst, td_infos) 
		= (KindArrow (kinds/* ++ [KindConst]*/), td_infos)
kindOfType TArrow td_infos
	= (KindArrow [KindConst, KindConst/*, KindConst*/], td_infos)
kindOfType (TArrow1 _) td_infos 
	= (KindArrow [KindConst/*, KindConst*/], td_infos)
kindOfType (TV _) td_infos 
	= (KindConst, td_infos)
kindOfType (GTV _) td_infos 
	= (KindConst, td_infos)
kindOfType (TQV _) td_infos 
	= (KindConst, td_infos)
kindOfType _ td_infos 
	= (KindConst, td_infos)
			
buildClassDef :: !Index !Index !Index !GenericDef !TypeKind !*GenericState
	-> (!ClassDef, !MemberDef!, !GenericDef, *GenericState)	
buildClassDef 	module_index class_index member_index generic_def=:{gen_name, gen_classes} kind gs=:{gs_heaps}
	#! ident = makeIdent (gen_name.id_name +++ ":" +++ (toString kind))
	#! class_ds={ds_ident=ident, ds_index=class_index, ds_arity=0}
	#! (class_var, gs_heaps) = build_class_var gs_heaps
	#! (member_def, class_contexts, gs_heaps) = build_member module_index class_index member_index class_var class_ds generic_def gs_heaps
	#! class_def = build_class module_index class_index member_index class_var kind ident generic_def member_def class_contexts
	#! generic_def = { generic_def & 	gen_classes = [{gci_kind=kind,gci_class=class_ds}:gen_classes]}
	= (class_def, member_def, generic_def, {gs & gs_heaps = gs_heaps}) 
		//---> ("generated class " +++ ident.id_name)
where

	build_class_var heaps=:{hp_type_heaps=hp_type_heaps=:{th_vars}}
		#! (class_var, th_vars) = freshTypeVar (makeIdent "class_var") th_vars
		=(class_var, {heaps & hp_type_heaps = {hp_type_heaps & th_vars = th_vars}})

	build_member 
			module_index class_index member_index 
			class_var class_ds=:{ds_ident} generic_def=:{gen_type} 
			heaps=:{hp_var_heap, hp_type_heaps}
		#! (type_ptr, hp_var_heap) = newPtr VI_Empty hp_var_heap 
		#! (tc_var_ptr, hp_var_heap) = newPtr VI_Empty hp_var_heap  
		#! type_context = 
			{	tc_class = {glob_module = module_index, glob_object=class_ds}
			,	tc_types = [ TV class_var ] 
			,	tc_var = tc_var_ptr 
			}
		#! (member_type, class_contexts, hp_type_heaps, hp_var_heap) = buildMemberType2 generic_def kind class_var hp_type_heaps hp_var_heap
		//#! member_type = { member_type & st_context = [type_context : gen_type.gt_type.st_context] }
		#! member_type = { member_type & st_context = [type_context : member_type.st_context] }
		#! member_def = {
			me_symb = ds_ident, // same name as class
			me_class = {glob_module = module_index, glob_object = class_index},
			me_offset = 0,
			me_type = member_type,
			me_type_ptr = type_ptr,				// empty
			me_class_vars = [class_var], 		// the same variable as in the class
			me_pos = generic_def.gen_pos,
			me_priority = NoPrio
			}
				//---> ("member_type", member_type)
		= (member_def, class_contexts, {heaps & hp_type_heaps = hp_type_heaps, hp_var_heap = hp_var_heap})
	
	build_class 
			module_index class_index member_index class_var kind ident 
			generic_def=:{gen_pos} member_def=:{me_type} class_contexts
		#! class_member = {ds_ident=ident, ds_index = member_index, ds_arity = me_type.st_arity}
		#! class_dictionary = { 
			ds_ident = ident, 
			ds_arity = 0, 
			ds_index = NoIndex/*index in the type def table, filled in later*/ 
			}
		#! class_def = { 
			class_name = ident, 
			class_arity = 1,  
			class_args = [class_var],
		    class_context = class_contexts, 
		    class_pos = gen_pos, 
		    class_members = createArray 1 class_member, 
		    class_cons_vars = 0, // dotted class variables
		    class_dictionary = class_dictionary,
		    class_arg_kinds = [kind]
		    }	 
			
		= class_def	

currySymbolType1 :: !SymbolType !String !*TypeHeaps 
	-> (!AType, ![AttributeVar], ![AttrInequality], !*TypeHeaps)
currySymbolType1 {st_args=[], st_result} attr_var_name th
	= (st_result, [], [], th)
currySymbolType1 {st_args, st_result} attr_var_name th=:{th_attrs}
	// TA_None indicates top-level attribute
	#! (at, attr_vars, ais, index, th_attrs) = curry_type st_args st_result TA_None 0 th_attrs
	= (at, attr_vars, ais, {th & th_attrs = th_attrs})
where
	curry_type [] type cum_attr index th_attrs 
		= (type, [], [], index, th_attrs)
	curry_type [at=:{at_attribute}] type cum_attr index th_attrs
		#! t = makeAType (at --> type) (if (cum_attr == TA_None) TA_Multi cum_attr)
		= (t, [], [], index, th_attrs)		 						 
	curry_type [at=:{at_attribute}:ats] type cum_attr index th_attrs
		#! (next_cum_attr, avs1, ais1, index, th_attrs) = combine_attributes at_attribute cum_attr index th_attrs
		#! (res_type, avs2, ais2, index, th_attrs) = curry_type ats type next_cum_attr index th_attrs 
		#! t = makeAType (at --> res_type) cum_attr
		= (t, avs1 ++ avs2, ais1 ++ ais2, index, th_attrs) 
	
	combine_attributes TA_Unique cum_attr index th_attrs
		= (TA_Unique, [], [], index, th_attrs)
	combine_attributes (TA_Var av) (TA_Var cum_av) index th_attrs
		#! (new_av, th_attrs) = freshAttrVar (makeIdent (attr_var_name+++ /*"_"+++*/ toString index)) th_attrs
		#! ais = [
			{ai_offered=new_av, ai_demanded=av},
			{ai_offered=new_av, ai_demanded=cum_av}]
		= (TA_Var new_av, [new_av], ais, (inc index), th_attrs)
	combine_attributes (TA_Var av) TA_None index th_attrs
		#! (new_av, th_attrs) = freshAttrVar (makeIdent (attr_var_name+++ /*"_"+++*/ toString index)) th_attrs
		= (TA_Var new_av, [new_av], [{ai_offered=new_av, ai_demanded=av}], (inc index), th_attrs)		
	combine_attributes (TA_Var _) cum_attr index th_attrs
		= (cum_attr, [], [], index, th_attrs)
	combine_attributes _ (TA_Var cum_av) index th_attrs
		#! (new_av, th_attrs) = freshAttrVar (makeIdent (attr_var_name+++ /*"_"+++*/ toString index)) th_attrs
		= (TA_Var new_av, [new_av], [{ai_offered=new_av, ai_demanded=cum_av}], (inc index), th_attrs)
	combine_attributes _ TA_None index th_attrs
		#! (new_av, th_attrs) = freshAttrVar (makeIdent (attr_var_name+++ /*"_"+++*/ toString index)) th_attrs
		= (TA_Var new_av, [new_av], [], (inc index), th_attrs)
	combine_attributes _ cum_attr index th_attrs
		= (cum_attr, [], [], index, th_attrs)


currySymbolType2 :: !SymbolType !String !*TypeHeaps 
	-> (!SymbolType, !*TypeHeaps)
currySymbolType2  st attr_var_name th
	#! (atype, avs, ais, th) = currySymbolType1 st attr_var_name th
	#! st = { st 
		& st_args = []
		, st_arity = 0
		, st_result = atype
		, st_attr_env = st.st_attr_env ++ ais
		, st_attr_vars = st.st_attr_vars ++ avs
		}
	= (st, th)

buildCurriedType :: ![AType] !AType !TypeAttribute ![AttrInequality] ![AttributeVar] !String !Int !*AttrVarHeap 
	-> (!AType, ![AttrInequality], ![AttributeVar], !Int, !*AttrVarHeap)
buildCurriedType [] type cum_attr attr_env attr_vars attr_var_name attr_store th_attrs 
	= (type, attr_env, attr_vars, attr_store, th_attrs)
buildCurriedType [at=:{at_attribute}] type cum_attr attr_env attr_vars attr_var_name attr_store th_attrs
	# atype = {at_annotation = AN_None, at_attribute = cum_attr , at_type = at --> type }
	= (atype, attr_env, attr_vars, attr_store, th_attrs)
buildCurriedType [at=:{at_attribute}:ats] type cum_attr attr_env attr_vars attr_var_name attr_store th_attrs
	# (next_cum_attr, new_attr_env, attr_vars, attr_store, th_attrs) = combine_attributes at_attribute cum_attr attr_env attr_vars attr_store th_attrs
	  (res_type, attr_env, attr_vars, attr_store, th_attrs) = buildCurriedType ats type next_cum_attr attr_env attr_vars attr_var_name attr_store th_attrs
	# atype = {at_annotation = AN_None, at_attribute = cum_attr , at_type = at --> res_type }  
	= (atype, attr_env, attr_vars, attr_store, th_attrs)
where
	combine_attributes TA_Unique cum_attr attr_env attr_vars attr_store th_attrs
		= (TA_Unique, attr_env, attr_vars, attr_store, th_attrs)
	combine_attributes (TA_Var attr_var) (TA_Var cum_attr_var) attr_env attr_vars attr_store th_attrs
		#! (new_attr_var, th_attrs) 
			= freshAttrVar (makeIdent (attr_var_name +++ toString attr_store)) th_attrs	
		# attr_env = 
			[	{ ai_demanded = cum_attr_var,ai_offered = new_attr_var }
			, 	{ ai_demanded = attr_var, ai_offered = new_attr_var }
			: 	attr_env
			]
		= (	TA_Var new_attr_var, attr_env, [new_attr_var:attr_vars], inc attr_store, th_attrs)
	combine_attributes (TA_Var _) cum_attr attr_env attr_vars attr_store th_attrs
		= (cum_attr, attr_env, attr_vars, attr_store, th_attrs)
	combine_attributes _ (TA_Var cum_attr_var) attr_env attr_vars attr_store th_attrs
		#! (new_attr_var, th_attrs) 
			= freshAttrVar (makeIdent (attr_var_name +++ toString attr_store)) th_attrs		
		# attr_env = [	{ ai_demanded = cum_attr_var,ai_offered = new_attr_var }: attr_env]
		= (	TA_Var new_attr_var, attr_env, [new_attr_var:attr_vars], inc attr_store, th_attrs)
	combine_attributes _ cum_attr attr_env attr_vars attr_store th_attrs
		= (cum_attr, attr_env, attr_vars, attr_store, th_attrs)

currySymbolType3 :: !SymbolType !String !*TypeHeaps 
	-> (!SymbolType, !*TypeHeaps)
currySymbolType3  st=:{st_args, st_result, st_attr_env, st_attr_vars} attr_var_name th=:{th_attrs}
	
	#! (cum_attr_var, th_attrs) = freshAttrVar (makeIdent (attr_var_name +++ "0")) th_attrs
	
	#! attr_env = foldSt (build_attr_env cum_attr_var) st_args st_attr_env
				
	#! (atype, attr_env, attr_vars, attr_store, th_attrs) 
		= buildCurriedType st_args st_result (TA_Var cum_attr_var) attr_env st_attr_vars attr_var_name 1 th_attrs

	# curried_st = 
		{ st 
		& st_args = []
		, st_arity = 0
		, st_result = atype
		, st_attr_env = attr_env
		, st_attr_vars = [cum_attr_var:attr_vars]
		}
	= (curried_st, {th & th_attrs = th_attrs})	
		//---> ("currySymbolType3", st, curried_st)
where
	
	build_attr_env cum_attr_var {at_attribute=(TA_Var attr_var)} attr_env
		= [{ ai_demanded = attr_var, ai_offered = cum_attr_var } : attr_env ]
	build_attr_env cum_attr_var _ attr_env
		= attr_env


currySymbolType4 :: !SymbolType !String !*TypeHeaps 
	-> (!SymbolType, !*TypeHeaps)
currySymbolType4  st=:{st_args, st_result, st_attr_env, st_attr_vars} attr_var_name th=:{th_attrs}
	
	#! (atype, attr_env, attr_vars, attr_store, th_attrs) 
		= buildCurriedType st_args st_result TA_Multi st_attr_env st_attr_vars attr_var_name 1 th_attrs

	# curried_st = 
		{ st 
		& st_args = []
		, st_arity = 0
		, st_result = atype
		, st_attr_env = attr_env
		, st_attr_vars = attr_vars
		}
	= (curried_st, {th & th_attrs = th_attrs})	
		//---> ("currySymbolType4", st, curried_st)

				
// specialize generic (kind-indexed) type for a kind
specializeGenericType :: !GenericDef !TypeKind !*TypeHeaps -> (!SymbolType, ![ATypeVar], ![AttributeVar], !*TypeHeaps) 
specializeGenericType generic_def=:{gen_name,gen_type} kind th

	//#! th = th ---> ("specializeSymbolType", kind, gen_type.gt_type)

	#! (gen_type, th) = freshGenericType gen_type th
	
	#! (agvs, gavs, th) = collect_gtv_attrs gen_type th
	
	#! (st, _, th) = build_symbol_type gen_type.gt_type agvs kind "" 1 th

	#! st = 
		{ st 
		& st_vars = removeDup st.st_vars
		, st_attr_vars = removeDup st.st_attr_vars
		, st_attr_env = removeDup st.st_attr_env 
		, st_context = removeDup st.st_context
		}
			
	# th = clearSymbolType st th
	
	= (st, agvs, gavs, th)
		//---> ("specializeGenericType result", kind, st)
where

	// collect generic variables and withe attributes 
	// and generic attribute variables 
	collect_gtv_attrs :: GenericType !*TypeHeaps -> !(![ATypeVar], ![AttributeVar], !*TypeHeaps)
	collect_gtv_attrs {gt_type, gt_vars} th
		#! th = clearSymbolType gt_type th		
		#! th = setTypeVarAttrs gt_type th		
		#! (attributed_vars, (avs, th)) = mapSt get_attr gt_vars ([], th)
		= (attributed_vars, avs, th)
	where
		get_attr tv=:{tv_info_ptr} (avs, th=:{th_vars})
			#! (TVI_Attribute attr, th_vars) = readPtr tv_info_ptr th_vars
			#! avs = case attr of 
				(TA_Var av) -> [av:avs]
				_			-> avs
			#! th = {th & th_vars = th_vars}
			= (	{atv_attribute=attr, atv_variable=tv, atv_annotation=AN_None},
				(avs, th))

			 
	build_symbol_type :: SymbolType ![ATypeVar] !TypeKind !String !Int !*TypeHeaps 
		-> !(!SymbolType, ![ATypeVar], !*TypeHeaps)
	build_symbol_type st agvs KindConst postfix order th	
		#! st = { st & st_vars = [atv_variable \\ {atv_variable}<- agvs] ++ st.st_vars } 		
		= (st, [], th)
			//---> ("build_symbol_type KindConst", st, order)

	build_symbol_type st agvs (KindArrow kinds) postfix order th

		| order > 2
			= abort "kinds of order higher then 2 are not supported"

		//#! th = th ---> ("build_symbol_type for st", (KindArrow kinds, order, postfix), agvs, st)

		#! gvs = [atv_variable \\ {atv_variable} <- agvs]
		#! gavs = [av \\ {atv_attribute=TA_Var av} <- agvs]

		#! arity = length kinds
		
		// build lifting argumnents
		#! (args, th) = mapSt (build_arg agvs st postfix order) (zip2 kinds [1..arity]) th 
		#! (curry_sts, atvss) = unzip args

		#! th = clearSymbolType st th
		#! th = foldSt build_gv_subst (zip2 gvs (transpose atvss)) th 
		#! th = foldSt subst_av_for_self (st.st_attr_vars ++ gavs) th
				 	
		#! (new_st, th) = substituteInSymbolType st th
		#! th = clearSymbolType st th
		#! th = clearSymbolType new_st th
		
		#! new_st = 
			{ new_st 
			& st_vars = 
				foldr (++) (new_st.st_vars ++ gvs) [st_vars \\ {st_vars} <- curry_sts]
			, st_attr_vars = 
				foldr (++) (new_st.st_attr_vars ++ gavs) [st_attr_vars \\ {st_attr_vars} <- curry_sts]
			//, st_attr_env = 
			//	foldr (++) new_st.st_attr_env [st_attr_env \\ {st_attr_env} <- curry_sts]
			, st_args = 
				[st_result \\ {st_result} <- curry_sts] ++ new_st.st_args
			, st_arity = new_st.st_arity + arity	
			, st_context = foldr (++) new_st.st_context [st_context \\ {st_context} <- curry_sts] 			
			} 		
		= (new_st, flatten atvss, th)
			//---> ("build_symbol_type new st", (KindArrow kinds, order), new_st)
		where
			build_gv_subst (gv=:{tv_info_ptr}, atvs) th=:{th_vars}
				#! type_args = [ makeAType (TV atv_variable) atv_attribute \\ {atv_variable, atv_attribute} <- atvs]
				#! type = (CV gv) :@: type_args
				#! th_vars = th_vars <:= (tv_info_ptr, TVI_Type type)			
				= {th & th_vars = th_vars}

	build_arg :: ![ATypeVar] !SymbolType !String !Int !(!TypeKind, !Int) !*TypeHeaps
		-> !(!(!SymbolType, ![ATypeVar]), !*TypeHeaps)
	build_arg agvs st postfix order (kind, arg_num) th
		
		//#! th = th ---> ("build_arg for st", (kind, arg_num, order), st)  
	
		#! postfix = toString arg_num
		#! gavs = [av \\ {atv_attribute=TA_Var av} <- agvs]

		#! th = clearSymbolType st th
		#! th = foldSt subst_av_for_self (st.st_attr_vars ++ gavs) th
		#! (fresh_atvs, th) = mapSt (fresh_agv postfix) agvs th
		#! (fresh_st, th) = substituteInSymbolType st th
		#! th = clearSymbolType st th
		#! th = clearSymbolType fresh_st th
		
		#! fresh_avs = [av \\ {atv_attribute=TA_Var av} <- fresh_atvs]
		#! fresh_st = 
			{ fresh_st 
			& st_attr_vars = fresh_st.st_attr_vars ++ fresh_avs	
			}	
				
		#! (fresh_st, forall_atvs, th) = build_symbol_type fresh_st fresh_atvs kind postfix (inc order) th		
	
		//#! (curry_st, th)	= currySymbolType2 fresh_st ("cur" +++ postfix) th 	
		#! (curry_st, th)	= currySymbolType4 fresh_st ("cur" +++ toString order +++ postfix) th 	
								
		#! curry_st = case forall_atvs of
			[] 	-> curry_st
			forall_atvs 
				# (atype=:{at_type}) = curry_st.st_result 
				-> 
			 	{ curry_st 
				& st_result = {atype & at_type = TFA forall_atvs at_type}
				, st_attr_vars = curry_st.st_attr_vars -- [av \\ {atv_attribute=TA_Var av} <- forall_atvs]
				, st_vars = curry_st.st_vars -- [atv_variable \\ {atv_variable} <- forall_atvs]
				} 					
		
		= ((curry_st, fresh_atvs), th)
			//---> ("build_arg curry_st", (kind, arg_num, order), curry_st) 
 
	where
		
		fresh_agv postfix agv=:{atv_attribute, atv_variable} th=:{th_attrs, th_vars}
			#! (tv, th_vars) = fresh_tv atv_variable postfix th_vars
			#! (attr, th_attrs) = fresh_attr atv_attribute postfix th_attrs
			= ({agv & atv_attribute = attr, atv_variable = tv}, {th & th_vars = th_vars, th_attrs = th_attrs})					
		where
			fresh_tv {tv_name, tv_info_ptr} postfix th_vars
				#! name = makeIdent (tv_name.id_name +++ postfix)
				#! (tv, th_vars) = freshTypeVar name th_vars 					
				#! th_vars = th_vars <:= (tv_info_ptr, TVI_Type (TV tv))	
				= (tv, th_vars)
				
			fresh_attr (TA_Unique) postfix th_attrs = (TA_Unique, th_attrs)	
			fresh_attr (TA_Multi) postfix th_attrs = (TA_Multi, th_attrs)	
			fresh_attr (TA_Var av=:{av_name, av_info_ptr}) postfix th_attrs
				#! (fresh_av, th_attrs) = freshAttrVar (makeIdent (av_name.id_name+++postfix)) th_attrs
				#! attr = TA_Var fresh_av					
				#! th_attrs = th_attrs <:= (av_info_ptr, AVI_Attr attr)
				= (attr, th_attrs)
					
	subst_av_for_self av=:{av_info_ptr} th=:{th_attrs}	
		= {th & th_attrs = th_attrs <:= (av_info_ptr, AVI_Attr (TA_Var av))}

buildMemberType2 :: !GenericDef !TypeKind !TypeVar !*TypeHeaps !*VarHeap -> (!SymbolType, ![TypeContext], !*TypeHeaps, !*VarHeap)
buildMemberType2 generic_def=:{gen_name,gen_type} kind class_var th var_heap

	# (st, agvs, gavs, th) = specializeGenericType generic_def kind th
	
	#! (st, th) = replace_gvs_with_class_var st agvs class_var kind th
	#! (st, th) = adjust_gavs st gavs kind th
	#! st = 
		{ st 
		& st_vars = removeDup st.st_vars
		, st_attr_vars = removeDup st.st_attr_vars
		, st_attr_env = removeDup st.st_attr_env 
		, st_context = removeDup st.st_context
		}
	#! (st_context, class_contexts, var_heap) = adjust_contexts st.st_context class_var kind var_heap
	#! st = {st & st_context = st_context} 
		
	# th = clearSymbolType st th
	
	= (st, class_contexts, th, var_heap)
where		
	replace_gvs_with_class_var :: !SymbolType ![ATypeVar] !TypeVar !TypeKind !*TypeHeaps 
		-> (!SymbolType, !*TypeHeaps) 
	replace_gvs_with_class_var st agvs class_var kind th
	
		#! gvs = [atv_variable \\ {atv_variable} <- agvs]
	
		#! th = clearSymbolType st th
		#! th = foldSt subst_av_for_self st.st_attr_vars th	
		#! th = foldSt (build_subst class_var) gvs th 
			with
				build_subst class_var {tv_info_ptr} th=:{th_vars}
					#! th_vars = th_vars <:= (tv_info_ptr, TVI_Type (TV class_var))
					= {th & th_vars = th_vars}		
		#! (new_st, th) = substituteInSymbolType st th
		#! (st_vars, th) = remove_gvs new_st.st_vars th
			with
				remove_gvs [] th = ([], th)
				remove_gvs [tv:tvs] th=:{th_vars}
					#! (tv_info, th_vars) = readPtr tv.tv_info_ptr th_vars
					#! (tvs, th) = remove_gvs tvs {th & th_vars = th_vars} 
					#! tvs = case tv_info of
						TVI_Empty 		-> [tv:tvs]
						(TVI_Type _)	-> tvs
						_ 				->	(abort "wrong TVI_?") ---> ("remove_gvs ", tv)	
					= (tvs, th)
		#! new_st = { new_st & st_vars = [class_var : st_vars] }
		#! th = clearSymbolType st th
		#! th = clearSymbolType new_st th
		= (new_st, th)
		
	adjust_gavs st [gav:gavs] KindConst th
	
		#! th = clearSymbolType st th
		#! th = foldSt subst_av_for_self st.st_attr_vars th	
		#! th = foldSt (subst_for_av gav) gavs th
			with 
				subst_for_av gav {av_info_ptr} th=:{th_attrs}
					= {th & th_attrs = th_attrs <:= (av_info_ptr, AVI_Attr (TA_Var gav))}
		#! (new_st, th) = substituteInSymbolType st th
		#! th = clearSymbolType st th
		#! th = clearSymbolType new_st th

		#! th = foldSt mark_av gavs th
			with 
				mark_av {av_info_ptr} th=:{th_attrs} 
					= {th & th_attrs = th_attrs <:= (av_info_ptr, AVI_Used)}
		#! (st_attr_vars, th) = remove_avs new_st.st_attr_vars th
			with
				remove_avs [] th = ([], th)
				remove_avs [av:avs] th=:{th_attrs}
					#! (av_info, th_attrs) = readPtr av.av_info_ptr th_attrs
					#! (avs, th) = remove_avs avs {th & th_attrs = th_attrs }
					#! avs = case av_info of
						AVI_Empty		-> [av:avs]
						AVI_Used 		-> avs	
						_				-> (abort "wrong AVI_") ---> ("remove_avs ", av)						  
					= (avs, th)

		#! th = clearSymbolType new_st th
				
		= (new_st, th)
	adjust_gavs st gavs kind th
		= (st, th)
	
	adjust_contexts contexts class_var kind var_heap
		#! (contexts, class_contexts, var_heap) = split_contexts contexts var_heap		
		#! class_contexs = case kind of
			KindConst 	-> class_contexts 
		 	_			-> [] // just drop them
		= (contexts, class_contexts, var_heap)	 
	where
	
		// split contexts into involving and not invloving class variables
		split_contexts [] var_heap
			= ([], [], var_heap)
		split_contexts [context:contexts] var_heap
			#! (contexts1, class_contexts1, var_heap) = split_context context var_heap
			#! (contexts2, class_contexts2, var_heap) = split_contexts contexts var_heap
			= (contexts1 ++ contexts2, class_contexts1 ++ class_contexts2, var_heap) 
		split_context tc=:{tc_class, tc_types, tc_var} var_heap
			#! (types, class_types) = split_types tc_types
			#! (tc_var, var_heap) = case isNilPtr tc_var of
				True  -> newPtr VI_Empty var_heap
				False -> (tc_var, var_heap)	 
			#! tc = {tc & tc_var = tc_var} 	
			| isEmpty types
				= ([], [tc], var_heap)
			| isEmpty class_types	 
			  	= ([tc], [], var_heap)
			| otherwise
				#! tc = {tc & tc_types = types}
				#! (tc_var, var_heap) = newPtr VI_Empty var_heap
				#! class_tc = {tc & tc_types = class_types, tc_var = tc_var} 	
			  	= ([tc], [class_tc], var_heap)
			   	
		split_types []
			= ([], [])	
		split_types [type:types]
			# (types1, class_types1) = split_type type
			# (types2, class_types2) = split_types types
			= (types1 ++ types2, class_types1 ++ class_types2)
		split_type type		
			#! contains_class_var = performOnTypeVars (\attr tv ok -> ok || tv == class_var) type False
			| contains_class_var		
				= ([], [type])	
				= ([type], [])	

	subst_av_for_self av=:{av_info_ptr} th=:{th_attrs}	
		= {th & th_attrs = th_attrs <:= (av_info_ptr, AVI_Attr (TA_Var av))}
	

buildMemberType :: !GenericDef !TypeKind !TypeVar !*TypeHeaps -> (!SymbolType, !*TypeHeaps)
buildMemberType generic_def=:{gen_name,gen_type} kind class_var th 
//	= abort "generics; buildMemberType"

	#! (gen_type, th) = freshGenericType gen_type th

	// Collect attributes of generic variables. 
	// The attributes are instantiated along with the variables.
	#! (gen_vars_with_attrs, generic_avs, th) = collect_generic_var_attrs gen_type th
	
	// build additional arguments that emerge due to lifting
	#! (new_args, atvss, new_avs, attr_inequalities, th) = build_args gen_type gen_vars_with_attrs kind th

	#! atvss = case atvss of 
		[] 		-> repeatn gen_type.gt_arity []
		atvss	-> transpose atvss
	
	// substitute generic variables for types
	// all non-generic variables must be left intact
	#! th = clearSymbolType gen_type.gt_type th	
 	#! th = build_generic_var_substs gen_vars_with_attrs class_var atvss kind th
//	#! th = build_attr_var_substs gen_type.gt_type.st_attr_vars generic_avs kind th
	#! (avs1, th) = build_attr_var_substs gen_type.gt_type.st_attr_vars generic_avs kind th
	#! (st, th) = substituteInSymbolType gen_type.gt_type th

	// update generated fields
	#! instantiation_tvs	 = [atv_variable \\ {atv_variable} <- (flatten atvss)]
	#! st = { st &
			st_vars 		= [class_var : instantiation_tvs ++ st.st_vars]
		,	st_arity 		= (length new_args) + st.st_arity
		,	st_args 		= new_args ++ st.st_args  
//		, 	st_attr_vars 	= st.st_attr_vars ++ new_avs
		, 	st_attr_vars 	= avs1 ++ new_avs
		,	st_attr_env 	= st.st_attr_env ++ attr_inequalities
		}
	
	= (st, th)
		//---> ("member type", gen_name, kind, st)

where

	collect_generic_var_attrs {gt_type, gt_vars} th
		#! th = clearSymbolType gt_type th		
		#! th = setTypeVarAttrs gt_type th
		
		#! (attributed_vars, (avs, th)) = mapSt get_attr gt_vars ([], th)
			with 
				get_attr tv=:{tv_info_ptr} (avs, th=:{th_vars})
					#! (TVI_Attribute attr, th_vars) = readPtr tv_info_ptr th_vars
					#! avs = (collect_attr_var attr) ++ avs
					#! th = {th & th_vars = th_vars}
					= (	{atv_attribute=attr, atv_variable=tv, atv_annotation=AN_None},
						(avs, th))
				collect_attr_var (TA_Var av)	= [av]
				collect_attr_var _ 				= []
					 
		= (attributed_vars, avs, th)

/*
	build_attr_var_substs avs generic_avs kind th
 		= foldSt build_subst (determine_attr_vars kind avs generic_avs)  th
	where
		determine_attr_vars KindConst avs generic_avs
			= removeMembers avs generic_avs 
		determine_attr_vars kind avs generic_avs
			= avs
		build_subst av=:{av_info_ptr} th=:{th_attrs}
			= { th & th_attrs = th_attrs <:= (av_info_ptr, AVI_Attr (TA_Var av))}
*/
	build_attr_var_substs avs [] KindConst th
		= (avs, foldSt build_attr_var_subst avs th)
	build_attr_var_substs avs generic_avs KindConst th		
		# nongeneric_avs = avs -- generic_avs
		
		# {th_attrs} = th
		# (gen_av, th_attrs) = freshAttrVar (makeIdent "gav") th_attrs 
		# new_generic_avs = repeatn (length generic_avs) gen_av
		
		// substitute generic var attributes with single attr var
		# th = foldSt build_subst generic_avs {th & th_attrs = th_attrs}
			with
				build_subst {av_info_ptr} th=:{th_attrs}
					= { th & th_attrs = th_attrs <:= (av_info_ptr, AVI_Attr (TA_Var gen_av))}
					
		# th = foldSt build_attr_var_subst nongeneric_avs th		
		= (nongeneric_avs ++ new_generic_avs, th)
	build_attr_var_substs avs generic_avs kind th	
		= (avs, foldSt build_attr_var_subst avs th)
	build_attr_var_subst av=:{av_info_ptr} th=:{th_attrs}
			= { th & th_attrs = th_attrs <:= (av_info_ptr, AVI_Attr (TA_Var av))}
						 
	build_generic_var_substs [] class_var [] kind th
		= th
	build_generic_var_substs [gv:gvs] class_var [tvs:tvss] kind th
		# th = build_generic_var_subst gv class_var tvs kind th
		# th = build_generic_var_substs gvs class_var tvss kind th
		= th	

	build_generic_var_subst {atv_variable={tv_info_ptr}} class_var [] KindConst th=:{th_vars}
		#! th_vars = th_vars <:= (tv_info_ptr, TVI_Type (TV class_var))
		= {th & th_vars = th_vars}		
	build_generic_var_subst {atv_variable={tv_info_ptr}} class_var atvs (KindArrow ks) th=:{th_vars}
		#! arity = length ks
		| arity <> length atvs = abort "sanity check: invalid number of type variables"

		#! type_args = [ makeAType (TV atv_variable) atv_attribute \\ {atv_variable, atv_attribute} <- atvs]
		#! type = (CV class_var) :@: type_args
		#! th_vars = th_vars <:= (tv_info_ptr, TVI_Type type)			
		= {th & th_vars = th_vars}
			
	build_args gen_type agvs KindConst th
		= ([], [], [], [], th)
	build_args gen_type agvs (KindArrow ks) th	
		#! arity = length ks
		#! postfixes = [/*"_" +++*/ toString i \\ i <- [1..arity]]
		#! (ats, atvss, new_avs, ais, th) = build_generic_args gen_type agvs postfixes th
		= (ats, atvss, new_avs, ais, th)
	
 	build_generic_args :: !GenericType ![ATypeVar] ![String] !*TypeHeaps 
 		-> (![AType], ![[ATypeVar]], ![AttributeVar], ![AttrInequality], !*TypeHeaps)
	build_generic_args gen_type agvs [] th 
		= ([], [], [], [], th)	
	build_generic_args gen_type agvs [postfix:postfixes] th
		#! (at, atvs, new_avs, ais, th) = build_generic_arg gen_type agvs postfix th
		#! (ats, atvss, new_avs1, ais1, th) = build_generic_args gen_type agvs postfixes th
		= ([at:ats], [atvs:atvss], new_avs ++ new_avs1, ais ++ ais1, th)  	
 	
 	build_generic_arg :: !GenericType ![ATypeVar] !String !*TypeHeaps 
 		-> (!AType, ![ATypeVar], ![AttributeVar], ![AttrInequality], !*TypeHeaps)
	build_generic_arg {gt_type, gt_vars, gt_arity} agvs postfix th=:{th_vars, th_attrs}
		#! th = clearSymbolType gt_type th
		#! {th_vars, th_attrs} = th
		
		// replace all generic variables with fresh variables
		#! (tvs, th_vars) = mapSt build_subst gt_vars th_vars			
			with
				build_subst gv=:{tv_name,tv_info_ptr} th_vars					
					#! name = makeIdent (tv_name.id_name +++ postfix)
					#! (tv, th_vars) = freshTypeVar name th_vars 					
					#! th_vars = th_vars <:= (tv_info_ptr, TVI_Type (TV tv))	
					= (tv, th_vars)
		
		// leave all non-generic attribute variables intact
		#! th_attrs = foldSt build_subst gt_type.st_attr_vars th_attrs
			with
				build_subst av=:{av_info_ptr} th_attrs
					= th_attrs <:= (av_info_ptr, AVI_Attr (TA_Var av))

		// all attribute variables at generic arguments must be taken afresh
		#! (attrs, (instantiated_avs, th_attrs)) = mapSt build_subst agvs ([], th_attrs)
			with
				build_subst {atv_attribute=TA_Unique} st = (TA_Unique, st)
				build_subst {atv_attribute=TA_Multi} st = (TA_Multi, st)
				build_subst {atv_attribute=TA_Var {av_name, av_info_ptr}} (avs, th_attrs)
					#! (fresh_av, th_attrs) = freshAttrVar (makeIdent (av_name.id_name+++postfix)) th_attrs
					#! attr = TA_Var fresh_av					
					#! th_attrs = th_attrs <:= (av_info_ptr, AVI_Attr attr)
					= (attr, ([fresh_av:avs], th_attrs))
		#! (st, th) = substituteInSymbolType gt_type {th & th_vars = th_vars, th_attrs = th_attrs}

		#! atvs = [{atv_attribute=attr, atv_variable=tv, atv_annotation=AN_None} \\
			attr 	<- attrs &
			tv 		<- tvs]
		
		#! (at, curry_avs, ais, th) = currySymbolType1 st ("arg"+++postfix) th		
		#! th = clearSymbolType gt_type th
		= (at, atvs, instantiated_avs ++ curry_avs, ais, th)

buildGenericRepType :: !Index !Index !*GenericState
	-> (AType, !*GenericState)
buildGenericRepType module_index td_index gs=:{gs_modules, gs_predefs, gs_error}
	# (type_def=:{td_name}, gs_modules) = getTypeDef module_index td_index gs_modules 
	# (common_defs, gs_modules) = gs_modules ! [module_index]		
	# (atype, gs_error) = build_type module_index type_def gs_predefs common_defs gs_error	
	= (atype, {gs & gs_modules = gs_modules, gs_error = gs_error})
where		 
	build_type td_module {td_rhs=(AlgType alts)} predefs common_defs error
		= (build_sum alts predefs common_defs.com_cons_defs, error)
	where
		build_sum :: ![DefinedSymbol] !PredefinedSymbols !{#ConsDef} -> !AType
		build_sum [] predefs cons_defs = abort "no alternatives in typedef"
		build_sum [{ds_index}] predefs cons_defs
			# cons_args = cons_defs.[ds_index].cons_type.st_args
			# atype = buildProductType cons_args predefs
			= case supportCons of
				True -> buildATypeCONS atype predefs
				False -> atype 
		build_sum alts predefs cons_defs 
			# (l,r) = splitAt ((length alts) / 2) alts 
			= buildATypeEITHER (build_sum l predefs cons_defs) (build_sum r predefs cons_defs) predefs
			
	build_type td_module {td_rhs=(RecordType {rt_constructor={ds_index}})} predefs common_defs error
		#! {cons_type={st_args}} = common_defs . com_cons_defs . [ds_index]
		#! atype = buildProductType st_args predefs
		#! atype = case supportCons of
					True -> buildATypeCONS atype predefs
					False -> atype 
		= (atype, error)
	
	build_type td_module {td_rhs=(SynType type)} predefs common_defs error
		= (type, error) // is that correct ???

	build_type 
			td_module td=:{td_rhs=(AbstractType _), td_name, td_arity, td_args, td_pos} 
			predefs common_defs error
		#! error = checkErrorWithIdentPos (newPosition td_name td_pos) "cannot build generic type repesentation for an abstract type" error
		= (makeAType TE TA_None, error)
			
buildIsoRecord :: !DefinedSymbol !Int !DefinedSymbol !DefinedSymbol !*GenericState
	-> (!FunDef, !*GenericState)
buildIsoRecord 
		def_sym group_index from_fun to_fun 
		gs=:{gs_heaps, gs_main_dcl_module_n, gs_predefs}
	# (from_expr, gs_heaps) 	= buildFunApp gs_main_dcl_module_n from_fun [] gs_heaps
	# (to_expr, gs_heaps) 		= buildFunApp gs_main_dcl_module_n to_fun [] gs_heaps	
	# (iso_expr, gs_heaps) 		= buildISO to_expr from_expr gs_predefs gs_heaps
	# fun_def = makeFunction def_sym group_index [] iso_expr No [] gs_main_dcl_module_n	NoPos				
	= (fun_def, {gs & gs_heaps = gs_heaps})

// convert a type to ot's generic representation
buildIsoTo :: !DefinedSymbol !Int !Int !CheckedTypeDef ![DefinedSymbol] !*GenericState
	-> (!FunDef, !*GenericState)
buildIsoTo 
		def_sym group_index type_def_mod 
		type_def=:{td_rhs, td_name, td_index, td_pos} 
		cons_infos
		gs=:{gs_heaps,gs_main_dcl_module_n}
	# (arg_expr, arg_var, gs_heaps) = buildVarExpr "x" gs_heaps 
	# (body_expr, free_vars, gs=:{gs_error}) = 
		build_body type_def_mod td_index td_rhs cons_infos arg_expr {gs&gs_heaps = gs_heaps}	
	| not gs_error.ea_ok
		#! fun_def = makeFunction {def_sym&ds_arity=0} NoIndex [] EE No [] gs_main_dcl_module_n NoPos
		= (fun_def, {gs & gs_error = gs_error})	
	# fun_def = makeFunction def_sym group_index [arg_var] body_expr No free_vars gs_main_dcl_module_n NoPos	
	= (fun_def, {gs & gs_error = gs_error})
		//---> fun_def
where
	get_cons_infos module_index td_index gs=:{gs_gtd_infos}
		# (GTDI_Generic {gtr_cons_infos}, gs_gtd_infos) = gs_gtd_infos ! [module_index, td_index] 							 
 		= (gtr_cons_infos, {gs & gs_gtd_infos = gs_gtd_infos})

	build_body :: !Int !Int !TypeRhs ![DefinedSymbol] !Expression !*GenericState 
		-> (!Expression, ![FreeVar], !*GenericState)
 	build_body type_def_mod type_def_index (AlgType def_symbols) cons_infos arg_expr gs
		= build_body1 type_def_mod type_def_index def_symbols cons_infos arg_expr gs
	
	build_body type_def_mod type_def_index (RecordType {rt_constructor}) cons_infos arg_expr gs		
		= build_body1 type_def_mod type_def_index [rt_constructor] cons_infos arg_expr gs

	build_body type_def_mod type_def_index (AbstractType _) cons_infos arg_expr gs=:{gs_error}
		#! gs_error = checkErrorWithIdentPos (newPosition td_name td_pos) "cannot build isomorphisms for an abstract type" gs_error
		= (EE, [], {gs & gs_error = gs_error})
	build_body type_def_mod type_def_index (SynType _) cons_infos arg_expr gs=:{gs_error}
		#! gs_error = checkErrorWithIdentPos (newPosition td_name td_pos) "cannot build isomorphisms for a synonym type" gs_error
		= (EE, [], {gs & gs_error = gs_error})
	
	build_body1 type_def_mod type_def_index cons_def_syms cons_infos arg_expr gs
		# (case_alts, free_vars, gs=:{gs_heaps}) = 
			build_alts 0 (length cons_def_syms) type_def_mod cons_def_syms cons_infos gs
		# case_patterns = AlgebraicPatterns {glob_module = type_def_mod, glob_object = type_def_index} case_alts
		# (case_expr, gs_heaps) = buildCaseExpr arg_expr case_patterns gs_heaps
		= (case_expr, free_vars, {gs & gs_heaps = gs_heaps})	
			//---> (free_vars, case_expr)	
				
	build_alts :: !Int !Int !Int ![DefinedSymbol] ![DefinedSymbol] !*GenericState 
		-> ([AlgebraicPattern], [FreeVar], !*GenericState)
	build_alts i n type_def_mod [] [] gs = ([], [], gs) 
	build_alts i n type_def_mod [cons_def_sym:cons_def_syms] cons_infos gs	
		#! (cons_info, cons_infos) = case supportCons of
			True -> (hd cons_infos, tl cons_infos)
			False -> (EmptyDefinedSymbol, [])	
		#! (alt, fvs, gs) = build_alt i n type_def_mod cons_def_sym cons_info gs
		#! (alts, free_vars, gs) =  build_alts (i+1) n type_def_mod cons_def_syms cons_infos gs 		
		= ([alt:alts], fvs ++ free_vars, gs)

	build_alt :: !Int !Int !Int !DefinedSymbol !DefinedSymbol !*GenericState 
		-> (AlgebraicPattern, [FreeVar], !*GenericState)
	build_alt 
			i n type_def_mod def_symbol=:{ds_ident, ds_arity} cons_info 
			gs=:{gs_heaps, gs_predefs, gs_main_dcl_module_n}		
		#! names = ["x" +++ toString (i+1) +++ toString k \\ k <- [1..ds_arity]]
		#! (var_exprs, vars, gs_heaps) = buildVarExprs names gs_heaps 
		#! (expr, gs_heaps) = build_prod var_exprs gs_predefs gs_heaps		
		#! (expr, gs_heaps) = case supportCons of
			True 
				//# (cons_info_expr, gs_heaps) = buildUndefFunApp [] gs_predefs gs_heaps
				# (cons_info_expr, gs_heaps) = buildFunApp gs_main_dcl_module_n cons_info [] gs_heaps 	
				-> buildCONS cons_info_expr expr gs_predefs gs_heaps
			False 
				-> (expr, gs_heaps)				
		#! (expr, gs_heaps) = build_sum i n expr gs_predefs gs_heaps
				
		#! alg_pattern = {
			ap_symbol = {glob_module = type_def_mod, glob_object = def_symbol},
			ap_vars = vars,
			ap_expr = expr,
			ap_position = NoPos
			}
		= (alg_pattern, vars, {gs & gs_heaps = gs_heaps})

	build_sum :: !Int !Int !Expression !PredefinedSymbols !*Heaps -> (!Expression, !*Heaps)
	build_sum i n expr predefs heaps
		| n == 0 	= abort "build sum of zero elements\n"
		| i >= n	= abort "error building sum"
		| n == 1 	= (expr, heaps)
		| i < (n/2) 
			# (expr, heaps) = build_sum i (n/2) expr predefs heaps
			= buildLEFT expr predefs heaps
		| otherwise
			# (expr, heaps) = build_sum (i - (n/2)) (n - (n/2)) expr predefs heaps
			= buildRIGHT expr predefs heaps

	build_prod :: ![Expression] !PredefinedSymbols !*Heaps -> (!Expression, !*Heaps)
	build_prod [] predefs heaps = buildUNIT predefs heaps 
	build_prod [expr] predefs heaps = (expr, heaps)
	build_prod exprs predefs heaps
		# (lexprs, rexprs) = splitAt ((length exprs)/2) exprs  
		# (lexpr, heaps) = build_prod lexprs predefs heaps
		# (rexpr, heaps) = build_prod rexprs predefs heaps
		= buildPAIR lexpr rexpr predefs heaps

// convert from generic representation to type
buildIsoFrom :: !DefinedSymbol !Int !Int !CheckedTypeDef !*GenericState
	-> (!FunDef, !*GenericState)
buildIsoFrom 
		def_sym group_index type_def_mod 
		type_def=:{td_rhs, td_name, td_index, td_pos} 
		gs=:{gs_predefs, gs_heaps, gs_error,gs_main_dcl_module_n}
	#! (body_expr, free_vars, gs_heaps, gs_error) = build_body type_def_mod td_rhs gs_predefs gs_heaps gs_error
	| not gs_error.ea_ok
		#! fun_def = makeFunction {def_sym&ds_arity=0} NoIndex [] EE No [] gs_main_dcl_module_n td_pos
		= (fun_def, {gs & gs_heaps = gs_heaps, gs_error = gs_error} )
	#! fun_def = makeFunction def_sym group_index [hd free_vars] body_expr No (tl free_vars) gs_main_dcl_module_n td_pos
	= (fun_def, {gs & gs_heaps = gs_heaps, gs_error = gs_error} )
		//---> fun_def
where	
	build_body :: !Int !TypeRhs !PredefinedSymbols !*Heaps !*ErrorAdmin
		-> (!Expression, ![FreeVar], !*Heaps, !*ErrorAdmin)
 	build_body type_def_mod (AlgType def_symbols) predefs heaps error
		= build_sum type_def_mod def_symbols predefs heaps error
	build_body type_def_mod (RecordType {rt_constructor}) predefs heaps error				
		= build_sum type_def_mod [rt_constructor] predefs heaps	error
	build_body type_def_mod (AbstractType _) predefs heaps error
		#! error = checkErrorWithIdentPos (newPosition td_name td_pos) "cannot build isomorphisms for an abstract type" error
		= (EE, [], heaps, error)
	build_body type_def_mod (SynType _) predefs heaps error
		#! error = checkErrorWithIdentPos (newPosition td_name td_pos) "cannot build isomorphisms for a synonym type" error
		= (EE, [], heaps, error)

	build_sum :: !Index [DefinedSymbol] !PredefinedSymbols !*Heaps !*ErrorAdmin
		-> (!Expression, ![FreeVar], !*Heaps, !*ErrorAdmin)
	build_sum type_def_mod [] predefs heaps error
		= abort "algebraic type with no constructors!\n"
	build_sum type_def_mod [def_symbol] predefs heaps error
		#! (cons_app_expr, cons_args, heaps) = build_cons_app type_def_mod def_symbol heaps
		#! (alt_expr, free_vars, heaps) = build_prod cons_app_expr cons_args predefs heaps 		
		=	case supportCons of
			True
				#! (var_expr, var, heaps) = buildVarExpr "c" heaps
				#! (info_var, heaps) = buildFreeVar0 "i" heaps
				#! (alt_expr, heaps) = buildCaseCONSExpr var_expr info_var (hd free_vars) alt_expr predefs heaps   
				-> (alt_expr, [var, info_var : free_vars], heaps, error)										
			False
				-> (alt_expr, free_vars, heaps, error)
				
	build_sum type_def_mod def_symbols predefs heaps error
		#! (var_expr, var, heaps) = buildVarExpr "e" heaps
		#! (left_def_syms, right_def_syms) = splitAt ((length def_symbols) /2) def_symbols
	
		#! (left_expr, left_vars, heaps, error) = build_sum type_def_mod left_def_syms predefs heaps error
		#! (right_expr, right_vars, heaps, error) = build_sum type_def_mod right_def_syms predefs heaps error
	
		#! (case_expr, heaps) = 
			buildCaseEITHERExpr var_expr (hd left_vars, left_expr) (hd right_vars, right_expr) predefs heaps
		#! vars = [var : left_vars ++ right_vars]
		= (case_expr, vars, heaps, error)
		
	build_prod :: !Expression ![FreeVar] !PredefinedSymbols !*Heaps
		-> (!Expression, ![FreeVar], !*Heaps)
	build_prod expr [] predefs heaps
		#! (var_expr, var, heaps) = buildVarExpr "x" heaps 
		#! (case_expr, heaps) = buildCaseUNITExpr var_expr expr predefs heaps	
		= (case_expr, [var], heaps)
	build_prod expr [cons_arg_var] predefs heaps
		= (expr, [cons_arg_var], heaps)	
	build_prod expr cons_arg_vars predefs heaps
		#! (var_expr, var, heaps) = buildVarExpr "p" heaps
		#! (left_vars, right_vars) = splitAt ((length cons_arg_vars) /2) cons_arg_vars
		 
		#! (expr, left_vars, heaps) = build_prod expr left_vars predefs heaps
		#! (expr, right_vars, heaps) = build_prod expr right_vars predefs heaps
		
		#! (case_expr, heaps) = buildCasePAIRExpr var_expr (hd left_vars) (hd right_vars) expr predefs heaps
		
		#! vars = [var : left_vars ++ right_vars]	
		= (case_expr, vars, heaps) 
	
	build_cons_app :: !Index !DefinedSymbol !*Heaps 
		-> (!Expression, [FreeVar], !*Heaps)
	build_cons_app cons_mod def_symbol=:{ds_arity} heaps
		#! names = ["x"  +++ toString k \\ k <- [1..ds_arity]]
		#! (var_exprs, vars, heaps) = buildVarExprs names heaps 
		#! (expr, heaps) = buildConsApp cons_mod def_symbol var_exprs heaps
		= (expr, vars, heaps) 

buildIsomapFromTo :: !IsoDirection !DefinedSymbol !Int !Int !Int !*GenericState
	-> (!FunDef, !Index, !*GenericState)
buildIsomapFromTo 
		iso_dir def_sym group_index type_def_mod type_def_index 
		gs=:{gs_heaps, gs_modules,gs_main_dcl_module_n}
	#! (type_def=:{td_name, td_index, td_arity, td_pos}, gs_modules) 
		= getTypeDef type_def_mod type_def_index gs_modules
	#! arg_names = [ "i" +++ toString n \\ n <- [1 .. td_arity]]
	#! (isomap_arg_vars, gs_heaps) = buildFreeVars arg_names gs_heaps 
	#! (arg_expr, arg_var, gs_heaps) = buildVarExpr "x" gs_heaps
	#! gs = {gs & gs_heaps = gs_heaps, gs_modules = gs_modules}
	#! (body_expr, free_vars, gs) = 
		build_body iso_dir type_def_mod td_index type_def arg_expr isomap_arg_vars gs	

	#! (fun_type, gs) = build_type1 iso_dir type_def_mod type_def_index gs
	#! fun_def = makeFunction def_sym group_index (isomap_arg_vars ++ [arg_var]) body_expr (Yes fun_type) free_vars gs_main_dcl_module_n td_pos	
	= (fun_def, def_sym.ds_index, gs)
		//---> ("isomap from/to", td_name, fun_def)
where
	build_body :: !IsoDirection !Int !Int !CheckedTypeDef !Expression ![FreeVar] !*GenericState
		-> (Expression, [FreeVar], !*GenericState)
	build_body iso_dir type_def_mod type_def_index type_def=:{td_rhs=(AlgType def_symbols)} arg_expr isomap_arg_vars gs
		= build_body1 iso_dir type_def_mod type_def_index type_def def_symbols arg_expr isomap_arg_vars gs
		
	build_body iso_dir type_def_mod type_def_index type_def=:{td_rhs=(RecordType {rt_constructor})} arg_expr isomap_arg_vars gs
		= build_body1 iso_dir type_def_mod type_def_index type_def [rt_constructor] arg_expr isomap_arg_vars gs
	
	build_body 
			iso_dir type_def_mod type_def_index 
			type_def=:{td_rhs=(AbstractType _),td_name, td_pos} arg_expr isomap_arg_vars gs=:{gs_error}
		#! gs_error = checkErrorWithIdentPos
				(newPosition td_name td_pos) 
				"cannot build map function for an abstract type" 
				gs_error
		= (EE, [], {gs & gs_error = gs_error})

	build_body 
			iso_dir type_def_mod type_def_index 
			type_def=:{td_rhs=(SynType _), td_name, td_pos} arg_expr isomap_arg_vars gs=:{gs_error}
		#! gs_error = checkErrorWithIdentPos
				(newPosition td_name td_pos) 
				"cannot build map function for a synonym type" 
				gs_error
		= (EE, [], {gs & gs_error = gs_error})

	build_body1 iso_dir type_def_mod type_def_index type_def def_symbols arg_expr isomap_arg_vars gs
		#! (case_alts, free_vars, gs=:{gs_heaps}) = 
			build_alts iso_dir 0 (length def_symbols) type_def_mod def_symbols isomap_arg_vars type_def gs
		#! case_patterns = AlgebraicPatterns {glob_module = type_def_mod, glob_object = type_def_index} case_alts
		#! (case_expr, gs_heaps) = buildCaseExpr arg_expr case_patterns gs_heaps
		= (case_expr, free_vars, {gs & gs_heaps = gs_heaps})

	build_alts :: !IsoDirection !Int !Int !Int ![DefinedSymbol] ![FreeVar] !CheckedTypeDef !*GenericState 
		-> ([AlgebraicPattern], [FreeVar], !*GenericState)
	build_alts iso_dir i n type_def_mod [] arg_vars type_def gs 
		= ([], [], gs) 
	build_alts iso_dir i n type_def_mod [def_symbol:def_symbols] arg_vars type_def gs
		#! (alt, fvs, gs) = build_alt iso_dir i n type_def_mod def_symbol arg_vars type_def gs
		#! (alts, free_vars, gs) = build_alts iso_dir (i+1) n type_def_mod def_symbols arg_vars type_def gs 		
		= ([alt:alts], fvs ++ free_vars, gs)

	build_alt :: !IsoDirection !Int !Int !Int !DefinedSymbol ![FreeVar] !CheckedTypeDef !*GenericState 
		-> (AlgebraicPattern, [FreeVar], !*GenericState)
	build_alt 
			iso_dir i n type_def_mod def_symbol=:{ds_ident, ds_arity, ds_index} 
			fun_arg_vars type_def gs=:{gs_heaps, gs_modules}		
		#! names = ["x" +++ toString (i+1) +++ toString k \\ k <- [1..ds_arity]]
		#! (cons_arg_vars, gs_heaps) = buildFreeVars names gs_heaps
		#! (cons_def=:{cons_type}, gs_modules) = getConsDef type_def_mod ds_index gs_modules 				
		#! gs = {gs & gs_heaps = gs_heaps, gs_modules = gs_modules}
		
		#! (cons_arg_exprs, gs=:{gs_heaps}) = 
			build_cons_args iso_dir cons_type.st_args cons_arg_vars fun_arg_vars type_def gs 
		#! (expr, gs_heaps) = buildConsApp type_def_mod def_symbol cons_arg_exprs gs_heaps				
		#! alg_pattern = {
			ap_symbol = {glob_module = type_def_mod, glob_object = def_symbol},
			ap_vars = cons_arg_vars,
			ap_expr = expr,
			ap_position = NoPos
			}
		= (alg_pattern, cons_arg_vars, {gs & gs_heaps = gs_heaps})
	
	build_cons_args :: !IsoDirection ![AType] ![FreeVar] ![FreeVar] !CheckedTypeDef !*GenericState 
		-> ([Expression], !*GenericState)
	build_cons_args iso_dir [] [] fun_arg_vars type_def gs = ([], gs) 	
	build_cons_args	iso_dir [arg_type:arg_types] [cons_arg_var:cons_arg_vars] fun_arg_vars type_def gs
		#! (arg_expr, gs) = build_cons_arg iso_dir arg_type cons_arg_var fun_arg_vars type_def gs
		#! (arg_exprs, gs) = build_cons_args iso_dir arg_types cons_arg_vars fun_arg_vars type_def gs 
		= ([arg_expr : arg_exprs], gs)
	
	build_cons_arg :: !IsoDirection !AType !FreeVar ![FreeVar] !CheckedTypeDef !*GenericState 
		-> (!Expression, !*GenericState)	
	build_cons_arg iso_dir type cons_arg_var fun_vars type_def=:{td_args, td_name, td_pos} gs
		#! type_def_args = [atv_variable \\ {atv_variable} <- td_args]	
		#! (iso_expr, gs) = buildIsomapExpr type type_def_args fun_vars td_name td_pos gs
		#! {gs_heaps, gs_predefs} = gs
		#! sel_expr = case iso_dir of 
			IsoTo 	-> buildIsoToSelectionExpr iso_expr gs_predefs  
			IsoFrom -> buildIsoFromSelectionExpr iso_expr gs_predefs  
 		#! (cons_var_expr, _, gs_heaps) = buildBoundVarExpr cons_arg_var gs_heaps
		= (sel_expr @ [cons_var_expr], {gs & gs_heaps = gs_heaps})

	build_type1 :: !IsoDirection !Int !Int !*GenericState -> (!SymbolType, !*GenericState)
	build_type1 iso_dir module_index type_def_index gs=:{gs_heaps, gs_modules, gs_predefs}

		#! (st=:{st_result, st_args, st_arity}, gs) = buildIsomapType module_index type_def_index gs

		# (type1, type2) = case st_result.at_type of
			(TA _ [type1, type2]) -> (type1, type2)
			_	-> abort "Must be ISO application" 

		#! (argtype, restype) = case iso_dir of 
			IsoTo	-> (type1, type2) 
			IsoFrom -> (type2, type1)

		#! st = 
			{ st
			& st_args = st_args ++ [argtype]
			, st_arity = inc st_arity 
			, st_result = restype 
			}

		= (st, gs)

	build_type :: !IsoDirection !Int !Int !*GenericState
		-> (!SymbolType, !*GenericState)
	build_type 
			iso_dir module_index type_def_index 
			gs=:{gs_heaps, gs_modules, gs_predefs}
	
		#! ({td_arity, td_name}, gs_modules) = getTypeDef module_index type_def_index gs_modules 		
	
		#! (tvs1, gs_heaps) = mapSt (\n->build_type_var ("a"+++toString n)) [1..td_arity] gs_heaps 
		#! (tvs2, gs_heaps) = mapSt (\n->build_type_var ("b"+++toString n)) [1..td_arity] gs_heaps 
		#! (iso_args) = [buildATypeISO t1 t2 gs_predefs \\ t1 <- tvs1 & t2 <- tvs2] 
	
		#! type_symb_ident = {
			type_name = td_name,
			type_index = { glob_module = module_index, glob_object = type_def_index },
			type_arity = td_arity,
			type_prop = { 
				tsp_sign = {sc_pos_vect=cAllBitsClear, sc_neg_vect=cAllBitsClear},
				tsp_propagation = cAllBitsClear, 
				tsp_coercible = False
				}
			}
			
		#! (av1, gs_heaps) = buildAttrVar "u1" gs_heaps
		#! (av2, gs_heaps) = buildAttrVar "u2" gs_heaps							
		#! type1 = makeAType (TA type_symb_ident tvs1) (TA_Var av1) 
		#! type2 = makeAType (TA type_symb_ident tvs2) (TA_Var av2)
		#! (arg_type, res_type) = case iso_dir of
			IsoTo 	-> (type1, type2)
			IsoFrom -> (type2, type1)
			 
		#! symbol_type = {
			st_vars = 	
				[tv \\ {at_type=(TV tv)} <- tvs1] ++ 
				[tv \\ {at_type=(TV tv)} <- tvs2],
			st_args = iso_args ++ [arg_type],
			st_arity = td_arity + 1,
			st_result = res_type,
			st_context = [],
			st_attr_vars = 
				[av \\ {at_attribute=(TA_Var av)} <- tvs1] ++ 
				[av \\ {at_attribute=(TA_Var av)} <- tvs2] ++
				[av1, av2],
			st_attr_env = []
			}
		#! gs = {gs & gs_heaps = gs_heaps, gs_modules = gs_modules}
		= (symbol_type, gs)
			//---> ("isomap to/from type", td_name, symbol_type)
	
	build_type_var name heaps
		#! (av, heaps) = buildAttrVar name heaps 
		#! (tv, heaps) = buildTypeVar name heaps
		= (makeAType (TV tv) (TA_Var av), heaps)	

buildIsomapForTypeDef :: !DefinedSymbol !Int !Int !CheckedTypeDef !DefinedSymbol !DefinedSymbol !*GenericState
	-> (!FunDef, !Index, !*GenericState)
buildIsomapForTypeDef	
		fun_def_sym group_index type_def_mod 
		type_def=:{td_name, td_index, td_arity, td_pos}
		from_fun to_fun 
		gs=:{gs_main_dcl_module_n, gs_heaps, gs_predefs}	 
	#! arg_names = [ "iso" +++ toString n \\ n <- [1 .. td_arity]]  
	#! (arg_exprs, arg_vars, gs_heaps) = buildVarExprs arg_names gs_heaps
		
	#! (from_expr, gs_heaps) = buildFunApp gs_main_dcl_module_n from_fun arg_exprs gs_heaps
	#! (to_expr, gs_heaps) 	= buildFunApp gs_main_dcl_module_n to_fun arg_exprs gs_heaps	
	#! (iso_expr, gs_heaps) 	= buildISO to_expr from_expr gs_predefs gs_heaps
	#! gs = {gs & gs_heaps = gs_heaps}
	#! (fun_type, gs) = buildIsomapType type_def_mod td_index gs 
	#! fun_def = makeFunction fun_def_sym group_index arg_vars iso_expr (Yes fun_type) [] gs_main_dcl_module_n td_pos					
	= (fun_def, fun_def_sym.ds_index, gs)

buildIsomapType :: !Int !Int !*GenericState -> (!SymbolType, !*GenericState)
buildIsomapType module_index type_def_index
			gs=:{gs_heaps, gs_modules, gs_predefs, gs_td_infos}

	#! ({td_arity, td_name, td_pos}, gs_modules) = getTypeDef module_index type_def_index gs_modules 		
	# ({tdi_kinds}, gs_td_infos) = gs_td_infos ! [module_index, type_def_index] 
	# kind = case tdi_kinds of
		[] -> KindConst
		ks -> KindArrow (ks /*++ [KindConst]*/) 

	// build generic type for isomap
	# (t1, tv1, av1, gs_heaps) = build_type_var1 "a" gs_heaps
	# (t2, tv2, av2, gs_heaps) = build_type_var1 "b" gs_heaps		
	# generic_type = 
		{ gt_type = 
			{ st_vars = []
			, st_args = []
			, st_arity = 0
			, st_result = buildATypeISO t1 t2 gs_predefs
			, st_context = []
			, st_attr_vars = [av1, av2]
			, st_attr_env = []
			}
		, gt_vars = [tv1, tv2]
		, gt_arity = 2
		}
	# dummy_generic_def = 
		{ gen_name = td_name	
		, gen_member_name = td_name
		, gen_type = generic_type
		, gen_pos = td_pos
		, gen_kinds_ptr	= nilPtr 
		, gen_cons_ptr = nilPtr
	 	, gen_classes = []
		, gen_isomap = EmptyDefinedSymbol
		}

	# (st, agvs, gavs, hp_type_heaps) = specializeGenericType dummy_generic_def kind gs_heaps.hp_type_heaps 

	// substitute generic variables with the type
	#! type_symb = {
		type_name = td_name,
		type_index = { glob_module = module_index, glob_object = type_def_index },
		type_arity = td_arity,
		type_prop = { 
			tsp_sign = {sc_pos_vect=cAllBitsClear, sc_neg_vect=cAllBitsClear},
			tsp_propagation = cAllBitsClear, 
			tsp_coercible = False
			}
		}

	# hp_type_heaps = foldSt subst_av_for_self st.st_attr_vars hp_type_heaps 
		with 
			subst_av_for_self av=:{av_info_ptr} th=:{th_attrs}	
				= {th & th_attrs = th_attrs <:= (av_info_ptr, AVI_Attr (TA_Var av))}
			
	# hp_type_heaps = foldSt subst_with_the_type agvs hp_type_heaps
		with 
			subst_with_the_type	{atv_variable={tv_info_ptr}} th=:{th_vars}
				= {th & th_vars = th_vars <:= (tv_info_ptr, TVI_Type (TA type_symb []))}
				
	# (ok, (st_args, st_result), hp_type_heaps) = substitute (st.st_args, st.st_result) hp_type_heaps	
	
	
	# symbol_type = 
		{ st 
		& st_args = st_args
		, st_result = st_result
		, st_vars = st.st_vars -- [atv_variable \\ {atv_variable} <- agvs]
		} 
	
	#! gs_heaps = { gs_heaps & hp_type_heaps = hp_type_heaps }
	#! gs = {gs & gs_heaps = gs_heaps, gs_modules = gs_modules, gs_td_infos = gs_td_infos}
	= (symbol_type, gs)
		//---> ("isomap to/from type", td_name, symbol_type)
where
	build_type_var1 name heaps
		#! (av, heaps) = buildAttrVar name heaps 
		#! (tv, heaps) = buildTypeVar name heaps
		= (makeAType (TV tv) (TA_Var av), tv, av, heaps)	


buildIsomapForGeneric :: !DefinedSymbol !Int !GenericDef !*GenericState
	-> (!FunDef, !Index, !*GenericState)
buildIsomapForGeneric def_sym group_index {gen_type, gen_name, gen_pos} gs=:{gs_heaps,gs_main_dcl_module_n}
	#! arg_names = [ "iso" +++ toString n \\ n <- [1 .. gen_type.gt_arity]]
	#! (arg_vars, gs_heaps) = buildFreeVars arg_names gs_heaps
	#! curried_gt_type = curry_symbol_type gen_type.gt_type
	#! gs = {gs & gs_heaps = gs_heaps }
	#! (body_expr, gs) = buildIsomapExpr curried_gt_type gen_type.gt_vars arg_vars gen_name gen_pos gs 	
	#! fun_def = makeFunction def_sym group_index arg_vars body_expr No [] gs_main_dcl_module_n gen_pos					
	= (fun_def, def_sym.ds_index, gs) 	
where
	// no uniqueness stuff is needed to build the
	// expression using the type
	curry_symbol_type {st_args, st_result}
		= foldr (\x y -> makeAType (x --> y) TA_Multi) st_result st_args 

// expression that does mapping of a type
buildIsomapExpr :: 
	!AType 		// type to build mapping expression for
	![TypeVar] 	// type variables of the type
	![FreeVar] 	// function arguments corresponding to the type variables
	!Ident !Position
	!*GenericState
	-> (!Expression, !*GenericState)
buildIsomapExpr {at_type} arg_type_vars arg_vars name pos gs
	= build_expr at_type arg_type_vars arg_vars name pos gs	
where

	build_expr :: !Type ![TypeVar] ![FreeVar] !Ident !Position !*GenericState
		-> (!Expression, !*GenericState)		
	build_expr (TA {type_arity=0} _) arg_type_vars arg_vars name pos gs=:{gs_predefs, gs_heaps}
		// isomap for types with no arguments is identity
		# (expr, gs_heaps) = buildIsomapIdApp gs_predefs gs_heaps
		= (expr, {gs & gs_heaps = gs_heaps})

	build_expr (TA {type_index, type_name} args) arg_type_vars arg_vars name pos gs
		# (arg_exprs, gs) = build_exprs args arg_type_vars arg_vars name pos gs
		# {gs_heaps, gs_main_dcl_module_n, gs_gtd_infos} = gs			
		# (gtd_info, gs_gtd_infos) = gs_gtd_infos ! [type_index.glob_module, type_index.glob_object]		
		# gt = case gtd_info of
			(GTDI_Generic gt) -> gt
			_ -> abort ("(generic.icl) type " +++ type_name.id_name +++ " does not have generic representation\n")
		# (expr, gs_heaps) = buildFunApp gs_main_dcl_module_n gt.gtr_isomap arg_exprs gs_heaps			
		= (expr, {gs & gs_heaps = gs_heaps, gs_gtd_infos = gs_gtd_infos})
	
	build_expr (arg_type --> res_type) arg_type_vars arg_vars name pos gs
		# (arg_expr, gs) = buildIsomapExpr arg_type arg_type_vars arg_vars name pos gs
		# (res_expr, gs) = buildIsomapExpr res_type arg_type_vars arg_vars name pos gs				
		# {gs_heaps, gs_main_dcl_module_n, gs_predefs} = gs		
		# (expr, gs_heaps) = buildIsomapArrowApp arg_expr res_expr gs_predefs gs_heaps
		= (expr, {gs & gs_heaps = gs_heaps})

	build_expr ((CV type_var) :@: args) arg_type_vars arg_vars name pos gs=:{gs_error}

		#! (arg_exprs, gs) = build_exprs args arg_type_vars arg_vars name pos gs
		#! (cons_var_expr, gs) = build_expr_for_type_var type_var arg_type_vars arg_vars gs	
		= (cons_var_expr @ arg_exprs, gs)

/*
		#! gs_error = reportError name pos "type constructor variables are not yet supported in generic types" gs_error
		= (EE, {gs & gs_error = gs_error})
*/
	build_expr (TB baric_type) arg_type_vars arg_vars name pos gs=:{gs_predefs, gs_heaps}		
		# (expr, gs_heaps) = buildIsomapIdApp gs_predefs gs_heaps
		= (expr, {gs & gs_heaps = gs_heaps})
						
	build_expr (TV type_var) arg_type_vars arg_vars name pos gs
		= build_expr_for_type_var type_var arg_type_vars arg_vars gs
	build_expr (GTV type_var) arg_type_vars arg_vars name pos gs
		= build_expr_for_type_var type_var arg_type_vars arg_vars gs 
	build_expr (TQV type_var) arg_type_vars arg_vars name pos gs
		= build_expr_for_type_var type_var arg_type_vars arg_vars gs 
	build_expr (TLifted type_var) arg_type_vars arg_vars name pos gs
		= build_expr_for_type_var type_var arg_type_vars arg_vars gs 
	build_expr _ arg_type_vars arg_vars name pos gs=:{gs_error}
		#! gs_error = reportError name pos "cannot build mapping for the type" gs_error
		= (EE, {gs & gs_error = gs_error})
			
	build_exprs [] arg_type_vars arg_vars name pos gs 
		= ([], gs)
	build_exprs [type:types] arg_type_vars arg_vars name pos gs
		# (expr, gs) = buildIsomapExpr type arg_type_vars arg_vars name pos gs
		# (exprs, gs) = build_exprs types arg_type_vars arg_vars name pos gs
		= ([expr:exprs], gs)
			 			
	build_expr_for_type_var type_var arg_type_vars arg_vars gs=:{gs_predefs, gs_heaps}
		# (var_expr, gs_heaps) = buildExprForTypeVar type_var arg_type_vars arg_vars gs_predefs gs_heaps 
		= (var_expr, {gs & gs_heaps = gs_heaps})
	
buildInstance :: !DefinedSymbol !Int !ClassInstance !GenericDef !*GenericState
	-> (!FunDef, !*GenericState)
buildInstance 
		def_sym group_index 
		instance_def=:{ins_type, ins_generic, ins_pos, ins_ident} 
		generic_def=:{gen_name, gen_type, gen_isomap} 
		gs=:{gs_heaps,gs_main_dcl_module_n}	

	#! original_arity 	= gen_type.gt_type.st_arity
	#! generated_arity 	= def_sym.ds_arity - original_arity // arity of kind
	
	#! generated_arg_names = [ "f" +++ toString n \\ n <- [1 .. generated_arity]]
	#! (generated_arg_vars, gs_heaps) = buildFreeVars generated_arg_names gs_heaps	
	#! original_arg_names = 	[ "x" +++ toString n \\ n <- [1 .. original_arity]]  
	#! (original_arg_exprs, original_arg_vars, gs_heaps) = buildVarExprs original_arg_names gs_heaps	
	#! arg_vars = generated_arg_vars ++ original_arg_vars
	
	#! (gt=:{gtr_type, gtr_type_args, gtr_cons_infos}, gs) = get_generic_type ins_type {gs & gs_heaps = gs_heaps } 		
	#! gen_glob_def_sym = {
		glob_module = ins_generic.glob_module,
		glob_object = {
			ds_ident = gen_name,
			ds_index = ins_generic.glob_object,
			ds_arity = 0
			}
		} 
		
	#! (adaptor_expr, gs)	 = build_adaptor_expr gt gen_isomap gs  
		//---> ("generic type", gtr_type)
		
	#! (instance_expr, cons_infos, gs)	 = build_instance_expr gtr_type gtr_cons_infos gtr_type_args generated_arg_vars gen_glob_def_sym gs 
		//---> ("build_instance_expr", gtr_type_args, generated_arg_vars)		
		
	| supportConsInfo && (not (isEmpty cons_infos))
		= abort "not all cons infos consumed"	
		
	#! body_expr = if (isEmpty original_arg_exprs)
		(adaptor_expr @ [instance_expr]) 
		((adaptor_expr @ [instance_expr]) @ original_arg_exprs)

	#! fun_def = makeFunction def_sym group_index arg_vars body_expr No [] gs_main_dcl_module_n ins_pos					
	= (fun_def, gs) 	
		//---> ("buildInstance", fun_def)
where
	get_generic_type :: !InstanceType !*GenericState 
		-> (GenericTypeRep, !*GenericState)
	get_generic_type ins_type gs=:{gs_modules, gs_gtd_infos, gs_error}
		# instance_type = hd ins_type.it_types
		# {type_index} = case instance_type of 
			TA type_symb_ident _ 	-> type_symb_ident
			_ 						-> abort ("instance type is not a type application")
				//---> ("get_generic_type", instance_type) 
		# (gtd_info, gs_gtd_infos) = gs_gtd_infos ! [type_index.glob_module, type_index.glob_object]
		# (GTDI_Generic gt) = gtd_info
		= (gt, {gs & gs_gtd_infos = gs_gtd_infos, gs_modules = gs_modules, gs_error=gs_error})
	
	build_adaptor_expr {gtr_iso, gtr_type} gen_isomap gs=:{gs_heaps, gs_main_dcl_module_n, gs_predefs}
		// create n iso applications 
		# (iso_exprs, gs_heaps) = build_iso_exprs gen_isomap.ds_arity gtr_iso gs_main_dcl_module_n gs_heaps		
		# (isomap_expr, gs_heaps) = buildFunApp gs_main_dcl_module_n gen_isomap iso_exprs gs_heaps
		# sel_expr = buildIsoFromSelectionExpr isomap_expr gs_predefs 
		= (sel_expr, {gs & gs_heaps = gs_heaps})
		
	build_iso_exprs n iso gs_main_dcl_module_n gs_heaps
		| n == 0 = ([], gs_heaps)
		# (expr, gs_heaps) = buildFunApp gs_main_dcl_module_n iso [] gs_heaps	
		# (exprs, gs_heaps) = build_iso_exprs (n - 1) iso gs_main_dcl_module_n gs_heaps	
		= ([expr:exprs], gs_heaps)
	
	// e.g. for eq on lists: 
	// 		eqEITHER eqUNIT (eqPAIR eqElt (eqList eqElt))
	// with cons info:
	// 		eqEITHER 
	//			(eqCONS info_Nil eqUNIT) 
	//			(eqCONS info_Cons (eqPAIR eqElt (eqList eqElt)))
	build_instance_expr :: !AType ![DefinedSymbol] ![TypeVar] ![FreeVar] !(Global DefinedSymbol) !*GenericState 
		-> (Expression, ![DefinedSymbol], !*GenericState)
	build_instance_expr {at_type} cons_infos type_vars vars gen_sym gs 
		= build_instance_expr1 at_type cons_infos type_vars vars gen_sym gs
	
	build_instance_expr1 (TA {type_name, type_index, type_arity} type_args) cons_infos type_vars vars gen_sym gs	
		# (arg_exprs, cons_infos, gs=:{gs_heaps}) = build_args type_args cons_infos gs
			with
				build_args [] cons_infos gs = ([], cons_infos, gs)
				build_args [t:ts] cons_infos gs  
					# (e, cons_infos, gs) = build_instance_expr t cons_infos type_vars vars gen_sym gs
					# (es, cons_infos, gs) = build_args ts cons_infos gs
					= ([e:es], cons_infos, gs)
		
		# (is_cons, gs) = is_cons_instance type_index gs
		| supportConsInfo && is_cons 
			= build_cons_fun_app gen_sym arg_exprs cons_infos gs			

		| otherwise 	
			# (kind, gs) = get_kind_of_type_def type_index gs
			= build_generic_app gen_sym kind arg_exprs cons_infos gs		
			
	build_instance_expr1 (arg_type --> res_type) cons_infos  type_vars vars gen_sym gs	
		#! (arg_expr, cons_infos, gs) = build_instance_expr arg_type cons_infos type_vars vars gen_sym gs
		#! (res_expr, cons_infos, gs) = build_instance_expr res_type cons_infos type_vars vars gen_sym gs
		= build_generic_app gen_sym (KindArrow [KindConst,KindConst/*,KindConst*/]) [arg_expr, res_expr] cons_infos gs
	build_instance_expr1 ((CV type_var) :@: type_args) cons_infos  type_vars vars gen_sym gs=:{gs_error}	
/*
		# gs_error = checkErrorWithIdentPos (newPosition ins_ident ins_pos) "application of type constructor variable is not yet supported in generic types" gs_error
		= (EE, cons_infos, {gs & gs_error = gs_error})				
*/
		# (arg_exprs, cons_infos, gs=:{gs_heaps}) = build_args type_args cons_infos gs
			with
				build_args [] cons_infos gs = ([], cons_infos, gs)
				build_args [t:ts] cons_infos gs  
					# (e, cons_infos, gs) = build_instance_expr t cons_infos type_vars vars gen_sym gs
					# (es, cons_infos, gs) = build_args ts cons_infos gs
					= ([e:es], cons_infos, gs)
		
		# (var_expr, cons_infos, gs) = build_expr_for_type_var type_var type_vars vars cons_infos gs
		
		= (var_expr @ arg_exprs, cons_infos, gs)

	build_instance_expr1 (TB basic_type) cons_infos  type_vars vars gen_sym gs 	
		= build_generic_app gen_sym KindConst [] cons_infos gs
	build_instance_expr1 (TV type_var) cons_infos  type_vars vars gen_sym gs 
		= build_expr_for_type_var type_var type_vars vars cons_infos gs 
	build_instance_expr1 (GTV type_var) cons_infos  type_vars vars gen_sym gs 
		= build_expr_for_type_var type_var type_vars vars cons_infos gs 
	build_instance_expr1 (TQV type_var) cons_infos  type_vars vars gen_sym gs 
		= build_expr_for_type_var type_var type_vars vars cons_infos gs 
	build_instance_expr1 _ cons_infos _ _ _ gs=:{gs_error}
		# gs_error = checkErrorWithIdentPos (newPosition ins_ident ins_pos) "can not build instance for the type" gs_error
		= (EE, cons_infos, {gs & gs_error = gs_error})
			
	build_expr_for_type_var type_var type_vars vars cons_infos gs=:{gs_predefs, gs_heaps}
		# (var_expr, gs_heaps) = buildExprForTypeVar type_var type_vars vars gs_predefs gs_heaps 
		= (var_expr, cons_infos, {gs & gs_heaps = gs_heaps})
		
	build_generic_app {glob_module, glob_object} kind arg_exprs cons_infos gs=:{gs_heaps}
		# (expr, gs_heaps) = buildGenericApp glob_module glob_object kind arg_exprs gs_heaps
		= (expr, cons_infos, {gs & gs_heaps = gs_heaps})	

	get_kind_of_type_def {glob_module, glob_object} gs=:{gs_td_infos}
		# (td_info, gs_td_infos) = gs_td_infos ! [glob_module, glob_object]
		= (make_kind td_info.tdi_kinds, {gs & gs_td_infos = gs_td_infos})
	where	
		make_kind [] = KindConst
		make_kind ks = KindArrow (ks /*++ [KindConst]*/)

	is_cons_instance {glob_module, glob_object} gs=:{gs_predefs}
		# {pds_def, pds_module} = gs_predefs.[PD_TypeCONS]
		= (pds_module == glob_module && pds_def == glob_object, gs)

	build_cons_fun_app 
			gen=:{glob_module, glob_object} 
			arg_exprs
			[cons_info:cons_infos]
			gs=:{	gs_heaps=gs_heaps=:{hp_type_heaps=hp_type_heaps=:{th_vars}},
					gs_main_dcl_module_n,
					gs_modules,  
					gs_error}

		#! (generic_def=:{gen_name, gen_pos, gen_cons_ptr}, gs_modules) 
			= getGenericDef glob_module glob_object.ds_index gs_modules 	
		#! (info, th_vars) = readPtr gen_cons_ptr th_vars			
		#! gs_heaps = { gs_heaps & hp_type_heaps = {hp_type_heaps & th_vars = th_vars }}	
		
		# (cons_info_expr, gs_heaps) = buildFunApp gs_main_dcl_module_n cons_info [] gs_heaps 	

		#! (fun_def_sym, gs_error) = case info of		
			TVI_ConsInstance fun_def_sym
				-> (fun_def_sym, gs_error)				
			TVI_Empty
				-> (EmptyDefinedSymbol, reportError gen_name gen_pos "no CONS instance provided" gs_error)
		
		#! (app_expr, gs_heaps) = buildFunApp gs_main_dcl_module_n fun_def_sym [cons_info_expr:arg_exprs] gs_heaps 								
		= (app_expr, cons_infos, {gs & gs_heaps = gs_heaps, gs_modules = gs_modules, gs_error = gs_error})
			//---> ("build_cons_app", cons_info.ds_ident, fun_def_sym.ds_ident) 
			 			
buildExprForTypeVar :: 
	TypeVar 	// type variable to build exspression for
	[TypeVar] 	// generic type variables
	[FreeVar]	// function arguments corresponding to the type variables 
	!PredefinedSymbols !*Heaps 
	-> (!Expression, !*Heaps)
buildExprForTypeVar type_var type_vars vars predefs heaps 
	| length type_vars <> length vars 
		= abort "buildExprForTypeVar: inconsistent arguments\n"
	# tv_info_ptrs = {tv_info_ptr \\ {tv_info_ptr} <- type_vars}
	
	// find whether type_var is contained in the array of generic variables.
	# index = find_in_array 0 tv_info_ptrs type_var.tv_info_ptr
	| index == (-1)		
		// If not, it is a non-generic variable.
		// For non-generic variables the isomorphism is identity
		= buildIsomapIdApp predefs heaps
		// This is a generic variable, 
		// use corresponding function argument variable
		# (expr, var, heaps) = buildBoundVarExpr (vars !! index) heaps
		= (expr, heaps)

where
	find_in_array :: !Int !{#TypeVarInfoPtr} !TypeVarInfoPtr -> !Int 
	find_in_array index array el 
		| index == size array  	= -1 	
		| array.[index] == el 	= index
								= find_in_array (inc index) array el	


buildKindConstInstance :: !DefinedSymbol !Int !Index !DefinedSymbol !TypeKind !GenericState
	-> (!FunDef, !*GenericState)
buildKindConstInstance 
		def_sym group_index 
		generic_module generic_def_sym kind=:(KindArrow kinds) 
		gs=:{gs_heaps,gs_main_dcl_module_n}
	#! arg_names = ["x" +++ toString i \\ i <- [1 .. def_sym.ds_arity]]
	#! (arg_exprs, arg_vars, gs_heaps) = buildVarExprs arg_names gs_heaps
	
	# (gen_exprs, gs_heaps) = mapSt build_gen_expr [1 .. (length kinds)/* - 1*/] gs_heaps
	  
	#! (body_expr, gs_heaps) = buildGenericApp generic_module generic_def_sym kind (gen_exprs ++ arg_exprs) gs_heaps
	#! fun_def = makeFunction def_sym group_index arg_vars body_expr No [] gs_main_dcl_module_n NoPos					
	= (fun_def, {gs & gs_heaps = gs_heaps})	
where
	build_gen_expr _ heaps
		= buildGenericApp generic_module generic_def_sym KindConst [] heaps

buildKindConstInstance1 :: !DefinedSymbol !Int !Index !DefinedSymbol ![TypeKind] !GenericState
	-> (!FunDef, !*GenericState)
buildKindConstInstance1 
		def_sym group_index 
		generic_module generic_def_sym arg_kinds 
		gs=:{gs_heaps,gs_main_dcl_module_n}
	#! arg_names = ["x" +++ toString i \\ i <- [1 .. def_sym.ds_arity]]
	#! (arg_exprs, arg_vars, gs_heaps) = buildVarExprs arg_names gs_heaps
	
	# (gen_exprs, gs_heaps) = mapSt build_gen_expr arg_kinds gs_heaps
	  
	#! (body_expr, gs_heaps) 
		= buildGenericApp generic_module generic_def_sym (KindArrow arg_kinds) (gen_exprs ++ arg_exprs) gs_heaps
	#! fun_def = makeFunction def_sym group_index arg_vars body_expr No [] gs_main_dcl_module_n NoPos					
	= (fun_def, {gs & gs_heaps = gs_heaps})	
where
	build_gen_expr kind heaps
		= buildGenericApp generic_module generic_def_sym kind [] heaps

										
//===========================================
// access to common definitions
//===========================================

  	
getTypeDef :: !Index  !Index !u:{#CommonDefs} -> (!CheckedTypeDef, !u:{#CommonDefs})
getTypeDef mod_index type_index modules
	# (common_defs=:{com_type_defs}, modules) = modules![mod_index]
	# type_def = com_type_defs.[type_index]
	= (type_def, modules)

getConsDef :: !Index  !Index !u:{#CommonDefs} -> (!ConsDef, !u:{#CommonDefs})
getConsDef mod_index type_index modules
	# (common_defs=:{com_cons_defs}, modules) = modules![mod_index]
	# cons_def = com_cons_defs.[type_index]
	= (cons_def, modules)

getSelectorDef :: !Index  !Index !u:{#CommonDefs} -> (!SelectorDef, !u:{#CommonDefs})
getSelectorDef mod_index type_index modules
	# (common_defs=:{com_selector_defs}, modules) = modules![mod_index]
	# sel_def = com_selector_defs.[type_index]
	= (sel_def, modules)


getInstanceDef :: !Index !Index !u:{#CommonDefs} -> (!ClassInstance, !u:{#CommonDefs})
getInstanceDef mod_index ins_index modules
	# (common_defs=:{com_instance_defs}, modules) = modules![mod_index]
	# instance_def = com_instance_defs.[ins_index]
	= (instance_def, modules)
		 			
getGenericDef :: !Index !Index !u:{#CommonDefs} -> (!GenericDef, !u:{#CommonDefs})
getGenericDef module_index generic_index modules
	# (common_defs=:{com_generic_defs}, modules) = modules![module_index]
	# generic_def = com_generic_defs.[generic_index]
	= (generic_def, modules)

getClassDef :: !Index !Index !u:{#CommonDefs} -> (!ClassDef, !u:{#CommonDefs})
getClassDef module_index class_index modules
	#! (common_defs=:{com_class_defs}, modules) = modules![module_index]
	#! class_def = com_class_defs.[class_index]
	= (class_def, modules)

getMemberDef :: !Index !Index !u:{#CommonDefs} -> (!MemberDef, !u:{#CommonDefs})
getMemberDef module_index member_index modules
	# (common_defs=:{com_member_defs}, modules) = modules![module_index]
	# member_def = com_member_defs.[member_index]
	= (member_def, modules)
	
getGenericMember :: !(Global Index) !TypeKind !{#CommonDefs} -> (Bool, Global Index)
getGenericMember {glob_module, glob_object} kind modules
	# (generic_def, modules) = getGenericDef glob_module glob_object modules  
	# (ok, def_sym) = getGenericClassForKind generic_def kind
	| not ok = (False, undef)		
	# (class_def, modules) = getClassDef glob_module def_sym.ds_index modules
	# {ds_index} = class_def.class_members.[0]
	= (True, {glob_module = glob_module, glob_object = ds_index})

			
//===================================
// Types 
//===================================

makeAType :: !Type !TypeAttribute -> !AType
makeAType type attr = 
	{	at_attribute = attr
	, 	at_annotation = AN_None
	, 	at_type = type
	}

buildTypeVar name heaps=:{hp_type_heaps=hp_type_heaps=:{th_vars}}
	# (tv, th_vars) = freshTypeVar {id_name=name,id_info=nilPtr} th_vars
	= (	tv, {heaps & hp_type_heaps = {hp_type_heaps & th_vars = th_vars}})

buildAttrVar name heaps=:{hp_type_heaps=hp_type_heaps=:{th_attrs}}
	# (av, th_attrs) = freshAttrVar {id_name=name,id_info=nilPtr} th_attrs
	= (	av, {heaps & hp_type_heaps = {hp_type_heaps & th_attrs = th_attrs}})

freshTypeVar :: !Ident  !*TypeVarHeap -> (!TypeVar, !*TypeVarHeap) 
freshTypeVar name th_vars 
	# (info_ptr, th_vars) = newPtr TVI_Empty th_vars
	= ({tv_name = name, tv_info_ptr = info_ptr}, th_vars)

freshAttrVar :: !Ident !*AttrVarHeap -> (!AttributeVar, !*AttrVarHeap)
freshAttrVar name th_attrs
	# (info_ptr, th_attrs) = newPtr AVI_Empty th_attrs
	= ({av_name = name, av_info_ptr = info_ptr}, th_attrs)

freshSymbolType :: String !SymbolType !*TypeHeaps -> (!SymbolType, !*TypeHeaps) 
freshSymbolType postfix st type_heaps
	# {st_vars, st_args, st_result, st_context, st_attr_vars, st_attr_env} = st
	# (new_st_vars, type_heaps) = subst_type_vars postfix st_vars type_heaps
	# (new_st_attr_vars, type_heaps) = subst_attr_vars postfix st_attr_vars type_heaps

	# (_, new_st_args, type_heaps) = 		substitute st_args 		type_heaps
	# (_, new_st_result, type_heaps) = 		substitute st_result 	type_heaps
	# (_, new_st_context, type_heaps) = 	substitute st_context 	type_heaps
	# (_, new_st_attr_env, type_heaps) = 	substitute st_attr_env 	type_heaps

	# new_st = { st &	
			st_vars = new_st_vars
		,	st_args = new_st_args
		,	st_result = new_st_result
		,	st_context = new_st_context
		,	st_attr_vars = new_st_attr_vars
		,	st_attr_env = new_st_attr_env 
		}
	= (new_st, type_heaps)

where	 
	subst_type_var postfix tv=:{tv_name={id_name}, tv_info_ptr} th_vars
		# (tv, th_vars) = freshTypeVar {id_name=id_name+++postfix, id_info=nilPtr} th_vars  
		= (tv, writePtr tv_info_ptr (TVI_Type (TV tv)) th_vars)
	subst_type_vars postfix tvs type_heaps=:{th_vars}
		# (tvs, th_vars) = mapSt (subst_type_var postfix) tvs th_vars
		= (tvs, {type_heaps & th_vars = th_vars})
	
	subst_attr_var postfix av=:{av_name={id_name}, av_info_ptr} th_attrs
		# (av, th_attrs) = freshAttrVar {id_name=id_name+++postfix, id_info=nilPtr} th_attrs  
		= (av, writePtr av_info_ptr (AVI_Attr (TA_Var av)) th_attrs)
	subst_attr_vars postfix avs type_heaps=:{th_attrs}
		# (avs, th_attrs) = mapSt (subst_attr_var postfix) avs th_attrs
		= (avs, {type_heaps & th_attrs = th_attrs})

// all variables are taken afresh
freshGenericType :: !GenericType !*TypeHeaps
	-> (!GenericType, !*TypeHeaps)
freshGenericType gen_type=:{gt_type, gt_vars, gt_arity} type_heaps
	// set variables that have to be taken fresh, i.e. 
	// both generic variables and non-variables
	# {st_vars} = gt_type	
	# symbol_type = { gt_type & st_vars = gt_vars ++ st_vars } 
	# (fresh_symbol_type, type_heaps) = freshSymbolType "" symbol_type type_heaps
		
	// split fresh variables into generic and non-generic variables
	# (fresh_gt_vars, st_vars) = splitAt gt_arity fresh_symbol_type.st_vars
	# fresh_gen_type = { gen_type & 
		gt_vars = fresh_gt_vars, gt_type = {fresh_symbol_type & st_vars = st_vars}}
	= (fresh_gen_type, type_heaps) 

// Only generic variables are taken afresh
// Non generic variables are supposed to be shared by
// generic subtypes of a type
freshGenericSubtype :: !String !GenericType !*TypeHeaps
	-> (!GenericType, !*TypeHeaps)
freshGenericSubtype postfix gen_type=:{gt_vars, gt_type, gt_arity} type_heaps 
	// set variables that have to be taken afresh, i.e. generic variables
	#! {st_vars} = gt_type
	#! symbol_type = {gt_type & st_vars = gt_vars}

	#! (fresh_symbol_type, type_heaps) = freshSymbolType postfix symbol_type type_heaps
		
	// restore non-generic variables 
	#! fresh_gt_vars = fresh_symbol_type.st_vars
	#! fresh_gen_type = { gen_type & 
		gt_vars = fresh_gt_vars, gt_type = {fresh_symbol_type & st_vars = st_vars}}
	= (fresh_gen_type, type_heaps)

clearType :: Type !*TypeHeaps -> !*TypeHeaps 
clearType type th=:{th_vars}	
	= {th & th_vars = performOnTypeVars initializeToTVI_Empty type th_vars}			

clearAType :: !AType !*TypeHeaps -> !*TypeHeaps 		
clearAType type th=:{th_vars, th_attrs}
	#! th_vars	 = performOnTypeVars initializeToTVI_Empty type th_vars
	#! th_attrs  = performOnAttrVars initializeToAVI_Empty type th_attrs
	= {th & th_vars = th_vars, th_attrs = th_attrs}			

clearSymbolType :: !SymbolType !*TypeHeaps -> !*TypeHeaps
clearSymbolType {st_args, st_context, st_result} th
	#! th = foldSt clearAType st_args th
	#! th = foldSt clearType (flatten [tc_types \\ {tc_types} <- st_context]) th 
	#! th = clearAType st_result th
	= th

substituteInSymbolType :: !SymbolType !*TypeHeaps -> (!SymbolType, !*TypeHeaps)
substituteInSymbolType st=:{st_args, st_result, st_attr_env, st_context} th
	#! (_, st_args, th) 	= substitute st.st_args th
	#! (_, st_result, th) 	= substitute st.st_result th	
	#! (_, st_context, th) 	= substitute st.st_context th	
	#! (_, st_attr_env, th)	= substitute st.st_attr_env th		
	#! st = { st &
		st_args = st_args,
		st_result = st_result,
		st_context = st_context,
		st_attr_env = st_attr_env
		}
	= (st, th)	

// sets ATV_Attribute in all variables
setTypeVarAttrs :: !SymbolType !*TypeHeaps -> !*TypeHeaps
setTypeVarAttrs {st_args, st_result} th=:{th_vars}
	#! th_vars = foldSt set_in_atype st_args th_vars
	#! th_vars = set_in_atype st_result th_vars
	= {th & th_vars = th_vars}
where
	set_in_atype at th_vars
		= performOnTypeVars on_type_var at th_vars
	on_type_var ta tv=:{tv_info_ptr} th_vars
		= writePtr tv_info_ptr (TVI_Attribute ta) th_vars

buildTypeApp :: !Index !CheckedTypeDef [AType] -> AType
buildTypeApp  td_module {td_name, td_arity, td_index} args
	# global_index = {glob_module = td_module, glob_object = td_index}
	# type_symb = MakeTypeSymbIdent global_index td_name (length args) 	
 	= makeAType (TA type_symb args) TA_Multi
		
buildPredefTypeApp :: !Int [AType] !PredefinedSymbols -> !AType
buildPredefTypeApp predef_index args predefs
	# {pds_module, pds_def} = predefs.[predef_index]
	# pds_ident = predefined_idents.[predef_index]
	# global_index = {glob_module = pds_module, glob_object = pds_def}
	# type_symb = MakeTypeSymbIdent global_index pds_ident (length args) 		  
	= makeAType (TA type_symb args) TA_Multi	

buildATypeISO	x y predefs = buildPredefTypeApp PD_TypeISO [x, y] predefs
buildATypeUNIT  predefs		= buildPredefTypeApp PD_TypeUNIT [] predefs
buildATypePAIR x y predefs 	= buildPredefTypeApp PD_TypePAIR [x, y] predefs
buildATypeEITHER x y predefs = buildPredefTypeApp PD_TypeEITHER [x, y] predefs
buildATypeARROW x y predefs = buildPredefTypeApp PD_TypeARROW [x, y] predefs
buildATypeCONS	x predefs 	= buildPredefTypeApp PD_TypeCONS [x] predefs

buildProductType :: ![AType] !PredefinedSymbols -> !AType 
buildProductType [] predefs = buildATypeUNIT predefs
buildProductType [type] predefs = type
buildProductType types predefs
	#  (l,r) = splitAt ((length types) / 2) types
	= buildATypePAIR (buildProductType l predefs) (buildProductType r predefs) predefs

//===================================
// Functions 
//===================================

makeFunction :: !DefinedSymbol !Index ![FreeVar] !Expression !(Optional SymbolType) ![FreeVar] !Index !Position
	-> FunDef
makeFunction {ds_index, ds_arity, ds_ident} group_index arg_vars body_expr opt_sym_type local_vars main_dcl_module_n fun_pos
	| length arg_vars <> ds_arity 
		= abort "length arg_vars <> ds_arity\n"  
	= {
		fun_symb = ds_ident,
		fun_arity = ds_arity,
		fun_priority = NoPrio,
		fun_body = TransformedBody {
			tb_args = arg_vars,
			tb_rhs = body_expr
			},
		fun_type = opt_sym_type,
		fun_pos = fun_pos,
		fun_kind  = FK_Function cNameNotLocationDependent,
		fun_lifted = 0,
		fun_info = {	
			fi_calls = [FunCall ind NotALevel \\ ind <- collectCalls main_dcl_module_n body_expr],	
			fi_group_index = group_index,
			fi_def_level = NotALevel,
			fi_free_vars =  [],
			fi_local_vars = local_vars,
			fi_dynamics = [],
			fi_properties = 0
			}	
		}

newGroupIndex gs=:{gs_last_group} = (gs_last_group, {gs & gs_last_group = gs_last_group + 1})
newFunIndex gs=:{gs_last_fun} = (gs_last_fun, {gs & gs_last_fun = gs_last_fun + 1})
newFunAndGroupIndex gs=:{gs_last_fun, gs_last_group} 
	= (gs_last_fun, gs_last_group, {gs & gs_last_fun = gs_last_fun + 1, gs_last_group = gs_last_group + 1})

addFunsAndGroups :: ![FunDef] ![Group] (!*GenericState) -> !*GenericState
addFunsAndGroups new_fun_defs new_groups 
		gs=:{gs_fun_defs, gs_groups, gs_first_fun, gs_last_fun, gs_first_group, gs_last_group,gs_main_dcl_module_n}
	# gs_fun_defs = add_funs new_fun_defs gs_fun_defs gs_first_fun gs_last_fun
	# gs_groups = add_groups new_groups gs_groups gs_first_group gs_last_group
	# (gs_groups, gs_fun_defs) = check_groups gs_first_group gs_groups gs_fun_defs
	= {gs & gs_fun_defs = gs_fun_defs, gs_groups = gs_groups}
where
	add_funs new_fun_defs gs_fun_defs gs_first_fun gs_last_fun
		# n_gs_fun_defs = size gs_fun_defs
		# n_new_fun_defs = length new_fun_defs
		| n_new_fun_defs <> gs_last_fun - gs_first_fun
			= abort "error in number of fun_defs" 	
		# fun_defs = createArray (n_new_fun_defs + n_gs_fun_defs) 
			(makeFunction EmptyDefinedSymbol NoIndex [] EE No [] gs_main_dcl_module_n NoPos)
		#! fun_defs = { fun_defs & [i] = gs_fun_defs . [i] \\ i <- [0..(n_gs_fun_defs - 1)]}
		#! fun_defs = { fun_defs & [i] = check_fun fun_def i \\ 
			i <- [n_gs_fun_defs .. (n_gs_fun_defs + n_new_fun_defs - 1)] & 
			fun_def <- new_fun_defs }
		= fun_defs
						
	add_groups new_groups gs_groups gs_first_group gs_last_group 
		# n_gs_groups = size gs_groups
		# n_new_groups = length new_groups
		| n_new_groups <> gs_last_group - gs_first_group
			= abort "error in number of groups"
		# groups = createArray (n_gs_groups + n_new_groups) {group_members = []}
		#! groups = { groups & [i] = gs_groups . [i] \\ i <- [0..(n_gs_groups - 1)]}
		#! groups = { groups & [i] = group \\ 
			i <- [n_gs_groups .. (n_gs_groups + n_new_groups - 1)] & 		
			group <- new_groups }
		= groups
	
	check_fun fun_def index
			= fun_def
/*			
		| fun_def.fun_index == index 
			= fun_def
			= abort ("conflicting fun_indexes of " +++ fun_def.fun_symb.id_name +++
				toString fun_def.fun_index +++ " and " +++ toString index) 
*/
	
	check_groups group_index groups funs 
		| group_index == size groups = (groups, funs)
		# (group, groups) = groups ! [group_index]
			//---> ("check group " +++ toString group_index)
		# funs = check_group group_index group.group_members funs 				
		= check_groups (group_index + 1) groups funs
	
	check_group group_index [] funs = funs
	check_group group_index [fun_index:fun_indexes] funs
		# (fun, funs) = funs ! [fun_index]
		| fun.fun_info.fi_group_index == group_index
			= check_group group_index fun_indexes funs
			= abort ("inconsistent group " +++ toString group_index +++ ": " +++ 
				toString fun_index +++ " and " +++ toString fun.fun_info.fi_group_index)		 		

buildIdFunction :: !DefinedSymbol Int !Ident !PredefinedSymbols !Index !*Heaps-> (!FunDef, !*Heaps)
buildIdFunction def_sym group_index name predefs gs_main_dcl_module_n heaps
	# (arg_expr, arg_var, heaps) = buildVarExpr "x" heaps 
	# fun_def = makeFunction def_sym group_index [arg_var] arg_expr No [] gs_main_dcl_module_n NoPos	
	= (fun_def, heaps)
	
buildUndefFunction :: !DefinedSymbol !Int !PredefinedSymbols !Index !*Heaps-> (!FunDef, !*Heaps)
buildUndefFunction def_sym group_index predefs gs_main_dcl_module_n heaps
	# names = [ "x" +++ toString i \\ i <- [1 .. def_sym.ds_arity]]
	# (arg_vars, heaps) = mapSt build_free_var names heaps
	# (body_expr, heaps) = buildUndefFunApp [] predefs heaps
	//# (body_expr, heaps) = buildUNIT predefs heaps
	# fun_def = makeFunction def_sym group_index arg_vars body_expr No [] gs_main_dcl_module_n NoPos	
	= (fun_def, heaps)
where
	build_free_var :: !String !*Heaps -> (!FreeVar, !*Heaps)
	build_free_var name heaps=:{hp_var_heap}
		# (var_info_ptr, hp_var_heap) = newPtr VI_Empty hp_var_heap
		# var_name = { id_name = name, id_info = nilPtr }
		# free_var = { fv_def_level = NotALevel, fv_count = 0, fv_info_ptr = var_info_ptr, fv_name = var_name}
		= (free_var, {heaps & hp_var_heap = hp_var_heap})

//===================================
// Case patterns
//===================================

buildPredefConsPattern :: !Int ![FreeVar] !Expression !PredefinedSymbols
	-> AlgebraicPattern
buildPredefConsPattern predef_index vars expr predefs
	# {pds_module, pds_def} = predefs.[predef_index]
	# pds_ident = predefined_idents.[predef_index]
	# cons_def_symbol = {
		ds_ident = pds_ident,
		ds_arity = length vars,
		ds_index = pds_def
		}
	# pattern = {
		ap_symbol = {glob_module = pds_module, glob_object = cons_def_symbol},
		ap_vars = vars,
		ap_expr = expr,
		ap_position = NoPos		
		}
	= pattern

buildUNITPattern expr predefs :== buildPredefConsPattern PD_ConsUNIT [] expr predefs
buildLEFTPattern var expr predefs :== buildPredefConsPattern PD_ConsLEFT [var] expr predefs
buildRIGHTPattern var expr predefs :== buildPredefConsPattern PD_ConsRIGHT [var] expr predefs
buildPAIRPattern var1 var2 expr predefs :== buildPredefConsPattern PD_ConsPAIR [var1, var2] expr predefs
buildCONSPattern cons_info_var cons_arg_var expr predefs :== buildPredefConsPattern PD_ConsCONS [cons_info_var, cons_arg_var] expr predefs

//===================================
// Expressions 
//===================================

buildConsApp :: !Index DefinedSymbol ![Expression] !*Heaps 
	-> (!Expression, !*Heaps) 
buildConsApp cons_mod {ds_ident, ds_index, ds_arity} arg_exprs heaps=:{hp_expression_heap}
	# (expr_info_ptr, hp_expression_heap) = newPtr EI_Empty hp_expression_heap
	# cons_glob = {glob_module = cons_mod, glob_object = ds_index}
	# expr = App {
		app_symb = {
			symb_name = ds_ident, 
			symb_kind = SK_Constructor cons_glob
			}, 
		app_args = arg_exprs, 
		app_info_ptr = expr_info_ptr} 	
	# heaps = { heaps & hp_expression_heap = hp_expression_heap } 
	= (expr, heaps)	

buildFunApp :: !Index DefinedSymbol ![Expression] !*Heaps 
	-> (!Expression, !*Heaps) 
buildFunApp fun_mod {ds_ident, ds_index, ds_arity} arg_exprs heaps=:{hp_expression_heap}
	# (expr_info_ptr, hp_expression_heap) = newPtr EI_Empty hp_expression_heap
	# fun_glob = {glob_module = fun_mod, glob_object = ds_index}
	# expr = App {
		app_symb = {
			symb_name = ds_ident, 
			symb_kind = SK_Function fun_glob
			}, 
		app_args = arg_exprs, 
		app_info_ptr = expr_info_ptr} 	
	# heaps = { heaps & hp_expression_heap = hp_expression_heap } 
	= (expr, heaps)	

buildGenericApp :: !Index !DefinedSymbol !TypeKind ![Expression] !*Heaps
	-> (!Expression, !*Heaps)
buildGenericApp module_index {ds_ident, ds_index} kind arg_exprs heaps=:{hp_expression_heap}
	# (expr_info_ptr, hp_expression_heap) = newPtr EI_Empty hp_expression_heap
	# glob_index = {glob_module = module_index, glob_object = ds_index}
	# expr = App {
		app_symb = {
			symb_name = ds_ident, 
			symb_kind = SK_Generic glob_index kind
		}, 
		app_args = arg_exprs, 
		app_info_ptr = expr_info_ptr} 	
	# heaps = { heaps & hp_expression_heap = hp_expression_heap } 
	= (expr, heaps)	

buildCaseExpr :: Expression CasePatterns !*Heaps 
	-> (!Expression, !*Heaps)
buildCaseExpr case_arg case_alts heaps=:{hp_expression_heap}	
	# (expr_info_ptr, hp_expression_heap) = newPtr EI_Empty hp_expression_heap
	# expr = Case {
		case_expr = case_arg,
		case_guards = case_alts,
		case_default = No,
		case_ident = No,
		case_info_ptr = expr_info_ptr,
// RWS ...
		case_explicit = False,
// ... RWS
		case_default_pos = NoPos 
		}
	# heaps = { heaps & hp_expression_heap = hp_expression_heap}	
	= (expr, heaps)

buildCaseUNITExpr :: !Expression !Expression !PredefinedSymbols !*Heaps 
	-> (!Expression, !*Heaps)
buildCaseUNITExpr arg_expr body_expr predefs heaps
	# unit_pat = buildUNITPattern body_expr predefs
	# {pds_module, pds_def} = predefs.[PD_TypeUNIT]
	# case_patterns = AlgebraicPatterns {glob_module = pds_module, glob_object = pds_def} [unit_pat]
	= buildCaseExpr arg_expr case_patterns heaps

buildCaseEITHERExpr :: !Expression (!FreeVar, !Expression) (!FreeVar, !Expression) !PredefinedSymbols !*Heaps 
	-> (!Expression, !*Heaps)
buildCaseEITHERExpr arg_expr (left_var, left_expr) (right_var, right_expr) predefs heaps
	# left_pat = buildLEFTPattern left_var left_expr predefs
	# right_pat = buildRIGHTPattern right_var right_expr predefs
	# {pds_module, pds_def} = predefs.[PD_TypeEITHER]
	# case_patterns = AlgebraicPatterns {glob_module = pds_module, glob_object = pds_def} [left_pat, right_pat]
	= buildCaseExpr arg_expr case_patterns heaps

buildCasePAIRExpr :: !Expression !FreeVar !FreeVar !Expression !PredefinedSymbols !*Heaps
	-> (!Expression, !*Heaps)
buildCasePAIRExpr arg_expr var1 var2 body_expr predefs heaps
	# pair_pat = buildPAIRPattern var1 var2 body_expr predefs	
	# {pds_module, pds_def} = predefs.[PD_TypePAIR]
	# case_patterns = AlgebraicPatterns {glob_module = pds_module, glob_object = pds_def} [pair_pat]	
	= buildCaseExpr arg_expr case_patterns heaps

buildCaseCONSExpr :: !Expression !FreeVar !FreeVar !Expression !PredefinedSymbols !*Heaps
	-> (!Expression, !*Heaps)
buildCaseCONSExpr arg_expr cons_info_var arg_var body_expr predefs heaps
	# cons_pat = buildCONSPattern cons_info_var arg_var body_expr predefs	
	# {pds_module, pds_def} = predefs.[PD_TypeCONS]
	# case_patterns = AlgebraicPatterns {glob_module = pds_module, glob_object = pds_def} [cons_pat]	
	= buildCaseExpr arg_expr case_patterns heaps
	


buildPredefConsApp :: !Int [Expression] !PredefinedSymbols !*Heaps
	-> (!Expression, !*Heaps)
buildPredefConsApp predef_index args predefs heaps=:{hp_expression_heap}
	# {pds_module, pds_def} = predefs.[predef_index]
	# pds_ident = predefined_idents.[predef_index]
	# global_index = {glob_module = pds_module, glob_object = pds_def}
	# symb_ident = {
		symb_name = pds_ident, 
		symb_kind = SK_Constructor global_index
		}
	# (expr_info_ptr, hp_expression_heap) = newPtr EI_Empty hp_expression_heap
	# app = App {app_symb = symb_ident, app_args = args, app_info_ptr = expr_info_ptr} 
	= (app, {heaps & hp_expression_heap = hp_expression_heap})

buildISO to_expr from_expr predefs heaps :== buildPredefConsApp PD_ConsISO [to_expr, from_expr] predefs heaps
buildUNIT predefs heaps		:== buildPredefConsApp PD_ConsUNIT [] predefs heaps
buildPAIR x y predefs heaps	:== buildPredefConsApp PD_ConsPAIR [x, y] predefs heaps
buildLEFT x predefs heaps	:== buildPredefConsApp PD_ConsLEFT [x] predefs heaps
buildRIGHT x predefs heaps	:== buildPredefConsApp PD_ConsRIGHT [x] predefs heaps
buildARROW x y predefs heaps :== buildPredefConsApp PD_ConsARROW [x, y] predefs heaps
buildCONS cons_info arg predefs heaps :== buildPredefConsApp PD_ConsCONS [cons_info, arg] predefs heaps

buildPredefFunApp :: !Int [Expression] !PredefinedSymbols !*Heaps
	-> (!Expression, !*Heaps)
buildPredefFunApp predef_index args predefs heaps=:{hp_expression_heap}
	# {pds_module, pds_def} = predefs.[predef_index]
	# pds_ident = predefined_idents.[predef_index]
	# global_index = {glob_module = pds_module, glob_object = pds_def}
	# symb_ident = {
		symb_name = pds_ident,
		symb_kind = SK_Function global_index
		}
	# (expr_info_ptr, hp_expression_heap) = newPtr EI_Empty hp_expression_heap
	# app = App {app_symb = symb_ident, app_args = args, app_info_ptr = expr_info_ptr} 
	= (app, {heaps & hp_expression_heap = hp_expression_heap})

buildUndefFunApp args predefs heaps :== buildPredefFunApp PD_undef args predefs heaps 
buildIsomapArrowApp x y predefs heaps :== buildPredefFunApp PD_isomap_ARROW_ [x,y] predefs heaps
buildIsomapIdApp predefs heaps :== buildPredefFunApp PD_isomap_ID [] predefs heaps
 	
buildIsoToSelectionExpr :: !Expression !PredefinedSymbols -> Expression
buildIsoToSelectionExpr record_expr predefs
	# {pds_module, pds_def} = predefs . [PD_iso_to]
	# pds_ident = predefined_idents . [PD_iso_to]
	# selector = { 
		glob_module = pds_module, 
		glob_object = {ds_ident = pds_ident, ds_index = pds_def, ds_arity = 1}}
	= Selection NormalSelector record_expr [RecordSelection selector 0]

buildIsoFromSelectionExpr :: !Expression !PredefinedSymbols -> Expression
buildIsoFromSelectionExpr record_expr predefs 
	# {pds_module, pds_def} = predefs . [PD_iso_from]
	# pds_ident = predefined_idents . [PD_iso_from]
	# selector = { 
		glob_module = pds_module, 
		glob_object = {ds_ident = pds_ident, ds_index = pds_def, ds_arity = 1}}
	= Selection NormalSelector record_expr [RecordSelection selector 1]

buildVarExpr :: !String !*Heaps	-> (!Expression, !FreeVar, !*Heaps)
buildVarExpr name heaps=:{hp_var_heap, hp_expression_heap} 
	# (expr_info_ptr, hp_expression_heap) = newPtr EI_Empty hp_expression_heap
	# (var_info_ptr, hp_var_heap) = newPtr VI_Empty hp_var_heap
	# var_name = { id_name = name, id_info = nilPtr }
	# fv = { fv_def_level = NotALevel, fv_count = 1, fv_info_ptr = var_info_ptr, fv_name = var_name}
	# var = Var {var_name = var_name, var_expr_ptr = expr_info_ptr, var_info_ptr = var_info_ptr } 
	# hp_var_heap = writePtr var_info_ptr (VI_Expression var) hp_var_heap
	# heaps = { heaps & hp_var_heap = hp_var_heap, hp_expression_heap = hp_expression_heap } 
	= (var, fv, heaps)

buildVarExprs :: ![String] !*Heaps -> (![Expression], [FreeVar], !*Heaps)	 		
buildVarExprs [] heaps = ([], [], heaps)
buildVarExprs [name:names] heaps 
	# (expr, var, heaps) = buildVarExpr name heaps
	# (exprs, vars, heaps) = buildVarExprs names heaps 
	= ([expr:exprs], [var:vars], heaps)

buildFreeVar :: !String !*Heaps -> (!FreeVar, !*Heaps)
buildFreeVar name heaps=:{hp_var_heap}
	# (var_info_ptr, hp_var_heap) = newPtr VI_Empty hp_var_heap
	# var_name = { id_name = name, id_info = nilPtr }
	# var = { fv_def_level = NotALevel, fv_count = 1, fv_info_ptr = var_info_ptr, fv_name = var_name}
	= (var, {heaps & hp_var_heap = hp_var_heap})


buildFreeVar0 :: !String !*Heaps -> (!FreeVar, !*Heaps)
buildFreeVar0 name heaps=:{hp_var_heap}
	# (var_info_ptr, hp_var_heap) = newPtr VI_Empty hp_var_heap
	# var_name = { id_name = name, id_info = nilPtr }
	# var = { fv_def_level = NotALevel, fv_count = 0, fv_info_ptr = var_info_ptr, fv_name = var_name}
	= (var, {heaps & hp_var_heap = hp_var_heap})

	

buildFreeVars :: ![String] !*Heaps -> (![FreeVar], !*Heaps)
buildFreeVars names heaps = mapSt buildFreeVar names heaps 	

// create expression from a variable  
buildBoundVarExpr :: !FreeVar !*Heaps -> (!Expression, !FreeVar, !*Heaps)
buildBoundVarExpr free_var=:{fv_info_ptr, fv_name, fv_count} heaps=:{hp_expression_heap, hp_var_heap} 
	# (expr_info_ptr, hp_expression_heap) = newPtr EI_Empty hp_expression_heap
	# expr = Var {var_name = fv_name, var_expr_ptr = expr_info_ptr, var_info_ptr = fv_info_ptr } 
	# hp_var_heap = writePtr fv_info_ptr (VI_Expression expr) hp_var_heap
	# heaps = { heaps & hp_var_heap = hp_var_heap, hp_expression_heap = hp_expression_heap } 		
	= (expr, {free_var & fv_count = fv_count + 1}, heaps)

buildBoundVarExprs :: ![FreeVar] !*Heaps -> (![Expression], ![FreeVar], !*Heaps)
buildBoundVarExprs [] heaps = ([], [], heaps)
buildBoundVarExprs [free_var:free_vars] heaps
	# (expr, free_var, heaps) = buildBoundVarExpr free_var heaps
	# (exprs, free_vars, heaps) = buildBoundVarExprs free_vars heaps
	= ([expr:exprs], [free_var:free_vars], heaps)


copyVar :: FreeVar !*Heaps -> (!FreeVar, !*Heaps)
copyVar var heaps=:{hp_var_heap}
	# (var_info_ptr, hp_var_heap) = newPtr VI_Empty hp_var_heap
	= ({var & fv_info_ptr = var_info_ptr}, {heaps & hp_var_heap = hp_var_heap})
		//---> ("copyVar", var, ptrToInt var_info_ptr)
copyVars vars heaps = mapSt copyVar vars heaps 

setVarInfo var=:{fv_info_ptr} var_info heaps=:{hp_var_heap}
	# hp_var_heap = writePtr fv_info_ptr var_info hp_var_heap
	= {heaps & hp_var_heap = hp_var_heap}
setVarInfos vars var_infos heaps 
	= fold2St setVarInfo vars var_infos heaps
clearVarInfos vars heaps 
	= setVarInfos vars (repeatn (length vars) VI_Empty) heaps

copyExpr :: !Expression !*Heaps -> (!Expression, !*Heaps)
copyExpr expr heaps=:{hp_var_heap, hp_expression_heap}
	#! state = 
		{	us_var_heap	= hp_var_heap
		,	us_symbol_heap	= hp_expression_heap
		,	us_opt_type_heaps = No
		,	us_cleanup_info	= []
		,	us_local_macro_functions = No			
		}
	#! info = 
		{	ui_handle_aci_free_vars	= LeaveThem
		,	ui_convert_module_n = -1
		,	ui_conversion_table = No
		}
	#! (expr, {us_var_heap, us_symbol_heap}) = unfold expr info state
	= (expr, {heaps & hp_var_heap = us_var_heap, hp_expression_heap = us_symbol_heap})
		//---> ("copy Expr")

mapExprSt :: !(Expression -> w:st -> u:(Expression, w:st)) !Expression w:st -> v:(Expression, w:st), [v<=w,u<=v]	
mapExprSt f (App app=:{app_args}) st
		# (app_args, st) = mapSt (mapExprSt f) app_args st
		= f (App { app & app_args = app_args }) st
				
mapExprSt f (Let lad=:{let_lazy_binds, let_strict_binds, let_expr}) st
	# (let_lazy_binds, st) = mapSt map_bind let_lazy_binds st
	# (let_strict_binds, st) = mapSt map_bind let_strict_binds st
	# (let_expr, st) = mapExprSt f let_expr st
	# lad =
		{ 	lad 
		& 	let_expr = let_expr
		, 	let_lazy_binds = let_lazy_binds
		, 	let_strict_binds = let_strict_binds
		}
	= f (Let lad) st
where
	map_bind b=:{lb_src} st
		# (lb_src, st) = mapExprSt f lb_src st
		= ({b & lb_src = lb_src}, st)

mapExprSt f (Selection a expr b) st
	# (expr, st) = mapExprSt f expr st
	= f (Selection a expr b) st
	
mapExprSt f (Update e1 x e2) st
	# (e1, st) = mapExprSt f e1 st
	# (e2, st) = mapExprSt f e2 st
	= f (Update e1 x e2) st

mapExprSt f (RecordUpdate x expr binds) st
	# (expr, st) = mapExprSt f expr st
	# (binds, st) = mapSt map_bind binds st
	= f (RecordUpdate x expr binds) st
where
	map_bind b=:{bind_src} st
		# (bind_dst, st) = mapExprSt f bind_src st
		= ({b & bind_src = bind_src}, st)	

mapExprSt f (TupleSelect x y expr) st
	# (expr, st) = mapExprSt f expr st
	= f (TupleSelect x y expr) st
	
mapExprSt f (Conditional cond=:{if_cond, if_then, if_else}) st
	# (if_cond, st) = mapExprSt f if_cond st
	# (if_then, st) = mapExprSt f if_then st
	# (if_else, st) = case if_else of
		(Yes x) 
			# (x, st) = mapExprSt f x st
			-> (Yes x, st)
		No  -> (No, st)	
	= f (Conditional {cond & if_cond = if_cond, if_then = if_then, if_else = if_else}) st
		
mapExprSt f (MatchExpr x y expr) st
	# (expr, st) = mapExprSt f expr st
	= f (MatchExpr x y expr) st

mapExprSt f (DynamicExpr dyn=:{dyn_expr}) st
	# (dyn_expr, st) = mapExprSt f dyn_expr st
	= f (DynamicExpr {dyn& dyn_expr = dyn_expr}) st 

mapExprSt f (Case c=:{case_expr, case_guards, case_default=case_default}) st
	# (case_expr, st) = mapExprSt f case_expr st
	# (case_guards, st) = map_patterns case_guards st
	# (case_default, st) = case case_default of 
		(Yes x) 
			# (x, st) = mapExprSt f x st
			-> (Yes x, st)
		No  -> (No, st)	
	# new_case = {c & case_expr=case_expr, case_guards=case_guards, case_default=case_default} 
	=  f (Case new_case) st 
where
	map_patterns (AlgebraicPatterns index pats) st
		# (pats, st) = mapSt map_alg_pattern pats st
		= (AlgebraicPatterns index pats, st) 
	map_patterns (BasicPatterns bt pats) st 
		# (pats, st) = mapSt map_basic_pattern pats st
		= (BasicPatterns bt pats, st)
	map_patterns (DynamicPatterns pats) st
		# (pats, st) = mapSt map_dyn_pattern pats st	
		= (DynamicPatterns pats, st) 
		
	map_alg_pattern pat=:{ap_expr} st 
		# (ap_expr, st) = mapExprSt f ap_expr st
		= ({pat & ap_expr = ap_expr}, st) 
	map_basic_pattern pat=:{bp_expr} st 
		# (bp_expr, st) = mapExprSt f bp_expr st
		= ({pat & bp_expr = bp_expr}, st) 
	map_dyn_pattern pat=:{dp_rhs} st 
		# (dp_rhs, st) = mapExprSt f dp_rhs	st
		= ({pat & dp_rhs = dp_rhs}, st) 

mapExprSt f expr st = f expr st		

				 
copyFunDef :: !FunDef !Index !Index !*Heaps -> (!FunDef, !*Heaps)
copyFunDef fun_def=:{fun_symb,fun_arity,fun_body,fun_info} fun_index group_index gs_heaps
	# (TransformedBody {tb_args, tb_rhs}) = fun_body

	# (fresh_arg_vars, gs_heaps) = copy_vars tb_args gs_heaps			
	# (copied_rhs, gs_heaps) = copyExpr tb_rhs gs_heaps
	
	# (copied_rhs, fresh_arg_vars, fresh_local_vars, gs_heaps) = 
		collect_local_vars copied_rhs fresh_arg_vars gs_heaps
		
	# gs_heaps = clearVarInfos tb_args gs_heaps
				
	# fun_def = 
		{ 	fun_def
		// & 	fun_index = fun_index
		//,	fun_symb = makeIdent "zzzzzzzzzzzz"
		&	fun_body = TransformedBody { tb_args = fresh_arg_vars, tb_rhs = copied_rhs }
		,	fun_info =
			{ 	fun_info
			& 	fi_group_index = group_index
			,	fi_local_vars = fresh_local_vars
			}			
		}
	= (fun_def, gs_heaps)
where
	copy_vars vars heaps
		# (fresh_vars, heaps) = copyVars vars heaps
		# infos = [VI_Variable fv_name fv_info_ptr\\ {fv_name,fv_info_ptr} <- fresh_vars]	 
		# heaps = setVarInfos vars infos heaps
	 	= (fresh_vars, heaps)
	 	
	collect_local_vars body_expr fun_arg_vars heaps=:{hp_var_heap, hp_expression_heap}
		# dummy_pds = {pds_module=NoIndex,pds_def=NoIndex}		
		#! cs =
	  		{ cos_error = {ea_file = stderr, ea_ok = True, ea_loc=[]}
	  		, cos_var_heap = hp_var_heap
	  		, cos_symbol_heap = hp_expression_heap	  		
	  		, cos_predef_symbols_for_transform = { predef_alias_dummy=dummy_pds, predef_and=dummy_pds, predef_or=dummy_pds }
			, cos_used_dynamics = {} //abort "error, please report to Martijn or Artem"
	  		}
		# (body_expr, fun_arg_vars, local_vars, {cos_symbol_heap, cos_var_heap}) = 
			determineVariablesAndRefCounts fun_arg_vars body_expr cs
		# heaps = { heaps & hp_var_heap = cos_var_heap, hp_expression_heap = cos_symbol_heap }
		= (body_expr, fun_arg_vars, local_vars, heaps)

// collect functions called in an expression 
collectCalls :: !Index !Expression -> [Index]
collectCalls current_module expr
	# symbidents = collect_expr_calls expr []
	= removeDup 
		[glob_object \\ 
			{symb_kind=SK_Function {glob_module,glob_object}} <- symbidents 
			| glob_module == current_module]
where
		
	collect_expr_calls (App app) rest = [app.app_symb:foldr collect_expr_calls rest app.app_args]
	collect_expr_calls (expr@exprs) rest = collect_expr_calls expr (foldr collect_expr_calls rest exprs)
	collect_expr_calls (Let li) rest = collect_expr_calls li.let_expr (foldr collect_letbind_calls (foldr collect_letbind_calls rest li.let_lazy_binds) li.let_strict_binds)
	collect_expr_calls (Case ci) rest = collect_expr_calls ci.case_expr (collect_casepatterns_calls ci.case_guards (foldOptional id collect_expr_calls ci.case_default rest))
	collect_expr_calls (Selection optgd expr sels) rest = collect_expr_calls expr (foldr collect_sel_calls rest sels)
	collect_expr_calls (Update expr1 sels expr2) rest = collect_expr_calls expr1 (foldr collect_sel_calls (collect_expr_calls expr2 rest) sels)
	collect_expr_calls (RecordUpdate gds expr binds) rest = collect_expr_calls expr (foldr collect_bind_calls rest binds)
	collect_expr_calls (TupleSelect ds i expr) rest = collect_expr_calls expr rest
	//collect_expr_calls (Lambda fvs expr) rest = collect_expr_calls expr rest
	collect_expr_calls (Conditional cond) rest = collect_expr_calls cond.if_cond (collect_expr_calls cond.if_then (foldOptional id collect_expr_calls cond.if_else rest))
	collect_expr_calls (MatchExpr ogds gds expr) rest = collect_expr_calls expr rest
	collect_expr_calls (DynamicExpr dyn) rest = collect_expr_calls dyn.dyn_expr (collect_tce_calls dyn.dyn_type_code rest)
	//collect_expr_calls (TypeCase tc) rest = collect_expr_calls tc.type_case_dynamic (foldr collect_dp_calls (foldOptional id collect_expr_calls rest) tc.type_case_patterns)
	collect_expr_calls (TypeCodeExpression tce) rest = collect_tce_calls tce rest
	collect_expr_calls _ rest = rest

	collect_letbind_calls lb rest = collect_expr_calls lb.lb_src rest
	
	collect_casepatterns_calls (AlgebraicPatterns gi aps) rest = foldr collect_ap_calls rest aps
	collect_casepatterns_calls (BasicPatterns gi bps) rest = foldr collect_bp_calls rest bps
	collect_casepatterns_calls (DynamicPatterns dps) rest = foldr collect_dp_calls rest dps
	collect_casepatterns_calls NoPattern rest = rest
	
	collect_ap_calls ap rest = collect_expr_calls ap.ap_expr rest
	collect_bp_calls bp rest = collect_expr_calls bp.bp_expr rest
	collect_dp_calls dp rest = collect_tce_calls dp.dp_type_code (collect_expr_calls dp.dp_rhs rest)
	
	collect_sel_calls (RecordSelection gds i) rest = rest
	collect_sel_calls (ArraySelection gds eip expr) rest = collect_expr_calls expr rest
	collect_sel_calls (DictionarySelection bv sels sip expr) rest = foldr collect_sel_calls (collect_expr_calls expr rest) sels
	
	collect_bind_calls b rest = collect_expr_calls b.bind_src rest
	
	collect_tce_calls (TCE_Constructor i tces) rest = foldr collect_tce_calls rest tces
	collect_tce_calls (TCE_Selector sels vip) rest = foldr collect_sel_calls rest sels
	collect_tce_calls _ rest = rest
	
	
makeIdent :: String -> Ident
makeIdent str = {id_name = str, id_info = nilPtr} 

makeIntExpr :: Int -> Expression
makeIntExpr value = BasicExpr (BVI (toString value))

makeStringExpr :: String !PredefinedSymbols -> Expression
makeStringExpr str predefs
	#! {pds_module, pds_def} = predefs.[PD_StringType]
	#! pds_ident = predefined_idents.[PD_StringType]
	#! type_symb = MakeTypeSymbIdent { glob_module = pds_module, glob_object = pds_def } pds_ident 0
	=  BasicExpr (BVS str)

makeListExpr :: [Expression] !PredefinedSymbols !*Heaps -> (Expression, !*Heaps)
makeListExpr [] predefs heaps
	= buildPredefConsApp PD_NilSymbol [] predefs heaps
makeListExpr [expr:exprs] predefs heaps 
	# (list_expr, heaps) = makeListExpr exprs predefs heaps 
	= buildPredefConsApp PD_ConsSymbol [expr, list_expr] predefs heaps

foldOptional no yes No = no
foldOptional no yes (Yes x) = yes x

transpose []             = []
transpose [[] : xss]     = transpose xss
transpose [[x:xs] : xss] = 
	[[x : [hd l \\ l <- xss]] : transpose [xs : [ tl l \\  l <- xss]]]

unzip3 [] = ([], [], [])
unzip3 [(x1,x2,x3):xs]
	# (x1s, x2s, x3s) = unzip3 xs
	= ([x1:x1s], [x2:x2s], [x3:x3s])
 
reportError name pos msg error
	= checkErrorWithIdentPos (newPosition name pos) msg error

(--) infixl 5 :: u:[a] .[a] -> u:[a] | Eq a
(--) x y = removeMembers x y 
