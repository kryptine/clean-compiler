implementation module generics

import StdEnv
import _aconcat
import hashtable
import checksupport
import checktypes
import check
from transform import Group
from type import buildCurriedType
import analtypes

:: *GenericState = {
	gs_modules				:: !*{#CommonDefs},
	gs_fun_defs				:: !*{# FunDef},
	gs_groups				:: !{!Group},
	gs_td_infos 			:: !*TypeDefInfos,
	gs_gtd_infos			:: !*GenericTypeDefInfos,
	gs_heaps				:: !*Heaps,
	gs_main_dcl_module_n	:: !Index,
	gs_first_fun			:: !Index,
	gs_last_fun				:: !Index,
	gs_first_group			:: !Index,
	gs_last_group			:: !Index,
	gs_predefs				:: !PredefinedSymbols,
	gs_error 				:: !*ErrorAdmin	
	}

:: GenericTypeDefInfo  
	= GTDI_Empty 							// no generic rep needed
	| GTDI_Generic GenericType				// generic representataion

:: GenericTypeDefInfos :== {# .{GenericTypeDefInfo}}

:: GenericType = {
	gt_type 				:: !AType,			// generic type representation
	gt_type_args			:: ![TypeVar],		// same as in td_info
	gt_iso					:: !DefinedSymbol,	// isomorphim function index 		
	gt_isomap_group			:: !Index, 			// isomap function group
	gt_isomap				:: !DefinedSymbol,	// isomap function for the type
 	gt_isomap_from			:: !DefinedSymbol,	// from-part of isomap
	gt_isomap_to			:: !DefinedSymbol 	// to-part 
	}

EmptyDefinedSymbol :== MakeDefinedSymbol {id_name="",id_info=nilPtr} NoIndex 0	
EmptyGenericType :== {
	gt_type 		= makeAType TE TA_Multi,
	gt_type_args	= [], 
	gt_iso 			= EmptyDefinedSymbol, 
	gt_isomap_group = NoIndex, 
	gt_isomap 		= EmptyDefinedSymbol,
	gt_isomap_from 	= EmptyDefinedSymbol,
	gt_isomap_to 	= EmptyDefinedSymbol
	}

:: IsoDirection = IsoTo | IsoFrom

instance toBool GenericTypeDefInfo where
	toBool GTDI_Empty 		= False
	toBool (GTDI_Generic _) 	= True

convertGenerics :: !{!Group} !Int !{#CommonDefs} !*{# FunDef} !*TypeDefInfos !*Heaps !*HashTable !*PredefinedSymbols !u:{# DclModule} !*ErrorAdmin 
	-> (!{!Group}, !{#CommonDefs}, !*{# FunDef}, !IndexRange, !*TypeDefInfos, !*Heaps, !*HashTable, !*PredefinedSymbols, !u:{# DclModule}, !*ErrorAdmin)
convertGenerics 
		groups main_dcl_module_n modules fun_defs td_infos heaps
		hash_table predefs dcl_modules error

	#! (fun_defs_size, fun_defs) = usize fun_defs 
	#! groups_size = size groups	

	#! (predef_size, predefs) = usize predefs
	#! (gs_predefs, predefs) = arrayCopyBegin predefs predef_size
	
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
								
	#! gs = {gs_modules = {m \\m <-: modules}, // unique copy
			gs_groups = groups, gs_fun_defs = fun_defs, 
			gs_td_infos = td_infos,
			gs_gtd_infos = gtd_infos, 
			gs_heaps = heaps,
			gs_main_dcl_module_n = main_dcl_module_n,
			gs_first_fun = fun_defs_size, gs_last_fun = fun_defs_size,
			gs_first_group = groups_size, gs_last_group = groups_size,
			gs_predefs = gs_predefs,
			gs_error = error} 
	
	#! (generic_types, gs) = collectGenericTypes gs
		//---> "*** collect generic types"
	//#! {gs_error} = gs  
	//| not gs_error.ea_ok
	//	= abort "collecting generic types failed"
	//#! gs = {gs & gs_error = gs_error}
			
	#! (instance_types, gs) = convertInstances gs
		//---> "*** build classes and bind instances"
		
	#! (td_indexes, gs) = collectGenericTypeDefs (generic_types ++ instance_types) gs	
		//---> "*** collect type definitions for which a generic representation must be created"
		
	#! (iso_funs, iso_groups, gs) = buildIsoFunctions td_indexes gs	
		//---> "*** build isomorphisms for type definitions"	
	#! (isomap_type_funs, isomap_type_groups, gs) = buildIsomapsForTypeDefs td_indexes gs	
		//---> "*** build maps for type definitions"	
	#! (isomap_gen_funs, isomap_gen_groups, gs) = buildIsomapsForGenerics gs 		
		//---> "*** build maps for generic function types"	
	#! (instance_funs, instance_groups, gs) = buildInstances gs
		//---> "*** build instances"	
	#! (star_funs, star_groups, gs) = buildKindConstInstances gs
		//---> "*** build shortcut instances for kind *"	

	// the order in the lists below is important! 
	// Indexes are allocated in that order.
	#! new_funs = iso_funs ++ isomap_type_funs ++ isomap_gen_funs ++ instance_funs ++ star_funs
	#! new_groups = iso_groups ++ isomap_type_groups ++ isomap_gen_groups ++ instance_groups ++ star_groups	
		//---> ("created isomaps", length isomap_funs, length isomap_groups)

	#! gs = addFunsAndGroups new_funs new_groups gs	
		//---> "*** add geenrated functions"
	#! gs = determineMemberTypes 0 0 gs
		//---> "*** determine types of member instances"	
	
	//| True
	//	= abort "-----------------\n"
				
	#! {gs_modules, gs_groups, gs_fun_defs, gs_td_infos, 
		gs_heaps,
		gs_error} = gs	
	
	#! {hte_symbol_heap} = hash_table
	#! cs = {
		cs_symbol_table = hte_symbol_heap, 
		cs_predef_symbols = predefs, 
		cs_error = gs_error, 
		cs_x= {
			x_needed_modules = 0,
			x_main_dcl_module_n = main_dcl_module_n, 
			x_is_dcl_module = False,
			x_type_var_position = 0
			}
		}

	# (common_defs, gs_modules) = gs_modules![main_dcl_module_n]
	# class_defs = { x \\ x <-: common_defs.com_class_defs } // make unique copy
	# {hp_type_heaps=hp_type_heaps=:{th_vars}, hp_var_heap} = gs_heaps
		
	# (class_defs, dcl_modules, new_type_defs, new_selector_defs, new_cons_defs, th_vars, hp_var_heap, cs) =
		createClassDictionaries 
			main_dcl_module_n 
			class_defs 
			dcl_modules 
			(size common_defs.com_type_defs) 
			(size common_defs.com_selector_defs) 
			(size common_defs.com_cons_defs) 
			th_vars hp_var_heap cs
		
	# gs_heaps = {gs_heaps & hp_var_heap = hp_var_heap, hp_type_heaps = {hp_type_heaps & th_vars = th_vars}} 

	# common_defs = { common_defs & 
		com_class_defs = class_defs, 
		com_type_defs = arrayPlusList common_defs.com_type_defs new_type_defs,
		com_selector_defs = arrayPlusList common_defs.com_selector_defs new_selector_defs,
		com_cons_defs = arrayPlusList common_defs.com_cons_defs new_cons_defs}
		
	# gs_modules = { gs_modules & [main_dcl_module_n] = common_defs } 
	# {cs_symbol_table, cs_predef_symbols, cs_error} = cs
	# hash_table = { hash_table & hte_symbol_heap = cs_symbol_table }	
	
	# index_range = {ir_from = gs.gs_first_fun, ir_to = gs.gs_last_fun}
		 			
	= (	gs_groups, gs_modules, gs_fun_defs, index_range, gs_td_infos, gs_heaps, hash_table, 
		cs_predef_symbols, dcl_modules, cs_error)

	
// for each generic instance
// - generate class and class member, if needed
// - rebind generic instance from generic to class
// - returns list of instance types for building generic representation
convertInstances :: !*GenericState	
	-> (![Type], !*GenericState)
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
		-> (![Type], !*{#ClassInstance}, !*GenericState)	
	convert_instance module_index instance_index instance_defs gs=:{gs_td_infos}

		#! (instance_def, instance_defs) = instance_defs ! [instance_index]
		| not instance_def.ins_is_generic
			= ([], instance_defs, {gs & gs_td_infos = gs_td_infos})
			
		// determine the kind of the instance type
		#! it_type = hd instance_def.ins_type.it_types
		#! (kind, gs_td_infos) = kindOfType it_type gs_td_infos
		#! gs = {gs & gs_td_infos = gs_td_infos}	

		// generate class and update the instance to point to the class		
		#! (_, gs) 			= buildClassDef instance_def.ins_class KindConst gs	
		#! (class_glob, gs) = buildClassDef instance_def.ins_class kind gs	
		#! ins_ident = instance_def.ins_ident
		#! ins_ident = { ins_ident & id_name = ins_ident.id_name +++ ":" +++ (toString kind)}
		#! instance_def = { instance_def & ins_class = class_glob, ins_ident = ins_ident }
		#! instance_defs = { instance_defs & [instance_index] = instance_def}

		| instance_def.ins_generate
			= ([it_type], instance_defs, gs)
			= ([], instance_defs, gs)


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
		# {gen_type={st_args, st_result}} = generic_defs . [generic_index]
		# (types, gs_modules) = collect_in_modules module_index (inc generic_index) gs_modules
		= ([at_type \\ {at_type} <- [st_result:st_args]] ++ types, gs_modules)	

/*
buildClasses :: !*GenericState -> !*GenericState
buildClasses gs=:{gs_modules} 
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
		# {gen_type={st_args, st_result}} = generic_defs . [generic_index]
		# (types, gs_modules) = collect_in_modules module_index (inc generic_index) gs_modules
		= ([at_type \\ {at_type} <- [st_result:st_args]] ++ types, gs_modules)	
*/
		 				
// find all types whose generic representation is needed
collectGenericTypeDefs :: ![Type] !*GenericState
	-> (![Global Index], !*GenericState)
collectGenericTypeDefs types gs
	# (td_indexes, gs) = collect_in_types types gs
	= (map fst td_indexes, gs)
where

	collect_in_types :: ![Type] !*GenericState  
		-> (![(Global Index, Int)], !*GenericState)
	collect_in_types [] gs = ([], gs)
	collect_in_types [type:types] gs
		# (td_indexes1, gs) = collect_in_type type gs
		# (td_indexes2, gs) = collect_in_types types gs
		= (merge_td_indexes td_indexes1 td_indexes2, gs)
		
	collect_in_type :: !Type !*GenericState 
		-> (![(Global Index, Int)], !*GenericState)
	collect_in_type 
			(TA type_symb_indet=:{type_index, type_name} args) 
			gs=:{gs_gtd_infos, gs_td_infos, gs_modules}
		# {glob_module, glob_object} = type_index	
		# (gtd_info, gs_gtd_infos) = gs_gtd_infos ! [glob_module, glob_object]
		| toBool gtd_info // already marked
			= ([], {gs & gs_gtd_infos = gs_gtd_infos})
		#! gs_gtd_infos = {gs_gtd_infos & [glob_module, glob_object] = GTDI_Generic EmptyGenericType}
			//---> ("collect in type " +++ type_name.id_name +++ ": " +++ 
			//		toString glob_module +++ " " +++ toString glob_object)						
		#! (type_def, gs_modules) = getTypeDef glob_module glob_object gs_modules
		#! (td_info, gs_td_infos) = gs_td_infos ! [glob_module, glob_object]
		# gs = {gs & gs_td_infos = gs_td_infos, gs_gtd_infos = gs_gtd_infos, gs_modules = gs_modules}
		# (td_indexes, gs) = collect_in_type_def_rhs glob_module type_def gs
		= (merge_td_indexes [(type_index, td_info.tdi_group_nr)] td_indexes, gs)				
	collect_in_type (arg --> res) gs
		#! (td_indexes1, gs) = collect_in_type arg.at_type gs
		#! (td_indexes2, gs) = collect_in_type res.at_type gs
		= (td_indexes1 ++ td_indexes2, gs)
	collect_in_type (cons_var :@: args) gs
		# types = [ at_type \\ {at_type} <- args] 
		= collect_in_types types gs				
	collect_in_type _ gs
		= ([], gs)
	
	collect_in_type_def_rhs :: !Index !CheckedTypeDef !*GenericState 
		-> (![(Global Index, Int)], !*GenericState)		 
	collect_in_type_def_rhs mod {td_rhs=(AlgType cons_def_symbols)} gs
		= collect_in_conses mod cons_def_symbols gs
	collect_in_type_def_rhs mod {td_rhs=(RecordType {rt_constructor})}	gs
		= collect_in_conses mod [rt_constructor] gs				
	collect_in_type_def_rhs mod {td_rhs=(SynType {at_type})}	gs			
		= collect_in_type at_type gs 
	collect_in_type_def_rhs mod {td_rhs=(AbstractType _), td_name, td_pos} gs=:{gs_error}				
		# gs_error = checkErrorWithIdentPos
				(newPosition td_name td_pos) 
				"cannot build generic type representation for an abstract type" 
				gs_error
		= ([], {gs & gs_error = gs_error})
	collect_in_type_def_rhs mod _	gs
		= abort "ERROR: unknown type def right hand side\n" 
	
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
		# (td_indexes1, gs) = collect_in_types (map (\x->x.at_type) st_args)  gs
		# (td_indexes2, gs) = collect_in_type st_result.at_type gs
		= (merge_td_indexes td_indexes1 td_indexes2, gs)
		 
	merge_td_indexes x y 
		= mergeBy (\(_,l) (_,r) ->l < r) x y 

buildIsoFunctions :: ![Global Index] !*GenericState
	-> (![FunDef], ![Group], !*GenericState)
buildIsoFunctions [] gs = ([], [], gs)
buildIsoFunctions [type_index:type_indexes] gs
	# (iso_funs1, iso_groups1, gs) = build_function type_index gs
	# (iso_funs2, iso_groups2, gs) = buildIsoFunctions type_indexes gs	 
	= (iso_funs1 ++ iso_funs2, iso_groups1 ++ iso_groups2, gs) 
where
	build_function {glob_module, glob_object} gs
		# (from_fun_index, 	from_group_index, gs) 	= newFunAndGroupIndex gs
		# (to_fun_index, 	to_group_index, gs) 	= newFunAndGroupIndex gs
		# (iso_fun_index, 	iso_group_index, gs) 	= newFunAndGroupIndex gs
			
		# {gs_gtd_infos, gs_modules, gs_predefs} = gs
		# (type_def=:{td_name}, gs_modules) = getTypeDef glob_module glob_object gs_modules 
		# (common_defs, gs_modules) = gs_modules ! [glob_module]		
		# generic_rep_type = buildGenericRepType type_def.td_rhs gs_predefs common_defs 
	
		# iso_def_sym = {
			ds_ident  = {id_name="iso:"+++type_def.td_name.id_name, id_info = nilPtr },
			ds_index  = iso_fun_index,
			ds_arity  = 0	
			}
	
		# from_def_sym = {
			ds_ident  = {id_name="iso_from:"+++type_def.td_name.id_name, id_info = nilPtr },
			ds_index  = from_fun_index,
			ds_arity  = 1	
			}
	
		# to_def_sym = {
			ds_ident  = {id_name="iso_to:"+++type_def.td_name.id_name, id_info = nilPtr },
			ds_index  = to_fun_index,
			ds_arity  = 1	
			}
		# gtd_info = GTDI_Generic { 
			gt_type 		= generic_rep_type,
			gt_type_args	= [atv_variable \\ {atv_variable} <- type_def.td_args], 
			gt_iso 			= iso_def_sym,
			gt_isomap_group	= NoIndex,
			gt_isomap		= EmptyDefinedSymbol,		
			gt_isomap_from	= EmptyDefinedSymbol,		
			gt_isomap_to	= EmptyDefinedSymbol		
			}
	
		# gs_gtd_infos = {gs_gtd_infos & [glob_module, glob_object] = gtd_info} 
		# gs = { gs & gs_gtd_infos = gs_gtd_infos, gs_modules = gs_modules }
	
		# (from_fun_def, gs) = buildIsoFrom from_def_sym from_group_index glob_module type_def gs	
		# (to_fun_def, gs) = buildIsoTo to_def_sym to_group_index glob_module type_def gs	
		# (iso_fun_def, gs) = 
			//buildUndefFunction iso_fun_index iso_group_index iso_name 1 gs_predefs gs_heaps	
			buildIsoRecord iso_def_sym iso_group_index from_def_sym to_def_sym gs	
	
		# funs = [ 
			from_fun_def, 
			to_fun_def, 
			iso_fun_def]
		# groups = [
			{group_members = [from_fun_index]}, 
			{group_members = [to_fun_index]}, 
			{group_members = [iso_fun_index]}]
	
		= (funs, groups, gs)
	
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
	= (funs, groups, gs)
where	

	fill_function_indexes :: !(Global Index) !*GenericState -> !*GenericState
	fill_function_indexes {glob_module, glob_object} gs=:{gs_gtd_infos}

		# (from_fun_index, gs) = newFunIndex gs
		# (to_fun_index, gs) = newFunIndex gs
		# (rec_fun_index, gs) = newFunIndex gs

		# (gs=:{gs_gtd_infos, gs_modules}) = gs
		# (type_def=:{td_name, td_arity}, gs_modules) = getTypeDef glob_module glob_object gs_modules
		# (GTDI_Generic gt, gs_gtd_infos) = gs_gtd_infos ! [glob_module, glob_object]

		# gtd_info = GTDI_Generic {gt & 
			gt_isomap_from 	= { 
				ds_ident = {id_name="isomap_from:"+++td_name.id_name, id_info=nilPtr}, 
				ds_index = from_fun_index, 
				ds_arity = (td_arity + 1)
				},
			gt_isomap_to 	= { 
				ds_ident = {id_name="isomap_to:"+++td_name.id_name, id_info=nilPtr}, 
				ds_index = to_fun_index, 
				ds_arity = (td_arity + 1)
				},
			gt_isomap 		= { 
				ds_ident = {id_name="isomap:"+++td_name.id_name, id_info=nilPtr}, 
				ds_index = rec_fun_index, 
				ds_arity = td_arity
				}
			}		
		# gs_gtd_infos = {gs_gtd_infos & [glob_module, glob_object] = gtd_info}		
		= {gs & gs_gtd_infos = gs_gtd_infos, gs_modules = gs_modules}			
	
	build_isomap_functions :: ![Global Index] !*GenericState
		-> (![FunDef], !*GenericState)		
	build_isomap_functions [] gs = ([], gs)
	build_isomap_functions [{glob_module, glob_object}:td_indexes] gs
		# (funs1, gs) = build_isomap_function glob_module glob_object gs
		# (funs2, gs) = build_isomap_functions td_indexes gs
		= (funs1 ++ funs2, gs)
	
	build_isomap_function module_index type_def_index gs

		# (group_index, gs)  = get_group module_index type_def_index gs

		# {gs_modules, gs_gtd_infos} = gs
		# (type_def=:{td_name}, gs_modules) = getTypeDef module_index type_def_index gs_modules
		
		# (GTDI_Generic {gt_isomap, gt_isomap_to, gt_isomap_from}, gs_gtd_infos) 
			= gs_gtd_infos![module_index, type_def_index]
		
		# gs = { gs & gs_gtd_infos = gs_gtd_infos, gs_modules = gs_modules } 

		# (from_fun_def, gs) = 
			buildIsomapFromTo IsoFrom gt_isomap_from group_index module_index type_def_index gs
		# (to_fun_def, gs) = 
			buildIsomapFromTo IsoTo gt_isomap_to group_index module_index type_def_index gs
		# (rec_fun_def, gs) = 
			buildIsomapForTypeDef gt_isomap group_index module_index type_def gt_isomap_from gt_isomap_to gs
		
		# funs = [ from_fun_def, to_fun_def, rec_fun_def ]		
		= (funs, gs)
			//---> from_fun_def 
		
	collect_groups :: !Index ![FunDef] !*{[Index]} -> !*{[Index]} 
	collect_groups first_group_index [] groups = groups
	collect_groups first_group_index [fun=:{fun_symb, fun_index, fun_info={fi_group_index}}:funs] groups
		# (group, groups) = groups ! [fi_group_index - first_group_index]
		# groups = {groups & [fi_group_index - first_group_index] = [fun_index:group]}
			//---> ("add fun " +++ fun_symb.id_name +++ " "+++ toString fun_index +++ 
			//		" to group " +++ toString fi_group_index) 
		= collect_groups first_group_index funs groups 

	get_group :: !Index  !Index !*GenericState 
		-> (!Index, !*GenericState)
	get_group module_index type_def_index gs=:{gs_gtd_infos}
		#! gtd_info = gs_gtd_infos . [module_index, type_def_index]
		# (GTDI_Generic gt) = gtd_info
		| gt.gt_isomap_group <> NoIndex // group index already allocated
			= (gt.gt_isomap_group, gs)
					
		# (group_index, gs=:{gs_td_infos, gs_gtd_infos}) 
			= newGroupIndex {gs & gs_gtd_infos = gs_gtd_infos}
				
		# (type_def_info, gs_td_infos) = gs_td_infos ! [module_index, type_def_index]
		# gs_gtd_infos = update_group group_index type_def_info.tdi_group gs_gtd_infos				
		= (group_index, { gs & gs_gtd_infos = gs_gtd_infos, gs_td_infos = gs_td_infos})
			//---> ("type group number of type " +++ toString module_index +++ " " +++ 
			//		toString type_def_index +++ " is " +++ toString type_def_info.tdi_group_nr)

	update_group :: !Index ![Global Index] !*GenericTypeDefInfos -> !*GenericTypeDefInfos
	update_group group_index [] gtd_infos = gtd_infos	
	update_group group_index [{glob_module, glob_object}:type_def_global_indexes] gtd_infos
		# (gtd_info, gtd_infos) = gtd_infos ! [glob_module, glob_object]
		# (GTDI_Generic gt) = gtd_info
		| gt.gt_isomap_group <> NoIndex 
			= abort "sanity check: updating already updated group\n"
		# gtd_info = GTDI_Generic {gt & gt_isomap_group = group_index }
		# gtd_infos = {gtd_infos & [glob_module, glob_object] = gtd_info}
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
		# (generic_def=:{gen_name, gen_type, gen_arity}, generic_defs) = generic_defs ! [generic_index] 		
		# (fun_index, group_index, gs) = newFunAndGroupIndex gs 		
		# def_sym = {
			ds_ident = {id_name="isomap:"+++gen_name.id_name, id_info = nilPtr}, 
			ds_index = fun_index, 
			ds_arity = gen_arity
			}
		# generic_defs = {generic_defs & [generic_index] = {generic_def & gen_isomap = def_sym}}				
		# (fun_def, gs) = buildIsomapForGeneric def_sym group_index generic_def gs
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
		| not instance_def.ins_generate
			= ([], [], instance_defs, gs)

		# {ins_class, ins_generic} = instance_def				
		# (class_def, gs_modules) = getClassDef ins_class.glob_module ins_class.glob_object.ds_index gs_modules
		# (member_def, gs_modules) = getMemberDef ins_class.glob_module class_def.class_members.[0].ds_index gs_modules
		# (generic_def, gs_modules) = getGenericDef ins_generic.glob_module ins_generic.glob_object gs_modules 
		# it_type = hd instance_def.ins_type.it_types

		# (fun_index, group_index, gs) = newFunAndGroupIndex {gs & gs_modules=gs_modules}
		# fun_def_sym = {
			ds_ident = instance_def.ins_ident, 
			ds_index = fun_index, 
			ds_arity = member_def.me_type.st_arity
			}
						
		# (fun_def, gs) = build_dummy_instance fun_def_sym group_index gs	
		//# (fun_def, gs) = buildInstance fun_def_sym group_index instance_def generic_def gs

		# instance_def = { instance_def & ins_members = {fun_def_sym} }		
		# instance_defs = {instance_defs & [instance_index] = instance_def} 
		= ([fun_def], [{group_members = [fun_index]}], instance_defs, gs)
		
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
	build_modules module_index gs=:{gs_modules}

		#! num_modules = size gs_modules
		| module_index == num_modules
			= ([], [], {gs & gs_modules = gs_modules})					
		# (new_funs, new_groups, instance_defs, gs) =
			build_instances module_index 0 {gs & gs_modules = gs_modules}
		# (funs, groups, gs) = build_modules (inc module_index) gs
		# {gs_modules} = gs

		// add instances 
		# (common_defs=:{com_instance_defs}, gs_modules) = gs_modules ! [module_index]		
		# com_instance_defs = arrayPlusList com_instance_defs instance_defs		
		# gs_modules = { gs_modules & [module_index] = {common_defs & com_instance_defs = com_instance_defs}} 
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
		
		| not (/*ins_generate &&*/ ins_is_generic)
			= ([], [], [], {gs & gs_td_infos = gs_td_infos, gs_modules = gs_modules, gs_heaps = gs_heaps})

		# it_type = hd ins_type.it_types
		#! (kind, gs_td_infos) = kindOfType it_type gs_td_infos
		| kind == KindConst
			= ([], [], [], { gs & gs_td_infos = gs_td_infos, gs_modules = gs_modules, gs_heaps = gs_heaps})

		# (generic_def, gs_modules) = getGenericDef ins_generic.glob_module ins_generic.glob_object gs_modules
		# (ok, class_def_sym) = getGenericClassForKind generic_def KindConst
		| not ok
			= abort "no class for kind *"			
		# (class_def, gs_modules) = getClassDef ins_generic.glob_module class_def_sym.ds_index gs_modules 
		# (member_def, gs_modules) = getMemberDef ins_generic.glob_module class_def.class_members.[0].ds_index gs_modules 	

		# (new_ins_type, gs_heaps) = 
			build_instance_type ins_type kind {glob_module=ins_generic.glob_module, glob_object=class_def_sym} gs_heaps

		# gs = {gs & gs_modules=gs_modules, gs_td_infos = gs_td_infos, gs_heaps = gs_heaps}
		# (fun_index, group_index, gs) = newFunAndGroupIndex gs
		# fun_def_sym = {
			ds_ident = class_def.class_name, // kind star name 
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
			buildKindConstInstance fun_def_sym group_index ins_generic.glob_module generic_def_sym kind gs

		# new_instance_def = {
			ins_class 		= {glob_module = ins_generic.glob_module, glob_object = class_def_sym},	
			ins_ident 		= class_def.class_name,	
			ins_type  		= new_ins_type,
			ins_members 	= {fun_def_sym},
			ins_specials 	= SP_None,
			ins_pos			= ins_pos, 
			ins_is_generic	= True, 
			ins_generate	= False,
			ins_generic 	= ins_generic
			}
			//---> fun_def

		= ([fun_def], [{group_members = [fun_index]}], [new_instance_def], gs)
		
	build_dummy_instance fun_def_sym group_index gs=:{gs_predefs, gs_heaps}
		# (fun_def, gs_heaps) = buildUndefFunction fun_def_sym group_index gs_predefs gs_heaps
		= (fun_def, {gs & gs_heaps = gs_heaps})
		
	build_instance_type ins_type=:{it_vars, it_types, it_context} (KindArrow kinds) class_glob_def_sym heaps		
		# type_var_names = ["a" +++ toString i \\ i <- [1 .. (length kinds) - 1]]
		# (type_vars, heaps) = mapSt buildTypeVar type_var_names heaps
		# type_var_types = map TV type_vars 	
		# new_type_args = map (\t->makeAType t TA_Multi) type_var_types

		# (TA type_symb_ident=:{type_arity} type_args) = hd it_types		
		# new_type = TA	{type_symb_ident & type_arity = type_arity + length new_type_args} (type_args ++ new_type_args)
		
		# (new_contexts, heaps) = mapSt (build_type_context class_glob_def_sym) type_var_types heaps
		
		# new_ins_type = { ins_type & 
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
		# type_context = {
		
			tc_class = class_glob_def_sym,
			tc_types = [type],
			tc_var	 = var_info_ptr
			}
		= (type_context, {heaps & hp_var_heap = hp_var_heap})	
									
// for all generic instances determine and set types
// of their functions
determineMemberTypes :: !Index !Index !*GenericState	
	-> !*GenericState
determineMemberTypes module_index ins_index 
		gs=:{gs_modules, gs_fun_defs, gs_heaps=gs_heaps=:{hp_var_heap, hp_type_heaps}}
	# (num_modules, gs_modules) = usize gs_modules
	| module_index == num_modules
		= {gs & gs_modules = gs_modules}
	# (common_defs=:{com_instance_defs}, gs_modules) = gs_modules![module_index]		
	| ins_index == size com_instance_defs
		= determineMemberTypes (inc module_index) 0 {gs & gs_modules = gs_modules} 		
	# (instance_def, com_instance_defs) = com_instance_defs![ins_index]
	| not instance_def.ins_is_generic		
		= determineMemberTypes module_index (inc ins_index) {gs & gs_modules = gs_modules}
	
	# {ins_class, ins_type, ins_members} = instance_def
	# (class_def, gs_modules) = getClassDef ins_class.glob_module ins_class.glob_object.ds_index gs_modules
	# (member_def, gs_modules) = getMemberDef ins_class.glob_module class_def.class_members.[0].ds_index gs_modules
	# {me_type, me_class_vars}  = member_def
		
		
		
	// determine type of the member instance		
	# (symbol_type, _, hp_type_heaps) = 
		determineTypeOfMemberInstance me_type me_class_vars ins_type SP_None hp_type_heaps
	# (st_context, hp_var_heap) = initializeContextVariables symbol_type.st_context hp_var_heap
	# symbol_type = {symbol_type & st_context = st_context}			
	
	// update the instance function
	# fun_index = ins_members.[0].ds_index
	# (fun_def, gs_fun_defs) = gs_fun_defs![fun_index]
	# fun_def = {fun_def & fun_type = (Yes symbol_type)} 

	# gs_fun_defs = {gs_fun_defs & [fun_index] = fun_def}
	
	# gs = { gs & 
		gs_modules = gs_modules, 
		gs_fun_defs = gs_fun_defs,
		gs_heaps = {gs_heaps & hp_type_heaps = hp_type_heaps, hp_var_heap = hp_var_heap} 
		}

	= determineMemberTypes module_index (inc ins_index) gs

kindOfType :: !Type !*TypeDefInfos -> (!TypeKind, !*TypeDefInfos)
kindOfType (TA type_cons args) td_infos
	# {glob_object,glob_module} = type_cons.type_index
	# ({tdi_kinds}, td_infos) = td_infos![glob_module,glob_object] 
	# kinds = drop (length args) tdi_kinds	
	| isEmpty kinds 
		= (KindConst, td_infos) 
		= (KindArrow (kinds ++ [KindConst]), td_infos)
kindOfType (TV _) td_infos = (KindConst, td_infos)
kindOfType (GTV _) td_infos = (KindConst, td_infos)
kindOfType (TQV _) td_infos = (KindConst, td_infos)
kindOfType _ td_infos = (KindConst, td_infos)
			
buildClassDef :: /*generic*/!(Global DefinedSymbol) !TypeKind !*GenericState
	-> (/*class*/!(Global DefinedSymbol), !*GenericState)	
buildClassDef 
		generic_glob=:{glob_module, glob_object={ds_ident, ds_index}} 
		kind 
		gs=:{gs_modules, gs_heaps=gs_heaps=:{hp_type_heaps=hp_type_heaps=:{th_vars}, hp_var_heap}}
	#! (common_defs=:{com_generic_defs, com_class_defs, com_member_defs}, gs_modules) = gs_modules![glob_module]
	#! (generic_def=:{gen_name=gen_name=:{id_name}, gen_type, gen_pos, gen_classes}, com_generic_defs) = com_generic_defs![ds_index]
	
	// check if the class is already created
	# (found, class_symbol) = getGenericClassForKind generic_def kind
	| found 
		= (	{glob_module = glob_module, glob_object = class_symbol}, 
			{gs & gs_modules = gs_modules}) 

	#! id_name = id_name +++ ":" +++ (toString kind) 
	#! ident = {id_name = id_name, id_info = nilPtr}

	// allocate new class and member
	#! class_index = size com_class_defs
	#! class_ds = {ds_ident = ident, ds_index = class_index, ds_arity = 1}
	#! glob_class = {glob_module = glob_module, glob_object = class_ds}	       
	#! member_index = size com_member_defs

	// class argument
	#! (tv_info_ptr, th_vars) = newPtr TVI_Empty th_vars 
	#! class_arg = {tv_name = {id_name = "class_var", id_info = nilPtr}, tv_info_ptr = tv_info_ptr}	

	// member
	#! (type_ptr, hp_var_heap) = newPtr VI_Empty hp_var_heap 
	#! (tc_var_ptr, hp_var_heap) = newPtr VI_Empty hp_var_heap  
	#! type_context = { 
		tc_class = glob_class,
		tc_types = [ TV class_arg ], 
		tc_var = tc_var_ptr 				// ???
		}
	#! hp_type_heaps = {hp_type_heaps & th_vars = th_vars}	
	#! (member_type, hp_type_heaps) = buildMemberType generic_def kind class_arg hp_type_heaps
	#! member_type = { member_type & st_context = [type_context : gen_type.st_context] }
	#! member_def = {
		me_symb = ident,
		me_class = {glob_module = glob_module, glob_object = class_index},
		me_offset = 0,
		me_type = member_type,
		me_type_ptr = type_ptr,				// empty
		me_class_vars = [class_arg], 		// the same variable as in the class
		me_pos = gen_pos,
		me_priority = NoPrio
		}
	
	// class
	#! class_member = {ds_ident=ident, ds_index = member_index, ds_arity = member_def.me_type.st_arity}
	#! class_dictionary = { 
		ds_ident = {id_name = id_name, id_info = nilPtr}, 
		ds_arity = 0, 
		ds_index = NoIndex/*index in the type def table, filled in later*/ 
		}
	#! class_def = { 
		class_name = ident, 
		class_arity = 1,  
		class_args = [class_arg],
	    class_context = [], 
	    class_pos = gen_pos, 
	    class_members = createArray 1 class_member, 
	    class_cons_vars = case kind of KindConst -> 0; _ -> 1,
	    class_dictionary = class_dictionary
	    }	 
	    
	#! com_class_defs = append_array com_class_defs class_def
	#! com_member_defs = append_array com_member_defs member_def	
	#! generic_def = {generic_def & gen_classes = [{gci_kind = kind, gci_class = class_ds} : gen_classes] }
	#! com_generic_defs = {(copy_array com_generic_defs) & [ds_index] = generic_def}
	#! common_defs = {common_defs & 
		com_class_defs = com_class_defs, 
		com_generic_defs = com_generic_defs, 
		com_member_defs = com_member_defs}	
	#! gs_modules = {gs_modules & [glob_module] = common_defs} 
	#! gs = { gs &
		gs_modules = gs_modules,
		gs_heaps = { gs_heaps & hp_type_heaps = hp_type_heaps, hp_var_heap = hp_var_heap}
		}		
	= (glob_class, gs) 
		//---> ("generated class " +++ id_name)
where
	append_array array el 
//1.3
		= arrayConcat array {el}
//3.1
/*2.0
		= r2
	where
		r2={r1 & [s]=el}
		r1={r0 & [i]=array.[i] \\ i<-[0..s-1]} 	
		r0 = _createArray (s+1)
		s = size array		
0.2*/
	copy_array array = {x \\ x <-: array}	

// create an instance of a polykinded (generic) type of a given kind
buildMemberType :: !GenericDef !TypeKind !TypeVar !*TypeHeaps -> (!SymbolType, !*TypeHeaps)
buildMemberType generic_def=:{gen_name,gen_type,gen_args} kind class_var type_heaps 
	// each generic type variable is replaced by the class var
	#! class_vars = repeatn (length gen_args) class_var		

	// each free type variable is substitued by a fresh var
	#! (fresh_st_vars, type_heaps) = mapSt subst_fresh_type_var gen_type.st_vars type_heaps 

	// each generic variable is substituted by generic application
	#! (gen_type, type_heaps) = generate_member_type gen_type gen_args kind class_vars type_heaps

	// run the real susbstitution
	#! (fresh_st_args, type_heaps) = substitute gen_type.st_args type_heaps
	#! (fresh_st_result, type_heaps) = substitute gen_type.st_result type_heaps	
	
	#! member_type = {gen_type &
		st_vars = gen_type.st_vars ++ fresh_st_vars,
		st_args = fresh_st_args,
		st_result = fresh_st_result
		}

	= (member_type, type_heaps)
		---> ("member type ", member_type)
where		
	generate_member_type :: !SymbolType ![TypeVar] !TypeKind ![TypeVar] !*TypeHeaps -> (!SymbolType, !*TypeHeaps)
	generate_member_type 
			gen_type gen_args 
			kind class_vars type_heaps
		#! (gen_type_varss, type_heaps) = subst_generic_vars gen_args class_vars kind type_heaps
		#! (fresh_st_args, type_heaps) = substitute gen_type.st_args type_heaps
		#! (fresh_st_result, type_heaps) = substitute gen_type.st_result type_heaps	

		#! gen_type_varss = transpose gen_type_varss
		#! (arg_types, type_heaps) = generate_args gen_type gen_args kind gen_type_varss type_heaps
		#! generated_symbol_type = {gen_type & 
			st_vars = (removeDup class_vars) ++ (flatten gen_type_varss), 
			st_args = arg_types ++ fresh_st_args,
			st_arity = gen_type.st_arity + (length arg_types), 
			st_result = fresh_st_result
			}
		= (generated_symbol_type, type_heaps)
			//---> ("generated member type", type)
			
	subst_generic_vars :: ![TypeVar] ![TypeVar] !TypeKind !*TypeHeaps -> (![[TypeVar]], !*TypeHeaps) 
	subst_generic_vars [] [] _ type_heaps = ([], type_heaps)
	subst_generic_vars [type_var:type_vars] [class_var:class_vars] kind type_heaps
		# (new_type_vars, type_heaps) = subst_generic_var type_var class_var kind type_heaps
		# (new_type_varss, type_heaps) = subst_generic_vars type_vars class_vars kind type_heaps
		= ([new_type_vars : new_type_varss], type_heaps)
	subst_generic_vars _ _ _ type_heaps 
		= abort "inconsistent number of type variables to be substituted"
	
	// create substitution of variable for cons var application
	// a => (t a1 .. ak), where k is arity of kind	
	subst_generic_var :: !TypeVar !TypeVar !TypeKind !*TypeHeaps -> (![TypeVar], !*TypeHeaps)
	subst_generic_var type_var type_cons_var KindConst type_heaps=:{th_vars}
		# th_vars = th_vars <:= (type_var.tv_info_ptr, TVI_Type (TV type_cons_var))
		= ([], {type_heaps & th_vars = th_vars})
			//---> ("subst var for kind *", type_var, type_cons_var) 		
	subst_generic_var type_var type_cons_var kind=:(KindArrow kinds) type_heaps=:{th_vars}
		# (new_vars, th_vars) = fresh_type_vars ((length kinds) - 1) type_var th_vars
		# type = (CV type_cons_var) :@: (map (\tv -> makeAType (TV tv) TA_Multi) new_vars)
		# th_vars = th_vars <:= (type_var.tv_info_ptr, TVI_Type type)
		= (new_vars, {type_heaps & th_vars = th_vars})
			//---> ("subst var for kind " +++ toString kind, type_var, type) 		
				 										
	fresh_type_vars :: !Int !TypeVar !*TypeVarHeap -> (![TypeVar], !*TypeVarHeap)
	fresh_type_vars num type_var th_vars
		= mapSt (\i st->fresh_var i type_var st) [1..num] th_vars
		where 
			fresh_var i type_var th_vars
				# id_name = type_var.tv_name.id_name +++ "_" +++ (toString i)
				# (tv_info_ptr, th_vars) = newPtr TVI_Empty th_vars 
				# var = {tv_name = {id_name = id_name, id_info = nilPtr}, tv_info_ptr = tv_info_ptr}	
				= (var, th_vars)

	subst_fresh_type_var :: !TypeVar !*TypeHeaps -> (!TypeVar, !*TypeHeaps) 
	subst_fresh_type_var type_var=:{tv_name,tv_info_ptr} type_heaps=:{th_vars}
		# (new_tv_info_ptr, th_vars) = newPtr TVI_Empty th_vars 
		# new_type_var = {tv_name={id_name=tv_name.id_name,id_info=nilPtr}, tv_info_ptr = new_tv_info_ptr }
		//# th_vars = writePtr tv_info_ptr (TVI_Type (TV new_type_var)) th_vars
		# th_vars = th_vars <:= (tv_info_ptr, TVI_Type (TV new_type_var))
		= (new_type_var, {type_heaps & th_vars = th_vars})

	// generate additional arguments that appear due to lifting
	generate_args :: !SymbolType ![TypeVar] !TypeKind ![[TypeVar]] !*TypeHeaps -> (![AType], !*TypeHeaps)				
	generate_args gen_type gen_args KindConst _ type_heaps 
		= ([], type_heaps)
	generate_args gen_type gen_args (KindArrow kinds) type_varss type_heaps
		= generate gen_type gen_args (init kinds) type_varss type_heaps
	where
		generate gen_type gen_args [] [] type_heaps = ([], type_heaps)
		generate gen_type gen_args [kind:kinds] [type_vars:type_varss] type_heaps
			# (symbol_type, type_heaps) = generate_member_type gen_type gen_args kind type_vars type_heaps
				//---> ("generate arg for kind " +++ toString kind, type_vars)
			# type = curry_symbol_type symbol_type					
			# (types, type_heaps) = generate gen_type gen_args kinds type_varss type_heaps
			= ([type:types], type_heaps)
		generate gen_type gen_args kinds type_varss type_heaps 
			= abort "inconsistent kind and type var lists"   

	curry_symbol_type :: SymbolType -> AType 
	curry_symbol_type {st_args, st_result} 
		#(type, _, _) = buildCurriedType st_args st_result TA_Multi [] 0
		= type
		 
buildGenericRepType :: !TypeRhs !PredefinedSymbols !CommonDefs 
	-> AType
buildGenericRepType (AlgType alts) predefs common_defs
	= build_sum alts predefs common_defs.com_cons_defs
where
	build_sum :: ![DefinedSymbol] !PredefinedSymbols !{#ConsDef} -> !AType
	build_sum [] predefs cons_defs = abort "no alternatives in typedef"
	build_sum [{ds_index}] predefs cons_defs
		#  cons_args = cons_defs.[ds_index].cons_type.st_args		
		= buildProductType cons_args predefs 
	build_sum alts predefs cons_defs 
		# (l,r) = splitAt ((length alts) / 2) alts 
		= buildATypeEITHER (build_sum l predefs cons_defs) (build_sum r predefs cons_defs) predefs
			
buildGenericRepType (RecordType {rt_constructor={ds_index}}) predefs common_defs
	# {cons_type={st_args}} = common_defs . com_cons_defs . [ds_index]
	= buildProductType st_args predefs

buildGenericRepType (SynType type) predefs common_defs
	= type // is that correct ???

buildGenericRepType (AbstractType _) predefs common_defs
	= abort "can not create generic representation of an abstract type" 
		
buildGenericRepType _ predefs cons_defs 
	= abort "cannot generate generic type represenation of this type"

			
buildIsoRecord :: !DefinedSymbol !Int !DefinedSymbol !DefinedSymbol !*GenericState
	-> (!FunDef, !*GenericState)
buildIsoRecord 
		def_sym group_index from_fun to_fun 
		gs=:{gs_heaps, gs_main_dcl_module_n, gs_predefs}
	# (from_expr, gs_heaps) 	= buildFunApp gs_main_dcl_module_n from_fun [] gs_heaps
	# (to_expr, gs_heaps) 		= buildFunApp gs_main_dcl_module_n to_fun [] gs_heaps	
	# (iso_expr, gs_heaps) 		= buildISO to_expr from_expr gs_predefs gs_heaps
	# fun_def = makeFunction def_sym group_index [] iso_expr No [] [from_fun.ds_index, to_fun.ds_index]					
	= (fun_def, {gs & gs_heaps = gs_heaps})
where
	build_fun_expr mod_index fun_def heaps=:{hp_expression_heap}
		# (expr_info_ptr, hp_expression_heap) = newPtr EI_Empty hp_expression_heap
		# global_index = {glob_module = mod_index/*gs_maindcl_module_n???*/, glob_object = fun_def.fun_index}
		# fun_symb = {
			symb_name = fun_def.fun_symb, 
			symb_kind = SK_Function global_index, 
			symb_arity = 0 //fun_def.fun_arity 
			}
		# fun_expr = App {app_symb = fun_symb, app_args = [], app_info_ptr = expr_info_ptr}	
		= (fun_expr, {heaps & hp_expression_heap = hp_expression_heap})

// convert a type to ot's generic representation
buildIsoTo :: !DefinedSymbol !Int !Int !CheckedTypeDef !*GenericState
	-> (!FunDef, !*GenericState)
buildIsoTo 
		def_sym group_index type_def_mod 
		type_def=:{td_rhs, td_name, td_index} 
		gs=:{gs_heaps, gs_predefs}
	# (arg_expr, arg_var, gs_heaps) = buildVarExpr "x" gs_heaps 
	# (body_expr, free_vars, gs_heaps) = build_body type_def_mod td_index td_rhs arg_expr gs_predefs gs_heaps	
	# fun_def = makeFunction def_sym group_index [arg_var] body_expr No free_vars []	
	= (fun_def, {gs & gs_heaps = gs_heaps})
		//---> fun_def
where
	build_body :: !Int !Int !TypeRhs !Expression !PredefinedSymbols !*Heaps 
		-> (!Expression, ![FreeVar], !*Heaps)
 	build_body type_def_mod type_def_index (AlgType def_symbols) arg_expr predefs heaps
		= build_body1 type_def_mod type_def_index def_symbols arg_expr predefs heaps
	
	build_body type_def_mod type_def_index (RecordType {rt_constructor}) arg_expr predefs heaps		
		= build_body1 type_def_mod type_def_index [rt_constructor] arg_expr predefs heaps

	build_body type_def_mod type_def_index (AbstractType _) arg_expr predefs heaps
		= abort "cannot build isomorphisms for an abstract type\n" 			 	
	build_body type_def_mod type_def_index _ arg_expr predefs heaps
		= abort "building isomorphisms for this type is not supported\n"
	
	build_body1 type_def_mod type_def_index def_symbols arg_expr predefs heaps
		# (case_alts, free_vars, heaps) = 
			build_alts 0 (length def_symbols) type_def_mod def_symbols predefs heaps
		# case_patterns = AlgebraicPatterns {glob_module = type_def_mod, glob_object = type_def_index} case_alts
		# (case_expr, heaps) = buildCaseExpr arg_expr case_patterns heaps
		= (case_expr, free_vars, heaps)	
			//---> (free_vars, case_expr)	
				
	build_alts :: !Int !Int !Int ![DefinedSymbol] PredefinedSymbols !*Heaps 
		-> ([AlgebraicPattern], [FreeVar], !*Heaps)
	build_alts i n type_def_mod [] predef heaps = ([], [], heaps) 
	build_alts i n type_def_mod [def_symbol:def_symbols] predefs heaps
		# (alt, fvs, heaps) = build_alt i n type_def_mod def_symbol predefs heaps
		# (alts, free_vars, heaps) =  build_alts (i+1) n type_def_mod def_symbols predefs heaps 		
		= ([alt:alts], fvs ++ free_vars, heaps)

	build_alt :: !Int !Int !Int !DefinedSymbol PredefinedSymbols !*Heaps 
		-> (AlgebraicPattern, [FreeVar], !*Heaps)
	build_alt i n type_def_mod def_symbol=:{ds_ident, ds_arity} predefs heaps		
		# names = ["x" +++ toString (i+1) +++ toString k \\ k <- [1..ds_arity]]
		# (var_exprs, vars, heaps) = buildVarExprs names heaps 
		# (expr, heaps) = build_prod var_exprs predefs heaps
		# (expr, heaps) = build_sum i n expr predefs heaps
				
		# alg_pattern = {
			ap_symbol = {glob_module = type_def_mod, glob_object = def_symbol},
			ap_vars = vars,
			ap_expr = expr,
			ap_position = NoPos
			}
		= (alg_pattern, vars, heaps)

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
		type_def=:{td_rhs, td_name, td_index} 
		gs=:{gs_predefs, gs_heaps}
	# (body_expr, free_vars, gs_heaps) = build_body type_def_mod td_rhs gs_predefs gs_heaps
	# [arg_var: free_vars] = free_vars	
	# fun_def = makeFunction def_sym group_index [arg_var] body_expr No free_vars []	
	= (fun_def, {gs & gs_heaps = gs_heaps} )
		//---> fun_def
where	
	build_body :: !Int !TypeRhs !PredefinedSymbols !*Heaps 
		-> (!Expression, ![FreeVar], !*Heaps)
 	build_body type_def_mod (AlgType def_symbols) predefs heaps
		= build_sum type_def_mod def_symbols predefs heaps
	build_body type_def_mod (RecordType {rt_constructor}) predefs heaps				
		= build_sum type_def_mod [rt_constructor] predefs heaps	
	build_body type_def_mod (AbstractType _) predefs heaps
		= abort "cannot build isomorphisms for an abstract type\n" 			 	
	build_body type_def_mod _ predefs heaps
		= abort "builing isomorphisms for this is not supported\n"

	build_sum :: !Index [DefinedSymbol] !PredefinedSymbols !*Heaps
		-> (!Expression, ![FreeVar], !*Heaps)
	build_sum type_def_mod [] predefs heaps
		= abort "algebraic type with no constructors!\n"
	build_sum type_def_mod [def_symbol] predefs heaps
		# (cons_app_expr, cons_args, heaps) = build_cons_app type_def_mod def_symbol heaps
		# (alt_expr, free_vars, heaps) = build_prod cons_app_expr cons_args predefs heaps 
		= (alt_expr, free_vars, heaps)
	build_sum type_def_mod def_symbols predefs heaps
		# (var_expr, var, heaps) = buildVarExpr "e" heaps
		# (left_def_symbols, right_def_symbols) = splitAt ((length def_symbols) /2) def_symbols
	
		# (left_expr, left_vars, heaps) = build_sum type_def_mod left_def_symbols predefs heaps
		# (right_expr, right_vars, heaps) = build_sum type_def_mod right_def_symbols predefs heaps
	
		# (case_expr, heaps) = 
			buildCaseEITHERExpr var_expr (hd left_vars, left_expr) (hd right_vars, right_expr) predefs heaps
		# vars = [var : left_vars ++ right_vars]
		= (case_expr, vars, heaps)
	
	build_prod :: !Expression ![FreeVar] !PredefinedSymbols !*Heaps
		-> (!Expression, ![FreeVar], !*Heaps)
	build_prod expr [] predefs heaps
		# (var_expr, var, heaps) = buildVarExpr "x" heaps 
		# (case_expr, heaps) = buildCaseUNITExpr var_expr expr predefs heaps	
		= (case_expr, [var], heaps)
	build_prod expr [cons_arg_var] predefs heaps
		= (expr, [cons_arg_var], heaps)	
	build_prod expr cons_arg_vars predefs heaps
		# (var_expr, var, heaps) = buildVarExpr "p" heaps
		# (left_vars, right_vars) = splitAt ((length cons_arg_vars) /2) cons_arg_vars
		 
		# (expr, left_vars, heaps) = build_prod expr left_vars predefs heaps
		# (expr, right_vars, heaps) = build_prod expr right_vars predefs heaps
		
		# (case_expr, heaps) = buildCasePAIRExpr var_expr (hd left_vars) (hd right_vars) expr predefs heaps
		
		# vars = [var : left_vars ++ right_vars]	
		= (case_expr, vars, heaps) 
	
	build_cons_app :: !Index !DefinedSymbol !*Heaps 
		-> (!Expression, [FreeVar], !*Heaps)
	build_cons_app cons_mod def_symbol=:{ds_arity} heaps
		# names = ["x"  +++ toString k \\ k <- [1..ds_arity]]
		# (var_exprs, vars, heaps) = buildVarExprs names heaps 
		# (expr, heaps) = buildConsApp cons_mod def_symbol var_exprs heaps
		= (expr, vars, heaps) 

buildIsomapFromTo :: !IsoDirection !DefinedSymbol !Int !Int !Int !*GenericState
	-> (!FunDef, !*GenericState)
buildIsomapFromTo 
		iso_dir def_sym group_index type_def_mod type_def_index 
		gs=:{gs_heaps, gs_modules}
	# (type_def=:{td_name, td_index, td_arity}, gs_modules) 
		= getTypeDef type_def_mod type_def_index gs_modules
	# arg_names = [ "isomap" +++ toString n \\ n <- [1 .. td_arity]]
	# (isomap_arg_vars, gs_heaps) = buildFreeVars arg_names gs_heaps 
	# (arg_expr, arg_var, gs_heaps) = buildVarExpr "x" gs_heaps
	# gs = {gs & gs_heaps = gs_heaps, gs_modules = gs_modules}
	# (body_expr, free_vars, gs) = 
		build_body iso_dir type_def_mod td_index type_def arg_expr isomap_arg_vars gs	

	# (fun_type, gs) = build_type iso_dir type_def_mod type_def_index gs
	# fun_def = makeFunction def_sym group_index (isomap_arg_vars ++ [arg_var]) body_expr (Yes fun_type) free_vars []	
	= (fun_def, gs)
where
	build_body :: !IsoDirection !Int !Int !CheckedTypeDef !Expression ![FreeVar] !*GenericState
		-> (Expression, [FreeVar], !*GenericState)
	build_body iso_dir type_def_mod type_def_index type_def=:{td_rhs=(AlgType def_symbols)} arg_expr isomap_arg_vars gs
		= build_body1 iso_dir type_def_mod type_def_index type_def def_symbols arg_expr isomap_arg_vars gs
		
	build_body iso_dir type_def_mod type_def_index type_def=:{td_rhs=(RecordType {rt_constructor})} arg_expr isomap_arg_vars gs
		= build_body1 iso_dir type_def_mod type_def_index type_def [rt_constructor] arg_expr isomap_arg_vars gs
				
	build_body iso_dir type_def_mod type_def_index _ arg_expr isomap_arg_vars gs
		= abort "cannot generate isomap for the type"		

	build_body1 iso_dir type_def_mod type_def_index type_def def_symbols arg_expr isomap_arg_vars gs
		# (case_alts, free_vars, gs=:{gs_heaps}) = 
			build_alts iso_dir 0 (length def_symbols) type_def_mod def_symbols isomap_arg_vars type_def gs
		# case_patterns = AlgebraicPatterns {glob_module = type_def_mod, glob_object = type_def_index} case_alts
		# (case_expr, gs_heaps) = buildCaseExpr arg_expr case_patterns gs_heaps
		= (case_expr, free_vars, {gs & gs_heaps = gs_heaps})

	build_alts :: !IsoDirection !Int !Int !Int ![DefinedSymbol] ![FreeVar] !CheckedTypeDef !*GenericState 
		-> ([AlgebraicPattern], [FreeVar], !*GenericState)
	build_alts iso_dir i n type_def_mod [] arg_vars type_def gs 
		= ([], [], gs) 
	build_alts iso_dir i n type_def_mod [def_symbol:def_symbols] arg_vars type_def gs
		# (alt, fvs, gs) = build_alt iso_dir i n type_def_mod def_symbol arg_vars type_def gs
		# (alts, free_vars, gs) = build_alts iso_dir (i+1) n type_def_mod def_symbols arg_vars type_def gs 		
		= ([alt:alts], fvs ++ free_vars, gs)

	build_alt :: !IsoDirection !Int !Int !Int !DefinedSymbol ![FreeVar] !CheckedTypeDef !*GenericState 
		-> (AlgebraicPattern, [FreeVar], !*GenericState)
	build_alt 
			iso_dir i n type_def_mod def_symbol=:{ds_ident, ds_arity, ds_index} 
			fun_arg_vars type_def gs=:{gs_heaps, gs_modules}		
		# names = ["x" +++ toString (i+1) +++ toString k \\ k <- [1..ds_arity]]
		# (cons_arg_vars, gs_heaps) = buildFreeVars names gs_heaps
		# (cons_def=:{cons_type}, gs_modules) = getConsDef type_def_mod ds_index gs_modules 				
		# gs = {gs & gs_heaps = gs_heaps, gs_modules = gs_modules}
		
		# (cons_arg_exprs, gs=:{gs_heaps}) = 
			build_cons_args iso_dir cons_type.st_args cons_arg_vars fun_arg_vars type_def gs 
		# (expr, gs_heaps) = buildConsApp type_def_mod def_symbol cons_arg_exprs gs_heaps				
		# alg_pattern = {
			ap_symbol = {glob_module = type_def_mod, glob_object = def_symbol},
			ap_vars = cons_arg_vars,
			ap_expr = expr,
			ap_position = NoPos
			}
		= (alg_pattern, cons_arg_vars, {gs & gs_heaps = gs_heaps})
	
	build_cons_args :: !IsoDirection ![AType] ![FreeVar] ![FreeVar] !CheckedTypeDef !*GenericState 
		-> ([!Expression], !*GenericState)
	build_cons_args iso_dir [] [] fun_arg_vars type_def gs = ([], gs) 	
	build_cons_args	iso_dir [arg_type:arg_types] [cons_arg_var:cons_arg_vars] fun_arg_vars type_def gs
		# (arg_expr, gs) = build_cons_arg iso_dir arg_type cons_arg_var fun_arg_vars type_def gs
		# (arg_exprs, gs) = build_cons_args iso_dir arg_types cons_arg_vars fun_arg_vars type_def gs 
		= ([arg_expr : arg_exprs], gs)
	
	build_cons_arg :: !IsoDirection !AType !FreeVar ![FreeVar] !CheckedTypeDef !*GenericState 
		-> (!Expression, !*GenericState)	
	build_cons_arg iso_dir type cons_arg_var fun_vars type_def gs
		# type_def_args = [atv_variable \\ {atv_variable} <- type_def.td_args]	
		# (iso_expr, gs) = buildIsomapExpr type type_def_args fun_vars gs
		# {gs_heaps, gs_predefs} = gs
		# sel_expr = case iso_dir of 
			IsoTo 	-> buildIsoToSelectionExpr iso_expr gs_predefs  
			IsoFrom -> buildIsoFromSelectionExpr iso_expr gs_predefs  
 		# (cons_var_expr, _, gs_heaps) = buildBoundVarExpr cons_arg_var gs_heaps
		= (sel_expr @ [cons_var_expr], {gs & gs_heaps = gs_heaps})

	build_type :: !IsoDirection !Int !Int !*GenericState
		-> (!SymbolType, !*GenericState)
	build_type 
			iso_dir module_index type_def_index 
			gs=:{gs_heaps, gs_modules, gs_predefs}
	
		#! ({td_arity, td_name}, gs_modules) = getTypeDef module_index type_def_index gs_modules 		
	
		# (arg_types, tvs1, tvs2, gs_heaps) = build_arg_types gs_predefs [1 .. td_arity] gs_heaps
						
		# type_symb_ident = {
			type_name = td_name,
			type_index = { glob_module = module_index, glob_object = type_def_index },
			type_arity = td_arity,
			type_prop = { 
				tsp_sign = {sc_pos_vect=cAllBitsClear, sc_neg_vect=cAllBitsClear},
				tsp_propagation = cAllBitsClear, 
				tsp_coercible = False
				}
			}				
		# type1 = makeAType (TA type_symb_ident [makeAType (TV tv) TA_Multi \\ tv <- tvs1]) TA_Multi 
		# type2 = makeAType (TA type_symb_ident [makeAType (TV tv) TA_Multi \\ tv <- tvs2]) TA_Multi
		# (arg_type, res_type) = case iso_dir of
			IsoTo 	-> (type1, type2)
			IsoFrom -> (type2, type1)
			 
		# symbol_type = {
			st_vars = tvs1 ++ tvs2,
			st_args = arg_types ++ [arg_type],
			st_arity = td_arity + 1,
			st_result = res_type,
			st_context = [],
			st_attr_vars = [],
			st_attr_env = []
			}
		#! gs = {gs & gs_heaps = gs_heaps, gs_modules = gs_modules}
		= (symbol_type, gs)
	 	
	build_arg_type predefs arg_no heaps
		# (type_var1, heaps) = buildTypeVar ("a"+++toString arg_no) heaps
		# type1 = makeAType (TV type_var1) TA_Multi
		# (type_var2, heaps) = buildTypeVar ("b"+++toString arg_no) heaps
		# type2 = makeAType (TV type_var2) TA_Multi
		# iso_type = buildATypeISO type1 type2 predefs 
		= (iso_type, type_var1, type_var2, heaps)
		
	build_arg_types predefs [] heaps
		= ([], [], [], heaps)
	build_arg_types predefs [n:ns] heaps
		# (t, tv1, tv2, heaps) = build_arg_type predefs n heaps
		# (ts, tvs1, tvs2, heaps) = build_arg_types predefs ns heaps
		= ([t:ts], [tv1:tvs1], [tv2:tvs2], heaps)	

buildIsomapForTypeDef :: !DefinedSymbol !Int !Int !CheckedTypeDef !DefinedSymbol !DefinedSymbol !*GenericState
	-> (!FunDef, !*GenericState)
buildIsomapForTypeDef	
		fun_def_sym group_index type_def_mod 
		type_def=:{td_name, td_index, td_arity}
		from_fun to_fun 
		gs=:{gs_main_dcl_module_n, gs_heaps, gs_predefs}	 
	# arg_names = [ "iso" +++ toString n \\ n <- [1 .. td_arity]]  
	# (arg_exprs, arg_vars, gs_heaps) = buildVarExprs arg_names gs_heaps
		
	# (from_expr, gs_heaps) = buildFunApp gs_main_dcl_module_n from_fun arg_exprs gs_heaps
	# (to_expr, gs_heaps) 	= buildFunApp gs_main_dcl_module_n to_fun arg_exprs gs_heaps	
	# (iso_expr, gs_heaps) 	= buildISO to_expr from_expr gs_predefs gs_heaps
	# fun_def = makeFunction fun_def_sym group_index arg_vars iso_expr No [] [from_fun.ds_index, to_fun.ds_index]					
	= (fun_def, {gs & gs_heaps = gs_heaps})

buildIsomapForGeneric :: !DefinedSymbol !Int !GenericDef !*GenericState
	-> (!FunDef, !*GenericState)
buildIsomapForGeneric def_sym group_index {gen_type, gen_arity, gen_args} gs=:{gs_heaps}
	#! arg_names = [ "iso" +++ toString n \\ n <- [1 .. gen_arity]]
	#! (arg_vars, gs_heaps) = buildFreeVars arg_names gs_heaps
	#! curried_gen_type = curry_symbol_type gen_type
	//#! (fun_type, gs_heaps) = build_type gen_type gen_args gs_heaps 
	#! (body_expr, gs) = buildIsomapExpr curried_gen_type gen_args arg_vars {gs & gs_heaps = gs_heaps} 	
	#! fun_def = makeFunction def_sym group_index arg_vars body_expr No [] []					
	= (fun_def, gs) 	
where 
/*	
	build_type :: !SymbolType ![TypeVar ]!*GenericState -> (!SymbolType, !*GenericState)
	build_type gen_type gen_args gs=:{gs_predefs, gs_heaps={hp_type_heaps}} 
	
		# (gen_type, gen_args, hp_type_vars) = fresh_generic_type gen_type gen_args hp_type_heaps
		# (st1, hp_type_heaps) = freshSymbolType "_1" gen_type hp_type_heaps
		# (st2, hp_type_heaps) = freshSymbolType "_2" gen_type hp_type_heaps
			
		# iso_args = [ buildATypeISO (makeAType (TV tv1) TA_Multi) (makeAType (TV tv2) TA_Multi) gs_predefs 
			\\ tv1 <- st1.st_vars & tv2 <- st2.st_vars ]
	
		# curried_st1 = curry_symbol_type st1
		# curried_st2 = curry_symbol_type st2		
		# iso_result = buildATypeISO curried_st1 curried_st2 gs_predefs	
		
		# st = {
				st_vars = removeDup (gen_args ++ st1.st_vars ++ st2.st_vars)
			,	st_args = iso_args
			,	st_arity = length iso_args
			,	st_result = iso_result
			,	st_context = []
			,	st_attr_vars = removeDup (st1.st_attr_vars ++ st2.st_attr_vars)
			,	st_attr_env = removeDup (st1.st_attr_env ++ st2.st_attr_env)
			}
	
		= (st, {gs & gs_heaps.hp_type_heaps = hp_type_heaps})

	fresh_generic_type gen_type=:{st_vars} gen_vars type_heaps	
		# gen_type = { gen_type & st_vars = gen_vars ++ st_vars } 
		# (fresh_gen_type, type_heaps) = freshSymbolType "" gen_type type_heaps
		# (fresh_gen_vars, st_vars) = splitAt (length gen_vars) fresh_gen_type.st_vars	
		= ({fresh_gen_type & st_vars = st_vars }, fresh_gen_vars, type_heaps) 
*/

	curry_symbol_type :: SymbolType -> AType 
	curry_symbol_type {st_args, st_result} 
		#(type, _, _) = buildCurriedType st_args st_result TA_Multi [] 0
		= type

// expression that does mapping of a type
buildIsomapExpr :: !AType ![TypeVar] ![FreeVar] !*GenericState
	-> (!Expression, !*GenericState)
buildIsomapExpr {at_type} arg_type_vars arg_vars gs
	= build_expr at_type arg_type_vars arg_vars gs	
where

	build_expr :: !Type ![TypeVar] ![FreeVar] !*GenericState
		-> (!Expression, !*GenericState)
	build_expr (TA {type_index, type_name} args) arg_type_vars arg_vars gs
		# (arg_exprs, gs) = build_exprs args arg_type_vars arg_vars gs
		# {gs_heaps, gs_main_dcl_module_n, gs_gtd_infos} = gs			
		# (gtd_info, gs_gtd_infos) = gs_gtd_infos ! [type_index.glob_module, type_index.glob_object]		
		# gt = case gtd_info of
			 		(GTDI_Generic gt) -> gt
			 		_ 	-> abort ("not a generic type " +++ type_name.id_name) 
		# (expr, gs_heaps) = buildFunApp gs_main_dcl_module_n gt.gt_isomap arg_exprs gs_heaps			
		= (expr, {gs & gs_heaps = gs_heaps, gs_gtd_infos = gs_gtd_infos})
	
	build_expr (arg --> res) arg_type_vars arg_vars gs
		# (arg_expr, gs) = buildIsomapExpr arg arg_type_vars arg_vars gs
		# (res_expr, gs) = buildIsomapExpr res arg_type_vars arg_vars gs				
		# {gs_heaps, gs_main_dcl_module_n, gs_predefs} = gs		
		# (expr, gs_heaps) = buildIsomapArrowApp arg_expr res_expr gs_predefs gs_heaps
		= (expr, {gs & gs_heaps = gs_heaps})

	build_expr (cons_var :@: args) arg_type_vars arg_vars gs
		# (arg_exprs, gs) = build_exprs args arg_type_vars arg_vars gs
		# type_var = case cons_var of
			CV type_var -> type_var
			_ -> abort "cons_var not implemented\n"
		# (cons_var_expr, gs) = build_expr_for_type_var type_var arg_type_vars arg_vars gs
		= (cons_var_expr @ arg_exprs, gs)

	build_expr (TB baric_type) arg_type_vars arg_vars gs=:{gs_predefs, gs_heaps}		
		# (expr, gs_heaps) = buildIsomapIdApp gs_predefs gs_heaps
		= (expr, {gs & gs_heaps = gs_heaps})
						
	build_expr (TV type_var) arg_type_vars arg_vars gs
		= build_expr_for_type_var type_var arg_type_vars arg_vars gs
	build_expr (GTV type_var) arg_type_vars arg_vars gs
		= build_expr_for_type_var type_var arg_type_vars arg_vars gs 
	build_expr (TQV type_var) arg_type_vars arg_vars gs
		= build_expr_for_type_var type_var arg_type_vars arg_vars gs 
	build_expr (TLifted type_var) arg_type_vars arg_vars gs
		= build_expr_for_type_var type_var arg_type_vars arg_vars gs 

	build_expr _ arg_type_vars arg_vars gs
		= abort "type does not match\n"
	
	build_exprs [] arg_type_vars arg_vars gs 
		= ([], gs)
	build_exprs [type:types] arg_type_vars arg_vars gs
		# (expr, gs) = buildIsomapExpr type arg_type_vars arg_vars gs
		# (exprs, gs) = build_exprs types arg_type_vars arg_vars gs
		= ([expr:exprs], gs)
			 			
	build_expr_for_type_var type_var arg_type_vars arg_vars gs=:{gs_predefs, gs_heaps}
		# (var_expr, gs_heaps) = buildExprForTypeVar type_var arg_type_vars arg_vars gs_predefs gs_heaps 
		= (var_expr, {gs & gs_heaps = gs_heaps})
	
buildInstance :: !DefinedSymbol !Int !ClassInstance !GenericDef !*GenericState
	-> (!FunDef, !*GenericState)
buildInstance 
		def_sym group_index 
		instance_def=:{ins_type, ins_generic} 
		generic_def=:{gen_name, gen_type, gen_isomap} 
		gs=:{gs_heaps}	

	#! original_arity 	= gen_type.st_arity
	#! generated_arity 	= def_sym.ds_arity - original_arity // depends on kind
	
	#! generated_arg_names = [ "f"/*gen_name.id_name*/ +++ toString n \\ n <- [1 .. generated_arity]]
	#! (generated_arg_vars, gs_heaps) = buildFreeVars generated_arg_names gs_heaps	
	#! original_arg_names = 	[ "x" +++ toString n \\ n <- [1 .. original_arity]]  
	#! (original_arg_exprs, original_arg_vars, gs_heaps) = buildVarExprs original_arg_names gs_heaps	
	#! arg_vars = generated_arg_vars ++ original_arg_vars
	
	#! (gt=:{gt_type, gt_type_args}, gs) = get_generic_type ins_type {gs & gs_heaps = gs_heaps } 	
	#! gen_glob_def_sym = {
		glob_module = ins_generic.glob_module,
		glob_object = {
			ds_ident = gen_name,
			ds_index = ins_generic.glob_object,
			ds_arity = 0
			}
		} 
		
	#! (adaptor_expr, gs)	 = build_adaptor_expr gt gen_isomap gs  
		//---> ("generic type", gt_type)
	#! (instance_expr, gs)	 = build_instance_expr gt_type gt_type_args generated_arg_vars gen_glob_def_sym gs 
	#! body_expr = (adaptor_expr @ [instance_expr]) @ original_arg_exprs

	#! fun_def = makeFunction def_sym group_index arg_vars body_expr No [] []					
	= (fun_def, gs) 	
where
	get_generic_type :: !InstanceType !*GenericState 
		-> (GenericType, !*GenericState)
	get_generic_type ins_type gs=:{gs_modules, gs_gtd_infos}
		# instance_type = hd ins_type.it_types
		# {type_index} = case instance_type of 
			TA type_symb_ident _ -> type_symb_ident
			_ -> abort "invalid type of generic instance"
		
		#! (gtd_info, gs_gtd_infos) = gs_gtd_infos ! [type_index.glob_module, type_index.glob_object]
		# (GTDI_Generic gt) = gtd_info 
		= (gt, {gs & gs_gtd_infos = gs_gtd_infos, gs_modules = gs_modules})
	
	build_adaptor_expr {gt_iso, gt_type} gen_isomap gs=:{gs_heaps, gs_main_dcl_module_n, gs_predefs}
		// create n iso applications 
		# (iso_exprs, gs_heaps) = build_iso_exprs gen_isomap.ds_arity gt_iso gs_main_dcl_module_n gs_heaps		
		# (isomap_expr, gs_heaps) = buildFunApp gs_main_dcl_module_n gen_isomap iso_exprs gs_heaps
		# sel_expr = buildIsoFromSelectionExpr isomap_expr gs_predefs 
		= (sel_expr, {gs & gs_heaps = gs_heaps})
		
	build_iso_exprs n iso gs_main_dcl_module_n gs_heaps
		| n == 0 = ([], gs_heaps)
		# (expr, gs_heaps) = buildFunApp gs_main_dcl_module_n iso [] gs_heaps	
		# (exprs, gs_heaps) = build_iso_exprs (n - 1) iso gs_main_dcl_module_n gs_heaps	
		= ([expr:exprs], gs_heaps)
	
	build_instance_expr :: !AType ![TypeVar] ![FreeVar] !(Global DefinedSymbol) !*GenericState 
		-> (Expression, !*GenericState)
	build_instance_expr {at_type} type_vars vars gen_sym gs 
		= build_instance_expr1 at_type type_vars vars gen_sym gs
	
	build_instance_expr1 (TA {type_name, type_index, type_arity} type_args) type_vars vars gen_sym gs	
		# (arg_exprs, gs=:{gs_heaps}) = 
			mapSt (\t gs -> build_instance_expr t type_vars vars gen_sym gs) type_args gs
		# (kind, gs) = get_kind_of_type_def type_index gs	
		= build_generic_app gen_sym kind arg_exprs gs

	build_instance_expr1 (arg_type --> res_type) type_vars vars gen_sym gs	
		= abort "build_instance_expr1: arrow type\n"
	build_instance_expr1 (type_cons_var :@: type_args) type_vars vars gen_sym gs	
		= abort "build_instance_expr1: type cons var application\n"
				
	build_instance_expr1 (TB basic_type) type_vars vars gen_sym gs 	
		= build_generic_app gen_sym KindConst [] gs
	build_instance_expr1 (TV type_var) type_vars vars gen_sym gs 
		= build_expr_for_type_var type_var type_vars vars gs 
	build_instance_expr1 (GTV type_var) type_vars vars gen_sym gs 
		= build_expr_for_type_var type_var type_vars vars gs 
	build_instance_expr1 (TQV type_var) type_vars vars gen_sym gs 
		= build_expr_for_type_var type_var type_vars vars gs 
	build_instance_expr1 _ type_vars vars gen_sym gs
		= abort "build_instance_expr1: type does not match\n" 
	
		
	build_expr_for_type_var type_var type_vars vars gs=:{gs_predefs, gs_heaps}
		# (var_expr, gs_heaps) = buildExprForTypeVar type_var type_vars vars gs_predefs gs_heaps 
		= (var_expr, {gs & gs_heaps = gs_heaps})
		
	build_generic_app {glob_module, glob_object} kind arg_exprs gs=:{gs_heaps}
		# (expr, gs_heaps) = buildGenericApp glob_module glob_object kind arg_exprs gs_heaps
		= (expr, {gs & gs_heaps = gs_heaps})	

	get_kind_of_type_def {glob_module, glob_object} gs=:{gs_td_infos}
		# (td_info, gs_td_infos) = gs_td_infos ! [glob_module, glob_object]
		= (make_kind td_info.tdi_kinds, {gs & gs_td_infos = gs_td_infos})
	where	
		make_kind [] = KindConst
		make_kind ks = KindArrow (ks ++ [KindConst])

		 			
buildExprForTypeVar :: TypeVar [TypeVar] [FreeVar] !PredefinedSymbols !*Heaps 
	-> (!Expression, !*Heaps)
buildExprForTypeVar type_var type_vars vars predefs heaps 
	| length type_vars <> length vars 
		= abort "buildExprForTypeVar: inconsistent arguments\n"
	# tv_info_ptrs = {tv_info_ptr \\ {tv_info_ptr} <- type_vars}
	# index = find_in_array 0 tv_info_ptrs type_var.tv_info_ptr
	| index == (-1)		
		= buildIsomapIdApp predefs heaps
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
		gs=:{gs_heaps}
	#! arg_names = ["x" +++ toString i \\ i <- [1 .. def_sym.ds_arity]]
	#! (arg_exprs, arg_vars, gs_heaps) = buildVarExprs arg_names gs_heaps
	
	# (gen_exprs, gs_heaps) = mapSt build_gen_expr [1 .. (length kinds) - 1] gs_heaps
	  
	#! (body_expr, gs_heaps) = buildGenericApp generic_module generic_def_sym kind (gen_exprs ++ arg_exprs) gs_heaps
	#! fun_def = makeFunction def_sym group_index arg_vars body_expr No [] []					
	= (fun_def, {gs & gs_heaps = gs_heaps})	
where
	build_gen_expr _ heaps
		= buildGenericApp generic_module generic_def_sym KindConst [] heaps
										
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

	# (new_st_args, type_heaps) = 		substitute st_args 		type_heaps
	# (new_st_result, type_heaps) = 	substitute st_result 	type_heaps
	# (new_st_context, type_heaps) = 	substitute st_context 	type_heaps
	# (new_st_attr_env, type_heaps) = 	substitute st_attr_env 	type_heaps

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

buildPredefTypeApp :: !Int [AType] !PredefinedSymbols -> !AType
buildPredefTypeApp predef_index args predefs
	# {pds_ident, pds_module, pds_def} = predefs.[predef_index]
	# global_index = {glob_module = pds_module, glob_object = pds_def}
	# type_symb = MakeTypeSymbIdent global_index pds_ident (length args) 		  
	= makeAType (TA type_symb args) TA_Multi	

buildATypeISO	x y predefs = buildPredefTypeApp PD_TypeISO [x, y] predefs
buildATypeUNIT  predefs		= buildPredefTypeApp PD_TypeUNIT [] predefs
buildATypePAIR x y predefs 	= buildPredefTypeApp PD_TypePAIR [x, y] predefs
buildATypeEITHER x y predefs = buildPredefTypeApp PD_TypeEITHER [x, y] predefs


buildProductType :: ![AType] !PredefinedSymbols -> !AType 
buildProductType [] predefs = buildATypeUNIT predefs
buildProductType [type] predefs = type
buildProductType types predefs
	#  (l,r) = splitAt ((length types) / 2) types
	= buildATypePAIR (buildProductType l predefs) (buildProductType r predefs) predefs

//===================================
// Functions 
//===================================

makeFunction :: !DefinedSymbol !Index ![FreeVar] Expression !(Optional SymbolType) [FreeVar] [Index] 
	-> FunDef
makeFunction {ds_index, ds_arity, ds_ident} group_index arg_vars body_expr opt_sym_type local_vars fun_call_indexes
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
		fun_pos = NoPos,
		fun_index = ds_index,
		fun_kind  = FK_ImpFunction cNameNotLocationDependent,
		fun_lifted = 0,
		fun_info = {	
			fi_calls = map (\ind->{fc_level = NotALevel, fc_index = ind}) fun_call_indexes,	
			fi_group_index = group_index,
			fi_def_level = NotALevel,
			fi_free_vars =  [],
			fi_local_vars = local_vars,
			fi_dynamics = [],
			fi_is_macro_fun = False
			}	
		}

newGroupIndex gs=:{gs_last_group} = (gs_last_group, {gs & gs_last_group = gs_last_group + 1})
newFunIndex gs=:{gs_last_fun} = (gs_last_fun, {gs & gs_last_fun = gs_last_fun + 1})
newFunAndGroupIndex gs=:{gs_last_fun, gs_last_group} 
	= (gs_last_fun, gs_last_group, {gs & gs_last_fun = gs_last_fun + 1, gs_last_group = gs_last_group + 1})

/*
addFunsAndGroups :: ![FunDef] ![Group] (!*GenericState) -> !*GenericState
addFunsAndGroups new_fun_defs new_groups gs=:{gs_fun_defs, gs_groups, gs_last_fun}
	# gs_fun_defs 	= arrayPlusList gs_fun_defs new_fun_defs
	# gs_groups 	= arrayPlusList gs_groups new_groups
	
	# (last_fun_def, gs_fun_defs) = gs_fun_defs![gs_last_fun - 1]
	| last_fun_def.fun_index <> gs_last_fun - 1
		= abort "addFunsAndGroups: inconsistently added functions\n"	 

	= {gs & gs_fun_defs = gs_fun_defs, gs_groups = gs_groups}
*/
addFunsAndGroups :: ![FunDef] ![Group] (!*GenericState) -> !*GenericState
addFunsAndGroups new_fun_defs new_groups 
		gs=:{gs_fun_defs, gs_groups, gs_first_fun, gs_last_fun, gs_first_group, gs_last_group}
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
			(makeFunction EmptyDefinedSymbol NoIndex [] EE No [] [])
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
		| fun_def.fun_index == index 
			= fun_def
			= abort ("conflicting fun_indexes of " +++ fun_def.fun_symb.id_name +++
				toString fun_def.fun_index +++ " and " +++ toString index) 
	
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

buildIdFunction :: !DefinedSymbol Int !Ident !PredefinedSymbols !*Heaps-> (!FunDef, !*Heaps)
buildIdFunction def_sym group_index name predefs heaps
	# (arg_expr, arg_var, heaps) = buildVarExpr "x" heaps 
	# fun_def = makeFunction def_sym group_index [arg_var] arg_expr No [] []		
	= (fun_def, heaps)
	
buildUndefFunction :: !DefinedSymbol !Int !PredefinedSymbols !*Heaps-> (!FunDef, !*Heaps)
buildUndefFunction def_sym group_index predefs heaps
	# names = [ "x" +++ toString i \\ i <- [1 .. def_sym.ds_arity]]
	# (arg_vars, heaps) = mapSt build_free_var names heaps
	# (body_expr, heaps) = buildUndefFunApp [] predefs heaps
	//# (body_expr, heaps) = buildUNIT predefs heaps
	# fun_def = makeFunction def_sym group_index arg_vars body_expr No [] []		
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
	# {pds_ident, pds_module, pds_def} = predefs.[predef_index]
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
			symb_kind = SK_Constructor cons_glob, 
			symb_arity = ds_arity }, 
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
			symb_kind = SK_Function fun_glob, 
			symb_arity = length arg_exprs }, 
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
			symb_kind = SK_Generic glob_index kind, 
			symb_arity = length arg_exprs }, 
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

buildPredefConsApp :: !Int [Expression] !PredefinedSymbols !*Heaps
	-> (!Expression, !*Heaps)
buildPredefConsApp predef_index args predefs heaps=:{hp_expression_heap}
	# {pds_ident, pds_module, pds_def} = predefs.[predef_index]
	# global_index = {glob_module = pds_module, glob_object = pds_def}
	# symb_ident = {
		symb_name = pds_ident, 
		symb_kind = SK_Constructor global_index, 
		symb_arity = length args 
		}
	# (expr_info_ptr, hp_expression_heap) = newPtr EI_Empty hp_expression_heap
	# app = App {app_symb = symb_ident, app_args = args, app_info_ptr = expr_info_ptr} 
	= (app, {heaps & hp_expression_heap = hp_expression_heap})

buildISO to_expr from_expr predefs heaps :== buildPredefConsApp PD_ConsISO [to_expr, from_expr] predefs heaps
buildUNIT predefs heaps		:== buildPredefConsApp PD_ConsUNIT [] predefs heaps
buildPAIR x y predefs heaps	:== buildPredefConsApp PD_ConsPAIR [x, y] predefs heaps
buildLEFT x predefs heaps	:== buildPredefConsApp PD_ConsLEFT [x] predefs heaps
buildRIGHT x predefs heaps	:== buildPredefConsApp PD_ConsRIGHT [x] predefs heaps

buildPredefFunApp :: !Int [Expression] !PredefinedSymbols !*Heaps
	-> (!Expression, !*Heaps)
buildPredefFunApp predef_index args predefs heaps=:{hp_expression_heap}
	# {pds_ident, pds_module, pds_def} = predefs.[predef_index]
	# global_index = {glob_module = pds_module, glob_object = pds_def}
	# symb_ident = {
		symb_name = pds_ident, 
		symb_kind = SK_Function global_index, 
		symb_arity = length args 
		}
	# (expr_info_ptr, hp_expression_heap) = newPtr EI_Empty hp_expression_heap
	# app = App {app_symb = symb_ident, app_args = args, app_info_ptr = expr_info_ptr} 
	= (app, {heaps & hp_expression_heap = hp_expression_heap})

buildUndefFunApp args predefs heaps :== buildPredefFunApp PD_undef args predefs heaps 
buildIsomapArrowApp x y predefs heaps :== buildPredefFunApp PD_isomap_ARROW_ [x,y] predefs heaps
buildIsomapIdApp predefs heaps :== buildPredefFunApp PD_isomap_ID [] predefs heaps
 	
buildIsoToSelectionExpr :: !Expression !PredefinedSymbols -> Expression
buildIsoToSelectionExpr record_expr predefs
	# {pds_module, pds_def, pds_ident} = predefs . [PD_iso_to]
	# selector = { 
		glob_module = pds_module, 
		glob_object = {ds_ident = pds_ident, ds_index = pds_def, ds_arity = 1}}
	= Selection No record_expr [RecordSelection selector 0]

buildIsoFromSelectionExpr :: !Expression !PredefinedSymbols -> Expression
buildIsoFromSelectionExpr record_expr predefs 
	# {pds_module, pds_def, pds_ident} = predefs . [PD_iso_from]
	# selector = { 
		glob_module = pds_module, 
		glob_object = {ds_ident = pds_ident, ds_index = pds_def, ds_arity = 1}}
	= Selection No record_expr [RecordSelection selector 1]

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

buildVarExprs :: ![String] !*Heaps -> (![Expression], [!FreeVar], !*Heaps)	 		
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




transpose []             = []
transpose [[] : xss]     = transpose xss
transpose [[x:xs] : xss] = 
	[[x : [hd l \\ l <- xss]] : transpose [xs : [ tl l \\  l <- xss]]]

 			