implementation module explicitimports
// compile with reuse unique nodes option

import StdEnv

:: FilterState =
	{	fs_wanted_symbols	:: ![Ident]
	,	fs_modules			:: !.{#DclModule}
	,	fs_symbol_table		:: !.SymbolTable
	,	fs_error			:: !.ErrorAdmin
	}

import syntax, typesupport, parse, checksupport, utilities, checktypes, transform, predef, RWSDebug, cheat

cUndef :== (-1)
implies a b :== not a || b

:: ImportNrAndIdents =
	{	ini_symbol_nr	:: !Index
	,	ini_belonging	:: !Optional [ImportedIdent]
	}

:: SolvedImports =
	{	si_explicit	:: ![([Declaration], Position)]
	,	si_implicit	:: ![(Index, Position)]	// module indices
	}

solveExplicitImports :: !(IntKeyHashtable [(Int,Position,[ImportNrAndIdents])]) !{#Int} !Index 
				!*(!{#x:DclModule},!*{#Int},!{!*ExplImpInfo},!*CheckState)
			-> (!.SolvedImports,!(!{#x:DclModule},!.{#Int},!{!.ExplImpInfo},!.CheckState))
solveExplicitImports expl_imp_indices_ikh modules_in_component_set importing_mod (dcl_modules, visited_modules, expl_imp_info, cs)
	# import_indices
			= ikhSearch` importing_mod expl_imp_indices_ikh
	  expl_imp_indices
	  		= [ imports \\ imports=:(_, _, [_:_]) <- import_indices ]
	  impl_imports
	  		= [ (mod_index, position) \\ imports=:(mod_index, position, []) <- import_indices ]
	  (expl_imports, state)
	  		= mapSt (solve_expl_imp_from_module expl_imp_indices_ikh modules_in_component_set importing_mod)
					expl_imp_indices (dcl_modules, visited_modules, expl_imp_info, cs)
	= ({ si_explicit = expl_imports, si_implicit = impl_imports }, state)
  where
	solve_expl_imp_from_module expl_imp_indices_ikh modules_in_component_set importing_mod
			(imported_mod, position, imported_symbols) (dcl_modules, visited_modules, expl_imp_info, cs)
		# (decl_infos, (visited_modules, expl_imp_info))
				= mapSt (search_expl_imp_symbol expl_imp_indices_ikh modules_in_component_set importing_mod imported_mod)
						imported_symbols 
						(visited_modules, expl_imp_info)
		  (expl_imp_info, cs_error)
		  		= (switch_import_syntax check_triples check_singles position) decl_infos imported_symbols
		  				(expl_imp_info, cs.cs_error)
		  belonging_to_solve
		  		= [ (di_decl, ini, imported_mod) \\ Yes ({di_decl}, ini=:{ini_belonging=Yes _}, imported_mod) <- decl_infos]
		  (belonging_decls, dcl_modules, visited_modules, expl_imp_info, cs)
		  		= foldSt (solve_belonging position expl_imp_indices_ikh modules_in_component_set importing_mod)
		  				belonging_to_solve
		  				([], dcl_modules, visited_modules, expl_imp_info, { cs & cs_error = cs_error }) 
// XXX alles Scheisse
		= ((flatten [[di_decl:di_instances] \\ Yes ({di_decl,di_instances}, _, _) <- decl_infos]++belonging_decls, position),
			(dcl_modules, visited_modules, expl_imp_info, cs))

	solve_belonging position expl_imp_indices_ikh modules_in_component_set importing_mod
			(decl, {ini_symbol_nr, ini_belonging=Yes belongs}, imported_mod)
			(decls_accu, dcl_modules, visited_modules, expl_imp_info, cs=:{cs_error, cs_symbol_table})
		# (all_belongs, dcl_modules)
				= get_all_belongs decl dcl_modules
		  (ExplImpInfo eii_ident eii_declaring_modules, expl_imp_info)
				= replace expl_imp_info ini_symbol_nr TemporarilyFetchedAway
		  (need_all, belongs_set, cs_error, cs_symbol_table)
		  		= case belongs of
		  			[]
		  				// an import like ::A(..) or ::A{..} or class c{..} 
		  				-> (False, [(belong_nr, belong_ident) \\ belong_nr<-[0..] & belong_ident<-all_belongs],
		  						cs_error, cs_symbol_table)
		  			_
		  				// an import like ::A(C1, C2) or ::A{f1} or class c{m1} 
		  				# (nr_of_belongs, cs_symbol_table)
			  					= foldSt numerate_belongs all_belongs (0, cs_symbol_table)
						  belongs_bitvect
						  		= bitvectCreate nr_of_belongs
						  (belongs_set, (cs_error, cs_symbol_table))
						  		= mapFilterYesSt (get_opt_nr_and_ident position eii_ident) belongs (cs_error, cs_symbol_table)
			  			  cs_symbol_table
			  			  		= foldSt restoreHeap all_belongs cs_symbol_table
						-> (True, belongs_set, cs_error, cs_symbol_table)
		  (decls_accu, dcl_modules, eii_declaring_modules, visited_modules, cs_error)
				= foldSt 
					(search_belonging need_all position eii_ident decl expl_imp_indices_ikh modules_in_component_set
							imported_mod ini_symbol_nr importing_mod)
					belongs_set (decls_accu, dcl_modules, eii_declaring_modules, visited_modules, cs_error)
		  expl_imp_info
		  		= { expl_imp_info & [ini_symbol_nr] = ExplImpInfo eii_ident eii_declaring_modules }
		= (decls_accu, dcl_modules, visited_modules, expl_imp_info, { cs & cs_error = cs_error, cs_symbol_table = cs_symbol_table })
		
	search_belonging need_all position eii_ident decl expl_imp_indices_ikh modules_in_component_set imported_mod ini_symbol_nr importing_mod
						(belong_nr, belong_ident) (decls_accu, dcl_modules, eii_declaring_modules, visited_modules, cs_error)
		# (found, path, eii_declaring_modules, visited_modules)
				=  depth_first_search expl_imp_indices_ikh modules_in_component_set
						imported_mod ini_symbol_nr belong_nr belong_ident [importing_mod]
						eii_declaring_modules (bitvectReset visited_modules)
		= case found of
			Yes _
				# eii_declaring_modules
				  		= foldSt (store_belonging belong_nr ini_symbol_nr) path eii_declaring_modules
				  (belong_decl, dcl_modules)
					= get_nth_belonging_decl position belong_nr decl dcl_modules
				-> ([belong_decl:decls_accu], dcl_modules, eii_declaring_modules, visited_modules, cs_error)
			_
				# cs_error
					= case need_all of
						True
							# cs_error
									= pushErrorAdmin (newPosition import_ident position) cs_error
							  cs_error
							  		= checkError belong_ident ("of "+++eii_ident.id_name+++" not exported by the specified module")
							  				cs_error
							-> popErrorAdmin cs_error
						_
							-> cs_error
				-> (decls_accu, dcl_modules, eii_declaring_modules, visited_modules, cs_error)

	store_belonging belong_nr ini_symbol_nr mod_index eii_declaring_modules
		# (Yes di=:{di_belonging}, eii_declaring_modules)
				= ikhUSearch mod_index eii_declaring_modules
		  (new, eii_declaring_modules)
		  		= ikhInsert True mod_index { di & di_belonging = addNr belong_nr di_belonging } eii_declaring_modules
		| new
			= abort "sanity check nr 2765 failed in module check"
		= eii_declaring_modules

	get_nth_belonging_decl position belong_nr decl dcl_modules
		# (STE_Imported _ def_mod_index) = decl.dcl_kind
		  (belongin_symbols, dcl_modules)
				= getBelongingSymbols decl dcl_modules
		= case belongin_symbols of
			BS_Constructors constructors
				# {ds_ident, ds_index} = constructors!!belong_nr
				-> ({ dcl_ident = ds_ident, dcl_pos = position, 
						dcl_kind = STE_Imported STE_Constructor def_mod_index,
						dcl_index = ds_index }, dcl_modules)
			BS_Fields rt_fields
				# {fs_name, fs_index} = rt_fields.[belong_nr]
				  ({sd_symb}, dcl_modules)
						= dcl_modules![def_mod_index].dcl_common.com_selector_defs.[fs_index]
				-> ({ dcl_ident = fs_name, dcl_pos = position, 
						dcl_kind = STE_Imported (STE_Field sd_symb) def_mod_index,
						dcl_index = fs_index }, dcl_modules)
			BS_Members class_members
				# {ds_ident, ds_index} = class_members.[belong_nr]
				-> ({ dcl_ident = ds_ident, dcl_pos = position,
						 dcl_kind = STE_Imported STE_Member def_mod_index,
						dcl_index = ds_index }, dcl_modules)

	get_all_belongs decl dcl_modules
		# (belonging_symbols, dcl_modules)
				= getBelongingSymbols decl dcl_modules
		= case belonging_symbols of
			BS_Constructors constructors
				-> ([ds_ident \\ {ds_ident}<-constructors], dcl_modules)
			BS_Fields rt_fields
				-> ([fs_name \\ {fs_name}<-:rt_fields], dcl_modules)
			BS_Members class_members
				# (STE_Imported _ def_mod_index) = decl.dcl_kind
				  ({class_members}, dcl_modules)
						= dcl_modules![def_mod_index].dcl_common.com_class_defs.[decl.dcl_index]
				-> ([ds_ident \\ {ds_ident}<-:class_members], dcl_modules)
			BS_Nothing
				-> ([], dcl_modules)

	numerate_belongs {id_info} (i, cs_symbol_table)
		# (ste, cs_symbol_table)
				= readPtr id_info cs_symbol_table
		  new_ste
		  		= { ste & ste_kind = STE_BelongingSymbol i, ste_previous = ste }
		= (i+1, writePtr id_info new_ste cs_symbol_table)
	
	get_opt_nr_and_ident position eii_ident {ii_ident=ii_ident=:{id_info}} (cs_error, cs_symbol_table)
		# ({ste_kind}, cs_symbol_table)
				= readPtr id_info cs_symbol_table
		= case ste_kind of
			STE_BelongingSymbol i
				-> (Yes (i, ii_ident), (cs_error, cs_symbol_table))
			_
				# cs_error
						= pushErrorAdmin (newPosition import_ident position) cs_error
				  cs_error
						= checkError ii_ident ("does not belong to "+++eii_ident.id_name) cs_error 
				-> (No, (popErrorAdmin cs_error, cs_symbol_table))
		
	search_expl_imp_symbol expl_imp_indices_ikh modules_in_component_set importing_mod imported_mod
			ini=:{ini_symbol_nr} (visited_modules, expl_imp_info)
		# (ExplImpInfo eii_ident eii_declaring_modules, expl_imp_info)
				= replace expl_imp_info ini_symbol_nr TemporarilyFetchedAway
		  (opt_decl, path, eii_declaring_modules, visited_modules)
				= depth_first_search expl_imp_indices_ikh modules_in_component_set imported_mod
						ini_symbol_nr cUndef stupid_ident [importing_mod]
						eii_declaring_modules (bitvectReset visited_modules)
		= case opt_decl of
			Yes di=:{di_decl}
				# new_eii_declaring_modules
				  		= foldSt (\mod_index eei_dm->ikhInsert` False mod_index 
				  					{di_decl = di_decl, di_instances = [], di_belonging=EndNumbers} eei_dm)
				  				path eii_declaring_modules
				  new_eii
				  		= ExplImpInfo eii_ident new_eii_declaring_modules
				-> (Yes (di, ini, imported_mod), (visited_modules, { expl_imp_info & [ini_symbol_nr] = new_eii }))
			No
				# eii
				  		= ExplImpInfo eii_ident eii_declaring_modules
				-> (No, (visited_modules, { expl_imp_info & [ini_symbol_nr] = eii }))

	depth_first_search expl_imp_indices_ikh modules_in_component_set
			imported_mod imported_symbol belong_nr belong_ident path eii_declaring_modules visited_modules
//		| False--->("depth_first_search imported_mod", imported_mod, "imported_symbol", imported_symbol)
//			= undef
		# (search_result, eii_declaring_modules)
				= ikhUSearch imported_mod eii_declaring_modules
		= case search_result of
			yes_di=:(Yes di)
				| belong_nr==cUndef
					-> (yes_di, path, eii_declaring_modules, visited_modules)
				| inNumberSet belong_nr di.di_belonging
					-> (yes_di, path, eii_declaring_modules, visited_modules)
			_
				| not (bitvectSelect imported_mod modules_in_component_set)
					// the eii_declaring_modules is complete for modules that are outside
					// (=beneath) the actual component=> no need to search further
					-> (No, [], eii_declaring_modules, visited_modules)
				# imports_of_imported_mod
				  		= ikhSearch` imported_mod expl_imp_indices_ikh
				-> try_children imports_of_imported_mod expl_imp_indices_ikh 
						modules_in_component_set imported_symbol belong_nr belong_ident
						[imported_mod:path]
						eii_declaring_modules (bitvectSet imported_mod visited_modules)

	try_children [(imp_imp_mod, _, imp_imp_symbols):imports] expl_imp_indices_ikh
			modules_in_component_set imported_symbol belong_nr belong_ident path eii_declaring_modules visited_modules
		| bitvectSelect imp_imp_mod visited_modules
//			| False--->"visited" = undef
			= try_children imports expl_imp_indices_ikh modules_in_component_set imported_symbol
					belong_nr belong_ident path eii_declaring_modules visited_modules
		| not (isEmpty imp_imp_symbols)
			// follow the path trough an explicit import only if the symbol is listed there
			# (found, ini_belonging)
					= search_imported_symbol imported_symbol imp_imp_symbols
			| not (found && implies (belong_nr<>cUndef) (belong_ident_found belong_ident ini_belonging))
				= try_children imports expl_imp_indices_ikh modules_in_component_set imported_symbol
						belong_nr belong_ident path eii_declaring_modules visited_modules
			= continue imp_imp_mod imports expl_imp_indices_ikh modules_in_component_set imported_symbol
						belong_nr belong_ident path eii_declaring_modules visited_modules
		= continue imp_imp_mod imports expl_imp_indices_ikh modules_in_component_set imported_symbol
						belong_nr belong_ident path eii_declaring_modules visited_modules
	  where
		continue imp_imp_mod imports expl_imp_indices_ikh modules_in_component_set imported_symbol
							belong_nr belong_ident path eii_declaring_modules visited_modules
			# (opt_decl, path, eii_declaring_modules, visited_modules)
					= depth_first_search expl_imp_indices_ikh modules_in_component_set imp_imp_mod
							imported_symbol belong_nr belong_ident path eii_declaring_modules visited_modules
			= case opt_decl of
				Yes _
					-> (opt_decl, path, eii_declaring_modules, visited_modules)
				No
					-> try_children imports expl_imp_indices_ikh modules_in_component_set
							imported_symbol belong_nr belong_ident path eii_declaring_modules visited_modules
	
	try_children [] expl_imp_indices_ikh _ imported_symbol belong_nr belong_ident path
			eii_declaring_modules visited_modules
		= (No, [], eii_declaring_modules, visited_modules)

	search_imported_symbol :: !Int ![ImportNrAndIdents] -> (!Bool, !Optional [ImportedIdent])
	search_imported_symbol imported_symbol []
		= (False, No)
	search_imported_symbol imported_symbol [{ini_symbol_nr, ini_belonging}:t]
		| imported_symbol==ini_symbol_nr
			= (True, ini_belonging)
		= search_imported_symbol imported_symbol t


	belong_ident_found :: !Ident !(Optional [ImportedIdent]) -> Bool
	belong_ident_found belong_ident No
		// like from m import ::T
		= False
	belong_ident_found belong_ident (Yes [])
		// like from m import ::T(..)
		= True 
	belong_ident_found belong_ident (Yes import_list)
		// like from m import ::T(C1,C2)
		= is_member belong_ident import_list

	is_member :: !Ident ![ImportedIdent] -> Bool
	is_member belong_ident []
		= False
	is_member belong_ident [{ii_ident}:t]
		| belong_ident==ii_ident
			= True
		= is_member belong_ident t

	// No, No, No!
	check_triples position [No, No, No: t1] [imported_symbol, _, _: t2] (expl_imp_info, cs_error)
		# (expl_imp_info, cs_error)
				= give_error position imported_symbol (expl_imp_info, cs_error)
		= check_triples position t1 t2 (expl_imp_info, cs_error)
	check_triples position [_, _, _: t1] [_, _, _: t2] (expl_imp_info, cs_error)
		= check_triples position t1 t2 (expl_imp_info, cs_error)
	check_triples position [] [] (expl_imp_info, cs_error)
		= (expl_imp_info, cs_error)
		
	check_singles position [No: t1] [imported_symbol: t2] (expl_imp_info, cs_error)
		# (expl_imp_info, cs_error)
				= give_error position imported_symbol (expl_imp_info, cs_error)
		= check_singles position t1 t2 (expl_imp_info, cs_error)
	check_singles position [_:t1] [_:t2] (expl_imp_info, cs_error)
		= check_singles position t1 t2 (expl_imp_info, cs_error)
	check_singles position [] [] (expl_imp_info, cs_error)
		= (expl_imp_info, cs_error)
		
	give_error position {ini_symbol_nr} (expl_imp_info, cs_error)
		# (eii_ident, expl_imp_info)
				= do_a_lot_just_to_read_an_array_2 ini_symbol_nr expl_imp_info
		  cs_error
				= pushErrorAdmin (newPosition import_ident position) cs_error
		  cs_error
				// XXX it should be also printed to which namespace eii_ident belongs
		  		= checkError eii_ident "not exported by the specified module" cs_error
		= (expl_imp_info, popErrorAdmin cs_error)

	do_a_lot_just_to_read_an_array_2 i expl_imp_info
		# (eii, expl_imp_info)
				= replace expl_imp_info i TemporarilyFetchedAway
		  (eii_ident, eii)
		  		= get_eei_ident eii
		= (eii_ident, { expl_imp_info & [i] = eii })

	get_eei_ident (eii=:ExplImpInfo eii_ident _) = (eii_ident, eii)
	
:: CheckCompletenessState =
	{	ccs_dcl_modules				:: !.{#DclModule}
	,	ccs_icl_functions			:: !.{#FunDef}
	,	ccs_set_of_visited_icl_funs	:: !.{#Bool}		// ccs_set_of_visited_icl_funs.[i] <=> function nr i has been considered
	,	ccs_expr_heap				:: !.ExpressionHeap
	,	ccs_symbol_table			:: !.SymbolTable
	,	ccs_error					:: !.ErrorAdmin
	,	ccs_heap_changes_accu		:: ![SymbolPtr]
	}

:: *CheckCompletenessStateBox = { box_ccs :: !*CheckCompletenessState }

:: CheckCompletenessInput =
	{	cci_import_position		:: !Position
	,	cci_main_dcl_module_n	:: !Int
	}

:: CheckCompletenessInputBox = { box_cci :: !CheckCompletenessInput }

checkExplicitImportCompleteness :: ![(Declaration, Position)] !*{#DclModule} !*{#FunDef} !*ExpressionHeap !*CheckState
				-> (!.{#DclModule},!.{#FunDef},!.ExpressionHeap,!.CheckState)
checkExplicitImportCompleteness dcls_explicit dcl_modules icl_functions expr_heap 
								cs=:{cs_symbol_table, cs_error}
	#! nr_icl_functions = size icl_functions
	   box_ccs = { ccs_dcl_modules = dcl_modules, ccs_icl_functions = icl_functions,
	   			ccs_set_of_visited_icl_funs = createArray nr_icl_functions False,
				ccs_expr_heap = expr_heap, ccs_symbol_table = cs_symbol_table,
				ccs_error = cs_error, ccs_heap_changes_accu = [] }
	   main_dcl_module_n
	   		= cs.cs_x.x_main_dcl_module_n
	   ccs = foldSt (checkCompleteness main_dcl_module_n) dcls_explicit { box_ccs = box_ccs }
	   { ccs_dcl_modules, ccs_icl_functions, ccs_expr_heap, ccs_symbol_table, ccs_error, ccs_heap_changes_accu }
	   		= ccs.box_ccs
	// repair heap contents
	   ccs_symbol_table = foldSt replace_ste_with_previous ccs_heap_changes_accu ccs_symbol_table
	   cs = { cs & cs_symbol_table = ccs_symbol_table, cs_error = ccs_error }
	= (ccs_dcl_modules, ccs_icl_functions, ccs_expr_heap, cs)
  where
	checkCompleteness :: !Int !(Declaration, Position) !*CheckCompletenessStateBox -> *CheckCompletenessStateBox
	checkCompleteness main_dcl_module_n ({dcl_ident, dcl_index, dcl_kind=STE_FunctionOrMacro _}, import_position) ccs 
		= checkCompletenessOfMacro dcl_ident dcl_index main_dcl_module_n import_position ccs
	checkCompleteness main_dcl_module_n ({dcl_ident, dcl_index, dcl_kind=STE_Imported (STE_FunctionOrMacro _) mod_index}, import_position) ccs 
		= checkCompletenessOfMacro dcl_ident dcl_index main_dcl_module_n import_position ccs
	checkCompleteness main_dcl_module_n ({dcl_ident, dcl_index, dcl_kind=STE_Imported expl_imp_kind mod_index}, import_position) ccs 
		#! ({dcl_common,dcl_functions}, ccs) = ccs!box_ccs.ccs_dcl_modules.[mod_index]
		   cci = { box_cci = { cci_import_position = import_position, cci_main_dcl_module_n=main_dcl_module_n }}
		= continuation expl_imp_kind dcl_common dcl_functions cci ccs
	  where
		continuation :: !STE_Kind CommonDefs !{# FunType} !CheckCompletenessInputBox !*CheckCompletenessStateBox
					-> *CheckCompletenessStateBox
		continuation STE_Type dcl_common dcl_functions cci ccs
			= check_completeness dcl_common.com_type_defs.[dcl_index] cci ccs
		continuation STE_Constructor dcl_common dcl_functions cci ccs
			= check_completeness dcl_common.com_cons_defs.[dcl_index] cci ccs
		continuation (STE_Field _) dcl_common dcl_functions cci ccs
			= check_completeness dcl_common.com_selector_defs.[dcl_index] cci ccs
		continuation STE_Class dcl_common dcl_functions cci ccs
			= check_completeness dcl_common.com_class_defs.[dcl_index] cci ccs
		continuation STE_Member dcl_common dcl_functions cci ccs
			= check_completeness dcl_common.com_member_defs.[dcl_index] cci ccs
		continuation (STE_Instance _) dcl_common dcl_functions cci ccs
			= check_completeness dcl_common.com_instance_defs.[dcl_index] cci ccs
		continuation STE_DclFunction dcl_common dcl_functions cci ccs
			= check_completeness dcl_functions.[dcl_index] cci ccs
	
	checkCompletenessOfMacro :: !Ident !Index !Int !Position !*CheckCompletenessStateBox -> *CheckCompletenessStateBox
	checkCompletenessOfMacro dcl_ident dcl_index main_dcl_module_n import_position ccs
		#! ({fun_body}, ccs) = ccs!box_ccs.ccs_icl_functions.[dcl_index]
		   ccs = { ccs & box_ccs.ccs_set_of_visited_icl_funs.[dcl_index] = True }
		   cci = { box_cci = { cci_import_position = import_position, cci_main_dcl_module_n=main_dcl_module_n }}
		= check_completeness fun_body cci ccs
	
	replace_ste_with_previous :: !SymbolPtr !*SymbolTable -> .SymbolTable
	replace_ste_with_previous changed_ste_ptr symbol_table
		#! ({ste_previous}, symbol_table) = readPtr changed_ste_ptr symbol_table
		= writePtr changed_ste_ptr ste_previous symbol_table
	
instance toString STE_Kind where
	toString (STE_FunctionOrMacro _)	= "function/macro"
	toString STE_Type 					= "type"
	toString STE_Constructor 			= "constructor"
	toString (STE_Field _) 				= "field"
	toString STE_Class 					= "class"
	toString STE_Member 				= "class member"
	toString (STE_Instance _)			= "instance"

check_whether_ident_is_imported :: !Ident !STE_Kind !CheckCompletenessInputBox !*CheckCompletenessStateBox 
								-> *CheckCompletenessStateBox
check_whether_ident_is_imported ident wanted_ste_kind cci ccs=:{box_ccs=box_ccs=:{ccs_symbol_table}}
	#! (ste=:{ste_kind}, ccs_symbol_table) = readPtr ident.id_info ccs_symbol_table
	   ccs = { ccs & box_ccs = { box_ccs & ccs_symbol_table = ccs_symbol_table } }
	| is_imported ste_kind wanted_ste_kind
		= ccs
	#! (ccs=:{box_ccs=box_ccs=:{ccs_symbol_table, ccs_error, ccs_heap_changes_accu}}) = ccs
	   {box_cci={cci_import_position}} = cci
	   ccs_error = checkErrorWithIdentPos (newPosition { id_name="import", id_info=nilPtr } cci_import_position)
	   				(" "+++toString wanted_ste_kind+++" "+++toString ident.id_name+++" not imported") ccs_error
	   // pretend that the unimported symbol was imported to prevent doubling error mesages
	   ccs_symbol_table = writePtr ident.id_info { ste & ste_kind = wanted_ste_kind, ste_previous = ste } ccs_symbol_table
	= { ccs & box_ccs = { box_ccs & ccs_error = ccs_error, ccs_symbol_table = ccs_symbol_table, 
									ccs_heap_changes_accu = [ident.id_info:ccs_heap_changes_accu] }}
  where
	is_imported (STE_Imported ste_kind _) wanted_ste_kind
		= ste_kind==wanted_ste_kind
	is_imported ste_kind wanted_ste_kind
		= ste_kind==wanted_ste_kind

class check_completeness x :: !x !CheckCompletenessInputBox !*CheckCompletenessStateBox -> *CheckCompletenessStateBox

instance check_completeness App where
	check_completeness {app_symb, app_args}	cci ccs
		= check_completeness app_symb cci
		  (check_completeness app_args cci ccs)
	
instance check_completeness AlgebraicPattern where
	check_completeness {ap_symbol, ap_expr} cci ccs
		= check_completeness ap_expr cci
		  (check_whether_ident_is_imported ap_symbol.glob_object.ds_ident STE_Constructor cci ccs)

instance check_completeness AType where
	check_completeness {at_type} cci ccs
		= check_completeness at_type cci ccs

instance check_completeness BasicPattern where
	check_completeness {bp_expr} cci ccs
		= check_completeness bp_expr cci ccs

instance check_completeness LetBind where
	check_completeness {lb_src} cci ccs
		= check_completeness lb_src cci ccs

instance check_completeness Case where
	check_completeness { case_expr, case_guards, case_default } cci ccs
		= ( (check_completeness case_expr cci)
		  o (check_completeness case_guards cci)
		  o (check_completeness case_default cci)
		  ) ccs

instance check_completeness CasePatterns where
	check_completeness (AlgebraicPatterns _ algebraicPatterns) cci ccs
		= check_completeness algebraicPatterns cci ccs
	check_completeness (BasicPatterns _ basicPatterns) cci ccs
		= check_completeness basicPatterns cci ccs
	check_completeness (DynamicPatterns dynamicPatterns) cci ccs
		= check_completeness dynamicPatterns cci ccs
	check_completeness NoPattern _ ccs
		= ccs

instance check_completeness CheckedAlternative where
	check_completeness {ca_rhs} cci ccs
		= check_completeness ca_rhs cci ccs

instance check_completeness CheckedBody where
	check_completeness {cb_rhs} cci ccs
		= check_completeness cb_rhs cci ccs

instance check_completeness ClassDef where
	check_completeness {class_context} cci ccs
		= check_completeness class_context cci ccs

instance check_completeness ClassInstance where
	check_completeness {ins_class, ins_type} cci ccs
		= check_completeness ins_type cci
		  (check_whether_ident_is_imported ins_class.glob_object.ds_ident STE_Class cci ccs)

instance check_completeness ConsDef
  where
	check_completeness {cons_type} cci ccs
		= check_completeness cons_type cci ccs

instance check_completeness DynamicPattern where
	check_completeness { dp_rhs, dp_type } cci ccs
		= check_completeness dp_rhs cci
		  (check_completeness_of_dyn_expr_ptr dp_type cci ccs)
	
instance check_completeness DynamicExpr where
	check_completeness { dyn_expr, dyn_opt_type } cci ccs
		= check_completeness dyn_expr cci
		  (check_completeness dyn_opt_type cci ccs)

instance check_completeness DynamicType where
	check_completeness { dt_type } cci ccs
		= check_completeness dt_type cci ccs

instance check_completeness Expression where
	check_completeness (Var _) cci ccs
		= ccs
	check_completeness (App app) cci ccs
		= check_completeness app cci ccs
	check_completeness (expression @ expressions) cci ccs
		= check_completeness expression cci
		  (check_completeness expressions cci ccs)
	check_completeness (Let lad) cci ccs
		= check_completeness lad cci ccs
	check_completeness (Case keesje) cci ccs
		= check_completeness keesje cci ccs
	check_completeness (Selection _ expression selections) cci ccs
		= check_completeness expression cci
		  (check_completeness selections cci ccs)
	check_completeness (TupleSelect _ _ expression) cci ccs
		= check_completeness expression cci ccs
	check_completeness (BasicExpr _ _) _ ccs
		= ccs
	check_completeness (AnyCodeExpr _ _ _) _ ccs
		= ccs
	check_completeness (ABCCodeExpr _ _) _ ccs
		= ccs
	check_completeness (MatchExpr _ constructor expression) cci ccs
		= check_completeness expression cci
		  (check_whether_ident_is_imported constructor.glob_object.ds_ident STE_Constructor cci ccs)
	check_completeness (FreeVar _) _ ccs
		= ccs
	check_completeness (DynamicExpr dynamicExpr) cci ccs
		= check_completeness dynamicExpr cci ccs
	check_completeness EE _ ccs
		= ccs
	check_completeness (Update expr1 selections expr2) cci ccs
		= ( (check_completeness expr1 cci)
		  o (check_completeness selections cci)
		  o (check_completeness expr2) cci
		  ) ccs
	check_completeness expr _ _
		= abort "explicitimports:check_completeness (Expression) does not match" <<- expr

instance check_completeness FunctionBody where
	check_completeness (CheckedBody body) cci ccs
		= check_completeness body cci ccs
	check_completeness (TransformedBody body) cci ccs
		= check_completeness body cci ccs
	check_completeness (RhsMacroBody body) cci ccs
		= check_completeness body cci ccs
			
instance check_completeness FunDef where
	check_completeness {fun_type, fun_body, fun_info} cci ccs
		= ( (check_completeness fun_type cci)
		  o (check_completeness fun_body cci)
		  o (foldSt (flipM check_completeness_of_dyn_expr_ptr cci) fun_info.fi_dynamics)
		  ) ccs

instance check_completeness FunType where
	check_completeness {ft_type} cci ccs
		= check_completeness ft_type cci ccs

instance check_completeness (Global x) | check_completeness x where
	check_completeness { glob_object } cci ccs
		= check_completeness glob_object cci ccs

instance check_completeness InstanceType where
	check_completeness {it_types, it_context} cci ccs
		= check_completeness it_types cci
		  (check_completeness it_context cci ccs)

instance check_completeness Let where
	check_completeness { let_strict_binds, let_lazy_binds, let_expr } cci ccs
  		= ( (check_completeness let_expr cci)
  		  o (check_completeness let_strict_binds cci)
  		  o (check_completeness let_lazy_binds cci)
  		  ) ccs

instance check_completeness MemberDef where
  	check_completeness {me_type} cci ccs 
  		= check_completeness me_type cci ccs

instance check_completeness (Optional x) | check_completeness x where
	check_completeness (Yes x) cci ccs
		= check_completeness x cci ccs
	check_completeness No _ ccs
		= ccs

instance check_completeness Selection where
	check_completeness (RecordSelection {glob_object,glob_module} _) cci ccs
		#! ({dcl_common}, ccs)	= ccs!box_ccs.ccs_dcl_modules.[glob_module]	// the selector's filed has to be looked up
		   ({sd_field}) = dcl_common.com_selector_defs.[glob_object.ds_index]
		= check_whether_ident_is_imported sd_field ste_field cci ccs
	check_completeness (ArraySelection _ _ index_expr) cci ccs
		= check_completeness index_expr cci ccs
	check_completeness (DictionarySelection _ selections _ index_expr) cci ccs
		= check_completeness selections cci
		  (check_completeness index_expr cci ccs)

instance check_completeness SelectorDef where
	check_completeness {sd_type} cci ccs
		= check_completeness sd_type cci ccs

instance check_completeness SymbIdent where
	check_completeness {symb_name, symb_kind} cci ccs
		= case symb_kind of
			SK_Constructor _
				-> check_whether_ident_is_imported symb_name STE_Constructor cci ccs
			SK_Function global_index
				-> check_completeness_for_function symb_name global_index ste_fun_or_macro cci ccs
			SK_LocalMacroFunction function_index
				-> check_completeness_for_local_macro_function symb_name function_index ste_fun_or_macro cci ccs
			SK_OverloadedFunction global_index
				-> check_completeness_for_function symb_name global_index STE_Member cci ccs
  			SK_Macro global_index
  				-> check_completeness_for_function symb_name global_index ste_fun_or_macro cci ccs
  	  where
		check_completeness_for_function symb_name {glob_object,glob_module} wanted_ste_kind cci ccs
			| glob_module<>cci.box_cci.cci_main_dcl_module_n
				// the function that is referred from within a macro is a DclFunction
				// -> must be global -> has to be imported
				= check_whether_ident_is_imported symb_name wanted_ste_kind cci ccs
			#! (fun_def, ccs)	= ccs!box_ccs.ccs_icl_functions.[glob_object]
			// otherwise the function was defined locally in a macro
			// it is not a consequence, but it's type and body are consequences !
			#! (already_visited, ccs) = ccs!box_ccs.ccs_set_of_visited_icl_funs.[glob_object]
			| already_visited
				= ccs
			#! ccs = { ccs & box_ccs.ccs_set_of_visited_icl_funs.[glob_object] = True }
			= check_completeness fun_def cci ccs

		check_completeness_for_local_macro_function symb_name glob_object wanted_ste_kind cci ccs
			#! (fun_def, ccs)	= ccs!box_ccs.ccs_icl_functions.[glob_object]
			// otherwise the function was defined locally in a macro
			// it is not a consequence, but it's type and body are consequences !
			#! (already_visited, ccs) = ccs!box_ccs.ccs_set_of_visited_icl_funs.[glob_object]
			| already_visited
				= ccs
			#! ccs = { ccs & box_ccs.ccs_set_of_visited_icl_funs.[glob_object] = True }
			= check_completeness fun_def cci ccs

instance check_completeness SymbolType where
	check_completeness {st_args, st_result, st_context} cci ccs
		= ( (check_completeness st_args cci)
		  o (check_completeness st_result cci)
		  o (check_completeness st_context cci)
		  ) ccs

instance check_completeness TransformedBody where
	check_completeness {tb_rhs} cci ccs
		= check_completeness tb_rhs cci ccs

instance check_completeness Type where
	check_completeness (TA {type_name} arguments) cci ccs
		= check_completeness arguments cci
		  (check_whether_ident_is_imported type_name STE_Type cci ccs)
	check_completeness (l --> r) cci ccs
		= check_completeness l cci
		  (check_completeness r cci ccs)
	check_completeness (_ :@: arguments) cci ccs
		= check_completeness arguments cci ccs
	check_completeness _ _ ccs
		= ccs

instance check_completeness TypeContext where
	check_completeness {tc_class, tc_types} cci ccs
		= check_completeness tc_types cci
		  (check_whether_ident_is_imported tc_class.glob_object.ds_ident STE_Class cci ccs)

instance check_completeness (TypeDef TypeRhs) where
	check_completeness {td_rhs, td_context}	cci ccs
		= check_completeness td_rhs cci 
		  (check_completeness td_context cci ccs)

instance check_completeness TypeRhs where
	check_completeness (SynType aType) cci ccs
		= check_completeness aType cci ccs
	check_completeness _ _ ccs
		= ccs

instance check_completeness [a]	| check_completeness a
  where
	check_completeness [] _ ccs
		= ccs
	check_completeness [h:t] cci ccs
		= check_completeness h cci
		  (check_completeness t cci ccs)

check_completeness_of_dyn_expr_ptr :: !ExprInfoPtr !CheckCompletenessInputBox !*CheckCompletenessStateBox
								-> *CheckCompletenessStateBox 
check_completeness_of_dyn_expr_ptr dyn_expr_ptr cci ccs=:{box_ccs=box_ccs=:{ccs_expr_heap}}
	#! (expr_info, ccs_expr_heap) = readPtr dyn_expr_ptr ccs_expr_heap
	   ccs = { ccs & box_ccs = { box_ccs & ccs_expr_heap = ccs_expr_heap }}
 	= case expr_info of
		(EI_Dynamic No)	
			-> ccs
		(EI_Dynamic (Yes dynamic_type))
			-> check_completeness dynamic_type cci ccs
		(EI_DynamicType dynamic_type further_dynamic_ptrs)
			-> check_completeness dynamic_type cci
			   (foldSt (flipM check_completeness_of_dyn_expr_ptr cci) further_dynamic_ptrs ccs)
		(EI_DynamicTypeWithVars _ dynamic_type further_dynamic_ptrs)
			-> check_completeness dynamic_type cci
			   (foldSt (flipM check_completeness_of_dyn_expr_ptr cci) further_dynamic_ptrs ccs)

flipM f a b :== f b a

// STE_Kinds just for comparision
ste_field =: STE_Field { id_name="", id_info=nilPtr }
ste_fun_or_macro =: STE_FunctionOrMacro []

stupid_ident =: { id_name = "stupid", id_info = nilPtr }

// XXX from m import :: T(..) works also if T is a record type

