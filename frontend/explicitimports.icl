implementation module explicitimports
// compile with reuse unique nodes option

import StdEnv

import syntax, typesupport, parse, checksupport, utilities, checktypes, transform, predef,
		compilerSwitches//, RWSDebug

cUndef :== (-1)
implies a b :== not a || b

:: ImportNrAndIdents =
	{	ini_symbol_nr	:: !Index
	,	ini_imp_decl	:: !ImportDeclaration
	}

:: SolvedImports =
	{	si_explicit	:: ![([Declaration], Position)]
	,	si_implicit	:: ![(Index, Position)]	// module indices
	}

markExplImpSymbols :: !Int !*(!*{!*{!u:ExplImpInfo}}, !*SymbolTable) -> (!.[Ident],!(!{!{!u:ExplImpInfo}},!.SymbolTable))
markExplImpSymbols component_nr (expl_imp_info, cs_symbol_table)
	#  (expl_imp_info_from_component,expl_imp_info) = replace expl_imp_info component_nr {}
	#! nr_of_expl_imp_symbols = size expl_imp_info_from_component
	#  (new_symbols, expl_imp_info_from_component, cs_symbol_table) = iFoldSt (mark_symbol component_nr) 0 nr_of_expl_imp_symbols ([], expl_imp_info_from_component, cs_symbol_table)
	   expl_imp_info = {expl_imp_info & [component_nr] = expl_imp_info_from_component}
	= (new_symbols, (expl_imp_info, cs_symbol_table))
  where
	mark_symbol component_nr i (changed_symbols_accu, expl_imp_info_from_component, cs_symbol_table)
		# (eii, expl_imp_info_from_component) = replace expl_imp_info_from_component i TemporarilyFetchedAway
		  (eii_ident, eii) = get_eei_ident eii
		  expl_imp_info_from_component = { expl_imp_info_from_component & [i] = eii }
		  (ste, cs_symbol_table) = readPtr eii_ident.id_info cs_symbol_table
		  cai = { cai_component_nr = component_nr, cai_index = i }
		= case ste.ste_kind of
			STE_ExplImpComponentNrs component_nrs
				# new_ste_kind = STE_ExplImpComponentNrs [cai:component_nrs]
				  cs_symbol_table = writePtr eii_ident.id_info { ste & ste_kind = new_ste_kind } cs_symbol_table
				-> (changed_symbols_accu, expl_imp_info_from_component, cs_symbol_table)
			_
				# new_ste = { ste & ste_kind = STE_ExplImpComponentNrs [cai], ste_previous = ste }
				-> ([eii_ident:changed_symbols_accu], expl_imp_info_from_component, writePtr eii_ident.id_info new_ste cs_symbol_table)

updateExplImpForMarkedSymbol :: !Index !Declaration !SymbolTableEntry !u:{#DclModule} !{!{!*ExplImpInfo}} !*SymbolTable
		-> (!u:{#DclModule}, !{!{!.ExplImpInfo}}, !.SymbolTable)
updateExplImpForMarkedSymbol mod_index decl {ste_kind=STE_ExplImpComponentNrs component_numbers} dcl_modules expl_imp_infos cs_symbol_table
	= foldSt (addExplImpInfo mod_index decl []) component_numbers (dcl_modules, expl_imp_infos, cs_symbol_table)
updateExplImpForMarkedSymbol _ _ entry dcl_modules expl_imp_infos cs_symbol_table
	= (dcl_modules, expl_imp_infos, cs_symbol_table)

addExplImpInfo :: !Index Declaration ![Declaration] !ComponentNrAndIndex !(!u:{#DclModule}, !{!{!*ExplImpInfo}}, !v:SymbolTable)
			-> (!u:{#DclModule}, !{!{!.ExplImpInfo}}, !v:SymbolTable)
addExplImpInfo mod_index decl instances { cai_component_nr, cai_index } (dcl_modules, expl_imp_infos, cs_symbol_table)
	# (ExplImpInfo eii_ident eii_declaring_modules, expl_imp_infos)
			= replaceTwoDimArrElt cai_component_nr cai_index TemporarilyFetchedAway expl_imp_infos
	  (di_belonging, dcl_modules, cs_symbol_table)
	  		= get_belonging_symbol_nrs decl dcl_modules cs_symbol_table
	  di = { di_decl = decl, di_instances = instances, di_belonging = di_belonging }
	  new_expl_imp_info = ExplImpInfo eii_ident (ikhInsert` False mod_index di eii_declaring_modules)
	= (dcl_modules, { expl_imp_infos & [cai_component_nr,cai_index] = new_expl_imp_info }, cs_symbol_table)
  where
	get_belonging_symbol_nrs :: !Declaration !v:{#DclModule} !u:(Heap SymbolTableEntry) 
							 -> (!.NumberSet,!v:{#DclModule},!u: Heap SymbolTableEntry)
	get_belonging_symbol_nrs decl dcl_modules cs_symbol_table
		# (all_belonging_symbols, dcl_modules) = getBelongingSymbols decl dcl_modules
		  nr_of_belongs = nrOfBelongingSymbols all_belonging_symbols
		  (_, belonging_bitvect, cs_symbol_table)
				= foldlBelongingSymbols set_bit all_belonging_symbols (0, bitvectCreate nr_of_belongs, cs_symbol_table)
		= (bitvectToNumberSet belonging_bitvect, dcl_modules, cs_symbol_table)

	set_bit {id_info} (bit_nr, bitvect, cs_symbol_table)
		# ({ste_kind}, cs_symbol_table) = readPtr id_info cs_symbol_table
		= ( bit_nr+1
		  , case ste_kind of
			 	STE_Empty -> bitvect
			 	STE_BelongingSymbolForExportedSymbol -> bitvect
				_ -> bitvectSet bit_nr bitvect
		  , cs_symbol_table
		  )

foldlBelongingSymbols f bs st
	:== case bs of
			BS_Constructors constructors
				-> foldSt (\{ds_ident} st -> f ds_ident st) constructors st 
			BS_Fields fields
				-> foldlArraySt (\{fs_ident} st -> f fs_ident st) fields st 
			BS_Members members
				-> foldlArraySt (\{ds_ident} st -> f ds_ident st) members st 
			BS_Nothing
				-> st
/*
imp_decl_to_string (ID_Function {ii_ident={id_name}}) = "ID_Function "+++toString id_name
imp_decl_to_string (ID_Class {ii_ident={id_name}} _) = "ID_Class "+++toString id_name
imp_decl_to_string (ID_Type {ii_ident={id_name}} _) = "ID_Type "+++toString id_name
imp_decl_to_string (ID_Record {ii_ident={id_name}} _) = "ID_Record "+++toString id_name
imp_decl_to_string (ID_Instance {ii_ident={id_name}} _ _ ) = "ID_Instance "+++toString id_name
imp_decl_to_string (ID_OldSyntax idents) = "ID_OldSyntax "+++idents_to_string idents
	where
		idents_to_string [] = ""
		idents_to_string [{id_name}] = toString id_name
		idents_to_string [{id_name}:l] = toString id_name+++","+++idents_to_string l
*/

getBelongingSymbolsFromID :: !ImportDeclaration -> Optional [ImportedIdent]
getBelongingSymbolsFromID (ID_Class _ x)						= x
getBelongingSymbolsFromID (ID_Type _ x)						= x
getBelongingSymbolsFromID (ID_Record _ x)						= x
getBelongingSymbolsFromID _									= No

solveExplicitImports :: !(IntKeyHashtable [(Int,Position,[ImportNrAndIdents])]) !{#Int} !Index 
								!*(!v:{#DclModule},!*{#Int},!{!*ExplImpInfo},!*CheckState)
			-> (!.SolvedImports,! (!v:{#DclModule},!.{#Int},!{!.ExplImpInfo},!.CheckState))
solveExplicitImports expl_imp_indices_ikh modules_in_component_set importing_mod (dcl_modules, visited_modules, expl_imp_info, cs)
	# import_indices = ikhSearch` importing_mod expl_imp_indices_ikh
	  expl_imp_indices = [ imports \\ imports=:(_, _, [_:_]) <- import_indices ]
	  impl_imports = [ (mod_index, position) \\ imports=:(mod_index, position, []) <- import_indices ]
	  (expl_imports, state)
	  		= mapSt (solve_expl_imp_from_module expl_imp_indices_ikh modules_in_component_set importing_mod)
					expl_imp_indices (dcl_modules, visited_modules, expl_imp_info, cs)
	= ({ si_explicit = expl_imports, si_implicit = impl_imports }, state)
  where
	solve_expl_imp_from_module expl_imp_indices_ikh modules_in_component_set importing_mod
			(imported_mod, position, imported_symbols) (dcl_modules, visited_modules, expl_imp_info, cs)
		# (not_exported_symbols,decl_accu, unsolved_belonging, visited_modules, expl_imp_info)
				= foldSt (search_expl_imp_symbol expl_imp_indices_ikh modules_in_component_set importing_mod imported_mod)
						imported_symbols
						([],[], [], visited_modules, expl_imp_info)
		  (expl_imp_info,cs_error) = report_not_exported_symbol_errors not_exported_symbols position expl_imp_info cs.cs_error
		  (decl_accu, dcl_modules, visited_modules, expl_imp_info, cs)
		  		= foldSt (solve_belonging position expl_imp_indices_ikh modules_in_component_set importing_mod)
		  				unsolved_belonging
		  				(decl_accu, dcl_modules, visited_modules, expl_imp_info, { cs & cs_error = cs_error }) 
		= ((decl_accu, position), (dcl_modules, visited_modules, expl_imp_info, cs))

	solve_belonging position expl_imp_indices_ikh modules_in_component_set importing_mod
			(decl, {ini_symbol_nr, ini_imp_decl}, imported_mod)
			(decls_accu, dcl_modules, visited_modules, expl_imp_info, cs=:{cs_error, cs_symbol_table})
		# (Yes belongs)
				= getBelongingSymbolsFromID ini_imp_decl
		  (all_belongs, dcl_modules)
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
						eii_declaring_modules (bitvectResetAll visited_modules)
		= case found of
			Yes _
				# eii_declaring_modules = foldSt (store_belonging belong_nr ini_symbol_nr) path eii_declaring_modules
				  (belong_decl, dcl_modules) = get_nth_belonging_decl position belong_nr decl dcl_modules
				-> ([belong_decl:decls_accu], dcl_modules, eii_declaring_modules, visited_modules, cs_error)
			_
				# cs_error
					= case need_all of
						True
							# cs_error = pushErrorAdmin (newPosition import_ident position) cs_error
							  cs_error = checkError belong_ident ("of "+++eii_ident.id_name+++" not exported by the specified module") cs_error
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

	get_nth_belonging_decl position belong_nr decl=:(Declaration {decl_kind}) dcl_modules
		# (STE_Imported _ def_mod_index) = decl_kind
		  (belongin_symbols, dcl_modules)
				= getBelongingSymbols decl dcl_modules
		= case belongin_symbols of
			BS_Constructors constructors
				# {ds_ident, ds_index} = constructors!!belong_nr
				-> (Declaration { decl_ident = ds_ident, decl_pos = position, 
						decl_kind = STE_Imported STE_Constructor def_mod_index,
						decl_index = ds_index }, dcl_modules)
			BS_Fields rt_fields
				# {fs_ident, fs_index} = rt_fields.[belong_nr]
				  ({sd_ident}, dcl_modules)
						= dcl_modules![def_mod_index].dcl_common.com_selector_defs.[fs_index]
				-> (Declaration { decl_ident = fs_ident, decl_pos = position, 
						decl_kind = STE_Imported (STE_Field sd_ident) def_mod_index,
						decl_index = fs_index }, dcl_modules)
			BS_Members class_members
				# {ds_ident, ds_index} = class_members.[belong_nr]
				-> (Declaration { decl_ident = ds_ident, decl_pos = position,
						 decl_kind = STE_Imported STE_Member def_mod_index,
						decl_index = ds_index }, dcl_modules)

	get_all_belongs decl=:(Declaration {decl_kind,decl_index}) dcl_modules
		# (belonging_symbols, dcl_modules)
				= getBelongingSymbols decl dcl_modules
		= case belonging_symbols of
			BS_Constructors constructors
				-> ([ds_ident \\ {ds_ident}<-constructors], dcl_modules)
			BS_Fields rt_fields
				-> ([fs_ident \\ {fs_ident}<-:rt_fields], dcl_modules)
			BS_Members class_members
				# (STE_Imported _ def_mod_index) = decl_kind
				  ({class_members}, dcl_modules)
						= dcl_modules![def_mod_index].dcl_common.com_class_defs.[decl_index]
				-> ([ds_ident \\ {ds_ident}<-:class_members], dcl_modules)
			BS_Nothing
				-> ([], dcl_modules)

	numerate_belongs {id_info} (i, cs_symbol_table)
		# (ste, cs_symbol_table) = readPtr id_info cs_symbol_table
		  new_ste = { ste & ste_kind = STE_BelongingSymbol i, ste_previous = ste }
		= (i+1, writePtr id_info new_ste cs_symbol_table)
	
	get_opt_nr_and_ident position eii_ident {ii_ident=ii_ident=:{id_info}} (cs_error, cs_symbol_table)
		# ({ste_kind}, cs_symbol_table) = readPtr id_info cs_symbol_table
		= case ste_kind of
			STE_BelongingSymbol i
				-> (Yes (i, ii_ident), (cs_error, cs_symbol_table))
			_
				# cs_error = pushErrorAdmin (newPosition import_ident position) cs_error
				  cs_error = checkError ii_ident ("does not belong to "+++eii_ident.id_name) cs_error 
				-> (No, (popErrorAdmin cs_error, cs_symbol_table))

	search_expl_imp_symbol :: (IntKeyHashtable [(Int,a,[ImportNrAndIdents])]) {#Int} Int Int ImportNrAndIdents
									*([ImportNrAndIdents],[Declaration],[(Declaration,ImportNrAndIdents,Int)],*{#Int},*{!*ExplImpInfo})
							-> ([ImportNrAndIdents],[Declaration],[(Declaration,ImportNrAndIdents,Int)],*{#Int},*{!*ExplImpInfo})
	search_expl_imp_symbol expl_imp_indices_ikh modules_in_component_set importing_mod imported_mod
			ini=:{ini_symbol_nr} (not_exported_symbols,decls_accu, belonging_accu, visited_modules, expl_imp_info)
		# (ExplImpInfo eii_ident eii_declaring_modules, expl_imp_info)
				= replace expl_imp_info ini_symbol_nr TemporarilyFetchedAway
		  (opt_decl, path, eii_declaring_modules, visited_modules)
				= depth_first_search expl_imp_indices_ikh modules_in_component_set imported_mod
						ini_symbol_nr cUndef stupid_ident [importing_mod]
						eii_declaring_modules (bitvectResetAll visited_modules)
		= case opt_decl of
			Yes di=:{di_decl, di_instances}
				| ( case di_decl of
			  			Declaration {decl_kind}
			  				-> case decl_kind of
			  					STE_Imported STE_Member _
			  						-> False
			  					STE_Member
			  						-> False
			  					_
			  						-> True
			  		)
					# new_eii_declaring_modules
					  		= foldSt (\mod_index eei_dm->ikhInsert` False mod_index 
					  					{di_decl = di_decl, di_instances = [], di_belonging=EndNumbers} eei_dm)
					  				path eii_declaring_modules
					  new_belonging_accu
					  		= case getBelongingSymbolsFromID ini.ini_imp_decl of
					  			No
					  				-> belonging_accu
					  			Yes _
					  				-> [(di_decl, ini, imported_mod):belonging_accu]
					  new_eii = ExplImpInfo eii_ident new_eii_declaring_modules
					-> (not_exported_symbols,[di_decl:di_instances++decls_accu], new_belonging_accu, visited_modules,
								{ expl_imp_info & [ini_symbol_nr] = new_eii })
				// otherwise GOTO next alternative
			_
				# eii = ExplImpInfo eii_ident eii_declaring_modules
				-> ([ini:not_exported_symbols],decls_accu, belonging_accu, visited_modules, { expl_imp_info & [ini_symbol_nr] = eii })

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
			# (found, opt_belongs)
					= search_imported_symbol imported_symbol imp_imp_symbols
			| not (found && implies (belong_nr<>cUndef) (belong_ident_found belong_ident opt_belongs))
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
	search_imported_symbol imported_symbol [{ini_symbol_nr, ini_imp_decl}:t]
		| imported_symbol==ini_symbol_nr
			= (True, getBelongingSymbolsFromID ini_imp_decl)
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

	report_not_exported_symbol_errors [{ini_symbol_nr,ini_imp_decl}:not_exported_symbols] position expl_imp_info cs_error
		# (eii_ident, expl_imp_info) = do_a_lot_just_to_read_an_array_2 ini_symbol_nr expl_imp_info
		  cs_error = popErrorAdmin (checkError eii_ident 
									("not exported as a "+++impDeclToNameSpaceString ini_imp_decl +++" by the specified module")
									(pushErrorAdmin (newPosition import_ident position) cs_error))
		= report_not_exported_symbol_errors not_exported_symbols position expl_imp_info cs_error
	report_not_exported_symbol_errors [] position expl_imp_info cs_error
		= (expl_imp_info,cs_error)

	do_a_lot_just_to_read_an_array_2 i expl_imp_info
		# (eii, expl_imp_info) = replace expl_imp_info i TemporarilyFetchedAway
		  (eii_ident, eii) = get_eei_ident eii
		= (eii_ident, { expl_imp_info & [i] = eii })

	impDeclToNameSpaceString (ID_Function _)	= "function/macro"
	impDeclToNameSpaceString (ID_Class _ _)		= "class"
	impDeclToNameSpaceString (ID_Type _ _)		= "type"
	impDeclToNameSpaceString (ID_Record _ _)	= "type"
	impDeclToNameSpaceString (ID_Instance _ _ _)= "instance"

get_eei_ident (eii=:ExplImpInfo eii_ident _) = (eii_ident, eii)
	
:: CheckCompletenessState =
	{	ccs_dcl_modules				:: !.{#DclModule}
	,	ccs_icl_functions			:: !.{#FunDef}
	,	ccs_macro_defs :: !.{#.{#FunDef}}
	,	ccs_set_of_visited_icl_funs	:: !.{#Bool}		// ccs_set_of_visited_icl_funs.[i] <=> function nr i has been considered
	,	ccs_set_of_visited_macros	:: !.{#.{#Bool}}
	,	ccs_expr_heap				:: !.ExpressionHeap
	,	ccs_symbol_table			:: !.SymbolTable
	,	ccs_error					:: !.ErrorAdmin
	,	ccs_heap_changes_accu		:: ![SymbolPtr]
	}

:: CheckCompletenessStateBox = { box_ccs :: !.CheckCompletenessState }

:: CheckCompletenessInput =
	{	cci_import_position		:: !Position
	,	cci_main_dcl_module_n	:: !Int
	}

:: CheckCompletenessInputBox = { box_cci :: !CheckCompletenessInput }

checkExplicitImportCompleteness :: ![([Declaration], Position)] !*{#DclModule} !*{#FunDef} !*{#*{#FunDef}} !*ExpressionHeap !*CheckState
															-> (!.{#DclModule},!.{#FunDef},!*{#*{#FunDef}},!.ExpressionHeap,!.CheckState)
checkExplicitImportCompleteness dcls_explicit dcl_modules icl_functions macro_defs expr_heap cs=:{cs_symbol_table, cs_error}
	#! nr_icl_functions = size icl_functions
	#! n_dcl_modules = size dcl_modules
	#  box_ccs = { ccs_dcl_modules = dcl_modules, ccs_icl_functions = icl_functions, ccs_macro_defs=macro_defs,
	   			ccs_set_of_visited_icl_funs = createArray nr_icl_functions False,
	   			ccs_set_of_visited_macros = { {} \\ module_n<-[0..n_dcl_modules-1]},
				ccs_expr_heap = expr_heap, ccs_symbol_table = cs_symbol_table,
				ccs_error = cs_error, ccs_heap_changes_accu = [] }
	   main_dcl_module_n
	   		= cs.cs_x.x_main_dcl_module_n
//	   ccs = foldSt (checkCompleteness main_dcl_module_n) dcls_explicit { box_ccs = box_ccs }
	   ccs = foldSt (\(dcls, position) ccs
	   					-> foldSt (checkCompleteness main_dcl_module_n position) dcls ccs)
	   				dcls_explicit
	   				{ box_ccs = box_ccs }
	   { ccs_dcl_modules, ccs_icl_functions,ccs_macro_defs,ccs_expr_heap, ccs_symbol_table, ccs_error, ccs_heap_changes_accu } = ccs.box_ccs
	// repair heap contents
	   ccs_symbol_table = foldSt replace_ste_with_previous ccs_heap_changes_accu ccs_symbol_table
	   cs = { cs & cs_symbol_table = ccs_symbol_table, cs_error = ccs_error }
	= (ccs_dcl_modules, ccs_icl_functions,ccs_macro_defs, ccs_expr_heap, cs)
  where
	checkCompleteness :: !Int !Position !Declaration !*CheckCompletenessStateBox -> *CheckCompletenessStateBox
	checkCompleteness main_dcl_module_n import_position (Declaration {decl_ident, decl_index, decl_kind=STE_FunctionOrMacro _}) ccs 
		= checkCompletenessOfMacro decl_ident decl_index main_dcl_module_n import_position ccs
	checkCompleteness main_dcl_module_n import_position (Declaration {decl_ident, decl_index, decl_kind=STE_Imported (STE_FunctionOrMacro _) mod_index}) ccs 
		= checkCompletenessOfMacro decl_ident decl_index main_dcl_module_n import_position ccs
	checkCompleteness main_dcl_module_n import_position (Declaration {decl_ident, decl_index, decl_kind=STE_Imported expl_imp_kind mod_index}) ccs
		#! ({dcl_common,dcl_functions}, ccs) = ccs!box_ccs.ccs_dcl_modules.[mod_index]
		   cci = { box_cci = { cci_import_position = import_position, cci_main_dcl_module_n=main_dcl_module_n }}
		= continuation expl_imp_kind dcl_common dcl_functions cci ccs
	  where
		continuation :: !STE_Kind CommonDefs !{# FunType} !CheckCompletenessInputBox !*CheckCompletenessStateBox
					-> *CheckCompletenessStateBox
		continuation STE_Type dcl_common dcl_functions cci ccs
			= check_completeness dcl_common.com_type_defs.[decl_index] cci ccs
		continuation STE_Constructor dcl_common dcl_functions cci ccs
			= check_completeness dcl_common.com_cons_defs.[decl_index] cci ccs
		continuation (STE_Field _) dcl_common dcl_functions cci ccs
			= check_completeness dcl_common.com_selector_defs.[decl_index] cci ccs
		continuation STE_Class dcl_common dcl_functions cci ccs
			= check_completeness dcl_common.com_class_defs.[decl_index] cci ccs
		continuation STE_Member dcl_common dcl_functions cci ccs
			= check_completeness dcl_common.com_member_defs.[decl_index] cci ccs
		continuation STE_Instance dcl_common dcl_functions cci ccs
			= check_completeness dcl_common.com_instance_defs.[decl_index] cci ccs
		continuation STE_DclFunction dcl_common dcl_functions cci ccs
			= check_completeness dcl_functions.[decl_index] cci ccs
		continuation (STE_DclMacroOrLocalMacroFunction _) dcl_common dcl_functions cci ccs
			# (macro,ccs) = ccs!box_ccs.ccs_macro_defs.[mod_index,decl_index]
			= check_completeness macro cci ccs
	
	checkCompletenessOfMacro :: !Ident !Index !Int !Position !*CheckCompletenessStateBox -> *CheckCompletenessStateBox
	checkCompletenessOfMacro decl_ident decl_index main_dcl_module_n import_position ccs
		#! ({fun_body}, ccs) = ccs!box_ccs.ccs_icl_functions.[decl_index]
		   ccs = { ccs & box_ccs.ccs_set_of_visited_icl_funs.[decl_index] = True }
		   cci = { box_cci = { cci_import_position = import_position, cci_main_dcl_module_n=main_dcl_module_n }}
		= check_completeness fun_body cci ccs
	
	replace_ste_with_previous :: !SymbolPtr !*SymbolTable -> .SymbolTable
	replace_ste_with_previous changed_ste_ptr symbol_table
		#! ({ste_previous}, symbol_table) = readPtr changed_ste_ptr symbol_table
		= writePtr changed_ste_ptr ste_previous symbol_table
	
instance toString STE_Kind where
	toString (STE_FunctionOrMacro _)	= "function/macro"
	toString (STE_DclMacroOrLocalMacroFunction _) = "macro"
	toString STE_Type 					= "type"
	toString STE_Constructor 			= "constructor"
	toString (STE_Field _) 				= "field"
	toString STE_Class 					= "class"
	toString STE_Member 				= "class member"
	toString STE_Generic 				= "generic"			//AA
	toString STE_Instance				= "instance"
	toString ste						= "<<unknown symbol kind>>"

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
	check_completeness (OverloadedListPatterns _ _ algebraicPatterns) cci ccs
		= check_completeness algebraicPatterns cci ccs
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
		  (check_completeness_of_dyn_expr_ptr cci dp_type ccs)
	
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
	check_completeness (BasicExpr _) _ ccs
		= ccs
	check_completeness (AnyCodeExpr _ _ _) _ ccs
		= ccs
	check_completeness (ABCCodeExpr _ _) _ ccs
		= ccs
	check_completeness (MatchExpr constructor expression) cci ccs
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
		= abort "explicitimports:check_completeness (Expression) does not match" //<<- expr

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
		  o (check_completeness_of_dyn_expr_ptrs cci fun_info.fi_dynamics)
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
	check_completeness {symb_ident, symb_kind} cci ccs
		= case symb_kind of
			SK_Constructor _
				-> check_whether_ident_is_imported symb_ident STE_Constructor cci ccs
			SK_Function global_index			
				-> check_completeness_for_function symb_ident global_index cci ccs
  			SK_DclMacro global_index
				-> check_completeness_for_macro symb_ident global_index cci ccs
			SK_LocalDclMacroFunction global_index
				-> check_completeness_for_local_dcl_macro symb_ident global_index cci ccs
			SK_LocalMacroFunction function_index
				-> check_completeness_for_local_macro_function symb_ident function_index cci ccs
			SK_OverloadedFunction global_index
				-> check_whether_ident_is_imported symb_ident STE_Member cci ccs
  	  where
		check_completeness_for_function symb_ident {glob_object,glob_module} cci ccs
			| glob_module<>cci.box_cci.cci_main_dcl_module_n
				// the function that is referred from within a macro is a DclFunction
				// -> must be global -> has to be imported
				= check_whether_ident_is_imported symb_ident (STE_FunctionOrMacro []) cci ccs
			// otherwise the function was defined locally in a macro
			// it is not a consequence, but it's type and body are consequences !
			#! (already_visited, ccs) = ccs!box_ccs.ccs_set_of_visited_icl_funs.[glob_object]
			| /* ccs.box_ccs.ccs_set_of_visited_icl_funs.[glob_object] */ already_visited
				= ccs
				# ccs = { ccs & box_ccs.ccs_set_of_visited_icl_funs.[glob_object] = True }
				# (fun_def, ccs)	= ccs!box_ccs.ccs_icl_functions.[glob_object]
				= check_completeness fun_def cci ccs

		check_completeness_for_macro symb_ident global_index cci ccs
			| global_index.glob_module<>cci.box_cci.cci_main_dcl_module_n
				= check_whether_ident_is_imported symb_ident (STE_DclMacroOrLocalMacroFunction []) cci ccs
				= check_completeness_for_local_dcl_macro symb_ident global_index cci ccs

		check_completeness_for_local_dcl_macro symb_ident {glob_module,glob_object} cci ccs
			| size ccs.box_ccs.ccs_set_of_visited_macros.[glob_module]==0
//				#! n_macros_in_dcl_module=size ccs.box_ccs.ccs_macro_defs.[glob_module]
				# (n_macros_in_dcl_module,ccs) = get_n_macros_in_dcl_module ccs glob_module
					with
						get_n_macros_in_dcl_module :: *CheckCompletenessStateBox Int -> (!Int,!*CheckCompletenessStateBox)
						get_n_macros_in_dcl_module ccs glob_module
							#! n_macros_in_dcl_module=size ccs.box_ccs.ccs_macro_defs.[glob_module]
							= (n_macros_in_dcl_module,ccs)
				# visited_dcl_macros = {createArray n_macros_in_dcl_module False & [glob_object]=True}
				# ccs= {ccs & box_ccs.ccs_set_of_visited_macros.[glob_module]=visited_dcl_macros}
				# (macro_def, ccs) = ccs!box_ccs.ccs_macro_defs.[glob_module,glob_object]
				= check_completeness macro_def cci ccs
			| ccs.box_ccs.ccs_set_of_visited_macros.[glob_module].[glob_object]
				= ccs
				# ccs = {ccs & box_ccs.ccs_set_of_visited_macros.[glob_module].[glob_object]=True}
				# (macro_def, ccs) = ccs!box_ccs.ccs_macro_defs.[glob_module,glob_object]
				= check_completeness macro_def cci ccs

		check_completeness_for_local_macro_function symb_ident glob_object cci ccs
			// otherwise the function was defined locally in a macro
			// it is not a consequence, but it's type and body are consequences !
			| ccs.box_ccs.ccs_set_of_visited_icl_funs.[glob_object]
				= ccs
				# ccs = { ccs & box_ccs.ccs_set_of_visited_icl_funs.[glob_object] = True }
				# (fun_def, ccs)	= ccs!box_ccs.ccs_icl_functions.[glob_object]
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
	check_completeness (TA {type_ident} arguments) cci ccs
		= check_completeness arguments cci
		  (check_whether_ident_is_imported type_ident STE_Type cci ccs)
	check_completeness (TAS {type_ident} arguments _) cci ccs
		= check_completeness arguments cci
		  (check_whether_ident_is_imported type_ident STE_Type cci ccs)
	check_completeness (l --> r) cci ccs
		= check_completeness l cci
		  (check_completeness r cci ccs)
	check_completeness (_ :@: arguments) cci ccs
		= check_completeness arguments cci ccs
	check_completeness _ _ ccs
		= ccs

instance check_completeness TypeContext where
	check_completeness {tc_class=TCClass class_symb, tc_types} cci ccs
		= check_completeness tc_types cci
		  (check_whether_ident_is_imported class_symb.glob_object.ds_ident STE_Class cci ccs)
	check_completeness {tc_class=TCGeneric {gtc_generic}, tc_types} cci ccs
		= check_completeness tc_types cci
		  (check_whether_ident_is_imported gtc_generic.glob_object.ds_ident STE_Generic cci ccs)
	

instance check_completeness (TypeDef TypeRhs) where
	check_completeness td=:{td_rhs, td_context}	cci ccs
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

check_completeness_of_dyn_expr_ptr :: !CheckCompletenessInputBox !ExprInfoPtr !*CheckCompletenessStateBox
								-> *CheckCompletenessStateBox 
check_completeness_of_dyn_expr_ptr cci dyn_expr_ptr ccs=:{box_ccs=box_ccs=:{ccs_expr_heap}}
	#! (expr_info, ccs_expr_heap) = readPtr dyn_expr_ptr ccs_expr_heap
	   ccs = { ccs & box_ccs = { box_ccs & ccs_expr_heap = ccs_expr_heap }}
 	= case expr_info of
		(EI_UnmarkedDynamic No further_dynamic_ptrs)
			-> (check_completeness_of_dyn_expr_ptrs cci further_dynamic_ptrs ccs)
		(EI_UnmarkedDynamic (Yes dynamic_type) further_dynamic_ptrs) 
			-> check_completeness dynamic_type cci (check_completeness_of_dyn_expr_ptrs cci further_dynamic_ptrs ccs)
		(EI_Dynamic No further_dynamic_ptrs)
			-> (check_completeness_of_dyn_expr_ptrs cci further_dynamic_ptrs ccs)
		(EI_Dynamic (Yes dynamic_type) further_dynamic_ptrs) 
			-> check_completeness dynamic_type cci (check_completeness_of_dyn_expr_ptrs cci further_dynamic_ptrs ccs)
		(EI_DynamicType dynamic_type further_dynamic_ptrs)
			-> check_completeness dynamic_type cci (check_completeness_of_dyn_expr_ptrs cci further_dynamic_ptrs ccs)
		(EI_DynamicTypeWithVars _ dynamic_type further_dynamic_ptrs)
			-> check_completeness dynamic_type cci
			   	(check_completeness_of_dyn_expr_ptrs cci further_dynamic_ptrs ccs)

check_completeness_of_dyn_expr_ptrs :: !CheckCompletenessInputBox ![ExprInfoPtr] !*CheckCompletenessStateBox
	-> *CheckCompletenessStateBox 
check_completeness_of_dyn_expr_ptrs cci dynamic_ptrs ccs
	= foldSt (check_completeness_of_dyn_expr_ptr cci) dynamic_ptrs ccs


// STE_Kinds just for comparision
ste_field =: STE_Field { id_name="", id_info=nilPtr }

stupid_ident =: { id_name = "stupid", id_info = nilPtr }

// XXX from m import :: T(..) works also if T is a record type

