implementation module explicitimports
// compile with reuse unique nodes option

import StdEnv

import syntax, typesupport, parse, checksupport, utilities, checktypes, transform, predef
from compare_constructor import equal_constructor

:: *ExplImpInfos :== *{#*{!*ExplImpInfo}}

:: ExplImpInfo = ExplImpInfo Ident !.DeclaringModulesSet

:: DeclaringModulesSet :== IntKeyHashtable DeclarationInfo

:: DeclarationInfo
	= DeclarationAndBelongings !Declaration !NumberSet
	| NoDeclarationAndBelongings !Declaration !NumberSet

:: ImportNrAndIdents =
	{	ini_symbol_nr	:: !Index
	,	ini_imp_decl	:: !ImportDeclaration
	}

:: QualifiedAndHiddenDeclaration
	= QualifiedHiddenDeclaration !Declaration // qualified and hidden
	| QualifiedNotHiddenDeclaration !Declaration // qualified and not hidden, because imported by another import in the same module
	| QualifiedSomeNotHiddenDeclaration !Declaration ![Int] // qualified and hidden, not hidden in some (other) modules of the component

:: SolvedImports =
	{	si_explicit :: ![([Declaration], Position)]
	,	si_qualified_explicit :: ![QualifiedDeclaration]
	,	si_qualified_hidden_explicit :: ![([QualifiedAndHiddenDeclaration], ModuleN)]
	,	si_implicit :: ![(ModuleN, Position)]
	}

idents_to_empty_ExplImpInfo_array :: ![Ident] -> *{!*ExplImpInfo}
idents_to_empty_ExplImpInfo_array expl_imp_symbols_in_component
	= {ExplImpInfo expl_imp_symbol ikhEmpty \\ expl_imp_symbol <- expl_imp_symbols_in_component}

addDeclarationWithAllBelongingsToExplImpInfo :: !Declaration !BelongingSymbols !Index !ComponentNrAndIndex !ExplImpInfos -> ExplImpInfos
addDeclarationWithAllBelongingsToExplImpInfo decl all_belong_s mod_index {cai_component_nr,cai_index} expl_imp_infos
	# (ExplImpInfo eii_ident eii_declaring_modules, expl_imp_infos) = expl_imp_infos![cai_component_nr,cai_index]
	  di_belonging = nsFromTo (nrOfBelongingSymbols all_belong_s)
	  di = DeclarationAndBelongings decl di_belonging
	# (new,eii_declaring_modules) = ikhInsert False mod_index di eii_declaring_modules
	| new
		= {expl_imp_infos & [cai_component_nr,cai_index] = ExplImpInfo eii_ident eii_declaring_modules}
		= case ikhSearch` mod_index eii_declaring_modules of
			NoDeclarationAndBelongings _ _
				# eii_declaring_modules = ikhInsert` True mod_index di eii_declaring_modules
				-> {expl_imp_infos & [cai_component_nr,cai_index] = ExplImpInfo eii_ident eii_declaring_modules}
			_
				-> {expl_imp_infos & [cai_component_nr,cai_index] = ExplImpInfo eii_ident eii_declaring_modules}

markExplImpSymbols :: !Int !*(!*ExplImpInfos,!*SymbolTable) -> (!.[Ident],!(!*ExplImpInfos,!*SymbolTable))
markExplImpSymbols component_nr (expl_imp_info, cs_symbol_table)
	#  (expl_imp_info_from_component,expl_imp_info) = expl_imp_info![component_nr]
	#! nr_of_expl_imp_symbols = size expl_imp_info_from_component
	#  (new_symbols, expl_imp_info_from_component, cs_symbol_table) = iFoldSt (mark_symbol component_nr) 0 nr_of_expl_imp_symbols ([], expl_imp_info_from_component, cs_symbol_table)
	   expl_imp_info = {expl_imp_info & [component_nr] = expl_imp_info_from_component}
	= (new_symbols, (expl_imp_info, cs_symbol_table))
  where
	mark_symbol component_nr i (changed_symbols_accu, expl_imp_info_from_component, cs_symbol_table)
		# (eii, expl_imp_info_from_component) = expl_imp_info_from_component![i]
		  (eii_ident, eii) = get_eei_ident eii
		  expl_imp_info_from_component = {expl_imp_info_from_component & [i] = eii}
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

updateExplImpForMarkedSymbol :: !Index !Declaration !SymbolTableEntry !u:{#DclModule} !*ExplImpInfos !*SymbolTable
																  -> (!u:{#DclModule},!*ExplImpInfos,!*SymbolTable)
updateExplImpForMarkedSymbol mod_index decl {ste_kind=STE_ExplImpComponentNrs component_numbers} dcl_modules expl_imp_infos cs_symbol_table
	= foldSt (addExplImpInfo mod_index decl) component_numbers (dcl_modules, expl_imp_infos, cs_symbol_table)
updateExplImpForMarkedSymbol _ _ entry dcl_modules expl_imp_infos cs_symbol_table
	= (dcl_modules, expl_imp_infos, cs_symbol_table)

addExplImpInfo :: !Index Declaration !ComponentNrAndIndex !(!u:{#DclModule},!*ExplImpInfos,!*SymbolTable)
														-> (!u:{#DclModule},!*ExplImpInfos,!*SymbolTable)
addExplImpInfo mod_index decl { cai_component_nr, cai_index } (dcl_modules, expl_imp_infos, cs_symbol_table)
	# (ExplImpInfo eii_ident eii_declaring_modules, expl_imp_infos) = expl_imp_infos![cai_component_nr,cai_index]
	  (di_belonging, dcl_modules, cs_symbol_table)
	  		= get_belonging_symbol_nrs decl dcl_modules cs_symbol_table
	  di = DeclarationAndBelongings decl di_belonging
	  (new,eii_declaring_modules) = ikhInsert False mod_index di eii_declaring_modules
	| new
		= (dcl_modules, { expl_imp_infos & [cai_component_nr,cai_index] = ExplImpInfo eii_ident eii_declaring_modules }, cs_symbol_table)
		= case ikhSearch` mod_index eii_declaring_modules of
			NoDeclarationAndBelongings _ _
				# eii_declaring_modules = ikhInsert` True mod_index di eii_declaring_modules
				-> (dcl_modules, {expl_imp_infos & [cai_component_nr,cai_index] = ExplImpInfo eii_ident eii_declaring_modules}, cs_symbol_table)
			_
				-> (dcl_modules, {expl_imp_infos & [cai_component_nr,cai_index] = ExplImpInfo eii_ident eii_declaring_modules}, cs_symbol_table)
  where
	get_belonging_symbol_nrs :: !Declaration !v:{#DclModule} !*SymbolTable
							 -> (!.NumberSet,!v:{#DclModule},!*SymbolTable)
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
			BS_MembersAndMacros members macro_members _ default_macros
				# st = foldlArraySt (\{ds_ident} st -> f ds_ident st) members st
				# st = foldlArraySt (\{mm_ident} st -> f mm_ident st) macro_members st
				-> foldlArraySt (\{mm_ident} st -> f mm_ident st) default_macros st
			BS_Nothing
				-> st

FoldSt op l st :== fold_st l st
	where
		fold_st [|] st		= st
		fold_st [|a:x] st	= fold_st x (op a st)

getBelongingSymbolsFromImportDeclaration :: !ImportDeclaration -> ImportBelongings
getBelongingSymbolsFromImportDeclaration (ID_Class _ x) = x
getBelongingSymbolsFromImportDeclaration (ID_Type _ x) = x
getBelongingSymbolsFromImportDeclaration (ID_Record _ x) = x
getBelongingSymbolsFromImportDeclaration _ = IB_None

importDeclarationImportsBelongingSymbols :: !ImportDeclaration -> Bool
importDeclarationImportsBelongingSymbols (ID_Class _ (IB_Idents _)) = True
importDeclarationImportsBelongingSymbols (ID_Class _ (IB_IdentsAndOptIdents _ _)) = True
importDeclarationImportsBelongingSymbols (ID_Type _ (IB_Idents _)) = True
importDeclarationImportsBelongingSymbols (ID_Record _ (IB_Idents _)) = True
importDeclarationImportsBelongingSymbols _ = False

:: ExplicitImportsModuleInfo = {
	eimi_module_path :: ![Int],
	eimi_modules_explicit_imports :: !IntKeyHashtable [ExplicitImport],
	eimi_component_mods :: !{#Int}
   }

:: Belonging = {
	belonging_declaration :: !Declaration,
	belonging_import_n_and_idents :: !ImportNrAndIdents,
	belonging_imported_mod :: !Int
   }

solveExplicitImports :: !(IntKeyHashtable [ExplicitImport]) !{#Int} ![Index] !Index
								!*(!v:{#DclModule},!*{#Int},!{!*ExplImpInfo},!*CheckState)
			-> (!.SolvedImports,! (!v:{#DclModule},!.{#Int},!{!.ExplImpInfo},!.CheckState))
solveExplicitImports expl_imp_indices_ikh modules_in_component_set modules_in_component importing_mod (dcl_modules, visited_modules, expl_imp_info, cs)
	# import_indices = ikhSearch` importing_mod expl_imp_indices_ikh
	  (expl_imp_indices,qualified_expl_imp_indices,qualfied_hidden_imports,impl_imports) = split_imports import_indices
	  state = (dcl_modules, visited_modules, expl_imp_info, cs)
	  eimi = {eimi_module_path=[importing_mod],eimi_modules_explicit_imports=expl_imp_indices_ikh,eimi_component_mods=modules_in_component_set}
	  (expl_imports, state) = mapSt (solve_expl_imp_from_module eimi) expl_imp_indices state
	  eimi = {eimi_module_path=[],eimi_modules_explicit_imports=expl_imp_indices_ikh,eimi_component_mods=modules_in_component_set}
	  other_modules_in_component = [module_in_component \\ module_in_component<-modules_in_component | module_in_component<>importing_mod]
	  (qualified_hidden_imports, state) = solve_qualified_hidden_imports qualfied_hidden_imports importing_mod other_modules_in_component eimi state
	  eimi = {eimi_module_path=[],eimi_modules_explicit_imports=expl_imp_indices_ikh,eimi_component_mods=modules_in_component_set}
	  (qualified_expl_imports, state) = mapSt (solve_qualified_expl_imp_from_module eimi) qualified_expl_imp_indices state
	  si = {si_explicit=expl_imports, si_qualified_explicit=qualified_expl_imports, si_qualified_hidden_explicit=qualified_hidden_imports, si_implicit=impl_imports}
	= (si, state)
  where
	split_imports :: [ExplicitImport] -> (![ExplicitImport],![ExplicitImport],![ExplicitImport],![(Int,Position)])
	split_imports [imports:import_indices]
		# (expl_imp_indices,qualified_expl_imp_indices,qualified_hidden_imports,impl_imports) = split_imports import_indices
		= case imports of
			{ei_symbols=ImportSymbolsOnly _,ei_qualified=NotQualified}
				-> ([imports:expl_imp_indices],qualified_expl_imp_indices,qualified_hidden_imports,impl_imports)
			{ei_symbols=ImportSymbolsOnly _}
				-> (expl_imp_indices,[imports:qualified_expl_imp_indices],qualified_hidden_imports,impl_imports)
			{ei_symbols=ImportSymbolsAll,ei_module_n,ei_position}
				-> (expl_imp_indices,qualified_expl_imp_indices,qualified_hidden_imports,[(ei_module_n,ei_position):impl_imports])
			{ei_symbols=ImportSymbolsAllSomeQualified _,ei_module_n,ei_position}
				-> (expl_imp_indices,qualified_expl_imp_indices,[imports:qualified_hidden_imports],[(ei_module_n,ei_position):impl_imports])
	split_imports []
		= ([],[],[],[])

	solve_expl_imp_from_module :: ExplicitImportsModuleInfo ExplicitImport
															*(v:{#DclModule},*{#Int},*{!*ExplImpInfo},*CheckState)
								-> (([Declaration],Position),(v:{#DclModule},*{#Int},*{!*ExplImpInfo},*CheckState))
	solve_expl_imp_from_module eimi
			{ei_symbols=ImportSymbolsOnly imported_symbols, ei_module_n=imported_mod, ei_position=position} (dcl_modules, visited_modules, expl_imp_info, cs)
		# (not_exported_symbols,decl_accu, unsolved_belongings, visited_modules, expl_imp_info)
				= search_expl_imp_symbols imported_symbols eimi imported_mod visited_modules expl_imp_info
		  (expl_imp_info,dcl_modules,cs_error)
		  		= report_not_exported_symbol_errors not_exported_symbols position expl_imp_info imported_mod dcl_modules cs.cs_error
		  (decl_accu, dcl_modules, visited_modules, expl_imp_info, cs)
		  		= solve_belongings unsolved_belongings position eimi (decl_accu,dcl_modules,visited_modules,expl_imp_info,{cs & cs_error=cs_error})
		= ((decl_accu, position), (dcl_modules, visited_modules, expl_imp_info, cs))

	solve_qualified_hidden_imports :: [ExplicitImport] Int [Int] ExplicitImportsModuleInfo
																				*(v:{#DclModule},*{#Int},*{!*ExplImpInfo},*CheckState)
									-> ([([QualifiedAndHiddenDeclaration],Int)],*(v:{#DclModule},*{#Int},*{!*ExplImpInfo},*CheckState))
	solve_qualified_hidden_imports [hidden_imports_from_module:hidden_imports_from_modules] importing_mod other_modules_in_component eimi state
		# (hidden_module_imports,state) = solve_qualified_hidden_imports_from_module eimi hidden_imports_from_module importing_mod other_modules_in_component state
		# (hidden_modules_imports,state) = solve_qualified_hidden_imports hidden_imports_from_modules importing_mod other_modules_in_component eimi state
		= ([hidden_module_imports:hidden_modules_imports],state)
	solve_qualified_hidden_imports [] importing_mod other_modules_in_component eimi state
		= ([],state)

	solve_qualified_hidden_imports_from_module :: ExplicitImportsModuleInfo ExplicitImport Int [Int]
																						 *(v:{#DclModule},*{#Int},*{!*ExplImpInfo},*CheckState)
												-> (([QualifiedAndHiddenDeclaration],Int),(v:{#DclModule},*{#Int},*{!*ExplImpInfo},*CheckState))
	solve_qualified_hidden_imports_from_module eimi
			{ei_symbols=ImportSymbolsAllSomeQualified imported_symbols, ei_module_n=imported_mod, ei_position=position}
			importing_mod other_modules_in_component (dcl_modules, visited_modules, expl_imp_info, cs)
		# (not_exported_symbols,decl_accu, unsolved_belonging, dcl_modules, visited_modules, expl_imp_info)
			= search_qualified_hidden_symbols imported_symbols eimi imported_mod importing_mod other_modules_in_component
												dcl_modules visited_modules expl_imp_info
		  (expl_imp_info,dcl_modules,cs_error)
			= report_not_exported_symbol_errors not_exported_symbols position expl_imp_info imported_mod dcl_modules cs.cs_error
		  (decl_accu, dcl_modules, visited_modules, expl_imp_info, cs)
		  	= solve_qualified_hidden_belongings unsolved_belonging position importing_mod other_modules_in_component eimi
		  		(decl_accu,dcl_modules,visited_modules,expl_imp_info,{cs & cs_error=cs_error})
		= ((decl_accu,imported_mod), (dcl_modules, visited_modules, expl_imp_info, cs))

	solve_qualified_expl_imp_from_module :: ExplicitImportsModuleInfo ExplicitImport
																	*(v:{#DclModule},*{#Int},*{!*ExplImpInfo},*CheckState)
											-> (QualifiedDeclaration,(v:{#DclModule},*{#Int},*{!*ExplImpInfo},*CheckState))
	solve_qualified_expl_imp_from_module eimi
			{ei_symbols=ImportSymbolsOnly imported_symbols, ei_module_n=imported_mod, ei_position=position, ei_qualified} (dcl_modules, visited_modules, expl_imp_info, cs)
		# (not_exported_symbols,decl_accu, unsolved_belongings, visited_modules, expl_imp_info)
				= search_qualified_expl_imp_symbols imported_symbols eimi imported_mod visited_modules expl_imp_info
		  (expl_imp_info,dcl_modules,cs_error)
		  		= report_not_exported_symbol_errors not_exported_symbols position expl_imp_info imported_mod dcl_modules cs.cs_error
		  (decl_accu, dcl_modules, visited_modules, expl_imp_info, cs)
				= solve_belongings unsolved_belongings position eimi (decl_accu,dcl_modules,visited_modules,expl_imp_info,{cs & cs_error=cs_error})
		  (module_ident,dcl_modules) = case ei_qualified of
		  									QualifiedAs module_ident
		  										-> (module_ident,dcl_modules)
		  									_
												-> dcl_modules![imported_mod].dcl_name
		= ((decl_accu, module_ident), (dcl_modules, visited_modules, expl_imp_info, cs))

	search_expl_imp_symbols :: [ImportNrAndIdents] ExplicitImportsModuleInfo Int *{#Int} *{!*ExplImpInfo}
							   -> ([ImportNrAndIdents],[Declaration],[Belonging],*{#Int},*{!*ExplImpInfo})
	search_expl_imp_symbols imported_symbols eimi imported_mod visited_modules expl_imp_info
		= foldSt (search_expl_imp_symbol eimi imported_mod) imported_symbols ([],[],[],visited_modules,expl_imp_info)

	search_qualified_expl_imp_symbols :: [ImportNrAndIdents] ExplicitImportsModuleInfo Int *{#Int} *{!*ExplImpInfo}
										 -> ([ImportNrAndIdents],[Declaration],[Belonging],*{#Int},*{!*ExplImpInfo})
	search_qualified_expl_imp_symbols imported_symbols eimi imported_mod visited_modules expl_imp_info
		= foldSt (search_qualified_expl_imp_symbol eimi imported_mod) imported_symbols ([],[],[],visited_modules,expl_imp_info)

	search_qualified_hidden_symbols :: [ImportNrAndIdents] ExplicitImportsModuleInfo Int Int [Int]		   v:{#DclModule} *{#Int} *{!*ExplImpInfo}
									   -> ([ImportNrAndIdents],[QualifiedAndHiddenDeclaration],[Belonging],v:{#DclModule},*{#Int},*{!*ExplImpInfo})
	search_qualified_hidden_symbols imported_symbols eimi imported_mod importing_mod other_modules_in_component dcl_modules visited_modules expl_imp_info
		= foldSt (search_qualified_hidden_symbol eimi imported_mod importing_mod other_modules_in_component)
					imported_symbols ([],[],[],dcl_modules,visited_modules,expl_imp_info)

	solve_qualified_hidden_belongings :: [Belonging] Position Int [Int] ExplicitImportsModuleInfo
										 !*([QualifiedAndHiddenDeclaration],v:{#DclModule},*{#Int},*{!*ExplImpInfo},*CheckState)
										-> ([QualifiedAndHiddenDeclaration],v:{#DclModule},*{#Int},*{!*ExplImpInfo},*CheckState)
	solve_qualified_hidden_belongings unsolved_belongings position importing_mod other_modules_in_component eimi state
  		= foldSt (solve_qualified_hidden_belonging position importing_mod other_modules_in_component eimi) unsolved_belongings state 

	solve_belongings :: [Belonging] Position ExplicitImportsModuleInfo *([Declaration],v:{#DclModule},*{#Int},*{!*ExplImpInfo},*CheckState)
																	 -> ([Declaration],v:{#DclModule},*{#Int},*{!*ExplImpInfo},*CheckState)
	solve_belongings unsolved_belongings position eimi state
  		= foldSt (solve_belonging position eimi) unsolved_belongings state 

	solve_belonging :: Position ExplicitImportsModuleInfo Belonging *([Declaration],v:{#DclModule},*{#Int},*{!*ExplImpInfo},*CheckState)
																  -> ([Declaration],v:{#DclModule},*{#Int},*{!*ExplImpInfo},*CheckState)
	solve_belonging position eimi unsolved_belonging=:{belonging_import_n_and_idents={ini_symbol_nr}} (decls_accu, dcl_modules, visited_modules, expl_imp_info, cs=:{cs_error, cs_symbol_table})
		# (ExplImpInfo eii_ident eii_declaring_modules, expl_imp_info) = expl_imp_info![ini_symbol_nr]
		# (need_all,belongs_set,belonging_symbols,dcl_modules,cs_error,cs_symbol_table)
			= get_numbered_belongings eii_ident unsolved_belonging position dcl_modules cs_error cs_symbol_table
		# (decls_accu, dcl_modules, eii_declaring_modules, visited_modules, cs_error)
			= search_belongings need_all belongs_set belonging_symbols eii_ident eii_declaring_modules position eimi unsolved_belonging decls_accu
								dcl_modules visited_modules cs_error
		# expl_imp_info = { expl_imp_info & [ini_symbol_nr] = ExplImpInfo eii_ident eii_declaring_modules }
		= (decls_accu, dcl_modules, visited_modules, expl_imp_info, {cs & cs_error=cs_error, cs_symbol_table=cs_symbol_table})
	where
		search_belongings need_all belongs_set belonging_symbols eii_ident eii_declaring_modules position eimi
				{belonging_declaration,belonging_import_n_and_idents={ini_symbol_nr},belonging_imported_mod}
				decls_accu dcl_modules visited_modules cs_error
			= foldSt
				(search_belonging need_all position eii_ident belonging_declaration belonging_symbols belonging_imported_mod ini_symbol_nr eimi)
				belongs_set (decls_accu, dcl_modules, eii_declaring_modules, visited_modules, cs_error)

	solve_qualified_hidden_belonging :: Position Int [Int] ExplicitImportsModuleInfo Belonging
								  *([QualifiedAndHiddenDeclaration],v:{#DclModule},*{#Int},*{!*ExplImpInfo},*CheckState)
						 		-> ([QualifiedAndHiddenDeclaration],v:{#DclModule},*{#Int},*{!*ExplImpInfo},*CheckState)
	solve_qualified_hidden_belonging position importing_mod other_modules_in_component eimi unsolved_belonging=:{belonging_import_n_and_idents={ini_symbol_nr}}
			(decls_accu, dcl_modules, visited_modules, expl_imp_info, cs=:{cs_error, cs_symbol_table})
		# (ExplImpInfo eii_ident eii_declaring_modules, expl_imp_info) = expl_imp_info![ini_symbol_nr]
		# (need_all,belongs_set,belonging_symbols,dcl_modules,cs_error,cs_symbol_table)
			= get_numbered_belongings eii_ident unsolved_belonging position dcl_modules cs_error cs_symbol_table
		# (decls_accu, eii_declaring_modules, dcl_modules, visited_modules, cs_error)
			= search_hidden_belongings need_all belongs_set belonging_symbols eii_ident position importing_mod other_modules_in_component eimi unsolved_belonging
										decls_accu eii_declaring_modules dcl_modules visited_modules cs_error
		# expl_imp_info = { expl_imp_info & [ini_symbol_nr] = ExplImpInfo eii_ident eii_declaring_modules }
		= (decls_accu, dcl_modules, visited_modules, expl_imp_info, {cs & cs_error=cs_error, cs_symbol_table=cs_symbol_table})
	where
		search_hidden_belongings :: Bool [(Int,Ident)] BelongingSymbols Ident Position Int [Int] ExplicitImportsModuleInfo Belonging
										[QualifiedAndHiddenDeclaration] *DeclaringModulesSet v:{#DclModule} *{#Int} *ErrorAdmin
									-> ([QualifiedAndHiddenDeclaration],*DeclaringModulesSet,v:{#DclModule},*{#Int},*ErrorAdmin)
		search_hidden_belongings need_all belongs_set belonging_symbols eii_ident position importing_mod other_modules_in_component eimi
				{belonging_declaration,belonging_import_n_and_idents={ini_symbol_nr},belonging_imported_mod}
				decls_accu eii_declaring_modules dcl_modules visited_modules cs_error
			= foldSt
				(search_qualified_hidden_belonging need_all position eii_ident belonging_declaration belonging_symbols belonging_imported_mod ini_symbol_nr importing_mod other_modules_in_component eimi)
				belongs_set (decls_accu, eii_declaring_modules, dcl_modules, visited_modules, cs_error)

	get_numbered_belongings :: Ident Belonging Position v:{#DclModule}  *ErrorAdmin  *SymbolTable
			-> (!Bool,![(Int,Ident)],!BelongingSymbols,!v:{#DclModule},!*ErrorAdmin,!*SymbolTable)
	get_numbered_belongings eii_ident {belonging_declaration,belonging_import_n_and_idents={ini_imp_decl}} position dcl_modules cs_error cs_symbol_table
		# (IB_Idents belongs) = getBelongingSymbolsFromImportDeclaration ini_imp_decl
		  (all_belongs,belonging_symbols,dcl_modules) = get_all_belongs belonging_declaration dcl_modules
  		= case belongs of
  			[]
  				// an import like ::A(..) or ::A{..} or class c{..}
				# belongs_set = [(belong_nr, belong_ident) \\ belong_nr<-[0..] & belong_ident<-all_belongs]
				-> (False, belongs_set,	belonging_symbols, dcl_modules, cs_error, cs_symbol_table)
  			_
  				// an import like ::A(C1, C2) or ::A{f1} or class c{m1} 
				# (nr_of_belongs, cs_symbol_table) = foldSt numerate_belongs all_belongs (0, cs_symbol_table)
				  (belongs_set, cs_error, cs_symbol_table)
					= get_opt_nr_and_idents belongs position eii_ident [] cs_error cs_symbol_table
	  			  cs_symbol_table = restoreIdentsSymbolPtrs all_belongs cs_symbol_table
				-> (True, belongs_set, belonging_symbols, dcl_modules, cs_error, cs_symbol_table)

	search_qualified_hidden_belonging :: Bool Position Ident Declaration BelongingSymbols Int Int Int [Int] ExplicitImportsModuleInfo (Int,Ident)
											([QualifiedAndHiddenDeclaration],*DeclaringModulesSet,v:{#DclModule},*{#Int},*ErrorAdmin)
										->	([QualifiedAndHiddenDeclaration],*DeclaringModulesSet,v:{#DclModule},*{#Int},*ErrorAdmin)
	search_qualified_hidden_belonging need_all position eii_ident belonging_declaration belonging_symbols belonging_imported_mod ini_symbol_nr importing_mod other_modules_in_component eimi
										(belong_nr,belong_ident) (decls_accu, eii_declaring_modules, dcl_modules, visited_modules, cs_error)
		# eimi & eimi_module_path=[]
		  (found, path, eii_declaring_modules, visited_modules)
			= search_belonging_symbol eii_declaring_modules ini_symbol_nr belong_nr belong_ident belonging_declaration belonging_imported_mod
										eimi (bitvectResetAll visited_modules)
		| found
			# eii_declaring_modules = foldSt (store_qualified_hidden_belonging belong_nr belonging_declaration) path eii_declaring_modules
			  eimi & eimi_module_path=[]
			// check if belonging of hidden symbol is imported by another import
			  (declaration_found, path, eii_declaring_modules, visited_modules)
				= search_belonging_symbol_in_importing_mod eii_declaring_modules ini_symbol_nr belong_nr belong_ident belonging_declaration
															importing_mod eimi (bitvectResetAll visited_modules)
			| declaration_found
				# eii_declaring_modules = foldSt (store_qualified_hidden_belonging belong_nr belonging_declaration) path eii_declaring_modules
				// forget belonging of hidden symbol because it is imported by another import
				  (decls_accu,dcl_modules) = add_nth_belonging_hidden_decls belong_nr QualifiedNotHiddenDeclaration
				  									belonging_symbols belonging_declaration position decls_accu dcl_modules
				= (decls_accu, eii_declaring_modules, dcl_modules, visited_modules, cs_error)

				# (modules_in_component_with_declaration,eii_declaring_modules,visited_modules)
					= search_belonging_in_component other_modules_in_component ini_symbol_nr belong_nr belong_ident eimi eii_declaring_modules visited_modules
				= case modules_in_component_with_declaration of
					[]
						# (decls_accu,dcl_modules) = add_nth_belonging_hidden_decls belong_nr QualifiedHiddenDeclaration
															belonging_symbols belonging_declaration position decls_accu dcl_modules
						-> (decls_accu, eii_declaring_modules, dcl_modules, visited_modules, cs_error)
					_
						# (decls_accu,dcl_modules) = add_nth_belonging_hidden_decls belong_nr
							(\ belong_decl -> QualifiedSomeNotHiddenDeclaration belong_decl modules_in_component_with_declaration)
															belonging_symbols belonging_declaration position decls_accu dcl_modules
						-> (decls_accu, eii_declaring_modules, dcl_modules, visited_modules, cs_error)
		| need_all
			# (dcl_modules,cs_error) = belonging_not_exported_error belong_ident eii_ident import_ident position belonging_imported_mod dcl_modules cs_error
			= (decls_accu, eii_declaring_modules, dcl_modules, visited_modules, cs_error)
			= (decls_accu, eii_declaring_modules, dcl_modules, visited_modules, cs_error)
	where
		search_belonging_in_component :: [Int] Int Int Ident ExplicitImportsModuleInfo *DeclaringModulesSet *{#Int}
																			 -> ([Int],*DeclaringModulesSet,*{#Int})
		search_belonging_in_component [module_in_component:other_modules_in_component] ini_symbol_nr belong_nr belong_ident eimi eii_declaring_modules visited_modules
			# eimi & eimi_module_path=[]
			# (declaration_found,path,eii_declaring_modules,visited_modules)
				= search_belonging_symbol_in_importing_mod eii_declaring_modules ini_symbol_nr belong_nr belong_ident belonging_declaration
															module_in_component eimi (bitvectResetAll visited_modules)
			| not declaration_found
				= search_belonging_in_component other_modules_in_component ini_symbol_nr belong_nr belong_ident eimi eii_declaring_modules visited_modules
			# eii_declaring_modules = foldSt (store_qualified_hidden_belonging belong_nr belonging_declaration) path eii_declaring_modules
			# (modules_in_component_with_declaration,eii_declaring_modules,visited_modules)
				= search_belonging_in_component other_modules_in_component ini_symbol_nr belong_nr belong_ident eimi eii_declaring_modules visited_modules
			= ([module_in_component:modules_in_component_with_declaration],eii_declaring_modules,visited_modules)
		search_belonging_in_component [] ini_symbol_nr belong_nr belong_ident eimi eii_declaring_modules visited_modules
			= ([],eii_declaring_modules,visited_modules)

	search_belonging :: Bool Position Ident Declaration BelongingSymbols Int Int ExplicitImportsModuleInfo (Int,Ident)
						*([Declaration],v:{#DclModule},*DeclaringModulesSet,*{#Int},*ErrorAdmin)
					  -> ([Declaration],v:{#DclModule},*DeclaringModulesSet,*{#Int},*ErrorAdmin)
	search_belonging need_all position eii_ident belonging_declaration belonging_symbols imported_mod ini_symbol_nr eimi
						(belong_nr, belong_ident) (decls_accu, dcl_modules, eii_declaring_modules, visited_modules, cs_error)
		# (found, path, eii_declaring_modules, visited_modules)
			= search_belonging_symbol eii_declaring_modules ini_symbol_nr belong_nr belong_ident belonging_declaration imported_mod
										eimi (bitvectResetAll visited_modules)
		| found
			# eii_declaring_modules = foldSt (store_belonging belong_nr) path eii_declaring_modules
			  (decls_accu, dcl_modules) = add_nth_belonging_decls position belong_nr belonging_declaration decls_accu dcl_modules
			= (decls_accu, dcl_modules, eii_declaring_modules, visited_modules, cs_error)
		| need_all
			# (dcl_modules,cs_error) = belonging_not_exported_error belong_ident eii_ident import_ident position imported_mod dcl_modules cs_error
			= (decls_accu, dcl_modules, eii_declaring_modules, visited_modules, cs_error)
			= (decls_accu, dcl_modules, eii_declaring_modules, visited_modules, cs_error)

	belonging_not_exported_error :: Ident Ident Ident Position Int v:{#DclModule} *ErrorAdmin -> (v:{#DclModule},*ErrorAdmin)
	belonging_not_exported_error belong_ident eii_ident import_ident position belonging_imported_mod dcl_modules cs_error
		# (module_name,dcl_modules)=dcl_modules![belonging_imported_mod].dcl_name.id_name
		  cs_error = pushErrorAdmin (newPosition import_ident position) cs_error
		  cs_error = checkError belong_ident ("of "+++eii_ident.id_name+++" not exported by module "+++module_name) cs_error
		  cs_error = popErrorAdmin cs_error
		= (dcl_modules,cs_error)

	store_belonging :: Int Int *DeclaringModulesSet -> *DeclaringModulesSet
	store_belonging belong_nr mod_index eii_declaring_modules
		# (Yes di, eii_declaring_modules) = ikhUSearch mod_index eii_declaring_modules
		= case di of
			DeclarationAndBelongings di_decl di_belonging
				# di_belonging = addNr belong_nr di_belonging
				  (new, eii_declaring_modules) = ikhInsert True mod_index (DeclarationAndBelongings di_decl di_belonging) eii_declaring_modules
				| not new
					-> eii_declaring_modules
			NoDeclarationAndBelongings di_decl di_belonging
				# di_belonging = addNr belong_nr di_belonging
				  (new, eii_declaring_modules) = ikhInsert True mod_index (NoDeclarationAndBelongings di_decl di_belonging) eii_declaring_modules
				| not new
					-> eii_declaring_modules

	store_qualified_hidden_belonging :: Int Declaration Int *DeclaringModulesSet -> *DeclaringModulesSet
	store_qualified_hidden_belonging belong_nr belonging_declaration mod_index eii_declaring_modules
		# (yes_di, eii_declaring_modules) = ikhUSearch mod_index eii_declaring_modules
		= case yes_di of
			Yes (DeclarationAndBelongings di_decl di_belonging)
				# (new, eii_declaring_modules) = ikhInsert True mod_index (DeclarationAndBelongings di_decl (addNr belong_nr di_belonging)) eii_declaring_modules
				| not new
					-> eii_declaring_modules
			Yes (NoDeclarationAndBelongings di_decl di_belonging)
				# (new, eii_declaring_modules) = ikhInsert True mod_index (NoDeclarationAndBelongings di_decl (addNr belong_nr di_belonging)) eii_declaring_modules
				| not new
					-> eii_declaring_modules
			No
				-> ikhInsert` False mod_index (NoDeclarationAndBelongings belonging_declaration (addNr belong_nr EndNumbers)) eii_declaring_modules

	add_nth_belonging_decls :: Position Int !Declaration [Declaration] v:{#DclModule} -> (![Declaration],!v:{#DclModule})
	add_nth_belonging_decls position belong_nr decl=:(Declaration {decl_kind,decl_ident}) decls_accu dcl_modules
		# (STE_Imported _ def_mod_index) = decl_kind
		  (belongin_symbols, dcl_modules) = getBelongingSymbols decl dcl_modules
		= case belongin_symbols of
			BS_Constructors constructors
				# {ds_ident, ds_index} = constructors!!belong_nr
				-> ([Declaration { decl_ident = ds_ident, decl_pos = position, 
						decl_kind = STE_Imported STE_Constructor def_mod_index,
						decl_index = ds_index } : decls_accu], dcl_modules)
			BS_Fields rt_fields
				# {fs_ident, fs_index} = rt_fields.[belong_nr]
				  ({sd_ident}, dcl_modules)
						= dcl_modules![def_mod_index].dcl_common.com_selector_defs.[fs_index]
				-> ([Declaration { decl_ident = fs_ident, decl_pos = position, 
						decl_kind = STE_Imported (STE_Field sd_ident) def_mod_index,
						decl_index = fs_index } : decls_accu], dcl_modules)
			BS_Members class_members
				# {ds_ident, ds_index} = class_members.[belong_nr]
				-> ([Declaration { decl_ident = ds_ident, decl_pos = position,
						decl_kind = STE_Imported STE_Member def_mod_index,
						decl_index = ds_index } : decls_accu], dcl_modules)
			BS_MembersAndMacros class_members macro_members default_member_indexes default_macros
				| belong_nr<size class_members
					# {ds_ident, ds_index} = class_members.[belong_nr]
					# decl = Declaration { decl_ident = ds_ident, decl_pos = position,
										   decl_kind = STE_Imported STE_Member def_mod_index,
										   decl_index = ds_index }
					| belong_nr>=size default_member_indexes
						-> ([decl : decls_accu], dcl_modules)
					# default_macros_index = default_member_indexes.[belong_nr]
					| default_macros_index<0
						-> ([decl : decls_accu], dcl_modules)
						#! {mm_ident,mm_index} = default_macros.[default_macros_index]
						# macro_decl = Declaration { decl_ident = mm_ident, decl_pos = position,
													 decl_kind = STE_Imported (STE_DclMacroOrLocalMacroFunction []) def_mod_index,
													 decl_index = mm_index }
						-> ([decl,macro_decl : decls_accu], dcl_modules)
				| belong_nr<size class_members+size macro_members
					# {mm_ident,mm_index} = macro_members.[belong_nr-size class_members]
					-> ([Declaration { decl_ident = mm_ident, decl_pos = position,
							decl_kind = STE_Imported (STE_DclMacroOrLocalMacroFunction []) def_mod_index,
							decl_index = mm_index } : decls_accu], dcl_modules)
					# {mm_ident,mm_index} = default_macros.[belong_nr-(size class_members+size macro_members)]
					-> ([Declaration { decl_ident = mm_ident, decl_pos = position,
							decl_kind = STE_Imported (STE_DclMacroOrLocalMacroFunction []) def_mod_index,
							decl_index = mm_index } : decls_accu], dcl_modules)

	add_nth_belonging_hidden_decls :: Int (Declaration->QualifiedAndHiddenDeclaration) !BelongingSymbols !Declaration Position [QualifiedAndHiddenDeclaration] v:{#DclModule} -> (![QualifiedAndHiddenDeclaration],!v:{#DclModule})
	add_nth_belonging_hidden_decls belong_nr make_qualified_hidden_declaration (BS_Constructors constructors) (Declaration {decl_kind=STE_Imported _ def_mod_index}) position decls_accu dcl_modules
		# {ds_ident, ds_index} = constructors!!belong_nr
		  decl_kind = STE_Imported STE_Constructor def_mod_index
		#! decl = Declaration {decl_ident=ds_ident, decl_pos=position, decl_kind=decl_kind, decl_index=ds_index}
		= ([make_qualified_hidden_declaration decl:decls_accu], dcl_modules)
	add_nth_belonging_hidden_decls belong_nr make_qualified_hidden_declaration (BS_Fields rt_fields) (Declaration {decl_kind=STE_Imported _ def_mod_index}) position decls_accu dcl_modules
		# {fs_ident, fs_index} = rt_fields.[belong_nr]
		  ({sd_ident}, dcl_modules) = dcl_modules![def_mod_index].dcl_common.com_selector_defs.[fs_index]
		  decl_kind = STE_Imported (STE_Field sd_ident) def_mod_index
		#! decl = Declaration {decl_ident = fs_ident, decl_pos=position, decl_kind=decl_kind, decl_index=fs_index}
		= ([make_qualified_hidden_declaration decl:decls_accu], dcl_modules)
	add_nth_belonging_hidden_decls belong_nr make_qualified_hidden_declaration (BS_Members class_members) (Declaration {decl_kind=STE_Imported _ def_mod_index}) position decls_accu dcl_modules
		# {ds_ident, ds_index} = class_members.[belong_nr]
		  decl_kind = STE_Imported STE_Member def_mod_index
		#! decl = Declaration {decl_ident=ds_ident, decl_pos=position, decl_kind=decl_kind, decl_index=ds_index}
		= ([make_qualified_hidden_declaration decl:decls_accu], dcl_modules)
	add_nth_belonging_hidden_decls belong_nr make_qualified_hidden_declaration (BS_MembersAndMacros class_members macro_members default_member_indexes default_macros) (Declaration {decl_kind=STE_Imported _ def_mod_index}) position decls_accu dcl_modules
		| belong_nr<size class_members
			# {ds_ident, ds_index} = class_members.[belong_nr]
			#! decl = Declaration {decl_ident = ds_ident, decl_pos = position,
								   decl_kind = STE_Imported STE_Member def_mod_index, decl_index = ds_index}
			| belong_nr>=size default_member_indexes
				= ([make_qualified_hidden_declaration decl : decls_accu], dcl_modules)
			# default_macros_index = default_member_indexes.[belong_nr]
			| default_macros_index<0
				= ([make_qualified_hidden_declaration decl : decls_accu], dcl_modules)
				#! {mm_ident,mm_index} = default_macros.[default_macros_index]
				#! macro_decl = Declaration {decl_ident = mm_ident, decl_pos = position,
											 decl_kind = STE_Imported (STE_DclMacroOrLocalMacroFunction []) def_mod_index,
											 decl_index = mm_index}
				= ([make_qualified_hidden_declaration decl,make_qualified_hidden_declaration macro_decl : decls_accu], dcl_modules)
		| belong_nr<size class_members+size macro_members
			# {mm_ident,mm_index} = macro_members.[belong_nr-size class_members]
			#! decl = Declaration {decl_ident = mm_ident, decl_pos = position,
								   decl_kind = STE_Imported (STE_DclMacroOrLocalMacroFunction []) def_mod_index, decl_index = mm_index}
			= ([make_qualified_hidden_declaration decl : decls_accu], dcl_modules)
			# {mm_ident,mm_index} = default_macros.[belong_nr-(size class_members+size macro_members)]
			#! decl = Declaration {decl_ident = mm_ident, decl_pos = position,
								   decl_kind = STE_Imported (STE_DclMacroOrLocalMacroFunction []) def_mod_index, decl_index = mm_index}
			= ([make_qualified_hidden_declaration decl : decls_accu], dcl_modules)

	get_all_belongs :: Declaration v:{#DclModule} -> (![Ident],!BelongingSymbols,!v:{#DclModule})
	get_all_belongs decl=:(Declaration {decl_kind,decl_index}) dcl_modules
		# (belonging_symbols, dcl_modules) = getBelongingSymbols decl dcl_modules
		= case belonging_symbols of
			BS_Constructors constructors
				-> ([ds_ident \\ {ds_ident}<-constructors], belonging_symbols, dcl_modules)
			BS_Fields rt_fields
				-> ([fs_ident \\ {fs_ident}<-:rt_fields], belonging_symbols, dcl_modules)
			BS_Members class_members
				-> ([ds_ident \\ {ds_ident}<-:class_members], belonging_symbols, dcl_modules)
			BS_MembersAndMacros class_members macro_members _ default_macros
				-> ([ds_ident \\ {ds_ident}<-:class_members]
					++[mm_ident\\{mm_ident}<-:macro_members]
					++[mm_ident\\{mm_ident}<-:default_macros], belonging_symbols, dcl_modules)
			BS_Nothing
				-> ([], belonging_symbols, dcl_modules)

	numerate_belongs :: Ident *(Int,*SymbolTable) -> (!Int,!*SymbolTable)
	numerate_belongs {id_info} (i, cs_symbol_table)
		# (ste, cs_symbol_table) = readPtr id_info cs_symbol_table
		  new_ste = { ste & ste_kind = STE_BelongingSymbol i, ste_previous = ste }
		= (i+1, writePtr id_info new_ste cs_symbol_table)
	
	get_opt_nr_and_idents :: ![Ident] Position Ident ![(Int,Ident)] !*ErrorAdmin !*SymbolTable -> (![(Int,Ident)],!*ErrorAdmin,!*SymbolTable)
	get_opt_nr_and_idents [ii_ident=:{id_info}:idents] position eii_ident opt_nr_and_idents cs_error cs_symbol_table
		# ({ste_kind}, cs_symbol_table) = readPtr id_info cs_symbol_table
		= case ste_kind of
			STE_BelongingSymbol i
				# (opt_nr_and_idents,cs_error,cs_symbol_table)
					= get_opt_nr_and_idents idents position eii_ident opt_nr_and_idents cs_error cs_symbol_table
				# opt_nr_and_idents = [(i, ii_ident):opt_nr_and_idents]
				-> (opt_nr_and_idents,cs_error,cs_symbol_table)
			_
				# cs_error = pushErrorAdmin (newPosition import_ident position) cs_error
				  cs_error = checkError ii_ident ("does not belong to "+++eii_ident.id_name) cs_error
				  cs_error = popErrorAdmin cs_error
				-> get_opt_nr_and_idents idents position eii_ident opt_nr_and_idents cs_error cs_symbol_table
	get_opt_nr_and_idents [] position eii_ident opt_nr_and_idents cs_error cs_symbol_table
		= (opt_nr_and_idents,cs_error,cs_symbol_table)

	search_expl_imp_symbol :: ExplicitImportsModuleInfo Int ImportNrAndIdents
							  *([ImportNrAndIdents],[Declaration],[Belonging],*{#Int},*{!*ExplImpInfo})
							-> ([ImportNrAndIdents],[Declaration],[Belonging],*{#Int},*{!*ExplImpInfo})
	search_expl_imp_symbol eimi imported_mod ini=:{ini_symbol_nr}
			(not_exported_symbols,decls_accu, belonging_accu, visited_modules, expl_imp_info)
		# (ExplImpInfo eii_ident eii_declaring_modules, expl_imp_info) = expl_imp_info![ini_symbol_nr]
		  (opt_decl, path, eii_declaring_modules, visited_modules)
			= search_symbol eii_declaring_modules ini_symbol_nr imported_mod eimi (bitvectResetAll visited_modules)
		= case opt_decl of
			Yes di=:(DeclarationAndBelongings di_decl=:(Declaration {decl_kind}) _)
				| is_not_STE_member decl_kind
					# new_eii_declaring_modules = update_declaring_modules di_decl path eii_declaring_modules
					  expl_imp_info = {expl_imp_info & [ini_symbol_nr] = ExplImpInfo eii_ident new_eii_declaring_modules}
					  new_belonging_accu = update_belonging_accu di_decl ini imported_mod belonging_accu
					-> (not_exported_symbols,[di_decl:decls_accu], new_belonging_accu, visited_modules, expl_imp_info)
			_
				# expl_imp_info = {expl_imp_info & [ini_symbol_nr] = ExplImpInfo eii_ident eii_declaring_modules}
				-> ([ini:not_exported_symbols],decls_accu, belonging_accu, visited_modules, expl_imp_info)

	search_qualified_expl_imp_symbol :: ExplicitImportsModuleInfo Int ImportNrAndIdents
							  *([ImportNrAndIdents],[Declaration],[Belonging],*{#Int},*{!*ExplImpInfo})
							-> ([ImportNrAndIdents],[Declaration],[Belonging],*{#Int},*{!*ExplImpInfo})
	search_qualified_expl_imp_symbol eimi imported_mod ini=:{ini_symbol_nr}
			(not_exported_symbols,decls_accu, belonging_accu, visited_modules, expl_imp_info)
		# (ExplImpInfo eii_ident eii_declaring_modules, expl_imp_info) = expl_imp_info![ini_symbol_nr]
		  (opt_decl, path, eii_declaring_modules, visited_modules)
			= search_symbol eii_declaring_modules ini_symbol_nr imported_mod eimi (bitvectResetAll visited_modules)
		= case opt_decl of
			Yes (DeclarationAndBelongings di_decl _)
				# new_eii_declaring_modules = update_declaring_modules di_decl path eii_declaring_modules
				  expl_imp_info = {expl_imp_info & [ini_symbol_nr] = ExplImpInfo eii_ident new_eii_declaring_modules}
				  new_belonging_accu = update_belonging_accu di_decl ini imported_mod belonging_accu
				-> (not_exported_symbols,[di_decl:decls_accu], new_belonging_accu, visited_modules, expl_imp_info)
			_
				# expl_imp_info = {expl_imp_info & [ini_symbol_nr] = ExplImpInfo eii_ident eii_declaring_modules}
				-> ([ini:not_exported_symbols],decls_accu, belonging_accu, visited_modules, expl_imp_info)

	search_qualified_hidden_symbol :: ExplicitImportsModuleInfo Int Int [Int] ImportNrAndIdents
							  *([ImportNrAndIdents],[QualifiedAndHiddenDeclaration],[Belonging],v:{#DclModule},*{#Int},*{!*ExplImpInfo})
							-> ([ImportNrAndIdents],[QualifiedAndHiddenDeclaration],[Belonging],v:{#DclModule},*{#Int},*{!*ExplImpInfo})
	search_qualified_hidden_symbol eimi imported_mod importing_mod other_modules_in_component ini=:{ini_symbol_nr,ini_imp_decl}
			(not_exported_symbols,decls_accu, belonging_accu,dcl_modules,visited_modules,expl_imp_info)
		# (ExplImpInfo eii_ident eii_declaring_modules, expl_imp_info) = expl_imp_info![ini_symbol_nr]
		  (opt_decl, path, eii_declaring_modules, visited_modules)
			= search_symbol eii_declaring_modules ini_symbol_nr imported_mod eimi (bitvectResetAll visited_modules)
		= case opt_decl of
			Yes (DeclarationAndBelongings di_decl=:(Declaration {decl_kind,decl_index}) _ )
				# eii_declaring_modules = update_declaring_modules di_decl path eii_declaring_modules
				// check if hidden symbol is imported by another import
				  eimi & eimi_module_path=[]
				  (declaration_found, path, eii_declaring_modules, visited_modules)
					= search_declaration_in_importing_mod eii_declaring_modules di_decl ini_symbol_nr importing_mod eimi (bitvectResetAll visited_modules)
				| declaration_found
					# eii_declaring_modules = update_declaring_modules di_decl path eii_declaring_modules
					  new_belonging_accu = update_belonging_accu di_decl ini imported_mod belonging_accu
					// forget hidden symbol because it is imported by another import, belongings may still be hidden and qualified
					  expl_imp_info = {expl_imp_info & [ini_symbol_nr] = ExplImpInfo eii_ident eii_declaring_modules}
					  decls_accu = [QualifiedNotHiddenDeclaration di_decl:decls_accu]
					-> (not_exported_symbols,decls_accu,new_belonging_accu,dcl_modules,visited_modules,expl_imp_info)
					# (modules_in_component_with_declaration,eii_declaring_modules,visited_modules)
						= search_declaration_in_component eii_declaring_modules di_decl ini_symbol_nr other_modules_in_component eimi visited_modules
					  new_belonging_accu = update_belonging_accu di_decl ini imported_mod belonging_accu
					  expl_imp_info = {expl_imp_info & [ini_symbol_nr] = ExplImpInfo eii_ident eii_declaring_modules}
					-> case di_decl of
						Declaration {decl_kind=STE_Imported STE_Type def_mod_index, decl_index}
							| case ini_imp_decl of ID_Record _ _ -> True; ID_Type _ _ -> True; _ -> False // for ::Record(..)
								/* also hide the constructor declaration of the record */
								# (td_rhs,dcl_modules) = dcl_modules![def_mod_index].dcl_common.com_type_defs.[decl_index].td_rhs
								-> case td_rhs of
									RecordType {rt_constructor={ds_ident,ds_index}}
										# decl_kind = STE_Imported STE_Constructor def_mod_index
										  record_cons_decl = Declaration {decl_ident=ds_ident,decl_pos=NoPos,decl_kind=decl_kind,decl_index=ds_index}
										-> case modules_in_component_with_declaration of
											[]	# decls_accu = [QualifiedHiddenDeclaration di_decl,
																QualifiedHiddenDeclaration record_cons_decl:decls_accu]
												-> (not_exported_symbols,decls_accu,new_belonging_accu,dcl_modules,visited_modules,expl_imp_info)
											_	# decls_accu = [QualifiedSomeNotHiddenDeclaration di_decl modules_in_component_with_declaration,
																QualifiedSomeNotHiddenDeclaration record_cons_decl modules_in_component_with_declaration
																:decls_accu]
												-> (not_exported_symbols,decls_accu,new_belonging_accu,dcl_modules,visited_modules,expl_imp_info)
									-> case modules_in_component_with_declaration of
										[]	# decls_accu = [QualifiedHiddenDeclaration di_decl:decls_accu]
											-> (not_exported_symbols,decls_accu,new_belonging_accu,dcl_modules,visited_modules,expl_imp_info)
										_	# decls_accu = [QualifiedSomeNotHiddenDeclaration di_decl modules_in_component_with_declaration:decls_accu]
											-> (not_exported_symbols,decls_accu,new_belonging_accu,dcl_modules,visited_modules,expl_imp_info)
						_
							-> case modules_in_component_with_declaration of
								[]	# decls_accu = [QualifiedHiddenDeclaration di_decl:decls_accu]
									-> (not_exported_symbols,decls_accu,new_belonging_accu,dcl_modules,visited_modules,expl_imp_info)
								_	# decls_accu = [QualifiedSomeNotHiddenDeclaration di_decl modules_in_component_with_declaration:decls_accu]
									-> (not_exported_symbols,decls_accu,new_belonging_accu,dcl_modules,visited_modules,expl_imp_info)
			_
				# expl_imp_info = {expl_imp_info & [ini_symbol_nr] = ExplImpInfo eii_ident eii_declaring_modules}
				-> ([ini:not_exported_symbols],decls_accu,belonging_accu,dcl_modules,visited_modules,expl_imp_info)
	where
		search_declaration_in_component :: *DeclaringModulesSet Declaration Int [Int] ExplicitImportsModuleInfo *{#Int}
											-> (![Int],!DeclaringModulesSet,!*{#Int})
		search_declaration_in_component eii_declaring_modules di_decl ini_symbol_nr [module_in_component:other_modules_in_component] eimi visited_modules				
			# eimi & eimi_module_path=[]
			# (declaration_found,path,eii_declaring_modules,visited_modules)
				= search_declaration_in_importing_mod eii_declaring_modules di_decl ini_symbol_nr module_in_component eimi (bitvectResetAll visited_modules)
			| not declaration_found
				= search_declaration_in_component eii_declaring_modules di_decl ini_symbol_nr other_modules_in_component eimi visited_modules
			# eii_declaring_modules = update_declaring_modules di_decl path eii_declaring_modules
			# (modules_in_component_with_declaration,eii_declaring_modules,visited_modules)
				= search_declaration_in_component eii_declaring_modules di_decl ini_symbol_nr other_modules_in_component eimi visited_modules
			= ([module_in_component:modules_in_component_with_declaration],eii_declaring_modules,visited_modules)
		search_declaration_in_component eii_declaring_modules di_decl ini_symbol_nr [] eimi visited_modules
			= ([],eii_declaring_modules,visited_modules)

	is_not_STE_member :: STE_Kind -> Bool
	is_not_STE_member (STE_Imported STE_Member _) = False
	is_not_STE_member STE_Member = False
	is_not_STE_member _ = True

	update_declaring_modules :: Declaration [Int] *DeclaringModulesSet -> *DeclaringModulesSet
	update_declaring_modules di_decl path eii_declaring_modules
		# di = DeclarationAndBelongings di_decl EndNumbers
		= foldSt (update_declaring_module di) path eii_declaring_modules
	where
		update_declaring_module di mod_index eei_dm
			# (new,eei_dm) = ikhInsert False mod_index di eei_dm
			| new
				= eei_dm
			# (Yes decl_b,eei_dm) = ikhUSearch mod_index eei_dm
			= case decl_b of
				NoDeclarationAndBelongings decl belongings
					->  ikhInsert` True mod_index (DeclarationAndBelongings decl belongings) eei_dm
				DeclarationAndBelongings decl belongings
					# (DeclarationAndBelongings di_decl _) = di
					| eq_declaration decl di_decl
						-> eei_dm
						// there are multiple definitions for this symbol in this module
						// ignore it, because the compiler already reports this error
						-> eei_dm

	update_belonging_accu :: Declaration ImportNrAndIdents Int [Belonging] -> [Belonging]
	update_belonging_accu di_decl ini imported_mod belonging_accu
		| importDeclarationImportsBelongingSymbols ini.ini_imp_decl
			= [{belonging_declaration=di_decl, belonging_import_n_and_idents=ini, belonging_imported_mod=imported_mod}:belonging_accu]
			= belonging_accu

	search_symbol :: *DeclaringModulesSet Int Int ExplicitImportsModuleInfo *{#Int} -> *(!Optional DeclarationInfo,![Int],!*DeclaringModulesSet,!*{#Int})
	search_symbol eii_declaring_modules imported_symbol_n imported_mod eimi=:{eimi_modules_explicit_imports,eimi_component_mods,eimi_module_path} visited_modules
		# (opt_declaration_info_of_symbol_in_mod, eii_declaring_modules) = ikhUSearch imported_mod eii_declaring_modules
		= case opt_declaration_info_of_symbol_in_mod of
			yes_di=:(Yes di)
				-> (yes_di, eimi_module_path, eii_declaring_modules, visited_modules)
			_
				| not (bitvectSelect imported_mod eimi_component_mods)
					// the eii_declaring_modules is complete for modules that are outside
					// (=beneath) the actual component=> no need to search further
					-> (No, [], eii_declaring_modules, visited_modules)
				# imports_of_imported_mod = ikhSearch` imported_mod eimi_modules_explicit_imports
				  visited_modules = bitvectSet imported_mod visited_modules
				  eimi & eimi_module_path = [imported_mod:eimi_module_path]
				-> search_symbol_in_imports imports_of_imported_mod eii_declaring_modules imported_symbol_n eimi visited_modules
	where
		search_symbol_in_imports :: [ExplicitImport] *DeclaringModulesSet Int !ExplicitImportsModuleInfo *{#Int} -> *(!Optional DeclarationInfo,![Int],!*DeclaringModulesSet,!*{#Int})
		search_symbol_in_imports [{ei_module_n=imp_imp_mod,ei_symbols}:imports] eii_declaring_modules imported_symbol_n eimi visited_modules
			| bitvectSelect imp_imp_mod visited_modules
				= search_symbol_in_imports imports eii_declaring_modules imported_symbol_n eimi visited_modules
			= case ei_symbols of
				ImportSymbolsOnly imp_imp_symbols
					| not (search_imported_symbol imported_symbol_n imp_imp_symbols)
						-> search_symbol_in_imports imports eii_declaring_modules imported_symbol_n eimi visited_modules
				ImportSymbolsAllSomeQualified imp_imp_qualified_symbols
					| search_imported_symbol imported_symbol_n imp_imp_qualified_symbols
						-> search_symbol_in_imports imports eii_declaring_modules imported_symbol_n eimi visited_modules				
				_
					# (opt_decl, path, eii_declaring_modules, visited_modules)
						= search_symbol eii_declaring_modules imported_symbol_n imp_imp_mod eimi visited_modules
					-> case opt_decl of
						Yes _
							-> (opt_decl, path, eii_declaring_modules, visited_modules)
						No
							-> search_symbol_in_imports imports eii_declaring_modules imported_symbol_n eimi visited_modules
		search_symbol_in_imports [] eii_declaring_modules imported_symbol_n eimi visited_modules
			= (No, [], eii_declaring_modules, visited_modules)

	search_belonging_symbol_in_importing_mod :: !*DeclaringModulesSet Int Int Ident !Declaration !Int !ExplicitImportsModuleInfo !*{#Int} -> *(!Bool,![Int],!*DeclaringModulesSet,!*{#Int})
	search_belonging_symbol_in_importing_mod eii_declaring_modules imported_symbol_n belong_nr belong_ident belonging_declaration imported_mod
			eimi=:{eimi_modules_explicit_imports,eimi_component_mods,eimi_module_path} visited_modules
		# (opt_declaration_info_of_symbol_in_mod, eii_declaring_modules) = ikhUSearch imported_mod eii_declaring_modules
		= case opt_declaration_info_of_symbol_in_mod of
			Yes di=:(DeclarationAndBelongings di_decl di_belonging)
				| eq_declaration di_decl belonging_declaration && inNumberSet belong_nr di_belonging
					-> (True, eimi_module_path, eii_declaring_modules, visited_modules)
			Yes di=:(NoDeclarationAndBelongings di_decl di_belonging)
				| eq_declaration di_decl belonging_declaration && inNumberSet belong_nr di_belonging
					-> (True, eimi_module_path, eii_declaring_modules, visited_modules)
			_
				# imports_of_imported_mod = ikhSearch` imported_mod eimi_modules_explicit_imports
				  visited_modules = bitvectSet imported_mod visited_modules
				  eimi & eimi_module_path = [imported_mod:eimi_module_path]
				-> search_belonging_symbol_in_imports imports_of_imported_mod eii_declaring_modules imported_symbol_n belong_nr belong_ident belonging_declaration
														eimi visited_modules

	search_belonging_symbol :: !*DeclaringModulesSet Int Int Ident !Declaration !Int !ExplicitImportsModuleInfo !*{#Int} -> *(!Bool,![Int],!*DeclaringModulesSet,!*{#Int})
	search_belonging_symbol eii_declaring_modules imported_symbol_n belong_nr belong_ident belonging_declaration imported_mod
			eimi=:{eimi_modules_explicit_imports,eimi_component_mods,eimi_module_path} visited_modules
		# (opt_declaration_info_of_symbol_in_mod, eii_declaring_modules) = ikhUSearch imported_mod eii_declaring_modules
		= case opt_declaration_info_of_symbol_in_mod of
			Yes di=:(DeclarationAndBelongings di_decl di_belonging)
				| eq_declaration di_decl belonging_declaration && inNumberSet belong_nr di_belonging
					-> (True, eimi_module_path, eii_declaring_modules, visited_modules)
			Yes di=:(NoDeclarationAndBelongings di_decl di_belonging)
				| eq_declaration di_decl belonging_declaration && inNumberSet belong_nr di_belonging
					-> (True, eimi_module_path, eii_declaring_modules, visited_modules)
			_
				| not (bitvectSelect imported_mod eimi_component_mods)
					// the eii_declaring_modules is complete for modules that are outside
					// (=beneath) the actual component=> no need to search further
					-> (False, [], eii_declaring_modules, visited_modules)
				# imports_of_imported_mod = ikhSearch` imported_mod eimi_modules_explicit_imports
				  visited_modules = bitvectSet imported_mod visited_modules
				  eimi & eimi_module_path = [imported_mod:eimi_module_path]
				-> search_belonging_symbol_in_imports imports_of_imported_mod eii_declaring_modules imported_symbol_n belong_nr belong_ident belonging_declaration
														eimi visited_modules

	search_belonging_symbol_in_imports :: [ExplicitImport] *DeclaringModulesSet Int Int Ident !Declaration
											!ExplicitImportsModuleInfo *{#Int} -> *(!Bool,![Int],!*DeclaringModulesSet,!*{#Int})
	search_belonging_symbol_in_imports [{ei_module_n=imp_imp_mod,ei_symbols}:imports] eii_declaring_modules imported_symbol_n belong_nr belong_ident belonging_declaration
			eimi visited_modules
		| bitvectSelect imp_imp_mod visited_modules
			= search_belonging_symbol_in_imports imports eii_declaring_modules imported_symbol_n belong_nr belong_ident belonging_declaration
													eimi visited_modules
		= case ei_symbols of
			ImportSymbolsOnly imp_imp_symbols
				# (found, opt_belongs) = search_imported_symbol_and_belongings imported_symbol_n imp_imp_symbols
				| not (found && belong_ident_found belong_ident opt_belongs)
					-> search_belonging_symbol_in_imports imports eii_declaring_modules imported_symbol_n belong_nr belong_ident belonging_declaration
															eimi visited_modules
			ImportSymbolsAllSomeQualified imp_imp_qualified_symbols
				# (found, opt_belongs) = search_imported_symbol_and_belongings imported_symbol_n imp_imp_qualified_symbols
				| found && belong_ident_found belong_ident opt_belongs
					-> search_belonging_symbol_in_imports imports eii_declaring_modules imported_symbol_n belong_nr belong_ident belonging_declaration
															eimi visited_modules
			_
				# (found, path, eii_declaring_modules, visited_modules)
					= search_belonging_symbol eii_declaring_modules imported_symbol_n belong_nr belong_ident belonging_declaration
												imp_imp_mod eimi visited_modules
				| found
					-> (True, path, eii_declaring_modules, visited_modules)
					-> search_belonging_symbol_in_imports imports eii_declaring_modules imported_symbol_n belong_nr belong_ident belonging_declaration
															eimi visited_modules
	search_belonging_symbol_in_imports [] eii_declaring_modules imported_symbol_n belong_nr belong_ident belonging_declaration
			eimi visited_modules
		= (False, [], eii_declaring_modules, visited_modules)

	search_declaration_in_importing_mod :: *DeclaringModulesSet Declaration Int Int ExplicitImportsModuleInfo *LargeBitvect -> *(!Bool,![Int],!*DeclaringModulesSet,!*LargeBitvect)
	search_declaration_in_importing_mod eii_declaring_modules declaration imported_symbol_n imported_mod
			eimi=:{eimi_modules_explicit_imports,eimi_component_mods,eimi_module_path} visited_modules
		# (opt_declaration_info_of_symbol_in_mod, eii_declaring_modules) = ikhUSearch imported_mod eii_declaring_modules
		= case opt_declaration_info_of_symbol_in_mod of
			Yes (DeclarationAndBelongings di_decl _)
				| eq_declaration di_decl declaration
					-> (True, eimi_module_path, eii_declaring_modules, visited_modules)
			_
				# imports_of_imported_mod = ikhSearch` imported_mod eimi_modules_explicit_imports
				  visited_modules = bitvectSet imported_mod visited_modules
				  eimi & eimi_module_path = [imported_mod:eimi_module_path]
				-> search_declaration_in_imports imports_of_imported_mod eii_declaring_modules declaration imported_symbol_n eimi visited_modules

	search_declaration :: *DeclaringModulesSet Declaration Int Int ExplicitImportsModuleInfo *LargeBitvect -> *(!Bool,![Int],!*DeclaringModulesSet,!*LargeBitvect)
	search_declaration eii_declaring_modules declaration imported_symbol_n imported_mod
			eimi=:{eimi_modules_explicit_imports,eimi_component_mods,eimi_module_path} visited_modules
		# (opt_declaration_info_of_symbol_in_mod, eii_declaring_modules) = ikhUSearch imported_mod eii_declaring_modules
		= case opt_declaration_info_of_symbol_in_mod of
			Yes (DeclarationAndBelongings di_decl _)
				| eq_declaration di_decl declaration
					-> (True, eimi_module_path, eii_declaring_modules, visited_modules)
			_
				| not (bitvectSelect imported_mod eimi_component_mods)
					// the eii_declaring_modules is complete for modules that are outside
					// (=beneath) the actual component=> no need to search further
					-> (False, [], eii_declaring_modules, visited_modules)
				# imports_of_imported_mod = ikhSearch` imported_mod eimi_modules_explicit_imports
				  visited_modules = bitvectSet imported_mod visited_modules
				  eimi & eimi_module_path = [imported_mod:eimi_module_path]
				-> search_declaration_in_imports imports_of_imported_mod eii_declaring_modules declaration imported_symbol_n eimi visited_modules

	eq_declaration :: Declaration Declaration -> Bool 
	eq_declaration (Declaration declaration1) (Declaration declaration2)
		= declaration1.decl_index==declaration2.decl_index && eq_STE_Kind declaration1.decl_kind declaration2.decl_kind

	search_declaration_in_imports :: [ExplicitImport] *DeclaringModulesSet Declaration Int ExplicitImportsModuleInfo *{#Int} -> *(!Bool,![Int],!*DeclaringModulesSet,!*{#Int})
	search_declaration_in_imports [{ei_module_n=imp_imp_mod,ei_symbols}:imports] eii_declaring_modules declaration imported_symbol_n eimi visited_modules
		| bitvectSelect imp_imp_mod visited_modules
			= search_declaration_in_imports imports eii_declaring_modules declaration imported_symbol_n eimi visited_modules
		= case ei_symbols of
			ImportSymbolsOnly imp_imp_symbols
				| not (search_imported_symbol imported_symbol_n imp_imp_symbols)
					-> search_declaration_in_imports imports eii_declaring_modules declaration imported_symbol_n eimi visited_modules
			ImportSymbolsAllSomeQualified imp_imp_qualified_symbols
				| search_imported_symbol imported_symbol_n imp_imp_qualified_symbols
					-> search_declaration_in_imports imports eii_declaring_modules declaration imported_symbol_n eimi visited_modules
			_
				# (declaration_found, path, eii_declaring_modules, visited_modules)
					= search_declaration eii_declaring_modules declaration imported_symbol_n imp_imp_mod eimi visited_modules
				| declaration_found
					-> (True, path, eii_declaring_modules, visited_modules)
					-> search_declaration_in_imports imports eii_declaring_modules declaration imported_symbol_n eimi visited_modules	
	search_declaration_in_imports [] eii_declaring_modules declaration imported_symbol_n eimi visited_modules
		= (False, [], eii_declaring_modules, visited_modules)

	search_imported_symbol :: !Int ![ImportNrAndIdents] -> Bool
	search_imported_symbol imported_symbol_n []
		= False
	search_imported_symbol imported_symbol_n [{ini_symbol_nr, ini_imp_decl}:t]
		= imported_symbol_n==ini_symbol_nr || search_imported_symbol imported_symbol_n t

	search_imported_symbol_and_belongings :: !Int ![ImportNrAndIdents] -> (!Bool, !ImportBelongings)
	search_imported_symbol_and_belongings imported_symbol_n []
		= (False, IB_None)
	search_imported_symbol_and_belongings imported_symbol_n [{ini_symbol_nr, ini_imp_decl}:t]
		| imported_symbol_n==ini_symbol_nr
			= (True, getBelongingSymbolsFromImportDeclaration ini_imp_decl)
		= search_imported_symbol_and_belongings imported_symbol_n t

	belong_ident_found :: !Ident !ImportBelongings -> Bool
	belong_ident_found belong_ident IB_None
		// like from m import ::T
		= False
	belong_ident_found belong_ident (IB_Idents [])
		// like from m import ::T(..)
		= True 
	belong_ident_found belong_ident (IB_Idents import_list)
		// like from m import ::T(C1,C2)
		= is_member belong_ident import_list
	belong_ident_found belong_ident (IB_IdentsAndOptIdents import_list macro_member_list)
		// like from m import class T(m1,m2)
		= is_member belong_ident import_list || is_member belong_ident macro_member_list

	is_member :: !Ident ![Ident] -> Bool
	is_member belong_ident []
		= False
	is_member belong_ident [ii_ident:t]
		| belong_ident==ii_ident
			= True
		= is_member belong_ident t

	report_not_exported_symbol_errors :: ![ImportNrAndIdents] Position *{!*ExplImpInfo} Int v:{#DclModule} *ErrorAdmin -> (*{!*ExplImpInfo},v:{#DclModule},*ErrorAdmin)
	report_not_exported_symbol_errors [{ini_symbol_nr,ini_imp_decl}:not_exported_symbols] position expl_imp_info imported_mod dcl_modules cs_error
		# (eii, expl_imp_info) = expl_imp_info![ini_symbol_nr]
		  (eii_ident, eii) = get_eei_ident eii
		  expl_imp_info = {expl_imp_info & [ini_symbol_nr] = eii}
		  (module_name,dcl_modules)=dcl_modules![imported_mod].dcl_name.id_name
		  cs_error = popErrorAdmin (checkError eii_ident
									("not exported as a "+++impDeclToNameSpaceString ini_imp_decl +++" by module "+++module_name)
									(pushErrorAdmin (newPosition import_ident position) cs_error))
		= report_not_exported_symbol_errors not_exported_symbols position expl_imp_info imported_mod dcl_modules cs_error
	report_not_exported_symbol_errors [] position expl_imp_info imported_mod dcl_modules cs_error
		= (expl_imp_info,dcl_modules,cs_error)

	impDeclToNameSpaceString :: !ImportDeclaration -> {#Char}
	impDeclToNameSpaceString (ID_Function _)	= "function/macro"
	impDeclToNameSpaceString (ID_Class _ _)		= "class"
	impDeclToNameSpaceString (ID_Type _ _)		= "type"
	impDeclToNameSpaceString (ID_Record _ _)	= "type"
	impDeclToNameSpaceString (ID_Instance _ _ _)= "instance"

get_eei_ident (eii=:ExplImpInfo eii_ident _) = (eii_ident, eii)

// instance == STE_Kind does not compare STE_Imported
eq_STE_Kind (STE_Imported sk1 mn1) (STE_Imported sk2 mn2)
	= mn1==mn2 && eq_STE_Kind sk1 sk2
eq_STE_Kind (STE_FunctionOrMacro _) STE_DclFunction
	= True
eq_STE_Kind (STE_FunctionOrMacro _) (STE_DclMacroOrLocalMacroFunction _)
	= True
eq_STE_Kind STE_DclFunction (STE_FunctionOrMacro _)
	= True
eq_STE_Kind (STE_DclMacroOrLocalMacroFunction _) (STE_FunctionOrMacro _)
	= True
eq_STE_Kind sk1 sk2
	= equal_constructor sk1 sk2

:: CheckCompletenessState =
	{	ccs_dcl_modules				:: !.{#DclModule}
	,	ccs_macro_defs :: !.{#.{#FunDef}}
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

checkExplicitImportCompleteness :: ![([Declaration],Position)] ![QualifiedDeclaration] ![([QualifiedAndHiddenDeclaration],ModuleN)]
										!*{#DclModule} !*{#*{#FunDef}} !*ExpressionHeap !*CheckState
									-> (!.{#DclModule},!*{#*{#FunDef}},!.ExpressionHeap,!.CheckState)
checkExplicitImportCompleteness dcls_explicit explicit_qualified_imports explicit_qualified_hidden_imports dcl_modules macro_defs expr_heap cs=:{cs_symbol_table, cs_error}
	#! n_dcl_modules = size dcl_modules

	# (modified_symbol_ptrs,cs_symbol_table)
		= store_qualified_explicitly_imported_symbols_in_symbol_table explicit_qualified_imports explicit_qualified_hidden_imports cs_symbol_table

	  box_ccs = { ccs_dcl_modules = dcl_modules, ccs_macro_defs=macro_defs,
	   			ccs_set_of_visited_macros = { {} \\ module_n<-[0..n_dcl_modules-1]},
				ccs_expr_heap = expr_heap, ccs_symbol_table = cs_symbol_table,
				ccs_error = cs_error, ccs_heap_changes_accu = modified_symbol_ptrs }
	  main_dcl_module_n = cs.cs_x.x_main_dcl_module_n

	  ccs = foldSt (\(dcls, position) ccs
	   					-> foldSt (checkCompleteness main_dcl_module_n position) dcls ccs)
	   				dcls_explicit
	   				{ box_ccs = box_ccs }
	  { ccs_dcl_modules, ccs_macro_defs,ccs_expr_heap, ccs_symbol_table, ccs_error, ccs_heap_changes_accu } = ccs.box_ccs
	// repair heap contents
	  ccs_symbol_table = restore_symbol_table_after_checking_completeness ccs_heap_changes_accu ccs_symbol_table

	  cs = { cs & cs_symbol_table = ccs_symbol_table, cs_error = ccs_error }
	= (ccs_dcl_modules, ccs_macro_defs, ccs_expr_heap, cs)
  where
	checkCompleteness :: !Int !Position !Declaration !*CheckCompletenessStateBox -> *CheckCompletenessStateBox
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
		continuation (STE_Generic _) dcl_common dcl_functions cci ccs
			= check_completeness dcl_common.com_generic_defs.[decl_index] cci ccs

instance toString STE_Kind where
	toString (STE_FunctionOrMacro _)	= "function/macro"
	toString (STE_DclMacroOrLocalMacroFunction _) = "macro"
	toString STE_Type 					= "type"
	toString STE_Constructor 			= "constructor"
	toString (STE_Field _) 				= "field"
	toString STE_Class 					= "class"
	toString STE_Member 				= "class member"
	toString (STE_Generic _)			= "generic"
	toString STE_Instance				= "instance"
	toString ste						= "<<unknown symbol kind>>"

check_whether_ident_is_imported :: !Ident !Int !Int !STE_Kind !CheckCompletenessInputBox !*CheckCompletenessStateBox 
								-> *CheckCompletenessStateBox
check_whether_ident_is_imported ident module_n symbol_index wanted_ste_kind cci ccs=:{box_ccs=box_ccs=:{ccs_symbol_table}}
	#! (ste=:{ste_kind,ste_index}, ccs_symbol_table) = readPtr ident.id_info ccs_symbol_table
	   ccs = { ccs & box_ccs = {box_ccs & ccs_symbol_table = ccs_symbol_table } }
	| is_imported ste_kind wanted_ste_kind symbol_index module_n ste_index
		= ccs
		#! (ccs=:{box_ccs=box_ccs=:{ccs_symbol_table, ccs_error, ccs_heap_changes_accu}}) = ccs
		#  {box_cci={cci_import_position}} = cci
		   ccs_error = checkErrorWithIdentPos (newPosition { id_name="import", id_info=nilPtr } cci_import_position)
		   				(" "+++toString wanted_ste_kind+++" "+++toString ident.id_name+++" not imported") ccs_error
		   // pretend that the unimported symbol was imported to prevent doubling error mesages
		   ccs_symbol_table = writePtr ident.id_info { ste & ste_kind = STE_ExplImpSymbolNotImported module_n ste_kind } ccs_symbol_table
		   ccs_heap_changes_accu = case ste_kind of
		   								STE_ExplImpSymbolNotImported _ _
		   									-> ccs_heap_changes_accu
		   								STE_ImportedQualified _ _
		   									-> ccs_heap_changes_accu
		   								_
		   									-> [ident.id_info:ccs_heap_changes_accu]
		= { ccs & box_ccs = { box_ccs & ccs_error = ccs_error, ccs_symbol_table = ccs_symbol_table, ccs_heap_changes_accu = ccs_heap_changes_accu }}
  where
	is_imported :: !STE_Kind !STE_Kind !Int !Int !Int -> Bool
	is_imported (STE_Imported ste_kind ste_module_n) wanted_ste_kind symbol_index module_n ste_index
		= ste_module_n==module_n && ste_index==symbol_index && ste_kind==wanted_ste_kind
	is_imported (STE_ImportedQualified (Declaration {decl_index,decl_kind=STE_Imported decl_kind decl_module_n}) ste_kind) wanted_ste_kind symbol_index module_n ste_index
		| decl_module_n==module_n && decl_index==symbol_index && decl_kind==wanted_ste_kind
			= True
			= is_imported ste_kind wanted_ste_kind symbol_index module_n ste_index
	is_imported (STE_ExplImpSymbolNotImported ste_module_n ste_kind) wanted_ste_kind symbol_index module_n ste_index
		| module_n==ste_module_n
			= True
			= is_imported ste_kind wanted_ste_kind symbol_index module_n ste_index
	is_imported ste_kind wanted_ste_kind symbol_index module_n ste_index
		= cci.box_cci.cci_main_dcl_module_n==module_n && ste_index==symbol_index && ste_kind==wanted_ste_kind

class check_completeness x :: !x !CheckCompletenessInputBox !*CheckCompletenessStateBox -> *CheckCompletenessStateBox

instance check_completeness App where
	check_completeness {app_symb, app_args}	cci ccs
		= check_completeness app_symb cci
		  (check_completeness app_args cci ccs)
	
instance check_completeness AlgebraicPattern where
	check_completeness {ap_symbol={glob_module,glob_object={ds_ident,ds_index}}, ap_expr} cci ccs
		= check_completeness ap_expr cci
		  (check_whether_ident_is_imported ds_ident glob_module ds_index STE_Constructor cci ccs)

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
	check_completeness {ins_class_index={gi_module,gi_index},ins_class_ident={ci_ident=Ident class_ident},ins_type} cci ccs
		= check_completeness ins_type cci
		  (check_whether_ident_is_imported class_ident gi_module gi_index STE_Class cci ccs)

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
	check_completeness (Update expr1 selections expr2) cci ccs
		= ( (check_completeness expr1 cci)
		  o (check_completeness selections cci)
		  o (check_completeness expr2) cci
		  ) ccs
	check_completeness (MatchExpr {glob_module,glob_object={ds_ident,ds_index}} expression) cci ccs
		= check_completeness expression cci
		  (check_whether_ident_is_imported ds_ident glob_module ds_index STE_Constructor cci ccs)
	check_completeness (IsConstructor expr {glob_module,glob_object={ds_ident,ds_index}} _ _ _ _) cci ccs
		= check_completeness expr cci
		  (check_whether_ident_is_imported ds_ident glob_module ds_index STE_Constructor cci ccs)
	check_completeness (FreeVar _) _ ccs
		= ccs
	check_completeness (DynamicExpr dynamicExpr) cci ccs
		= check_completeness dynamicExpr cci ccs
	check_completeness EE _ ccs
		= ccs
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

instance check_completeness GenericDef where
	check_completeness {gen_ident, gen_type, gen_deps} cci ccs
		= (check_completeness gen_type cci o foldSt (flip check_completeness cci) gen_deps) ccs

instance check_completeness GenericDependency where
	check_completeness {gd_ident=Ident ident, gd_index={gi_module, gi_index}} cci ccs
		= check_whether_ident_is_imported ident gi_module gi_index (STE_Generic -1) cci ccs

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
  	check_completeness {me_type,me_default_implementation=Yes {mm_index},me_class} cci ccs
		# (macro,ccs) = ccs!box_ccs.ccs_macro_defs.[me_class.glob_module,mm_index];
		= check_completeness macro cci (check_completeness me_type cci ccs)
  	check_completeness {me_type} cci ccs 
  		= check_completeness me_type cci ccs

instance check_completeness (Optional x) | check_completeness x where
	check_completeness (Yes x) cci ccs
		= check_completeness x cci ccs
	check_completeness No _ ccs
		= ccs

instance check_completeness Selection where
	check_completeness (RecordSelection {glob_object={ds_index},glob_module} _) cci ccs
		#! ({dcl_common}, ccs)	= ccs!box_ccs.ccs_dcl_modules.[glob_module]	// the selector's field has to be looked up
		   ({sd_field}) = dcl_common.com_selector_defs.[ds_index]
		= check_whether_ident_is_imported sd_field glob_module ds_index ste_field cci ccs
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
			SK_Constructor {glob_module,glob_object}
				-> check_whether_ident_is_imported symb_ident glob_module glob_object STE_Constructor cci ccs
			SK_Function global_index
				-> check_completeness_for_function symb_ident global_index cci ccs
  			SK_DclMacro global_index
				-> check_completeness_for_macro symb_ident global_index cci ccs
			SK_LocalDclMacroFunction global_index
				-> check_completeness_for_local_dcl_macro symb_ident global_index cci ccs
			SK_OverloadedFunction {glob_module,glob_object}
				-> check_whether_ident_is_imported symb_ident glob_module glob_object STE_Member cci ccs
			SK_Generic {glob_module,glob_object} _
				-> check_whether_ident_is_imported symb_ident glob_module glob_object (STE_Generic 0) cci ccs
  	  where
		check_completeness_for_function symb_ident {glob_object,glob_module} cci ccs
			= check_whether_ident_is_imported symb_ident glob_module glob_object (STE_FunctionOrMacro []) cci ccs

		check_completeness_for_macro symb_ident global_index cci ccs
			| global_index.glob_module<>cci.box_cci.cci_main_dcl_module_n
				= check_whether_ident_is_imported symb_ident global_index.glob_module global_index.glob_object (STE_DclMacroOrLocalMacroFunction []) cci ccs
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
	check_completeness (TA {type_ident,type_index={glob_module,glob_object}} arguments) cci ccs
		= check_completeness arguments cci
		  (check_whether_ident_is_imported type_ident glob_module glob_object STE_Type cci ccs)
	check_completeness (TAS {type_ident,type_index={glob_module,glob_object}} arguments _) cci ccs
		= check_completeness arguments cci
		  (check_whether_ident_is_imported type_ident glob_module glob_object STE_Type cci ccs)
	check_completeness (l --> r) cci ccs
		= check_completeness l cci
		  (check_completeness r cci ccs)
	check_completeness (_ :@: arguments) cci ccs
		= check_completeness arguments cci ccs
	check_completeness _ _ ccs
		= ccs

instance check_completeness TypeContext where
	check_completeness {tc_class=TCClass {glob_module,glob_object={ds_ident,ds_index}}, tc_types} cci ccs
		= check_completeness tc_types cci
		  (check_whether_ident_is_imported ds_ident glob_module ds_index STE_Class cci ccs)
	check_completeness {tc_class=TCGeneric {gtc_generic={glob_module,glob_object={ds_ident,ds_index}}}, tc_types} cci ccs
		= check_completeness tc_types cci
		  (check_whether_ident_is_imported ds_ident glob_module ds_index (STE_Generic -1) cci ccs)

instance check_completeness (TypeDef TypeRhs) where
	check_completeness td=:{td_rhs}	cci ccs
		= check_completeness td_rhs cci ccs

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

// XXX from m import :: T(..) works also if T is a record type

store_qualified_explicitly_imported_symbols_in_symbol_table :: ![QualifiedDeclaration] ![([QualifiedAndHiddenDeclaration],ModuleN)] !*SymbolTable -> (![SymbolPtr],!*SymbolTable)
store_qualified_explicitly_imported_symbols_in_symbol_table explicit_qualified_imports explicit_qualified_hidden_imports symbol_table
	# (modified_symbol_ptrs,symbol_table) = store_qualified_explicitly_imported_symbols_in_symbol_table explicit_qualified_imports [] symbol_table
	= store_qualified_hidden_explicitly_imported_symbols_in_symbol_table explicit_qualified_hidden_imports modified_symbol_ptrs symbol_table
where
	store_qualified_explicitly_imported_symbols_in_symbol_table :: ![QualifiedDeclaration] ![SymbolPtr] !*SymbolTable -> (![SymbolPtr],!*SymbolTable)
	store_qualified_explicitly_imported_symbols_in_symbol_table [(declarations,module_n):explicit_qualified_imports] modified_symbol_ptrs symbol_table
		# (modified_symbol_ptrs,symbol_table) = foldSt store_qualified_explicitly_imported_symbol declarations (modified_symbol_ptrs,symbol_table)
		= store_qualified_explicitly_imported_symbols_in_symbol_table explicit_qualified_imports modified_symbol_ptrs symbol_table
	store_qualified_explicitly_imported_symbols_in_symbol_table [] modified_symbol_ptrs symbol_table
		= (modified_symbol_ptrs,symbol_table)

	store_qualified_hidden_explicitly_imported_symbols_in_symbol_table :: ![([QualifiedAndHiddenDeclaration],ModuleN)] ![SymbolPtr] !*SymbolTable -> (![SymbolPtr],!*SymbolTable)
	store_qualified_hidden_explicitly_imported_symbols_in_symbol_table [(declarations,module_n):explicit_qualified_hidden_imports] modified_symbol_ptrs symbol_table
		# (modified_symbol_ptrs,symbol_table) = foldSt store_qualified_hidden_explicitly_imported_symbol declarations (modified_symbol_ptrs,symbol_table)
		= store_qualified_hidden_explicitly_imported_symbols_in_symbol_table explicit_qualified_hidden_imports modified_symbol_ptrs symbol_table
	store_qualified_hidden_explicitly_imported_symbols_in_symbol_table [] modified_symbol_ptrs symbol_table
		= (modified_symbol_ptrs,symbol_table)

	store_qualified_hidden_explicitly_imported_symbol :: QualifiedAndHiddenDeclaration *([SymbolPtr],*SymbolTable) -> (![SymbolPtr],!*SymbolTable)
	store_qualified_hidden_explicitly_imported_symbol (QualifiedHiddenDeclaration declaration) modified_symbol_ptrs_and_symbol_table
		= store_qualified_explicitly_imported_symbol declaration modified_symbol_ptrs_and_symbol_table
	store_qualified_hidden_explicitly_imported_symbol (QualifiedNotHiddenDeclaration declaration) modified_symbol_ptrs_and_symbol_table
		= store_qualified_explicitly_imported_symbol declaration modified_symbol_ptrs_and_symbol_table
	store_qualified_hidden_explicitly_imported_symbol (QualifiedSomeNotHiddenDeclaration declaration _) modified_symbol_ptrs_and_symbol_table
		= store_qualified_explicitly_imported_symbol declaration modified_symbol_ptrs_and_symbol_table

	store_qualified_explicitly_imported_symbol :: Declaration *([SymbolPtr],*SymbolTable) -> (![SymbolPtr],!*SymbolTable)
	store_qualified_explicitly_imported_symbol declaration=:(Declaration {decl_ident={id_info},decl_kind=STE_Imported _ module_n}) (modified_symbol_ptrs,symbol_table)
		# (symbol_ste=:{ste_kind},symbol_table) = readPtr id_info symbol_table
		# ste_kind = STE_ImportedQualified declaration ste_kind
		# symbol_table = writePtr id_info {symbol_ste & ste_kind=ste_kind} symbol_table
		= ([id_info:modified_symbol_ptrs],symbol_table)					

restore_symbol_table_after_checking_completeness :: ![SymbolPtr] !*SymbolTable -> *SymbolTable
restore_symbol_table_after_checking_completeness modified_symbol_ptrs symbol_table
	= foldSt restore_symbol modified_symbol_ptrs symbol_table
	where
		restore_symbol symbol_ptr symbol_table
			# (symbol_ste=:{ste_kind},symbol_table) = readPtr symbol_ptr symbol_table
			# ste_kind = restore_ste_kind ste_kind
				with
					restore_ste_kind (STE_ImportedQualified declaration ste_kind)
						= restore_ste_kind ste_kind
					restore_ste_kind (STE_ExplImpSymbolNotImported _ ste_kind)
						= restore_ste_kind ste_kind
					restore_ste_kind ste_kind
						= ste_kind
			= writePtr symbol_ptr {symbol_ste & ste_kind=ste_kind} symbol_table

store_qualified_explicit_imports_in_symbol_table :: ![QualifiedDeclaration] ![([QualifiedAndHiddenDeclaration],ModuleN)]
														![(SymbolPtr,STE_Kind)] !*SymbolTable !*{#DclModule}
													-> (![(SymbolPtr,STE_Kind)],!*SymbolTable,!*{#DclModule})
store_qualified_explicit_imports_in_symbol_table qualified_explicit_imports explicit_qualified_hidden_imports modified_ste_kinds symbol_table modules
	# (modified_ste_kinds,symbol_table) = store_explicit_qualified_imports_in_symbol_table qualified_explicit_imports modified_ste_kinds symbol_table
	= store_explicit_qualified_hidden_imports_in_symbol_table explicit_qualified_hidden_imports modified_ste_kinds symbol_table modules
where
	store_explicit_qualified_imports_in_symbol_table :: ![QualifiedDeclaration] ![(SymbolPtr,STE_Kind)] !*SymbolTable
																			-> (![(SymbolPtr,STE_Kind)],!*SymbolTable)
	store_explicit_qualified_imports_in_symbol_table [(declarations,module_symbol):qualified_explicit_imports] modified_ste_kinds symbol_table
		# module_symbol_ptr = module_symbol.id_info
		  (module_ste=:{ste_kind},symbol_table) = readPtr module_symbol_ptr symbol_table
		  (sorted_qualified_imports,modified_ste_kinds) = get_sorted_qualified_imports_of_module_ste_kind ste_kind module_symbol_ptr modified_ste_kinds
		  sorted_qualified_imports = foldSt add_qualified_import declarations sorted_qualified_imports
		  module_ste = {module_ste & ste_kind=STE_ModuleQualifiedImports sorted_qualified_imports}
		  symbol_table = writePtr module_symbol_ptr module_ste symbol_table
		= store_explicit_qualified_imports_in_symbol_table qualified_explicit_imports modified_ste_kinds symbol_table
	store_explicit_qualified_imports_in_symbol_table [] modified_ste_kinds symbol_table
		= (modified_ste_kinds,symbol_table)

	store_explicit_qualified_hidden_imports_in_symbol_table :: ![([QualifiedAndHiddenDeclaration],ModuleN)] ![(SymbolPtr,STE_Kind)] !*SymbolTable !*{#DclModule}
																										-> (![(SymbolPtr,STE_Kind)],!*SymbolTable,!*{#DclModule})
	store_explicit_qualified_hidden_imports_in_symbol_table [(qualified_hidden_declarations,module_n):explicit_qualified_hidden_imports] modified_ste_kinds symbol_table modules
		# (module_symbol_ptr,modules) = modules![module_n].dcl_name.id_info
		  (module_ste=:{ste_kind},symbol_table) = readPtr module_symbol_ptr symbol_table
		  (sorted_qualified_imports,modified_ste_kinds) = get_sorted_qualified_imports_of_module_ste_kind ste_kind module_symbol_ptr modified_ste_kinds
		  sorted_qualified_imports = foldSt add_qualified_hidden_import qualified_hidden_declarations sorted_qualified_imports
		  module_ste = {module_ste & ste_kind=STE_ModuleQualifiedImports sorted_qualified_imports}
		  symbol_table = writePtr module_symbol_ptr module_ste symbol_table
		= store_explicit_qualified_hidden_imports_in_symbol_table explicit_qualified_hidden_imports modified_ste_kinds symbol_table modules
	store_explicit_qualified_hidden_imports_in_symbol_table [] modified_ste_kinds symbol_table modules
		= (modified_ste_kinds,symbol_table,modules)

	get_sorted_qualified_imports_of_module_ste_kind :: STE_Kind SymbolPtr [(SymbolPtr,STE_Kind)] -> (!SortedQualifiedImports,![(SymbolPtr,STE_Kind)])
	get_sorted_qualified_imports_of_module_ste_kind (STE_ModuleQualifiedImports sorted_qualified_imports) module_symbol_ptr modified_ste_kinds
		= (sorted_qualified_imports,modified_ste_kinds)
	get_sorted_qualified_imports_of_module_ste_kind module_ste_kind=:STE_ClosedModule module_symbol_ptr modified_ste_kinds
		= (EmptySortedQualifiedImports,[(module_symbol_ptr,module_ste_kind):modified_ste_kinds])
	get_sorted_qualified_imports_of_module_ste_kind module_ste_kind=:(STE_Module _) module_symbol_ptr modified_ste_kinds
		= (EmptySortedQualifiedImports,[(module_symbol_ptr,module_ste_kind):modified_ste_kinds])
	get_sorted_qualified_imports_of_module_ste_kind STE_Empty module_symbol_ptr modified_ste_kinds // for import as
		= (EmptySortedQualifiedImports,[(module_symbol_ptr,STE_Empty):modified_ste_kinds])

	add_qualified_hidden_import :: !QualifiedAndHiddenDeclaration !u:SortedQualifiedImports -> u:SortedQualifiedImports
	add_qualified_hidden_import (QualifiedHiddenDeclaration declaration) sorted_qualified_imports
		= add_qualified_import declaration sorted_qualified_imports
	add_qualified_hidden_import (QualifiedNotHiddenDeclaration declaration) sorted_qualified_imports
		= add_qualified_import declaration sorted_qualified_imports
	add_qualified_hidden_import (QualifiedSomeNotHiddenDeclaration declaration _) sorted_qualified_imports
		= add_qualified_import declaration sorted_qualified_imports

add_qualified_import :: !Declaration !u:SortedQualifiedImports -> u:SortedQualifiedImports
add_qualified_import new_declaration EmptySortedQualifiedImports
	= SortedQualifiedImports new_declaration EmptySortedQualifiedImports EmptySortedQualifiedImports
add_qualified_import new_declaration=:(Declaration {decl_ident=new_ident,decl_kind=new_ste_kind}) (SortedQualifiedImports declaration=:(Declaration {decl_ident,decl_kind}) sqi_left sqi_right)
	| new_ident.id_name<decl_ident.id_name
		= SortedQualifiedImports declaration (add_qualified_import new_declaration sqi_left) sqi_right
	| new_ident.id_name==decl_ident.id_name && less_imported_ste_kind new_ste_kind decl_kind
		= SortedQualifiedImports declaration (add_qualified_import new_declaration sqi_left) sqi_right
		= SortedQualifiedImports declaration sqi_left (add_qualified_import new_declaration sqi_right)

less_imported_ste_kind (STE_Imported ste_kind1 _) (STE_Imported ste_kind2 _)
	= ste_kind_to_name_space_n ste_kind1 < ste_kind_to_name_space_n ste_kind2
less_imported_ste_kind _ _
	= False

imported_ste_kind_to_name_space_n (STE_Imported ste_kind1 _)
	= ste_kind_to_name_space_n ste_kind1
imported_ste_kind_to_name_space_n _
	= 3

:: NameSpaceN:==Int

ExpressionNameSpaceN:==0
TypeNameSpaceN:==1
ClassNameSpaceN:==2
FieldNameSpaceN:==3
GenericNameSpaceN:==4
OtherNameSpaceN:==5

ste_kind_to_name_space_n STE_DclFunction = ExpressionNameSpaceN
ste_kind_to_name_space_n STE_Constructor = ExpressionNameSpaceN
ste_kind_to_name_space_n STE_Member = ExpressionNameSpaceN
ste_kind_to_name_space_n (STE_DclMacroOrLocalMacroFunction _) = ExpressionNameSpaceN
ste_kind_to_name_space_n STE_Type = TypeNameSpaceN
ste_kind_to_name_space_n STE_Class = ClassNameSpaceN
ste_kind_to_name_space_n (STE_Field _) = FieldNameSpaceN
ste_kind_to_name_space_n (STE_Generic _) = GenericNameSpaceN
ste_kind_to_name_space_n _ = OtherNameSpaceN

search_qualified_ident :: !Ident {#Char} !NameSpaceN !*CheckState -> (!Bool,!DeclarationRecord,!*CheckState)
search_qualified_ident module_id=:{id_info} ident_name name_space_n cs
	# ({ste_kind}, cs_symbol_table) = readPtr id_info cs.cs_symbol_table
	# cs = {cs & cs_symbol_table=cs_symbol_table}
	= case ste_kind of
		STE_ModuleQualifiedImports sorted_qualified_imports
			# (found,declaration) = search_qualified_import ident_name sorted_qualified_imports name_space_n
			| found
				-> (True,declaration,cs)
				-> not_imported_error cs
		STE_ClosedModule
			-> not_imported_error cs
		STE_Module _
			-> not_imported_error cs
		_
			-> (False,{decl_ident={id_name="",id_info=nilPtr},decl_pos=NoPos,decl_kind=STE_Empty,decl_index=NoIndex},
					{cs & cs_error=checkError module_id "undefined" cs.cs_error})
	where
		not_imported_error cs
			= (False,{decl_ident={id_name="",id_info=nilPtr},decl_pos=NoPos,decl_kind=STE_Empty,decl_index=NoIndex},
					{cs & cs_error=checkError ("'"+++module_id.id_name+++"'."+++ident_name) "not imported" cs.cs_error})

search_qualified_import :: !String !SortedQualifiedImports !NameSpaceN -> (!Bool,!DeclarationRecord)
search_qualified_import name EmptySortedQualifiedImports name_space_n
	= (False,{decl_ident = {id_name="",id_info=nilPtr},decl_pos=NoPos,decl_kind=STE_Empty,decl_index=0})
search_qualified_import name (SortedQualifiedImports (Declaration declaration=:{decl_ident={id_name},decl_kind}) sqi_left sqi_right) name_space_n
	| name==id_name
		# decl_name_space_n = imported_ste_kind_to_name_space_n decl_kind
		| name_space_n == decl_name_space_n
			= (True,declaration)
		| name_space_n < decl_name_space_n
			= search_qualified_import name sqi_left name_space_n
			= search_qualified_import name sqi_right name_space_n
	| name<id_name
		= search_qualified_import name sqi_left name_space_n
		= search_qualified_import name sqi_right name_space_n

search_qualified_imports :: !String !SortedQualifiedImports !NameSpaceN -> [DeclarationRecord]
search_qualified_imports name EmptySortedQualifiedImports name_space_n
	= []
search_qualified_imports name (SortedQualifiedImports (Declaration declaration=:{decl_ident={id_name},decl_kind}) sqi_left sqi_right) name_space_n
	| name==id_name
		# decl_name_space_n = imported_ste_kind_to_name_space_n decl_kind
		| name_space_n == decl_name_space_n
			# declarations_left =search_qualified_imports name sqi_left  name_space_n
			# declarations_right=search_qualified_imports name sqi_right name_space_n
			= declarations_left++[declaration:declarations_right]
		| name_space_n < decl_name_space_n
			= search_qualified_imports name sqi_left  name_space_n
			= search_qualified_imports name sqi_right name_space_n
	| name<id_name
		= search_qualified_imports name sqi_left  name_space_n
		= search_qualified_imports name sqi_right name_space_n

qualified_import_for_type :: !String !SortedQualifiedImports -> Bool
qualified_import_for_type name EmptySortedQualifiedImports
	= False
qualified_import_for_type name (SortedQualifiedImports (Declaration declaration=:{decl_ident={id_name},decl_kind}) sqi_left sqi_right)
	| name==id_name
		# decl_name_space_n = imported_ste_kind_to_name_space_n decl_kind
		| TypeNameSpaceN == decl_name_space_n
			= True
		| TypeNameSpaceN < decl_name_space_n
			= qualified_import_for_type name sqi_left
			= qualified_import_for_type name sqi_right
	| name<id_name
		= qualified_import_for_type name sqi_left
		= qualified_import_for_type name sqi_right

restore_module_ste_kinds_in_symbol_table :: ![(SymbolPtr,STE_Kind)] !*SymbolTable -> *SymbolTable
restore_module_ste_kinds_in_symbol_table [(ptr,ste_kind):ptrs_and_ste_kinds] symbol_table
	# (ste,symbol_table) = readPtr ptr symbol_table
	# symbol_table = writePtr ptr {ste & ste_kind=ste_kind} symbol_table
	= restore_module_ste_kinds_in_symbol_table ptrs_and_ste_kinds symbol_table
restore_module_ste_kinds_in_symbol_table [] symbol_table
	= symbol_table

collect_imported_instances :: !{!Declaration} ![QualifiedDeclaration] ![([QualifiedAndHiddenDeclaration],ModuleN)] -> [!GlobalInstanceIndex!]
collect_imported_instances icl_imports icl_qualified_imports icl_qualified_hidden_explicit_imports
	# instance_indices = collect_imported_instances_in_array 0 icl_imports
	# instance_indices = collect_qualified_imported_instances icl_qualified_imports instance_indices
	= collect_qualified_hidden_explicit_imported_instances icl_qualified_hidden_explicit_imports instance_indices
where
	collect_imported_instances_in_array :: !Int !{!Declaration} -> [!GlobalInstanceIndex!]
	collect_imported_instances_in_array i imports
		| i<size imports
			= case imports.[i] of
				Declaration {decl_kind = STE_Imported STE_Instance mod_index, decl_index}
					-> [! {gii_module_n=mod_index,gii_instance_n=decl_index} : collect_imported_instances_in_array (i+1) imports !]
				_
					-> collect_imported_instances_in_array (i+1) imports
			= [!!]

	collect_qualified_imported_instances :: ![([Declaration],a)] ![!GlobalInstanceIndex!] -> [!GlobalInstanceIndex!]
	collect_qualified_imported_instances [(declarations,_):qualified_imports] instance_indices
		= collect_imported_instances_in_list declarations (collect_qualified_imported_instances qualified_imports instance_indices)
	collect_qualified_imported_instances [] instance_indices
		= instance_indices

	collect_imported_instances_in_list :: ![Declaration] ![!GlobalInstanceIndex!] -> [!GlobalInstanceIndex!]
	collect_imported_instances_in_list [Declaration {decl_kind = STE_Imported STE_Instance mod_index, decl_index}:declarations] instance_indices
		= [! {gii_module_n=mod_index,gii_instance_n=decl_index} : collect_imported_instances_in_list declarations instance_indices!]
	collect_imported_instances_in_list [_:declarations] instance_indices
		= collect_imported_instances_in_list declarations instance_indices
	collect_imported_instances_in_list [] instance_indices
		= instance_indices

	collect_qualified_hidden_explicit_imported_instances :: ![([QualifiedAndHiddenDeclaration],a)] ![!GlobalInstanceIndex!] -> [!GlobalInstanceIndex!]
	collect_qualified_hidden_explicit_imported_instances [(qualified_hidden_explicit_declarations,_):qualified_hidden_explicit_imports] instance_indices
		# instance_indices = collect_qualified_hidden_explicit_imported_instances qualified_hidden_explicit_imports instance_indices
		= collect_qualified_and_hidden_imported_instances qualified_hidden_explicit_declarations instance_indices
	collect_qualified_hidden_explicit_imported_instances [] instance_indices
		= instance_indices

	collect_qualified_and_hidden_imported_instances
			[QualifiedHiddenDeclaration (Declaration {decl_kind=STE_Imported STE_Instance mod_index,decl_index}):declarations] instance_indices
		= [! {gii_module_n=mod_index,gii_instance_n=decl_index} : collect_qualified_and_hidden_imported_instances declarations instance_indices!]
	collect_qualified_and_hidden_imported_instances
			[QualifiedNotHiddenDeclaration (Declaration {decl_kind=STE_Imported STE_Instance mod_index,decl_index}):declarations] instance_indices
		= [! {gii_module_n=mod_index,gii_instance_n=decl_index} : collect_qualified_and_hidden_imported_instances declarations instance_indices!]
	collect_qualified_and_hidden_imported_instances
			[QualifiedSomeNotHiddenDeclaration (Declaration {decl_kind=STE_Imported STE_Instance mod_index,decl_index}) _:declarations] instance_indices
		= [! {gii_module_n=mod_index,gii_instance_n=decl_index} : collect_qualified_and_hidden_imported_instances declarations instance_indices!]
	collect_qualified_and_hidden_imported_instances [_:declarations] instance_indices
		= collect_qualified_and_hidden_imported_instances declarations instance_indices
	collect_qualified_and_hidden_imported_instances [] instance_indices
		= instance_indices
