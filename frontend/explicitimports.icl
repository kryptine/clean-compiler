implementation module explicitimports

import StdEnv

import syntax, typesupport, parse, checksupport, utilities, checktypes, transform, predef, RWSDebug

possiblyFilterExplImportedDecls :: ![ImportDeclaration] u:[w:(.Index,y:Declarations)] Position u0:{#DclModule} !*CheckState
				-> (!v:[x:(Index,z:Declarations)],!u0:{#DclModule},!.CheckState), [y <= z, w <= x, u <= v]
possiblyFilterExplImportedDecls [] decls_of_imported_module _ modules cs // implicit import
	= (decls_of_imported_module, modules, cs)
possiblyFilterExplImportedDecls import_declarations decls_of_imported_module import_statement_pos modules cs=:{cs_error, cs_symbol_table}
	// explicit import
	# cs_error = pushErrorAdmin (newPosition { id_name="", id_info=nilPtr } import_statement_pos) cs_error
	  (wanted_symbols, cs_symbol_table, cs_error)
	  		= foldSt add_wanted_symbol_to_symbol_table import_declarations ([], cs_symbol_table, cs_error)
	  (imported_decls, wanted_symbols, modules, cs=:{cs_error, cs_symbol_table})
	  		= foldSt (filter_decls_per_module import_statement_pos) decls_of_imported_module
	  					([], wanted_symbols, modules, { cs & cs_error = cs_error, cs_symbol_table = cs_symbol_table })
	  cs = { cs & cs_error = cs_error, cs_symbol_table = cs_symbol_table }
	  cs = foldSt (switch_import_syntax restore_symbol_table_old_syntax restore_symbol_table) wanted_symbols cs
	  cs = { cs & cs_error = popErrorAdmin cs.cs_error }
	= (imported_decls, modules, cs)
  where
	add_wanted_symbol_to_symbol_table import_declaration=:(ID_OldSyntax idents) (wanted_symbols_accu, cs_symbol_table, cs_error)
		// this alternative is only for old syntax
		= foldSt (add_symbols import_declaration) idents (wanted_symbols_accu, cs_symbol_table, cs_error)
	  where
		add_symbols import_declaration ident=:{id_info} (wanted_symbols_accu, cs_symbol_table, cs_error)
			# (ste=:{ste_kind}, cs_symbol_table) = readPtr id_info cs_symbol_table
	  		= case ste_kind of
  				STE_ExplImp _ _ _ _
  					-> (wanted_symbols_accu, cs_symbol_table, cs_error)
  				_	# new_ste_kind = STE_ExplImp False (Yes import_declaration) STE_Empty False
					  new_ste = { ste & ste_kind = new_ste_kind, ste_previous = ste }
					  cs_symbol_table = writePtr id_info new_ste cs_symbol_table //--->("writing", ident)
					-> ([ident:wanted_symbols_accu], cs_symbol_table, cs_error)
	add_wanted_symbol_to_symbol_table import_declaration (wanted_symbols_accu, cs_symbol_table, cs_error)
		// "wanted" means: a symbol is listed in an explicit import statement
		# (ident=:{id_info}) = get_ident import_declaration
		  (ste=:{ste_kind}, cs_symbol_table) = readPtr id_info cs_symbol_table
  		= case ste_kind of
  			STE_ExplImp _ _ _ _
  				-> (wanted_symbols_accu, cs_symbol_table,
  					checkError ident "appeared twice in one explicit import statement" cs_error)
  			_	# new_ste_kind = STE_ExplImp False (Yes import_declaration) (imp_decl_to_ste_kind import_declaration) False
				  new_ste = { ste & ste_kind = new_ste_kind, ste_previous = ste }
				  cs_symbol_table = writePtr id_info new_ste cs_symbol_table
				-> ([ident:wanted_symbols_accu], cs_symbol_table, cs_error)
	  where
		imp_decl_to_ste_kind (ID_Function _)				= STE_FunctionOrMacro []
		imp_decl_to_ste_kind (ID_Class _ _)					= STE_Class
		imp_decl_to_ste_kind (ID_Type _ _)					= STE_Type
		imp_decl_to_ste_kind (ID_Record _ _)				= STE_Type
		imp_decl_to_ste_kind (ID_Instance {ii_ident} _ _)	= STE_Instance ii_ident
		
	add_bracket_symbol_to_symbol_table ste_kind all_bracket_ids_are_wanted ident=:{id_info} symbol_table
		# (ste=:{ste_kind}, symbol_table) = readPtr id_info symbol_table
		  new_ste_kind = STE_ExplImp all_bracket_ids_are_wanted No ste_kind (not all_bracket_ids_are_wanted)
		  new_ste = { ste & ste_kind = new_ste_kind, ste_previous = ste }
		  symbol_table = writePtr id_info new_ste symbol_table //--->("writing", ident)
		= symbol_table

	get_ident (ID_Function {ii_ident})						= ii_ident
	get_ident (ID_Class {ii_ident} _)						= ii_ident
	get_ident (ID_Type {ii_ident} _)						= ii_ident
	get_ident (ID_Record {ii_ident} _)						= ii_ident
	get_ident (ID_Instance class_ident instance_ident _)	= instance_ident

	restore_symbol_table id=:{id_info} cs=:{ cs_symbol_table, cs_error }
		# (ste, cs_symbol_table) = readPtr id_info cs_symbol_table
		  cs_symbol_table = writePtr id_info ste.ste_previous cs_symbol_table //--->("restoring", id)
		  cs_error = case ste.ste_kind of
		  				STE_ExplImp success _ ste_kind _
		  					| success
		  						-> cs_error
		  					-> checkError id ("not exported as a "+++toString ste_kind+++
		  															" by the specified module") cs_error
		  				_	-> abort "assertion 1 failed in module explicitimports"
		= { cs & cs_symbol_table = cs_symbol_table, cs_error = cs_error }
	
	restore_symbol_table_old_syntax id=:{id_info} cs=:{ cs_symbol_table }
		# (ste, cs_symbol_table) = readPtr id_info cs_symbol_table
		  cs_symbol_table = writePtr id_info ste.ste_previous cs_symbol_table //--->("restoring", id)
		  cs = { cs & cs_symbol_table = cs_symbol_table }
		= case ste.ste_kind of
			STE_ExplImp success opt_id _ _
				| success
					-> cs
				# cs_symbol_table = opt_make_partners_succesful opt_id cs.cs_symbol_table
				  cs_error = checkError id "not exported by the specified module" cs.cs_error
				-> { cs & cs_error = cs_error, cs_symbol_table = cs_symbol_table }
		  	_	-> abort "assertion 54 failed in module explicitimports"
	  where
		opt_make_partners_succesful No cs_symbol_table
			= cs_symbol_table
		opt_make_partners_succesful (Yes (ID_OldSyntax partners)) cs_symbol_table
			= foldSt make_partner_succesful partners cs_symbol_table

		make_partner_succesful {id_info} cs_symbol_table
			// set the success bit for the partner entries, because an error message has been
			// given already
			# (ste, cs_symbol_table) = readPtr id_info cs_symbol_table
			= case ste.ste_kind of
				STE_ExplImp _ a b c
					-> writePtr id_info { ste & ste_kind = STE_ExplImp True a b c } cs_symbol_table
				_	-> cs_symbol_table
			
	filter_decls_per_module import_statement_pos (mod_index, {dcls_import, dcls_local}) (imported_decls_per_module, wanted_symbols, modules, cs)
		# (dcls_import, (wanted_symbols, modules, cs))
				= iMapFilterYesSt (i_filter_possibly_imported_decl mod_index dcls_import)
						0 (size dcls_import) (wanted_symbols, modules, cs)
		  (dcls_local, (wanted_symbols, modules, cs))
		  		= mapFilterYesSt (filter_possibly_imported_decl mod_index) dcls_local (wanted_symbols, modules, cs)
		  dcls_import_array
		  		= { el \\ el <- dcls_import}
		  size_dia
		  		= size dcls_import_array
		  dcls_local_for_import
		  		= {local_declaration_for_import decl mod_index \\ decl<-dcls_local}
		  dcls_explicit
		  		= { ExplicitImport 
		  				(if (i<size_dia) dcls_import_array.[i] dcls_local_for_import.[i-size_dia])
		  				import_statement_pos 
		  			\\ i <- [0..size_dia+size dcls_local_for_import-1] }
		= ( [ (mod_index, { dcls_import = dcls_import_array, dcls_local = dcls_local,
							dcls_local_for_import = dcls_local_for_import,
							dcls_explicit = dcls_explicit })
			:imported_decls_per_module
			],
			wanted_symbols, modules, cs)

	i_filter_possibly_imported_decl mod_index dcls_import i state
		= filter_possibly_imported_decl mod_index dcls_import.[i] state
		
	filter_possibly_imported_decl _ decl=:{dcl_kind=STE_Imported ste_kind mod_index} state
		= filter_decl mod_index decl ste_kind state
	filter_possibly_imported_decl mod_index decl=:{dcl_kind} state
		= filter_decl mod_index decl dcl_kind state

//	filter_decl :: !Int !Declaration !STE_Kind !(!v:[Ident],!u:{#DclModule},!*CheckState)
//			-> (!Optional Declaration,!(!w:[Ident],!u:{#DclModule},!.CheckState)), [v<=w]
	filter_decl mod_index decl (STE_Instance class_ident) state
		// this alternative is only for old syntax
		| switch_import_syntax True False
			= filter_instance_decl mod_index decl class_ident state
	filter_decl mod_index decl=:{dcl_ident={id_info}} dcl_kind (wanted_symbols_accu, modules, cs=:{cs_symbol_table})
		# (ste=:{ste_kind}, cs_symbol_table) = readPtr id_info cs_symbol_table
		  cs = { cs & cs_symbol_table = cs_symbol_table }
		= case ste_kind of
			STE_ExplImp _ opt_import_declaration ste_kind_2 _
				// the symbol is wanted (see above).
				# cs_symbol_table 
						= writePtr id_info { ste & ste_kind = STE_ExplImp True opt_import_declaration ste_kind_2 False}
									cs.cs_symbol_table //--->("setting True", decl.dcl_ident)
						// mark this symbol as being succesfully imported
				  cs = { cs & cs_symbol_table = cs_symbol_table}
		  		-> case opt_import_declaration of
					No	-> (Yes decl, (wanted_symbols_accu, modules, cs))
					Yes import_declaration
						# cs = switch_import_syntax (mark_partners import_declaration cs) cs
						-> (Yes decl, add_bracketed_symbols_to_symbol_table import_declaration decl dcl_kind mod_index
												 (wanted_symbols_accu, modules, cs))
			_	-> (No, (wanted_symbols_accu, modules, cs))

	// only for old syntax
	filter_instance_decl mod_index decl=:{dcl_index} class_ident
							(wanted_symbols_accu, modules, cs=:{cs_symbol_table})
		# (ste=:{ste_kind}, cs_symbol_table) = readPtr class_ident.id_info cs_symbol_table
		  cs = { cs & cs_symbol_table = cs_symbol_table }
		= case ste_kind of
			STE_ExplImp _ _ _ _
				-> (Yes decl, (wanted_symbols_accu, modules, cs))
			_	-> (No, (wanted_symbols_accu, modules, cs))

	// only for old syntax
	mark_partners (ID_OldSyntax partners) cs=:{cs_symbol_table}
		# cs_symbol_table = foldSt mark_partner partners cs_symbol_table
		= { cs & cs_symbol_table = cs_symbol_table }
	  where
		mark_partner {id_info} cs_symbol_table
			# (ste=:{ste_kind=STE_ExplImp _ a b c}, cs_symbol_table) = readPtr id_info cs_symbol_table
			= writePtr id_info { ste & ste_kind = STE_ExplImp True a b c } cs_symbol_table
		
	add_bracketed_symbols_to_symbol_table import_declaration decl dcl_kind mod_index
										(wanted_symbols_accu, modules, cs)
		# (opt_bracket_info, modules, cs=:{cs_symbol_table})
				= (switch_import_syntax get_opt_bracket_info_old_syntax get_opt_bracket_info)
					import_declaration decl dcl_kind mod_index modules cs
		| isNo opt_bracket_info
			= (wanted_symbols_accu, modules, { cs & cs_symbol_table = cs_symbol_table })
		# (Yes (all_bracket_ids, wanted_bracket_ids, structure_name, ste_kind)) 
				= opt_bracket_info
		  all_bracket_ids_are_wanted
		  		= isEmpty wanted_bracket_ids
		  cs_symbol_table
				= foldSt (add_bracket_symbol_to_symbol_table ste_kind all_bracket_ids_are_wanted) all_bracket_ids
																  cs_symbol_table
		  cs = { cs & cs_symbol_table = cs_symbol_table }
		| all_bracket_ids_are_wanted
			// "import class C (..)" or "import :: T (..)" or "import :: T {..}" 
			= (all_bracket_ids++wanted_symbols_accu, modules, cs)
		// "import class C (m1, m2)" or "import :: T (C1, C2)" or "import :: T {f1, f2}" 
		// currently all bracket symbols have (STE_ExplImp _ _ _ True). Mark those that are really wanted False
		// and overwrite the remaining again with STE_Empty
		# cs = foldSt (check_wanted_idents structure_name) wanted_bracket_ids cs
		  cs_symbol_table = foldSt overwrite_wanted_idents wanted_bracket_ids cs.cs_symbol_table
		  (wanted_symbols_accu, cs_symbol_table)
		  		= foldSt remove_and_collect all_bracket_ids (wanted_symbols_accu, cs_symbol_table)
		= (wanted_symbols_accu, modules, { cs & cs_symbol_table = cs_symbol_table })
	  where
	  	isNo No = True
	  	isNo _  = False

	add_bracketed_symbols_to_symbol_table _ _ _ mod_index states
		= states
	
	get_opt_bracket_info (ID_Class _ (Yes wanted_members)) {dcl_kind, dcl_index} mod_index modules cs=:{cs_symbol_table}
		# (dcl_module, module_entry, modules, cs_symbol_table)
				= get_module_and_entry dcl_kind mod_index modules cs_symbol_table
		  class_def = case module_entry.ste_kind of
						STE_OpenModule _ modul
							-> modul.mod_defs.def_classes!!dcl_index
						STE_ClosedModule
							-> dcl_module.dcl_common.com_class_defs.[dcl_index]
		  all_member_idents = [ ds_ident \\ {ds_ident} <-: class_def.class_members ]
		= (Yes (all_member_idents, wanted_members, class_def.class_name, STE_Member),
			modules, { cs & cs_symbol_table = cs_symbol_table })
	get_opt_bracket_info (ID_Type ii (Yes wanted_constructors)) {dcl_kind, dcl_index} mod_index modules cs=:{cs_symbol_table}
		# (dcl_module, module_entry, modules, cs_symbol_table)
				= get_module_and_entry dcl_kind mod_index modules cs_symbol_table
		  type_def = case module_entry.ste_kind of
						STE_OpenModule _ modul
							-> modul.mod_defs.def_types!!dcl_index
						STE_ClosedModule
							-> dcl_module.dcl_common.com_type_defs.[dcl_index]
		| not (isAlgType type_def.td_rhs)
			# cs = { cs & cs_error = checkError ii.ii_ident "is not an algebraic type" cs.cs_error,
							cs_symbol_table = cs_symbol_table }
			= (No, modules, cs)
		# (AlgType constructors) = type_def.td_rhs
		  all_constructor_idents = [ ds_ident \\ {ds_ident} <- constructors ]
		  cs = { cs & cs_symbol_table = cs_symbol_table }
		= (Yes (all_constructor_idents, wanted_constructors, type_def.td_name, STE_Constructor), modules, cs)
	  where
		isAlgType (AlgType _) = True
		isAlgType _ = False
	get_opt_bracket_info (ID_Record ii (Yes wanted_fields)) {dcl_kind, dcl_index} mod_index modules cs=:{cs_symbol_table}
		# (dcl_module, module_entry, modules, cs_symbol_table)
				= get_module_and_entry dcl_kind mod_index modules cs_symbol_table
		  type_def = case module_entry.ste_kind of
						STE_OpenModule _ modul
							-> modul.mod_defs.def_types!!dcl_index
						STE_ClosedModule
							-> dcl_module.dcl_common.com_type_defs.[dcl_index]
		| not (isRecordType type_def.td_rhs)
			# cs = { cs & cs_error = checkError ii.ii_ident "is not a record type" cs.cs_error,
							cs_symbol_table = cs_symbol_table }
			= (No, modules, cs)
		# (RecordType {rt_fields}) = type_def.td_rhs
		  all_field_idents = [ fs_name \\ {fs_name} <-: rt_fields ]
		  cs = { cs & cs_symbol_table = cs_symbol_table }
		= (Yes (all_field_idents, wanted_fields, type_def.td_name, STE_Field (hd all_field_idents)), modules, cs)
	  where
		isRecordType (RecordType _) = True
		isRecordType _ = False
	get_opt_bracket_info _ _ _ modules cs
		= (No, modules, cs)

	// this function is only for old syntax
	get_opt_bracket_info_old_syntax _ {dcl_index} STE_Class mod_index modules cs=:{cs_symbol_table}
		# (dcl_module, module_entry, modules, cs_symbol_table)
				= get_module_and_entry STE_Class mod_index modules cs_symbol_table
		  class_def = case module_entry.ste_kind of
						STE_OpenModule _ modul
							-> modul.mod_defs.def_classes!!dcl_index
						STE_ClosedModule
							-> dcl_module.dcl_common.com_class_defs.[dcl_index]
		  all_member_idents = [ ds_ident \\ {ds_ident} <-: class_def.class_members ]
		  (all_member_idents_2, cs_symbol_table)
		  		= foldSt filter_member all_member_idents ([], cs_symbol_table)
		= (Yes (all_member_idents_2, [], class_def.class_name, STE_Member),
			modules, { cs & cs_symbol_table = cs_symbol_table })
	get_opt_bracket_info_old_syntax _ {dcl_index} STE_Type mod_index modules cs=:{cs_symbol_table}
		# (dcl_module, module_entry, modules, cs_symbol_table)
				= get_module_and_entry STE_Type mod_index modules cs_symbol_table
		  type_def = case module_entry.ste_kind of
						STE_OpenModule _ modul
							-> modul.mod_defs.def_types!!dcl_index
						STE_ClosedModule
							-> dcl_module.dcl_common.com_type_defs.[dcl_index]
		  cs = { cs & cs_symbol_table = cs_symbol_table }
		= case type_def.td_rhs of
			RecordType {rt_fields}
				# all_field_idents = [ fs_name \\ {fs_name} <-: rt_fields ]
				-> (Yes (all_field_idents, [], type_def.td_name, STE_Field (hd all_field_idents)), modules, cs)
			_	-> (No, modules, cs)
	get_opt_bracket_info_old_syntax _ _ _ _ modules cs
		= (No, modules, cs)
	
	// only for old syntax
	filter_member member_id=:{id_info} (accu, cs_symbol_table)
		// it is possible that a member that had to be added the the list of wanted
		// symbols is already in there because an identifier with the same name was
		// explicitly imported. Special case: class and member have the same name
		# ({ste_kind}, cs_symbol_table) = readPtr id_info cs_symbol_table
		= case ste_kind of
			STE_ExplImp _ _ _ _
				-> (accu, cs_symbol_table)
			_	-> ([member_id:accu], cs_symbol_table)
			
	get_module_and_entry dcl_kind mod_index modules cs_symbol_table
		# index_mod_with_def = case dcl_kind of
								STE_Imported _ index_mod_with_def
									-> abort "assertion 2 failed in module explicitimports"
								_	-> mod_index
							// get the index of the module where the symbol is defined
		  (dcl_module=:{dcl_name=dcl_name=:{id_info}}, modules) = modules![index_mod_with_def]
		  (module_entry, cs_symbol_table) = readPtr id_info cs_symbol_table
		= (dcl_module, module_entry, modules, cs_symbol_table)

	check_wanted_idents structure_name {ii_ident=ii_ident=:{id_info}} cs=:{cs_symbol_table}
		# (ste=:{ste_kind}, cs_symbol_table) = readPtr id_info cs_symbol_table
		  cs = { cs & cs_symbol_table = cs_symbol_table }
		= case ste_kind of
			STE_ExplImp a b _ True
				-> cs 
			_	-> { cs & cs_error = checkError ii_ident ("does not belong to "+++toString structure_name) cs.cs_error}

	overwrite_wanted_idents {ii_ident={id_info}} cs_symbol_table
		# (ste=:{ste_kind}, cs_symbol_table) = readPtr id_info cs_symbol_table
		= case ste_kind of
			STE_ExplImp a b c _
				-> writePtr id_info { ste & ste_kind = STE_ExplImp a b c False } cs_symbol_table
			STE_Empty
				-> cs_symbol_table
		
	remove_and_collect ident=:{id_info} (wanted_symbols_accu, cs_symbol_table)
		# (ste=:{ste_kind=STE_ExplImp _ _ _ is_unwanted}, cs_symbol_table) = readPtr id_info cs_symbol_table
		| is_unwanted
			= (wanted_symbols_accu, writePtr id_info { ste & ste_kind = STE_Empty } cs_symbol_table)
		= ([ident:wanted_symbols_accu], cs_symbol_table)


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

checkExplicitImportCompleteness :: !Int ![ExplicitImport] !*{#DclModule} !*{#FunDef} !*ExpressionHeap !*CheckState 
				-> (!.{#DclModule},!.{#FunDef},!.ExpressionHeap,!.CheckState)
checkExplicitImportCompleteness main_dcl_module_n dcls_explicit dcl_modules icl_functions expr_heap 
								cs=:{cs_symbol_table, cs_error}
	#! nr_icl_functions = size icl_functions
	   box_ccs = { ccs_dcl_modules = dcl_modules, ccs_icl_functions = icl_functions,
	   			ccs_set_of_visited_icl_funs = createArray nr_icl_functions False,
				ccs_expr_heap = expr_heap, ccs_symbol_table = cs_symbol_table,
				ccs_error = cs_error, ccs_heap_changes_accu = [] }
	   ccs = foldSt checkCompleteness dcls_explicit { box_ccs = box_ccs }
	   { ccs_dcl_modules, ccs_icl_functions, ccs_expr_heap, ccs_symbol_table, ccs_error, ccs_heap_changes_accu }
	   		= ccs.box_ccs
	// repair heap contents
	   ccs_symbol_table = foldSt replace_ste_with_previous ccs_heap_changes_accu ccs_symbol_table
	   cs = { cs & cs_symbol_table = ccs_symbol_table, cs_error = ccs_error }
	= (ccs_dcl_modules, ccs_icl_functions, ccs_expr_heap, cs)
  where
	checkCompleteness :: !ExplicitImport *CheckCompletenessStateBox -> *CheckCompletenessStateBox
	checkCompleteness (ExplicitImport {dcl_ident, dcl_index, dcl_kind=STE_FunctionOrMacro _} import_position) ccs 
		= checkCompletenessOfMacro dcl_ident dcl_index main_dcl_module_n import_position ccs
	checkCompleteness (ExplicitImport {dcl_ident, dcl_index, dcl_kind=STE_Imported (STE_FunctionOrMacro _) mod_index} import_position) ccs 
		= checkCompletenessOfMacro dcl_ident dcl_index main_dcl_module_n import_position ccs
	checkCompleteness (ExplicitImport {dcl_ident, dcl_index, dcl_kind=STE_Imported expl_imp_kind mod_index} import_position) ccs 
		#! ({dcl_common,dcl_functions}, ccs) = ccs!box_ccs.ccs_dcl_modules.[mod_index]
		   cci = { box_cci = { cci_import_position = import_position, cci_main_dcl_module_n=main_dcl_module_n }}
		= case expl_imp_kind of
			STE_Type			-> check_completeness dcl_common.com_type_defs.[dcl_index] cci ccs
			STE_Constructor		-> check_completeness dcl_common.com_cons_defs.[dcl_index] cci ccs
			(STE_Field _)		-> check_completeness dcl_common.com_selector_defs.[dcl_index] cci ccs
			STE_Class			-> check_completeness dcl_common.com_class_defs.[dcl_index] cci ccs
			STE_Member			-> check_completeness dcl_common.com_member_defs.[dcl_index] cci ccs
			(STE_Instance _)	-> check_completeness dcl_common.com_instance_defs.[dcl_index] cci ccs
			STE_DclFunction		-> check_completeness dcl_functions.[dcl_index] cci ccs

	checkCompletenessOfMacro :: !Ident !Index !Int !Position *CheckCompletenessStateBox -> *CheckCompletenessStateBox
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
	check_completeness {ins_type} cci ccs
		= check_completeness ins_type cci ccs

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
