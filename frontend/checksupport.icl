implementation module checksupport

import StdEnv, compare_constructor
import syntax, predef
import utilities

::	VarHeap :== Heap VarInfo

//cIclModIndex 			:== 0

CS_NotChecked 	:== -1
NotFound		:== -1
	
cModuleScope	:== 0
cGlobalScope	:== 1

cIsNotADclModule 	:== False
cIsADclModule 		:== True

// MW..
cNeedStdArray	:== 1
cNeedStdEnum	:== 2
cNeedStdDynamics:== 4
// ..MW

::	Heaps =
	{	hp_var_heap			::!.VarHeap
	,	hp_expression_heap	::!.ExpressionHeap
	,	hp_type_heaps		::!.TypeHeaps
	}

::	ErrorAdmin = { ea_file :: !.File, ea_loc :: ![IdentPos], ea_ok :: !Bool }

::	CheckState = { cs_symbol_table :: !.SymbolTable, cs_predef_symbols :: !.PredefinedSymbols, cs_error :: !.ErrorAdmin, cs_x :: !CheckStateX }

::	CheckStateX = {x_needed_modules :: !BITVECT,x_main_dcl_module_n :: !Int }

::	ConversionTable		:== {# .{# Int }}

cTypeDefs				:== 0
cConstructorDefs		:== 1
cSelectorDefs			:== 2
cClassDefs				:== 3
cMemberDefs				:== 4
cInstanceDefs			:== 5
cFunctionDefs			:== 6
cMacroDefs				:== 7

cConversionTableSize	:== 8

instance toInt STE_Kind
where
	toInt STE_Type					= cTypeDefs
	toInt STE_Constructor			= cConstructorDefs
	toInt (STE_Field _)				= cSelectorDefs
	toInt STE_Class					= cClassDefs
	toInt STE_Member				= cMemberDefs
	toInt STE_Instance				= cInstanceDefs
	toInt STE_DclFunction			= cFunctionDefs
	toInt (STE_FunctionOrMacro _)	= cMacroDefs
	toInt _							= NoIndex

::	CommonDefs =
	{	com_type_defs 		:: !.{# CheckedTypeDef}
	,	com_cons_defs		:: !.{# ConsDef}
	,	com_selector_defs	:: !.{# SelectorDef}
	,	com_class_defs		:: !.{# ClassDef}
	,	com_member_defs		:: !.{# MemberDef}
	,	com_instance_defs	:: !.{# ClassInstance}
	}

::	Declaration =
	{	dcl_ident	:: !Ident
	,	dcl_pos		:: !Position
	,	dcl_kind	:: !STE_Kind
	,	dcl_index	:: !Index
	}

::	Declarations = {
		dcls_import		::!{!Declaration}
	,	dcls_local		::![Declaration]
	,	dcls_local_for_import ::!{!Declaration}
	,	dcls_explicit	::!{!ExplicitImport}
	}

:: ExplicitImport = ExplicitImport !Declaration !LineNr;
	
::	IclModule  =
	{	icl_name			:: !Ident
	,	icl_functions		:: !.{# FunDef }
	,	icl_instances		:: !IndexRange
	,	icl_specials		:: !IndexRange
	,	icl_common			:: !.CommonDefs
//	,	icl_declared		:: !Declarations
	,	icl_import		:: !{!Declaration}
	,	icl_imported_objects	:: ![ImportedObject]
	,	icl_used_module_numbers :: !ModuleNumberSet
	}

::	DclModule =
	{	dcl_name			:: !Ident
	,	dcl_functions		:: !{# FunType }
	,	dcl_instances		:: !IndexRange
	,	dcl_macros			:: !IndexRange
	,	dcl_class_specials	:: !IndexRange
	,	dcl_specials		:: !IndexRange
	,	dcl_common			:: !CommonDefs
	,	dcl_sizes			:: !{# Int}
	,	dcl_declared		:: !Declarations
	,	dcl_conversions		:: !Optional ConversionTable
	,	dcl_is_system		:: !Bool
	,	dcl_imported_module_numbers :: !ModuleNumberSet
	}

:: ModuleNumberSet = ModuleNumbers !Int !ModuleNumberSet | EndModuleNumbers;

in_module_number_set :: !Int !ModuleNumberSet -> Bool
in_module_number_set n EndModuleNumbers
	= False;
in_module_number_set n (ModuleNumbers module_numbers rest_module_numbers)
	| n<32
		= (module_numbers bitand (1<<n))<>0
		= in_module_number_set (n-32) rest_module_numbers

class Erroradmin state // PK...
where
	pushErrorAdmin :: !IdentPos *state -> *state
	setErrorAdmin :: !IdentPos *state -> *state
	popErrorAdmin  :: *state -> *state

instance Erroradmin ErrorAdmin
where
	pushErrorAdmin pos error=:{ea_loc}
		= { error & ea_loc = [pos : ea_loc] } 
	
	setErrorAdmin pos error
		= { error & ea_loc = [pos] } 
	
	popErrorAdmin error=:{ea_loc = [_:ea_locs]}
		=  { error & ea_loc = ea_locs }

instance Erroradmin CheckState
where
	pushErrorAdmin pos cs=:{cs_error}
		= {cs & cs_error = pushErrorAdmin pos cs_error } 
	
	setErrorAdmin pos cs=:{cs_error}
		= {cs & cs_error = setErrorAdmin pos cs_error }
	
	popErrorAdmin cs=:{cs_error}
		= {cs & cs_error = popErrorAdmin cs_error } //...PK

newPosition :: !Ident  !Position -> IdentPos 
newPosition id (FunPos file_name line_nr _)
	= { ip_ident = id, ip_line = line_nr, ip_file = file_name }
newPosition id (LinePos file_name line_nr)
	= { ip_ident = id, ip_line = line_nr, ip_file = file_name }
newPosition id (PreDefPos file_name)
	= { ip_ident = id, ip_line = cNotALineNumber, ip_file = file_name.id_name }
newPosition id NoPos
	= { ip_ident = id, ip_line = cNotALineNumber, ip_file = "???" }

checkError :: !a !b !*ErrorAdmin -> *ErrorAdmin | <<< a & <<< b // PK
checkError id mess error=:{ea_file,ea_loc=[]}
	= { error & ea_file = ea_file <<< "Check Error " <<< "\"" <<< id <<< "\" " <<< mess <<< '\n', ea_ok = False }
checkError id mess error=:{ea_file,ea_loc}
	= { error & ea_file = ea_file <<< "Check Error " <<< hd ea_loc <<< ":\"" <<< id  <<< "\" " <<< mess <<< '\n', ea_ok = False }

checkWarning :: !a !b !*ErrorAdmin -> *ErrorAdmin | <<< a & <<< b // PK
checkWarning id mess error=:{ea_file,ea_loc=[]}
	= { error & ea_file = ea_file <<< "Check Warning " <<< "\"" <<< id <<< "\" " <<< mess <<< '\n' }
checkWarning id mess error=:{ea_file,ea_loc}
	= { error & ea_file = ea_file <<< "Check Warning " <<< hd ea_loc <<< ":\"" <<< id  <<< "\" " <<< mess <<< '\n' }


checkErrorWithIdentPos :: !IdentPos !a !*ErrorAdmin -> .ErrorAdmin | <<< a;
checkErrorWithIdentPos ident_pos mess error=:{ea_file}
	= { error & ea_file = ea_file <<< "Check Error " <<< ident_pos <<< ":" <<< mess <<< '\n', ea_ok = False }

class envLookUp a :: !a !(Env Ident .b) -> (!Bool,.b)

instance envLookUp TypeVar
where
	envLookUp var [bind:binds]
		| var.tv_name == bind.bind_src
			= (True, bind.bind_dst)
			= envLookUp var binds
	envLookUp var []
		= (False, abort "illegal value")
	
instance envLookUp AttributeVar
where
	envLookUp var [bind:binds]
		| var.av_name == bind.bind_src
			= (True, bind.bind_dst)
			= envLookUp var binds
	envLookUp var []
		= (False, abort "illegal value")

instance envLookUp ATypeVar
where
	envLookUp var=:{atv_variable} [bind:binds]
		| atv_variable.tv_name == bind.bind_src
			= (True, bind.bind_dst)
			= envLookUp var binds
	envLookUp var []
		= (False, abort "illegal value")

retrieveAndRemoveImportsFromSymbolTable :: ![(.a,.Declarations)] [Declaration] *(Heap SymbolTableEntry) -> ([Declaration],.Heap SymbolTableEntry);
retrieveAndRemoveImportsFromSymbolTable [(_, {dcls_import,dcls_local,dcls_local_for_import}) : imports] all_decls symbol_table
//	# (all_decls, symbol_table) = retrieveAndRemoveImportsOfModuleFromSymbolTable dcls_import dcls_local all_decls symbol_table
	# (all_decls, symbol_table) = retrieveAndRemoveImportsOfModuleFromSymbolTable2 dcls_import dcls_local_for_import all_decls symbol_table
	= retrieveAndRemoveImportsFromSymbolTable imports all_decls symbol_table
retrieveAndRemoveImportsFromSymbolTable []  all_decls symbol_table
	= (all_decls, symbol_table)

retrieveAndRemoveImportsOfModuleFromSymbolTable2 :: !{!.Declaration} !{!.Declaration} ![.Declaration] !*(Heap SymbolTableEntry) -> ([Declaration],.Heap SymbolTableEntry);
retrieveAndRemoveImportsOfModuleFromSymbolTable2 imports locals_for_import all_decls symbol_table
	# (all_decls, symbol_table) = retrieve_declared_symbols_in_array 0 imports all_decls symbol_table
	= retrieve_declared_symbols_in_array 0 locals_for_import all_decls symbol_table

retrieveAndRemoveImportsOfModuleFromSymbolTable :: !{!.Declaration} ![.Declaration] ![.Declaration] !*(Heap SymbolTableEntry) -> ([Declaration],.Heap SymbolTableEntry);
retrieveAndRemoveImportsOfModuleFromSymbolTable imports locals all_decls symbol_table
	# (all_decls, symbol_table) = retrieve_declared_symbols_in_array 0 imports all_decls symbol_table
	= retrieve_declared_symbols locals all_decls symbol_table
where
	retrieve_declared_symbols :: ![Declaration] ![Declaration] !*SymbolTable -> (![Declaration], !*SymbolTable)
	retrieve_declared_symbols [declaration=:{dcl_ident=ident=:{id_info},dcl_kind,dcl_index}:symbols] decls symbol_table
		#! entry = sreadPtr id_info symbol_table
		# {ste_kind,ste_def_level} = entry
		| ste_kind == STE_Empty || ste_def_level > cModuleScope
			= retrieve_declared_symbols symbols decls symbol_table
			# symbol_table = symbol_table <:= (id_info, entry.ste_previous)
			= case ste_kind of
				STE_Field selector_id
					| case dcl_kind of
							STE_Field f -> f==selector_id
							_ -> False
						-> retrieve_declared_symbols symbols [declaration : decls ] (removeFieldFromSelectorDefinition selector_id NoIndex dcl_index symbol_table)
						#! declaration = { declaration & dcl_kind = ste_kind }
						-> retrieve_declared_symbols symbols [declaration : decls ] (removeFieldFromSelectorDefinition selector_id NoIndex dcl_index symbol_table)
				STE_Imported (STE_Field selector_id) def_mod
					| case dcl_kind of
							STE_Imported (STE_Field f) d -> d==def_mod && f==selector_id
							_ -> False
						-> retrieve_declared_symbols symbols [declaration : decls ] (removeFieldFromSelectorDefinition selector_id def_mod dcl_index symbol_table)
						#! declaration = { declaration & dcl_kind = ste_kind }
						-> retrieve_declared_symbols symbols [declaration : decls ] (removeFieldFromSelectorDefinition selector_id def_mod dcl_index symbol_table)
				_
					| same_STE_Kind ste_kind dcl_kind
						-> retrieve_declared_symbols symbols [declaration : decls ] symbol_table					
						#! declaration = { declaration & dcl_kind = ste_kind }
						-> retrieve_declared_symbols symbols [declaration : decls ] symbol_table
	retrieve_declared_symbols [] decls symbol_table
		= (decls, symbol_table)

retrieve_declared_symbols_in_array :: !Int !{!Declaration} ![Declaration] !*SymbolTable -> (![Declaration], !*SymbolTable)
retrieve_declared_symbols_in_array symbol_index symbols decls symbol_table
	| symbol_index<size symbols
		#! (declaration,symbols) = symbols![symbol_index]
		# {dcl_ident=ident=:{id_info},dcl_kind}=declaration
		#! entry = sreadPtr id_info symbol_table
		# {ste_kind,ste_def_level} = entry
		| ste_kind == STE_Empty || ste_def_level > cModuleScope
			= retrieve_declared_symbols_in_array (symbol_index+1) symbols decls symbol_table
			# symbol_table = symbol_table <:= (id_info, entry.ste_previous)
			= case ste_kind of
				STE_Field selector_id
					| case dcl_kind of
							STE_Field f -> f==selector_id
							_ -> False
						#! (declaration,symbols) = symbols![symbol_index]
						#! dcl_index = symbols.[symbol_index].dcl_index
						-> retrieve_declared_symbols_in_array (symbol_index+1) symbols [declaration : decls ] (removeFieldFromSelectorDefinition selector_id NoIndex dcl_index symbol_table)
						#! (declaration,symbols) = symbols![symbol_index]
						#! dcl_index = declaration.dcl_index
						#! declaration = { declaration & dcl_kind = ste_kind }
						-> retrieve_declared_symbols_in_array (symbol_index+1) symbols [declaration : decls ] (removeFieldFromSelectorDefinition selector_id NoIndex dcl_index symbol_table)
				STE_Imported (STE_Field selector_id) def_mod
					| case dcl_kind of
							STE_Imported (STE_Field f) d -> d==def_mod && f==selector_id
							_ -> False
						#! (declaration,symbols) = symbols![symbol_index]
						#! dcl_index = symbols.[symbol_index].dcl_index
						-> retrieve_declared_symbols_in_array (symbol_index+1) symbols [declaration : decls ] (removeFieldFromSelectorDefinition selector_id def_mod dcl_index symbol_table)
						#! (declaration,symbols) = symbols![symbol_index]
						#! dcl_index = declaration.dcl_index
						#! declaration = { declaration & dcl_kind = ste_kind }
						-> retrieve_declared_symbols_in_array (symbol_index+1) symbols [declaration : decls ] (removeFieldFromSelectorDefinition selector_id def_mod dcl_index symbol_table)
				_
					| same_STE_Kind ste_kind dcl_kind
						#! (declaration,symbols) = symbols![symbol_index]
						-> retrieve_declared_symbols_in_array (symbol_index+1) symbols [declaration : decls ] symbol_table					
						#! (declaration,symbols) = symbols![symbol_index]
						#! declaration = { declaration & dcl_kind = ste_kind }
						-> retrieve_declared_symbols_in_array (symbol_index+1) symbols [declaration : decls ] symbol_table
		= (decls, symbol_table)

same_STE_Kind (STE_Imported s1 i1) (STE_Imported s2 i2) = i1==i2 && same_STE_Kind s1 s2
same_STE_Kind STE_DclFunction STE_DclFunction = True
same_STE_Kind (STE_FunctionOrMacro []) (STE_FunctionOrMacro []) = True
same_STE_Kind STE_Type STE_Type = True
same_STE_Kind STE_Constructor STE_Constructor = True
same_STE_Kind (STE_Field f1) (STE_Field f2) = f1==f2
same_STE_Kind STE_Instance STE_Instance = True
same_STE_Kind STE_Member STE_Member = True
same_STE_Kind STE_Class STE_Class = True
same_STE_Kind _ _ = False

removeImportsAndLocalsOfModuleFromSymbolTable :: !Declarations !*(Heap SymbolTableEntry) -> .Heap SymbolTableEntry
removeImportsAndLocalsOfModuleFromSymbolTable {dcls_import,dcls_local} symbol_table
	# symbol_table = remove_declared_symbols_in_array 0 dcls_import symbol_table
	= remove_declared_symbols dcls_local symbol_table
where
	remove_declared_symbols :: ![Declaration] !*SymbolTable -> !*SymbolTable
	remove_declared_symbols [symbol=:{dcl_ident={id_info},dcl_index}:symbols] symbol_table
		#! entry = sreadPtr id_info symbol_table
		# {ste_kind,ste_def_level} = entry
		| ste_kind == STE_Empty || ste_def_level > cModuleScope
			= remove_declared_symbols symbols symbol_table
			# symbol_table = symbol_table <:= (id_info, entry.ste_previous)
			= case ste_kind of
				STE_Field selector_id
					-> remove_declared_symbols symbols (removeFieldFromSelectorDefinition selector_id NoIndex dcl_index symbol_table)
				STE_Imported (STE_Field selector_id) def_mod
					-> remove_declared_symbols symbols (removeFieldFromSelectorDefinition selector_id def_mod dcl_index symbol_table)
				_
					-> remove_declared_symbols symbols symbol_table					
	remove_declared_symbols [] symbol_table
		= symbol_table

	remove_declared_symbols_in_array :: !Int !{!Declaration} !*SymbolTable -> !*SymbolTable
	remove_declared_symbols_in_array symbol_index symbols symbol_table
		| symbol_index<size symbols
			#! (symbol,symbols) = symbols![symbol_index]
			# {dcl_ident={id_info}}=symbol
			#! entry = sreadPtr id_info symbol_table
			# {ste_kind,ste_def_level} = entry
			| ste_kind == STE_Empty || ste_def_level > cModuleScope
				= remove_declared_symbols_in_array (symbol_index+1) symbols symbol_table
				# symbol_table = symbol_table <:= (id_info, entry.ste_previous)
				= case ste_kind of
					STE_Field selector_id
						#! dcl_index = symbols.[symbol_index].dcl_index
						-> remove_declared_symbols_in_array (symbol_index+1) symbols (removeFieldFromSelectorDefinition selector_id NoIndex dcl_index symbol_table)
					STE_Imported (STE_Field selector_id) def_mod
						#! dcl_index = symbols.[symbol_index].dcl_index
						-> remove_declared_symbols_in_array (symbol_index+1) symbols (removeFieldFromSelectorDefinition selector_id def_mod dcl_index symbol_table)
					_
						-> remove_declared_symbols_in_array (symbol_index+1) symbols symbol_table
			= symbol_table

addLocalFunctionDefsToSymbolTable :: !Level !Index !Index !u:{#FunDef} !*SymbolTable !*ErrorAdmin -> (!u:{# FunDef}, !*SymbolTable, !*ErrorAdmin)
addLocalFunctionDefsToSymbolTable level from_index to_index fun_defs symbol_table error
	| from_index == to_index
		= (fun_defs, symbol_table, error)	
		# (fun_def, fun_defs) = fun_defs![from_index]
		  (symbol_table, error) = addDefToSymbolTable level from_index fun_def.fun_symb (STE_FunctionOrMacro []) symbol_table error
		= addLocalFunctionDefsToSymbolTable level (inc from_index) to_index fun_defs symbol_table error

NewEntry symbol_table symb_ptr def_kind def_index level previous :==
	 symbol_table <:= (symb_ptr,{  ste_kind = def_kind, ste_index = def_index, ste_def_level = level, ste_previous = previous })
	
		
addDefToSymbolTable :: !Level !Index !Ident !STE_Kind !*SymbolTable !*ErrorAdmin -> (!* SymbolTable, !*ErrorAdmin)
addDefToSymbolTable level def_index def_ident=:{id_info} def_kind symbol_table error
	#! entry = sreadPtr id_info symbol_table
	| entry.ste_kind == STE_Empty || entry.ste_def_level <> level
		# entry = {ste_index = def_index, ste_kind = def_kind, ste_def_level = level, ste_previous = entry }
		= (symbol_table <:= (id_info,entry), error)
		= (symbol_table, checkError def_ident " already defined" error)

addDeclaredSymbolsToSymbolTable2 :: .Bool .Int !{!.Declaration} !{!.Declaration} !*CheckState -> .CheckState;
addDeclaredSymbolsToSymbolTable2 is_dcl_mod ste_index locals imported cs
	# cs=add_imports_in_array_to_symbol_table 0 is_dcl_mod imported cs
	= addLocalSymbolsForImportToSymbolTable 0 locals ste_index cs

addDeclaredSymbolsToSymbolTable :: .Bool .Int ![.Declaration] !{!.Declaration} !*CheckState -> .CheckState;
addDeclaredSymbolsToSymbolTable is_dcl_mod ste_index locals imported cs
	# cs=add_imports_in_array_to_symbol_table 0 is_dcl_mod imported cs
	= addLocalSymbolsToSymbolTable locals ste_index cs
where
	add_imports_to_symbol_table is_dcl_mod [{dcl_ident,dcl_pos,dcl_kind,dcl_index} : symbols] cs=:{cs_x}
		= case dcl_kind of
			STE_Imported def_kind def_mod
				| is_dcl_mod || def_mod <> cs_x.x_main_dcl_module_n
	//				-> add_imports_to_symbol_table is_dcl_mod symbols (addImportedSymbol dcl_ident dcl_pos def_kind dcl_index def_mod cs)
					-> add_imports_to_symbol_table is_dcl_mod symbols (addIndirectlyImportedSymbol dcl_ident dcl_pos dcl_kind def_kind dcl_index def_mod cs)
					-> add_imports_to_symbol_table is_dcl_mod symbols cs
			STE_FunctionOrMacro _
				-> add_imports_to_symbol_table is_dcl_mod symbols (addImportedFunctionOrMacro dcl_ident dcl_index cs)
	add_imports_to_symbol_table is_dcl_mod [] cs
		= cs

add_imports_in_array_to_symbol_table symbol_index is_dcl_mod symbols cs=:{cs_x}
	| symbol_index<size symbols
		#! ({dcl_ident,dcl_pos,dcl_kind},symbols) = symbols![symbol_index]
		= case dcl_kind of
			STE_Imported def_kind def_mod
//					| is_dcl_mod || def_mod <> cIclModIndex
				| is_dcl_mod || def_mod <> cs_x.x_main_dcl_module_n
//					-> add_imports_in_array_to_symbol_table (symbol_index+1) is_dcl_mod symbols (addImportedSymbol dcl_ident dcl_pos def_kind dcl_index def_mod cs)
					#! dcl_index= symbols.[symbol_index].dcl_index
					-> add_imports_in_array_to_symbol_table (symbol_index+1) is_dcl_mod symbols (addIndirectlyImportedSymbol dcl_ident dcl_pos dcl_kind def_kind dcl_index def_mod cs)
					-> add_imports_in_array_to_symbol_table (symbol_index+1) is_dcl_mod symbols cs
			STE_FunctionOrMacro _
					#! dcl_index= symbols.[symbol_index].dcl_index
				-> add_imports_in_array_to_symbol_table (symbol_index+1) is_dcl_mod symbols (addImportedFunctionOrMacro dcl_ident dcl_index cs)
		= cs

addLocalSymbolsForImportToSymbolTable :: !Int !{!.Declaration} Int !*CheckState -> .CheckState;
addLocalSymbolsForImportToSymbolTable symbol_index symbols mod_index cs
	| symbol_index<size symbols
		# ({dcl_ident,dcl_pos,dcl_kind,dcl_index},symbols) = symbols![symbol_index]
		= case dcl_kind of
			STE_FunctionOrMacro _
				-> addLocalSymbolsForImportToSymbolTable (symbol_index+1) symbols mod_index (addImportedFunctionOrMacro dcl_ident dcl_index cs)
			STE_Imported def_kind def_mod
				-> addLocalSymbolsForImportToSymbolTable (symbol_index+1) symbols mod_index (addIndirectlyImportedSymbol dcl_ident dcl_pos dcl_kind def_kind dcl_index mod_index cs)
		= cs

addLocalSymbolsToSymbolTable :: ![.Declaration] Int !*CheckState -> .CheckState;
addLocalSymbolsToSymbolTable [{dcl_ident,dcl_pos,dcl_kind,dcl_index} : symbols] mod_index cs
	= case dcl_kind of
		STE_FunctionOrMacro _
			-> addLocalSymbolsToSymbolTable symbols mod_index (addImportedFunctionOrMacro dcl_ident dcl_index cs)
		_
			-> addLocalSymbolsToSymbolTable symbols mod_index (addImportedSymbol dcl_ident dcl_pos dcl_kind dcl_index mod_index cs)
addLocalSymbolsToSymbolTable [] mod_index cs
	= cs

addImportedFunctionOrMacro :: !Ident .Int !*CheckState -> .CheckState;
addImportedFunctionOrMacro ident=:{id_info} def_index cs=:{cs_symbol_table}
	#! entry = sreadPtr id_info cs_symbol_table
	= case entry.ste_kind of
		STE_Empty
			-> { cs & cs_symbol_table = NewEntry cs.cs_symbol_table id_info (STE_FunctionOrMacro []) def_index cModuleScope entry}
		STE_FunctionOrMacro _
			| entry.ste_index == def_index
				-> cs
		_
			-> { cs & cs_error = checkError ident " multiply imported" cs.cs_error}

addFieldToSelectorDefinition :: !Ident (Global .Int) !*CheckState -> .CheckState;
addFieldToSelectorDefinition {id_info} glob_field_index cs=:{cs_symbol_table}
	# (entry, cs_symbol_table) = readPtr id_info cs_symbol_table 
	  cs = { cs & cs_symbol_table = cs_symbol_table }
	= case entry.ste_kind of
		STE_Selector selector_list
			-> { cs & cs_symbol_table = cs.cs_symbol_table <:= (id_info, { entry & ste_kind = STE_Selector [ glob_field_index : selector_list ] })}
		_
			-> { cs & cs_symbol_table = NewEntry cs.cs_symbol_table id_info (STE_Selector [glob_field_index]) NoIndex cModuleScope entry }

addImportedSymbol :: !Ident !Position !STE_Kind !.Int !.Int !*CheckState -> .CheckState;
addImportedSymbol ident pos def_kind def_index def_mod cs=:{cs_symbol_table}
	# (entry, cs_symbol_table) = readPtr ident.id_info cs_symbol_table 
	= add_imported_symbol entry ident pos def_kind def_index def_mod { cs & cs_symbol_table = cs_symbol_table }
	where
		add_imported_symbol /*entry=:*/{ste_kind = STE_Empty} {id_name,id_info} _ def_kind def_index def_mod cs=:{cs_symbol_table}
			// JVG: read the entry again, because it is boxed
			# (entry, cs_symbol_table) = readPtr id_info cs_symbol_table
			# cs = { cs & cs_symbol_table = NewEntry cs_symbol_table id_info (STE_Imported def_kind def_mod) def_index cModuleScope entry}
			= case def_kind of
				STE_Field selector_id
					-> addFieldToSelectorDefinition selector_id	{ glob_module = def_mod, glob_object = def_index } cs
				_
					-> cs
		add_imported_symbol	/*entry=:*/{ste_kind = STE_Imported kind mod_index, ste_index} ident=:{id_info} _ def_kind def_index def_mod cs
			| kind == def_kind && mod_index == def_mod && ste_index == def_index
				= cs
		add_imported_symbol	entry ident pos def_kind def_index def_mod cs=:{cs_error}
			= { cs & cs_error = checkErrorWithIdentPos (newPosition ident pos) " multiply imported" cs_error}

// same as addImportedSymbol but does not create a new STE_Imported
addIndirectlyImportedSymbol :: !Ident !Position !STE_Kind !STE_Kind !.Int !.Int !*CheckState -> .CheckState;
addIndirectlyImportedSymbol ident pos dcl_kind def_kind def_index def_mod cs=:{cs_symbol_table}
	# (entry, cs_symbol_table) = readPtr ident.id_info cs_symbol_table
	= add_indirectly_imported_symbol entry ident pos def_kind def_index def_mod { cs & cs_symbol_table = cs_symbol_table }
	where
		add_indirectly_imported_symbol /*entry=:*/{ste_kind = STE_Empty} {id_name,id_info} _ def_kind def_index def_mod cs=:{cs_symbol_table}
			// JVG: read the entry again, because it is boxed
			# (entry, cs_symbol_table) = readPtr id_info cs_symbol_table
			# cs = { cs & cs_symbol_table = NewEntry cs_symbol_table id_info dcl_kind def_index cModuleScope entry}
			= case def_kind of
				STE_Field selector_id
					-> addFieldToSelectorDefinition selector_id	{ glob_module = def_mod, glob_object = def_index } cs
				_
					-> cs
		add_indirectly_imported_symbol	/*entry=:*/{ste_kind = STE_Imported kind mod_index, ste_index} ident=:{id_info} _ def_kind def_index def_mod cs
			| kind == def_kind && mod_index == def_mod && ste_index == def_index
				= cs
		add_indirectly_imported_symbol	entry ident pos def_kind def_index def_mod cs=:{cs_error}
			= { cs & cs_error = checkErrorWithIdentPos (newPosition ident pos) " multiply imported" cs_error}

addGlobalDefinitionsToSymbolTable :: ![.Declaration] !*CheckState -> .CheckState;
addGlobalDefinitionsToSymbolTable decls cs
	= foldSt add_global_definition decls cs
where
	add_global_definition {dcl_ident=ident=:{id_info},dcl_pos,dcl_kind,dcl_index} cs=:{cs_symbol_table}
		#! entry = sreadPtr id_info cs_symbol_table
		| entry.ste_def_level < cGlobalScope
			# cs = { cs & cs_symbol_table = NewEntry cs_symbol_table id_info dcl_kind dcl_index cGlobalScope entry }
			= case dcl_kind of
				STE_Field selector_id
					-> addFieldToSelectorDefinition selector_id	{ glob_module = NoIndex, glob_object = dcl_index } cs
				_
					-> cs
			= { cs & cs_error = checkErrorWithIdentPos (newPosition ident dcl_pos) "(global definition) already defined" cs.cs_error}

retrieveImportsFromSymbolTable :: ![Import ImportDeclaration] ![Declaration] !*{#DclModule} !*(Heap SymbolTableEntry) -> *(![Declaration],!*{#DclModule},!*Heap SymbolTableEntry);
retrieveImportsFromSymbolTable [{import_module=import_module=:{id_info},import_symbols} : mods ] decls modules symbol_table
	# ({ste_index}, symbol_table) = readPtr id_info symbol_table
	  ({dcl_declared={dcls_import,dcls_local,dcls_local_for_import}}, modules) = modules![ste_index]	
//	  (decls, symbol_table) = retrieveAndRemoveImportsOfModuleFromSymbolTable dcls_import dcls_local decls symbol_table
	  (decls, symbol_table) = retrieveAndRemoveImportsOfModuleFromSymbolTable2 dcls_import dcls_local_for_import decls symbol_table
	= retrieveImportsFromSymbolTable mods decls modules symbol_table
retrieveImportsFromSymbolTable [] decls modules symbol_table
	= (decls, modules, symbol_table)
 
removeFieldFromSelectorDefinition :: !Ident .Int .Int !*(Heap SymbolTableEntry) -> .Heap SymbolTableEntry;
removeFieldFromSelectorDefinition {id_info} field_mod field_index symbol_table 
	# (entry, symbol_table) = readPtr id_info symbol_table
	= case entry.ste_kind of
	  	STE_Selector selector_list
			-> symbol_table <:= (id_info, { entry & ste_kind = STE_Selector (remove_field field_mod field_index selector_list) })
		_	-> symbol_table
where	
	remove_field field_mod field_index [field=:{glob_module, glob_object} : fields]
		| field_mod == glob_module && field_index == glob_object
			= fields
			= [field : remove_field field_mod field_index fields]
	remove_field field_mod field_index []
		= []

removeDeclarationsFromSymbolTable :: ![Declaration] !Int !*(Heap SymbolTableEntry) -> *Heap SymbolTableEntry;
removeDeclarationsFromSymbolTable decls scope symbol_table
	= foldSt (remove_declaration scope) decls symbol_table
where
	remove_declaration scope {dcl_ident={id_name,id_info}, dcl_index} symbol_table
		# ({ste_kind,ste_previous}, symbol_table) = readPtr id_info symbol_table
		= case ste_kind of
			STE_Field field_id
				# symbol_table = removeFieldFromSelectorDefinition field_id NoIndex dcl_index symbol_table
				| ste_previous.ste_def_level == scope
					-> symbol_table <:= (id_info, ste_previous.ste_previous)
					-> symbol_table <:= (id_info, ste_previous)
			STE_Empty
				-> symbol_table
			_
				| ste_previous.ste_def_level == scope
					-> symbol_table <:= (id_info, ste_previous.ste_previous)
					-> symbol_table <:= (id_info, ste_previous)

removeLocalIdentsFromSymbolTable :: .Int !.[Ident] !*(Heap SymbolTableEntry) -> .Heap SymbolTableEntry;
removeLocalIdentsFromSymbolTable level idents symbol_table
	= foldSt (removeIdentFromSymbolTable level) idents symbol_table

removeIdentFromSymbolTable :: !.Int !Ident !*(Heap SymbolTableEntry) -> .Heap SymbolTableEntry;
removeIdentFromSymbolTable level {id_name,id_info} symbol_table
	#! {ste_previous,ste_def_level} = sreadPtr id_info symbol_table
	| level <= ste_def_level 
		= symbol_table <:= (id_info,ste_previous) // ---> ("removeIdentFromSymbolTable", id_name)
		= symbol_table // ---> ("NO removeIdentFromSymbolTable", id_name)

class toIdent a :: !a -> Ident

instance toIdent SymbIdent
where
	toIdent symb = symb.symb_name

instance toIdent TypeSymbIdent
where
	toIdent type_symb = type_symb.type_name

instance toIdent BoundVar
where
	toIdent var = var.var_name

instance toIdent TypeVar
where
	toIdent tvar = tvar.tv_name

instance toIdent ATypeVar
where
	toIdent {atv_variable} = atv_variable.tv_name


instance toIdent Ident
where
	toIdent id = id

instance toIdent ConsDef
where
	toIdent cons = cons.cons_symb

instance toIdent (TypeDef a)
where
	toIdent td = td.td_name

instance toIdent ClassDef
where
	toIdent cl = cl.class_name

instance toIdent MemberDef
where
	toIdent me = me.me_symb

instance toIdent FunDef
where
	toIdent fun = fun.fun_symb

instance toIdent SelectorDef
where
	toIdent sd = sd.sd_symb

/*
instance toIdent DeltaRule
where
	toIdent delta = delta.delta_name
*/

instance toIdent (a,b) | toIdent a
where
	toIdent (x,y) = toIdent x

instance == STE_Kind
where
	(==) (STE_FunctionOrMacro _) STE_DclFunction	= True
	(==) STE_DclFunction (STE_FunctionOrMacro _)	= True
	(==) sk1 sk2 									= equal_constructor sk1 sk2

instance <<< IdentPos
where
	(<<<) file {ip_file,ip_line,ip_ident}
	| ip_line == cNotALineNumber
		= file <<< '[' <<< ip_file <<< ',' <<< ip_ident <<< ']'
		= file <<< '[' <<< ip_file <<< ',' <<< ip_line <<< ',' <<< ip_ident <<< ']'
	

instance <<< STE_Kind
where
	(<<<) file
		(STE_FunctionOrMacro _)
			= file <<< "STE_FunctionOrMacro"
	(<<<) file
		STE_Type
			= file <<< "STE_Type"
	(<<<) file
		STE_Constructor
			= file <<< "STE_Constructor"
	(<<<) file
		(STE_Selector _)
			= file <<< "STE_Selector"
	(<<<) file
		STE_Class
			= file <<< "STE_Class"
	(<<<) file
		STE_Member
			= file <<< "STE_Member"
	(<<<) file
		STE_Instance
			= file <<< "STE_Instance"
	(<<<) file
		(STE_Variable _) 
			= file <<< "STE_Variable"
	(<<<) file
		(STE_TypeVariable _) 
			= file <<< "STE_TypeVariable"
	(<<<) file
		(STE_TypeAttribute _)
			= file <<< "STE_TypeAttribute"
	(<<<) file
		(STE_BoundTypeVariable _)
			= file <<< "STE_BoundTypeVariable"
	(<<<) file
		(STE_Imported _ _)
			= file <<< "STE_Imported"
	(<<<) file
		STE_DclFunction
			= file <<< "STE_DclFunction"
	(<<<) file
		(STE_Module _)
			= file <<< "STE_Module"
	(<<<) file
		(STE_OpenModule _ _)
			= file <<< "STE_OpenModule"
	(<<<) file
		STE_ClosedModule
			= file <<< "STE_ClosedModule"
	(<<<) file
		STE_LockedModule
			= file <<< "STE_LockedModule"
	(<<<) file
		STE_Empty 
			= file <<< "STE_Empty"

instance <<< Declaration
  where
	(<<<) file { dcl_ident } 
		= file <<< dcl_ident

