implementation module checksupport

import StdEnv, compare_constructor
import syntax, predef, containers
import utilities
from check import checkFunctions

import RWSDebug

::	VarHeap :== Heap VarInfo

cUndef			:== -1
CS_NotChecked 	:== -1
NotFound		:== -1
	
cModuleScope	:== 0
cGlobalScope	:== 1

cIsNotADclModule 	:== False
cIsADclModule 		:== True

cNeedStdArray	:== 1
cNeedStdEnum	:== 2
cNeedStdDynamics:== 4

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
	toInt (STE_Instance _)				= cInstanceDefs
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

::	Declarations = {
		dcls_import		::!{!Declaration}
	,	dcls_local		::![Declaration]
	,	dcls_local_for_import ::!{!Declaration}
	}

::	ExplImpInfos :== {!{!.ExplImpInfo}}

::	ExplImpInfo
		= ExplImpInfo Ident !.DeclaringModulesSet
		| TemporarilyFetchedAway

::	DeclaringModulesSet :== IntKeyHashtable DeclarationInfo

::	DeclarationInfo =
	{	di_decl			::	!Declaration
	,	di_instances	::	![Declaration]
	,	di_belonging	::	!NumberSet
	}

::	IclModule  =
	{	icl_name			:: !Ident
	,	icl_functions		:: !.{# FunDef }
	,	icl_instances		:: !IndexRange
	,	icl_specials		:: !IndexRange
	,	icl_common			:: !.CommonDefs
//	,	icl_declared		:: !Declarations
	,	icl_import		:: !{!Declaration}
	,	icl_imported_objects	:: ![ImportedObject]
	,	icl_used_module_numbers :: !NumberSet
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
	,	dcl_imported_module_numbers :: !NumberSet
	}

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


::	ExpressionInfo =
	{	ef_type_defs		:: !.{# CheckedTypeDef}
	,	ef_selector_defs	:: !.{# SelectorDef}
	,	ef_cons_defs		:: !.{# ConsDef}
	,	ef_member_defs		:: !.{# MemberDef}
	,	ef_class_defs		:: !.{# ClassDef}
	,	ef_modules			:: !.{# DclModule}
	,	ef_is_macro_fun		:: !Bool
	}

checkLocalFunctions :: !Index !Level !LocalDefs !*{#FunDef} !*ExpressionInfo !*Heaps !*CheckState
					-> (!.{#FunDef},!.ExpressionInfo,!.Heaps,!.CheckState);
checkLocalFunctions mod_index level (CollectedLocalDefs {loc_functions={ir_from,ir_to}}) fun_defs e_info heaps cs
	= checkFunctions mod_index level ir_from ir_to fun_defs e_info heaps cs


convertIndex :: !Index !Index !(Optional ConversionTable) -> !Index
convertIndex index table_index (Yes tables)
	= tables.[table_index].[index]
convertIndex index table_index No
	= index



retrieveGlobalDefinition :: !SymbolTableEntry !STE_Kind !Index -> (!Index, !Index)
retrieveGlobalDefinition {ste_kind = STE_Imported kind dcl_index, ste_def_level, ste_index} requ_kind mod_index
	| kind == requ_kind
		= (ste_index, dcl_index)
		= (NotFound, mod_index)
retrieveGlobalDefinition {ste_kind,ste_def_level,ste_index} requ_kind mod_index
	| ste_kind == requ_kind && ste_def_level == cGlobalScope
		= (ste_index, mod_index)
		= (NotFound, mod_index)


getBelongingSymbols :: !Declaration !v:{#DclModule} -> (!BelongingSymbols, !v:{#DclModule})
getBelongingSymbols {dcl_kind=STE_Imported STE_Type def_mod_index, dcl_index} dcl_modules
	# ({td_rhs}, dcl_modules)
			= dcl_modules![def_mod_index].dcl_common.com_type_defs.[dcl_index]
	= case td_rhs of
		AlgType constructors
			-> (BS_Constructors constructors, dcl_modules)
		RecordType {rt_fields}
			-> (BS_Fields rt_fields, dcl_modules)
		_
			-> (BS_Nothing, dcl_modules)
getBelongingSymbols {dcl_kind=STE_Imported STE_Class def_mod_index, dcl_index} dcl_modules
	# ({class_members}, dcl_modules)
			= dcl_modules![def_mod_index].dcl_common.com_class_defs.[dcl_index]
	= (BS_Members class_members, dcl_modules)
getBelongingSymbols _ dcl_modules
	= (BS_Nothing, dcl_modules)

nrOfBelongingSymbols :: !BelongingSymbols -> Int
nrOfBelongingSymbols (BS_Constructors constructors)
	= length constructors
nrOfBelongingSymbols (BS_Fields fields)
	= size fields
nrOfBelongingSymbols (BS_Members members)
	= size members
nrOfBelongingSymbols BS_Nothing
	= 0

:: BelongingSymbols
	=	BS_Constructors ![DefinedSymbol]
	|	BS_Fields !{#FieldSymbol}
	|	BS_Members !{#DefinedSymbol}
	|	BS_Nothing


removeImportsAndLocalsOfModuleFromSymbolTable :: !Declarations !*(Heap SymbolTableEntry) -> .Heap SymbolTableEntry
removeImportsAndLocalsOfModuleFromSymbolTable {dcls_import,dcls_local_for_import} symbol_table
	# symbol_table = remove_declared_symbols_in_array 0 dcls_import symbol_table
	= remove_declared_symbols_in_array 0 dcls_local_for_import symbol_table
where
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

addLocalFunctionDefsToSymbolTable :: !Level !Index !Index !Bool !*{#FunDef} !*SymbolTable !*ErrorAdmin -> (!*{# FunDef}, !*SymbolTable, !*ErrorAdmin)
addLocalFunctionDefsToSymbolTable level from_index to_index is_macro_fun fun_defs symbol_table error
	| from_index == to_index
		= (fun_defs, symbol_table, error)	
		# (fun_def, fun_defs) = fun_defs![from_index]
		# (symbol_table, error) = addDefToSymbolTable level from_index fun_def.fun_symb (STE_FunctionOrMacro []) symbol_table error
		| is_macro_fun
			# fun_defs = {fun_defs & [from_index].fun_info.fi_is_macro_fun=is_macro_fun}
			= addLocalFunctionDefsToSymbolTable level (inc from_index) to_index is_macro_fun fun_defs symbol_table error
			= addLocalFunctionDefsToSymbolTable level (inc from_index) to_index is_macro_fun fun_defs symbol_table error

NewEntry symbol_table symb_ptr def_kind def_index level previous :==
	 symbol_table <:= (symb_ptr,{  ste_kind = def_kind, ste_index = def_index, ste_def_level = level, ste_previous = previous })

addDefToSymbolTable :: !Level !Index !Ident !STE_Kind !*SymbolTable !*ErrorAdmin -> (!* SymbolTable, !*ErrorAdmin)
addDefToSymbolTable level def_index def_ident=:{id_info} def_kind symbol_table error
	#! entry = sreadPtr id_info symbol_table
	| entry.ste_kind == STE_Empty || entry.ste_def_level <> level
		# entry = {ste_index = def_index, ste_kind = def_kind, ste_def_level = level, ste_previous = entry }
		= (symbol_table <:= (id_info,entry), error)
		= (symbol_table, checkError def_ident " already defined" error)

addDeclarationsOfDclModToSymbolTable :: .Int !{!Declaration} !{!Declaration} !*CheckState -> .CheckState;
addDeclarationsOfDclModToSymbolTable ste_index locals imported cs
	# cs=add_imports_in_array_to_symbol_table 0 imported cs
	= addLocalSymbolsForImportToSymbolTable 0 locals ste_index cs
  where
	add_imports_in_array_to_symbol_table symbol_index symbols cs=:{cs_x}
		| symbol_index<size symbols
			#! ({dcl_ident,dcl_pos,dcl_kind},symbols) = symbols![symbol_index]
			= case dcl_kind of
				STE_Imported def_kind def_mod
					#! dcl_index= symbols.[symbol_index].dcl_index
					   (_, cs)
					   		= addSymbol No dcl_ident dcl_pos dcl_kind
					   				def_kind dcl_index def_mod cUndef cs
					-> add_imports_in_array_to_symbol_table (symbol_index+1) symbols cs
				STE_FunctionOrMacro _
					#! dcl_index= symbols.[symbol_index].dcl_index
					   (_, cs)
					   		= addImportedFunctionOrMacro No dcl_ident dcl_index cs
					-> add_imports_in_array_to_symbol_table (symbol_index+1) symbols cs
			= cs

	addLocalSymbolsForImportToSymbolTable :: !Int !{!Declaration} Int !*CheckState -> .CheckState;
	addLocalSymbolsForImportToSymbolTable symbol_index symbols mod_index cs
		| symbol_index<size symbols
			# ({dcl_ident,dcl_pos,dcl_kind,dcl_index},symbols) = symbols![symbol_index]
			= case dcl_kind of
				STE_FunctionOrMacro _
					# (_, cs)
							= addImportedFunctionOrMacro No dcl_ident dcl_index cs
					-> addLocalSymbolsForImportToSymbolTable (symbol_index+1) symbols mod_index cs
				STE_Imported def_kind def_mod
					# (_, cs)
							= addSymbol No dcl_ident dcl_pos dcl_kind
									def_kind dcl_index mod_index cUndef cs
					-> addLocalSymbolsForImportToSymbolTable (symbol_index+1) symbols mod_index cs
			= cs
	
addImportedFunctionOrMacro :: !(Optional IndexRange) !Ident !Int !*CheckState -> (!Bool, !.CheckState)
addImportedFunctionOrMacro opt_dcl_macro_range ident=:{id_info} def_index cs=:{cs_symbol_table}
	#! entry = sreadPtr id_info cs_symbol_table
	= case entry.ste_kind of
		STE_Empty
			-> (True, { cs & cs_symbol_table = NewEntry cs.cs_symbol_table id_info (STE_FunctionOrMacro []) 
													def_index cModuleScope entry})
		STE_FunctionOrMacro _
			| entry.ste_index == def_index || within_opt_range opt_dcl_macro_range def_index
				-> (False, cs)
		_
			-> (False, { cs & cs_error = checkError ident "multiply defined" cs.cs_error})
  where
	within_opt_range (Yes {ir_from, ir_to}) i
		= ir_from<=i && i<ir_to
	within_opt_range No _
		= False


addFieldToSelectorDefinition :: !Ident (Global .Int) !*CheckState -> .CheckState;
addFieldToSelectorDefinition {id_info} glob_field_index cs=:{cs_symbol_table}
	# (entry, cs_symbol_table) = readPtr id_info cs_symbol_table 
	  cs = { cs & cs_symbol_table = cs_symbol_table }
	= case entry.ste_kind of
		STE_Selector selector_list
			-> { cs & cs_symbol_table = cs.cs_symbol_table <:= (id_info, { entry & ste_kind = STE_Selector [ glob_field_index : selector_list ] })}
		_
			-> { cs & cs_symbol_table = NewEntry cs.cs_symbol_table id_info (STE_Selector [glob_field_index]) NoIndex cModuleScope entry }

addSymbol :: !(Optional a) !Ident !Position !STE_Kind !STE_Kind !.Int !.Int !Int !*CheckState -> (!Bool, !.CheckState)
addSymbol yes_for_icl_module ident pos dcl_kind def_kind def_index def_mod importing_mod cs=:{cs_symbol_table}
	# (entry, cs_symbol_table) = readPtr ident.id_info cs_symbol_table
	= add_indirectly_imported_symbol yes_for_icl_module entry ident pos def_kind def_index def_mod 
			importing_mod { cs & cs_symbol_table = cs_symbol_table }
	where
		add_indirectly_imported_symbol _ {ste_kind = STE_Empty} {id_info} _ def_kind def_index def_mod _ cs=:{cs_symbol_table}
			# (entry, cs_symbol_table) = readPtr id_info cs_symbol_table
			  cs = { cs & cs_symbol_table = NewEntry cs_symbol_table id_info dcl_kind def_index cModuleScope entry}
			= case def_kind of
				STE_Field selector_id
					-> (True, addFieldToSelectorDefinition selector_id	{ glob_module = def_mod, glob_object = def_index } cs)
				_
					-> (True, cs)
		add_indirectly_imported_symbol _ {ste_kind = STE_Imported kind mod_index, ste_index} _ _ def_kind def_index def_mod _ cs
			| kind == def_kind && mod_index == def_mod && ste_index == def_index
				= (False, cs)
		add_indirectly_imported_symbol (Yes _) _ _ _ def_kind def_index def_mod _ cs
			| def_mod == cs.cs_x.x_main_dcl_module_n
				// an icl module imports one of it's definitions from the dcl module
				= (False, cs)
		add_indirectly_imported_symbol _ _ _ _ def_kind def_index def_mod importing_mod cs
			| importing_mod==def_mod // a dcl module imports a definition from itself (cycle)
				= (False, cs)
		add_indirectly_imported_symbol _ entry ident pos def_kind def_index def_mod _ cs=:{cs_error}
			= (False, { cs & cs_error = checkError ident "multiply defined" cs_error})

addGlobalDefinitionsToSymbolTable :: ![Declaration] !*CheckState -> .CheckState;
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
			= { cs & cs_error = checkErrorWithIdentPos (newPosition ident dcl_pos) " multiply defined" cs.cs_error}

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

removeDeclarationsFromSymbolTable :: ![Declaration] !Int !*SymbolTable -> *SymbolTable
removeDeclarationsFromSymbolTable decls scope symbol_table
	= foldSt (remove_declaration scope) decls symbol_table
where
	remove_declaration scope decl=:{dcl_ident={id_info}, dcl_index} symbol_table
		# ({ste_kind,ste_previous}, symbol_table)
				= readPtr id_info symbol_table
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

removeLocalsFromSymbolTable :: !Level ![Ident] !LocalDefs !u:{# FunDef} !*(Heap SymbolTableEntry)
			-> (!u:{# FunDef}, !.Heap SymbolTableEntry)
removeLocalsFromSymbolTable level loc_vars (CollectedLocalDefs {loc_functions={ir_from,ir_to}}) defs symbol_table
	= remove_defs_from_symbol_table level ir_from ir_to defs (removeLocalIdentsFromSymbolTable level loc_vars symbol_table)
where
	remove_defs_from_symbol_table level from_index to_index defs symbol_table
		| from_index == to_index
			= (defs, symbol_table)	
			#! def = defs.[from_index]
			   id_info = (toIdent def).id_info
			   entry = sreadPtr id_info symbol_table
			| level == entry.ste_def_level
				= remove_defs_from_symbol_table level (inc from_index) to_index defs (symbol_table <:= (id_info, entry.ste_previous))
				= remove_defs_from_symbol_table level (inc from_index) to_index defs symbol_table


newFreeVariable :: !FreeVar ![FreeVar] ->(!Bool, ![FreeVar])
newFreeVariable new_var vars=:[free_var=:{fv_def_level,fv_info_ptr}: free_vars]
	| new_var.fv_def_level > fv_def_level
		= (True, [new_var : vars])
	| new_var.fv_def_level == fv_def_level
		| new_var.fv_info_ptr == fv_info_ptr
			= (False, vars)
			#! (free_var_added, free_vars) = newFreeVariable new_var free_vars
			= (free_var_added, [free_var : free_vars])
		#! (free_var_added, free_vars) = newFreeVariable new_var free_vars
		= (free_var_added, [free_var : free_vars])
newFreeVariable new_var []
	= (True, [new_var])


local_declaration_for_import :: !u:Declaration .Index -> v:Declaration, [u <= v]
local_declaration_for_import decl=:{dcl_kind=STE_FunctionOrMacro _} module_n
	= decl
local_declaration_for_import decl=:{dcl_kind=STE_Imported _ _} module_n
	= abort "local_declaration_for_import"
local_declaration_for_import decl=:{dcl_kind} module_n
	= {decl & dcl_kind = STE_Imported dcl_kind module_n}

	
get_ident :: !ImportDeclaration -> Ident
get_ident (ID_Function {ii_ident})						= ii_ident
get_ident (ID_Class {ii_ident} _)						= ii_ident
get_ident (ID_Type {ii_ident} _)						= ii_ident
get_ident (ID_Record {ii_ident} _)						= ii_ident
get_ident (ID_Instance class_ident instance_ident _)	= instance_ident

getBelongingSymbolsFromID :: !ImportDeclaration -> Optional [ImportedIdent]
getBelongingSymbolsFromID (ID_Class _ x)						= x
getBelongingSymbolsFromID (ID_Type _ x)						= x
getBelongingSymbolsFromID (ID_Record _ x)						= x
getBelongingSymbolsFromID _									= No

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
	

instance <<< ExplImpInfo
  where
	(<<<) file (ExplImpInfo eii_ident eii_declaring_modules)
		= file <<< eii_ident //<<< " is declared in " <<< eii_declaring_modules

instance <<< DeclarationInfo
  where
	(<<<) file {di_decl, di_instances}
		= file <<< di_decl <<< di_instances
		
import_ident :: Ident
import_ident =: { id_name = "import", id_info = nilPtr }

restoreHeap :: !Ident !*SymbolTable -> .SymbolTable
restoreHeap {id_info} cs_symbol_table
	# ({ste_previous}, cs_symbol_table)
			= readPtr id_info cs_symbol_table
	= writePtr id_info ste_previous cs_symbol_table

expand_syn_types_late_XXX yes no :== no
