definition module checksupport

import StdEnv
import syntax, predef, containers, utilities

CS_NotChecked 	:== -1
NotFound		:== -1

cModuleScope	:== 0
cGlobalScope	:== 1

cIsNotADclModule 	:== False
cIsADclModule 		:== True

cNeedStdArray	:== 1
cNeedStdEnum	:== 2
cNeedStdDynamics:== 4
cNeedStdGeneric	:== 8 // AA

::	VarHeap :== Heap VarInfo

::	Heaps =
	{	hp_var_heap			::!.VarHeap
	,	hp_expression_heap	::!.ExpressionHeap
	,	hp_type_heaps		::!.TypeHeaps
	}

::	ErrorAdmin = { ea_file :: !.File, ea_loc :: ![IdentPos], ea_ok :: !Bool }

::	CheckState = { cs_symbol_table :: !.SymbolTable, cs_predef_symbols :: !.PredefinedSymbols, cs_error :: !.ErrorAdmin,cs_x :: !CheckStateX }

::	CheckStateX = {x_needed_modules :: !BITVECT,x_main_dcl_module_n :: !Int /* TD */, x_is_dcl_module :: !Bool, x_type_var_position :: !Int }

//	SymbolTable			:== {# SymbolTableEntry}

instance == STE_Kind

::	ConversionTable		:== {# .{# Int }}

cTypeDefs				:== 0
cConstructorDefs		:== 1
cSelectorDefs			:== 2
cClassDefs				:== 3
cMemberDefs				:== 4
cGenericDefs			:== 5 // AA
cInstanceDefs			:== 6
cFunctionDefs			:== 7
cMacroDefs				:== 8

cConversionTableSize	:== 9 // AA

::	CommonDefs =
	{	com_type_defs 		:: !.{# CheckedTypeDef}
	
	,	com_unexpanded_type_defs :: !{# CheckedTypeDef}
	
	,	com_cons_defs		:: !.{# ConsDef}
	,	com_selector_defs	:: !.{# SelectorDef}
	,	com_class_defs		:: !.{# ClassDef}
	,	com_member_defs		:: !.{# MemberDef}
	,	com_instance_defs	:: !.{# ClassInstance}
//	,	com_instance_types	:: !.{ SymbolType}
	,	com_generic_defs	:: !.{# GenericDef} // AA
	}

::	Declarations = {
		dcls_import	::!{!Declaration}
	,	dcls_local		::![Declaration]
	,	dcls_local_for_import ::!{!Declaration}
	}

::	*ExplImpInfos :== *{!*{!*ExplImpInfo}}

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
	{	icl_name				:: !Ident
	,	icl_functions			:: !.{# FunDef }
	,	icl_instances			:: !IndexRange
	,	icl_specials			:: !IndexRange
	,	icl_common				:: !.CommonDefs
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
	,	dcl_specials		:: !IndexRange
	,	dcl_common			:: !CommonDefs
	,	dcl_sizes			:: !{# Int}
	,	dcl_declared		:: !Declarations
	,	dcl_conversions		:: !Optional ConversionTable
	,	dcl_is_system		:: !Bool
	,	dcl_imported_module_numbers :: !NumberSet
	,	dcl_is_cashed		:: !Bool
	}

class Erroradmin state
where
	pushErrorAdmin :: !IdentPos *state -> *state
	setErrorAdmin :: !IdentPos *state -> *state
	popErrorAdmin  :: *state -> *state

instance Erroradmin ErrorAdmin, CheckState

newPosition :: !Ident !Position -> IdentPos 

checkError :: !a !b !*ErrorAdmin -> *ErrorAdmin | <<< a & <<< b
checkWarning :: !a !b !*ErrorAdmin -> *ErrorAdmin | <<< a & <<< b
checkErrorWithIdentPos :: !IdentPos !a !*ErrorAdmin -> .ErrorAdmin | <<< a;

class envLookUp a :: !a !(Env Ident .b) -> (!Bool,.b)

instance envLookUp TypeVar, AttributeVar, ATypeVar

class toIdent a :: !a -> Ident

instance toIdent ConsDef, (TypeDef a), ClassDef, MemberDef, FunDef, SelectorDef // , ClassInstance
instance toIdent SymbIdent, TypeSymbIdent, BoundVar, TypeVar, ATypeVar, Ident

instance toInt STE_Kind
instance <<< IdentPos, ExplImpInfo, DeclarationInfo

::	ExpressionInfo =
	{	ef_type_defs		:: !.{# CheckedTypeDef}
	,	ef_selector_defs	:: !.{# SelectorDef}
	,	ef_cons_defs		:: !.{# ConsDef}
	,	ef_member_defs		:: !.{# MemberDef}
	,	ef_class_defs		:: !.{# ClassDef}
	,	ef_generic_defs		:: !.{# GenericDef} // AA
	,	ef_modules			:: !.{# DclModule}
	,	ef_is_macro_fun		:: !Bool
	}

checkLocalFunctions :: !Index !Level !LocalDefs !*{#FunDef} !*ExpressionInfo !*Heaps !*CheckState
					-> (!.{#FunDef},!.ExpressionInfo,!.Heaps,!.CheckState);

convertIndex :: !Index !Index !(Optional ConversionTable) -> !Index

retrieveGlobalDefinition :: !SymbolTableEntry !STE_Kind !Index -> (!Index, !Index)
//retrieveAndRemoveImportsFromSymbolTable :: !Index  ![(.a,.Declarations)] !Int ![Declaration] !*ExplImpInfos !*(Heap SymbolTableEntry)
//		-> (!Int, ![Declaration], !.ExplImpInfos, !.Heap SymbolTableEntry);
addLocalFunctionDefsToSymbolTable :: !Level !Index !Index !Bool !*{#FunDef} !*SymbolTable !*ErrorAdmin -> (!*{# FunDef}, !*SymbolTable, !*ErrorAdmin)
addDefToSymbolTable :: !Level !Index !Ident !STE_Kind !*SymbolTable !*ErrorAdmin -> (!* SymbolTable, !*ErrorAdmin)
addDeclarationsOfDclModToSymbolTable :: .Int !{!Declaration} !{!Declaration} !*CheckState -> .CheckState;
addGlobalDefinitionsToSymbolTable :: ![Declaration] !*CheckState -> .CheckState;
addSymbol :: !(Optional a) !Ident !Position !STE_Kind !STE_Kind !.Int !.Int !Int !*CheckState -> (!Bool, !.CheckState)
addImportedFunctionOrMacro :: !(Optional IndexRange) !Ident !Int !*CheckState -> (!Bool, !.CheckState)
removeImportedSymbolsFromSymbolTable :: Declaration !*SymbolTable -> .SymbolTable
removeFieldFromSelectorDefinition :: !Ident .Int .Int !*(Heap SymbolTableEntry) -> .Heap SymbolTableEntry;
removeDeclarationsFromSymbolTable :: ![Declaration] !Int !*SymbolTable -> *SymbolTable
removeLocalIdentsFromSymbolTable :: .Int !.[Ident] !*(Heap SymbolTableEntry) -> .Heap SymbolTableEntry;
removeIdentFromSymbolTable :: !.Int !Ident !*(Heap SymbolTableEntry) -> .Heap SymbolTableEntry;
removeImportsAndLocalsOfModuleFromSymbolTable :: !Declarations !*(Heap SymbolTableEntry) -> .Heap SymbolTableEntry
removeLocalsFromSymbolTable :: !Level ![Ident] !LocalDefs !u:{# FunDef} !*(Heap SymbolTableEntry)
			-> (!u:{# FunDef}, !.Heap SymbolTableEntry)

newFreeVariable :: !FreeVar ![FreeVar] ->(!Bool, ![FreeVar])

local_declaration_for_import :: !u:Declaration .Index -> v:Declaration, [u <= v]

get_ident :: !ImportDeclaration -> Ident
getBelongingSymbolsFromID :: !ImportDeclaration -> Optional [ImportedIdent]

:: BelongingSymbols
	=	BS_Constructors ![DefinedSymbol]
	|	BS_Fields !{#FieldSymbol}
	|	BS_Members !{#DefinedSymbol}
	|	BS_Nothing

getBelongingSymbols :: !Declaration !v:{#DclModule} -> (!BelongingSymbols, !v:{#DclModule})
nrOfBelongingSymbols :: !BelongingSymbols -> Int

import_ident :: Ident
restoreHeap :: !Ident !*SymbolTable -> .SymbolTable
