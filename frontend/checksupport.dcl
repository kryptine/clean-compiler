definition module checksupport

import StdEnv
import syntax, predef

//cIclModIndex 	:== 0

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

::	VarHeap :== Heap VarInfo

::	Heaps =
	{	hp_var_heap			::!.VarHeap
	,	hp_expression_heap	::!.ExpressionHeap
	,	hp_type_heaps		::!.TypeHeaps
	}

::	ErrorAdmin = { ea_file :: !.File, ea_loc :: ![IdentPos], ea_ok :: !Bool }

::	CheckState = { cs_symbol_table :: !.SymbolTable, cs_predef_symbols :: !.PredefinedSymbols, cs_error :: !.ErrorAdmin,cs_x :: !CheckStateX }

::	CheckStateX = {x_needed_modules :: !BITVECT,x_main_dcl_module_n :: !Int }

//	SymbolTable			:== {# SymbolTableEntry}

instance == STE_Kind

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

::	CommonDefs =
	{	com_type_defs 		:: !.{# CheckedTypeDef}
	,	com_cons_defs		:: !.{# ConsDef}
	,	com_selector_defs	:: !.{# SelectorDef}
	,	com_class_defs		:: !.{# ClassDef}
	,	com_member_defs		:: !.{# MemberDef}
	,	com_instance_defs	:: !.{# ClassInstance}
//	,	com_instance_types	:: !.{ SymbolType}
	}

::	Declaration =
	{	dcl_ident	:: !Ident
	,	dcl_pos		:: !Position
	,	dcl_kind	:: !STE_Kind
	,	dcl_index	:: !Index
	}

::	Declarations = {
		dcls_import	::!{!Declaration}
	,	dcls_local		::![Declaration]
	,	dcls_local_for_import ::!{!Declaration}
	,	dcls_explicit	::!{!ExplicitImport}
	}

:: ExplicitImport = ExplicitImport !Declaration !LineNr;

::	IclModule  =
	{	icl_name				:: !Ident
	,	icl_functions			:: !.{# FunDef }
	,	icl_instances			:: !IndexRange
	,	icl_specials			:: !IndexRange
	,	icl_common				:: !.CommonDefs
//	,	icl_declared		:: !Declarations
	,	icl_import		:: !{!Declaration}
	,	icl_imported_objects	:: ![ImportedObject]
	,	icl_used_module_numbers :: !ModuleNumberSet
	}

:: ModuleNumberSet = ModuleNumbers !Int !ModuleNumberSet | EndModuleNumbers;

in_module_number_set :: !Int !ModuleNumberSet -> Bool

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

class Erroradmin state
where
	pushErrorAdmin :: !IdentPos *state -> *state
	setErrorAdmin :: !IdentPos *state -> *state
	popErrorAdmin  :: *state -> *state

instance Erroradmin ErrorAdmin, CheckState

newPosition :: !Ident  !Position -> IdentPos 

checkError :: !a !b !*ErrorAdmin -> *ErrorAdmin | <<< a & <<< b
checkWarning :: !a !b !*ErrorAdmin -> *ErrorAdmin | <<< a & <<< b
checkErrorWithIdentPos :: !IdentPos !a !*ErrorAdmin -> .ErrorAdmin | <<< a;

class envLookUp a :: !a !(Env Ident .b) -> (!Bool,.b)

instance envLookUp TypeVar, AttributeVar, ATypeVar

class toIdent a :: !a -> Ident

instance toIdent ConsDef, (TypeDef a), ClassDef, MemberDef, FunDef, SelectorDef // , ClassInstance
instance toIdent SymbIdent, TypeSymbIdent, BoundVar, TypeVar, ATypeVar, Ident

instance toInt STE_Kind
instance <<< STE_Kind, IdentPos, Declaration

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

convertIndex :: !Index !Index !(Optional ConversionTable) -> !Index

retrieveGlobalDefinition :: !SymbolTableEntry !STE_Kind !Index -> (!Index, !Index)
retrieveAndRemoveImportsFromSymbolTable :: ![(.a,.Declarations)] [Declaration] *(Heap SymbolTableEntry) -> ([Declaration],.Heap SymbolTableEntry);
addLocalFunctionDefsToSymbolTable :: !Level !Index !Index !Bool !*{#FunDef} !*SymbolTable !*ErrorAdmin -> (!*{# FunDef}, !*SymbolTable, !*ErrorAdmin)
addDefToSymbolTable :: !Level !Index !Ident !STE_Kind !*SymbolTable !*ErrorAdmin -> (!* SymbolTable, !*ErrorAdmin)
addDeclaredSymbolsToSymbolTable :: .Bool .Int ![.Declaration] !{!.Declaration} !*CheckState -> .CheckState;
addDeclaredSymbolsToSymbolTable2 :: .Bool .Int !{!.Declaration} !{!.Declaration} !*CheckState -> .CheckState;
addFieldToSelectorDefinition :: !Ident (Global .Int) !*CheckState -> .CheckState;
addGlobalDefinitionsToSymbolTable :: ![.Declaration] !*CheckState -> .CheckState;
retrieveImportsFromSymbolTable :: ![Import ImportDeclaration] ![Declaration] !*{#DclModule} !*(Heap SymbolTableEntry) -> *(![Declaration],!*{#DclModule},!*Heap SymbolTableEntry);
removeFieldFromSelectorDefinition :: !Ident .Int .Int !*(Heap SymbolTableEntry) -> .Heap SymbolTableEntry;
removeDeclarationsFromSymbolTable :: ![Declaration] !Int !*(Heap SymbolTableEntry) -> *Heap SymbolTableEntry;
removeLocalIdentsFromSymbolTable :: .Int !.[Ident] !*(Heap SymbolTableEntry) -> .Heap SymbolTableEntry;
removeIdentFromSymbolTable :: !.Int !Ident !*(Heap SymbolTableEntry) -> .Heap SymbolTableEntry;
removeImportsAndLocalsOfModuleFromSymbolTable :: !Declarations !*(Heap SymbolTableEntry) -> .Heap SymbolTableEntry
removeLocalsFromSymbolTable :: !Level ![Ident] !LocalDefs !u:{# FunDef} !*(Heap SymbolTableEntry)
			-> (!u:{# FunDef}, !.Heap SymbolTableEntry)

newFreeVariable :: !FreeVar ![FreeVar] ->(!Bool, ![FreeVar])
