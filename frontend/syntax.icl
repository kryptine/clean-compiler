implementation module syntax

import StdEnv, compare_constructor // ,RWSDebug

import scanner, general, Heap, typeproperties, utilities, compilerSwitches

::	Ident =
	{ 	id_name		:: !String
	,	id_info 	:: !SymbolPtr
	}

instance toString Ident
where toString {id_name} = id_name

instance toString (Import from_symbol)
where toString {import_module} = toString import_module


/*	Each Identifier is equipped with a pointer to a SymbolTableEntry that is
	used for binding the identifier with its definition.
*/

::	SymbolTable			:== Heap SymbolTableEntry
::	SymbolPtr 			:== Ptr SymbolTableEntry

::	SymbolTableEntry = 
	{	ste_kind		:: !STE_Kind
	,	ste_index		:: !Index
	,	ste_def_level	:: !Level
	,	ste_previous	:: SymbolTableEntry
	}

:: FunctionOrMacroIndex = FunctionOrIclMacroIndex !Int | DclMacroIndex /*module_n*/ !Int /*macro_n_in_module*/ !Int;

instance == FunctionOrMacroIndex
	where
		(==) (FunctionOrIclMacroIndex f1) (FunctionOrIclMacroIndex f2) = f1==f2
		(==) (DclMacroIndex m1 f1) (DclMacroIndex m2 f2) = m1==m2 && f1==f2
		(==) _ _ = False

::	STE_BoundTypeVariable	= { stv_count :: !Int, stv_attribute :: !TypeAttribute, stv_info_ptr :: !TypeVarInfoPtr }

::	STE_Kind	= STE_FunctionOrMacro ![FunctionOrMacroIndex]
				| STE_DclMacroOrLocalMacroFunction ![FunctionOrMacroIndex]
				| STE_Type
				| STE_Constructor
				| STE_Selector ![Global Index]
				| STE_Field !Ident
				| STE_Class
				| STE_Member
				| STE_Generic			// AA
				| STE_GenericCase   // AA
				| STE_Instance !Ident // the class (for explicit imports (1.3 syntax only))
				| STE_Variable !VarInfoPtr
				| STE_TypeVariable !TypeVarInfoPtr
				| STE_TypeAttribute !AttrVarInfoPtr
				| STE_BoundTypeVariable !STE_BoundTypeVariable
				| STE_Imported !STE_Kind !Index
				| STE_DclFunction
				| STE_Module !(Module (CollectedDefinitions ClassInstance IndexRange))
				| STE_ClosedModule
				| STE_Empty 
				| STE_DictType !CheckedTypeDef
				| STE_DictCons !ConsDef
				| STE_DictField !SelectorDef
				| STE_Called ![FunctionOrMacroIndex] /* used during macro expansion to indicate that this function is called */
				| STE_ExplImpSymbol !Int
				| STE_ExplImpComponentNrs ![ComponentNrAndIndex] ![Declaration]
				| STE_BelongingSymbol !Int
				| STE_UsedType !Index !STE_Kind
				| STE_BelongingSymbolExported
				| STE_BelongingSymbolForExportedSymbol

::	Declaration = Declaration !DeclarationRecord

::	DeclarationRecord =
	{	decl_ident	:: !Ident
	,	decl_pos	:: !Position
	,	decl_kind	:: !STE_Kind
	,	decl_index	:: !Index
	}

::	ComponentNrAndIndex =
	{	cai_component_nr	:: !Int
	,	cai_index			:: !Int
	}

::	Global object =
	{	glob_object	:: !object
	,	glob_module	:: !Index
	}
	
::	Module defs = 
	{	mod_name		:: !Ident
	,	mod_modification_time	:: {#Char}
	,	mod_type		:: !ModuleKind
	, 	mod_imports		:: ![ParsedImport]
	,	mod_imported_objects :: ![ImportedObject]
	,	mod_defs		:: !defs
	}

::	ParsedModule	:== Module  [ParsedDefinition]
::	ScannedModule 	:== Module  (CollectedDefinitions (ParsedInstance FunDef) IndexRange)

::	ModuleKind	= MK_Main | MK_Module | MK_System | MK_None | MK_NoMainDcl

::	RhsDefsOfType	= ConsList ![ParsedConstructor]
					| SelectorList !Ident ![ATypeVar] ![ParsedSelector]
					| TypeSpec !AType
					| EmptyRhs !BITVECT

::	CollectedDefinitions instance_kind def_macros =
	{	def_types 			:: ![TypeDef TypeRhs]
	,	def_constructors	:: ![ConsDef]
	,	def_selectors		:: ![SelectorDef]
	,	def_macros			:: ![FunDef]
	,	def_macro_indices	:: !IndexRange
	,	def_classes			:: ![ClassDef]
	,	def_members			:: ![MemberDef]
	,	def_funtypes		:: ![FunType]
	,	def_instances		:: ![instance_kind]
	,	def_generics		:: ![GenericDef] 		// AA
	, 	def_generic_cases 	:: ![GenericCaseDef]	// AA	
	}

::	LocalDefs = LocalParsedDefs [ParsedDefinition] | CollectedLocalDefs CollectedLocalDefs

::	IndexRange	= { ir_from :: !Index, ir_to :: !Index }

::	ArrayAndListInstances = {
		ali_array_first_instance_indices :: ![Int],
		ali_list_first_instance_indices :: ![Int],
		ali_tail_strict_list_first_instance_indices :: ![Int],
		ali_instances_range :: !IndexRange
	}

::  Index	:== Int
NoIndex		:== -1

::  Level	:== Int
NotALevel 	:==  -1

::	CollectedLocalDefs =
	{	loc_functions	:: !IndexRange
	,	loc_nodes		:: ![NodeDef ParsedExpr]
	,	loc_in_icl_module :: !Bool // False for local functions in macros in dcl modules, otherwise True
	}

::	NodeDef dst =
	{	nd_dst		::!dst,
		nd_alts		::!OptGuardedAlts,
		nd_locals	::!LocalDefs,
		nd_position	::!Position		
	}

::	Rhs =
	{	rhs_alts	:: !OptGuardedAlts
	,	rhs_locals	:: !LocalDefs
	}

cIsAFunction	:== True
cIsNotAFunction :== False

::	ParsedDefinition 
	=	PD_Function  Position Ident Bool [ParsedExpr] Rhs FunKind
	|	PD_NodeDef  Position ParsedExpr Rhs
	|	PD_Type ParsedTypeDef
	|	PD_TypeSpec Position Ident Priority (Optional SymbolType) Specials
	|	PD_Class ClassDef [ParsedDefinition]
	|	PD_Instance (ParsedInstance ParsedDefinition)
	|	PD_Instances [ParsedInstance ParsedDefinition]
	|	PD_Import [ParsedImport]
	|	PD_ImportedObjects [ImportedObject]
	|	PD_Generic GenericDef // AA
	| 	PD_GenericCase GenericCaseDef // AA	
	|	PD_Derive [GenericCaseDef] // AA
	|	PD_Erroneous

::	StrictnessList = NotStrict | Strict !Int | StrictList !Int StrictnessList

::	FunKind = FK_Function !Bool | FK_Macro | FK_Caf | FK_NodeDefOrFunction | FK_Unknown

cNameNotLocationDependent :== False
cNameLocationDependent :== True

::	ParsedSelector =
	{	ps_field_name		:: !Ident
	,	ps_selector_name	:: !Ident
	,	ps_field_annotation	:: !Annotation
	,	ps_field_type		:: !AType
	,	ps_field_var		:: !Ident
	,	ps_field_pos		:: !Position
	}

::	ParsedConstructor =
	{	pc_cons_name 	:: !Ident
	,	pc_cons_arity	:: !Int
	,	pc_exi_vars		:: ![ATypeVar]
	,	pc_arg_types	:: ![AType]
	,	pc_args_strictness	:: !StrictnessList
	,	pc_cons_prio	:: !Priority
	,	pc_cons_pos		:: !Position
	}
	
::	ParsedInstance member =
	{	pi_class 	:: !Ident
	,	pi_ident	:: !Ident
	,	pi_types	:: ![Type]
	,	pi_context	:: ![TypeContext]
	,	pi_pos		:: !Position
	,	pi_members	:: ![member]
	,	pi_specials	:: !Specials
	}


::	Specials
	= SP_ParsedSubstitutions 	![Env Type TypeVar]
	| SP_Substitutions 		 	![SpecialSubstitution]
	| SP_ContextTypes			![Special]
	| SP_FunIndex				!Index
	| SP_TypeOffset				!Int
	| SP_None

::	SpecialSubstitution =
	{	ss_environ	:: !Env Type TypeVar
	,	ss_context	:: ![TypeContext]
	,	ss_vars		:: ![TypeVar]
	,	ss_attrs	:: ![AttributeVar]
	}

::	Special =
	{	spec_index	:: !Global Index
	,	spec_types	:: ![[Type]]
	,	spec_vars	:: ![TypeVar]
	, 	spec_attrs	:: ![AttributeVar]
	}


::	AttrInequality =
	{	ai_demanded :: !AttributeVar
	,	ai_offered	:: !AttributeVar
	}

::	DefinedSymbol = 
	{	ds_ident		:: !Ident
	,	ds_arity		:: !Int
	,	ds_index		:: !Index
	}

::	ClassSymbIdent =
	{	cs_name		:: !Ident
	,	cs_arity 	:: !Int
	,	cs_index 	:: !Int
	}

::	ClassDef =
 	{	class_name			:: !Ident
	,	class_arity			:: !Int
	,	class_args			:: ![TypeVar]
	,	class_context		:: ![TypeContext]
	,	class_members		:: !{# DefinedSymbol}
	,	class_dictionary	:: !DefinedSymbol
	,	class_pos			:: !Position
	,	class_cons_vars		:: !BITVECT
	,	class_arg_kinds		:: ![TypeKind] // filled in in checkKindCorrectness phase
	}

::	ClassDefInfos :== {# .{! [TypeKind]}}

::	MemberDef =
	{	me_symb			:: !Ident
	,	me_class		:: !Global Index
	,	me_offset		:: !Index
	,	me_type			:: !SymbolType
	,	me_type_ptr		:: !VarInfoPtr
	,	me_class_vars	:: ![TypeVar]
	,	me_pos			:: !Position
	,	me_priority 	:: !Priority
	}

// AA.. 
::	GenericDef = 
	{	gen_name		:: !Ident		// the generics name in IC_Class 
	,	gen_member_name	:: !Ident		// the generics name in IC_Member
	, 	gen_pos			:: !Position
	,	gen_type		:: !SymbolType	// Generic type (st_vars include generic type vars)
	,	gen_vars		:: ![TypeVar]	// Generic type variables
	,	gen_info_ptr	:: !GenericInfoPtr
	}

:: GenericClassInfo = 
	{	gci_kind	:: !TypeKind	// the kind
	,	gci_module 	:: !Index		// filled with main_module_index
	,	gci_class	:: !Index		// class_index in the main module
	,	gci_member	:: !Index 		// the class member index 
	}
:: GenericClassInfos :== {[GenericClassInfo]}

:: GenericInfo = 
	{	gen_classes		:: !GenericClassInfos
	,	gen_cases		:: ![GlobalIndex]
	,	gen_var_kinds	:: ![TypeKind]  	// kinds of all st_vars of the gen_type
	, 	gen_star_case	:: !GlobalIndex 	// general case for kind-star types
	}
:: GenericInfoPtr :== Ptr GenericInfo	
:: GenericHeap :== Heap GenericInfo

:: TypeCons 
	= TypeConsSymb TypeSymbIdent
	| TypeConsBasic BasicType 
	| TypeConsArrow
	| TypeConsVar TypeVar 

:: GenericCaseDef = 
	{	gc_name			:: !Ident				// name in IC_GenricInstance namespace
	,	gc_gname		:: !Ident  				// name in IC_Generic namespace
	,	gc_generic		:: !GlobalIndex  		// index of the generic
	,	gc_arity		:: !Int					// number of value arguments
	,	gc_pos			:: !Position			// position in the source file
	,	gc_type			:: !Type				// the type argument
	,   gc_type_cons	:: !TypeCons			// type constructor of the type argument
	,	gc_body			:: !GenericCaseBody		// the body function or NoIndex
	,	gc_kind			:: !TypeKind			// kind of the instance type
	}
:: GenericCaseBody 
	= GCB_None 
	| GCB_FunIndex !Index 
	| GCB_FunDef !FunDef 
	| GCB_ParsedBody ![ParsedExpr] !Rhs 

:: GenericType = 
	{	gt_type 		:: !SymbolType
	,	gt_vars			:: ![TypeVar]			// generic arguments
	,	gt_arity		:: !Int					// number of generic arguments	
	}

/*
getGenericClassForKind 	:: !GenericDef !TypeKind -> (!Bool, DefinedSymbol)
getGenericClassForKind	{gen_classes} kind
	= get_class gen_classes kind
where
	get_class [] kind 
		= (False, undef)
	get_class [{gci_kind, gci_class}:gcis] kind
		| gci_kind == kind	= (True, gci_class)	 
		| otherwise			= get_class gcis kind
	
addGenericKind :: !GenericDef !TypeKind -> !GenericDef
addGenericKind generic_def=:{gen_name, gen_classes} kind 
	#(ok, _) = getGenericClassForKind generic_def kind
	| ok = generic_def
	# class_ds = 
		{	ds_ident = {id_name = gen_name.id_name +++ ":" +++ toString kind, id_info = nilPtr}
		, 	ds_index = NoIndex
		,	ds_arity = 1
		}
	= {generic_def & gen_classes = [{gci_kind = kind, gci_class = class_ds}:gen_classes]} 	
*/
// ..AA

::	InstanceType =
	{	it_vars			:: [TypeVar]
	,	it_types		:: ![Type]
	,	it_attr_vars	:: [AttributeVar]
	,	it_context		:: ![TypeContext]
	}

::	ClassInstance =
 	{	ins_class		:: !Global DefinedSymbol
	,	ins_ident		:: !Ident
	,	ins_type		:: !InstanceType
	,	ins_members		:: !{# DefinedSymbol}
	,	ins_specials	:: !Specials
	,	ins_pos			:: !Position
	}

::	Import from_symbol =
	{	import_module		:: !Ident
	,	import_symbols		:: ![from_symbol]
	,	import_file_position:: !Position	// for error messages
	}

::	ParsedImport		:== Import ImportDeclaration

::	ImportedIdent =
	{	ii_ident	:: !Ident
	,	ii_extended	:: !Bool
	}

::	ImportDeclaration	= ID_Function !ImportedIdent
						| ID_Class !ImportedIdent !(Optional [ImportedIdent])
						| ID_Type !ImportedIdent !(Optional [ImportedIdent])
						| ID_Record !ImportedIdent !(Optional [ImportedIdent])
						| ID_Instance !ImportedIdent !Ident !(![Type],![TypeContext])
						| ID_OldSyntax ![Ident]

cIsImportedLibrary :== True
cIsImportedObject :== False
:: ImportedObject =
	{	io_is_library :: !Bool
	,	io_name    :: !{#Char}
	}

::	RecordType =
	{	rt_constructor	:: !DefinedSymbol
	,	rt_fields		:: !{# FieldSymbol}
	}
	
::	FieldSymbol =
	{	fs_name			:: !Ident
	,	fs_var			:: !Ident
	,	fs_index		:: !Index
	}


::	TypeRhs	= AlgType ![DefinedSymbol]
			| SynType !AType
			| RecordType !RecordType
			| AbstractType !BITVECT
			| UnknownType

::	ParsedTypeDef :== TypeDef RhsDefsOfType
::	CheckedTypeDef :== TypeDef TypeRhs

cAllBitsClear			:== 0
cIsHyperStrict			:== 1
cIsNonCoercible			:== 2
cIsAnalysed				:== 4
cIsAbstractType			:== 8

::	GlobalIndex =
	{	gi_module	::!Int
	,	gi_index	::!Int
	}
NoGlobalIndex :== {gi_module=NoIndex,gi_index=NoIndex}	

instance == GlobalIndex
where
	(==) gi1 gi2 = gi1.gi_module == gi2.gi_module && gi1.gi_index == gi2.gi_index
	
::	TypeDef type_rhs =
 	{	td_name			:: !Ident
	,	td_index		:: !Int
	,	td_arity		:: !Int
	,	td_args			:: ![ATypeVar]
	,	td_attrs		:: ![AttributeVar]
	,	td_context		:: ![TypeContext]
	,	td_rhs			:: !type_rhs
	,	td_attribute	:: !TypeAttribute
	,	td_pos			:: !Position
	,	td_used_types	:: ![GlobalIndex]
	}

::	FunType =
	{	ft_symb			:: !Ident
	,	ft_arity		:: !Int
	,	ft_priority		:: !Priority
	,	ft_type			:: !SymbolType
	,	ft_pos			:: !Position
	,	ft_specials		:: !Specials
	,	ft_type_ptr		:: !VarInfoPtr
	}

::	FreeVar =
	{	fv_def_level	:: !Level
	,	fv_name			:: !Ident
	,	fv_info_ptr		:: !VarInfoPtr
	,	fv_count		:: !Int
	}
	
::	FunCall = FunCall !Index !Level | MacroCall !Index !Index Level;

/* Sjaak 19-3-2001 ... */

FI_IsMacroFun	:== 1			// whether the function is a local function of a macro
FI_HasTypeSpec	:== 2			// whether the function has u user defined type

::	FunInfo =
	{	fi_calls			:: ![FunCall]
	,	fi_group_index		:: !Index
	,	fi_def_level		:: !Level
	,	fi_free_vars		:: ![FreeVar]
	,	fi_local_vars		:: ![FreeVar]
	,	fi_dynamics			:: ![ExprInfoPtr]
	,	fi_properties		:: !BITVECT
	}
/* ... Sjaak 19-3-2001 */

::	ParsedBody =
	{	pb_args	:: ![ParsedExpr]
	,	pb_rhs	:: !Rhs
	,	pb_position	:: !Position
	}

::	CheckedBody =
	{	cb_args		:: ![FreeVar]
	,	cb_rhs		:: ![CheckedAlternative]
	}

::	CheckedAlternative =
	{	ca_rhs		:: !Expression
	,	ca_position	:: !Position	// the position is NoPos iff the position information for this
	}								// alternative is already stored in a case alternative
									// (in ap_position, bp_position or dp_position)

::	TransformedBody =
	{	tb_args			:: ![FreeVar]
	,	tb_rhs			:: !Expression
	}

::	FunctionBody	= ParsedBody ![ParsedBody]
					| CheckedBody !CheckedBody
	/* The next three constructors are used during macro expansion (module transform) */
					| PartitioningMacro
					| PartitioningFunction !CheckedBody !Int
					| RhsMacroBody !CheckedBody
	/* macro expansion the transforms a CheckedBody into a TransformedBody */
					| TransformedBody !TransformedBody
					| Expanding ![FreeVar] // the parameters of the newly generated function
					| BackendBody ![BackendBody]
					| GeneratedBody // the body will be generated automatically - for generics
					| NoBody
					
::	BackendBody =
	{	bb_args	:: ![FunctionPattern]
	,	bb_rhs	:: !Expression
	}

::	FunDef =
	{	fun_symb		:: !Ident
	,	fun_arity		:: !Int
	,	fun_priority	:: !Priority
	,	fun_body		:: !FunctionBody
	,	fun_type		:: !Optional SymbolType
	,	fun_pos			:: !Position
	,	fun_kind		:: !FunKind
	,	fun_lifted		:: !Int
	,	fun_info		:: !FunInfo
	}

cIsAGlobalVar	:== True
cIsALocalVar	:== False

::	ConsClasses =
	{	cc_size			::!Int
	,	cc_args			::![ConsClass]
	,	cc_linear_bits	::![Bool]
	,	cc_producer		::!ProdClass
	}
					
::	ConsClass	:== Int

::	ProdClass	:== Bool

pIsSafe			:== True

::	OptionalVariable :== Optional (Bind Ident VarInfoPtr)

:: 	AuxiliaryPattern
		= AP_Algebraic !(Global DefinedSymbol) !Index [AuxiliaryPattern] OptionalVariable
		| AP_Variable !Ident !VarInfoPtr OptionalVariable
		| AP_Basic !BasicValue OptionalVariable
		| AP_Dynamic !AuxiliaryPattern !DynamicType !OptionalVariable
		| AP_Constant !AP_Kind !(Global DefinedSymbol) !Priority
		| AP_WildCard !OptionalVariable
		| AP_Empty !Ident

:: AP_Kind = APK_Constructor !Index | APK_Macro !Bool // is_dcl_macro

::	VarInfo  =	VI_Empty | VI_Type !AType !(Optional CoercionPosition) | VI_FAType ![ATypeVar] !AType !(Optional CoercionPosition) |
				VI_Occurrence !Occurrence | VI_UsedVar !Ident |
				VI_Expression !Expression | VI_Variable !Ident !VarInfoPtr | VI_LiftedVariable !VarInfoPtr |
				VI_Count !Int /* the reference count of a variable */ !Bool /* true if the variable is global, false otherwise */ |
				VI_AccVar !ConsClass !ArgumentPosition /* used during fusion to determine accumulating parameters of functions */ |
				VI_Alias !BoundVar /* used for resolving aliases just before type checking (in transform) */ |
				 /* used during elimination and lifting of cases */
				VI_FreeVar !Ident !VarInfoPtr !Int !AType | VI_BoundVar !AType | VI_LocalVar |
				VI_ClassVar !Ident !VarInfoPtr !Int | /* to hold dictionary variables during overloading */
				VI_ForwardClassVar !VarInfoPtr | /* to hold the dictionary variable generated during overloading */
				VI_Forward !BoundVar | VI_LetVar !LetVarInfo | VI_LetExpression !LetExpressionInfo | VI_CaseVar !VarInfoPtr |
				VI_CorrespondenceNumber !Int | /* it is assumed that this alternative is _only_ used in module comparedefimp */
				VI_SequenceNumber !Int | VI_AliasSequenceNumber !BoundVar |
				VI_Used | /* for indicating that an imported function has been used */
				VI_PropagationType !SymbolType | /* for storing the type with propagation environment of an imported function */
				VI_ExpandedType !SymbolType | /* for storing the (expanded) type of an imported function */
				VI_Record ![AuxiliaryPattern] |
				VI_Pattern !AuxiliaryPattern |
				VI_Default !Int | VI_Indirection !Int | /* used during conversion of dynamics; the Int indiacted the refenrence count */
				VI_Body !SymbIdent !TransformedBody ![FreeVar] | /* used during fusion */
				VI_Dictionary !SymbIdent ![Expression] !Type | /* used during fusion */
				VI_Extended !ExtendedVarInfo !VarInfo |
				VI_Defined /* for marking type code variables during overloading */ | VI_LocallyDefined |
// MdM
				VI_CPSLocalExprVar !Int /* MdM - the index of the variable as generated by the theorem prover */
// ... MdM
				| VI_Labelled_Empty {#Char} // RWS debugging
				| VI_LocalLetVar // RWS, mark Let vars during case transformation

::	ExtendedVarInfo = EVI_VarType !AType

::	ArgumentPosition :== Int

::	VarInfoPtr	:== Ptr VarInfo

::	LetVarInfo =
	{	lvi_count		:: !Int
	,	lvi_depth		:: !Int
	,	lvi_new			:: !Bool
	,	lvi_var			:: !Ident
	,	lvi_expression	:: !Expression	
	,   lvi_previous	:: ![PreviousLetVarInfo]
	}

::	PreviousLetVarInfo =
	{	plvi_count		:: !Int
	,	plvi_depth		:: !Int
	,	plvi_new		:: !Bool
	}

::	LetExpressionStatus	= LES_Untouched | LES_Moved | LES_Updated !Expression

::	LetExpressionInfo =
	{	lei_count			:: !Int
	,	lei_depth			:: !Int 
	,	lei_var				:: !FreeVar 
	,   lei_expression		:: !Expression
	,   lei_status			:: !LetExpressionStatus
	,   lei_type			:: !AType
	}

cNotVarNumber :== -1

::	BoundVar = 
	{	var_name		:: !Ident
	,	var_info_ptr	:: !VarInfoPtr
	,	var_expr_ptr	:: !ExprInfoPtr
	}

::	TypeSymbIdent =
	{	type_name		:: !Ident
	,	type_arity		:: !Int
	,	type_index		:: !Global Index
	,	type_prop		:: !TypeSymbProperties
	}

::	TypeSymbProperties =
	{	tsp_sign		:: !SignClassification
	,	tsp_propagation	:: !PropClassification
	,	tsp_coercible	:: !Bool
	}

::	SymbKind	= SK_Unknown
				| SK_Function !(Global Index)
				| SK_IclMacro !Index
				| SK_LocalMacroFunction !Index
				| SK_DclMacro !(Global Index)
				| SK_LocalDclMacroFunction !(Global Index)
				| SK_OverloadedFunction !(Global Index)
				| SK_GeneratedFunction !FunctionInfoPtr !Index
				| SK_Constructor !(Global Index)
				| SK_Generic !(Global Index) !TypeKind
				| SK_TypeCode

// MW2 moved some type definitions

/*	Some auxiliary type definitions used during fusion. Actually, these definitions
	should have beengiven in seperate module. Unfortunately, Clean's module system
	forbids cyclic dependencies between def modules.
	
*/

::	FunctionHeap 	:== Heap FunctionInfo

::	FunctionInfoPtr	:== Ptr FunctionInfo

::	FunctionInfo	= FI_Empty | FI_Function !GeneratedFunction

::	Producer	= PR_Empty
				| PR_Function !SymbIdent !Int !Index
				| PR_Class !App ![(BoundVar, Type)] !Type
				| PR_Constructor !SymbIdent !Int ![Expression]
				| PR_GeneratedFunction !SymbIdent !Int !Index
				| PR_Curried !SymbIdent !Int

::	InstanceInfo = II_Empty | II_Node !{! Producer} !FunctionInfoPtr !InstanceInfo !InstanceInfo

::	GeneratedFunction = 
	{	gf_fun_def			:: !FunDef
	,	gf_instance_info	:: !InstanceInfo
	,	gf_cons_args		:: !ConsClasses
	,	gf_fun_index		:: !Index
	}
	
/*	... main type definitions continued .... */

::	ExpressionHeap 	:== Heap ExprInfo

::	ExprInfoPtr		:== Ptr ExprInfo

::	TempLocalVar	:== Int

::	DynamicPtr		:== ExprInfoPtr

::	ExprInfo		= EI_Empty

		/* For handling overloading */

					| EI_Overloaded !OverloadedCall 						/* initial, set by the type checker */
					| EI_Instance 	!(Global DefinedSymbol) ![Expression]	/* intermedediate, used during resolving of overloading */ 
					| EI_Selection 	![Selection] !VarInfoPtr ![Expression]	/* intermedediate, used during resolving of overloading */
					| EI_Context 	![Expression]							/* intermedediate, used during resolving of overloading */

		/* For handling dynamics */

					| EI_UnmarkedDynamic 		!(Optional DynamicType) ![DynamicPtr]
					| EI_Dynamic 				!(Optional DynamicType) ![DynamicPtr]
					| EI_DynamicType			!DynamicType ![DynamicPtr]

		/* Auxiliary, was EI_DynamicType before checking */

					| EI_DynamicTypeWithVars	![TypeVar] !DynamicType ![DynamicPtr]				

		/* Auxiliary, used during type checking */

					| EI_TempDynamicType 		!(Optional DynamicType) ![DynamicPtr] !AType ![TypeContext] !ExprInfoPtr !SymbIdent
					| EI_TempDynamicPattern 	![TypeVar] !DynamicType ![DynamicPtr] ![TempLocalVar] !AType ![TypeContext] !ExprInfoPtr !SymbIdent
					
					| EI_TypeOfDynamic 			![VarInfoPtr] !TypeCodeExpression				/* Final */
					| EI_TypeOfDynamicPattern 	![VarInfoPtr] !TypeCodeExpression				/* Final */

					| EI_TypeCode 		!TypeCodeExpression
					| EI_TypeCodes 		![TypeCodeExpression]

					| EI_Attribute !Int


		/*	EI_FreeVariables is uded to store the (free) variables occurring in the case expression */

//					| EI_FreeVariables ![UnboundVariable] !ExprInfo

		/* EI_ClassTypes is used to store the instance types of a class These type are used during fusion to generate proper types for 
		   the fusion result (i.e. the resulting function after elimination of dictionaries) */

					| EI_DictionaryType !Type
					| EI_CaseType !CaseType
					| EI_LetType ![AType]
					| EI_CaseTypeAndRefCounts !CaseType !RefCountsInCase
					| EI_LetTypeAndRefCounts ![AType] ![Int]

		/* for converting case into function patterns the following auxiliary constuctors are used */

					| EI_Default !Expression !AType !ExprInfoPtr
					| EI_DefaultFunction !SymbIdent ![Expression]
					| EI_Extended !ExtendedExprInfo !ExprInfo

::	ExtendedExprInfo
					= EEI_ActiveCase !ActiveCaseInfo

::	ActiveCaseInfo =
	{	aci_params					:: ![FreeVar]
	,	aci_opt_unfolder			:: !(Optional SymbIdent)
	,	aci_free_vars				:: !Optional [BoundVar]
	,	aci_linearity_of_patterns	:: ![[Bool]]
	}

::	RefCountsInCase = 
	{	rcc_all_variables		:: ![CountedVariable]
	,	rcc_default_variables	:: ![CountedVariable]
	,	rcc_pattern_variables	:: ![[CountedVariable]]
	}

::	CountedVariable =
	{	cv_variable	:: !VarInfoPtr
	,	cv_count	:: !Int
	}


/*
	OverloadedCall contains (type) information about functions that are overloaded. This structure is built during type checking
	and used after (standard) unification to insert the proper instances of the corresponding functions.

*/

::	OverloadedCall = 
	{	oc_symbol	:: !SymbIdent
	,	oc_context	:: ![TypeContext]
	,	oc_specials	:: ![Special]
	}

/*
	CaseType contains the type information needed to type the corresponding case construct:
		ct_pattern_type : the type of the pattern
		ct_result_type  : the type of the result (of each pattern)
		ct_cons_types   : the types of the arguments of each pattern constructor
*/
		
::	CaseType =
	{	ct_pattern_type	:: !AType
	,	ct_result_type	:: !AType
	,	ct_cons_types 	:: ![[AType]]
	}
		

::	SymbIdent =
	{	symb_name		:: !Ident
	,	symb_kind		:: !SymbKind
	}

::	ConsDef =
	{	cons_symb			:: !Ident
	,	cons_type			:: !SymbolType
	,	cons_arg_vars		:: ![[ATypeVar]]
	,	cons_priority		:: !Priority
	,	cons_index			:: !Index
	,	cons_type_index		:: !Index
	,	cons_exi_vars		:: ![ATypeVar]
//	,	cons_exi_attrs		:: ![AttributeVar]
	,	cons_type_ptr		:: !VarInfoPtr
	,	cons_pos			:: !Position
	}

::	SelectorDef =
	{	sd_symb			:: !Ident
	,	sd_field		:: !Ident
	,	sd_type			:: !SymbolType
	,	sd_exi_vars		:: ![ATypeVar]
//	,	sd_exi_attrs	:: ![AttributeVar]
	,	sd_field_nr		:: !Int
	,	sd_type_index	:: !Int
	,	sd_type_ptr		:: !VarInfoPtr
	,	sd_pos			:: !Position
	}

::	SymbolType =
	{	st_vars			:: ![TypeVar]
	,	st_args			:: ![AType]
	,	st_args_strictness :: !StrictnessList
	,	st_arity		:: !Int
	,	st_result		:: !AType
	,	st_context		:: ![TypeContext]
	,	st_attr_vars	:: ![AttributeVar]
	,	st_attr_env		:: ![AttrInequality]
	}

::	TypeContext =
	{	tc_class	:: !TCClass
	,	tc_types	:: ![Type]
	,	tc_var		:: !VarInfoPtr
	}

//AA: class in a type context is either normal class or a generic class
:: TCClass 	= TCClass 		!(Global DefinedSymbol) // Normal class
			| TCGeneric 	!GenericTypeContext		// Generic class

:: GenericTypeContext = 
	{ gtc_generic 	:: !(Global DefinedSymbol)
	, gtc_kind		:: !TypeKind 
	, gtc_class		:: !(Global DefinedSymbol) // generated class
	, gtc_dictionary:: !(Global DefinedSymbol) // HACK: dictionary different from the one contained in the class
	}
//..AA

::	AType =
	{	at_attribute	:: !TypeAttribute
	,	at_type			:: !Type
	}
	
::	TempAttrId		:== Int
::	TempVarId		:== Int

::	Type	=	TA !TypeSymbIdent ![AType]
			|	TAS !TypeSymbIdent ![AType] !StrictnessList
			|	(-->) infixr 9 !AType !AType
			| 	TArrow							/* (->) */
			| 	TArrow1	!AType					/* ((->) a) */
			|	(:@:) infixl 9 !ConsVariable ![AType]
			|	TB !BasicType

			|	TST [ATypeVar] SymbolType		/* Universally quantified types */

			| 	GTV !TypeVar
			| 	TV !TypeVar
			|	TempV !TempVarId				/* Auxiliary, used during type checking */

			
			|	TQV	TypeVar
			|	TempQV !TempVarId				/* Auxiliary, used during type checking */

			|	TLifted !TypeVar				/* Auxiliary, used during type checking of lifted arguments */

			|	TE

::	ConsVariable = CV 		!TypeVar
				 | TempCV 	!TempVarId
				 | TempQCV 	!TempVarId


::	DynamicType =
	{	dt_uni_vars 	:: ![ATypeVar]
	,	dt_global_vars	:: ![TypeVar]
	,	dt_type			:: !AType
	}

::	KindHeap	:== Heap KindInfo
::	KindInfoPtr	:== Ptr KindInfo

::	KindInfo	= KI_Var !KindInfoPtr
				| KI_Arrow !KindInfo !KindInfo
				| KI_Const
				
				| KI_ConsVar
				
				| KI_VarBind !KindInfoPtr
				| KI_NormVar !Int


::	TypeVarInfo  	= TVI_Empty
					| TVI_Type !Type
					| TVI_TypeVar !TypeVarInfoPtr // Sjaak: to collect universally quantified type variables
					| TVI_Forward !TempVarId | TVI_TypeKind !KindInfoPtr
					| TVI_SignClass !Index !SignClassification !TypeVarInfo | TVI_PropClass !Index !PropClassification !TypeVarInfo
					| TVI_Attribute TypeAttribute
					| TVI_CorrespondenceNumber !Int /* auxiliary used in module comparedefimp */
					| TVI_AType !AType /* auxiliary used in module comparedefimp */
					| TVI_Used /* to administer that this variable is encountered (in checkOpenTypes) */
					| TVI_TypeCode !TypeCodeExpression
					| TVI_CPSLocalTypeVar !Int /* MdM - the index of the variable as generated by the theorem prover */
					| TVI_Kinds ![TypeKind] // AA: used to collect kinds during checking 
					| TVI_Kind !TypeKind
					| TVI_ConsInstance !DefinedSymbol //AA: generic cons instance function 
					| TVI_Normalized !Int /* MV - position of type variable in its definition */
					| TVI_Expr !Expression	/* AA: Expression corresponding to the type var during generic specialization */

::	TypeVarInfoPtr	:== Ptr TypeVarInfo
::	TypeVarHeap 	:== Heap TypeVarInfo

::	AttrVarInfo  	= AVI_Empty
					| AVI_Attr !TypeAttribute
					| AVI_AttrVar !AttrVarInfoPtr // Sjaak: to collect universally quantified attribute variables
					| AVI_Forward !TempAttrId 
					| AVI_CorrespondenceNumber !Int /* auxiliary used in module comparedefimp */
					| AVI_Used
					| AVI_Count !Int /* auxiliary used in module typesupport */
					| AVI_SequenceNumber !Int // RWS
					| AVI_Collected // RWS

::	AttrVarInfoPtr	:== Ptr AttrVarInfo
::	AttrVarHeap 	:== Heap AttrVarInfo

::	TypeHeaps =
	{	th_vars		:: ! .TypeVarHeap
	,	th_attrs	:: ! .AttrVarHeap
	}

::	TypeVar =
	{	tv_name				:: !Ident
	,	tv_info_ptr			:: !TypeVarInfoPtr
	}


::	ATypeVar =
	{	atv_attribute		:: !TypeAttribute
	,	atv_variable		:: !TypeVar
	}

::	TypeAttribute = TA_Unique | TA_Multi | TA_Var !AttributeVar | TA_RootVar AttributeVar | TA_TempVar !Int // | TA_TempExVar !Int
					| TA_Anonymous | TA_None
					| TA_List !Int !TypeAttribute | TA_Locked !TypeAttribute
					| TA_MultiOfPropagatingConsVar
					| TA_PA_BUG

::	AttributeVar =
	{	av_name			:: !Ident
	,	av_info_ptr		:: !AttrVarInfoPtr
	}

::	Annotation	=  AN_Strict | AN_None 

::	BasicType	= BT_Int | BT_Char | BT_Real | BT_Bool | BT_Dynamic
				| BT_File | BT_World
				| BT_String !Type /* the internal string type synonym only used to type string denotations */

::	BasicValue	= BVI !String | BVInt !Int |BVC !String | BVB !Bool | BVR !String | BVS !String

::	TypeKind = KindVar !KindInfoPtr | KindConst | KindArrow ![TypeKind] | KindCycle | KindError

::	PatternVar =
	{	pv_var		:: !FreeVar
	,	pv_arg_nr	:: !Int
	}

::	Occurrence =
	{	occ_ref_count		:: !ReferenceCount
	,	occ_bind			:: !OccurrenceBinding
	,	occ_pattern_vars	:: ![[PatternVar]]
	,	occ_observing		:: !Bool
	,	occ_previous 		:: ![ReferenceCount]
	}

::	ReferenceCount = RC_Used !RC_Used | RC_Unused 

::	SelectiveUse =
	{	su_field	:: !Int
	,	su_multiply :: ![ExprInfoPtr]
	,	su_uniquely :: ![ExprInfoPtr]
	}

::	RC_Used =
	{ 	rcu_multiply	:: ![ExprInfoPtr]
	,	rcu_selectively :: ![SelectiveUse]
	,	rcu_uniquely	:: ![ExprInfoPtr]
	}

::	CountedFreeVar =
	{	cfv_var		:: !FreeVar
	,	cfv_is_let	:: !Bool
	,	cfv_count	:: !ReferenceCount
	}

::	OccurrenceBinding	= OB_Empty 
						| OB_OpenLet	FreeVar (Optional RefMarkResult)
						| OB_LockedLet	OccurrenceBinding

::	RefMarkResult :== ([CountedFreeVar], [FreeVar])

::	TypeDefInfo =
	{	tdi_kinds			:: ![TypeKind]
	,	tdi_properties		:: !BITVECT
	,	tdi_group			:: ![GlobalIndex]
	,	tdi_group_nr		:: !Int
	,	tdi_group_vars		:: ![Int]
	,	tdi_cons_vars		:: ![Int]
	,	tdi_index_in_group	:: !Index
	,	tdi_classification	:: !TypeClassification
	,	tdi_mark			:: !Bool //AA
	,	tdi_gen_rep			:: !Optional GenericTypeRep //AA
	}

// AA..
// type structure is used to specialize a generic to a type
:: GenTypeStruct 
	= GTSAppCons TypeKind [GenTypeStruct]
	| GTSAppVar TypeVar [GenTypeStruct] 
	| GTSVar TypeVar
 	| GTSCons DefinedSymbol GenTypeStruct
 	| GTSField DefinedSymbol GenTypeStruct
 	| GTSE
 
:: GenericTypeRep = 
	{ gtr_type :: GenTypeStruct		//AType				// generic structure type
	, gtr_iso  :: DefinedSymbol		// the conversion isomorphism
	}
// ..AA

::	TypeDefInfos :== {# .{# TypeDefInfo}}

::	OptGuardedAlts	= GuardedAlts ![GuardedExpr] !(Optional ExprWithLocalDefs)
				 	| UnGuardedExpr !ExprWithLocalDefs

::	GuardedExpr =
	{	alt_nodes	:: ![NodeDefWithLocals]
	,	alt_guard	:: !ParsedExpr
	,	alt_expr	:: !OptGuardedAlts
	,	alt_ident	:: !Ident
	,	alt_position:: !Position
	}

::	ExprWithLocalDefs = 
	{	ewl_nodes	:: ![NodeDefWithLocals]
	,	ewl_expr	:: !ParsedExpr
	,	ewl_locals	:: !LocalDefs
	,	ewl_position:: !Position
	}

::	NodeDefWithLocals =
	{	ndwl_strict		:: !Bool
	,	ndwl_def		:: !Bind ParsedExpr ParsedExpr
	,	ndwl_locals		:: !LocalDefs
	,	ndwl_position	:: !Position
	}


::	CaseAlt =
	{	calt_pattern	:: !ParsedExpr
	,	calt_rhs		:: !Rhs
	}
	
:: LocalDef		:== ParsedDefinition

::	ParsedSelectorKind
		=	ParsedNormalSelector	// .
		|	ParsedUniqueSelector	// !
				!Bool					// 	is result element unique?

:: ParsedExpr	= PE_List ![ParsedExpr]
				| PE_Ident !Ident
				| PE_Basic !BasicValue
				| PE_Bound !BoundExpr
				| PE_Lambda !Ident ![ParsedExpr] !ParsedExpr !Position
				| PE_Tuple ![ParsedExpr]				
				| PE_Record !ParsedExpr !(Optional Ident) ![FieldAssignment]
				| PE_ArrayPattern ![ElemAssignment]
				| PE_UpdateComprehension !ParsedExpr !ParsedExpr !ParsedExpr ![Qualifier]
				| PE_ArrayDenot ![ParsedExpr]
				| PE_Selection !ParsedSelectorKind !ParsedExpr ![ParsedSelection]
				| PE_Update !ParsedExpr [ParsedSelection] ParsedExpr
				| PE_Case !Ident !ParsedExpr [CaseAlt]
				| PE_If !Ident !ParsedExpr !ParsedExpr !ParsedExpr
				| PE_Let !Bool !LocalDefs !ParsedExpr
				| PE_ListCompr /*predef_cons_index:*/ !Int /*predef_nil_index:*/ !Int !ParsedExpr ![Qualifier]
				| PE_ArrayCompr !ParsedExpr ![Qualifier]
				| PE_Sequ Sequence
				| PE_WildCard
				| PE_Field !ParsedExpr !(Global FieldSymbol) /* Auxiliary, used during checking */

				| PE_ABC_Code ![String] !Bool
				| PE_Any_Code !(CodeBinding Ident) !(CodeBinding Ident) ![String]

				| PE_DynamicPattern !ParsedExpr !DynamicType
				| PE_Dynamic !ParsedExpr !(Optional DynamicType)
				
				| PE_Generic !Ident !TypeKind	/* AA: For generics, kind indexed identifier */
				
				| PE_Empty

::	ParsedSelection	= PS_Record !Ident !(Optional Ident)
					| PS_Array  !ParsedExpr
					| PS_Erroneous

::	GeneratorKind = IsListGenerator | IsOverloadedListGenerator | IsArrayGenerator

:: LineAndColumn = {lc_line :: !Int, lc_column :: !Int}

::	Generator =
	{	gen_kind	:: !GeneratorKind
	,	gen_pattern :: !ParsedExpr
	,	gen_expr	:: !ParsedExpr
	,	gen_position :: !LineAndColumn
	}

::	Qualifier	=
	{	qual_generators	:: ![Generator]
	,	qual_filter		:: !Optional ParsedExpr
	,	qual_position	:: !LineAndColumn
	,	qual_filename	:: !FileName
	}

::	Sequence	= SQ_FromThen ParsedExpr ParsedExpr
				| SQ_FromThenTo ParsedExpr ParsedExpr ParsedExpr
				| SQ_From ParsedExpr
				| SQ_FromTo ParsedExpr ParsedExpr

::	BoundExpr	:== Bind ParsedExpr Ident

::	FieldAssignment :== Bind ParsedExpr Ident

::	ElemAssignment :== Bind ParsedExpr [ParsedExpr]

//::	NodeDef :== Bind ParsedExpr ParsedExpr

cIsStrict		:== True
cIsNotStrict	:== False

::	SelectorKind
		=	NormalSelector
		|	NormalSelectorUniqueElementResult
		|	UniqueSelector			// !

::	Expression	= Var !BoundVar 
				| App !App
				| (@) infixl 9  !Expression ![Expression]
				| Let !Let
				| Case !Case
				| Selection !SelectorKind !Expression ![Selection]
				| Update !Expression ![Selection] Expression
				| RecordUpdate !(Global DefinedSymbol) !Expression ![Bind Expression (Global FieldSymbol)]
				| TupleSelect !DefinedSymbol !Int !Expression
				| BasicExpr !BasicValue
				| WildCard
				| Conditional !Conditional

				| AnyCodeExpr !(CodeBinding BoundVar) !(CodeBinding FreeVar) ![String]
				| ABCCodeExpr ![String] !Bool

				| MatchExpr !(Global DefinedSymbol) !Expression
				| FreeVar FreeVar 
				| Constant !SymbIdent !Int !Priority !Bool	/* auxiliary clause used during checking */
				| ClassVariable !VarInfoPtr					/* auxiliary clause used during overloading */

				| DynamicExpr !DynamicExpr
//				| TypeCase !TypeCase

				| TypeCodeExpression !TypeCodeExpression
				| EE 
				| NoBind ExprInfoPtr /* auxiliary, to store fields that are not specified in a record expression */ 


::	CodeBinding	variable :== Env String variable

::	App =
	{	app_symb 		:: !SymbIdent
	,	app_args 		:: ![Expression]
	,	app_info_ptr	:: !ExprInfoPtr
	}

::	Case =
	{	case_expr		:: !Expression
	,	case_guards		:: !CasePatterns
	,	case_default	:: !Optional Expression
	,	case_ident		:: !Optional Ident
	,	case_info_ptr	:: !ExprInfoPtr
// RWS ...
	,	case_explicit	:: !Bool
// ... RWS
	,	case_default_pos:: !Position
	}

::	Let =
	{	let_strict_binds	:: ![LetBind]
	,	let_lazy_binds		:: ![LetBind]
	,	let_expr			:: !Expression
	,	let_info_ptr		:: !ExprInfoPtr
	,	let_expr_position	:: !Position
	}

::	LetBind =
	{	lb_dst		:: !FreeVar
	,	lb_src		:: !Expression
	,	lb_position	:: !Position
	}

::	DynamicExpr =
	{	dyn_expr		:: !Expression
	,	dyn_opt_type	:: !Optional DynamicType
	,	dyn_info_ptr	:: !ExprInfoPtr
//	,	dyn_uni_vars	:: ![VarInfoPtr]			/* filled after type checking */
	,	dyn_type_code	:: !TypeCodeExpression		/* filled after type checking */
	}	

::	CasePatterns= AlgebraicPatterns !(Global Index) ![AlgebraicPattern]
				| BasicPatterns !BasicType [BasicPattern]
				| DynamicPatterns [DynamicPattern]						/* auxiliary */
				| OverloadedListPatterns !OverloadedListType !Expression ![AlgebraicPattern]
				| NoPattern											/* auxiliary */

::	OverloadedListType	= UnboxedList !(Global Index) !Index !Index !Index // list_type_symbol StdStrictLists module index, decons_u index, nil_u index
						| UnboxedTailStrictList !(Global Index) !Index !Index !Index // list_type_symbol StdStrictLists module index, decons_uts index, nil_uts index
						| OverloadedList !(Global Index) !Index !Index !Index // list_type_symbol StdStrictLists module index, decons index, nil index

::	Selection	= RecordSelection !(Global DefinedSymbol) !Int
				| ArraySelection !(Global DefinedSymbol) !ExprInfoPtr !Expression
				| DictionarySelection !BoundVar ![Selection] !ExprInfoPtr !Expression

::	TypeCodeExpression	= TCE_Empty
						| TCE_Var 			!VarInfoPtr
						| TCE_TypeTerm		!VarInfoPtr
						| TCE_Constructor	!Index			![TypeCodeExpression]
						| TCE_Selector		![Selection]	!VarInfoPtr
						| TCE_UniType 		![VarInfoPtr] 	!TypeCodeExpression

::	GlobalTCType = GTT_Basic !BasicType	| GTT_Constructor !TypeSymbIdent !String !Bool | GTT_Function

::	FunctionPattern	= FP_Basic !BasicValue !(Optional FreeVar)
					| FP_Algebraic !(Global DefinedSymbol) ![FunctionPattern] !(Optional FreeVar)
					| FP_Variable !FreeVar
					| FP_Dynamic ![VarInfoPtr] !FreeVar !TypeCodeExpression !(Optional FreeVar)
					| FP_Empty

::	AlgebraicPattern =
	{	ap_symbol	:: !(Global DefinedSymbol)
	,	ap_vars		:: ![FreeVar]
	,	ap_expr		:: !Expression
	,	ap_position	:: !Position
	}
	
::	BasicPattern =
	{	bp_value	:: !BasicValue
	,	bp_expr		:: !Expression
	,	bp_position	:: !Position
	}

::	TypeCase =
	{	type_case_dynamic	:: !Expression 
	,	type_case_patterns 	:: ![DynamicPattern]
	,	type_case_default	:: !Optional Expression
	,	type_case_info_ptr	:: !ExprInfoPtr
	}
	
::	DynamicPattern =
	{	dp_var					:: !FreeVar
	,	dp_type					:: !ExprInfoPtr
	,	dp_type_patterns_vars	:: ![VarInfoPtr]			/* filled after type checking */
	,	dp_type_code			:: !TypeCodeExpression		/* filled after type checking */
	,	dp_rhs					:: !Expression
	,	dp_position				:: !Position
	}
	
	
::	Conditional =
	{	if_cond		:: !Expression
	,	if_then		:: !Expression
	,	if_else		:: !Optional Expression
	}

/*
	error handling
*/

:: Position			= FunPos  FileName LineNr FunctName
					| LinePos FileName LineNr
					| PreDefPos Ident
					| NoPos

::	CoercionPosition
	=	CP_Expression !Expression
	|	CP_FunArg !Ident !Int // Function symbol, argument position (>=1)

::	IdentPos =
	{	ip_ident	:: !Ident
	,	ip_line		:: !Int
	,	ip_file		:: !FileName
	}

:: FileName			:== String

:: FunctName		:== String

:: LineNr			:== Int

cNotALineNumber :== -1

/* Used for hashing identifiers */

class needs_brackets a :: a -> Bool

instance == BoundVar
where
	(==) varid1 varid2
		= varid1.var_name == varid2.var_name

instance == Ident
where
	(==) id1 id2
		= id1.id_info == id2.id_info

instance needs_brackets AType
where
	needs_brackets {at_type}
		= needs_brackets at_type

instance needs_brackets Type
where
	needs_brackets (TA {type_arity} _)
		= type_arity > 0
	needs_brackets (TAS {type_arity} _ _)
		= type_arity > 0
	needs_brackets (_ --> _)
		= True
	needs_brackets (_ :@: _)
		= True
	needs_brackets (TArrow1 _)
		= True		
/*	needs_brackets (TFA _ _)
		= True
*/	needs_brackets _
		= False

instance needs_brackets Expression
where
	needs_brackets (App {app_args})
		= not (isEmpty app_args)
	needs_brackets (_ @ _)
		= True
	needs_brackets (Let _)
		= True
	needs_brackets (Case _)
		= True
	needs_brackets (Selection _ _ _)
		= True
	needs_brackets _
		= False

instance needs_brackets a
where
	needs_brackets _ = False

instance toString BasicType  where
	toString BT_Int = "Int"
	toString BT_Char = "Char"
	toString BT_Real = "Real"
	toString BT_Bool = "Bool"
	toString (BT_String _) = "String"
	toString BT_Dynamic = "Dynamic"
	toString BT_File = "File"
	toString BT_World = "World"
	
instance <<< BasicType
where
	(<<<) file bt			= file <<< toString bt

instance <<< TypeVar
where
//	(<<<) file varid = file <<< varid.tv_name 
	(<<<) file varid = file <<< varid.tv_name <<< "<" <<< varid.tv_info_ptr <<< ">"

instance <<< AttributeVar
where
	(<<<) file {av_name,av_info_ptr} = file <<< av_name <<< "[" <<< av_info_ptr <<< "]"
//	(<<<) file {av_name,av_info_ptr} = file <<< av_name

instance toString AttributeVar
where
	toString {av_name,av_info_ptr} = toString av_name + "[" + toString (ptrToInt av_info_ptr) + "]"
//	toString {av_name,av_info_ptr} = toString av_name

instance <<< AType
where
	(<<<) file {at_attribute,at_type}
		= file <<< at_attribute <<< at_type

instance <<< TypeCons 
where
	(<<<) file (TypeConsSymb name) = file <<< name
	(<<<) file (TypeConsBasic basic_type) = file <<< basic_type
	(<<<) file TypeConsArrow = file <<< "(->)"
	(<<<) file (TypeConsVar tv) = file <<< tv

instance <<< TypeAttribute
where
	(<<<) file ta
		= file <<< toString ta

instance toString TypeAttribute
where
	toString (TA_Unique)
		= "*"
	toString (TA_TempVar tav_number)
		= "u" + toString tav_number + ":"
	toString (TA_Var avar)
		= toString avar + ":"
	toString (TA_RootVar avar)
		= toString avar + ":"
	toString (TA_Anonymous)
		= "."
	toString TA_None
		= ""
	toString TA_Multi
		= "o "
	toString TA_MultiOfPropagatingConsVar
		= "@@ "
	toString (TA_List _ _)
		= "??? "
	toString TA_PA_BUG
		= PA_BUG "(E)" (abort "toString TA_PA_BUG")

instance <<< Annotation
where
	(<<<) file an = file <<< toString an

instance toString Annotation
where
	toString AN_Strict	= "!" 
	toString _			= "" 

instance <<< ATypeVar
where
	(<<<) file {atv_attribute,atv_variable}
		= file <<< atv_attribute <<< atv_variable

instance <<< ConsVariable
where
	(<<<) file (CV tv)
		= file <<< tv
	(<<<) file (TempCV tv)
		= file <<<  "v" <<< tv <<< ' ' 
	(<<<) file (TempQCV tv)
		= file <<<  "E." <<< tv <<< ' ' 

instance <<< StrictnessList
where
	(<<<) file (NotStrict)
		= file <<< 0
	(<<<) file (Strict s)
		= file <<< s
	(<<<) file (StrictList s l)
		= file <<< s <<< ' ' <<< l

instance <<< Type
where
	(<<<) file (TV varid)
		= file <<< varid
	(<<<) file (TempV tv_number)
		= file  <<< 'v' <<< tv_number <<< ' ' 
	(<<<) file (TA consid types)
		= file  <<< consid <<< " " <<< types
	(<<<) file (TAS consid types strictness)
		= file  <<< consid <<< ' ' <<< strictness <<< ' ' <<< types
	(<<<) file (arg_type --> res_type)
		= file <<< arg_type <<< " -> " <<< res_type
	(<<<) file TArrow
		= file <<< "(->)"	
	(<<<) file (TArrow1 t)
		= file <<< "(->) " <<< t	
	(<<<) file (type :@: types)
		= file <<< type <<< " @" <<< types
	(<<<) file (TB tb)
		= file <<< tb
	(<<<) file (TST atvs st)
		= file <<< "(A. " <<< atvs <<< ": " <<< st <<< ")"
	(<<<) file (TQV varid)
		= file <<< "E." <<< varid
	(<<<) file (TempQV tv_number)
		= file  <<< "E." <<< tv_number <<< ' ' 
	(<<<) file TE
		= file <<< "### EMPTY ###"
/*
instance <<< [a] | <<< , needs_brackets a
where
	(<<<) file [] 		= file
	(<<<) file [x:xs]
		| needs_brackets x
			= file <<< " (" <<< x <<< ')' <<< xs
			= file <<< ' ' <<< x <<< xs
*/

instance <<< SymbolType
where
	(<<<) file st=:{st_vars,st_attr_vars}
		| st.st_arity == 0
			= write_inequalities st.st_attr_env (write_contexts st.st_context (file <<< '[' <<< st_vars <<< ',' <<< st_attr_vars <<< ']' <<< st.st_args_strictness <<< ' ' <<< st.st_result))
			= write_inequalities st.st_attr_env (write_contexts st.st_context (file <<< '[' <<< st_vars <<< ',' <<< st_attr_vars <<< ']' <<< st.st_args_strictness <<< ' ' <<< st.st_args <<< " -> " <<< st.st_result))

write_contexts [] file
	= file
write_contexts [tc : tcs] file
	= write_contexts2 tcs (file <<< " | " <<< tc) 
where
	write_contexts2 [] file
		= file
	write_contexts2 [tc : tcs] file
		= write_contexts2 tcs (file <<< " & " <<< tc)

instance <<< AttrInequality
where
	(<<<) file {ai_demanded,ai_offered}
		= file <<< ai_offered <<< " <= " <<< ai_demanded
	
write_inequalities [] file
	= file
write_inequalities [ineq:ineqs] file
	= write_remaining_inequalities ineqs (file <<< ',' <<< ineq)
where
	write_remaining_inequalities [] file
		= file
	write_remaining_inequalities [ineq:ineqs] file
		= write_remaining_inequalities ineqs (file <<< ' ' <<< ineq)

instance <<< TypeContext
where
	(<<<) file co = file <<< co.tc_class <<< " " <<< co.tc_types <<< " <" <<< co.tc_var <<< '>'

instance <<< TCClass 
where
	(<<<) file (TCClass glob) = file <<< glob
	(<<<) file (TCGeneric {gtc_generic,gtc_kind}) = file <<< gtc_generic <<< gtc_kind

instance toString TCClass
where
	toString (TCClass clazz) = clazz.glob_object.ds_ident.id_name
	toString (TCGeneric {gtc_generic,gtc_kind}) = gtc_generic.glob_object.ds_ident.id_name +++ toString gtc_kind
	 
instance <<< SymbIdent
where
	(<<<) file symb=:{symb_kind = SK_Function symb_index }
		= file <<< symb.symb_name <<<  '@' <<< symb_index
	(<<<) file symb=:{symb_kind = SK_LocalMacroFunction symb_index }
		= file <<< symb.symb_name <<<  "[lm]@" <<< symb_index
	(<<<) file symb=:{symb_kind = SK_GeneratedFunction _ symb_index }
		= file <<< symb.symb_name <<<  "[g]@" <<< symb_index
	(<<<) file symb=:{symb_kind = SK_LocalDclMacroFunction symb_index }
		= file <<< symb.symb_name <<<  "[ldm]@" <<< symb_index
	(<<<) file symb=:{symb_kind = SK_OverloadedFunction symb_index }
		= file <<< symb.symb_name <<<  "[o]@" <<< symb_index
	(<<<) file symb
		= file <<< symb.symb_name 

instance <<< TypeSymbIdent
where
	(<<<) file symb	= file <<< symb.type_name <<< '.' <<< symb.type_index

instance <<< ClassSymbIdent
where
	(<<<) file symb	= file <<< symb.cs_name 

instance <<< BoundVar
where
	(<<<) file {var_name,var_info_ptr,var_expr_ptr}
		= file <<< var_name <<< "<I" <<< var_info_ptr <<< ", E" <<< var_expr_ptr <<< '>'

instance <<< (Bind a b) | <<< a & <<< b 
where
	(<<<) file {bind_src,bind_dst} = file <<< bind_dst <<<  " = " <<< bind_src 


instance <<< AlgebraicPattern
where
	//(<<<) file g = file <<< g.ap_symbol <<< g.ap_vars <<< " -> " <<< g.ap_expr
	(<<<) file g = file <<< '\n' <<< g.ap_symbol <<< g.ap_vars <<< "\n\t-> " <<< g.ap_expr

instance <<< BasicPattern
where
	//(<<<) file g = file <<< g.bp_value <<< " -> " <<< g.bp_expr
	(<<<) file g = file <<< '\n' <<< g.bp_value <<< "\n\t-> " <<< g.bp_expr

instance <<< CasePatterns
where
	(<<<) file (BasicPatterns type patterns) = file <<< " " <<<patterns
	(<<<) file (AlgebraicPatterns type patterns) = file <<< patterns
	(<<<) file (DynamicPatterns patterns) = file <<< patterns
	(<<<) file (OverloadedListPatterns type decons_expr patterns) = file <<< decons_expr <<< " " <<< patterns
	(<<<) file NoPattern = file 

instance <<< CheckedAlternative
where
	(<<<) file {ca_rhs} = file <<< ca_rhs

instance <<< Qualifier
where
	(<<<) file {qual_generators,qual_filter = Yes qual_filter} = file <<< qual_generators <<< "| " <<< qual_filter
	(<<<) file {qual_generators,qual_filter = No} = file <<< qual_generators

instance <<< Generator
where
	(<<<) file {gen_kind,gen_pattern,gen_expr}
		= file <<< gen_pattern <<< (gen_kind_to_string gen_kind) <<< gen_expr
	where
		gen_kind_to_string IsListGenerator = "<-"
		gen_kind_to_string IsOverloadedListGenerator = "<|-"
		gen_kind_to_string IsArrayGenerator = "<-:"

instance <<< BasicValue
where
	(<<<) file (BVI int)	= file <<< int
	(<<<) file (BVInt int)	= file <<< int
	(<<<) file (BVC char)	= file <<< char
	(<<<) file (BVB bool)	= file <<< bool
	(<<<) file (BVR real)	= file <<< real
	(<<<) file (BVS string)	= file <<< string
	
instance <<< Sequence
where
	(<<<) file (SQ_From expr) = file <<< expr
	(<<<) file (SQ_FromTo from_expr to_expr) = file <<< from_expr <<< ".."  <<< to_expr
	(<<<) file (SQ_FromThen from_expr then_expr) = file <<< from_expr  <<< ',' <<< then_expr <<< ".."
	(<<<) file (SQ_FromThenTo from_expr then_expr to_expr) = file <<< from_expr  <<< ',' <<< then_expr <<< ".." <<< to_expr

instance <<< Expression
where
	(<<<) file (Var ident) = file <<< ident
	(<<<) file (App {app_symb, app_args, app_info_ptr})
		= case app_symb.symb_kind of
			SK_Generic _ kind 
				->  file <<< app_symb <<< kind <<< ' ' <<< app_args
			_ 	-> file <<< app_symb <<< ' ' <<< app_args
	(<<<) file (f_exp @ a_exp) = file <<< '(' <<< f_exp <<< " @ " <<< a_exp <<< ')'
	(<<<) file (Let {let_info_ptr, let_strict_binds, let_lazy_binds, let_expr}) 
			= write_binds "" (write_binds "!" (file <<< "let" <<< '\n') let_strict_binds) let_lazy_binds <<< "in\n" <<< let_expr
	where
		write_binds x file []
			= file
		write_binds x file [bind : binds]
			= write_binds x (file <<< x <<< " " <<< bind) binds
 	(<<<) file (Case {case_expr,case_guards,case_default=No})
		//= file <<< "case " <<< case_expr <<< " of\n" <<< case_guards
		= file <<< "case " <<< case_expr <<< " of" <<< case_guards
	(<<<) file (Case {case_expr,case_guards,case_default= Yes def_expr})
		//= file <<< "case " <<< case_expr <<< " of\n" <<< case_guards <<< "\n\t->" <<< def_expr
		= file <<< "case " <<< case_expr <<< " of" <<< case_guards <<< "\n\t->" <<< def_expr
	(<<<) file (BasicExpr basic_value) = file <<< basic_value
	(<<<) file (Conditional {if_cond,if_then,if_else}) =
			else_part (file <<< "IF " <<< if_cond <<< "\nTHEN\n" <<< if_then) if_else
	where
		else_part file No = file <<< '\n'
		else_part file (Yes else) = file <<< "\nELSE\n" <<< else <<< '\n'

/*	(<<<) file (Conditional {if_cond = {con_positive,con_expression},if_then,if_else}) =
			else_part (file <<< (if con_positive "IF " "IFNOT ") <<< con_expression <<< "\nTHEN\n" <<< if_then) if_else
	where
		else_part file No = file <<< '\n'
		else_part file (Yes else) = file <<< "\nELSE\n" <<< else <<< '\n'
*/
 	(<<<) file (Selection selector_kind expr selectors) = file <<< expr <<< selector_kind <<< selectors
	(<<<) file (Update expr1 selections expr2) =  file <<< '{' <<< expr1  <<< " & " <<<  selections <<< " = " <<< expr2 <<< '}'
	(<<<) file (RecordUpdate cons_symbol expression expressions) = file <<< '{' <<< cons_symbol <<< ' ' <<< expression <<< " & " <<< expressions <<< '}'
	(<<<) file (TupleSelect field field_nr expr) = file <<< expr <<<'.' <<< field_nr
//	(<<<) file (Lambda vars expr) = file <<< '\\' <<< vars <<< " -> " <<< expr
	(<<<) file WildCard = file <<< '_'
	(<<<) file (MatchExpr cons expr) = file <<< cons <<< " =: " <<< expr
	(<<<) file EE = file <<< "** E **"
	(<<<) file (NoBind _) = file <<< "** NB **"
	(<<<) file (DynamicExpr {dyn_expr,dyn_type_code})     = file <<< "dynamic " <<< dyn_expr <<< " :: " <<< dyn_type_code 
//	(<<<) file (DynamicExpr {dyn_expr,dyn_uni_vars,dyn_type_code})     = writeVarPtrs (file <<< "dynamic " <<< dyn_expr <<< " :: dyn_uni_vars") dyn_uni_vars <<< "dyn_type_code=" <<< dyn_type_code 
//	(<<<) file (TypeCase type_case)      = file <<< type_case
	(<<<) file (TypeCodeExpression type_code)      = file <<< type_code
	(<<<) file (Constant symb _ _ _)         = file <<<  "** Constant **" <<< symb

	(<<<) file (ABCCodeExpr code_sequence do_inline)      = file <<< (if do_inline "code inline\n" "code\n") <<< code_sequence
	(<<<) file (AnyCodeExpr input output code_sequence)   = file <<< "code\n" <<< input <<< "\n" <<< output <<< "\n" <<< code_sequence

	(<<<) file (FreeVar {fv_name})         	= file <<< fv_name
	(<<<) file (ClassVariable info_ptr)         	= file <<< "ClassVariable " <<< info_ptr

	(<<<) file expr         				= abort ("<<< (Expression) [line 1290]" )//<<- expr)
	
instance <<< LetBind
where
	(<<<) file {lb_dst, lb_src}
		= file <<< lb_dst <<< " = " <<< lb_src <<< "\n"

instance <<< TypeCase
where
	(<<<) file {type_case_dynamic,type_case_patterns,type_case_default}
			= file <<< "typecase " <<< type_case_dynamic <<< "of\n" <<<
				type_case_patterns <<< type_case_default

instance <<< DynamicPattern
where
	(<<<) file {dp_type_patterns_vars,dp_var,dp_rhs,dp_type_code}
			= writeVarPtrs (file <<< dp_var <<< " :: ")  dp_type_patterns_vars <<<  dp_type_code <<< " = " <<< dp_rhs

writeVarPtrs file []
	= file
writeVarPtrs file vars
	= write_var_ptrs (file <<< '<') vars <<< '>'
	where
		write_var_ptrs file [var]
			= file <<< var
		write_var_ptrs file [var : vars]
			= write_var_ptrs (file <<< var <<< '.') vars
		
		
instance <<< TypeCodeExpression
where
	(<<<) file TCE_Empty
		= file
	(<<<) file (TCE_Var info_ptr)
		= file <<< "TCE_Var " <<< info_ptr
	(<<<) file (TCE_TypeTerm info_ptr)
		= file <<< "TCE_TypeTerm " <<< info_ptr
	(<<<) file (TCE_Constructor index exprs)
		= file <<< "TCE_Constructor " <<< index <<< ' ' <<< exprs
	(<<<) file (TCE_Selector selectors info_ptr)
		= file <<< "TCE_Selector " <<< selectors <<< "VAR " <<< info_ptr
	(<<<) file (TCE_UniType vars type_code)
		= file <<< "TCE_UniType " <<< vars <<< " " <<< type_code

instance <<< (Ptr a)
where
	(<<<) file ptr
		= file <<< ptrToInt ptr

instance <<< SelectorKind
where
 	(<<<) file NormalSelector = file <<< "."
 	(<<<) file NormalSelectorUniqueElementResult = file <<< "!*"
 	(<<<) file UniqueSelector = file <<< "!"

instance <<< Selection
where
	(<<<) file (RecordSelection selector _) = file <<< selector
	(<<<) file (ArraySelection {glob_object={ds_index}} _ index_expr) = file <<< '<' <<< ds_index <<< '>' <<< '[' <<< index_expr <<< ']'
	(<<<) file (DictionarySelection var selections _ index_expr) = file <<< '(' <<< var <<< '.' <<< selections <<< ')' <<< '[' <<< index_expr <<< ']'

instance <<< LocalDefs
where
	(<<<) file (LocalParsedDefs defs) = file <<< defs
	(<<<) file (CollectedLocalDefs defs) = file <<< defs

instance <<< (NodeDef dst) | <<< dst 
where
	(<<<) file {nd_dst,nd_alts,nd_locals} = file <<< nd_dst <<< nd_alts <<< nd_locals


instance <<< CollectedLocalDefs
where
	(<<<) file {loc_functions,loc_nodes}
		= file <<< loc_functions <<< loc_nodes
/*
	(<<<) file {def_types,def_constructors,def_selectors,def_macros,def_classes,def_members,def_instances}
		= file <<< def_types <<< def_constructors <<< def_selectors <<< def_macros <<< def_classes <<< def_members <<< def_instances
*/

instance <<< ParsedExpr
where
	(<<<) file (PE_List exprs) = file <<< exprs
	(<<<) file (PE_Tuple args) = file <<< '(' <<< args <<< ')'
	(<<<) file (PE_Basic basic_value) = file <<< basic_value
	(<<<) file (PE_Selection selector_kind expr selectors) =  file <<< expr <<< selector_kind <<< selectors
	(<<<) file (PE_Update expr1 selections expr2) =  file <<< '{' <<< expr1  <<< " & " <<<  selections <<< " = " <<< expr2 <<< '}'
	(<<<) file (PE_Record PE_Empty _ fields) = file <<< '{' <<< fields <<< '}'
	(<<<) file (PE_Record rec _ fields) = file <<< '{' <<< rec <<< " & " <<< fields <<< '}'
	(<<<) file (PE_ListCompr _ _ expr quals) = file <<< '[' <<< expr <<< " \\ " <<< quals <<< ']'
	(<<<) file (PE_ArrayCompr expr quals) = file <<< '{' <<< expr <<< " \\ " <<< quals <<< '}'
	(<<<) file (PE_Sequ seq) = file <<< '[' <<< seq <<< ']'
	(<<<) file PE_Empty = file <<< "** E **"
	(<<<) file (PE_Ident symb) = file <<< symb
	(<<<) file PE_WildCard = file <<< '_'
	(<<<) file (PE_Lambda _ exprs expr _) = file <<< '\\' <<< exprs <<< " -> " <<< expr
	(<<<) file (PE_Bound bind) = file <<< bind
	(<<<) file (PE_Case _ expr alts) = file <<< "case " <<< expr <<< " of\n" <<< alts
	(<<<) file (PE_Let _ defs expr) = file <<< "let " <<< defs <<< " in\n" <<< expr
	(<<<) file (PE_DynamicPattern expr type) = file <<< expr <<< "::" <<< type
	(<<<) file (PE_Dynamic expr maybetype)
		= case maybetype of
			Yes type
				-> file <<< "dynamic " <<< expr <<< "::" <<< type
			No
				-> file <<< "dynamic " <<< expr
	(<<<) file _ = file <<< "some expression"

instance <<< ParsedSelectorKind
where
	(<<<) file ParsedNormalSelector			= file <<< "."
	(<<<) file (ParsedUniqueSelector False)	= file <<< "!"
	(<<<) file (ParsedUniqueSelector True)	= file <<< "!*"
	
instance <<< ParsedSelection
where
	(<<<) file (PS_Record selector _)	= file <<< selector
	(<<<) file (PS_Array index_expr)	= file <<< '[' <<< index_expr <<< ']'
	(<<<) file PS_Erroneous				= file <<< "Erroneous selector" // PK

instance <<< CaseAlt
where
	(<<<) file {calt_pattern,calt_rhs} = file <<< calt_pattern <<< " -> " <<< calt_rhs

instance <<< ParsedBody
where
	(<<<) file {pb_args,pb_rhs} = file <<< pb_args <<< " = " <<< pb_rhs
	
instance <<< BackendBody
where
	(<<<) file {bb_args,bb_rhs} = file <<< bb_args <<< " = " <<< bb_rhs

instance <<< FunctionPattern
where
	(<<<) file (FP_Basic val (Yes var))
		= file <<< var <<< "=:" <<< val
	(<<<) file (FP_Basic val No)
		= file <<< val
	(<<<) file (FP_Algebraic constructor vars (Yes var))
		= file <<< var <<< "=:" <<< constructor <<< vars
	(<<<) file (FP_Algebraic constructor vars No)
		= file <<< constructor <<< vars
	(<<<) file (FP_Variable var) = file <<< var 
	(<<<) file (FP_Dynamic vars var type_code _)
		= writeVarPtrs (file <<< var <<< " :: ") vars <<<  type_code
	(<<<) file (FP_Empty) = file <<< '_' 


instance <<< FunKind
where
	(<<<) file (FK_Function False) = file <<< "FK_Function"
	(<<<) file (FK_Function True) = file <<< "Lambda"
	(<<<) file FK_NodeDefOrFunction = file <<< "FK_NodeDefOrFunction"
	(<<<) file FK_Macro = file <<< "FK_Macro"
	(<<<) file FK_Caf = file <<< "FK_Caf"
	(<<<) file FK_Unknown = file <<< "FK_Unknown"

instance <<< FunType 
where
	(<<<) file {ft_symb,ft_type} = file <<< ft_symb <<< "::" <<< ft_type

instance <<< FunDef
where
	(<<<) file {fun_symb,fun_body=ParsedBody bodies} = file <<< fun_symb <<< '.' <<< ' ' <<< bodies 
	(<<<) file {fun_symb,fun_body=CheckedBody {cb_args,cb_rhs},fun_info={fi_free_vars,fi_def_level,fi_calls}} = file <<< fun_symb <<< '.'
			<<< "C " <<< cb_args <<< " = " <<< cb_rhs <<< '\n'
//			<<< '.' <<< fi_def_level <<< ' ' <<< '[' <<< fi_free_vars <<< ']' <<< cb_args <<< " = " <<< cb_rhs 
	(<<<) file {fun_symb,fun_body=TransformedBody {tb_args,tb_rhs},fun_info={fi_free_vars,fi_local_vars,fi_def_level,fi_calls}}
		= file <<< fun_symb <<< '.' <<< "T "  
//			<<< '[' <<< fi_free_vars <<< "]  [" <<< fi_local_vars <<< ']'
			<<< tb_args <<< '[' <<< fi_calls <<< ']' <<< " = " <<< tb_rhs <<< '\n'
//			<<< '.' <<< fi_def_level <<< ' ' <<< '[' <<< fi_free_vars <<< ']' <<< tb_args <<< " = " <<< tb_rhs 
	(<<<) file {fun_symb,fun_body=BackendBody body,fun_type=Yes type} = file // <<< type <<< '\n'
			<<< fun_symb <<< '.' <<< body <<< '\n'
	(<<<) file {fun_symb,fun_body=NoBody,fun_type=Yes type} = file // <<< type <<< '\n'
			<<< fun_symb <<< '.' <<< "Array function\n"

	(<<<) file {fun_symb} = file <<< fun_symb <<< "???" <<< '\n'

instance <<< FunctionBody
where
	(<<<) file (ParsedBody bodies) = file <<< bodies 
	(<<<) file (CheckedBody {cb_args,cb_rhs}) = file <<< "C " <<< cb_args <<< " = " <<< cb_rhs <<< '\n'
	(<<<) file (TransformedBody {tb_args,tb_rhs}) = file <<< "T "  <<< tb_args <<< " = " <<< tb_rhs <<< '\n'
	(<<<) file (BackendBody body) = file <<< body <<< '\n'
	(<<<) file (Expanding vars) = file <<< "E " <<< vars 
	(<<<) file GeneratedBody = file <<< "Generic function\n"
	(<<<) file NoBody = file <<< "Array function\n"
	

instance <<< FunCall
where
	(<<<) file (FunCall fc_index fc_level)
			= file <<< fc_index <<< '.' <<< fc_level
	(<<<) file (MacroCall module_index fc_index fc_level)
			= file <<< "MacroCall "<<< module_index <<<" "<<<fc_index <<< '.' <<< fc_level

instance <<< FreeVar
where
	(<<<) file {fv_name,fv_info_ptr,fv_count} = file <<< fv_name <<< '.' <<< fv_count <<< '<' <<< fv_info_ptr <<< '>'

instance <<< DynamicType
where
	(<<<) file {dt_uni_vars,dt_type}
		| isEmpty dt_uni_vars
			= file <<< "DynamicType" <<< dt_type
			= file <<< "DynamicType" <<< "A." <<< dt_uni_vars <<< ":" <<< dt_type
			

instance <<< SignClassification
where
	(<<<) file {sc_pos_vect,sc_neg_vect} = write_signs file sc_pos_vect sc_neg_vect 0
	where
		write_signs file sc_pos_vect sc_neg_vect index
			| sc_pos_vect == 0 && sc_neg_vect == 0
				= file
			#	index_bit = (1 << index)
			| sc_pos_vect bitand index_bit == 0
				| sc_neg_vect bitand index_bit == 0
					= write_signs (file <<< 'O') sc_pos_vect sc_neg_vect (inc index)
					= write_signs (file <<< '-') sc_pos_vect (sc_neg_vect bitand (bitnot index_bit)) (inc index)
				| sc_neg_vect bitand index_bit == 0
					= write_signs (file <<< '+') (sc_pos_vect bitand (bitnot index_bit)) sc_neg_vect (inc index)
					= write_signs (file <<< 'T') (sc_pos_vect bitand (bitnot index_bit)) (sc_neg_vect bitand (bitnot index_bit)) (inc index)

instance toString TypeKind
where
	toString (KindVar _) 		= "**"
	toString KindConst			= "*"
	toString (KindArrow args) 	= "{" +++ (to_string args) +++ "->*}" 
	where
		to_string []		= "??????" 
		to_string [k]		= toString k  
		to_string [k:ks]	= (toString k) +++ "->" +++ (to_string ks)

				
instance <<< TypeKind
where
	(<<<) file kind 		= file <<< (toString kind)

instance == TypeKind 
where
	(==) KindConst KindConst = True
	(==) (KindArrow xs) (KindArrow ys) = xs == ys
	(==) _ _ = False
				

instance toString KindInfo
where
	toString (KI_Var ptr) 				= "*" +++ toString (ptrToInt ptr)
	toString (KI_Const) 				= "*"
	toString (KI_Arrow kind1 kind2)		= withBrackets kind1 (toString kind1) +++ " -> " +++ toString kind2
	where
		withBrackets (KI_Arrow _ _) kind_str	= "(" +++ kind_str +++ ")"
		withBrackets _				kind_str	= kind_str

instance <<< TypeDefInfo
where
	(<<<) file {tdi_group,tdi_group_vars,tdi_cons_vars}
//		= file <<< '[' <<< tdi_group <<< '=' <<< tdi_group_vars <<< '=' <<< tdi_cons_vars <<< ']'
		= file <<< '[' <<< tdi_group_vars <<< '=' <<< tdi_cons_vars <<< ']'

instance <<< DefinedSymbol
where
	(<<<) file {ds_ident}
		= file <<< ds_ident 

instance <<< (TypeDef a) | <<< a
where
	(<<<) file {td_name, td_args, td_rhs}
		= file <<< ":: " <<< td_name <<< ' ' <<< td_args <<< td_rhs

instance <<< TypeRhs
where
	(<<<) file (SynType type)
		= file <<< " :== " <<< type 
	(<<<) file (AlgType data)
		= file <<< " = " <<< data 
	(<<<) file (RecordType record)
		= file <<< " = " <<< '{' <<< record <<< '}'
	(<<<) file _
		= file 


instance <<< RecordType
where
	(<<<) file {rt_fields} = iFoldSt (\index file -> file <<< rt_fields.[index]) 0 (size rt_fields) file

instance <<< FieldSymbol
where
	(<<<) file {fs_name} = file <<< fs_name

/*
	where
		write_data_defs file []
			= file
		write_data_defs file [d:ds]
			= write_data_defs (file <<< d <<< '\n') ds
*/

instance <<< GenericClassInfo 
where
	(<<<) file {gci_kind, gci_class} = file <<< gci_kind <<< ":" <<< gci_class 

instance <<< InstanceType
where
	(<<<) file it = write_contexts it.it_context (file <<< it.it_types) 

instance <<< RhsDefsOfType
where
	(<<<) file (ConsList cons_defs) = file <<< cons_defs
	(<<<) file (SelectorList _ _ sel_defs) = file <<< sel_defs
	(<<<) file (TypeSpec type) = file <<< type
	(<<<) file _ = file

instance <<< ParsedConstructor
where
	(<<<) file {pc_cons_name,pc_arg_types} = file <<< pc_cons_name <<< pc_arg_types

instance <<< ParsedSelector
where
	(<<<) file {ps_field_name,ps_field_type} = file <<< ps_field_name <<< ps_field_type


instance <<< ModuleKind
where
	(<<<) file kind 		= file

instance <<< ConsDef
where
	(<<<) file {cons_symb,cons_type} = file <<< cons_symb <<< " :: " <<< cons_type

instance <<< SelectorDef
where
	(<<<) file {sd_symb} = file <<< sd_symb

instance <<< ClassDef
where
	(<<<) file {class_name} = file <<< class_name

instance <<< ClassInstance
where
	(<<<) file {ins_class,ins_type} = file <<< ins_class <<< " :: " <<< ins_type

instance <<< (Optional a) | <<< a
where
	(<<<) file (Yes x) = file <<< x
	(<<<) file No = file
	
instance <<< (Module a) | <<< a
where
	(<<<) file {mod_name,mod_type,mod_defs} = file <<< mod_type <<< mod_name <<< mod_defs

instance <<< (CollectedDefinitions a b) | <<< a & <<< b
where
	(<<<) file {def_types,def_constructors,def_selectors,def_macros,def_classes,def_members,def_instances}
		= file

instance <<< ParsedDefinition
where
	(<<<) file (PD_Function _ name _ exprs rhs _ ) = file <<< name <<< exprs <<< " = " <<< rhs
	(<<<) file (PD_NodeDef  _ pattern rhs) = file <<< pattern <<< " =: " <<< rhs
	(<<<) file (PD_TypeSpec _ name prio st sp) = file <<< name <<< st
	(<<<) file (PD_Type td) = file <<< td
	(<<<) file (PD_Generic {gen_name}) = file <<< "generic " <<< gen_name
	(<<<) file (PD_GenericCase {gc_name,gc_type_cons}) = file <<< gc_name <<< "{|" <<< gc_type_cons <<< "|}"
	 
	(<<<) file _ = file

instance <<< Rhs
where
	(<<<) file {rhs_alts,rhs_locals} = file <<< rhs_alts <<< rhs_locals <<< '\n'

instance <<< OptGuardedAlts
where
	(<<<) file (GuardedAlts guarded_exprs def_expr) = file <<< guarded_exprs <<< def_expr
	(<<<) file (UnGuardedExpr unguarded_expr) = file <<< unguarded_expr

instance <<< ExprWithLocalDefs
where
	(<<<) file {ewl_expr,ewl_locals} = file <<< ewl_expr <<< ewl_locals

instance <<< GuardedExpr
where
	(<<<) file {alt_nodes,alt_guard,alt_expr} = file <<< '|' <<< alt_guard <<< alt_expr


instance <<< IndexRange
where
	(<<<) file {ir_from,ir_to}
		| ir_from == ir_to
			= file
			= file <<< ir_from <<< "---" <<< ir_to

instance <<< Ident
where
//	(<<<) file {id_name,id_index} = file <<< id_name <<< '.' <<< id_index
	(<<<) file {id_name} = file <<< id_name

instance <<< (Global a) | <<< a
where
	(<<<) file {glob_object,glob_module} = file <<< glob_object <<< "M:" <<< glob_module

instance <<< Position
where
	(<<<) file (FunPos file_name line func) = file <<< '[' <<< file_name <<< ',' <<< line <<< ',' <<< func <<< ']'
	(<<<) file (LinePos file_name line) = file <<< '[' <<< file_name <<< ',' <<< line <<< ']'
	(<<<) file _ = file

instance <<< TypeVarInfo
where
	(<<<) file TVI_Empty				= file <<< "TVI_Empty"
	(<<<) file (TVI_Type _)				= file <<< "TVI_Type"
	(<<<) file (TVI_TypeVar ptr)		= file <<< (ptrToInt ptr) 
	(<<<) file (TVI_Forward	_) 			= file <<< "TVI_Forward"
	(<<<) file (TVI_SignClass _ _ _) 	= file <<< "TVI_SignClass"
	(<<<) file (TVI_Attribute ta) 		= file <<< "TVI_Attribute " <<< ta
	(<<<) file (TVI_CorrespondenceNumber n) = file <<< "TVI_CorrespondenceNumber " <<< n
	(<<<) file (TVI_AType at) 			= file <<< "TVI_AType " <<< at
	(<<<) file TVI_Used					= file <<< "TVI_Used"
	(<<<) file (TVI_TypeCode	_)		= file <<< "TVI_TypeCode"
	(<<<) file (TVI_CPSLocalTypeVar	_)	= file <<< "TVI_CPSLocalTypeVar"		
	(<<<) file (TVI_Kinds _)		= file <<< "TVI_Kinds"
	(<<<) file (TVI_TypeKind _)			= file <<< "TVI_TypeKind"
	(<<<) file (TVI_PropClass _ _ _) 	= file <<< "TVI_PropClass"
	(<<<) file (TVI_TypeKind kind_info_ptr) = file <<< "TVI_TypeKind " <<< (ptrToInt kind_info_ptr)
	(<<<) file (TVI_Kind kind) 			= file <<< "TVI_Kind" <<< kind
	(<<<) file (TVI_Expr expr) 			= file <<< "TVI_Expr " <<< expr

instance <<< AttrVarInfo
where
	(<<<) file AVI_Empty				= file <<< "AVI_Empty"
	(<<<) file (AVI_Attr attr)			= file <<< "AVI_Attr " <<< attr
	(<<<) file (AVI_AttrVar av_info_ptr) = file <<< "AVI_AttrVar " <<< ptrToInt av_info_ptr
	(<<<) file (AVI_Forward temp_attr_id) = file <<< "AVI_Forward " <<< temp_attr_id 
	(<<<) file (AVI_CorrespondenceNumber n) = file <<< "AVI_CorrespondenceNumber " <<< n
	(<<<) file AVI_Used					= file <<< "AVI_Used"
	(<<<) file (AVI_Count n) 			= file <<< "AVI_Count " <<< n
	(<<<) file (AVI_SequenceNumber n) 	= file <<< "AVI_SequenceNumber " <<< n
	(<<<) file AVI_Collected 			= file <<< "AVI_Collected"

	
instance <<< (Import from_symbol) | <<< from_symbol
where
	(<<<) file {import_module, import_symbols}
		= file <<< "import " <<< import_module <<< import_symbols

instance <<< ImportDeclaration
where
	(<<<) file (ID_Function ident)			= file <<< ident
	(<<<) file (ID_Class ident optIdents)	= file <<< "class " <<< ident <<< optIdents
	(<<<) file (ID_Type ident optIdents)	= file <<< ":: " <<< ident <<< optIdents
	(<<<) file (ID_Record ident optIdents)	= file <<< ident <<< " { " <<< optIdents <<< " } "
	(<<<) file (ID_Instance i1 i2 tup)		= file <<< "instance " <<< i1 <<< i2 <<< tup // !ImportedIdent !Ident !(![Type],![TypeContext])

instance <<< CoercionPosition
where
	(<<<) file (CP_FunArg fun_name arg_nr) = file <<< "argument " <<< arg_nr <<< " of " <<< readable fun_name
	(<<<) file (CP_Expression expression) = show_expression file expression
	where
		show_expression file (Var {var_name})
			= file <<< var_name
		show_expression file (FreeVar {fv_name})
			= file <<< fv_name
		show_expression file (App {app_symb={symb_name}, app_args})
			| symb_name.id_name=="_dummyForStrictAlias"
				= show_expression file (hd app_args)
			= file <<< readable symb_name
		show_expression file (fun @ fun_args)
			= show_expression file fun
		show_expression file (Case {case_ident=No})
			= file <<< "(case ... )"
		show_expression file (Selection _ expr selectors)
			= file <<< "selection"
		show_expression file (Update expr1 selectors expr2)
			= file <<< "update"
		show_expression file (TupleSelect {ds_arity} elem_nr expr)
			= file <<< "argument " <<< (elem_nr + 1) <<< " of " <<< ds_arity <<< "-tuple"
		show_expression file (BasicExpr bv)
			= file <<< bv
		show_expression file (MatchExpr _ expr)
			= file <<< "match expression"
		show_expression file _
			= file
		
instance <<< Declaration
  where
	(<<<) file (Declaration { decl_ident, decl_kind })
		= file <<< decl_ident <<< '<' <<< decl_ident.id_info <<< '>' <<< '(' <<< decl_kind <<< ')'

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
// AA..			
	(<<<) file
		STE_Generic
			= file <<< "STE_Generic"
	(<<<) file
		STE_GenericCase
			= file <<< "STE_GenericCase"
// ..AA
	(<<<) file
		(STE_Field _)
			= file <<< "STE_Field"
	(<<<) file
		STE_Member
			= file <<< "STE_Member"
	(<<<) file
		(STE_Instance _)
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
		(STE_Imported a b)
			= file <<< "STE_Imported (" <<< a <<< ")" <<< b 
	(<<<) file
		STE_DclFunction
			= file <<< "STE_DclFunction"
	(<<<) file
		(STE_Module _)
			= file <<< "STE_Module"
	(<<<) file
		STE_ClosedModule
			= file <<< "STE_ClosedModule"
	(<<<) file
		STE_Empty 
			= file <<< "STE_Empty"
	(<<<) file
		_ 
			= file <<< "STE_???"

readable :: !Ident -> String // somewhat hacky
readable {id_name}
	| size id_name>0 && id_name.[0]=='_'
		| id_name=="_Cons" || id_name=="_Nil"
			= "list constructor"
		| id_name=="_!Cons" || id_name=="_!Nil"
			= "! list constructor"
		| id_name=="_#Cons" || id_name=="_#Nil"
			= "# list constructor"
		| id_name=="_Cons!" || id_name=="_Nil!"
			= "list constructor !"
		| id_name=="_!Cons!" || id_name=="_!Nil!"
			= "! list constructor !"
		| id_name=="_#Cons!" || id_name=="_#Nil!"
			= "# list constructor !"
			= id_name%(1, size id_name-1)
	= id_name

instance <<< ImportedIdent
where
	(<<<) file {ii_ident, ii_extended}	= file <<< ii_ident <<< ' ' <<< ii_extended

instance == ModuleKind
where
	(==) mk1 mk2 = equal_constructor mk1 mk2

instance == TypeAttribute
where
	(==) attr1 attr2 = equal_constructor attr1 attr2

instance == Annotation
where
	(==) a1 a2 = equal_constructor a1 a2

instance == OverloadedListType
where
	(==) a1 a2 = equal_constructor a1 a2
	
EmptySymbolTableEntry :== EmptySymbolTableEntryCAF.boxed_symbol_table_entry

::BoxedSymbolTableEntry = {boxed_symbol_table_entry::!SymbolTableEntry}

EmptySymbolTableEntryCAF :: BoxedSymbolTableEntry
EmptySymbolTableEntryCAF =: {boxed_symbol_table_entry = { ste_kind = STE_Empty, ste_index = NoIndex, ste_def_level = NotALevel, ste_previous = abort_empty_SymbolTableEntry } }

abort_empty_SymbolTableEntry :: a
abort_empty_SymbolTableEntry = abort "empty SymbolTableEntry"

cNotAGroupNumber :== -1

EmptyTypeDefInfo :== { tdi_kinds = [], tdi_properties = cAllBitsClear, tdi_group = [], tdi_group_vars = [], tdi_cons_vars = [],
					   tdi_classification = EmptyTypeClassification, tdi_group_nr = cNotAGroupNumber, tdi_index_in_group = NoIndex, tdi_mark=False, tdi_gen_rep = No }

MakeTypeVar name :== { tv_name = name, tv_info_ptr = nilPtr }
MakeVar name :== { var_name = name, var_info_ptr = nilPtr, var_expr_ptr = nilPtr }

MakeAttributedType type :== { at_attribute = TA_None, at_type = type }
MakeAttributedTypeVar type_var :== { atv_attribute = TA_None, atv_variable = type_var }

EmptyFunInfo :== { fi_calls = [], fi_group_index = NoIndex, fi_def_level = NotALevel,
				   fi_free_vars = [], fi_local_vars = [], fi_dynamics = [], fi_properties=0 }

BottomSignClass		:== { sc_pos_vect = 0, sc_neg_vect = 0 }
PostiveSignClass	:== { sc_pos_vect = bitnot 0, sc_neg_vect = 0 }

NoPropClass			:== 0
PropClass			:== bitnot 0

newTypeSymbIdentCAF :: TypeSymbIdent;
newTypeSymbIdentCAF =: MakeTypeSymbIdentMacro { glob_object = NoIndex, glob_module = NoIndex } {id_name="",id_info=nilPtr} 0

MakeNewTypeSymbIdent name arity
	:== {newTypeSymbIdentCAF & type_name=name, type_arity=arity }

MakeTypeSymbIdent type_index name arity
	:== {	newTypeSymbIdentCAF & type_name = name, type_arity = arity, type_index = type_index }

MakeTypeSymbIdentMacro type_index name arity
	:== {	type_name = name, type_arity = arity, type_index = type_index,
			type_prop = { tsp_sign = BottomSignClass, tsp_propagation = NoPropClass, tsp_coercible = True }}

ParsedSelectorToSelectorDef sd_type_index ps :==
	{	sd_symb = ps.ps_selector_name, sd_field_nr = NoIndex, sd_pos =  ps.ps_field_pos, sd_type_index = sd_type_index,
		sd_exi_vars = [], sd_type_ptr = nilPtr, sd_field = ps.ps_field_name,
		sd_type	= { st_vars = [], st_args = [], st_args_strictness=NotStrict, st_result = ps.ps_field_type, st_arity = 0, st_context = [],
				    st_attr_env = [], st_attr_vars = [] }}

ParsedConstructorToConsDef pc :==
	{	cons_symb = pc.pc_cons_name, cons_pos = pc.pc_cons_pos, cons_priority = pc.pc_cons_prio, cons_index = NoIndex, cons_type_index = NoIndex,
		cons_type = { st_vars = [], st_args = pc.pc_arg_types, st_args_strictness=pc.pc_args_strictness, st_result = MakeAttributedType TE, 
				  st_arity = pc.pc_cons_arity, st_context = [], st_attr_env = [], st_attr_vars = []},
		cons_exi_vars = pc.pc_exi_vars, cons_type_ptr = nilPtr, cons_arg_vars = [] }

ParsedInstanceToClassInstance pi members :==
 	{	ins_class = {glob_object = MakeDefinedSymbol pi.pi_class NoIndex (length pi.pi_types), glob_module = NoIndex}, ins_ident = pi.pi_ident, 
 		ins_type = { it_vars = [], it_types = pi.pi_types, it_attr_vars = [],
 					 it_context = pi.pi_context }, 
 		ins_members = members, ins_specials = pi.pi_specials, ins_pos = pi.pi_pos}

MakeTypeDef name lhs rhs attr contexts pos  :== 
	{	td_name = name, td_index = -1, td_arity = length lhs, td_args = lhs, td_attrs = [], td_attribute = attr, td_context = contexts,
		td_pos = pos, td_rhs = rhs, td_used_types = [] }

MakeDefinedSymbol ident index arity :== { ds_ident = ident, ds_arity = arity, ds_index = index }

MakeNewFunctionType name arity prio type pos specials var_ptr
	:== { ft_symb = name, ft_arity = arity, ft_priority = prio, ft_type = type, ft_pos = pos, ft_specials = specials, ft_type_ptr = var_ptr  }

backslash :== '\\'
