definition module syntax

import StdEnv

import scanner, general, typeproperties, Heap

::	Ident =
	{ 	id_name		:: !String
	,	id_info 	:: !SymbolPtr
	}

instance toString Ident


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

::	STE_BoundTypeVariable	= { stv_count :: !Int, stv_attribute :: !TypeAttribute, stv_info_ptr :: !TypeVarInfoPtr }

::	STE_Kind	= STE_FunctionOrMacro ![Index]
				| STE_Type
				| STE_Constructor
				| STE_Selector ![Global Index]
				| STE_Field !Ident
				| STE_Class
				| STE_Member
				| STE_Generic			// AA: For generic declarations
				| STE_Instance !Ident // argument: the class (used in explicitimports (1.3 syntax only))
				| STE_Variable !VarInfoPtr
				| STE_TypeVariable !TypeVarInfoPtr
				| STE_TypeAttribute !AttrVarInfoPtr
				| STE_BoundTypeVariable !STE_BoundTypeVariable
				| STE_Imported !STE_Kind !Index
				| STE_DclFunction
				| STE_Module !(Module (CollectedDefinitions ClassInstance IndexRange))
				| STE_ClosedModule
				| STE_Empty
					/* for creating class dictionaries */
				| STE_DictType !CheckedTypeDef
				| STE_DictCons !ConsDef
				| STE_DictField !SelectorDef
				| STE_Called ![Index] /* used during macro expansion to indicate that this function is called */
				| STE_ExplImpSymbol !Int
				| STE_ExplImpComponentNrs ![ComponentNrAndIndex] ![Declaration]
					/*	stores the numbers of all module components that import the symbol from
						the "actual" dcl module. Further for each class all encountered
						instances are accumulated.
					*/
				| STE_BelongingSymbol !Int
				
				| STE_UsedType !Index !STE_Kind
					/* used during binding of types to mark types that have been applied. The first  */

::	Declaration = Declaration !DeclarationRecord

::	DeclarationRecord =
	{	decl_ident	:: !Ident
	,	decl_pos	:: !Position
	,	decl_kind	:: !STE_Kind
	,	decl_index	:: !Index
	}

::	ComponentNrAndIndex =
	{	cai_component_nr	:: !Int
	,	cai_index			:: !Int // points into ExplImpInfos
	}

::	Global object =
	{	glob_object	:: !object
	,	glob_module	:: !Index
	}
	
::	Module defs = 
	{	mod_name		:: !Ident
	,	mod_type		:: !ModuleKind
	, 	mod_imports		:: ![ParsedImport]
	,	mod_imported_objects :: ![ImportedObject]
	,	mod_defs		:: !defs
	}

::	ParsedModule	:== Module  [ParsedDefinition]
::	ScannedModule 	:== Module  (CollectedDefinitions (ParsedInstance FunDef) IndexRange)
	
::	ModuleKind		= MK_Main | MK_Module | MK_System | MK_None | MK_NoMainDcl

::	RhsDefsOfType	= ConsList ![ParsedConstructor]
					| SelectorList !Ident ![ATypeVar] ![ParsedSelector]
					| TypeSpec !AType
					| EmptyRhs !BITVECT

::	CollectedDefinitions instance_kind macro_defs =
	{	def_types 			:: ![TypeDef TypeRhs]
	,	def_constructors	:: ![ConsDef]
	,	def_selectors		:: ![SelectorDef]
	,	def_macros			:: !macro_defs
	,	def_classes			:: ![ClassDef]
	,	def_members			:: ![MemberDef]
	,	def_generics		:: ![GenericDef] // AA
	,	def_funtypes		:: ![FunType]
	,	def_instances		:: ![instance_kind]
	}

::	LocalDefs	= LocalParsedDefs [ParsedDefinition]
				| CollectedLocalDefs CollectedLocalDefs

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
	|	PD_Generic GenericDef // AA
	|	PD_Instance (ParsedInstance ParsedDefinition)
	|	PD_Instances [ParsedInstance ParsedDefinition]
	|	PD_Import [ParsedImport]
	|	PD_ImportedObjects [ImportedObject]
	|	PD_Erroneous

::	FunKind = FK_Function !Bool | FK_Macro | FK_Caf | FK_Unknown

::	DefOrImpFunKind = FK_DefFunction !Bool| FK_ImpFunction !Bool | FK_DefMacro | FK_ImpMacro | FK_ImpCaf | FK_DefOrImpUnknown

cNameNotLocationDependent :== False
cNameLocationDependent :== True

::	ParsedSelector =
	{	ps_field_name		:: !Ident
	,	ps_selector_name	:: !Ident
	,	ps_field_type		:: !AType
	,	ps_field_var		:: !Ident
	,	ps_field_pos		:: !Position
	}

::	ParsedConstructor =
	{	pc_cons_name 	:: !Ident
	,	pc_cons_arity	:: !Int
	,	pc_exi_vars		:: ![ATypeVar]
	,	pc_arg_types	:: ![AType]
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
	,	pi_generate  :: !Bool // AA: instance is to be generated
	}

/*
	Objects of type Specials are used to specify specialized instances of overloaded functions.
	These can only occur in definition modules. After parsing the SP_ParsedSubstitutions alternative
	is used to indicate the specific instantiation. The SP_Substitutions alternative is used to deduce
	the type of the specialized version. Finally the SP_ContextTypes alternative is set and used during 
	the typing to check whether this instance has been used. The auxiliary SP_FunIndex alternative is used
	to store the index of the function that has been specialized.
*/


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

// AA ... 

::	GenericDef = 
	{	gen_name		:: !Ident				// the generics name in the IC_Class
	,	gen_member_name	:: !Ident				// the generics name in the IC_Member
	,	gen_type		:: !GenericType
	, 	gen_pos			:: !Position
	,	gen_kinds_ptr	:: !TypeVarInfoPtr		// hack: contains all used kinds 
	,	gen_cons_ptr 	:: !TypeVarInfoPtr		// hack: cons instance function
	, 	gen_classes		:: !GenericClassInfos 	// generated classes
	,	gen_isomap		:: !DefinedSymbol		// isomap function
	}

:: GenericType = 
	{	gt_type 		:: !SymbolType
	,	gt_vars			:: ![TypeVar]			// generic arguments
	,	gt_arity		:: !Int					// number of generic arguments	
	}
	
:: GenericClassInfo = 
	{	gci_kind 	:: !TypeKind
	,	gci_class	:: !DefinedSymbol
	}
:: GenericClassInfos :== [GenericClassInfo] 	 

getGenericClassForKind 	:: !GenericDef !TypeKind -> (!Bool, DefinedSymbol)
addGenericKind			:: !GenericDef !TypeKind -> !GenericDef

// ... AA

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
	,	ins_is_generic	:: !Bool				//AA 
	, 	ins_generate	:: !Bool				//AA
	,	ins_partial		:: !Bool				//AA
	,	ins_generic		:: !Global Index		//AA 	
	}

/*
::	Export =
	{	export_class	:: Ident
	,	export_types	:: [Type]
	}
*/
::	Import from_symbol =
	{	import_module		:: !Ident
	,	import_symbols		:: ![from_symbol]
	,	import_file_position:: !Position	// for error messages
	}

instance toString (Import from_symbol), AttributeVar, TypeAttribute, Annotation

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

::	ParsedTypeDef	:== TypeDef RhsDefsOfType
::	CheckedTypeDef	:== TypeDef TypeRhs

cAllBitsClear			:== 0
cIsHyperStrict			:== 1
cIsNonCoercible			:== 2
cIsAnalysed				:== 4

::	GlobalIndex =
	{	gi_module	::!Int
	,	gi_index	::!Int
	}

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

::	TypeDefInfo =
	{	tdi_kinds			:: ![TypeKind]
	,	tdi_properties		:: !BITVECT
	,	tdi_group			:: ![GlobalIndex]
	,	tdi_group_nr		:: !Int
	,	tdi_group_vars		:: ![Int]
	,	tdi_cons_vars		:: ![Int]
	,	tdi_index_in_group	:: !Index
	,	tdi_classification	:: !TypeClassification
	}

::	TypeDefInfos :== {# .{# TypeDefInfo}}

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
//	,	fv_expr_ptr		:: !ExprInfoPtr
	,	fv_count		:: !Int
	}
	
::	FunCall =
	{	fc_level	:: !Level
	,	fc_index	:: !Index
	}

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
	{	pb_args		:: ![ParsedExpr]
	,	pb_rhs		:: !Rhs
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
					| PartioningMacro
					| PartioningFunction !CheckedBody !Int
					| RhsMacroBody !CheckedBody
	/* macro expansion transforms a CheckedBody into a TransformedBody */
					| TransformedBody !TransformedBody
					| Expanding ![FreeVar] // the parameters of the newly generated function
					| BackendBody ![BackendBody]
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
	,	fun_kind		:: !DefOrImpFunKind
	,	fun_lifted		:: !Int
	,	fun_info		:: !FunInfo
	}

cIsAGlobalVar	:== True
cIsALocalVar	:== False

::	ConsClasses =
	{	cc_size			::!Int
	,	cc_args			::![ConsClass]
	,	cc_linear_bits	::![Bool]
	}
					
::	ConsClass	:== Int

::	OptionalVariable :== Optional (Bind Ident VarInfoPtr)

:: 	AuxiliaryPattern
		= AP_Algebraic !(Global DefinedSymbol) !Index [AuxiliaryPattern] OptionalVariable
		| AP_Variable !Ident !VarInfoPtr OptionalVariable
		| AP_Basic !BasicValue OptionalVariable
		| AP_Dynamic !AuxiliaryPattern !DynamicType !OptionalVariable
		| AP_Constant !AP_Kind !(Global DefinedSymbol) !Priority
		| AP_WildCard !OptionalVariable
		| AP_Empty !Ident

:: AP_Kind = APK_Constructor !Index | APK_Macro

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

/*
cRecursiveAppl		:== True
cNonRecursiveAppl	:== False	

::	ApplicationKind	:== Bool
*/
 
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
				| SK_LocalMacroFunction !Index
				| SK_OverloadedFunction !(Global Index)
				| SK_Generic !(Global Index) !TypeKind		// AA
				| SK_Constructor !(Global Index)
				| SK_Macro !(Global Index)
//				| SK_RecordSelector !(Global Index)
				| SK_GeneratedFunction !FunctionInfoPtr !Index
				| SK_TypeCode

/*	Some auxiliary type definitions used during fusion. Actually, these definitions
	should have been given in seperate module. Unfortunately, Clean's module system
	forbids cyclic dependencies between def modules.
	
*/

::	FunctionHeap 	:== Heap FunctionInfo

::	FunctionInfoPtr	:== Ptr FunctionInfo

::	FunctionInfo	= FI_Empty | FI_Function !GeneratedFunction

::	Producer	= PR_Empty
				| PR_Function !SymbIdent !Index
				| PR_Class !App ![(BoundVar, Type)] !Type
//				| PR_Constructor !SymbIdent ![Expression]
				| PR_GeneratedFunction !SymbIdent !Index
				| PR_Curried !SymbIdent

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
//					| EI_Selection 	![Selection] !BoundVar ![Expression]	/* intermedediate, used during resolving of overloading */
					| EI_Selection 	![Selection] !VarInfoPtr ![Expression]	/* intermedediate, used during resolving of overloading */
					| EI_Context 	![Expression]							/* intermedediate, used during resolving of overloading */

		/* For handling dynamics */

					| EI_Dynamic 				!(Optional DynamicType) !Int
					| EI_DynamicType			!DynamicType ![DynamicPtr]
//					| EI_DynamicType			!DynamicType !(Optional ExprInfoPtr)

		/* Auxiliary, was EI_DynamicType before checking */

					| EI_DynamicTypeWithVars	![TypeVar] !DynamicType ![DynamicPtr]				
//					| EI_DynamicTypeWithVars	![TypeVar] !DynamicType !(Optional ExprInfoPtr)			

		/* Auxiliary, used during type checking */

					| EI_TempDynamicType 		!(Optional DynamicType) !AType ![TypeContext] !ExprInfoPtr !SymbIdent
//					| EI_TempDynamicPattern 	![TypeVar] !DynamicType !(Optional ExprInfoPtr) ![TempLocalVar] !AType ![TypeContext] !ExprInfoPtr !SymbIdent
					| EI_TempDynamicPattern 	![TypeVar] !DynamicType ![DynamicPtr] ![TempLocalVar] !AType ![TypeContext] !ExprInfoPtr !SymbIdent
					
					| EI_TypeOfDynamic 			![VarInfoPtr] !TypeCodeExpression				/* Final */
					| EI_TypeOfDynamicPattern 	![VarInfoPtr] !TypeCodeExpression				/* Final */

					| EI_TypeCode 		!TypeCodeExpression
					| EI_TypeCodes 		![TypeCodeExpression]

					| EI_Attribute !Int

		/* EI_DictionaryType is used to store the instance type of a class. This type is used during fusion to generate proper types for 
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
::	UnboundVariable =
	{	free_name		:: !Ident
	,	free_info_ptr	:: !VarInfoPtr
	,	free_selections	:: ![Int]
	}
*/

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
	,	symb_arity		:: !Int
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
	,	st_arity		:: !Int
	,	st_result		:: !AType
	,	st_context		:: ![TypeContext]
	,	st_attr_vars	:: ![AttributeVar]
	,	st_attr_env		:: ![AttrInequality]
	}

::	TypeContext =
	{	tc_class	:: !Global DefinedSymbol
	,	tc_types	:: ![Type]
	,	tc_var		:: !VarInfoPtr
	}

::	AType =
	{	at_attribute	:: !TypeAttribute
	,	at_annotation	:: !Annotation
	,	at_type			:: !Type
	}
	
::	TempAttrId		:== Int
::	TempVarId		:== Int


::	Type	=	TA !TypeSymbIdent ![AType]
			|	(-->) infixr 9 !AType !AType
			| 	TArrow							/* (->) */
			| 	TArrow1	!AType					/* ((->) a) */
			|	(:@:) infixl 9 !ConsVariable ![AType]
			|	TB !BasicType

			|	TFA [ATypeVar] Type				/* Universally quantified types */

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
				| KI_Arrow ![KindInfo]
				| KI_Const
				
				| KI_ConsVar
				
				| KI_VarBind !KindInfoPtr
				| KI_NormVar !Int

::	TypeVarInfo  	= TVI_Empty
					| TVI_Type !Type
					| TVI_TypeVar !TypeVarInfoPtr // Sjaak: to collect and check universally quantified type variables
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
	,	atv_annotation		:: !Annotation
	,	atv_variable		:: !TypeVar
	}

::	TypeAttribute = TA_Unique | TA_Multi | TA_Var !AttributeVar | TA_RootVar AttributeVar | TA_TempVar !Int // | TA_TempExVar !Int
					| TA_Anonymous | TA_None
					| TA_List !Int !TypeAttribute | TA_Locked !TypeAttribute
					| TA_MultiOfPropagatingConsVar // only filled in after type checking, semantically equal to TA_Multi
					| TA_PA_BUG
							
::	AttributeVar =
	{	av_name			:: !Ident
	,	av_info_ptr		:: !AttrVarInfoPtr
	}

::	Annotation	=  AN_Strict | AN_None 

::	BasicType	= BT_Int | BT_Char | BT_Real | BT_Bool | BT_Dynamic
				| BT_File | BT_World
				| BT_String !Type /* the internal string type synonym only used to type string denotations */

::	BasicValue	= BVI !String | BVC !String | BVB !Bool | BVR !String | BVS !String

::	TypeKind = KindVar !KindInfoPtr | KindConst | KindArrow ![TypeKind]

instance toString 	TypeKind
instance <<< 		TypeKind
instance == 		TypeKind
instance toString 	KindInfo

/* A few obscure type definitions */

::	Occurrence =
	{	occ_ref_count	:: !ReferenceCount
//	,	occ_aliases		:: ![[(FreeVar,Int)]]
//	,	occ_expression	:: !Expression
	,	occ_bind		:: !OccurrenceBinding
	,	occ_observing	:: !Bool
//	,	occ_attribute	:: !ExprInfoPtr
	,	occ_previous 	:: ![ReferenceCount]
	}

::	ReferenceCount = RC_Used !RC_Used | RC_Unused 

::	SelectiveUse = { su_field :: !Int, su_multiply :: ![ExprInfoPtr], su_uniquely :: ![ExprInfoPtr]  }

::	RC_Used = { rcu_multiply :: ![ExprInfoPtr], rcu_selectively :: ![SelectiveUse], rcu_uniquely :: ![ExprInfoPtr] }

::	OccurrenceBinding	= OB_Empty | OB_OpenLet !Expression | OB_LockedLet !Expression
						| OB_Pattern ![(FreeVar, Int)] !OccurrenceBinding
//						| OB_Closed !LetOccurrences | OB_Marked !LetOccurrences

/*
::	LetOccurrences =
	{	lo_used_lets		:: ![FreeVar]
	,	lo_free_variables	:: ![(FreeVar, ReferenceCount)]
	}
*/
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

cUniqueSelection	:== True
cNonUniqueSelection	:== False

::	ParsedExpr	= PE_List ![ParsedExpr]
				| PE_Ident !Ident
				| PE_Basic !BasicValue
				| PE_Bound !BoundExpr
				| PE_Lambda !Ident ![ParsedExpr] !ParsedExpr !Position
				| PE_Tuple ![ParsedExpr]				
				| PE_Record !ParsedExpr !(Optional Ident) ![FieldAssignment]
				| PE_ArrayPattern ![ElemAssignment]
				| PE_UpdateComprehension !ParsedExpr !ParsedExpr !ParsedExpr ![Qualifier]
				| PE_ArrayDenot ![ParsedExpr]
				| PE_Selection !Bool !ParsedExpr ![ParsedSelection]
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

::	GeneratorKind :== Bool

IsListGenerator 	:== True
IsArrayGenerator	:== False
			
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


cIsStrict		:== True
cIsNotStrict	:== False

/*
::	SelectorKind	= SEK_Normal | SEK_First | SEK_Next | SEK_Last

::	ArraySelector	= DictionarySelection !(Global DefinedSymbol) !Int !Expression
					| SelectorInstance !(Global DefinedSymbol)
*/
::	Expression	= Var !BoundVar 
				| App !App
				| (@) infixl 9  !Expression ![Expression]
				| Let !Let
				| Case !Case
				| Selection !(Optional (Global DefinedSymbol)) !Expression ![Selection]
							// Yes: a "!" selection
				| Update !Expression ![Selection] Expression
				| RecordUpdate !(Global DefinedSymbol) !Expression ![Bind Expression (Global FieldSymbol)]
				| TupleSelect !DefinedSymbol !Int !Expression
//				| Lambda .[FreeVar] !Expression
				| BasicExpr !BasicValue !BasicType
				| WildCard
				| Conditional !Conditional

				| AnyCodeExpr !(CodeBinding BoundVar) !(CodeBinding FreeVar) ![String]
				| ABCCodeExpr ![String] !Bool

				| MatchExpr !(Optional (Global DefinedSymbol)) !(Global DefinedSymbol) !Expression
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
//	,	case_guards		:: ![PatternExpression]
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

::	Conditional =
	{	if_cond		:: !Expression
	,	if_then		:: !Expression
	,	if_else		:: !Optional Expression
	}

/*
::	Conditional =
	{	if_cond		:: !Condition
	,	if_then		:: !Expression
	,	if_else		:: !Optional Expression
	}


::	Condition =
	{	con_positive 	:: !Bool
	,	con_expression	:: !Expression
	}
*/

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

instance == OverloadedListType

::	Selection	= RecordSelection !(Global DefinedSymbol) !Int
				| ArraySelection !(Global DefinedSymbol) !ExprInfoPtr !Expression
				| DictionarySelection !BoundVar ![Selection] !ExprInfoPtr !Expression

::	TypeCodeExpression	= TCE_Empty
						| TCE_Var 			!VarInfoPtr
						| TCE_TypeTerm		!VarInfoPtr
						| TCE_Constructor	!Index			![TypeCodeExpression]
						| TCE_Selector		![Selection]	!VarInfoPtr
						| TCE_UniType 		![VarInfoPtr] 	!TypeCodeExpression

::	GlobalTCType = GTT_Basic !BasicType	| GTT_Constructor !TypeSymbIdent !String | GTT_Function
	

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

instance == ModuleKind, Ident
instance <<< (Module a) | <<< a, ParsedDefinition, InstanceType, AttributeVar, TypeVar, SymbolType, Expression, Type, Ident, (Global object) | <<< object,
			 Position, CaseAlt, AType, FunDef, ParsedExpr, TypeAttribute, (Bind a b) | <<< a & <<< b, ParsedConstructor, (TypeDef a) | <<< a, TypeVarInfo,
			 BasicValue, ATypeVar, TypeRhs, FunctionPattern, (Import from_symbol) | <<< from_symbol, ImportDeclaration, ImportedIdent, CasePatterns,
			 (Optional a) | <<< a, ConsVariable, BasicType, Annotation, Selection, SelectorDef, ConsDef, LocalDefs, FreeVar, ClassInstance, SignClassification,
			 TypeCodeExpression, CoercionPosition, AttrInequality, LetBind, Declaration, STE_Kind, BoundVar

instance <<< FunctionBody

instance == TypeAttribute
instance == Annotation
instance == GlobalIndex

/*
ErrorToString :: Error -> String

*/

EmptySymbolTableEntry :== EmptySymbolTableEntryCAF.boxed_symbol_table_entry

::BoxedSymbolTableEntry = {boxed_symbol_table_entry::!SymbolTableEntry}

EmptySymbolTableEntryCAF :: BoxedSymbolTableEntry

cNotAGroupNumber :== -1

EmptyTypeDefInfo :== { tdi_kinds = [], tdi_properties = cAllBitsClear, tdi_group = [], tdi_group_vars = [], tdi_cons_vars = [],
					   tdi_classification = EmptyTypeClassification, tdi_group_nr = cNotAGroupNumber, tdi_index_in_group = NoIndex }

MakeTypeVar name	:== { tv_name = name, tv_info_ptr = nilPtr }
MakeVar name		:== { var_name = name, var_info_ptr = nilPtr, var_expr_ptr = nilPtr }

MakeAttributedType type :== { at_attribute = TA_None, at_annotation = AN_None, at_type = type }
MakeAttributedTypeVar type_var :== { atv_attribute = TA_None, atv_annotation = AN_None, atv_variable = type_var }

EmptyFunInfo :== { fi_calls = [], fi_group_index = NoIndex, fi_def_level = NotALevel,
				   fi_free_vars = [], fi_local_vars = [], fi_dynamics = [], fi_properties=0 }

BottomSignClass		:== { sc_pos_vect = 0, sc_neg_vect = 0 }
PostiveSignClass	:== { sc_pos_vect = bitnot 0, sc_neg_vect = 0 }

NoPropClass			:== 0
PropClass			:== bitnot 0

newTypeSymbIdentCAF :: TypeSymbIdent;

MakeNewTypeSymbIdent name arity
	:== {newTypeSymbIdentCAF & type_name=name, type_arity=arity }

MakeTypeSymbIdent type_index name arity
	:== {	newTypeSymbIdentCAF & type_name = name, type_arity = arity, type_index = type_index }

MakeSymbIdent name arity	:== { symb_name = name, symb_kind = SK_Unknown, symb_arity = arity  }
MakeConstant name			:== MakeSymbIdent name 0

ParsedSelectorToSelectorDef sd_type_index ps :==
	{	sd_symb = ps.ps_selector_name, sd_field_nr = NoIndex, sd_pos =  ps.ps_field_pos, sd_type_index = sd_type_index,
		sd_exi_vars = [], sd_type_ptr = nilPtr, sd_field = ps.ps_field_name,
		sd_type	= { st_vars = [], st_args = [], st_result = ps.ps_field_type, st_arity = 0, st_context = [],
				    st_attr_env = [], st_attr_vars = [] }}

ParsedConstructorToConsDef pc :==
	{	cons_symb = pc.pc_cons_name, cons_pos = pc.pc_cons_pos, cons_priority = pc.pc_cons_prio, cons_index = NoIndex, cons_type_index = NoIndex,
		cons_type = { st_vars = [], st_args = pc.pc_arg_types, st_result = MakeAttributedType TE, 
				  st_arity = pc.pc_cons_arity, st_context = [], st_attr_env = [], st_attr_vars = []},
		cons_exi_vars = pc.pc_exi_vars, cons_type_ptr = nilPtr, cons_arg_vars = [] }

ParsedInstanceToClassInstance pi members :==
 	{	ins_class = {glob_object = MakeDefinedSymbol pi.pi_class NoIndex (length pi.pi_types), glob_module = NoIndex}, ins_ident = pi.pi_ident, 
 		ins_type = { it_vars = [], it_types = pi.pi_types, it_attr_vars = [],
 					 it_context = pi.pi_context }, ins_members = members, ins_specials = pi.pi_specials, ins_pos = pi.pi_pos, 
 		/*AA*/
 		ins_is_generic = False, 
 		ins_generate = pi.pi_generate,
 		ins_partial = False, 
 		ins_generic = {glob_module = NoIndex, glob_object = NoIndex}}

MakeTypeDef name lhs rhs attr contexts pos  :== 
	{	td_name = name, td_index = -1, td_arity = length lhs, td_args = lhs, td_attrs = [], td_attribute = attr, td_context = contexts,
		td_pos = pos, td_rhs = rhs, td_used_types = [] }

MakeDefinedSymbol ident index arity :== { ds_ident = ident, ds_arity = arity, ds_index = index }

MakeNewFunctionType name arity prio type pos specials var_ptr
	:== { ft_symb = name, ft_arity = arity, ft_priority = prio, ft_type = type, ft_pos = pos, ft_specials = specials, ft_type_ptr = var_ptr  }

backslash :== '\\'
