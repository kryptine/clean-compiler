# include "system.h"
# include "syntaxtr.t"
# include "buildtree.h"

# include "dumprestore.h"

# ifdef DUMP_AND_RESTORE

# include "comsupport.h"
# include "checker.h"

# include "backendsupport.h"
# define Clean(ignore)
# include "backend.h"


Bool gDumpAndRestore = True;

/*
	Utilities
	=========
*/
# define	CopyContents(from, to) { *(to) = *(from);}

/*
	Memory management
	=================
*/
static CleanString
ConvertCString (char *string)
{
	int			length;
	CleanString	cleanString;

	length		= strlen (string);
	cleanString	= (CleanString) CompAlloc (sizeof (CleanString) + length);
	cleanString->length	= length;
	strncpy (cleanString->chars, string, length);

	return (cleanString);
} /* ConvertCString */

/*
	Forward declarations
	====================
*/
static SymbDefP ConvertSymbDef (SymbDefP sdef);
static TypeNode ConvertTypeNode (TypeNode node);
static NodeP ConvertNode (NodeP node);
static NodeDefP ConvertNodeDefs (NodeDefP nodeDefs);
static int DefineLhsNode (NodeP node, int sequenceNumber);

/*
	Symbol
	======
*/

static void
SetSymbolIndices (SymbolP symbol, int symbolIndex, int moduleIndex)
{
	unsigned int	indices;

	Assert (0 <= moduleIndex && moduleIndex <= 0xFFFF);
	Assert (0 <= symbolIndex && symbolIndex <= 0xFFFF);
	Assert (symbol->symb_kind == definition);

	indices	= symbolIndex | (moduleIndex << 16);

	symbol->symb_def->sdef_number	= indices;
} /* SetSymbolIndices */

static void
GetSymbolIndices (SymbolP symbol, int *symbolIndexP, int *moduleIndexP)
{
	unsigned int	indices;

	Assert (symbol->symb_kind == definition);
	indices	=	(unsigned int) symbol->symb_def->sdef_number;

	*symbolIndexP	= indices & 0xFFFF;
	*moduleIndexP	= (indices >> 16) & 0xFFFF;
} /* GetSymbolIndices */

static SymbolP
ConvertSymbol (SymbolP symbol)
{
	SymbolP	copy;
	int	symbolIndex, moduleIndex;

	Assert (!IsConverted (symbol));
	switch (symbol->symb_kind)
	{
		case definition:
			switch (symbol->symb_def->sdef_kind)
			{
				case ABSTYPE:
					copy	= BEDontCareDefinitionSymbol ();
					break;
				case TYPE:
				case RECORDTYPE:
					GetSymbolIndices (symbol, &symbolIndex, &moduleIndex);
					copy	= BETypeSymbol (symbolIndex, moduleIndex);
					break;
				case TYPESYN:
					break;
				case DEFRULE:
				case IMPRULE:
				case SYSRULE:	/* +++ */
					GetSymbolIndices (symbol, &symbolIndex, &moduleIndex);
					copy	= BEFunctionSymbol (symbolIndex, moduleIndex);
					break;
				case CONSTRUCTOR:
					GetSymbolIndices (symbol, &symbolIndex, &moduleIndex);
					copy	= BEConstructorSymbol (symbolIndex, moduleIndex);
					break;
					break;
				case FIELDSELECTOR:
					GetSymbolIndices (symbol, &symbolIndex, &moduleIndex);
					copy	= BEFieldSymbol (symbolIndex, moduleIndex);
					break;
				case MACRORULE:
					break;
				case OVERLOADEDRULE:
					break;
				case INSTANCE:
					break;
				case CLASS:
					break;
				case CLASSINSTANCE:
					break;
				case CLASSLIST:
					break;
				default:
					Assert (False);
					break;
			}
			break;

		/* literals */
		case int_denot:
		case char_denot:
		case real_denot:
		case string_denot:
			copy	= BELiteralSymbol ((SymbKind) symbol->symb_kind, ConvertCString (symbol->symb_int));
			break;

		/* basic symbols +++ some of these should be moved to the predefined module */
		case int_type:
		case bool_type:
		case char_type:
		case real_type:
		case file_type:
		case world_type:
		case procid_type:
		case redid_type:
		case fun_type:

		case array_type:
		case strict_array_type:
		case unboxed_array_type:
			
		case tuple_type:
		case tuple_symb:
			copy	= BEBasicSymbol ((SymbKind) symbol->symb_kind);
			break;

		/* symbols from the predefined module */
		case list_type:
			copy	= BETypeSymbol (0, kPredefinedModuleIndex);
			break;
		case nil_symb:
			copy	= BEConstructorSymbol (0, kPredefinedModuleIndex);
			break;
		case cons_symb:
			copy	= BEConstructorSymbol (1, kPredefinedModuleIndex);
			break;


		default:
			Assert (False);
			break;
	}

	return (copy);
} /* ConvertSymbol */

/*
	TypeArg
	=======
*/
static TypeArgs
ConvertTypeArgs (TypeArgs args)
{
	TypeArgs	copy;

	if (args == NULL)
		copy	= BENoTypeArgs ();
	else
		copy	= BETypeArgs (ConvertTypeNode (args->type_arg_node), ConvertTypeArgs (args->type_arg_next));

	return (copy);
} /* ConvertTypeArgs */

/*
	TypeNode
	========
*/
static TypeNode
ConvertTypeNode (TypeNode node)
{
	TypeNode	copy;

	Assert (!IsConverted (node));

	if (node->type_node_is_var)
	{
		Assert (node->type_node_arguments== NULL);
		copy	= BEVarTypeNode (ConvertCString (node->type_node_tv->tv_ident->ident_name));
	}
	else
		copy	= BENormalTypeNode (ConvertSymbol (node->type_node_symbol), ConvertTypeArgs (node->type_node_arguments));

	Assert (node->type_node_annotation == NoAnnot || node->type_node_annotation == StrictAnnot);
	copy	= BEAnnotateTypeNode (node->type_node_annotation, copy);

	return (copy);
} /* ConvertTypeNode */

/*
	TypeAlt
	=======
*/
static TypeAlt *
ConvertTypeAlt (TypeAlt *typeAlt)
{
	TypeAlt	*copy;

	Assert (!IsConverted (typeAlt));

	copy	= BETypeAlt (ConvertTypeNode (typeAlt->type_alt_lhs), ConvertTypeNode (typeAlt->type_alt_rhs));

	return (copy);
} /* ConvertTypeAlt */

/*
	Arg
	===
*/
static ArgP
ConvertArgs (ArgP args)
{
	ArgP	copy;

	if (args == NULL)
		copy	= BENoArgs ();
	else
		copy	= BEArgs (ConvertNode (args->arg_node), ConvertArgs (args->arg_next));

	return (copy);
} /* ConvertArgs */

/*
	NodeIds
*/

static int
DefineNodeIds (NodeDefP nodeDef, int lhsOrRhs, int sequenceNumber)
{
	for ( ; nodeDef != NULL; nodeDef = nodeDef->def_next)
	{
		NodeIdP	nodeId;

		nodeId	= nodeDef->def_id;
		nodeId->nid_scope	= sequenceNumber;

		/* RWS ??? Assert (nodeId->nid_mark == 0); */

		BEDeclareNodeId (sequenceNumber, lhsOrRhs, ConvertCString (nodeId->nid_ident->ident_name));
		sequenceNumber++;
	}
	return (sequenceNumber);
} /* DefineNodeIds */

static int
DefineLhsNodeId (NodeIdP nodeId, int sequenceNumber)
{
	Assert (nodeId->nid_refcount < 0);
	Assert (nodeId->nid_node_def == NULL);
	/* RWS ??? Assert (nodeId->nid_forward_node_id == NULL); */
	Assert (nodeId->nid_state.state_arity == 0);
	Assert (nodeId->nid_state.state_kind == 0);
	Assert (nodeId->nid_state.state_mark == 0);
	Assert (nodeId->nid_state.state_object == 0);
	Assert (nodeId->nid_state.state_type == 0);

	if (nodeId->nid_node == NULL)
	{
		nodeId->nid_scope	= sequenceNumber;
		BEDeclareNodeId (sequenceNumber, BELhsNodeId, ConvertCString (nodeId->nid_ident->ident_name));
		sequenceNumber++;
	}

	return (sequenceNumber);
} /* DefineLhsNodeId */

static int
DefineLhsArgs (ArgP arg, int sequenceNumber)
{
	for ( ; arg != NULL; arg = arg->arg_next)
		sequenceNumber	= DefineLhsNode (arg->arg_node, sequenceNumber);

	return (sequenceNumber);
} /* DefineLhsArgs */

static int
DefineLhsNode (NodeP node, int sequenceNumber)
{
	switch (node->node_kind)
	{
		case NodeIdNode:
			sequenceNumber	= DefineLhsNodeId (node->node_node_id, sequenceNumber);
			break;
		case NormalNode:
			break;
		default:
			Assert (False);
			break;
	}

	sequenceNumber	= DefineLhsArgs (node->node_arguments, sequenceNumber);

	return (sequenceNumber);
} /* DefineLhsNode */

static NodeIdP
ConvertNodeId (NodeIdP nodeId)
{
	Assert (!IsConverted (nodeId));

	return (BENodeId (nodeId->nid_scope));
} /* ConvertNodeId*/


/*
	RuleAlt
	=======
*/

static RuleAlts
ConvertRuleAlt (RuleAltP alt)
{
	RuleAltP	copy;

	int	sequenceNumber;

	Assert (!IsConverted (alt));

	Assert (alt->alt_kind == Contractum);
	Assert (alt->alt_strict_node_ids == NULL);

	sequenceNumber	= 0;
	sequenceNumber	= DefineNodeIds (alt->alt_lhs_defs, BELhsNodeId, sequenceNumber);
	sequenceNumber	= DefineNodeIds (alt->alt_rhs_defs, BERhsNodeId, sequenceNumber);
	sequenceNumber	= DefineLhsArgs (alt->alt_lhs_root->node_arguments, sequenceNumber);

	copy	= BERuleAlt (alt->alt_line, ConvertNodeDefs (alt->alt_lhs_defs), ConvertNode (alt->alt_lhs_root), ConvertNodeDefs (alt->alt_rhs_defs), ConvertNode (alt->alt_rhs_root));

	return (copy);
} /* ConvertRuleAlt */

static RuleAlts
ConvertRuleAlts (RuleAltP alts)
{
	RuleAltP	copy;

	if (alts == NULL)
		copy	= BENoRuleAlts ();
	else
		copy	= BERuleAlts (ConvertRuleAlt (alts), ConvertRuleAlts (alts->alt_next));

	return (copy);
} /* ConvertRuleAlts */

/*
	Node
	====
*/
static NodeP
ConvertNode (NodeP node)
{
	NodeP	copy;

	Assert (node->node_annotation == NoAnnot);
	switch (node->node_kind)
	{
		case NormalNode:
			copy	= BENormalNode (ConvertSymbol (node->node_symbol), ConvertArgs (node->node_arguments));
			break;
		case NodeIdNode:
			copy	= BENodeIdNode (ConvertNodeId (node->node_node_id), ConvertArgs (node->node_arguments));
			break;
		case SelectorNode:
			copy	= BESelectorNode (ConvertSymbol (node->node_symbol), ConvertArgs (node->node_arguments));
			break;
		default:
			Assert (False);
			break;
	}

	return (copy);
} /* ConvertNode */

/*
	NodeDef
	=======
*/
static NodeDefP
ConvertNodeDef (NodeDefP nodeDef)
{
	NodeDefP	copy;

	Assert (nodeDef->def_mark == 0);

	copy	= BENodeDef (nodeDef->def_id->nid_scope, ConvertNode (nodeDef->def_node));

	return (copy);
} /* ConvertNodeDef */

static NodeDefP
ConvertNodeDefs (NodeDefP nodeDefs)
{
	if (nodeDefs == NULL)
		return (BENoNodeDefs ());
	else
		return (BENodeDefs (ConvertNodeDef (nodeDefs), ConvertNodeDefs (nodeDefs->def_next)));
} /* ConvertNodeDefs */

/*
	ImpRule
	=======
*/
static ImpRuleP
ConvertRule (ImpRuleP rule)
{
	ImpRuleP	copy;
	SymbolP		functionSymbol;
	int			symbolIndex, moduleIndex;

	Assert (!IsConverted (rule));
	Assert (rule->rule_mark == RULE_CHECKED_MASK);

	functionSymbol	= rule->rule_root->node_symbol;

	GetSymbolIndices (functionSymbol, &symbolIndex, &moduleIndex);
	Assert (moduleIndex == kIclModuleIndex);
	copy	= BERule (symbolIndex, ConvertTypeAlt (rule->rule_type), ConvertRuleAlts (rule->rule_alts));

	return (copy);
} /* ConvertRule */

static ImpRuleP
ConvertRules (ImpRuleP rules)
{
	ImpRuleP	copy;

	if (rules == NULL)
		copy	= BENoRules ();
	else
		copy	= BERules (ConvertRule (rules), ConvertRules (rules->rule_next));

	return (copy);
} /* ConvertRules */

static void
DefineRuleType (int functionIndex, int moduleIndex, RuleTypes ruleType)
{
	SymbolP	functionSymbol;

	Assert (!IsConverted (ruleType));

	// +++ move to count
	functionSymbol	= ruleType->rule_type_root->type_node_symbol;
	SetSymbolIndices (functionSymbol, functionIndex, moduleIndex);
			
	Assert (functionSymbol->symb_kind == definition);

	BEDeclareRuleType (functionIndex, moduleIndex, ConvertCString (functionSymbol->symb_def->sdef_ident->ident_name));
	BEDefineRuleType (functionIndex, moduleIndex, ConvertTypeAlt (ruleType->rule_type_rule));
} /* DefineRuleType */

static void
DefineRuleTypes (SymbolP allSymbols, char *moduleName)
{
	SymbolP	symbol;

	for (symbol = allSymbols; symbol != NULL; symbol = symbol->symb_next)
	{
		if (symbol->symb_kind == definition)
		{
			SymbDef	sdef;

			sdef	= symbol->symb_def;
			if ((sdef->sdef_kind == DEFRULE || sdef->sdef_kind == SYSRULE) && sdef->sdef_isused
					&& sdef->sdef_module == moduleName)
			{
				int	functionIndex, moduleIndex;

				GetSymbolIndices (symbol, &functionIndex, &moduleIndex);
				DefineRuleType (functionIndex, moduleIndex, sdef->sdef_rule_type);
			}
			
		}
	}
} /* DefineRuleTypes */

static void
DeclareFunctions (SymbDefP sdefs)
{
	int			i;
	SymbDefP	sdef;

	i	= 0;
	for (sdef = sdefs; sdef != NULL; sdef = sdef->sdef_next_scc)
	{
		Node		root;
		ImpRuleP	rule;
		Symbol		symbol;

		Assert (sdef->sdef_kind == IMPRULE);
		rule	= sdef->sdef_rule;

		root	= rule->rule_root;
		Assert (root->node_kind == NormalNode);
		symbol	= root->node_symbol;
		Assert (symbol->symb_kind == definition);

		SetSymbolIndices (symbol, i, kIclModuleIndex);

		Assert (sdef->sdef_kind == IMPRULE);
		Assert (sdef->sdef_mark == 0);
		Assert (sdef->sdef_over_arity == 0);
//		Assert (!sdef->sdef_exported);
		Assert (sdef->sdef_arfun == NoArrayFun);

		// +++ hack
		if (sdef->sdef_exported)
			sdef->sdef_ancestor	= -sdef->sdef_ancestor-1;

		BEDeclareFunction (ConvertCString (sdef->sdef_ident->ident_name), sdef->sdef_arity, i, sdef->sdef_ancestor);

		i++;
	}
} /* DeclareFunctions */

static TypeVar
ConvertTypeVar (TypeVar typeVar)
{
	return (BETypeVar (ConvertCString (typeVar->tv_ident->ident_name)));
} /* ConvertTypeVar */

static TypeVarList
ConvertTypeVarList (TypeVarList typeVarList)
{
	if (typeVarList == NULL)
		return (BENoTypeVars ());
	else
		return (BETypeVars (ConvertTypeVar (typeVarList->tvl_elem), ConvertTypeVarList (typeVarList->tvl_next)));
} /* ConvertTypeVarList */

static FlatType
ConvertFlatType (FlatType flatType)
{
	BEFlatType (ConvertSymbol (flatType->ft_symbol), ConvertTypeVarList (flatType->ft_arguments));
} /* ConvertFlatType */

static void
SequenceTypesAndConstructors (Types types, int moduleIndex, int *nTypesP, int *nConstructorsP, int *nFieldsP)
{
	int	typeIndex, constructorIndex, fieldIndex;

	typeIndex			= 0;
	constructorIndex	= 0;
	fieldIndex			= 0;

	for (; types != NULL; types = types->type_next)
	{
		SymbolP			typeSymbol;
		ConstructorList	constructor;
		
		typeSymbol	= types->type_lhs->ft_symbol;
		SetSymbolIndices (typeSymbol, typeIndex++, moduleIndex);

		if (types->type_nr_of_constructors == 0)
		{
			SymbolP		constructorSymbol;
			FieldList	field;

			constructor = types->type_constructors;

			Assert (!constructor->cl_constructor->type_node_is_var);
			Assert (constructor->cl_fields != NULL);
			/* Assert (constructor->cl_next == NULL); ??? unitialised */
			constructorSymbol	= constructor->cl_constructor->type_node_symbol;
	
			SetSymbolIndices (constructorSymbol, constructorIndex++, moduleIndex);

			for (field = types->type_fields; field != NULL; field = field->fl_next)
			{
				SymbolP	fieldSymbol;

				fieldSymbol	= field->fl_symbol;

				SetSymbolIndices (fieldSymbol, fieldIndex++, moduleIndex);
			}
		}
		else
		{
			for (constructor = types->type_constructors; constructor != NULL; constructor = constructor->cl_next)
			{
				SymbolP		constructorSymbol;
	
				Assert (!constructor->cl_constructor->type_node_is_var);
				Assert (constructor->cl_fields == NULL);
				constructorSymbol	= constructor->cl_constructor->type_node_symbol;
	
				SetSymbolIndices (constructorSymbol, constructorIndex++, moduleIndex);
			}
		}	
	}
	*nTypesP		= typeIndex;
	*nConstructorsP	= constructorIndex;
	*nFieldsP		= fieldIndex;
} /* SequenceTypesAndConstructors */

static int
SequenceRuleTypes (SymbolP allSymbols, int moduleIndex, char *moduleName)
{
	int		nRuleTypes;
	SymbolP	symbol;

	nRuleTypes	= 0;
	for (symbol = allSymbols; symbol != NULL; symbol = symbol->symb_next)
	{
		if (symbol->symb_kind == definition)
		{
			SymbDef	sdef;

			sdef	= symbol->symb_def;
			if ((sdef->sdef_kind == DEFRULE || sdef->sdef_kind == SYSRULE) && sdef->sdef_isused
					&& sdef->sdef_module == moduleName)
			{
				SetSymbolIndices (symbol, nRuleTypes, moduleIndex);
				nRuleTypes++;
			}
			
		}
	}

	return (nRuleTypes);
} /* SequenceRuleTypes */

static ConstructorList
ConvertConstructor (ConstructorList constructor)
{
	SymbolP			constructorSymbol;
	ConstructorList	copy;
	int				constructorIndex, moduleIndex;

	Assert (!constructor->cl_constructor->type_node_is_var);
	constructorSymbol	= constructor->cl_constructor->type_node_symbol;

	GetSymbolIndices (constructorSymbol, &constructorIndex, &moduleIndex);

	BEDeclareConstructor (constructorIndex, moduleIndex, ConvertCString (constructorSymbol->symb_def->sdef_ident->ident_name));
	copy	=	BEConstructor (ConvertTypeNode (constructor->cl_constructor));

	return (copy);
} /* ConvertConstructor */

static ConstructorList
ConvertConstructors (ConstructorList constructors)
{
	ConstructorList	copy;

	if (constructors == NULL)
		copy	= BENoConstructors ();
	else
		copy	= BEConstructors (ConvertConstructor (constructors), ConvertConstructors (constructors->cl_next));

	return (copy);
} /* ConvertConstructors */

static FieldList
ConvertField (FieldList field)
{
	SymbolP		fieldSymbol;
	FieldList	copy;
	int			fieldIndex, moduleIndex;

	fieldSymbol	= field->fl_symbol;

	GetSymbolIndices (fieldSymbol, &fieldIndex, &moduleIndex);

	BEDeclareField (fieldIndex, moduleIndex, ConvertCString (fieldSymbol->symb_def->sdef_ident->ident_name));
	copy	=	BEField (fieldIndex, moduleIndex, ConvertTypeNode (field->fl_type));

	return (copy);
} /* ConvertField */

static FieldList
ConvertFields (FieldList fields)
{
	FieldList	copy;

	if (fields == NULL)
		copy	= BENoFields ();
	else
		copy	= BEFields (ConvertField (fields), ConvertFields (fields->fl_next));

	return (copy);
} /* ConvertFields */

static Types
ConvertType (Types type)
{
	SymbolP	typeSymbol;
	Types	copy;
	int		typeIndex, moduleIndex;

	typeSymbol	= type->type_lhs->ft_symbol;
	GetSymbolIndices (typeSymbol, &typeIndex, &moduleIndex);

	Assert (typeSymbol->symb_kind == definition);

	BEDeclareType (typeIndex, moduleIndex, ConvertCString (typeSymbol->symb_def->sdef_ident->ident_name));

	if (type->type_nr_of_constructors == 0)
		copy	= BERecordType (BEFlatType (BETypeSymbol (typeIndex, moduleIndex), NULL), ConvertTypeNode (type->type_constructors->cl_constructor), ConvertFields (type->type_fields));
	else
		copy	= BEAlgebraicType (BEFlatType (BETypeSymbol (typeIndex, moduleIndex), NULL), ConvertConstructors (type->type_constructors));

	return (copy);
} /* ConvertType */

static Types
ConvertTypes (Types types)
{
	Types	copy;

	if (types == NULL)
		copy	= BENoTypes ();
	else
		copy	= BETypes (ConvertType (types), ConvertTypes (types->type_next));

	return (copy);
} /* ConvertTypes */


/*
	ImpMod
	======
*/

static void
ConvertIclModule (ImpMod module)
{
	SymbDefP	sdef;
	int			nFunctions, nTypes, nConstructors, nFields;

//	Assert (module->im_def_module == NULL);
//	Assert (module->im_main);

	nFunctions	= 0;
	for (sdef = scc_dependency_list; sdef != NULL; sdef = sdef->sdef_next_scc)
		nFunctions++;

	SequenceTypesAndConstructors (module->im_types, kIclModuleIndex, &nTypes, &nConstructors, &nFields);

	BEDeclareIclModule (ConvertCString (module->im_name->symb_ident->ident_name), nFunctions, nTypes, nConstructors, nFields);

	ConvertTypes (module->im_types);

	DeclareFunctions (scc_dependency_list);
	BEDefineRules (ConvertRules (module->im_rules));
} /* ConvertIclModule */

/*
	DefMod
	======
*/

static int
CountDclModules (DefMod module, int moduleIndex)
{
	ImportList	import;

	if ((int) module->dm_abs_types == 1)
		return (moduleIndex);

	module->dm_abs_types	= (void *) 1;
	module->dm_syn_types	= (void *) moduleIndex++;

	for (import = module->dm_imports; import != NULL; import = import->ilist_next)
		moduleIndex	= CountDclModules (import->ilist_def, moduleIndex);

	return (moduleIndex);	
} /* CountDclModules */

static void
ConvertDclModule (DefMod module, SymbolP allSymbols)
{
	int			moduleIndex, functionIndex, nTypes, nConstructors, nFields;
	char		*moduleName;
	ImportList	import;

	if ((unsigned int) module->dm_abs_types == 2)
		return;

	Assert ((unsigned int) module->dm_abs_types == 1);
	module->dm_abs_types	= (void *) 2;

	for (import = module->dm_imports; import != NULL; import = import->ilist_next)
		ConvertDclModule (import->ilist_def, allSymbols);

	moduleName	= module->dm_name->symb_ident->ident_name;
	moduleIndex	= (int) module->dm_syn_types;

	functionIndex	= SequenceRuleTypes (allSymbols, moduleIndex, moduleName);

	SequenceTypesAndConstructors (module->dm_types, moduleIndex, &nTypes, &nConstructors, &nFields);

	BEDeclareDclModule (moduleIndex, ConvertCString (module->dm_name->symb_ident->ident_name), False, 
							functionIndex, nTypes, nConstructors, nFields);


	DefineRuleTypes (allSymbols, moduleName);

# if 0
	functionIndex	= 0;
	functionIndex	= DefineRuleTypes (moduleIndex, module->dm_rules, functionIndex);
	functionIndex	= DefineInstances (moduleIndex, module->dm_instances, functionIndex);
# endif

	ConvertTypes (module->dm_types);
} /* ConvertDclModule */

static void
ConvertModules (ImpMod module)
{
	int			n;
	ImportList	import;

	n	=	2; 	/* 2: icl + predef */
	for (import = module->im_imports; import != NULL; import = import->ilist_next)
		n	= CountDclModules (import->ilist_def, n);

	BEDeclareModules (n);

	// +++ temporary test
	BEDeclarePredefinedModule (1, 2);
	BEPredefineTypeSymbol (0, kPredefinedModuleIndex, list_type);
	BEPredefineConstructorSymbol (0, kPredefinedModuleIndex, nil_symb);
	BEPredefineConstructorSymbol (1, kPredefinedModuleIndex, cons_symb);

	for (import = module->im_imports; import != NULL; import = import->ilist_next)
		ConvertDclModule (import->ilist_def, module->im_symbols);

	ConvertIclModule (module);
} /* ConvertModules */

void
CoclBackEnd (ImpMod module, char *outputFileName)
{
	BackEnd	backEnd;

	backEnd	= BEInit (0);

	ConvertModules (module);

	CompFree ();
	InitStorage ();

	BEGenerateCode (ConvertCString (outputFileName));

	BEFree (backEnd);
} /* CoclBackEnd */

# endif /* DUMP_AND_RESTORE */