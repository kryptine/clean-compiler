/*

	Version 1.0 10/06/1994

	Author:  Sjaak Smetsers

*/

/*
	global type defintions
*/

/* LAST
typedef enum
{
	AlgebraicType, SynonymType, FunctionType, ClassType

} TypeDefKind;

typedef struct instance_list
{
	SymbDef					il_symbol;
	unsigned long			il_basic_instances;
	struct instance_list *	il_next;
	
} * InstanceList;
*/

typedef enum
{	AlgebraicType, SynonymType, FunctionType, ClassType
} TypeDefKind;


/*
	global variables
*/

extern TypeArgClass FunTypeClass, GeneralTypeClass;

/*
	global functions
*/

extern void CheckInstances (Instance instances);

extern void AdjustFixitiesAndPrioritiesOfInstances (ClassInstance instances);

extern void CheckTypesImpOfRules (ImpRules imp_rules);
extern void CheckTypesOfDefRules (RuleTypes def_rules);

extern void CheckAbsTypes (AbsTypes abstr);
extern void CheckSynonymTypes (SynTypes syn_type);
extern void CheckTypes (Types types);
extern void CheckTypeVars (TypeVarList lhs_vars);
extern void CheckTypeClasses (ClassDefinition classes, Bool check_icl_file);

extern Symbol MarkTypeClasses (ClassDefinition classes, Symbol all_symbols);
extern Symbol MarkTypeClassInstances (ClassInstance instances, Symbol all_symbols, char * def_mod_name);

extern void CollectInstancesOfTypeClasses (ClassInstance instances);
extern void CheckInstancesInIclFile (ClassInstance instances);

extern Symbol CheckInstancesInDclFile (ClassInstance instances, Symbol all_symbols, Bool is_def_mod);

extern void CheckOverloadedRules (Overloaded overrules);

extern void ExpandSymbolTypes (Symbol imp_symbols);

extern void VerifyTypeDefinitions (SymbDef type1,SymbDef type2);
extern void VerifyRuleTypes (TypeAlts type1,TypeAlts type2, Bool check_exported_instances);
extern Bool VerifySymbDefs (SymbDef dcl_sdef, SymbDef icl_sdef);
extern Bool VerifyTypeGraphs (TypeNode root1,TypeNode root2);
extern Bool VerifyLhsOfTypes (FlatType lhs1, FlatType lhs2);

extern void CheckExportedInstances (DefMod def);
extern void CollectBasicClassInstances (Symbol symbs, Bool is_icl_file);
extern void CollectBasicClassInstancesOfEmptyClasses (Symbol all_symbols);

extern void VerifyTypeClasses (SymbDef dcl_symb, SymbDef icl_symb);
extern void VerifyInstances (ClassInstance dcl_instance, SymbDef icl_sdef);

extern void InitCheckTypeDefs (void);
extern void ExitCheckTypeDefs (void);
