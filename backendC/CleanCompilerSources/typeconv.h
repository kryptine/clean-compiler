/*

Version 1.0 25/04/1994

Author: Sjaak Smetsers 

*/

extern Bool ConvertTypesOfLiftedTypeVarsOrWildCards (TypeAlts type_alt, SymbolType symbtype, PolyList lifted_type_vars);

extern TypeAlts ConvertSymbolTypeToRuleType (Symbol rule_symbol, SymbolType rtype, int arity,
		TypeCell extra_args [], int nr_of_extra_args, TypeCell over_vars [], int over_arity);

extern void PrintType (SymbDef tdef, TypeAlts type);

extern Symbol ConvertSymbDefToSymbol (SymbDef sdef);

extern void ConvertSymbolToType (SymbDef sdef, char * module_env);
extern Bool ConvertTypeAltToTCType (SymbDef lhs_def, SymbolType result_type, TypeAlts type_alt,
	unsigned nr_of_lifted_args, int over_arity, TypeCell over_vars []);

extern void InitAttributeRow (void);

extern void InitARC_Info (void);

extern void ConversionError (Symbol which_symbol, char *which, char *error);

extern SymbolTypeInfoP NewSymbolTypeInfo (void);

extern void PrintTypeClass (SymbDef class_def, File file);

#define NewTypeCells(n,hd)	TH_AllocArray (hd,n,TypeCell)
