/*

Version 1.0 06/09/1995

Author: Sjaak Smetsers 

*/

extern jmp_buf ExitTypeComponent;

extern void OverloadingError (Symbol symbol, char *msg, TypeCell type, Bool make_jump);

extern void Unify (TypeCell offtype, TypeCell demtype, Node uni_node, int argnr);

extern UnificationStatus UnifyTypes (TypeCell offtype, TypeCell demtype);

extern void UnifyError (UnificationStatus ustat, Node err_node, int err_argnr, TypeCell type1, TypeCell type2);

extern void UniquenessError (UniquenessErrorKind err_kind, Node err_node, int err_argnr, TypeCell type, TypeCell sub_type);

extern void ReportTypeError (Node err_node, int err_argnr, char *err_msg);

extern TypeCell ExpandSynonymType (TypeCell synappl, SymbDef syndef);

extern AttributeCellKind DetermineAttrkindOfTypeCell (TypeCell type);

#define GetExistentionalVarsOfTypeCons(typecons) (typecons -> sdef_contains_freevars) ?\
		typecons -> sdef_type -> type_exivars : ALLBITSCLEAR

extern Symbol BuildNewSymbol (SymbDef old_symb_def, int id_nr, TypeCell ins_types [], int arity, TableKind table);

extern Symbol BuildNewClassSymbol (SymbolList class_symbols);

extern Ident BuildNewSymbolId (char *prefix, int id_nr, TypeCell ins_types [], int arity, TableKind table);

extern TypeCell SkipTypeSynIndirection (TypeCell type);

extern void PrepareTypesAndImportedInstances (Symbol symbs, char *icl_module);
