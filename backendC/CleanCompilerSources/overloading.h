/*

	Version 1.0 08/25/1994

	Author:  Sjaak Smetsers

*/

/*

typedef struct member_descriptor
{
	SymbDef		md_class;
	Symbol		md_rule;

} * MemberDescriptor;

typedef struct member_item
{	
	Bool					mi_is_class;
	union
	{	Overloaded		mi_u_rule;
		SymbDef			mi_u_class;
	} mi_union;
				
	struct member_item *	mi_next;
	
} * MemberItems;

#define mi_rule	mi_union.mi_u_rule
#define mi_class	mi_union.mi_u_class

*/

/*
	Global variables
*/

extern unsigned NrOfOverloadedTypeVars, NrOfOverloadedRules, NrOfUntypedImpRules,
			 NrOfTypeClasses;


/*
	Global functions
*/

extern int LengthOfPolyList (PolyList list);

extern PolyList NewPolyListElem (void *elem, PolyList next, HeapDescr hd);

extern Bool IsSubClass (SymbolList sub_tree, SymbolList whole_list);

extern void DetermineClassesOfOverloadedTypeVariables (struct type_cell * type_inst);

extern Bool TryToBindOverloadedTypeVariables (Node appl_node, SymbolList class_symbols, struct type_cell *  type_inst);

extern void CheckInstancesOfTypeClasses (Symbol symbs);

extern void ConvertTypeClasses (void);

extern void ConvertTypeContexts (TypeContext type_cont, struct type_cell * typeargs []);

extern void  SetOverloadedTypeVars (int over_arity, TypeContext type_cont, struct type_cell * over_vars []);

extern void DetermineClassNumber (SymbDef class_symb);

extern ClassInstance RetrieveSpecificInstance (ClassDefinition class, struct type_cell * inst_type);

extern SymbDef CopySymbDef (SymbDef old);

extern SymbDef NewEmptyRule (Symbol rule_symb, int arity, unsigned line);

extern Bool EqualTypeClasses (int var_nr1, int var_nr2);

extern void InitOverloading (void);

extern void AddToInstanceList (ClassInstance class_instance, ClassDefinition class_def);

extern FieldList RetrieveClassSelector (SymbolList class_symbols, SymbDef class_symbol);

extern Types DetermineClassRecord (int nr_of_fields);

extern Bool InstanceIsExported (struct type_cell * inst_types [], struct type_cell * over_vars [], TypeContext type_cont);

extern struct type_cell * DetermineDefaultInstance (struct type_cell * over_var, Node over_appl_node);

extern Bool EqualSymbolList (SymbolList class_symbols1, SymbolList class_symbols2);

extern Bool ClassesHaveAGenericInstance (SymbolList classes);

extern struct type_cell * DetermineGenericInstance (struct type_cell * over_var);

extern SymbolList RebuildClassSymbolList (SymbolList class_symbs, void *alloc (SizeT size));

#define cTakeIclDef	True
#define cDontTakeIclDef	False

extern void InsertSymbolInSymbolList (SymbolList *symbols, SymbDef new_symbol, Bool take_icl_def, void *alloc (SizeT size));

extern void ConvertClassSymbolTreeToList (SymbolList symbols, SymbolList * result_list, void *alloc (SizeT size));

extern void CreateRuleType (SymbDef icl_def, TypeAlts imp_type);

