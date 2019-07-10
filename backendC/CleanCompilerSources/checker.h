
extern char *StdBoolId;

extern SymbDef AndSymbDef,OrSymbDef,abort_symb_def,undef_symb_def;
#if SA_RECOGNIZES_ABORT_AND_UNDEF
extern char *StdMiscId;
#endif
extern char *PreludeId;
extern SymbDef seq_symb_def;

extern SymbDef scc_dependency_list;

SymbDef MakeNewSymbolDefinition (char *module, char *name, int arity, SDefKind kind);
char *ConvertSymbolToString (Symbol symb);
void InitChecker (void);
void GenDependencyList (void);
NodeDefs NewNodeDef (NodeId nid, Node node);

struct def_list {
	DefMod				mod_body;
	struct def_list *	mod_next;
};

extern struct def_list *OpenDefinitionModules;

void ClearOpenDefinitionModules (void);
void AddOpenDefinitionModule (DefMod definitionModule);
