
extern SymbDef scc_dependency_list;

SymbDef MakeNewSymbolDefinition (char *module, char *name, int arity, SDefKind kind);
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
