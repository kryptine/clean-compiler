
void InitChecker (void);
void GenDependencyList (void);

struct def_list {
	DefMod				mod_body;
	struct def_list *	mod_next;
};

extern struct def_list *OpenDefinitionModules;

void ClearOpenDefinitionModules (void);
void AddOpenDefinitionModule (DefMod definitionModule);
