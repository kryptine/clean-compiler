
extern	void PutStringInHashTable (char *string, TableKind tabkind, SymbDefP sys_rule_def);

extern	void	InitScanner (void);

extern	void	ScanInitialise (void);

extern	void ScanInitIdentStringTable (void);

extern void ScanInlineFile (char *fname,TableKind table_kind);
