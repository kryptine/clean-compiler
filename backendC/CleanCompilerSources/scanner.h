
extern	IdentP	PutStringInHashTable (char *string, TableKind tabkind);

extern	void	InitScanner (void);

extern	void	ScanInitialise (void);

extern	void ScanInitIdentStringTable (void);

extern void ScanInlineFile (char *fname,TableKind table_kind);
