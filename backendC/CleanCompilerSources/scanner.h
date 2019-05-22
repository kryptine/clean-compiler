
typedef enum {
	errorsym, arraysym, strictarraysym, unboxedarraysym,
	boolsym, charsym, falsesym, filesym, ifsym,
	intsym, procidsym, redidsym, realsym,
	truesym, applysym, worldsym,
	NumberOfKeywords /* make sure that this constant is the last one */
} KeywordKind;

extern char 	**ReservedWords;

extern	IdentP	PutStringInHashTable (char *string, TableKind tabkind);

extern	void	InitScanner (void);

extern	void	ScanInitialise (void);

extern	void ScanInitIdentStringTable (void);

extern void ScanInlineFile (char *fname,TableKind table_kind);
