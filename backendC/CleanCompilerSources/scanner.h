
typedef
	enum
	{
		IdentToken, IntToken,  CharToken,
		StringToken, RealToken, AnnotToken, InstructionToken,
		EOFToken,
		errorsym, barsym, strictsym, opensym,
		closesym, opensquaresym, closesquaresym, colonsym,
 		typesym, semicolonsym, commasym, dotsym, openbracesym,
		closebracesym, arrowsym,
		arraysym, strictarraysym, unboxedarraysym,

		boolsym, codesym, charsym,
		falsesym, filesym, fromsym, ifsym,
		intsym, procidsym, redidsym,
		realsym, stringsym,
		truesym, applysym,
		worldsym,
		NumberOfKeywords /* make sure that this constant is the last one */
		
	} KeywordKind;  

extern char 	**ReservedWords;

	enum
	{
		/* 0 .. 255 are reserved for single ascii characters */
		kTokenImport = 256,	kTokenFrom, kTokenDefinition, kTokenImplementation,
		kTokenSystem, kTokenModule,
		kTokenLet, kTokenIn, kTokenCase, kTokenOf,
		kTokenWith, kTokenWhere, kTokenEquals, kTokenEqualColon,
		kTokenColonDoubleEqual, kTokenDoubleBackSlash,
		kTokenDoubleRightArrow,
		kTokenLeftArrow, kTokenLeftArrowColon, kTokenRightArrow,
		kTokenInfix, kTokenInfixL, kTokenInfixR,
		kTokenDotDot, kTokenDoubleColon,
		
		kTokenProcessOpen, kTokenProcessClose,
		kTokenChar, kTokenMultiChar, kTokenString, kTokenInt, kTokenReal,
		kTokenLowerIdentifier, kTokenUpperIdentifier, kTokenUnderscoreIdentifier,
		kTokenCode, kTokenInstruction,
		kTokenFalse, kTokenTrue,
		kTokenIf, kTokenAll,
		kNoToken, kTokenEOF,
		kTokenHashExclamationMark,

		kTokenOverload, kTokenInstance, kTokenClass,
		kTokenExport,

#ifdef H
		kTokenData, kTokenType, kTokenAtSign, kTokenThen, kTokenElse, kTokenInterface,
#endif

		kTokenDefault, kTokenResync
	};

typedef	unsigned int Token;

extern	IdentP	PutStringInHashTable (char *string, TableKind tabkind);
extern	IdentP	PutIdentStringInTable (IdentStringP identString, TableKind tabkind);

extern	void	InitScanner (void);

extern	void	ScanInitialise (void);

extern	void ScanInitIdentStringTable (void);

extern void ScanInlineFile (char *fname,TableKind table_kind);
