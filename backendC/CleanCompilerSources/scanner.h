/*
     +---------------------------------------------------------------------+
     |    For each identifier stored in the symbol table a structure of    |
     |    type 'Ident' is reserved.								|
     +---------------------------------------------------------------------+
*/

extern char *ConvertNextTokenToString (void);

typedef
	enum
	{
		IdentToken, IntToken,  CharToken,
		StringToken, RealToken, AnnotToken, InstructionToken,
		EOFToken,
		errorsym, barsym, strictsym, opensym,
		closesym, opensquaresym, closesquaresym, colonsym,
 		typesym, semicolonsym, commasym, dotsym, openbracesym,
		closebracesym, arrowsym, abstypesym,
		arraysym, strictarraysym, unboxedarraysym,

		atsym,boolsym, codesym, charsym,defsym,
		falsesym, filesym, fromsym, ifsym, impsym,
/* RWS */
		allsym,
		importsym, intsym, macrosym, modulesym, procidsym, redidsym,
		realsym, rulesym, stringsym,
		systemsym, truesym, typedefsym, applysym,
		uniquesym, worldsym,
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

typedef	unsigned int		Token;

STRUCT (tokenValue, TokenValue)
{
	Token	token;	
	long	lineNumber;
	union {
		char			*literal;
		IdentStringP	identString;
	} value;
};

typedef	enum { kScanModeNormal,kScanModeTypes,kScanModeInstructions } ScanMode;

extern	IdentP	RetrieveFromSymbolTable (char *name);
extern	IdentP	PutStringInHashTable (char *string, TableKind tabkind);
extern	IdentP	PutIdentStringInTable (IdentStringP identString, TableKind tabkind);


extern	void	InitScanner (void);

extern	void	ScanInit (void);
extern	void	ScanSetMode (ScanMode scanMode);
enum {kOffsideOnHardBrace = True, kNoOffsideOnHardBrace = False};
extern	void	ScanSetOffside (Bool offsideOnHardBrace);
extern	Bool	ScanUnsetOffside (void);
extern	void	ScanSetLayoutOption (void);
extern	Bool	ScanOpenFile (char *fileName, FileKind fileKind);
#if WRITE_DCL_MODIFICATION_TIME
extern	Bool	ScanOpenFileWithModificationTime (char *fileName, FileKind fileKind, FileTime *file_time_p);
#endif
extern	void	ScanCloseFile (void);
extern	Bool	ScanTokenToString (Token token, char *string);

/*
	ScanCleanToken fills the global structure gCurrentToken.
*/
extern	void		ScanInitialise (void);

#ifdef CLEAN2
extern	void ScanInitIdentStringTable (void);
#endif

extern	void		ScanCleanToken (void);
extern	TokenValueS	gCurrentToken;
extern void ScanInlineFile (char *fname);

extern Bool	gApplyLayoutRule;
