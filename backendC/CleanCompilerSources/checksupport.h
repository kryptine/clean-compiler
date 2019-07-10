
#define cTypeDelimiter	';'	/* also in optimisations.c */
#define cTypeFirstArg	'<'
#define cTypeLastArg	'>'

extern char *ConvertSymbolKindToString (SymbKind skind);

extern void PrintSymbolOfIdent (char *name,unsigned line_nr,File file);
