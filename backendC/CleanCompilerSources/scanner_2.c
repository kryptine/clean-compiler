/*
		Ronny Wichers Schreur
		University of Nijmegen
*/

# include	<stdio.h>
# include	<string.h>
# include	<ctype.h>
# include	<limits.h>

# undef H

# include	"compiledefines.h"
# include	"types.t"

#if defined (applec) || (defined (__MWERKS__) && !defined (_WINDOWS_)) || defined (__MRC__)
# define __ppc__
#endif

# include	"system.h"
# include	"syntaxtr.t"
# include	"comsupport.h"
# include	"scanner.h"
# include	"sizes.h"

typedef struct ident_string *IdentStringP;

struct ident_string {
	IdentStringP	left;
	IdentStringP	right;
	Ident			ident;
	char			*string;
};

static IdentP
NewIdentInTable (TableKind tableKind, char *name)
{
	IdentP	ident;

	ident	= CompAllocType (struct ident);
		
	ident->ident_table	= tableKind;
	ident->ident_name	= name;

	ident->ident_next		= NULL;
	ident->ident_instructions = NULL;
	ident->ident_mark 		= 0;

	return (ident);
}

#define CompAllocString(size) ((char*)CompAlloc(size))

static	char *
AllocString (char *string, short length)
{
	int		i;
	char	*s, *newString;
	
	s	= newString	= CompAllocString (length+1);

	for (i = 0; i < length; i++)
		*s++	= *string++;
	*s	= '\0';
	
	return (newString);
} /* AllocString */

IdentP
NewIdent (char *name)
{
	IdentP	ident;

	ident	= CompAllocType (struct ident);

	ident->ident_name	= AllocString (name,strlen (name));

	ident->ident_table	= LastSystemModuleTable;
	ident->ident_next		= NULL;
	ident->ident_instructions = NULL;
	ident->ident_mark 		= 0;

	return ident;
}

# define	kIdentStringTableSizeBits	10
# define	kIdentStringTableSize		((1 << kIdentStringTableSizeBits) - 1)

static	IdentStringP *gIdentStringTable;

static IdentStringP
StringInTable (char *string, short length)
{
	int			i;
	unsigned	long		hash;
	IdentStringP identString, *identStringPtr;
	char		*s;

	hash	= 0;
	s		= string;
	for (i = 0; i < length; i++)
	{
        hash <<= 2;
        hash  += *s++;
	}

    /*  Compute (hash % kIdentStringTableSize) */
    while (hash >= (kIdentStringTableSize<<1))
        hash   = (hash & kIdentStringTableSize) + (hash >> kIdentStringTableSizeBits);
    if (hash >= kIdentStringTableSize)
        hash   -= kIdentStringTableSize;

	identStringPtr = &gIdentStringTable [hash];

	while ((identString = *identStringPtr) != NIL)
	{
		int		compare;

		compare	= strncmp (identString->string, string, length);

		if (compare == 0 && (compare = ((unsigned char *)identString->string) [length]) == 0)
			/* found it */
			break;
		else if (compare > 0)
			identStringPtr	= &identString->left;
		else /* if (compare < 0) */
			identStringPtr	= &identString->right;
	}

	if (identString == NIL)
	{
		identString	= CompAllocType (struct ident_string);

		identString->left	= NIL;
		identString->right	= NIL;
		identString->ident	= NIL;

		identString->string	= AllocString (string, length);

		*identStringPtr	= identString;
	}

	return (identString);
} /* StringInTable */

static IdentP
PutIdentStringInTable (IdentStringP identString, TableKind tableKind)
{
	IdentP		ident;

	for (ident = identString->ident; ident != NIL; ident = ident->ident_next)
		if (ident->ident_table == tableKind)
			break;

	if (ident == NIL)
	{
		ident	= NewIdentInTable (tableKind, identString->string);
		
		ident->ident_next	= identString->ident;

		identString->ident	= ident;
	}

	return (ident);
} /* PutIdentStringInTable */

IdentP
PutStringInHashTable (char *string, TableKind tableKind)
{
	IdentStringP	identString;

	identString	= StringInTable (string, strlen (string));

	return (PutIdentStringInTable (identString, tableKind));
} /* PutStringInHashTable */

static IdentP RetrieveFromSymbolTable (char *string,TableKind table_kind)
{
	char *s;
	unsigned long hash;
	IdentStringP identString;
	IdentP ident;

	hash = 0;
	for (s = string; *s != '\0'; s++){
        hash <<= 2;
        hash  += *s;
	}

    /*  Compute (hash % 1023) */
    while (hash >= 2046)
        hash   = (hash & 1023) + (hash >> 10);
    if (hash >= 1023)
        hash   -= 1023;

	identString	= gIdentStringTable [hash];

	while (identString != NIL){
		int		compare;

		compare	= strcmp (identString->string, string);

		if (compare == 0)
			/* found it */
			break;
		else if (compare > 0)
			identString	= identString->left;
		else /* if (compare < 0) */
			identString	= identString->right;
	}
	
	if (identString != NIL){
		for (ident = identString->ident; ident != NIL; ident = ident->ident_next)
			if (ident->ident_table == table_kind)
				break;
	} else
		ident	= NIL;

	return ident;
}

/*
	+-----------------------------------------------------------------------+
	| ReadInlineCode scans all the imported SYSTEM modules and stores the	|
	| the encountered inline instructions in the symbol table.				|
	+-----------------------------------------------------------------------+
*/

char NextLine[LineLength];

/* has a command been read? */

static char *IsCommand (char *com, char *p)
{
	while (*com++ == *p++)
          if (*com == '\0')
               return (p);
    return ((char *) NIL);
}

/* scan a file for .inline-.end command pairs */

char    *InlineCodeBuffer;
unsigned InlineBufferIndex, InlineBufferStart;

void ScanInlineFile (char *fname,TableKind system_module_table_kind)
{
	register char *tail, *instr, *importingModule, *importingExtension;
	IdentP instrid;
	int nrinstr;
	File f;

	importingModule		= CurrentModule;
	importingExtension	= CurrentExt;
    
	CurrentModule = fname;
	CurrentExt    = GetFileExtension (abcFile);

	if (! (f = FOpen (fname, abcFile, "r")))
	{	CurrentModule = importingModule;
		CurrentExt    = importingExtension;

		return;
	}

#	if defined (POWER)
		setvbuf ((void*) f, NULL, _IOFBF, 8192);
#	endif
		
	CurrentLine		= 0;
	CurrentPhase	= NULL;
		
	for (;;){
		if (! FGetS (NextLine, LineLength, f))
			break;

		for (tail = NextLine; isspace (*tail); tail++)
			;

		/* if not at .inline reenter loop from top */
		if ((tail = IsCommand (".inline", tail)) == NIL)
			continue;

		/* get the function name */
		while (*tail == ' ' || *tail == '\t')
			tail++;

		/* terminate it with a '\0' */
		for (instr = tail; ! isspace (*tail); tail++)
			;
		if (instr == tail)
			continue;

		*tail = '\0';
		if (! (instrid = RetrieveFromSymbolTable (instr,system_module_table_kind)))
			continue;
		if ((instrid->ident_mark & INLINE_MASK) != 0)
		{
			StaticMessage (True, "%s", "multiple .inline directives", instr);
			continue;
		}
		instrid->ident_mark |= INLINE_MASK;
	
		/* Open the buffer for the next instructions */
		InlineBufferIndex = InlineBufferStart;

		for (nrinstr = 0; nrinstr <= MaxInlineInstr;){
			if (! FGetS (NextLine, LineLength, f)){
				StaticMessage (False, "%s", "%s no .end found in this file", instrid->ident_name,fname);
				break;
			}
			for (tail = NextLine; *tail == ' ' || *tail == '\t'; tail++)
				;
			if (IsCommand (".end", tail))
            	break;
			
			if (*tail != '\n' && *tail != '\0'){
				instr = NextLine;
				/* Copy this instruction into the buffer */

				do
				{	if (InlineBufferIndex < InlineBuffSize-2)
						InlineCodeBuffer [InlineBufferIndex++] = *instr++;
					else
						DoFatalError ("too many inline instructions");
				} while (*instr != '\n' && *instr != '\0');

				/* close the instruction with a newline character */
				InlineCodeBuffer [InlineBufferIndex++] = '\n';
				nrinstr++;
			}
		}

		if (nrinstr > MaxInlineInstr){
			StaticMessage (False, "%s", "%s file contains too many instructions", instrid->ident_name,fname);
		}
		
		/* save the list of inline instructions */
/*		if (InlineBufferIndex != InlineBufferStart){ */
			instrid->ident_instructions = &InlineCodeBuffer [InlineBufferStart];
			InlineBufferStart     = InlineBufferIndex+1;

			/* close the list with the NULL character */
			InlineCodeBuffer [InlineBufferIndex] = '\0';
/*		} */
	}

	FClose (f);

	CurrentModule = importingModule;
	CurrentExt    = importingExtension;
}

void
ScanInitIdentStringTable (void)
{
	int		i;

	gIdentStringTable	= (struct ident_string**)CompAlloc (kIdentStringTableSize * sizeof (struct ident_string));
	for (i = 0; i < kIdentStringTableSize; i++)
		gIdentStringTable [i]	= NIL;
}

void
ScanInitialise (void)
{
	ScanInitIdentStringTable();
} /* ScanInitialise */

void
InitScanner (void)
{
	InlineCodeBuffer  = (char*)CompAlloc (InlineBuffSize);
	InlineBufferStart = 0;
} /* InitScanner */
