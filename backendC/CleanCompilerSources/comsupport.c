/*
	(Concurrent) Clean Compiler:	Support			
	========================================		
														
	This module contains all the compiler supporting routines,
	such as: the storage administration and the error handling
	routines and some global variables containing the compiler
	settings. 											
	At the end of this module the version number of the compiler
	is administered.									
														
	Author:	Sjaak Smetsers 								
	At:		University of Nijmegen, department of computing science
	Version:	1.0
*/

#include "compiledefines.h"
#include "types.t"
#include "system.h"
#include "sizes.h"

#include "settings.h"
#include "syntaxtr.t"
#include "comsupport.h"
#include "scanner.h"
#include "buildtree.h"
#include "comparser.h"
#include "checker.h"
#include "statesgen.h"
#include "codegen_types.h"
#include "codegen1.h"
#include "codegen2.h"
#include "instructions.h"
#include "checksupport.h"
#include "dbprint.h"

extern int VERSION;

/* 'CurrentModule' contains the name of the module that is currently under examination. */

char *CurrentPhase, *CurrentModule, *CurrentExt;
unsigned CurrentLine;
Symbol CurrentSymbol;
Bool CompilerError;

int ExitEnv_valid=0;
jmp_buf ExitEnv;

/*	The storage administration. */

unsigned long NrOfBytes;
unsigned NrOfLargeBlocks;

static char *StartStorage, *FirstBlock, *LastBlock, *NextFreeMem;

static void *AllocLarge (SizeT size)
{
	char **newblock;

	size = ReSize (size);
	if ((newblock = (char **) Alloc ((unsigned long) size + SizeOf (char *), SizeOf (char)))!=NULL){
		*newblock  = FirstBlock;
		FirstBlock = (char *) newblock++;
		NrOfBytes += size;
		return (char *) newblock;
	} else {	
		FatalCompError ("comsupport", "AllocLarge", "Insufficient Memory");
		
		return (void *) Null;
	}
}

static Bool InitStorageFlag = True;

void InitStorage (void)
{
	if (InitStorageFlag){
		char **newblock;
		
		if ((newblock = (char **) Alloc ((unsigned long) (MemBlockSize + (SizeT) (SizeOf (char *))), SizeOf (char)))!=NULL){
			*newblock = (char *) NIL;
			StartStorage = LastBlock = FirstBlock = (char *) newblock;
			NextFreeMem = SizeOf(char*)+(char*)newblock;
			InitStorageFlag = False;
			NrOfBytes = (unsigned long) (MemBlockSize + (SizeT) (SizeOf (char *)));
			NrOfLargeBlocks = 0;
		} else
			FatalCompError ("comsupport", "InitStorage","Insufficient Memory");
	}
}

#undef FILL_ALLOCATED_MEMORY_WITH_GARBAGE

#ifdef FILL_ALLOCATED_MEMORY_WITH_GARBAGE
static unsigned char g_next_garbage_byte=0;
#endif

void *CompAlloc (SizeT size)
{
	char *new_block;
	
	size = ReSize (size);
	
	if (size > KBYTE){
		NrOfLargeBlocks++;
#ifdef FILL_ALLOCATED_MEMORY_WITH_GARBAGE
		{
			void *m;
			unsigned char *p,next_garbage_byte;
			int i;
			
			m=AllocLarge (size);
			
			i=size;
			p=m;

			next_garbage_byte=g_next_garbage_byte;
			while (--i>=0)
				*p++ = next_garbage_byte++;
			g_next_garbage_byte=next_garbage_byte;

			return m;
		}
#else
		return AllocLarge (size);
#endif
	}
	
	new_block=NextFreeMem;
	
	if (new_block-LastBlock+size > MemBlockSize+SizeOf(char*)){
		char **newblock;

		newblock = (char **) Alloc ((unsigned long)
				(MemBlockSize + (SizeT) (sizeof (char *))), SizeOf (char));

		if (newblock!=NULL){
			*((char **) LastBlock) = (char *) newblock;
			LastBlock = (char *) newblock;
		
			*newblock = (char *) NIL;
			new_block=LastBlock+SizeOf(char*);
		
			NrOfBytes += (unsigned long) (MemBlockSize + (SizeT) (SizeOf (char *)));
		} else {
/*			FPrintF (StdError,"Allocated %ld bytes\n",(long)NrOfBytes); */
			FatalCompError ("comsupport", "CompAlloc", "Insufficient Memory");
		}
	}

	NextFreeMem = new_block+size;

#ifdef FILL_ALLOCATED_MEMORY_WITH_GARBAGE
		{
			unsigned char *p,next_garbage_byte;
			int i;
						
			i=size;
			p=(unsigned char*)new_block;

			next_garbage_byte=g_next_garbage_byte;
			while (--i>=0)
				*p++ = next_garbage_byte++;
			g_next_garbage_byte=next_garbage_byte;
		}
#endif

	return (void *) new_block;
}

extern void finish_strictness_analysis (void);

void CompFree (void)
{
	if (! InitStorageFlag){
		char *block;

		for (block = FirstBlock; block; ){
			char *next_block;

			next_block=*((char **) block);
			Free (block);
			block=next_block;
		}

		finish_strictness_analysis();

		InitStorageFlag = True;
	}
}

/* The environment to leave the compiler if a fatal error occurs */

void FatalCompError (char *mod, char *proc, char *mess)
{
	FPrintF (StdError,"Fatal Error in %s:%s \"%s\"\n", mod, proc, mess);
	if (OpenedFile){
		if (ABCFileName){
			CompilerError = True;
			CloseABCFile (ABCFileName);
		} else
			FClose (OpenedFile);
		OpenedFile = (File) NIL;
	}
#ifdef CLEAN2
# ifdef _MAC_
	{
		FILE *f;
	
		f=fopen ("FatalCompError","w");
		if (f!=NULL){
			FPrintF (f,"Fatal Error in %s:%s \"%s\"\n", mod, proc, mess);
			fclose (f);
		}
	}
# endif
	if (!ExitEnv_valid)
		exit (1);
#endif
	longjmp (ExitEnv, 1);
}

void PrintSymbol (Symbol symbol, File file)
{
	Ident symb_id;
	unsigned line_nr;
	
	switch (symbol -> symb_kind)
	{
	case definition:
		line_nr = 0;
		PrintSymbolOfIdent (symbol->symb_def->sdef_name, line_nr, file);
		return;
	case int_denot:
		FPutS (symbol->symb_int, file);
		return;
	case bool_denot:
		FPutS (symbol->symb_bool ? "True" : "False", file);
		return;
	case char_denot:
		FPutS (symbol->symb_char, file);
		return;
	case string_denot:
		FPutS (symbol->symb_string, file);
		return;
	case real_denot:
		FPutS (symbol->symb_real, file);
		return;
	case tuple_symb:
		FPutS ("Tuple", file);
		return;
	case cons_symb:
		FPutS ("[:]", file);
		return;
	case nil_symb:
		FPutS ("[]", file);
		return;
	case select_symb:
		FPutS ("_Select", file);
		return;
	case apply_symb:
		FPutS ("AP", file);
		return;
	case if_symb:
		FPutS ("if", file);
		return;
	case fail_symb:
		FPutS ("_Fail", file);
		return;
	default:
		FPutS (ConvertSymbolKindToString ((SymbKind)symbol -> symb_kind), file);
		return;
	}

	PrintSymbolOfIdent (symb_id->ident_name, line_nr, file);

} /* PrintSymbol */

#include <stdarg.h>

static char *FindFormatSpecifier (char * format_string)
{
	for (; *format_string != '\0' && *format_string != '%'; format_string++)
		;
	return format_string;

}

#ifdef GNU_C
void StaticMessage (Bool error, char *symbol_format1, char *message_format1, ...)
{
	char *format, format_spec;
	char symbol_format [256], message_format [256];

	va_list ap;
	
	strcpy (symbol_format, symbol_format1);
	strcpy (message_format, message_format1);

	va_start (ap, message_format1);

#else

void StaticMessage (Bool error, char *symbol_format, char *message_format, ...)
{
	char *format, format_spec;

	va_list ap;
	va_start (ap, message_format);

#endif
	
	if (! (error || DoWarning))
		return;

#ifdef MAKE_MPW_TOOL
	FPutS ("### ",StdError);
#endif

	if (CurrentPhase){
		FPutS (CurrentPhase, StdError);
		FPutS (error ? " error [" : " warning [", StdError);
	} else
		FPutS (error ? "Error [" : "Warning [", StdError);

#ifdef MAKE_MPW_TOOL
	FPutS ("File ",StdError);
#endif

	FPutS (CurrentModule, StdError);
	FPutS (CurrentExt, StdError);
	
	if (CurrentLine > 0){
#ifdef MAKE_MPW_TOOL
		FPrintF (StdError, "; Line %u", CurrentLine);
#else
		FPrintF (StdError, ",%u", CurrentLine);
#endif
	}

#ifdef MAKE_MPW_TOOL
	FPutS ("] ", StdError);
#else
	FPutC (',', StdError);
#endif

	for (format = symbol_format; ;)
	{	char *tail_format = FindFormatSpecifier (format);
		
		if (*tail_format == '\0')
		{	FPutS (format, StdError);
			break;
		}
		else
		{	*tail_format = '\0';
			FPutS (format, StdError);
			*tail_format = '%';
			format_spec = * (++tail_format);
			
			if (format_spec == '\0')
			{	FPutC ('%', StdError);
				break;
			}
			else			
			{	switch (format_spec)
				{
				case 's':
				{	char * message = va_arg (ap, char *);
					if (message != NULL)
						FPutS (message, StdError);
					break;
				}
				case 'D':
				{
					SymbDef def  = va_arg (ap, SymbDef);
					PrintSymbolOfIdent (def->sdef_name, 0, StdError);
					break;
				}
				case 'S':
					PrintSymbol (va_arg (ap, Symbol), StdError);
					break;
				default:
					FPutC ('%', StdError);
					FPutC (format_spec, StdError);
					break;
				}
				format = ++tail_format;
			}
		}
	}

#ifdef MAKE_MPW_TOOL
	FPutS (": ", StdError);
#else
	FPutS ("]: ", StdError);
#endif

	for (format = message_format; ;)
	{	char *tail_format = FindFormatSpecifier (format);
		
		if (*tail_format == '\0')
		{	FPutS (format, StdError);
			break;
		}
		else
		{	*tail_format = '\0';
			FPutS (format, StdError);
			*tail_format = '%';
			format_spec = * (++tail_format);
			
			if (format_spec == '\0')
			{	FPutC ('%', StdError);
				break;
			}
			else			
			{	switch (format_spec)
				{
				case 's':
				{	char * message = va_arg (ap, char *);
					if (message != NULL)
						FPutS (message, StdError);
					break;
				}
				case 'd':
				{	int nr	= va_arg (ap, int);
					FPrintF (StdError, "%d", nr);
					break;
				}
				case 'S':
					PrintSymbol (va_arg (ap, Symbol), StdError);
					break;
				default:
					FPutC ('%', StdError);
					FPutC (format_spec, StdError);
					break;
				}
				format = ++tail_format;
			}
		}
	}

	FPutC ('\n', StdError);

	va_end (ap);
	
	if (error)
		CompilerError = True;
}

void Verbose (char *msg)
{
	if (DoVerbose)
		FPrintF (StdVerboseL, "%s \"%s%s\"\n", msg, CurrentModule, CurrentExt);
}

void PrintVersion (void)
{
	if (DoVerbose)
		FPrintF (StdVerboseL, "Concurrent Clean Compiler (Version %d.%d)\n",
			   VERSION / 1000, VERSION % 1000);
}

static char Init[] = "Compiler initialization";

File OpenedFile;

void InitCompiler (void)
{
	OpenedFile     = (File) NIL;
	CompilerError	= False;
	/* Call all the initialization functions */
	/* InitStorage has to be called first */
	CurrentModule = Init;
	CurrentExt    = "";

	InitStorage		();
	InitScanner		();
	InitParser		();
	InitChecker		();
	InitStatesGen		();
	InitCoding		();
	InitInstructions	();
} /* InitCompiler */

void ExitCompiler (void)
{
	CompFree();
}

#ifdef CLEAN2
extern struct clean_string_128 { size_t length; char chars[128]; } clean_error_string;
#endif

#ifdef _DEBUG_

void ErrorInCompiler (char *mod, char *proc, char *msg)
{
	if (CurrentModule!=NULL)
		FPrintF (StdError,"Error in compiler while compiling %s.icl: Module %s, Function %s, \"%s\"\n",CurrentModule,mod,proc,msg);
	else
		FPrintF (StdError,"Error in compiler: Module %s, Function %s, \"%s\"\n",mod,proc,msg);

#ifdef CLEAN2
	if (CurrentModule!=NULL)
		sprintf (clean_error_string.chars,"Error in compiler while compiling %s.icl: Module %s, Function %s, \"%s\"\n",CurrentModule,mod,proc,msg);
	else
		sprintf (clean_error_string.chars,"Error in compiler: Module %s, Function %s, \"%s\"\n",mod,proc,msg);	
	clean_error_string.length = strlen (clean_error_string.chars);

# ifdef _MAC_
	{
		FILE *f;
	
		f=fopen ("ErrorInCompiler","w");
		if (f!=NULL){
			if (CurrentModule!=NULL)
				FPrintF (f,"Error in compiler while compiling %s.icl: Module %s, Function %s, \"%s\"\n",CurrentModule,mod,proc,msg);
			else
				FPrintF (f,"Error in compiler: Module %s, Function %s, \"%s\"\n",mod,proc,msg);
			fclose (f);
		}
	}
	exit (1);
# endif
	if (ExitEnv_valid)
		longjmp (ExitEnv, 1);
#endif
}

void Assume (Bool cond, char *mod, char *proc)
{
	if (! cond)
		ErrorInCompiler (mod, proc, "wrong assumption");
}

void AssumeError (char *mod, char *proc)
{
	ErrorInCompiler (mod, proc, "wrong assumption");
}
#endif

#if D
void error (void)
{
	printf ("error in compiler\n");
}
#endif
