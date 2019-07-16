
#ifdef __MWERKS__
#	define _WINDOWS_
#endif

#include "compiledefines.h"
#include "system.h"
#include <stdio.h>

#ifdef _WIN64
# undef _WINDOWS_
# include <windows.h>
#else
# ifdef __MWERKS__
#	include <x86_prefix.h>
# else
#	define _X86_
# endif
# include <windef.h>
# include <winbase.h>
#endif

File FOpen (char *fname,char *mode)
{
	return fopen (fname,mode);
}

int FClose (File f)
{
	return fclose ((FILE *) f);
}

int FDelete (char *fname)
{
	return remove (fname);
}

int FPrintF (File f, char *fmt, ...)
{	int n;
	va_list args;
	
	va_start (args, fmt);

	n = vfprintf ((FILE*)f, fmt, args);

	va_end (args);
	return n;
}

int FPutS (char *s, File f)
{
	return fputs (s, (FILE *) f);
}

void DoFatalError (char *fmt, ...)
{
	va_list args;
	
	va_start (args, fmt);

	(void) vfprintf (stderr, fmt, args);
	
	va_end (args);

	exit (0);
}

void CmdError (char *errormsg,...)
{
	va_list args;
	
	va_start (args, errormsg);

	fputs ("Command line error: ", stdout);
	vfprintf (stdout, errormsg, args);
	fputc ('\n', stdout); 
		
	va_end (args);
}

void *Alloc (long unsigned count, SizeT size)
{	
	if (size == 1){
		if (count >= MAXUNSIGNED)
			DoFatalError ("Allocate: severe memory allocation problem");
		return (void *) malloc ((size_t) count);
	}
	else if (count >= (MAXUNSIGNED / size))
		DoFatalError ("Allocate: severe memory allocation problem");
	return (void *) malloc ((size_t) (count * size));
}

void Free (void *p)
{
	(void) free (p);
}
