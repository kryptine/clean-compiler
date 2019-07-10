 
#include "system.h"

#if !defined (applec) || defined (__MWERKS__)
#	include <sys/types.h>
#	include <sys/file.h>
#	include <sys/param.h>
#endif

#if !(defined (applec) || defined (_PC_))
#	include <unistd.h>
#endif

#include <sys/time.h>
#include <sys/resource.h>
#include <sys/stat.h>

File FOpen (char *fname, char *mode)
{
	return (File) fopen (fname, mode);
				}

int FClose (File f)
{
	return fclose ((FILE *) f);
} /* FClose */

int FDelete (char *fname)
{
	return remove (fname);
}

#ifndef FPutC
int FPutC (int c, File f)
{
	return fputc (c, (FILE *) f);
}
#endif

int FPrintF (File f, char *fmt, ...)
{
	int n;
	va_list args;
	
	va_start (args, fmt);

	n = vfprintf ((FILE*)f, fmt, args);

	va_end (args);
	return n;
}

int FPutS (char *s, File f)
{
	return fputs (s, (FILE *) f);
} /* FPutS */

/* Error Handling */
	
void DoError (char *fmt, ...)
{	va_list args;
	
	va_start (args, fmt);

	(void) vfprintf (StdError, fmt, args);
	
	va_end (args);
}

void DoFatalError (char *fmt, ...)
{	va_list args;
	
	va_start (args, fmt);

	(void) vfprintf (StdError, fmt, args);
	
	va_end (args);

	exit (0);
}

void CmdError (char *errormsg,...)
{	va_list args;
	
	va_start (args, errormsg);

	fputs ("Command line error: ", stdout);
	vfprintf (stdout, errormsg, args);
	fputc ('\n', stdout); 
		
	va_end (args);
}

/*******************************************************************************
 *     Storage                                                                 *
 ******************************************************************************/

void *Alloc (long unsigned count, SizeT size)
{	
	if (size == 1)
	{	if (count >= MAXUNSIGNED)
			DoFatalError ("Allocate: severe memory allocation problem");
		return (void *) malloc ((size_t) count);
	}
	else if (count >= (MAXUNSIGNED / size))
		DoFatalError ("Allocate: severe memory allocation problem");
	return (void *) malloc ((size_t) (count * size));
} /* Alloc */

void Free (void *p)
{
	(void) free (p);
} /* Free */
