
extern int MACVAR;
#define CheckVersion if (MACVAR != VERSION) DoFatalError ("Wrong version number")

#define SizeT		unsigned long
#define SizeOf(A)	((SizeT) sizeof (A))

#include <limits.h>
#define MAXUNSIGNED	ULONG_MAX

#define _VARARGS_

#include <string.h>
#include <stdlib.h>

#if defined (__MWERKS__) || defined (_WINDOWS_)
#	include <stdio.h>
#else
#	include <unix.h>
#endif

#include <setjmp.h>
#include <stdarg.h>

typedef FILE *File;

#ifdef _MSC_VER
extern FILE *std_out_file_p,*std_error_file_p;
# define StdOut std_out_file_p 
# define StdError std_error_file_p
#else
# define StdOut stdout
# define StdError stderr
#endif

#define FPutC(c,f) fputc(c,f)
