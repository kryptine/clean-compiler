
#define CheckVersion

typedef short int		TwoBytesInt;
typedef int				FourBytesInt;
typedef short unsigned	TwoBytesUnsigned;
typedef unsigned		FourBytesUnsigned;
typedef double			EightBytesReal;
typedef float			FourBytesReal;

#define SizeT	unsigned long
#define SizeOf(A) ((SizeT) sizeof (A))
#define MAXUNSIGNED 20000000L

#include <string.h>
#include <sys/types.h>
#include <setjmp.h>
#include <stdlib.h>
#include <stdarg.h>
#include <stdio.h>

#define _VARARGS_

typedef FILE *File;

#define StdOut stdout
#define StdError stderr
#define StdVerboseH stdout
#define StdVerboseL stdout
#define StdTrace stdout
#define StdDebug stdout;
#define StdListTypes stdout

#define FGetC(f) fgetc(f)
#define FGetS(s,n,f) fgets(s,n,f)
#define FPutC(c,f) fputc(c,f)

/* #define System system */

int System (char *s);
int abs (int n);

/* int rand (void); */
/* int vsprintf (char *s, char *format, va_list arg); */


