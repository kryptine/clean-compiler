/*******************************************************************************
 *   MAC Dependencies                                                          *
 ******************************************************************************/

typedef short          TwoBytesInt;
typedef int            FourBytesInt;
typedef unsigned short TwoBytesUnsigned;
typedef unsigned int   FourBytesUnsigned;
typedef double  EightBytesReal;
typedef float         FourBytesReal;

#define SizeT		unsigned long
#define SizeOf(A)	((SizeT) sizeof (A))

#include <limits.h>
#define MAXUNSIGNED	ULONG_MAX

#define _VARARGS_

#include <string.h>
#include <stdlib.h>
#include <stdio.h>

#include <setjmp.h>
#include <stdarg.h>

typedef FILE *File;

void GetInitialPathList (void);
void FreePathList (void);

#define StdOut stdout
#if defined (__MWERKS__) || defined (__MRC__)
#define StdError stderr
#else
#define StdError stdout
#endif

#define FGetC(f) fgetc(f)
#define FGetS(s,n,f) fgets(s,n,f)
#define FPutC(c,f) fputc(c,f)
