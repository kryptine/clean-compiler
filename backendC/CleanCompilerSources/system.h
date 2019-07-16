/*
       system.h
       Author: Eric Nocker
       At: Department of Computer Science
           University of Nijmegen
*/

#define _SYSTEM_

#if defined (__MWERKS__) && defined (_X86_)
#	define _WINDOWS_
#endif

#if defined (applec) || (defined (__MWERKS__) && !defined (_X86_)) || defined (__MRC__)
#	define _MAC_
#	define __ppc__
#endif

#define _DEBUG_

#if ! (defined (_MAC_) || defined (_SUN_))
# define NEW_APPLY
#endif

#if defined (_MAC_)
# include "mac.h"
#elif defined (_SUN_)
# include "sun.h"
#elif defined (OS2)
#  include "os2.h"
#elif defined (_WINDOWS_)
#  include "windows_io.h"
#else
#  include "standard.h"
#endif

#include "types.t"

extern File FOpen (char *fname, char *mode);
extern int FDelete (char *fname);
extern int FClose (File f);

extern int FPutS (char *s, File f);
#ifdef _VARARGS_
extern int FPrintF (File f, char *fmt,...);
#else
extern int FPrintF (); /* (File w, char *fmt,...) */
#endif

#ifdef _VARARGS_
	extern void DoFatalError (char *fmt,...);
	extern void CmdError (char *errormsg,...);
#else
	extern void DoFatalError ();
	extern void CmdError ();
#endif

extern void *Alloc (unsigned long count, SizeT size);

extern void Free (void *p);

#define ReSize(A) (((A)+3) & ~3)
