
#if !defined (_THE__TYPES_)
#define _THE__TYPES_

#if defined (__MWERKS__) && defined (_X86_)
# define _WINDOWS_
#endif

#if (defined (__MWERKS__) && !defined (_X86_)) || defined (__MRC__)
# define POWER 1
#endif

#define NIL			0L
#define Null		0L

#define REALSIZE	2 /*1*/
#define FILESIZE	2

#define KBYTE		1024L

typedef unsigned Bool;
	enum {
		False = 0, True, MightBeTrue
	};

#define FileNameMax		256

#ifdef _WINDOWS_
# ifdef _WIN64
#  undef _WINDOWS_
#  include <windows.h>
# else
#  ifdef __MWERKS__
#      include <x86_prefix.h>
#  else
#   ifndef _X86_
#    define _X86_
#   endif
#  endif
#  include <windef.h>
#  include <winbase.h>
# endif
#endif

#endif
