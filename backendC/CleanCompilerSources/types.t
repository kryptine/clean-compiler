
#if !defined (_THE__TYPES_)
#define _THE__TYPES_

#undef _WINDOWS_

#if (defined (__MWERKS__) && !defined (_WINDOWS_)) || defined (__MRC__)
# define POWER 1
#endif

#define NIL			0L
#define Null		0L

#define REALSIZE	2
#define FILESIZE	2

#define KBYTE		1024L

#ifdef THINK_C
	typedef enum {
			False = 0, True, MightBeTrue
		} Bool;
#else
	typedef unsigned Bool;
		enum {
			False = 0, True, MightBeTrue
		};
#endif

typedef enum
		{abcFile = 1, iclFile, dclFile, dumpFile, statFile,
		 stasFile, helpFile, applFile, assFile, sunAssFile,
		 obj00File, obj20File, obj81File,
		 otherFile,miraFile,miraExpFile
		} FileKind;

#define EndOfFile		((int) -1)
#define FileNameMax		256
#define FOpenMax		10
#define SeekSet
#define SeekCur
#define SeekEnd

typedef unsigned long SysTime;

#define NR_OPTIONS 9

typedef struct
{
	unsigned	opt_code:1,
				opt_debug:1,
				opt_inline:1,
				opt_listalltypes:1,
				opt_listtypes:1,
				opt_parallel:1,
				opt_stacklayout:1,
				opt_strictnessanalysis:1,
				opt_typecheck:1,
				opt_verbose:1,
				opt_warning:1,
				opt_system:1,
				opt_liststricttypes:1;
} CompilerOptions;

#ifdef _WINDOWS_
# include <stdarg.h>
# define FileTime FILETIME
# ifdef __MWERKS__
#	include <x86_prefix.h>
# else
#	define _X86_
# endif
# include <windef.h>
# include <winbase.h>
#else
# ifdef KARBON
#include <UTCUtils.h>
typedef UTCDateTime FileTime;
# else
typedef unsigned long FileTime;
# endif
#endif

#define NoFile			((FileTime) 0)

#endif
