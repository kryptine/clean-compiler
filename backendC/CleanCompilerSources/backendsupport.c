# include "system.h"
# include "comsupport.h"
# include "backendsupport.h"


/*
	Utilities
	=========
*/
# ifdef _WINDOWS_
# undef _WINDOWS_
# include <windows.h>
# define	Debugger()	DebugBreak();
# else
# define	Debugger()	{ * (int *) NULL = 0; }
# endif

void
AssertionFailed (char *conditionString, char *file, int line)
{	
	FPrintF (StdError, "Error in backend: File %s, Line %d (%s)\n", file, line, conditionString);

# ifdef _WINDOWS_
	{
		static char error[200];

		sprintf (error, "Error in backend: File %s, Line %d (%s)\nDebug ?", file, line, conditionString);
	
		if (MessageBox (NULL,error,"AssertionFailed",MB_YESNO)==IDYES)
			Debugger ();
	}
#else
	Debugger ();
#endif
} /* AssertionFailed */
