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

	Debugger ();
} /* AssertionFailed */

/*
	Memory management
	=================
*/

static enum {kMemoryInitClear, kMemoryInitSet} gMemoryInit = kMemoryInitSet;

# define	kConvertBufferSize	(32 * 1024)

typedef struct convert_buffer ConvertBufferS, *ConvertBufferP;

struct convert_buffer
{
	ConvertBufferP	cb_next;
	char			cb_memory [kConvertBufferSize];
};

static void
InvalidateMemory (void *memory, size_t size)
{
	char	value, *p;
	int		i;

	switch (gMemoryInit)
	{
		case kMemoryInitClear:
			value	= 0;
			break;
		case kMemoryInitSet:
			value	= ~0;
			break;
		default:
			Assert (False);
			break;
	}

	p	= memory;
	for (i = 0; i < size; i++)
		*p++	= value;
} /* InvalidateMemory */

static ConvertBufferP	gFirstBuffer = NULL, gCurrentBuffer = NULL;
static char 			*gMemory;
static long gBytesLeft = 0;

static void
AllocConvertBuffer (void)
{
	ConvertBufferP	newBuffer;

	newBuffer	= (ConvertBufferP) malloc (sizeof (ConvertBufferS));

	if (newBuffer == NULL)
		FatalCompError ("backendsupport.c", "AllocConvertBuffer", "out of memory");

	if (gFirstBuffer == NULL)
		gCurrentBuffer	= gFirstBuffer				= newBuffer;
	else
		gCurrentBuffer	= gCurrentBuffer->cb_next	= newBuffer;

	gCurrentBuffer->cb_next	=	NULL;

	gBytesLeft	= kConvertBufferSize;
	gMemory		= gCurrentBuffer->cb_memory;

	InvalidateMemory (gMemory, kConvertBufferSize);

	if (gFirstBuffer == NULL)
		gFirstBuffer	= gCurrentBuffer;
} /* AllocConvertBuffer */

void
FreeConvertBuffers (void)
{
	ConvertBufferP	buffer;

	buffer	= gFirstBuffer;

	while (buffer != NULL)
	{
		ConvertBufferP	nextBuffer;

		nextBuffer	= buffer->cb_next;

		InvalidateMemory (buffer, sizeof (ConvertBufferS));
		free (buffer);

		buffer	= nextBuffer;
	}

	gFirstBuffer	= NULL;
	gCurrentBuffer	= NULL;
	gBytesLeft	= NULL;
} /* FreeConvertBuffers */

void *
ConvertAlloc (SizeT size)
{
	void	*memory;

	size	= (size+3) & ~3;

	if (size > gBytesLeft)
		AllocConvertBuffer ();

	Assert (size <= gBytesLeft);

	memory	= gMemory;	
	gBytesLeft	-= size;
	gMemory	+=	size;

	return ((void *) memory);
} /* ConvertAlloc */
