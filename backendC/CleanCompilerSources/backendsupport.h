/*
	Clean string
	============
*/
typedef struct clean_string {int length; char chars [1]; } *CleanString;

/*
	Debugging
	=========
*/

extern void AssertionFailed (char *conditionString, char *file, int line);
# define	Assert(condition)	{if (!(condition)) AssertionFailed ("!(" #condition ")", __FILE__, __LINE__);}

/*
	Memory management
	=================
*/
extern void FreeConvertBuffers (void);
extern void	*ConvertAlloc (SizeT size);
# define ConvertAllocType(t) ((t*) ConvertAlloc (SizeOf (t)))
# define	ArraySize(array)	((unsigned) (sizeof (array) / sizeof (array[0])))