
/*
	Compiler setttings
	Note that changes are of influence for project.c !!
*/

extern Bool DoCode;					/* not generated in abc file */
extern Bool DoDebug;
extern Bool DoParallel;
extern Bool DoStackLayout;
extern Bool DoStrictnessAnalysis;
extern Bool DoVerbose;
extern Bool DoWarning;	
extern Bool DoListTypes;			/* not generated in abc file */
extern Bool DoListAllTypes;			/* not generated in abc file */
extern Bool DoShowAttributes;		/* not generated in abc file */
extern Bool DoListStrictTypes;		/* not generated in abc file */
extern Bool DoStrictWarning;		/* not generated in abc file */
extern Bool DoStrictAllWarning;		/* not generated in abc file */
extern Bool DoStrictCheck;			/* not generated in abc file */
extern Bool DoDescriptors;			/* not generated in abc file */
extern Bool ListOptimizations;

extern Bool ExportLocalLabels;

extern Bool DoProfiling;
extern Bool DoTimeProfiling;

extern Bool DoReuseUniqueNodes;
extern Bool OptimizeLazyTupleRecursion;
extern Bool OptimizeTailCallModuloCons;
extern Bool WriteModificationTimes;

#define NR_BLOCKS 100
#define BLOCK_SIZE (unsigned long) (16 * KBYTE)
#define	StrictDoRelated	False

extern unsigned StrictDepth;
extern Bool StrictDoLists;
extern Bool StrictDoPaths;
extern Bool StrictDoAllPaths;
extern Bool StrictDoExtEq;
extern Bool StrictDoLessEqual;
extern Bool StrictDoEager;
extern Bool StrictDoVerbose;
extern Bool StrictDoAnnots;
extern unsigned long StrictMemUse;

extern Bool VERBOSE;

extern Bool FunctionMayFailIsError,NotUsedIsError,FunctionNotUsedIsError;
