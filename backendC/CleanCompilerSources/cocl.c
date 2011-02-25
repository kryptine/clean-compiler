
#include "compiledefines.h"
#include "comsupport.h"
#include "settings.h"
#include <ctype.h>
#include "compiler.h"
#include "version.h"

#include "MAIN_CLM.d"

static char usage[]=
	"Usage: \'cocl [options] [-o file] file\'\n"
	"Options: [-v] [-w] [-tc] [-d] [-sl] [-p] [-sa] [-lt] [-lset] [-lat] [-lattr]";

static void Usage (void)
{
	FPutS (usage, StdError);
	FPutC ('\n', StdError);
}

static Bool GetInt (char *s, int *i)
{
	int j;
	char *cp;
	
	for (j = 0, cp = s; *cp; cp++)
	{	if (!isdigit (*cp))
			return False;
		
		j = (10 * j) + (*cp - '0');
	}
	*i = j;
	return True;
}

static Bool SetStrictOption (char *opt)
{	int i;

	if (strcmp (opt, "w") == 0)
		DoStrictWarning = False;
	else if (strcmp (opt, "wa") == 0)
		DoStrictAllWarning = True;
	else if (strcmp (opt, "c") == 0)
		DoStrictCheck = True;
	else if (strcmp (opt, "sa") == 0)
		StrictDoAnnots = True;
	else if (opt[0] == 'd')
	{	if (GetInt (opt+1, &i))
			StrictDepth = i;
		else
			return False;
	}
	else
		return False;

	return True;
}

char *path_parameter;
#ifdef _SUN_
int use_clean_system_files;
#endif

#ifdef CLEAN2
	int StdOutReopened,StdErrorReopened;
	
	/* Windows:
	static int myfreopen (char *fileName, char *mode, FILE *oldFile)
	{
		FILE    *newFile;
	
		newFile=freopen (fileName,mode,oldFile);
		if (newFile == NULL)
			return False;
	
		return True;
	}
	
	static int myfreopen (char *fileName, char *mode, FILE *oldFile)
	{
		FILE    *newFile;
		FILE    tmpFile;
	
		newFile=fopen (fileName,mode);
		if (newFile == NULL)
			return False;
	
		tmpFile     = *oldFile;
		*oldFile    = *newFile;
		*newFile    = tmpFile;
	}
	# define freopen myfreopen
	*/
#endif

#if defined (_MAC_) && defined (GNU_C)
extern char *convert_file_name (char *file_name,char *buffer);

static FILE *freopen_with_file_name_conversion (char *file_name,char *mode,FILE *file_p)
{
	char buffer[512+1];

	file_name=convert_file_name (file_name,buffer);
	if (file_name==NULL)
		return NULL;

	return freopen (file_name,mode,file_p);
}

# define freopen freopen_with_file_name_conversion
#endif

#ifdef CLEAN2
Bool ParseCommandArgs (int argc, char **argv, char **file_name_p, char **output_file_name_p)
#else
Bool CallCompiler (int argc, char **argv)
#endif
{
	char *fname,*output_file_name;
	int i;
#ifdef OS2
	extern int window_application;

	window_application=0;
#endif

	fname = NULL;
	output_file_name=NULL;

	path_parameter=NULL;
#ifdef _SUN_
	use_clean_system_files=0;
#endif
	
	DoWarning 				= True;
	DoVerbose 				= False;
	DoCode					= True;
	DoDebug 				= False;
	DoStrictnessAnalysis	= True;
	DoStackLayout			= True /* False */;
	DoParallel				= False;
	DoShowAttributes		= True;
	DoListTypes				= False;
	DoListAllTypes			= False;
	DoListStrictTypes		= False;

	DoStrictCheck			= False;
	DoStrictWarning			= True;
	DoStrictAllWarning		= False;

	DoProfiling=False;
	DoTimeProfiling=False;
	DoReuseUniqueNodes=False;
	DoFusion=False;
	DoDescriptors=False;
	ExportLocalLabels=False;
	AddStrictnessToExportedFunctionTypes=False;

	StrictDoAnnots			= False;
	StrictDepth				= 10;/* 8; */

	FunctionMayFailIsError	= False;

#ifdef CLEAN2
	StdErrorReopened	= False;
	StdOutReopened		= False;
#endif

	for (i = 0; i < argc; i++){
		if (argv[i][0] == '-' || argv[i][0] == '+'){
			char *argv_i;
			
			argv_i=argv[i];
			
			if (strcmp (argv_i, "-v") == 0)
				DoVerbose = True;
			else if (strcmp (argv_i, "-w") == 0){
				DoWarning = False;
				DoStrictWarning	= False;
			} else if (strcmp (argv_i, "-d") == 0)
				DoDebug = True;
			else if (strcmp (argv_i, "-c") == 0)
				DoCode = False;
			else if (strcmp (argv_i, "-p") == 0)
#ifdef OS2
				window_application=1;
#else
				DoParallel = True;
#endif
#ifdef _SUN_
			else if (strcmp (argv_i, "-csf")==0)
				use_clean_system_files=1;
#endif
			else if (strcmp (argv_i, "-sl") == 0)
				DoStackLayout = True;
			else if (strcmp (argv_i, "-sa") == 0)
				DoStrictnessAnalysis = False;
			else if (strcmp (argv_i, "-lattr") == 0)
				DoShowAttributes = False;
			else if (strcmp (argv_i, "-lt") == 0)
				DoListTypes = True;
			else if (strcmp (argv_i, "-lset") == 0)
				DoListStrictTypes = True;				
			else if (strcmp (argv_i, "-lat") == 0)
				DoListAllTypes = True;
			else if (strcmp (argv_i,"-ou") == 0)
				DoReuseUniqueNodes=True;
			else if (strcmp (argv_i,"-pm") == 0)
				DoProfiling=True;
			else if (strcmp (argv_i,"-pt") == 0)
				DoTimeProfiling=True;
			else if (strcmp (argv_i,"-wmt") == 0)
				WriteModificationTimes=True;
			else if (strcmp (argv_i,"-emf") == 0)
				FunctionMayFailIsError=True;
			else if (strcmp (argv_i,"-desc") ==0)
				DoDescriptors=True;
			else if (strcmp (argv_i,"-exl") ==0)
				ExportLocalLabels=True;
			else if (strcmp (argv_i,"-fusion") == 0)
				DoFusion=True;
			else if (strcmp (argv_i,"-seft") == 0)
				AddStrictnessToExportedFunctionTypes=True;
			else if (strncmp (argv_i, "-sa", 3) == 0){
				if (!SetStrictOption (argv[i]+3)){
					CmdError ("unknown flag %s", argv[i]);
					Usage ();
					return False;
				}
			} else if (strcmp (argv_i, "-o") == 0){
				if (++i < argc)
					output_file_name = argv[i];
				else {
					CmdError ("no output file given to option -o");
					return False;
				}
			} else if (strcmp (argv_i, "-P") == 0){
				if (++i < argc)
					path_parameter = argv[i];
				else {
					CmdError ("no path list given to option -P");
					return False;
				}
			} else if (strcmp (argv_i, "-RE") == 0){
				if (++i < argc){
					freopen (argv[i],"w",StdError);
#ifdef CLEAN2
					StdErrorReopened	= True;
#endif
				} else {
					CmdError ("file name expected after -RE");
					return False;
				}
			} else if (strcmp (argv_i, "-RAE") == 0){
				if (++i < argc){
					freopen (argv[i],"aw",StdError);
#ifdef CLEAN2
					StdErrorReopened	= True;
#endif
				} else {
					CmdError ("file name expected after -RAE");
					return False;
				}
			} else if (strcmp (argv_i, "-RO") == 0){
				if (++i < argc){
					freopen (argv[i],"w",StdOut);
#ifdef CLEAN2
					StdOutReopened	= True;
#endif
				} else {
					CmdError ("file name expected after -RO");
					return False;
				}
			} else if (strcmp (argv_i, "-RAO") == 0){
				if (++i < argc){
					freopen (argv[i],"aw",StdOut);
#ifdef CLEAN2
					StdOutReopened	= True;
#endif
				} else {
					CmdError ("file name expected after -RAO");
					return False;
				}
			} else {
				CmdError ("unknown flag %s", argv_i);
				Usage ();
				return False;
			}
		} else {
			/* process (non-flag) argument */
			if (fname){
				CmdError ("only one input file allowed");
				return False;
			}
			fname = argv[i];
		}
	}

#ifdef CLEAN2
		*file_name_p=fname;
		*output_file_name_p=output_file_name;
	
	#ifdef _MAC_
		GetInitialPathList();
	#endif
	
		InitCompiler();
	
		return True;
	}
	/*
	Bool CallCompiler (int argc, char **argv)
	{
		char *fname, *output_file_name;
	
		if (!ParseCommandArgs (argc,argv,&fname,&output_file_name))
			return False;
	*/
#else

	if (fname)
		return Compile (fname,output_file_name);
	else if (DoVerbose){
		FPrintF (StdOut, "\nConcurrent Clean Compiler (Version %d.%d)\n\n", VERSION / 1000, VERSION % 1000);
		return True;
	} else {
		CmdError ("no input file given");
		Usage ();
		return False;
	}
}

#if ! defined (MAIN_CLM)
int main (int argc, char *argv[])
{
#ifdef OS2
	{
		int length;
		extern char clean_lib_directory[];

		length=strlen (argv[0]);
		
		if (length<=128){
			strcpy (clean_lib_directory,argv[0]);
	
			while (length>0){
				--length;
				if (clean_lib_directory[length]=='\\'){
					 clean_lib_directory[length]=0;
					break;
				}
			}
		} else
			clean_lib_directory[0]='\0';
	}
#endif
	if (CallCompiler (argc-1, & argv[1]))
		return 0;
	else
		return 1;
}
#endif

#endif
