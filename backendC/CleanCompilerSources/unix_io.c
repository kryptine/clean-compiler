/*******************************************************************************
 *     Concurrent Clean Simulator: simple_sun_io.c                             *
 *     ===========================================                             *
 *     At: Department of Computer Science                                      *
 *         University of Nijmegen                                              *
 *     Version: 1.1                                                            *
 ******************************************************************************/
 
#include "system.h"

#if !defined (applec) || defined (__MWERKS__)
#	include <sys/types.h>
#	include <sys/file.h>
#	include <sys/param.h>
#endif

#if !(defined (applec) || defined (_PC_))
#	include <unistd.h>
#endif

char *GetFileExtension (FileKind kind)
{
	switch (kind){
		case abcFile:		return ".abc";
		case obj00File:		return ".obj0";
		case obj20File:		return ".obj1";
		case obj81File:		return ".obj2";
		case iclFile:		return ".icl";
		case dclFile:		return ".dcl";
		case assFile:		return ".a";
		case sunAssFile:	return ".s";
		case applFile:
		case otherFile:
		default:			return "";
	}	
}

#define	SEARCHPATH	"CLEANPATH"

#ifdef SOLARIS
char clean_lib_directory[145] = "#$@CLEANLIB  %*&.";
# define clean_lib_directory (&clean_lib_directory[16])
#else
char clean_lib_directory[129] = ".";
#endif

#define CLEANLIB	clean_lib_directory

static int use_clean_system_files_folder=1;

char *PATHLIST = SEARCHPATH;

static Bool file_exists (char *path)
{
	return access (path, F_OK) == 0;
}

extern char *path_parameter;

static void append_file_name_and_ext (char *path_p,char *fname_p,char *ext,int in_clean_system_files_folder)
{
	int i;
	char c;
	
	if (in_clean_system_files_folder){
		int last_dot_i;

		last_dot_i = -1;

		i=0;
		while (c=fname_p[i], c!='\0'){
			if (c=='.')
				last_dot_i=i;
			++i;
		}

		if (last_dot_i>=0){
			i=0;
			while (i<last_dot_i){
				path_p[i]=fname_p[i];
				++i;
			}
			path_p[i]='/';
			
			path_p+=last_dot_i+1;
			fname_p+=last_dot_i+1;
		}
		

		strcpy (path_p,"Clean System Files/");
		path_p += 19;

		i=0;
		while (c=fname_p[i], c!='\0'){
			path_p[i] = c;
			++i;
		}
		path_p+=i;
	} else {
		int i;
		char c;

		i=0;
		while (c=fname_p[i], c!='\0'){
			path_p[i] = c=='.' ? '/' : c;
			++i;
		}
		path_p+=i;
	}

	i=0;
	do {
		c=ext[i];
		path_p[i]=c;
		++i;
	} while (c!='\0');
}

static Bool findfilepath (char *fname,FileKind kind,char *mode,char *path)
{
    char *s,*path_elem,c,*pathlist,*ext;
	int in_clean_system_files_folder;

	if (path_parameter==NULL)
	    pathlist=getenv ("CLEANPATH");
	else
		pathlist=path_parameter;

    if (pathlist==NULL)
		pathlist=".";

	ext = GetFileExtension (kind);

	in_clean_system_files_folder=0;

	if (use_clean_system_files_folder)
		switch (kind){
			case abcFile:
			case obj00File:
			case obj20File:
			case obj81File:
				in_clean_system_files_folder=1;
		}


	if (! (fname[0]=='/')){
		path_elem = pathlist;

		s=path_elem;		
		for (;;){
			c = *s;
			if (c == ':' || c == '\0'){
				char *from_p,*dest_p;
			
				from_p=path_elem;
				dest_p=path;
				while (from_p<s)
					*dest_p++ = *from_p++;
				*dest_p = '\0';

				*dest_p++ = '/';
				append_file_name_and_ext (dest_p,fname,ext,in_clean_system_files_folder);
				if (file_exists (path))
					return True;
		    
			    if (c == '\0')
			    	break;
	
				path_elem = ++s;
			} else
			    ++s;
		}
	}

	append_file_name_and_ext (path,fname,ext,in_clean_system_files_folder);

 	return file_exists (path);
}

#if 0
static Bool findfilepath (char *fname, FileKind kind, char *mode, char *path)
{
	int accmode;
    char *s, *pathelem,c;
    char *getenv ();
    char *pathlist;
    char pathbuf[MAXPATHLEN];			/* buffer for tmp file name */
	char *ext;

	accmode = F_OK;		      		/* required file access mode */
    pathlist = getenv (SEARCHPATH);
	
	ext = GetFileExtension (kind);
	
    /* only scan current directory if path nonexistent */
    if (pathlist == (char *) 0)
		pathlist = ".";

    /* interpret file mode */
    for (s = mode; *s; s++)
    {	switch (*s)
		{
		case 'r':
		    accmode |= R_OK;
		    break;
		case 'w':
		case 'a':
		    accmode |= W_OK;
		    break;
		case '+':
		    accmode |= (R_OK | W_OK);
		    break;
		}
    }
    
    /* no searching on absolute paths or if not read only */
    if (fname[0] == '/' || (accmode & W_OK) == W_OK)
	{	(void) strcpy (path, fname);
		(void) strcat (path, ext);
		if ((accmode & W_OK) == W_OK || access (path, accmode) == 0)
			return True;
		else
			return False;
	}

    /* start scanning path list */
    s        = strcpy (pathbuf, pathlist);
    pathelem = s;
    for (c = *s;;c = *s){
#if defined (OS2) || defined (DOS)
		if (c == ';' || c == '\0'){
#else
		if (c == ':' || c == '\0'){
#endif
			*s = '\0';
		    (void) strcpy (path, pathelem);
		    (void) strcat (path, "/");
		    (void) strcat (path, fname);
		    (void) strcat (path, ext);
		    if (access (path, accmode) == 0)
				return True;
		    *s = c;
		    if (c == '\0')
		    	break;
		    pathelem = ++s;
		}
		else
		    ++s;
    }

	/* try CLEANLIB */
 	strcpy (path, CLEANLIB);
	strcat (path, "/");
	strcat (path, fname);
	strcat (path, ext);
	if (access (path, accmode) == 0)
		return True;

	/* try . */
	(void) strcpy (path, fname);
	(void) strcat (path, ext);

 	return ((Bool) (access (path, accmode) == 0));
}
#endif

static char *skip_after_last_dot (char *s)
{
	int i,after_last_dot_i;
	char c;

	after_last_dot_i=0;

	i=0;
	while (c=s[i],c!='\0'){
		++i;
		if (c=='.')
			after_last_dot_i=i;
	}
	
	return &s[after_last_dot_i];
}

#include <sys/time.h>
#include <sys/resource.h>
#include <sys/stat.h>

File FOpen (char *wname, FileKind kind, char *mode)
{
	char path[MAXPATHLEN];
	Bool res;
	
	if (mode[0]=='r')
	{
		if (findfilepath (wname, kind, mode, path))
			return (File) fopen (path, mode);
		else
			return (File) Null;
	}
	else
	{
		res=findfilepath (wname,dclFile,mode,path);
		if (!res)
			res=findfilepath (wname,iclFile,mode,path);

		if (res){
			char *p,*after_last_slash;

			after_last_slash=NULL;

			p=path;
			while (*p)
				if (*p++=='/')
					after_last_slash=p;

			if (after_last_slash==NULL)
				after_last_slash=path;

			if (use_clean_system_files_folder){
				strcpy (after_last_slash,"Clean System Files");

				if (access (path,F_OK)!=0){
					if (mkdir (path,0777)!=0)
						return NULL;
				}

				strcat (after_last_slash,"/");

				strcat (after_last_slash,skip_after_last_dot (wname));
			} else
				strcpy (after_last_slash,skip_after_last_dot (wname));
			strcat (after_last_slash,GetFileExtension (kind));
			
			return fopen (path,mode);
		} else
			return NULL;
	}	

} /* FOpen */


int FClose (File f)
{
	return fclose ((FILE *) f);
} /* FClose */

int FDelete (char *fname, FileKind kind)
{
	char path[MAXPATHLEN];
	Bool res;
	
	res = findfilepath (fname, kind, "w", path);

	if (res)
		return remove (path);
	else
		return -1;
} /* FDelete */

#ifndef FPutC
int FPutC (int c, File f)
{
	return fputc (c, (FILE *) f);
}
#endif

#ifndef FGetC
int FGetC (File f)
{
	return fgetc ((FILE *) f);
}
#endif

int FPrintF (File f, char *fmt, ...)
{
	int n;
	va_list args;
	
	va_start (args, fmt);

	n = vfprintf ((FILE*)f, fmt, args);

	va_end (args);
	return n;
}

#ifndef FGetS
char *FGetS (char *s, int n, File f)
{
	return fgets (s, n, (FILE *) f);
}
#endif

int FPutS (char *s, File f)
{
	return fputs (s, (FILE *) f);
} /* FPutS */

/* Error Handling */
	
void DoError (char *fmt, ...)
{	va_list args;
	
	va_start (args, fmt);

	(void) vfprintf (StdError, fmt, args);
	
	va_end (args);
}

void DoFatalError (char *fmt, ...)
{	va_list args;
	
	va_start (args, fmt);

	(void) vfprintf (StdError, fmt, args);
	
	va_end (args);

	exit (0);
}

void CmdError (char *errormsg,...)
{	va_list args;
	
	va_start (args, errormsg);

	fputs ("Command line error: ", stdout);
	vfprintf (stdout, errormsg, args);
	fputc ('\n', stdout); 
		
	va_end (args);
}

/*******************************************************************************
 *     Storage                                                                 *
 ******************************************************************************/

void *Alloc (long unsigned count, SizeT size)
{	
	if (size == 1)
	{	if (count >= MAXUNSIGNED)
			DoFatalError ("Allocate: severe memory allocation problem");
		return (void *) malloc ((size_t) count);
	}
	else if (count >= (MAXUNSIGNED / size))
		DoFatalError ("Allocate: severe memory allocation problem");
	return (void *) malloc ((size_t) (count * size));
} /* Alloc */

void Free (void *p)
{
	(void) free (p);
} /* Free */
