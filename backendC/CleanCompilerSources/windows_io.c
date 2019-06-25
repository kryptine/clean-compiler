
#ifdef __MWERKS__
#	define _WINDOWS_
#endif

#include "compiledefines.h"
#include "system.h"
#include <stdio.h>

#ifdef _WIN64
# undef _WINDOWS_
# include <windows.h>
#else
# ifdef __MWERKS__
#	include <x86_prefix.h>
# else
#	define _X86_
# endif
# include <windef.h>
# include <winbase.h>
#endif

char *GetFileExtension (FileKind kind)
{
	switch (kind){
		case abcFile:
			return ".abc";
		case obj00File:
		case obj20File:
		case obj81File:
			return ".obj";
		case iclFile:
			return ".icl";
		case dclFile:
			return ".dcl";
		case hsFile:
			return ".hs";
		case assFile:
			return ".a";
		case sunAssFile:
			return ".s";
		case applFile:
		case otherFile:
		default:
			return "";
	}	
}

char clean_lib_directory[129] = ".";

static int file_exists (char *file_name)
{
	HANDLE h;
	WIN32_FIND_DATA find_data;
	
	h=FindFirstFile (file_name,&find_data);

	if (h!=INVALID_HANDLE_VALUE){
		FindClose (h);
		return True;
	} else
		return False;
}

static int use_clean_system_files_folder=1;

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
			path_p[i]='\\';
			
			path_p+=last_dot_i+1;
			fname_p+=last_dot_i+1;
		}
		

		strcpy (path_p,"Clean System Files\\");
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
			path_p[i] = c=='.' ? '\\' : c;
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

static Bool findfilepath (char *fname,FileKind kind,char *path)
{
    char *s,*path_elem,c,*pathlist,*ext;
	int in_clean_system_files_folder;

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


	if (! (fname[0]=='\\' || (fname[0]!=0 && fname[1]==':'))){
		path_elem = pathlist;

		s=path_elem;		
		for (;;){
			c = *s;
			if (c == ';' || c == '\0'){
				char *from_p,*dest_p;
			
				from_p=path_elem;
				dest_p=path;
				while (from_p<s)
					*dest_p++ = *from_p++;
				*dest_p = '\0';

				*dest_p++ = '\\';
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

File FOpen (char *fname,FileKind kind,char *mode)
{
	char path[MAXPATHLEN];
	Bool res;

	if (fname[0]=='\\' || (fname[0]!=0 && fname[1]==':')){
		strcpy (path,fname);
		strcat (path,GetFileExtension (kind));
		return fopen (path,mode);
	}

	if (mode[0]=='r'){
		findfilepath (fname,kind,path);
		return fopen (path,mode);
	} else {
		res=findfilepath (fname,dclFile,path);
		if (!res)
			res=findfilepath (fname,iclFile,path);
		if (!res)
			res=findfilepath (fname,hsFile,path);

		if (res){
			char *p,*after_last_slash;

			after_last_slash=NULL;

			p=path;
			while (*p)
				if (*p++=='\\')
					after_last_slash=p;

			if (after_last_slash==NULL)
				after_last_slash=path;

			if (use_clean_system_files_folder){
				strcpy (after_last_slash,"Clean System Files");

				if (!file_exists (path)){
					SECURITY_ATTRIBUTES sa;

					sa.nLength = sizeof(SECURITY_ATTRIBUTES);
					sa.bInheritHandle = TRUE;
					sa.lpSecurityDescriptor = NULL;

					CreateDirectory (path,&sa);
				}

				strcat (after_last_slash,"\\");
				
				strcat (after_last_slash,skip_after_last_dot (fname));
			} else
				strcpy (after_last_slash,skip_after_last_dot (fname));
			strcat (after_last_slash,GetFileExtension (kind));
			
			return fopen (path,mode);
		} else
			return NULL;
	}	
}

int FClose (File f)
{
	return fclose ((FILE *) f);
}

int FDelete (char *fname, FileKind kind)
{
	char path[MAXPATHLEN];
	Bool res;
	
	res = findfilepath (fname,kind,path);

	if (res)
		return remove (path);
	else
		return -1;
}

int FPrintF (File f, char *fmt, ...)
{	int n;
	va_list args;
	
	va_start (args, fmt);

	n = vfprintf ((FILE*)f, fmt, args);

	va_end (args);
	return n;
}

char *FGetS (char *s, int n, File f)
{
	return fgets (s, n, (FILE *) f);
}

int FPutS (char *s, File f)
{
	return fputs (s, (FILE *) f);
}

void DoError (char *fmt, ...)
{
	va_list args;
	
	va_start (args, fmt);

	(void) vfprintf (stderr, fmt, args);
	
	va_end (args);
}

void DoFatalError (char *fmt, ...)
{
	va_list args;
	
	va_start (args, fmt);

	(void) vfprintf (stderr, fmt, args);
	
	va_end (args);

	exit (0);
}

void CmdError (char *errormsg,...)
{
	va_list args;
	
	va_start (args, errormsg);

	fputs ("Command line error: ", stdout);
	vfprintf (stdout, errormsg, args);
	fputc ('\n', stdout); 
		
	va_end (args);
}

void *Alloc (long unsigned count, SizeT size)
{	
	if (size == 1){
		if (count >= MAXUNSIGNED)
			DoFatalError ("Allocate: severe memory allocation problem");
		return (void *) malloc ((size_t) count);
	}
	else if (count >= (MAXUNSIGNED / size))
		DoFatalError ("Allocate: severe memory allocation problem");
	return (void *) malloc ((size_t) (count * size));
}

void Free (void *p)
{
	(void) free (p);
}
