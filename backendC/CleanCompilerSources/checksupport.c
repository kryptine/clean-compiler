
#include "compiledefines.h"
#include "types.t"
#include "syntaxtr.t"
#include "comsupport.h"
#include "checksupport.h"
#include "settings.h"
#include "buildtree.h"
#include <ctype.h>

static int string_and_string_begin_equal (char *s1,char *s2_begin,char *s2_passed_end)
{
	char c,*s2;
	
	s2=s2_begin;
	do {
		c=*s1++;
		if (c=='\0')
			return s2==s2_passed_end;
		if (s2>=s2_passed_end)
			return 0;
	} while (*s2++ == c);

	return 0;
}

static void print_compiler_generated_function_name (char *name, char *name_end, unsigned line_nr, File file)
{
	char *parsed_digits;

	FPutS (name,file);
	
	parsed_digits=NULL;
	if (name_end[0]==';' && isdigit (name_end[1])){
		char *s;
		
		s=name_end+2;
		while (isdigit (*s))
			++s;
		if (*s==';')
			parsed_digits=s;
	}
	
	if (line_nr>0){
		FPrintF (file,"[line: %u]", line_nr);
		if (parsed_digits)
			name_end=parsed_digits;
	} else
		if (parsed_digits){
			char *d_p;

			FPutS ("[line:",file);
			for (d_p=name_end+1; d_p<parsed_digits; ++d_p)
				FPutC (*d_p,file);
			FPutC (']',file);

			name_end=parsed_digits;
		}
	FPutS (name_end,file);
}

void PrintSymbolOfIdent (char *name, unsigned line_nr, File file)
{
	char *name_end;

	for (name_end=name; *name_end!=';' && *name_end!='\0'; ++name_end)
		;

	if (*name=='\\' && name+1==name_end){
		print_compiler_generated_function_name ("<lambda>",name_end,line_nr,file);
		return;
	}

	if (*name == '_'){
		if (string_and_string_begin_equal ("c",name+1,name_end))
			print_compiler_generated_function_name ("<case>",name_end,line_nr,file);
		else if (string_and_string_begin_equal ("if",name+1,name_end))
			print_compiler_generated_function_name ("<if>",name_end,line_nr,file);	
		else
			FPutS (name, file);
		return;
	}
	
	if (line_nr > 0 && *name_end == ';' && isdigit (name_end[1])){
		char *end_name;

		for (; name!=name_end; name++)
			FPutC (*name, file);

		for (end_name = name_end + 2; *end_name!=';' && *end_name!='\0'; end_name++)
			 ;
		
		FPrintF (file, " [line: %u]", line_nr);
		
		if (*end_name == '\0')
			return;

		name = end_name;
	}

	FPutS (name, file);
}
