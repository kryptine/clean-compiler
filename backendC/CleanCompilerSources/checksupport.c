
#include "compiledefines.h"
#include "types.t"
#include "syntaxtr.t"
#include "comsupport.h"
#include "checksupport.h"
#include "settings.h"
#include "buildtree.h"
#include "checker.h"
#include <ctype.h>

char *ConvertSymbolKindToString (SymbKind skind)
{
	switch (skind)
	{
		case int_type: 		return "Int";
		case bool_type:		return "Bool";
		case char_type:		return "Char";
		case real_type:		return "Real";
		case file_type:		return "File";
		case array_type:		return "{ }";
		case strict_array_type:	return "{ ! }";
		case unboxed_array_type:return "{ # }";
		case world_type:	return "World";
		case procid_type:	return "ProcId";
		case redid_type:	return "RedId";
		case fun_type:		return "=>";
		case list_type:		return "List";
		case tuple_type:	return "Tuple";
		case dynamic_type:	return "Dynamic";
		default:			return "Erroneous";
	}

} /* ConvertSymbolKindToString */

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

static char *print_compiler_generated_function_name (char *name, char *name_end, unsigned line_nr, File file)
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

	return name_end+strlen (name_end);
}

static char *PrintName (char *name, char *name_end, unsigned line_nr, File file)
{
	if (*name=='\\' && name+1==name_end)
		return print_compiler_generated_function_name ("<lambda>",name_end,line_nr,file);

	if (*name == '_'){
		char *name_tail;

		if (string_and_string_begin_equal ("c",name+1,name_end))
			return print_compiler_generated_function_name ("<case>",name_end,line_nr,file);
		else if (string_and_string_begin_equal ("if",name+1,name_end))
			return print_compiler_generated_function_name ("<if>",name_end,line_nr,file);
	
		for (name_tail = name + 1; name_tail != name_end; name_tail++)
			if (isdigit (*name_tail))
				break;

		if (string_and_string_begin_equal (kCasePrefix,name,name_tail))
			FPutS ("<case expression>", file);
		else if (string_and_string_begin_equal (kLambdaPrefix,name,name_tail))
			FPutS ("<lambda expression>", file);
		else if (string_and_string_begin_equal (kListGeneratorPrefix,name,name_tail))
			FPutS ("<list comprehension>", file);
		else if (string_and_string_begin_equal (kArrayGeneratorPrefix,name,name_tail))
			FPutS ("<array comprehension>", file);
		else {
			FPutS (name, file);
			while (*name_end!='\0')
				++name_end;
			return name_end;
		}
		FPrintF (file, " [line: %u]", line_nr);
		return name_end;
	} else {
		for (; name!=name_end; name++)
			FPutC (*name, file);

		return name_end;
	}
}

void PrintSymbolOfIdent (char *name, unsigned line_nr, File file)
{
	char *next_char;

	for (next_char=name; *next_char!=';' && *next_char!='\0'; ++next_char)
		;

	next_char = PrintName (name, next_char, line_nr, file);

	if (*next_char == ';'){
		++next_char;
	
		if (isdigit (*next_char)){
			char *end_name;
		
			for (end_name = next_char + 1; *end_name!=';' && *end_name!='\0'; end_name++)
				 ;
			
			if (line_nr > 0){
				FPrintF (file, " [line: %u]", line_nr);
			} else {
				FPutC (';', file);
				PrintName (next_char, end_name, line_nr, file);
			}
			
			if (*end_name == '\0')
				return;
			next_char = end_name;
		} else
			FPutC (';', file);

		FPutS (next_char, file);
	}
}
