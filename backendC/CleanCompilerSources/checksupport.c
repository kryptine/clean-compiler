
#include "compiledefines.h"
#include "types.t"
#include "syntaxtr.t"
#include "comsupport.h"
#include "scanner.h"
#include "checksupport.h"
#include "overloading.h"
#include "settings.h"
#include "buildtree.h"
#include "checker.h"
#include <ctype.h>

char
	*Earity			= "used with wrong arity",
	*Ecyclicsyn	 	= "cyclic dependencies between synonym types",
	*EwrongdefS		= "differs from the symbol of the first rule alternative",
	*Einfix_imp_def	= "infix specification in the impl module conflicts with the def module",
	*EImplandDef1	= "definition in the impl module conflicts with the def module",
	*EImplandDef5	= "should have a type specification in the implementation rule",
	*Enodeid2		= "multiply defined",
	*Enodeid3		= "not defined";

static char
	*Etuple			= "tuples without type checking not allowed";

unsigned RuleCount,TypeSymbolCount;
SymbDef StackTop;


char *ConvertSymbolKindToString (SymbKind skind)
{
	switch (skind)
	{
		case int_type: 		return ReservedWords [(int) intsym];
		case bool_type:		return ReservedWords [(int) boolsym];
		case char_type:		return ReservedWords [(int) charsym];
		case string_type:	return ReservedWords [(int) stringsym];
		case real_type:		return ReservedWords [(int) realsym];
		case file_type:		return ReservedWords [(int) filesym];
		case array_type:		return ReservedWords [(int) arraysym];
		case strict_array_type:	return ReservedWords [(int) strictarraysym];
		case unboxed_array_type:return ReservedWords [(int) unboxedarraysym];
		case world_type:	return ReservedWords [(int) worldsym];
		case procid_type:	return ReservedWords [(int) procidsym];
		case redid_type:	return ReservedWords [(int) redidsym];
		case fun_type:		return ReservedWords [(int) applysym];
		case list_type:		return ListId	-> ident_name;
		case tuple_type:	return TupleId	-> ident_name;
#ifdef CLEAN2
		case dynamic_type:	return DynamicId -> ident_name;
#endif
		default:			return ReservedWords [errorsym];
	}

} /* ConvertSymbolKindToString */

static void PrintString (char * string, File file, int length, int * const max_length_p)
{	
	if (*max_length_p >= length)
	{	char del = string [length];

		*max_length_p -= length;

		if (del != '\0')
		{	string [length] = '\0';
			FPutS (string, file);
			string [length] = del;
		}
		else
			FPutS (string, file);
	}
	else if (*max_length_p >= 0)
	{	*max_length_p = -1;
		FPutS ("(...)", file);
 	}
 	
 } /* PrintString */
 
static void PrintChar (char c, File file, int * const max_length_p)
{
	if (*max_length_p > 0)
	{	--*max_length_p;
		FPutC (c, file);
	}
	else if (*max_length_p == 0)
	{	*max_length_p = -1;
		FPutS ("(...)", file);
	}

} /* PrintChar */

static char *PrintTypesOfSymbol (char *type_repr, File file, ModuleInfo module_info, int * const max_length_p);

static char *FindTypeName (int type_number, TypeConversionTable types)
{
	TypeConversionTable next_type;
	
	for (next_type = types; next_type; next_type = next_type -> tct_next)
	{	if (next_type -> tct_number == type_number)
			return next_type -> tct_type_symbol -> sdef_ident ->ident_name;
	}
	Assume (False, "checksupport", "FindTypeName");
	return "";

} /* FindTypeName */

static char *PrintArgumentsOfType (char *type_repr, File file, ModuleInfo module_info, int * const max_length_p)
{
	for (; ; ++type_repr)
	{	type_repr = PrintTypesOfSymbol (type_repr,file, module_info, max_length_p);
		if (*type_repr == cTypeLastArg)
			break;
		else
			PrintChar ('(', file, max_length_p);
	}
	return ++type_repr;

} /* PrintArgumentsOfType */

static void PrintName (char *name, char *name_end, unsigned line_nr, File file)
{
	if (*name == '_')
	{	char *name_tail;
	
		for (name_tail = name + 1; name_tail != name_end; name_tail++)
			if (isdigit (*name_tail))
				break;

		if (strncmp (name, kCasePrefix, name_tail - name) == 0)
			FPutS ("<case expression>", file);
		else if (strncmp (name, kLambdaPrefix, name_tail - name) == 0)
			FPutS ("<lambda expression>", file);
		else if (strncmp (name, kListGeneratorPrefix, name_tail - name) == 0)
			FPutS ("<list comprehension>", file);
		else if (strncmp (name, kArrayGeneratorPrefix, name_tail - name) == 0)
			FPutS ("<array comprehension>", file);
		else
		{	FPutS (name, file);
			return;	
		}
		FPrintF (file, " [line: %u]", line_nr);
	}
	else
	{	for (; name != name_end; name++)
		{	if (*name != '.')
			{
/*				if (*name == ':')
					FPutC (' ', file);
				else
*/					FPutC (*name, file);
			}
		}
	}

} /* PrintName */

static char *PrintTypesOfSymbol (char *type_repr, File file, ModuleInfo module_info, int * const max_length_p)
{
	char first_char = * type_repr;
	if (islower (first_char))
	{	if (first_char == 'l')
		{	PrintChar ('[', file, max_length_p);
			if (*(++type_repr) == cTypeFirstArg)
				type_repr = PrintArgumentsOfType (++type_repr, file, module_info, max_length_p);
			PrintChar (']', file, max_length_p);
			return type_repr;
		}
		else if (first_char == 't')
		{	int tuparity;
		
			++type_repr;
		
			Assume (isdigit (*type_repr),"checksupport","PrintTypesOfSymbol");
			tuparity = strtol (type_repr, & type_repr, 10);

			PrintChar ('(', file, max_length_p);

			if (*type_repr == cTypeFirstArg)
			{	type_repr = PrintArgumentsOfType (++type_repr, file, module_info, max_length_p);
				PrintChar (')', file, max_length_p);
			}
			else
			{	for (; tuparity>1; tuparity--)
					PrintString ("_,", file, 2, max_length_p);
				PrintString ("_)", file, 2, max_length_p);
			}

			return type_repr;
		}
		else if (first_char == 'a')
		{	PrintChar ('{', file, max_length_p);
			if (*(++type_repr) == cTypeFirstArg)
				type_repr = PrintArgumentsOfType (++type_repr, file, module_info, max_length_p);
			PrintChar ('}', file, max_length_p);
			return type_repr;
		}
		else if (first_char == 'd')
		{	PrintString ("<default>", file, 9, max_length_p);
			return ++type_repr;
		}
		else if (first_char == 'h')
		{	PrintString ("-> (", file, 4, max_length_p);
			++type_repr;
			if (*type_repr==cTypeFirstArg)
				type_repr = PrintArgumentsOfType (type_repr+1, file, module_info, max_length_p);

			PrintChar (')', file, max_length_p);
			return type_repr;
		}
		else if (first_char == 'u')
		{	int type_number;
			char *type_name;
		
			++type_repr;
		
			Assume (isdigit (*type_repr),"checksupport","PrintTypesOfSymbol");
			type_number = strtol (type_repr, & type_repr, 10);

			type_name = FindTypeName (type_number, module_info -> mi_type_table);
			
			PrintString (type_name, file, strlen (type_name), max_length_p);
			
			if (*type_repr == cTypeFirstArg)
			{	PrintChar ('(', file, max_length_p);
				type_repr = PrintArgumentsOfType (++type_repr, file, module_info, max_length_p);
				PrintChar (')', file, max_length_p);
			}
			
			return type_repr;
		}
		else
		{	int symbkind;
			char *symbol_string;
			for (symbkind = int_type;  symbkind < Nr_Of_Basic_Types; symbkind++)
			{	if (BasicTypeIds [symbkind] == first_char)
					break;
			}
			
			Assume (symbkind < Nr_Of_Basic_Types,"checksupport","PrintTypesOfSymbol");
			symbol_string = ConvertSymbolKindToString ((SymbKind) symbkind);
			
			PrintString (symbol_string, file, strlen (symbol_string), max_length_p);
			return ++type_repr;
		}
	}
	else if (first_char == '!')
	{	PrintString ("{!", file, 2, max_length_p);
		if (*(++type_repr) == cTypeFirstArg)
			type_repr = PrintArgumentsOfType (++type_repr, file, module_info, max_length_p);
		PrintChar ('}', file, max_length_p);
		return type_repr;
	}
	else if (first_char == '#')
	{	PrintString ("{#", file, 2, max_length_p);
		if (*(++type_repr) == cTypeFirstArg)
			type_repr = PrintArgumentsOfType (++type_repr, file, module_info, max_length_p);
		PrintChar ('}', file, max_length_p);
		return type_repr;
	}
	else if (first_char == cTypeFirstArg)
	{	char *type_end;
		for (type_end = ++type_repr; *type_end != cTypeLastArg; type_end++)
			;

		PrintString (type_repr, file, type_end - type_repr, max_length_p);
		
		return ++type_end;
	}
	else
	{	char *type_end;
		for (type_end = type_repr; *type_end != cTypeDelimiter && *type_end != '\0' && *type_end != cTypeFirstArg && *type_end != cTypeLastArg; type_end++)
			if (*type_end == '.')
				type_end++;

		PrintString (type_repr, file, type_end - type_repr, max_length_p);
		
		if (*type_end == cTypeFirstArg)
		{	PrintChar ('(', file, max_length_p);
			type_end = PrintArgumentsOfType (++type_end, file, module_info, max_length_p);
			PrintChar (')', file, max_length_p);
		}
		return type_end;
	}

} /* PrintTypesOfSymbol */

#define _ANALYSE_IDENT_ 		/* also in optimisations.c */
#ifndef CLEAN2
#define _ANALYSE_INSTANCE_TYPES_
#endif
#define MAX_SYMBOL_EXTENSION_SIZE 40

void PrintSymbolOfIdent (Ident sid, unsigned line_nr, File file)
{
	char *next_char,*name;
	int print_length = MAX_SYMBOL_EXTENSION_SIZE;

	name  = sid -> ident_name;

#ifdef _ANALYSE_IDENT_
	if (*name == cTypeDelimiter)
	{	for (next_char = name + 1; *next_char == cTypeDelimiter; next_char++)
			;
		if (*next_char == '\0')
		{	FPutS (name, file);
			return;
		}
		else
			next_char--;
	}
	else
	{	for (next_char = name; *next_char != cTypeDelimiter && *next_char != '\0';  next_char++)
			if (*next_char == '.')
			{	next_char++;
				if (*next_char == '\0')
					break;
			}
	}	
	
	PrintName (name, next_char, line_nr, file);

	if ((*next_char) == cTypeDelimiter && next_char[1] != '\0')
	{	next_char++;
	
		if (isdigit (* next_char))
		{	char *end_name;
		
			for (end_name = next_char + 1; *end_name != cTypeDelimiter && *end_name != '\0'; end_name++)
				 ;
			
			if (line_nr > 0)
			{	FPrintF (file, " [line: %u]", line_nr);
				if (*end_name == '\0')
					return;
			}
			else
			{	FPutC (cTypeDelimiter, file);
			
				PrintName (next_char, end_name, line_nr, file);
				
				if (*end_name == '\0')
					return;
			}
			
			next_char = end_name + 1;
		}

#ifdef _ANALYSE_INSTANCE_TYPES_		
		FPutS (" (", file);

		next_char = PrintTypesOfSymbol (next_char, file, sid -> ident_mod_info, & print_length);

		for (;  *next_char == cTypeDelimiter; )
		{	FPutC (',', file);
			next_char = PrintTypesOfSymbol (++next_char, file, sid -> ident_mod_info, & print_length);
		}

		FPutC (')', file);
#else
		FPutS (next_char, file);
#endif /* _ANALYSE_INSTANCE_TYPES_ */
	}

#else

	FPutS (name, file);

#endif	
}

void CheckWarningOrError2 (Bool error,char *msg1,char *msg2,char *msg3)
{
	StaticMessage (error,"%S","%s,%s %s",CurrentSymbol,msg1,msg2,msg3);
}

void CheckError (char *msg1,char *msg2)
{
	StaticMessage (True,"%S","%s %s",CurrentSymbol,msg1,msg2);
}

void CheckNodeError (char *msg1,char *msg2,NodeP node_p)
{
	if (node_p->node_line>=0){
		unsigned old_CurrentLine;
		
		old_CurrentLine=CurrentLine;
		
		CurrentLine=node_p->node_line;
		StaticMessage (True,"%S","%s %s",CurrentSymbol,msg1,msg2);
		
		CurrentLine=old_CurrentLine;
	} else
		StaticMessage (True,"%S","%s %s",CurrentSymbol,msg1,msg2);
}

void CheckNodeSymbolError (struct symbol *symbol,char *msg,NodeP node_p)
{
	if (node_p->node_line>=0){
		unsigned old_CurrentLine;
		
		old_CurrentLine=CurrentLine;
		
		CurrentLine=node_p->node_line;
		StaticMessage (True,"%S","%S %s",CurrentSymbol,symbol,msg);
		
		CurrentLine=old_CurrentLine;
	} else
		StaticMessage (True,"%S","%S %s",CurrentSymbol,symbol,msg);
}

void CheckSymbolError (struct symbol *symbol,char *msg)
{
	StaticMessage (True,"%S","%S %s",CurrentSymbol,symbol,msg);
}

void CheckWarning (char *msg1,char *msg2)
{
	StaticMessage (False,"%S","%s %s",CurrentSymbol,msg1,msg2);
}

void CheckWarningOrError (Bool error,char *msg1,char *msg2)
{
	StaticMessage (error,"%S","%s %s",CurrentSymbol,msg1,msg2);
}

void CheckSymbolWarning (struct symbol *symbol,char *msg)
{
	StaticMessage (False,"%S","%S %s",CurrentSymbol,symbol,msg);
}

void CheckSymbolWarningOrError (Bool error,struct symbol *symbol,char *msg)
{
	StaticMessage (error,"%S","%S %s",CurrentSymbol,symbol,msg);
}

extern Ident TupleId;

void TupleError (void)
{
	CheckError (TupleId->ident_name,Etuple);
}

