/*
Version 1.0 26/08/1994
Author: Sjaak Smetsers 
*/

#define STATES_GENERATED
#define STORE_UNIQUE_ATTRIBUTES_IN_TYPE_NODES

#include "compiledefines.h"
#include "types.t"
#include "system.h"
#include "settings.h"
#include "syntaxtr.t"
#include "comsupport.h"

#include "tctypes.t"
#include "scanner.h"
#include "comparser.h"
#include "sizes.h"
#include "checker.h"
#include "transform.h"
#include "sa.h"
#include "typechecker.h"
#include "typechecker2.h"
#include "typeconv.h"
#include "overloading.h"
#include "checksupport.h"
#include "statesgen.h"
#include "buildtree.h"

typedef
	struct attr_ref_count_info
	{	BITVECT			  		arci_used;
		BITVECT			  		arci_multiply_used;
		BITVECT			  		arci_implicitly_attributed;
		struct attr_ref_count_info  * arci_next;
	} * ARC_Info;

static ARC_Info CurrentARC_Info;

static ARC_Info NewARC_Info (void)
{
	ARC_Info new = CompAllocType (struct attr_ref_count_info);
	new -> arci_used				= ALLBITSCLEAR;
	new -> arci_multiply_used		= ALLBITSCLEAR;
	new -> arci_implicitly_attributed	= ALLBITSCLEAR;
	new -> arci_next = NULL;
	return new;

} /* NewARC_Info */

static void ClearARC_Info (void)
{
	ARC_Info next;
	for (next = CurrentARC_Info; next; next = next -> arci_next)
	{	next -> arci_used 				= ALLBITSCLEAR;
		next -> arci_multiply_used		= ALLBITSCLEAR;
		next -> arci_implicitly_attributed	= ALLBITSCLEAR;
	}
	
} /* ClearARC_Info */

static void UpdateRefCountInfo (int attr_var, Bool used_implicitly)
{
	ARC_Info attrinfo = CurrentARC_Info;
	while (attr_var >= 32)
	{	attr_var -= 32;
		if (attrinfo -> arci_next == NULL)
			attrinfo -> arci_next = NewARC_Info ();
		attrinfo = attrinfo -> arci_next;
	}
	if (used_implicitly)
		attrinfo -> arci_implicitly_attributed |= BIT (attr_var);
	if (BITTEST (attrinfo -> arci_used, attr_var))
		attrinfo -> arci_multiply_used |= BIT (attr_var);
	else
		attrinfo -> arci_used |= BIT (attr_var);

} /* UpdateRefCountInfo */

static Bool DetermineRefCountOfAttributeVarsInTypeVar (TypeNode type_var)
{
	if (type_var -> type_node_attribute >= FirstUniVarNumber)
	{	if (type_var -> type_node_tv != NULL)
		{	if (! TestMark (type_var -> type_node_tv, tv_mark, TV_UNIQUE_VARIABLE_PRINT_MASK))
			{	SetMark (type_var -> type_node_tv, tv_mark, TV_UNIQUE_VARIABLE_PRINT_MASK);
				UpdateRefCountInfo (type_var -> type_node_attribute - FirstUniVarNumber, False);
			}
		}
		return True;
	}
	else
		return False;

} /* DetermineRefCountOfAttributeVarsInTypeVar */

static BITVECT CombineTypeArguments (ConsVarList cons_var, int arity1, BITVECT args1, int arity2, BITVECT args2)
{
	BITVECT combined_args = ALLBITSCLEAR;
	int cons_var_arity = cons_var -> cvl_arity;
				
	int i, j;

	for (j = 0; j < cons_var_arity; j++)
	{	BITVECT cons_var_prop = cons_var -> cvl_argclass [j].tac_uniprop;

		for (i = 0; i < arity1; i++)
		{	if (BITTEST (cons_var_prop, i) && BITTEST (args1, i))
				combined_args |= BIT (j);
		}

		for (i = 0; i < arity2; i++)
		{	if (BITTEST (cons_var_prop, i+arity1) && BITTEST (args2, i))
				combined_args |= BIT (j);
		}
	}

	return combined_args;

} /* CombineTypeArguments */

static Bool DetermineRefCountOfAttributeVarsInNode (TypeNode type_node);

static Bool DetermineRefCountOfAttributeVarsInTypeConsNode (TypeNode type_node, Symbol type_symb,
	int nr_of_extra_args, BITVECT extra_prop_args)
{
	TypeArgs type_args;
	int arg_nr;
	
	Bool contains_propating_univars = False;

	ConsVarList cons_vars;
	BITVECT uniprop, cons_var_vect, propagating_args = ALLBITSCLEAR;
	
	
	if (type_symb -> symb_kind == definition)
	{	cons_var_vect = DetermineConsVarsOfTypeCons (type_symb -> symb_def, & cons_vars);
		uniprop = DetermineUniPropOfTypeCons (type_symb -> symb_def);
	}
	else
	{	cons_var_vect	= ALLBITSCLEAR;
		cons_vars		= NULL;
		if (type_symb -> symb_kind == fun_type)
			uniprop = ALLBITSCLEAR;
		else if (type_symb -> symb_kind == apply_symb)
 			uniprop = BIT (0);
 		else
			uniprop = ALLBITSSET;
	}
	
	for (type_args = type_node -> type_node_arguments, arg_nr=0; type_args;
		type_args = type_args -> type_arg_next, arg_nr++)
	{	if (! BITTEST (cons_var_vect, arg_nr))
		{	if (DetermineRefCountOfAttributeVarsInNode (type_args -> type_arg_node))
			{	propagating_args |= BIT(arg_nr);
				if (BITTEST (uniprop, arg_nr))
					contains_propating_univars = True;
			}
		}
	}

	for (type_args = type_node -> type_node_arguments, arg_nr=0; cons_vars; cons_vars = cons_vars -> cvl_next)
	{	for (; type_args != NULL && arg_nr < cons_vars -> cvl_number; arg_nr++, type_args = type_args -> type_arg_next)
			;
		if (type_args != NULL)
		{	TypeNode cons_node = type_args -> type_arg_node;
		
			if (cons_node -> type_node_is_var)
			{	if (DetermineRefCountOfAttributeVarsInTypeVar (cons_node) && BITTEST (uniprop, arg_nr))
					contains_propating_univars = True;
			}
			else 
			{	BITVECT comb_args_prop = CombineTypeArguments (cons_vars, type_node -> type_node_arity, propagating_args, 
								nr_of_extra_args, extra_prop_args);
					
				if (DetermineRefCountOfAttributeVarsInTypeConsNode (cons_node, cons_node -> type_node_symbol,
							cons_vars -> cvl_arity, comb_args_prop) && BITTEST (uniprop, arg_nr))
					contains_propating_univars = True;
			}
		}
	}
	
	if (! contains_propating_univars)
	{	extra_prop_args &= uniprop >> type_node -> type_node_arity;
	
		for (arg_nr = 0; arg_nr < nr_of_extra_args; arg_nr ++)
		{	if (BITTEST (extra_prop_args, arg_nr))
			{	contains_propating_univars = True;
				break;
			} 
		}
	}
	
	if (type_node -> type_node_attribute >= FirstUniVarNumber)
	{	UpdateRefCountInfo (type_node -> type_node_attribute - FirstUniVarNumber, contains_propating_univars);
		return True;
	}
	else
		return contains_propating_univars;

} /* DetermineRefCountOfAttributeVarsInTypeConsNode */

static Bool DetermineRefCountOfAttributeVarsInNode (TypeNode type_node)
{
	if (type_node -> type_node_is_var)
		return DetermineRefCountOfAttributeVarsInTypeVar (type_node);
	else
	{	Symbol typesymb = type_node -> type_node_symbol;

		if (typesymb -> symb_kind < Nr_Of_Basic_Types)
		{	if (type_node -> type_node_attribute >= FirstUniVarNumber)
			{	UpdateRefCountInfo (type_node -> type_node_attribute - FirstUniVarNumber, False);
				return True;
			}
			else
				return False;
		}
		else
			return DetermineRefCountOfAttributeVarsInTypeConsNode (type_node, typesymb, 0, ALLBITSCLEAR);
	}


} /* DetermineRefCountOfAttributeVarsInNode */

static void DetermineRefCountOfAttributeVars (TypeAlts type)
{
	TypeArgs type_args;
	UniVarEquations attr_equas;
	
	ClearARC_Info ();

	for (type_args = type -> type_alt_lhs -> type_node_arguments; type_args; type_args = type_args -> type_arg_next)
		DetermineRefCountOfAttributeVarsInNode (type_args -> type_arg_node);
	DetermineRefCountOfAttributeVarsInNode (type -> type_alt_rhs);

	for (attr_equas = type -> type_alt_attr_equations; attr_equas; attr_equas = attr_equas -> uve_next)
	{	AttributeKindList next;
		UpdateRefCountInfo (attr_equas -> uve_demanded - FirstUniVarNumber, False);
		for (next = attr_equas -> uve_offered; next; next = next -> akl_next)
			UpdateRefCountInfo (next -> akl_elem - FirstUniVarNumber, False);
	}

} /* DetermineRefCountOfAttributeVars */

static char *TypeConv = "typeconv";

static unsigned RetrieveRefCountInfo (int attr_var, Bool *used_implicitly)
{
	ARC_Info attrinfo = CurrentARC_Info;
	unsigned newnumber = 0;
	int i;
	
	while (attr_var >= 32)
	{	attr_var -= 32;
		for (i = 0; i < 32; i++)
		{	if (BITTEST (attrinfo -> arci_multiply_used, i))
				newnumber++;
		}
		attrinfo = attrinfo -> arci_next;
		Assume (attrinfo != NULL, TypeConv, "RetrieveRefCountInfo");
	}
	if (BITTEST (attrinfo -> arci_multiply_used, attr_var))
	{	for (i = 0; i < attr_var; i++)
		{	if (BITTEST (attrinfo -> arci_multiply_used, i))
				newnumber++;
		}
		*used_implicitly = False;
		return newnumber + 1;
	}
	else
	{	*used_implicitly = BITTEST (attrinfo -> arci_implicitly_attributed, attr_var);
		return 0;
	}
		
} /* RetrieveRefCountInfo */

static char *PrintVars = "abcdefghijklmnopqrst";
#define NrOfPrintVars 20

static char *PrintUniVars = "uvwxyz";
#define NrOfPrintUniVars 6

#define cDoPrintAnnot	True
#define cDontPrintAnnot	False

static void PrintNode (TypeNode node, Bool brackets, Bool strict_context, Bool print_annot);
static unsigned RetrieveRefCountInfo (int attr_var, Bool *used_implicitly);

static void PrintAttributeVariable (unsigned attr_nr)
{
	if (attr_nr <= NrOfPrintUniVars)
		FPrintF (StdListTypes, "%c", PrintUniVars [attr_nr - 1]);
	else
		FPrintF (StdListTypes, "u%d", attr_nr - NrOfPrintUniVars);

} /* PrintAttributeVariable */

extern Bool DoShowAttributes;

#define cDoPrintColon	True

static Bool PrintAttribute (AttributeKind attr, Bool print_colon)
{
	if (attr == UniqueAttr)
	{	FPutC ('*', StdListTypes);
		return True;
	}
	else if (DoShowAttributes)
	{	Bool used_implicitly;
		unsigned attr_nr = RetrieveRefCountInfo (attr - FirstUniVarNumber, & used_implicitly);

		if (attr_nr == 0)
		{	if (! used_implicitly)
			{	FPutC ('.', StdListTypes);
				return True;
			}
			else
				return False;
		}
		else
		{	PrintAttributeVariable (attr_nr);
			if (print_colon)
				FPutC (':', StdListTypes);
			return True;
		}
	}
	else
		return False;
	
} /* PrintAttribute */

#define cDoPrintAttribute	True
#define cDontPrintAttribute	False

#define cInAStrictContext	True
#define cNotInAStrictContext	False

#define cPrintBrackets		True
#define cDontPrintBrackets	False


static void PrintArgument (TypeArgs arg, Bool brackets, Bool strict_context, Bool print_attribute)
{
	if (arg -> type_arg_node -> type_node_is_var)
	{	if (strict_context)
#ifdef STATES_GENERATED
# if 1
			strict_context = arg -> type_arg_node -> type_node_annotation==StrictAnnot;
# else
			strict_context = !IsLazyState (arg -> type_arg_node -> type_node_state);
# endif
#else
			strict_context = arg -> type_arg_node -> type_node_state.state_kind == StrictOnA;
#endif
	
		if (	strict_context && (DoListAllTypes || DoListStrictTypes) &&
#ifdef STATES_GENERATED
# if 1
			arg -> type_arg_node -> type_node_annotation==StrictAnnot)
# else
			!IsLazyState (arg -> type_arg_node -> type_node_state))
# endif
#else
			arg -> type_arg_node -> type_node_state.state_kind == StrictOnA)
#endif
			FPutC ('!', StdListTypes);

		if (print_attribute && arg -> type_arg_node -> type_node_attribute > NoAttr)
			PrintAttribute (arg -> type_arg_node -> type_node_attribute, arg -> type_arg_node -> type_node_tv != NULL);

		if (arg -> type_arg_node -> type_node_tv)
		{	if (arg -> type_arg_node -> type_node_tv -> tv_ident)
				FPutS (arg -> type_arg_node -> type_node_tv -> tv_ident -> ident_name, StdListTypes);
			else
				FPrintF (StdListTypes, "i%ld", arg -> type_arg_node -> type_node_tv);
		}
	}
	else
		PrintNode (arg -> type_arg_node, brackets, strict_context, cDoPrintAnnot);

} /* PrintArgument */

static void PrintArguments (TypeArgs args, char separator, Bool brackets, Bool strict_context, FlatType form_type)
{
	if (args)
	{	int arg_nr, nr_of_exi_vars;
		TypeVarList form_type_vars;
		
		if (form_type != NULL)
		{	nr_of_exi_vars = form_type -> ft_exist_arity;
			form_type_vars = form_type -> ft_arguments;

			if (nr_of_exi_vars > 0)
			{	FPutC (':', StdListTypes);
				PrintArgument (args, cPrintBrackets, strict_context, cDoPrintAttribute);
			}
			else
			{	PrintArgument (args, brackets, strict_context, ! TestMark (form_type_vars -> tvl_elem, tv_mark, TV_EXISTENTIAL_ATTRIBUTE_MASK));
				form_type_vars = form_type_vars -> tvl_next;
			}
		}
		else
		{	nr_of_exi_vars = 0;
			form_type_vars = NULL;
			PrintArgument (args, brackets, strict_context, cDoPrintAttribute);
		}

		for (arg_nr = 1, args = args -> type_arg_next; args; args = args -> type_arg_next, arg_nr++)
		{	if (arg_nr == nr_of_exi_vars)
				FPutS (": ", StdListTypes);
			else if (arg_nr < nr_of_exi_vars)
			{	FPutC (',', StdListTypes);
				PrintArgument (args, brackets, strict_context, cDoPrintAttribute);
				continue;
			}
			else
				FPutC (separator, StdListTypes);
				
			if (form_type_vars != NULL)
			{	PrintArgument (args, brackets, strict_context, ! TestMark (form_type_vars -> tvl_elem, tv_mark, TV_EXISTENTIAL_ATTRIBUTE_MASK));
				form_type_vars = form_type_vars -> tvl_next;
			}
			else
				PrintArgument (args, brackets, strict_context, cDoPrintAttribute);
		}
		if (arg_nr == nr_of_exi_vars)
			FPutC (':', StdListTypes);
	}
	
} /* PrintArguments */

static void PrintNode (TypeNode node, Bool brackets, Bool strict_context, Bool print_annot)
{

	if (print_annot && strict_context && (DoListAllTypes || DoListStrictTypes) &&
#ifdef STATES_GENERATED
# if 1
		node -> type_node_annotation==StrictAnnot)
# else
		!IsLazyState (node -> type_node_state))
# endif
#else
		node -> type_node_state.state_kind == StrictOnA)
#endif
		FPutC ('!', StdListTypes);

	if (node -> type_node_attribute > NoAttr)
	{	if (PrintAttribute (node -> type_node_attribute, cDoPrintColon) &&
			(node -> type_node_symbol -> symb_kind == fun_type || node -> type_node_symbol -> symb_kind == apply_symb))
			brackets = True;
	}
	switch (node -> type_node_symbol -> symb_kind)
	{
	case tuple_type:
	{	int form_arity = node -> type_node_symbol -> symb_arity;
	
		if (node -> type_node_arity == form_arity)
		{	FPutC ('(', StdListTypes);
			PrintArguments (node -> type_node_arguments, ',', cDontPrintBrackets, strict_context, NULL);
			FPutC (')', StdListTypes);
		}
		else
		{	int i;
			if (brackets && node -> type_node_arguments)
				FPutC ('(', StdListTypes);
			FPutC ('(', StdListTypes);
			for (i=1; i<form_arity; i++)
				FPutC (',', StdListTypes);
			FPutC (')', StdListTypes);
			if (node -> type_node_arguments)
			{	PrintArguments (node -> type_node_arguments, ' ', cPrintBrackets, strict_context, NULL);
				if (brackets)
					FPutC (')', StdListTypes);
			}
		}
		break;
	}
	case list_type:
		FPutC ('[', StdListTypes);
#if STRICT_LISTS
		if (node->type_node_symbol->symb_head_strictness==1)
			FPutC ('!', StdListTypes);			
		else if (node->type_node_symbol->symb_head_strictness==2)
			FPutC ('#', StdListTypes);
#endif
		PrintArguments (node -> type_node_arguments, ',', cDontPrintBrackets, cNotInAStrictContext, NULL);
#if STRICT_LISTS
		if (node->type_node_symbol->symb_tail_strictness)
			FPutC ('!', StdListTypes);			
#endif
		FPutC (']', StdListTypes);
		break;
	case array_type:
		FPutS ("{", StdListTypes);
		PrintArguments (node -> type_node_arguments, ',', cDontPrintBrackets, cInAStrictContext, NULL);
		FPutS ("}", StdListTypes);
		break;
	case strict_array_type:
		FPutS ("{!", StdListTypes);
		PrintArguments (node -> type_node_arguments, ',', cDontPrintBrackets, cInAStrictContext, NULL);
		FPutS ("}", StdListTypes);
		break;
	case unboxed_array_type:
		FPutS ("{#", StdListTypes);
		PrintArguments (node -> type_node_arguments, ',', cDontPrintBrackets, cInAStrictContext, NULL);
		FPutS ("}", StdListTypes);
		break;
	case fun_type:
	{	TypeNode arg_type_node = node -> type_node_arguments -> type_arg_node;
		if (brackets)
			FPutC ('(', StdListTypes);
		if ((! arg_type_node -> type_node_is_var) && arg_type_node -> type_node_symbol -> symb_kind == fun_type)
			PrintArgument (node -> type_node_arguments, cPrintBrackets, cNotInAStrictContext, cDoPrintAttribute);
		else
			PrintArgument (node -> type_node_arguments, cDontPrintBrackets, cNotInAStrictContext, cDoPrintAttribute);
		FPutS (" -> ", StdListTypes);
		PrintArgument (node -> type_node_arguments -> type_arg_next, cDontPrintBrackets, cNotInAStrictContext, cDoPrintAttribute);
		if (brackets)
			FPutC (')', StdListTypes);
		break;
	}
	case apply_symb:
		if (brackets)
			FPutC ('(', StdListTypes);
		PrintArguments (node -> type_node_arguments, ' ', cPrintBrackets, strict_context, NULL);
		if (brackets)
			FPutC (')', StdListTypes);
		break;
	default:
		if (brackets && node -> type_node_arguments)
			FPutC ('(', StdListTypes);
		PrintSymbol (node -> type_node_symbol, StdListTypes);
		if (node -> type_node_arguments)
		{	FlatType lhs_type;
		
			if (node -> type_node_symbol -> symb_kind == definition)
				lhs_type =  RetrieveLhsOfTypeDefinition (node -> type_node_symbol -> symb_def);
			else
				lhs_type = NULL;

			FPutC (' ', StdListTypes);
			PrintArguments (node -> type_node_arguments,' ', cPrintBrackets, strict_context, lhs_type);
			if (brackets)
				FPutC (')', StdListTypes);
		}
		break;
	}

} /* PrintNode */

static void PrintAttributeEquations (UniVarEquations attr_equas)
{
	FPutS (", [", StdListTypes);
	
	for ( ; ; )
	{	AttributeKindList next;
		Bool used_implicitly;
		unsigned dem_attr_nr = RetrieveRefCountInfo (attr_equas -> uve_demanded - FirstUniVarNumber, & used_implicitly);

		for (next = attr_equas -> uve_offered ; ; )
		{	unsigned	off_attr_nr = RetrieveRefCountInfo (next -> akl_elem - FirstUniVarNumber, & used_implicitly);

			PrintAttributeVariable (off_attr_nr);
			if ((next = next -> akl_next))
				FPutC (' ', StdListTypes);
			else
				break;
		}


		FPutS (" <= ", StdListTypes);
		PrintAttributeVariable (dem_attr_nr);

		if ((attr_equas = attr_equas -> uve_next))
			FPutS (", ", StdListTypes);
		else
			break;
	}
	FPutC (']', StdListTypes);

} /* PrintAttributeEquations */

#include <ctype.h>

void PrintTypeClass (SymbDef class_def, File file)
{
	char * class_name = class_def -> sdef_ident -> ident_name;
	
	if (*class_name == '.')
		class_name++;

	FPutS (class_name, file);

} /* PrintTypeClass */

static void PrintTypeContext (TypeContext context)
{
	SymbolList class_symbs = context -> tyco_symbols;
	TypeVar context_var = context -> tyco_variable;
	
	PrintTypeClass (class_symbs -> sl_symbol, StdListTypes);
	
	for (class_symbs = class_symbs -> sl_next; class_symbs; class_symbs = class_symbs -> sl_next)
	{	FPutS (" , ", StdListTypes);
		PrintTypeClass (class_symbs -> sl_symbol, StdListTypes);
	}

	FPutC (' ', StdListTypes);
	if (TestMark (context_var, tv_mark, TV_WITH_INST_RESTR))
		FPutC ('.', StdListTypes);
	FPutS (context_var -> tv_ident -> ident_name, StdListTypes);
	
} /* PrintTypeContext */

void PrintType (SymbDef tdef, TypeAlts type)
{
	TypeNode lhs_root = type -> type_alt_lhs;
	TypeArgs lhsargs = lhs_root -> type_node_arguments;
	int i;
	
	if (tdef -> sdef_unq_attributed && DoShowAttributes)
		DetermineRefCountOfAttributeVars (type);
	
	for (i=0; i<tdef -> sdef_nr_of_lifted_nodeids; i++)
		lhsargs = lhsargs -> type_arg_next; 
	
	PrintSymbolOfIdent (tdef -> sdef_ident, tdef -> sdef_line, StdListTypes);
	FPutS (" :: ", StdListTypes);
	
	if (lhsargs)
	{	PrintArguments (lhsargs,' ', cPrintBrackets, cInAStrictContext, NULL);
		FPutS (" -> ", StdListTypes);
	}
	if (type -> type_alt_rhs -> type_node_is_var)
	{	if (type -> type_alt_rhs -> type_node_attribute > NoAttr)
			PrintAttribute (type -> type_alt_rhs -> type_node_attribute, cDoPrintColon);
		FPutS (type -> type_alt_rhs -> type_node_tv -> tv_ident -> ident_name, StdListTypes);
	}
	else
	{	Bool rhs_brackets = (lhsargs == NULL) && (type -> type_alt_rhs -> type_node_symbol -> symb_kind == fun_type);
		PrintNode (type -> type_alt_rhs, rhs_brackets, cInAStrictContext, cDontPrintAnnot);
	}
	if (type -> type_alt_type_context)
	{	TypeContext next_context;
		FPutS (" | ", StdListTypes);
		PrintTypeContext (type -> type_alt_type_context);
		for (next_context = type -> type_alt_type_context -> tyco_next; next_context; next_context = next_context -> tyco_next)
		{	FPutS (" & ", StdListTypes);
			PrintTypeContext (next_context);
		}
	}
	
	if (DoShowAttributes && type -> type_alt_attr_equations)
		PrintAttributeEquations (type -> type_alt_attr_equations);

	FPutS (";\n", StdListTypes);
	
	if (tdef -> sdef_nr_of_lifted_nodeids > 0)
	{	FPutS ("// internal argument types:", StdListTypes);
		for (i=0, lhsargs = lhs_root -> type_node_arguments;
			i<tdef -> sdef_nr_of_lifted_nodeids; i++, lhsargs = lhsargs -> type_arg_next)
		{	FPutC (' ', StdListTypes);
			PrintArgument (lhsargs, cPrintBrackets, cInAStrictContext, cDoPrintAttribute);
		}
		FPutC ('\n', StdListTypes);
	}
	

} /* PrintType */

/******

	Routines for printing types
	
******/


void InitARC_Info (void)
{
	CurrentARC_Info = CompAllocType (struct attr_ref_count_info);
	CurrentARC_Info -> arci_next = NULL;

} /* InitARC_Info */

