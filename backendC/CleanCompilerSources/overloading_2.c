/*
	Version 1.0 - 24 okt 1994

	Author:  Sjaak Smetsers
*/

#include "compiledefines.h"
#include "types.t"
#include "system.h"
#include "settings.h"
#include "syntaxtr.t"
#include "comsupport.h"

#include "scanner.h"
#include "comparser.h"
#include "sizes.h"
#include "checker.h"
#include "checksupport.h"
#include "transform.h"
#include "sa.h"
#include "statesgen.h"
#include "tctypes.t"
#include "typechecker.h"
#include "typechecker2.h"
#include "typeconv.h"
#include "tcsupport.h"
#include "refcountanal.h"
#include "overloading.h"
#include "buildtree.h"

#ifdef _DEBUG_
	static char *OV = "overloading";
#endif

PolyList NewPolyListElem (void *elem, PolyList next, HeapDescr hd)
{
	PolyList new = TH_AllocType (hd, struct poly_list);
	new -> pl_elem = elem;
	new -> pl_next = next;
	return new;
	
} /* NewPolyListElem */

void InsertSymbolInSymbolList (SymbolList *symbols, SymbDef new_symbol, Bool take_icl_def, void *alloc (SizeT size))
{
	SymbolList new_elem;

	for (; *symbols; symbols = & (*symbols) -> sl_next)
	{	int cmp = strcmp ((*symbols) -> sl_symbol -> sdef_ident -> ident_name, new_symbol -> sdef_ident -> ident_name);
		if (cmp == 0)
			return;
		else if (cmp > 0)
			break;
	}

	new_elem 	= (SymbolListS *) alloc (SizeOf (SymbolListS));

	if (take_icl_def && new_symbol -> sdef_main_dcl)
		new_elem -> sl_symbol = new_symbol -> sdef_dcl_icl;
	else
		new_elem -> sl_symbol = new_symbol;

	new_elem -> sl_kind		= SLK_Symbol;
	new_elem -> sl_next		= *symbols;

	*symbols = new_elem;

} /* InsertSymbolInSymbolList */

void ConvertClassSymbolTreeToList (SymbolList symbols, SymbolList * result_list, void *alloc (SizeT size))
{
	SymbolList next_symbol;
	for (next_symbol = symbols; next_symbol -> sl_kind == SLK_TreeOfLists; next_symbol = next_symbol -> sl_next_tree)
		ConvertClassSymbolTreeToList (next_symbol -> sl_next, result_list, alloc);
	if (next_symbol -> sl_kind == SLK_ListNumber)
		next_symbol = next_symbol -> sl_next;
	for (; next_symbol; next_symbol = next_symbol -> sl_next)
		InsertSymbolInSymbolList (result_list, next_symbol -> sl_symbol, cTakeIclDef, alloc);		

} /* ConvertClassSymbolTreeToList */
