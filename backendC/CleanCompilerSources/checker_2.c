/*
	Authors:	Sjaak Smetsers & John van Groningen
	Version:	1.2
*/

#include "compiledefines.h"
#include "types.t"
#include "system.h"
#include "syntaxtr.t"
#include "comsupport.h"
#include "sizes.h"
#include "scanner.h"
#include "buildtree.h"
#include "comparser.h"
#include "statesgen.h"
#include "codegen_types.h"
#include "codegen1.h"
#include "codegen2.h"
#include "instructions.h"
#include "checksupport.h"
#include "settings.h"
#include "checker.h"
#ifdef applec
#	include <types.h>
#endif

#define for_l(v,l,n) for(v=(l);v!=NULL;v=v->n)

typedef struct def_list *DefModList,DefModElem;

struct def_list *OpenDefinitionModules;

void GenDependencyList (void)
{
	DefModList def_mod;

	for_l (def_mod,OpenDefinitionModules,mod_next)
		GenDepend (def_mod->mod_body->dm_name
#if WRITE_DCL_MODIFICATION_TIME
					,def_mod->mod_body->dm_modification_time
#endif
					);
}

void ReadInlineCode (void)
{
	DefModList d_mod;

	for_l (d_mod,OpenDefinitionModules,mod_next){
		DefMod def_mod;
		
		def_mod=d_mod->mod_body;
		if (def_mod->dm_system_module){
			int i,n_function_symbols;
			Symbol function_symbol_a;
			
			n_function_symbols=def_mod->dm_n_function_symbols;
			function_symbol_a=def_mod->dm_function_symbol_a;
			for (i=0; i<n_function_symbols; ++i)
				if (function_symbol_a[i].symb_kind==definition){
					SymbDef sdef;

					sdef=function_symbol_a[i].symb_def;
					if (sdef->sdef_kind==SYSRULE && sdef->sdef_mark & SDEF_USED_STRICTLY_MASK)
						break;
				}

			if (i<n_function_symbols && d_mod->mod_body->dm_name!=CurrentModule)
				/* Get the inline instructions of all the rules that are defined in this module */
				ScanInlineFile (d_mod->mod_body->dm_name,FirstSystemModuleTable+def_mod->dm_module_n);
		}
	}
}

Ident ApplyId, IfId, FailId;

char *StdBoolId;
SymbDef AndSymbDef,OrSymbDef;

#if SA_RECOGNIZES_ABORT_AND_UNDEF
char *StdMiscId;
SymbDef abort_symb_def,undef_symb_def;
#endif

char *PreludeId;
SymbDef seq_symb_def;

SymbDef scc_dependency_list;

SymbDef MakeNewSymbolDefinition (char *module, char *name, int arity, SDefKind kind)
{
	SymbDef def;
	int i,string_length;
	char *s,*new_string;
	
	string_length = strlen (name);
	new_string = CompAlloc (string_length+1);

	for (i=0; i<string_length; ++i)
		new_string[i] = name[i];
	new_string [string_length] = '\0';
	
	def = CompAllocType (SymbDefS);
	
	def->sdef_module = module;
	def->sdef_name = new_string;
	def->sdef_arity = arity;
	def->sdef_kind = kind;

	def->sdef_mark=0;

	def->sdef_exported=False;

	def->sdef_arfun = NoArrayFun;
	
	return def;
}

NodeDefs NewNodeDef (NodeId nid,Node node)
{
	NodeDefs new;

	new = CompAllocType (NodeDefS);

	new->def_id		= nid;
	new->def_node	= node;
	new->def_mark	= 0;

	return new;
}

void InitChecker (void)
{
	OpenDefinitionModules	= NIL;
}

void ClearOpenDefinitionModules (void)
{
	OpenDefinitionModules	= NULL;
}

void AddOpenDefinitionModule (DefMod definitionModule)
{
	DefModList	openModule;

	openModule = CompAllocType (DefModElem);
	openModule->mod_body	= definitionModule;
	openModule->mod_next	= OpenDefinitionModules;

	OpenDefinitionModules  = openModule;
}
