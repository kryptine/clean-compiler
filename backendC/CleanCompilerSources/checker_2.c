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
