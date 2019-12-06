
#include "compiledefines.h"
#include "types.t"
#include "system.h"
#include "syntaxtr.t"
#include "comsupport.h"
#include "sizes.h"
#include "buildtree.h"
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
