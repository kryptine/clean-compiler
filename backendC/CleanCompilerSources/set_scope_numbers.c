
#include "system.h"

#include "settings.h"
#include "syntaxtr.t"
#include "comsupport.h"
#include "buildtree.h"
#include "codegen_types.h"
#include "codegen1.h"
#include "codegen2.h"
#include "statesgen.h"
#include "checker.h"
#include "instructions.h"
#include "optimisations.h"
#include "sa.h"

#include "set_scope_numbers.h"

#define for_l(v,l,n) for(v=(l);v!=NULL;v=v->n)

static int scope;

static void set_node_id_scope_numbers (NodeDefP node_defs,int local_scope)
{
	NodeDefP node_def_p;
	
	for_l (node_def_p,node_defs,def_next)
		node_def_p->def_id->nid_scope=local_scope;
}

static void set_root_scope_numbers (NodeP node_p,int local_scope)
{
	if (node_p->node_kind==IfNode){
		int new_local_scope;
		ArgP arg_p;

		node_p->node_if_scope=local_scope;

		new_local_scope=scope+2;
		scope+=3;

		arg_p=node_p->node_arguments;
		set_root_scope_numbers (arg_p->arg_node,local_scope);
		
		++scope;
		arg_p=arg_p->arg_next;
		set_root_scope_numbers (arg_p->arg_node,new_local_scope);
		set_node_id_scope_numbers (node_p->node_then_node_defs,new_local_scope);	
		
		++scope;
		arg_p=arg_p->arg_next;
		set_root_scope_numbers (arg_p->arg_node,new_local_scope);
		set_node_id_scope_numbers (node_p->node_else_node_defs,new_local_scope);
	}
}

void set_scope_numbers (RuleAltS *rule_alt_p)
{
	scope=1;
	
	set_root_scope_numbers (rule_alt_p->alt_rhs_root,0);
	set_node_id_scope_numbers (rule_alt_p->alt_rhs_defs,0);
}

