
# undef H

# include	"compiledefines.h"
# include	"types.t"
# include	"syntaxtr.t"

# include	"comsupport.h"
# include	"sizes.h"
# include	"checker.h"
# include	"statesgen.h"
# include	"comparser.h"
# include	"buildtree.h"
# include	"settings.h"
# include	"checksupport.h"

void
InitParser (void)
{
	int		i;

	for (i = 0; i < MaxNodeArity; i++)
	{	SelectSymbols	 [i] = NULL;
		TupleTypeSymbols [i] = NULL;
	}

	IfSymbol		= NewSymbol (if_symb);

	TrueSymbol		= NewSymbol (bool_denot);
	TrueSymbol->symb_bool = True;
	FalseSymbol		= NewSymbol (bool_denot);
	FalseSymbol->symb_bool = False;

	TupleSymbol		= NewSymbol (tuple_symb);

	ApplySymbol		= NewSymbol (apply_symb);
	ApplySymbol->symb_instance_apply = 0;

	clear_p_at_node_tree();
} /* InitParser */
