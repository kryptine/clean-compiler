
extern void InitGlobalSymbols (void);

extern Args NewArgument (NodeP pattern);
extern NodeP NewNode (SymbolP symb, Args args, int arity);
extern NodeP NewIfNode (void);
extern NodeP NewSelectorNode (SymbolP symb, Args args, int arity);
extern NodeP NewNodeIdNode (NodeIdP node_id);
extern NodeP NewUpdateNode (SymbolP symb,Args args,int arity);
extern NodeP NewNodeByKind (NodeKind nodeKind, SymbolP symb, Args args, int arity);
# define	NewNormalNode(symb, args, arity)	NewNodeByKind (NormalNode, (symb), (args), (arity))
# define	NewRecordNode(symb, args, arity)	NewNodeByKind (RecordNode, (symb), (args), (arity))
# define	NewMatchNode(symb, args, arity)		NewNodeByKind (MatchNode, (symb), (args), (arity))
# define	NewFalse()			NewNormalNode (FalseSymbol, NIL, 0)
# define	NewTrue()			NewNormalNode (TrueSymbol, NIL, 0)

extern NodeIdP NewNodeId (void);
extern StrictNodeIdP NewStrictNodeId (NodeIdP node_id, StrictNodeIdP next);
extern NodeDefs NewNodeDefinition (NodeIdP nid, NodeP node);
extern SymbolP NewSymbol (SymbKind symbolKind);
extern TypeArgs NewTypeArgument (TypeNode pattern);

extern NodeP NewSelectNode (SymbolP selectSymbol, NodeIdP selectId, int arity);
extern NodeIdP BuildSelect (NodeP node, NodeDefs **node_defs_p);
extern NodeIdP BuildSelectors (NodeP pattern, NodeP node, NodeDefs **node_defs_p);

extern SymbolP NewSelectSymbol (int arity);
extern SymbolP NewTupleTypeSymbol (int arity);
extern SymbolP NewListFunctionSymbol (void);

extern	ImpRules	NewImpRule (unsigned line_number,TypeAlts typeAlternative,NodeP rule_root);
extern RuleAltP	NewRuleAlt (void);

extern NodeIdP FreshNodeId (NodeP node, NodeDefs **node_defs_h);

extern char *CopyString (char *to, char *from, int *rest_size);

extern SymbolP	TrueSymbol, FalseSymbol, TupleSymbol,
				ApplySymbol, ApplyTypeSymbol, SelectSymbols[],
				FailSymbol, IfSymbol;

extern	SymbolP	TupleTypeSymbols [];

void clear_p_at_node_tree (void);
void store_p_at_node (NodeP annoted_node,NodeP at_node);
NodeP *get_p_at_node_p (NodeP annoted_node);
NodeP get_p_at_node (NodeP annoted_node);

