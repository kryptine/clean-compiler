
extern Node substitute_macro_in_rhs (Macro *macro_p,Node appl,int local_scope,NodeDefs **node_def_p,ImpRuleS ***imp_rule_p);
extern Node substitute_macro_in_lhs (RuleAltS *alt,Node appl,int local_scope,NodeDefs **node_def_p);
extern void CheckEqualMacros (RuleAltS *alt1,RuleAltS *alt2);

extern struct local_def *AllocateLocalDef (void);

extern struct local_def *free_ldefs;
