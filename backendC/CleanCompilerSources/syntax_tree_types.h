/*
	Version 1.2 17 dec1996
*/

#define BASIC_TYPE_IDS_STRING "ibcrfswpvr" /* indexed by SymbKind */

#define Type_Variable_Mark	(1 << Nr_Of_Basic_Types)

typedef enum
{	NoUniAttr, NotUniqueAttr, UniqueAttr, ExistsAttr, UniqueVariable, FirstUniVarNumber
} UniquenessAttributeKind;
	
typedef unsigned AttributeKind;

typedef struct poly_list
{	void *				pl_elem;
	struct poly_list *	pl_next;
} * PolyList;

typedef struct type_arg * TypeArgs, TypeArg;
typedef struct type_node *	TypeNode;
typedef struct type_alt *	TypeAlts;

typedef struct
{	BITVECT	tac_uniprop;
	BITVECT	tac_possign;
	BITVECT	tac_negsign;		
} TypeArgClass;

#define type_uniprop  type_argclass.tac_uniprop
#define type_possign  type_argclass.tac_possign
#define type_negsign  type_argclass.tac_negsign

typedef struct type_var *TypeVar;

typedef struct type_var_list
{
	TypeVar					tvl_elem;
	struct type_var_list *	tvl_next;
	AttributeKind			tvl_attribute;
	Bool					tvl_exist_quant:1;
	Bool					tvl_cons_variable:1;

} * TypeVarList;

typedef struct flat_type 
{
	Symbol					ft_symbol;
	TypeVarList				ft_arguments;
	AttributeKind			ft_attribute;
} * FlatType;

typedef enum {	SLK_Symbol, SLK_TreeOfLists, SLK_ListNumber } SymbolListKind;

STRUCT (symbol_list, SymbolList)
{
	union
	{	struct symbol_def *		sl_u_symbol;
		IdentStringP			sl_u_ident_string;
		struct symbol_list *	sl_u_next_tree;
		int						sl_u_class_number;
	} sl_union;
	
	struct symbol_list *		sl_next;

	SymbolListKind				sl_kind;
	
};

#define sl_symbol		sl_union.sl_u_symbol
#define sl_ident_string sl_union.sl_u_ident_string
#define sl_next_tree	sl_union.sl_u_next_tree
#define sl_class_number	sl_union.sl_u_class_number

STRUCT (type_context, TypeContext)
{
	SymbolList				tyco_symbols;

#ifdef SHORT_CLASS_NAMES
	int						tyco_number;
#endif	
	TypeVar					tyco_variable;
	
/*	
	AttributeKind			tyco_attribute;
*/
	unsigned long			tyco_basic_instances;
	struct type_context	*	tyco_next;

};

typedef struct field_list
{
	Symbol				fl_symbol;
	TypeNode			fl_type;
	StateS				fl_state;
	struct field_list *	fl_next;
} * FieldList;

typedef struct constructor_list
{
	TypeNode					cl_constructor;
	FieldList					cl_fields;
	StateP						cl_state_p; /* for constructors, union met cl_fields ? */
	struct constructor_list *	cl_next;

} * ConstructorList;

typedef struct type
{
	FlatType			type_lhs;
	ConstructorList		type_constructors;
	struct type *		type_next;
	unsigned			type_line;
	int					type_nr_of_constructors;	/* 0 for records */
	TypeArgClass		type_argclass;

	BITVECT				type_exivars;
	BITVECT				type_univars;
	BITVECT				type_consvars;

} * Types;

#define type_fields 	type_constructors -> cl_fields
#define type_symbol		type_lhs -> ft_symbol

struct rule_type
{	TypeAlts			rule_type_rule;
	StateP              rule_type_state_p;
	TypeNode			rule_type_root;
	struct rule_type *	rule_type_next;
	unsigned			rule_type_line;
};

typedef struct syn_type SynType,*SynTypes;

struct syn_type
{	FlatType 			syn_lhs;
	TypeNode 			syn_rhs;
	TypeVarList			syn_exist_quant_typevars;
	struct syn_type *	syn_next;
	TypeArgClass 		syn_argclass;

	BITVECT				syn_univars;
	BITVECT				syn_consvars;

	unsigned			syn_line;
};

#define syntype_uniprop  syn_argclass.tac_uniprop
#define syntype_possign  syn_argclass.tac_possign
#define syntype_negsign  syn_argclass.tac_negsign

#define syntype_exivars  syn_exivars
#define syntype_univars  syn_univars

#define syntype_symbol	syn_lhs -> ft_symbol

typedef struct abs_type
{	FlatType			abs_graph;
	struct symbol_def *	abs_impl;
	struct abs_type *	abs_next;
	TypeArgClass		abs_argclass;
	BITVECT				abs_exivars;
	BITVECT				abs_univars;
	unsigned			abs_line;
	int					abs_number;
} *AbsTypes;

#define abstype_uniprop  abs_argclass.tac_uniprop
#define abstype_possign  abs_argclass.tac_possign
#define abstype_negsign  abs_argclass.tac_negsign

#define abstype_exivars  abs_exivars
#define abstype_univars  abs_univars

#define abstype_symbol	abs_graph -> ft_symbol

struct type_node
{
	union
	{	TypeVar				contents_tv;
		Symbol				contents_symbol;
	} type_node_contents;

	struct type_arg *		type_node_arguments;
	AttributeKind			type_node_attribute;
	short					type_node_arity;
	Annotation				type_node_annotation;
	unsigned char			type_node_is_var:1;
# ifdef CLEAN2
	TypeVarList				type_for_all_vars;
# endif
};

#define type_node_symbol type_node_contents.contents_symbol
#define type_node_tv type_node_contents.contents_tv

struct type_arg
{	TypeNode	type_arg_node;
	TypeArgs	type_arg_next;
};

typedef struct attr_kind_list
{	AttributeKind			akl_elem;
	struct uni_var *		akl_id;
	struct attr_kind_list *	akl_next;
} * AttributeKindList;
	
typedef struct uni_var_equats
{	AttributeKind			uve_demanded;
	struct uni_var *		uve_demanded_var;
	AttributeKindList		uve_offered;
	struct uni_var_equats *	uve_next;
} * UniVarEquations;

#if CLEAN2
STRUCT (strict_positions, StrictPositions)
{
	int sp_size;		/* size in bits */
	int sp_bits [1];	/* variable size */
};
#endif

typedef struct type_alt
{
	TypeNode				type_alt_lhs;
	TypeNode				type_alt_rhs;
	UniVarEquations			type_alt_attr_equations;
	TypeContext				type_alt_type_context;
	struct uni_var_admin *	type_alt_attr_vars;

	unsigned				type_alt_line;
#ifdef CLEAN2
	StrictPositionsP		type_alt_strict_positions;
#endif
} TypeAlt;

typedef struct cons_var_list
{
	TypeVar					cvl_nodeid;
	TypeArgClass *			cvl_argclass;
	struct cons_var_list *	cvl_next;
	int						cvl_number;
	int						cvl_arity;
	
} * ConsVarList;

struct type_var
{
	Ident			tv_ident;
	unsigned short	tv_mark;
	int				tv_refcount;
	int				tv_number;
	int 			tv_argument_nr;
	int				tv_overvar_arity;
	union
	{	TypeVar						u1_imp_tv;
		TypeNode					u1_subst_type;
		struct cons_var_list *		u1_cons_var_info;
	} tv_u1;
	union
	{	TypeVar						u2_forward_tv;
		struct type_cell *			u2_type;
		TypeNode					u2_type_node;
		struct type_context *		u2_context;
		PolyList					u2_formal_type_vars;
	} tv_u2;
};

#define tv_type					tv_u2.u2_type			/* comparser,typechecker */
#define tv_type_node			tv_u2.u2_type_node		/* typeconv */
#define tv_forward_tv			tv_u2.u2_forward_tv		/* checker,transform */
#define tv_type_context			tv_u2.u2_context		/* checktypedefs */
#define tv_formal_type_vars		tv_u2.u2_formal_type_vars/* checktypedefs */

#define tv_imp_tv				tv_u1.u1_imp_tv
#define tv_subst_type			tv_u1.u1_subst_type			/* checktypedefs */
#define tv_cons_var_info		tv_u1.u1_cons_var_info		/* checktypedefs */
#define tv_imp_tv				tv_u1.u1_imp_tv				/* checktypedefs */

#define TestMark(n,f,mask) 	(((n)->f & (mask)) != 0)
#define SetMark(n,f,mask) 	((n)->f |= (mask))
#define ClearMark(n,f,mask) ((n)->f &= ~(mask))

#define TV_INSTANTIATION_MASK 						(1 << 0)	/* checktypedefs */
#define TV_VERIFY_MASK								(1 << 1)	/* checktypedefs */
#define TV_CONVERSION_MASK							(1 << 2)	/* typeconv */
#define TV_EXISTENTIAL_ATTRIBUTE_MASK				(1 << 3)	/* checktypedefs, typeconv */
#define TV_RHS_EXISTENTIAL_MASK						(1 << 4)	/* checktypedefs */
#define TV_CONSTRUCTOR_VARIABLE_MASK				(1 << 5)	/* checktypedefs */
#define TV_OVERLOADED_VARIABLE_MASK					(1 << 6)	/* comparser */
#define TV_INIT_MASK								(1 << 7)	/* checktypedefs */
#define TV_DUPLICATED								(1 << 8)	/* checktypedefs */
#define TV_UNIQUE_MASK								(1 << 9)	/* checktypedefs */
#define TV_CLASS_VARIABLE_MASK						(1 << 10)	/* checktypedefs */
#define TV_CONS_VAR_WITH_ARGS						(1 << 11)	/* checktypedefs */
#define TV_UNIQUE_VARIABLE_PRINT_MASK				(1 << 12)	/* typeconv */
#define TV_NO_CONTEXT_VARIABLE_MASK					(1 << 13)	/* checktypedefs */
#define TV_WITH_INST_RESTR							(1 << 14)	/* checktypedefs */
#define TV_HAS_INST_MASK							(1 << 15)	/* checktypedefs */

typedef struct uni_var
{
	Ident				uv_ident;
	unsigned short		uv_mark;
	int					uv_number;
	struct uni_var *	uv_next_uni_var;
	UniVarEquations		uv_equations;

} * UniVar;

#define UV_INSTANTIATION_MASK 						(1 << 0)	/* checktypedefs */
#define UV_CYCLE_MASK 								(1 << 1)	/* checktypedefs */
#define UV_CHECKED_MASK 							(1 << 2)	/* checktypedefs */

typedef struct uni_var_admin
{	unsigned	uva_next_number;
	UniVar 		uva_list;

} * UniVarAdministration;


#ifdef SHORT_CLASS_NAMES
STRUCT (module_info, ModuleInfo)
{
	Symbol							mi_module_symbol;
	struct class_conversion_table *	mi_class_table;
	int								mi_next_class_number;
	struct type_conversion_table *	mi_type_table;
	int								mi_next_type_number;
};

STRUCT (class_conversion_table, ClassConversionTable) 
{	int								cct_number;
	SymbolList						cct_symbols;
	struct class_conversion_table *	cct_next;
};

STRUCT (type_conversion_table, TypeConversionTable) 
{	int								tct_number;
	struct symbol_def *				tct_type_symbol;
	struct type_conversion_table *	tct_next;
};
#endif
