
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

typedef struct type_var *TypeVar;

typedef struct flat_type 
{
	Symbol					ft_symbol;
	AttributeKind			ft_attribute;
} * FlatType;

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
	int					type_nr_of_constructors;	/* 0 for records */
} * Types;

#define type_fields 	type_constructors -> cl_fields
#define type_symbol		type_lhs -> ft_symbol

struct rule_type
{	TypeAlts			rule_type_rule;
	StateP              rule_type_state_p;
};

struct type_node
{
	union {
		int					contents_tv_argument_n;
		Symbol				contents_symbol;
	} type_node_contents;

	struct type_arg *		type_node_arguments;
	AttributeKind			type_node_attribute;
	short					type_node_arity;
	Annotation				type_node_annotation;
	unsigned char			type_node_is_var:1;
};

#define type_node_symbol type_node_contents.contents_symbol
#define type_node_tv_argument_n type_node_contents.contents_tv_argument_n

struct type_arg
{	TypeNode	type_arg_node;
	TypeArgs	type_arg_next;
};

STRUCT (strict_positions, StrictPositions)
{
	int sp_size;		/* size in bits */
	int sp_bits [1];	/* variable size */
};

typedef struct type_alt
{
	TypeNode				type_alt_lhs;
	TypeNode				type_alt_rhs;
	StrictPositionsP		type_alt_strict_positions;
} TypeAlt;
