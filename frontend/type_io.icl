implementation module type_io

import StdEnv, compare_constructor

import scanner, general, Heap, typeproperties, utilities, checksupport

//import DebugUtilities;
F a b :== b;

// Unsupported:
// - type synonyms, expanded version must be stored. Which function in the compiler
//   expands synonyms correctly.
// - abstract data type, what should be written?
//

class WriteTypeInfo a 
where
	write_type_info :: a !*File -> !*File
	
instance WriteTypeInfo CommonDefs
where 
	write_type_info {com_type_defs,com_cons_defs} tcl_file
		# tcl_file
			= write_type_info com_type_defs tcl_file
		# tcl_file
 			= write_type_info com_cons_defs tcl_file
		= tcl_file
	
instance WriteTypeInfo ConsDef
where 
	write_type_info {cons_symb,cons_arg_vars,cons_priority,cons_index,cons_type_index,cons_exi_vars} tcl_file
		# tcl_file
			= write_type_info cons_symb tcl_file
		# tcl_file
			= write_type_info cons_arg_vars tcl_file
		# tcl_file
			= write_type_info cons_priority tcl_file

		# tcl_file
			= write_type_info cons_index tcl_file
		# tcl_file
			= write_type_info cons_type_index tcl_file
		# tcl_file
			= write_type_info cons_exi_vars tcl_file
	
		= tcl_file
		
PrioCode	=: toChar 0
NoPrioCode	=: toChar 1

instance WriteTypeInfo Priority
where 
	write_type_info (Prio assoc i) tcl_file
		# tcl_file
			= fwritec PrioCode tcl_file
		# tcl_file
			= write_type_info assoc tcl_file
		# tcl_file
			= write_type_info i tcl_file
		= tcl_file
	write_type_info NoPrio tcl_file
		# tcl_file
			= fwritec NoPrioCode tcl_file
		= tcl_file
		
LeftAssocCode	=: toChar 2
RightAssocCode	=: toChar 3
NoAssocCode		=: toChar 4
		
instance WriteTypeInfo Assoc
where 
	write_type_info LeftAssoc tcl_file
		# tcl_file
			= fwritec LeftAssocCode tcl_file
		= tcl_file

	write_type_info RightAssoc tcl_file
		# tcl_file
			= fwritec RightAssocCode tcl_file
		= tcl_file	

	write_type_info NoAssoc tcl_file
		# tcl_file
			= fwritec NoAssocCode tcl_file
		= tcl_file	
		
instance WriteTypeInfo TypeDef TypeRhs
where 
	write_type_info {td_name,td_arity,td_args,td_rhs} tcl_file
		|  F ("TypeDef '" +++ td_name.id_name +++ "'") True
 		#! tcl_file
 			= write_type_info td_name tcl_file
		#! tcl_file
 			= write_type_info td_arity tcl_file
 		#! tcl_file
 			= write_type_info td_args tcl_file
		#! tcl_file
 			= write_type_info td_rhs tcl_file
 		= tcl_file
 		
instance WriteTypeInfo ATypeVar
where 
	write_type_info {atv_annotation,atv_variable} tcl_file
 		#! tcl_file
 			= write_type_info atv_annotation tcl_file
 		#! tcl_file
 			= write_type_info atv_variable tcl_file
 		= tcl_file
 		
instance WriteTypeInfo Annotation
where 
	write_type_info AN_Strict tcl_file	
		= fwritec '!' tcl_file
	write_type_info AN_None tcl_file
		= fwritec ' ' tcl_file
		
instance WriteTypeInfo TypeVar
where
	write_type_info {tv_name} tcl_file
		= write_type_info tv_name tcl_file
		
AlgTypeCode			=: (toChar 5)
SynTypeCode 		=: (toChar 6)
RecordTypeCode		=: (toChar 7)
AbstractTypeCode	=: (toChar 8)

instance WriteTypeInfo TypeRhs
where 
	write_type_info (AlgType defined_symbols) tcl_file
 		#! tcl_file
 			= fwritec AlgTypeCode tcl_file;
		
		# tcl_file
			= write_type_info defined_symbols tcl_file

		= tcl_file
		
	write_type_info (SynType _) tcl_file
		#! tcl_file
 			= fwritec SynTypeCode tcl_file;
 			
 		// unimplemented
 		= tcl_file 
		
	write_type_info (RecordType {rt_fields}) tcl_file
 		#! tcl_file
 			= fwritec RecordTypeCode tcl_file;
		= write_type_info rt_fields tcl_file

	write_type_info (AbstractType _) tcl_file
 		#! tcl_file
 			= fwritec AbstractTypeCode tcl_file;
 			
 		// unimplemented
		= tcl_file
		
instance WriteTypeInfo DefinedSymbol 
where
	write_type_info {ds_ident,ds_arity,ds_index} tcl_file
		# tcl_file
			= write_type_info ds_ident tcl_file
		# tcl_file
			= write_type_info ds_arity tcl_file
		# tcl_file
			= write_type_info ds_index tcl_file
		= tcl_file

instance WriteTypeInfo Ident 
where
	write_type_info {id_name} tcl_file
		# tcl_file
			= fwritei (size id_name) tcl_file
		= fwrites id_name tcl_file
//		= write_type_info id_name tcl_file;
		
instance WriteTypeInfo FieldSymbol
where
	write_type_info {fs_name,fs_var,fs_index} tcl_file
		# tcl_file
			= write_type_info fs_name tcl_file
		# tcl_file
			= write_type_info fs_var tcl_file
		# tcl_file
			= write_type_info fs_index tcl_file
		= tcl_file
			
// basic and structural write_type_info's
instance WriteTypeInfo Int 
where
	write_type_info i tcl_file
		= fwritei i tcl_file

instance WriteTypeInfo {#b} | select_u, size_u, WriteTypeInfo b 
where
	write_type_info unboxed_array tcl_file
		# s_unboxed_array
			= size unboxed_array
		# tcl_file
			= fwritei s_unboxed_array tcl_file
			
		= write_type_info_loop 0 s_unboxed_array tcl_file
	where 
		write_type_info_loop i limit tcl_file
			| i == limit
				= tcl_file
			# tcl_file
				= write_type_info unboxed_array.[i] tcl_file
			= write_type_info_loop (inc i) limit tcl_file
			
instance WriteTypeInfo [a] | WriteTypeInfo a
where
	write_type_info l tcl_file
		# tcl_file
			= fwritei (length l) tcl_file
		= write_type_info_loop l tcl_file
	where
		write_type_info_loop []	tcl_file
			= tcl_file
		write_type_info_loop [x:xs] tcl_file
			# tcl_file
				= write_type_info x tcl_file
			= write_type_info_loop xs tcl_file
			
instance WriteTypeInfo Char
where
	write_type_info c tcl_file
		# tcl_file
			= fwritec c tcl_file;
		= tcl_file;

// read
class ReadTypeInfo a
where
	read_type_info :: !*File -> (!Bool,a,!*File)
	
instance ReadTypeInfo CommonDefs
where
	read_type_info tcl_file
		# (ok1,com_type_defs,tcl_file)
			= read_type_info tcl_file
		# (ok2,com_cons_defs,tcl_file)
			= read_type_info tcl_file
			
		# common_defs
			= { CommonDefs |
				com_type_defs		= com_type_defs
			,	com_cons_defs		= com_cons_defs
			,	com_selector_defs	= {}
			,	com_class_defs		= {}
			,	com_member_defs		= {}
			,	com_instance_defs	= {}
			}
		= (ok1&&ok2,common_defs,tcl_file)

instance ReadTypeInfo TypeDef TypeRhs
where
	read_type_info tcl_file
		
		// td_name
		#! (ok1,td_name,tcl_file)
			= read_type_info tcl_file
		| F ("TypeDef '" +++ td_name.id_name +++ "'") not ok1
			= (False,default_elem,tcl_file)
			
		// td_arity
		#! (ok2,td_arity,tcl_file)
			= read_type_info tcl_file
		| not ok2
			= (False,default_elem,tcl_file)

		// td_args
		#! (ok2,td_args,tcl_file)
			= read_type_info tcl_file
		| not ok2
			= (False,default_elem,tcl_file)

		// td_rhs
		#! (ok2,td_rhs,tcl_file)
			= read_type_info tcl_file
		| not ok2
			= (False,default_elem,tcl_file)
	
		# type_def
			= { default_elem &
				td_name 	= td_name
			,	td_arity	= td_arity
			,	td_args		= td_args
			,	td_rhs		= td_rhs
			}
		
		= (ok1,type_def,tcl_file)

instance ReadTypeInfo TypeRhs
where
	read_type_info tcl_file
		# (ok1,c,tcl_file)
			= freadc tcl_file
		| not ok1
			= (False,default_elem,tcl_file)
			
		| c == AlgTypeCode
			# (ok,defined_symbols,tcl_file)
				= read_type_info tcl_file
			= (ok,AlgType defined_symbols,tcl_file)
			
		| c == SynTypeCode
			= (True,UnknownType,tcl_file)
		| c == RecordTypeCode
			# (ok,rt_fields,tcl_file)
				= read_type_info tcl_file
				
			# record_type
				= { default_elem &
					rt_fields	= rt_fields
				};
			= (True,RecordType record_type,tcl_file)
			
		| c == AbstractTypeCode
			= (True,UnknownType,tcl_file)
			
instance ReadTypeInfo Priority
where
	read_type_info tcl_file
		# (ok1,p,tcl_file)
			= freadc tcl_file
		| not ok1
			= (False,default_elem,tcl_file)
			
		| p == PrioCode
			# (ok1,assoc,tcl_file)
				= read_type_info tcl_file
			# (ok2,i,tcl_file)
				= read_type_info tcl_file
			
			# prio
				= Prio assoc i
			= (ok1&&ok2,prio,tcl_file)	
			
		| p == NoPrioCode
			= (ok1,NoPrio,tcl_file)
			
instance ReadTypeInfo Assoc
where
	read_type_info tcl_file
		# (ok1,a,tcl_file)
			= freadc tcl_file
		| not ok1
			= (False,default_elem,tcl_file)	
			
		| a == LeftAssocCode
			= (ok1,LeftAssoc,tcl_file)
		| a == RightAssocCode
			= (ok1,RightAssoc,tcl_file)
		| a == NoAssocCode
			= (ok1,NoAssoc,tcl_file)
						
instance ReadTypeInfo DefinedSymbol
where
	read_type_info tcl_file
		// ds_ident
		# (ok1,ds_ident,tcl_file)
			= read_type_info tcl_file
		| not ok1
			= (False,default_elem,tcl_file)
			
		// ds_arity
		# (ok2,ds_arity,tcl_file)
			= read_type_info tcl_file
		| not ok2
			= (False,default_elem,tcl_file)
		
		// ds_index
		# (ok3,ds_index,tcl_file)
			= read_type_info tcl_file
		
		# defined_symbol
			= { default_elem &
				ds_ident	= ds_ident
			,	ds_arity	= ds_arity
			,	ds_index	= ds_index
			}
		= (ok3,defined_symbol,tcl_file)
		

instance ReadTypeInfo ConsDef 
where
	read_type_info tcl_file
		# (ok1,cons_symb,tcl_file)
			= read_type_info tcl_file
		# (ok2,cons_arg_vars,tcl_file)
			= read_type_info tcl_file
		# (ok3,cons_priority,tcl_file)
			= read_type_info tcl_file

		# (ok4,cons_index,tcl_file)
			= read_type_info tcl_file
		# (ok5,cons_type_index,tcl_file)
			= read_type_info tcl_file
		# (ok6,cons_exi_vars,tcl_file)
			= read_type_info tcl_file
			
		# consdef
			= { default_elem &
				cons_symb			= cons_symb
			,	cons_arg_vars		= cons_arg_vars
			,	cons_priority		= cons_priority
			
			,	cons_index			= cons_index
			,	cons_type_index		= cons_type_index
			,	cons_exi_vars		= cons_exi_vars
			}
		= (ok1&&ok2&&ok3&&ok4&&ok5&&ok6,consdef,tcl_file)
		
instance ReadTypeInfo Char
where
	read_type_info :: !*File -> (!Bool,Char,!*File)
	read_type_info tcl_file
		= freadc tcl_file

instance ReadTypeInfo Ident
where 
	read_type_info :: !*File -> (!Bool,Ident,!*File)
	read_type_info tcl_file
		# (ok1,i,tcl_file)
			= freadi tcl_file
		# (id_name,tcl_file)
			= freads tcl_file i;
		| F ("Ident " +++ toString i +++ " - " +++ id_name) True
				
		# ident
			= { default_elem &
				id_name		= id_name
			,	id_info		= nilPtr
			}
		= (ok1,ident,tcl_file)

instance ReadTypeInfo ATypeVar
where
	read_type_info tcl_file
		// atv_annotation
		# (ok1,atv_annotation,tcl_file)
			= read_type_info tcl_file
		| not ok1
			= (False,default_elem,tcl_file)
			
		// atv_variable
		# (ok2,atv_variable,tcl_file)
			= read_type_info tcl_file
		| not ok2
			= (False,default_elem,tcl_file)
			
		# atypevar
			= { default_elem &
				atv_annotation	= atv_annotation
			,	atv_variable	= atv_variable
			}
		= (True,atypevar,tcl_file)
		
instance ReadTypeInfo TypeVar
where
	read_type_info tcl_file
		# (ok1,tv_name,tcl_file)
			= read_type_info tcl_file
		
		# typevar
			= { default_elem &
				tv_name		= tv_name
			}
		= (ok1,typevar,tcl_file)
			
instance ReadTypeInfo Annotation
where
	read_type_info tcl_file
		#! (ok1,c,tcl_file)
			= freadc tcl_file
		
		# annotation
			= if (c == '!') AN_Strict AN_None
		= (ok1,annotation,tcl_file)
		
instance ReadTypeInfo FieldSymbol
where
	read_type_info tcl_file
		# (ok1,fs_name,tcl_file)
			= read_type_info tcl_file
		# (ok2,fs_var,tcl_file)	
			= read_type_info tcl_file
		# (ok3,fs_index,tcl_file)
			= read_type_info tcl_file
		
		# field_symbol
			= { FieldSymbol | 
				fs_name			= fs_name
			,	fs_var			= fs_var
			,	fs_index		= fs_index
			}
		= (ok1&&ok2&&ok3,field_symbol,tcl_file)		
		
// basic and structural write_type_info's
instance ReadTypeInfo Int
where 
	read_type_info :: !*File -> (!Bool,Int,!*File)
	read_type_info tcl_file
		= freadi tcl_file			
	
instance ReadTypeInfo {#b} | ReadTypeInfo b & DefaultElem b & ArrayElem b
where 
	read_type_info tcl_file

		# (ok,s_unboxed_array,tcl_file)
			= freadi tcl_file
		| F ("s_unboxed_array: " +++ toString s_unboxed_array) not ok
			= (False,{default_elem},tcl_file)
			
		# unboxed_array
			= { default_elem \\ i <- [1..s_unboxed_array] }
		= read_type_info_loop 0 s_unboxed_array tcl_file unboxed_array

	where
		read_type_info_loop i limit tcl_file unboxed_array
			| F ("  " +++ toString i) i == limit
				= (True,unboxed_array,tcl_file)
				
			# (ok,elem,tcl_file)
				= read_type_info tcl_file
			| not ok
				= (False,unboxed_array,tcl_file)
				
				= read_type_info_loop (inc i) limit tcl_file {unboxed_array & [i] = elem}
	
		
instance ReadTypeInfo [a] | ReadTypeInfo a
where
	read_type_info tcl_file
		# (ok1,limit,tcl_file)
			= freadi tcl_file
		| not ok1
			= (False,[],tcl_file)
			
		= read_type_info_loop 0 limit tcl_file []
	where
		read_type_info_loop i limit tcl_file elems
			| i == limit
				= (True,reverse elems,tcl_file)
				
			# (ok,elem,tcl_file)
				= read_type_info tcl_file
			| not ok 
				= (False,[],tcl_file)
				= read_type_info_loop (inc i) limit tcl_file [elem:elems]
	
// defaults
class DefaultElem a
where
	default_elem :: a
	
instance DefaultElem (TypeDef TypeRhs)
where 	
	default_elem
	 	= { TypeDef |
	 		td_name			= default_elem
		,	td_index		= default_elem
		,	td_arity		= default_elem
		,	td_args			= default_elem
		,	td_attrs		= default_elem
		,	td_context		= default_elem
		,	td_rhs			= default_elem
		,	td_attribute	= default_elem
		,	td_pos			= default_elem
		}
		
instance DefaultElem Position
where
	default_elem
		= NoPos
		
instance DefaultElem TypeAttribute
where
	default_elem
		= TA_None
		
instance DefaultElem TypeRhs
where
	default_elem
		= UnknownType
		
instance DefaultElem ATypeVar
where
	default_elem
		= {	ATypeVar |
			atv_attribute		= TA_None
		,	atv_annotation		= AN_None
		,	atv_variable		= default_elem
		}	

instance DefaultElem TypeVar
where
	default_elem
		= { TypeVar |
			tv_name				= default_elem
		,	tv_info_ptr			= default_elem
		}
	
instance DefaultElem (Ptr a)
where
	default_elem
		= nilPtr
		
instance DefaultElem Ident
where 
	default_elem
		= { Ident |
		 	id_name		= {}
		,	id_info 	= default_elem
		}
		
		
instance DefaultElem TypeVarInfo
where
	default_elem
		= TVI_Empty
		
instance DefaultElem SymbolTableEntry
where
	default_elem
		= { SymbolTableEntry |
			ste_kind		= STE_Empty
		,	ste_index		= NoIndex
		,	ste_def_level	= NotALevel
		,	ste_previous	= abort "instance DefaultElem SymboltableEntry"
		}
		
instance DefaultElem [a]
where
	default_elem
		= []
		
instance DefaultElem Int
where
	default_elem
		= abort "instance DefaultElem Int"
		
instance DefaultElem DefinedSymbol
where
	default_elem
		= { DefinedSymbol |
			ds_ident		= default_elem
		,	ds_arity		= default_elem
		,	ds_index		= default_elem
		}
		
instance DefaultElem ConsDef
where
	default_elem
		= { ConsDef |
			cons_symb			= default_elem
		,	cons_type			= default_elem
		,	cons_arg_vars		= default_elem
		,	cons_priority		= default_elem
		,	cons_index			= default_elem
		,	cons_type_index		= default_elem
		,	cons_exi_vars		= default_elem
		,	cons_type_ptr		= default_elem
		,	cons_pos			= default_elem
		}

instance DefaultElem Priority
where
	default_elem
		= NoPrio
		
instance DefaultElem SymbolType
where
	default_elem
		= { SymbolType |
			st_vars			= [] //default_elem
		,	st_args			= [] //default_elem
		,	st_arity		= 0 //default_elem
		,	st_result		= default_elem
		,	st_context		= [] //default_elem
		,	st_attr_vars	= [] //default_elem
		,	st_attr_env		= [] //default_elem
		}		

instance DefaultElem VarInfo
where
	default_elem
		= VI_Empty
		
instance DefaultElem AType
where
	default_elem
		= { AType |
			at_attribute	= default_elem
		,	at_annotation	= default_elem
		,	at_type			= default_elem
		}

instance DefaultElem Type
where
	default_elem
		= TE
		
instance DefaultElem Annotation
where
	default_elem
		= AN_None
		
instance DefaultElem Assoc
where
	default_elem
		= NoAssoc
	
	
instance DefaultElem RecordType
where
	default_elem 
		= { RecordType |
			rt_constructor	= default_elem
		,	rt_fields		= {}
		}
		
instance DefaultElem FieldSymbol
where
	default_elem
		= { FieldSymbol |
			fs_name			= default_elem
		,	fs_var			= default_elem
		,	fs_index		= default_elem
		}						

instance DefaultElem {#a}	| ArrayElem, DefaultElem a
where
	default_elem
		= {default_elem}


