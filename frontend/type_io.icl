implementation module type_io

// WARNING: It is essential to report changes in this module to martijnv@cs.kun.nl
//			because the binary format for type-files is used by the dynamic run-time
//			system.

import StdEnv, compare_constructor
import scanner, general, Heap, typeproperties, utilities, checksupport

import type_io_common
// normal form:
// -	type variables in type definitions are normalized by checkTypeDef in the
//		module checktypes.icl. The position of a type variable in the left-hand
//		side of a type constructor is used.
// -	algebraic datatypes; constructors are alphabetically ordered in this 
//		module
//
// unsupported:
// - 	type synonyms
// - 	ADTs

//import DebugUtilities;
F a b :== b;

class NormaliseTypeDef a 
where
	normalise_type_def :: a -> a
	
import RWSDebug

instance NormaliseTypeDef TypeRhs
where
	normalise_type_def (AlgType defined_symbols)
		// algebraic data types are further normalized by an alphabetical sort on the
		// constructor names.
		= AlgType (sortBy (\{ds_ident={id_name=id_name1}} {ds_ident={id_name=id_name2}} -> id_name1 < id_name2) defined_symbols)
	normalise_type_def i
		= i

//1.3		
instance NormaliseTypeDef TypeDef rhs | NormaliseTypeDef rhs
//3.1
/*2.0
instance NormaliseTypeDef (TypeDef rhs) | NormaliseTypeDef rhs
0.2*/
where
	normalise_type_def type_def=:{td_args,td_arity}
		= type_def
				
	
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
	write_type_info {cons_symb,cons_type,cons_arg_vars,cons_priority,cons_index,cons_type_index,cons_exi_vars} tcl_file
		# tcl_file
			= write_type_info cons_symb tcl_file
		# tcl_file
			= write_type_info cons_type tcl_file
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
		
//1.3
instance WriteTypeInfo TypeDef TypeRhs
//3.1
/*2.0
instance WriteTypeInfo (TypeDef TypeRhs)
0.2*/
where 
	write_type_info /*{td_name,td_arity,td_args,td_rhs}*/ type_def tcl_file
		# {td_name,td_arity,td_args,td_rhs}
			= normalise_type_def type_def
	
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
		// writing tv_name as number suffices
		= write_type_info tv_name tcl_file
		
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
		
// NEW ->
instance WriteTypeInfo SymbolType
where
	write_type_info {st_vars,st_args,st_arity,st_result} tcl_file
		# tcl_file
			= write_type_info st_vars tcl_file
		# tcl_file
			= write_type_info st_args tcl_file
		# tcl_file
			= write_type_info st_arity tcl_file
		# tcl_file
			= write_type_info st_result tcl_file
		= tcl_file
		
instance WriteTypeInfo AType
where
	write_type_info {at_annotation,at_type} tcl_file
		# tcl_file
			= write_type_info at_annotation tcl_file
		# tcl_file
			= write_type_info at_type tcl_file
		= tcl_file
		
instance WriteTypeInfo Type
where
	write_type_info (TA type_symb_ident atypes) tcl_file
		# tcl_file
			= fwritec TypeTACode tcl_file
		# tcl_file
			= write_type_info type_symb_ident tcl_file
		# tcl_file
			= write_type_info atypes tcl_file
		= tcl_file

	write_type_info (atype1 --> atype2) tcl_file
		# tcl_file
			= fwritec TypeArrowCode tcl_file
		# tcl_file
			= write_type_info atype1 tcl_file
		# tcl_file
			= write_type_info atype2 tcl_file
		= tcl_file
		
	write_type_info (cons_variable :@: atypes) tcl_file
		# tcl_file
			= fwritec TypeConsApplyCode tcl_file
		# tcl_file
			= write_type_info cons_variable tcl_file
		# tcl_file
			= write_type_info atypes tcl_file
		= tcl_file
		
	write_type_info tb=:(TB basic_type) tcl_file
		# tcl_file
			= case basic_type of
				BT_Int		-> fwritec BT_IntCode tcl_file
				BT_Char		-> fwritec BT_CharCode tcl_file
				BT_Real		-> fwritec BT_RealCode tcl_file
				BT_Bool		-> fwritec BT_BoolCode tcl_file
				BT_Dynamic	-> fwritec BT_DynamicCode tcl_file
				BT_File		-> fwritec BT_FileCode tcl_file
				BT_World	-> fwritec BT_WorldCode tcl_file
				BT_String type
					# tcl_file
						= fwritec BT_StringCode tcl_file
					# tcl_file
						= write_type_info type tcl_file
					-> tcl_file
		= tcl_file
	
	write_type_info (GTV type_var) tcl_file
		# tcl_file
			= fwritec TypeGTVCode tcl_file
		# tcl_file
			= write_type_info type_var tcl_file
		= tcl_file

	write_type_info (TV type_var) tcl_file
		# tcl_file
			= fwritec TypeTVCode tcl_file
		# tcl_file
			= write_type_info type_var tcl_file
		= tcl_file
		
	write_type_info (TQV type_var) tcl_file
		# tcl_file
			= fwritec TypeTQVCode tcl_file
		# tcl_file
			= write_type_info type_var tcl_file
		= tcl_file	

	write_type_info TE tcl_file
		# tcl_file
			= fwritec TypeTECode tcl_file
		= tcl_file	

instance WriteTypeInfo ConsVariable
where
	write_type_info (CV type_var) tcl_file
		# tcl_file
			= fwritec ConsVariableCVCode tcl_file
		# tcl_file
			= write_type_info type_var tcl_file
		= tcl_file	

	write_type_info (TempCV temp_var_id) tcl_file
		# tcl_file
			= fwritec ConsVariableTempCVCode tcl_file
		# tcl_file
			= write_type_info temp_var_id tcl_file
		= tcl_file	
		
	write_type_info (TempQCV temp_var_id) tcl_file
		# tcl_file
			= fwritec ConsVariableTempQCVCode tcl_file
		# tcl_file
			= write_type_info temp_var_id tcl_file
		= tcl_file	

instance WriteTypeInfo TypeSymbIdent
where
	write_type_info {type_name,type_arity} tcl_file
		# tcl_file
			= write_type_info type_name tcl_file
		# tcl_file
			= write_type_info type_arity tcl_file
		= tcl_file
		
/*2.0
instance WriteTypeInfo String
where
	write_type_info s tcl_file
		# tcl_file
			= fwritei (size s) tcl_file
		= fwrites s tcl_file
	// warning:
	// Should be identical to the code in Ident

0.2*/

// basic and structural write_type_info's
instance WriteTypeInfo Int 
where
	write_type_info i tcl_file
		= fwritei i tcl_file

//1.3
instance WriteTypeInfo {#b} | select_u, size_u, WriteTypeInfo b
//3.1
/*2.0
instance WriteTypeInfo {#b} | WriteTypeInfo b & Array {#} b
0.2*/
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
