/*
	module owner: Martijn Vervoort
*/
implementation module type_io

// WARNING: It is essential to report changes in this module to martijnv@cs.kun.nl
//			because the binary format for type-files is used by the dynamic run-time
//			system.

import StdEnv, compare_constructor
import scanner, general, Heap, typeproperties, utilities, checksupport
import trans

import type_io_common
// normal form:
// -	type variables in type definitions are normalized by checkTypeDef in the
//		module checktypes.icl. The position of a type variable in the left-hand
//		side of a type constructor is used.
// -	algebraic datatypes; constructors are alphabetically ordered in this 
//		module
//
// unsupported:
// - 	ADTs

F a b :== b;

:: WriteTypeInfoState
	= { 
		wtis_n_type_vars						:: !Int
	,	wtis_predefined_module_def				:: !Index
	,	wtis_common_defs						:: !{#CommonDefs}	
	,	wtis_type_defs							:: !.{#{#CheckedTypeDef}}
	,	wtis_collected_conses					:: !ImportedConstructors
	,	wtis_type_heaps							:: !.TypeHeaps
	,	wtis_var_heap							:: !.VarHeap
	,	wtis_main_dcl_module_n 					:: !Int
	};
	
class WriteTypeInfo a 
where
	write_type_info :: a !*File !*WriteTypeInfoState -> (!*File,!*WriteTypeInfoState)
	
instance WriteTypeInfo CommonDefs
where 
	write_type_info {com_type_defs,com_cons_defs,com_selector_defs} tcl_file wtis
		# (tcl_file,wtis)
			= write_type_info com_type_defs tcl_file wtis
		# (tcl_file,wtis)
 			= write_type_info com_cons_defs tcl_file wtis
 		# (tcl_file,wtis)
 			= write_type_info com_selector_defs tcl_file wtis
		= (tcl_file,wtis)
		
instance WriteTypeInfo SelectorDef
where
	write_type_info {sd_type} tcl_file wtis
		# (tcl_file,wtis)
			= write_type_info sd_type tcl_file wtis
		= (tcl_file,wtis)
	
instance WriteTypeInfo ConsDef
where 
	write_type_info {cons_ident,cons_type,cons_arg_vars,cons_priority,cons_index,cons_type_index,cons_exi_vars} tcl_file wtis=:{wtis_n_type_vars}
 		// normalize ...
 		# (th_vars,wtis)
 			= sel_type_var_heap wtis
 		# (_,(_,th_vars))
 			= mapSt normalize_type_var cons_exi_vars (wtis_n_type_vars,th_vars)
  		# wtis
 			= { wtis & wtis_type_heaps.th_vars = th_vars }
 		// ... normalize

		# (tcl_file,wtis)
			= write_type_info cons_ident tcl_file wtis
		# (tcl_file,wtis)
			= write_type_info cons_type tcl_file wtis
		
		# (tcl_file,wtis)
			= write_type_info cons_arg_vars tcl_file wtis
		# (tcl_file,wtis)
			= write_type_info cons_index tcl_file wtis
						
		# (tcl_file,wtis)
			= write_type_info cons_type_index tcl_file wtis
		# (tcl_file,wtis)
			= write_type_info cons_exi_vars tcl_file wtis
		= (tcl_file,wtis)
			
//1.3
instance WriteTypeInfo TypeDef TypeRhs
//3.1
/*2.0
instance WriteTypeInfo (TypeDef TypeRhs)
0.2*/
where 
	write_type_info {td_ident,td_arity,td_args,td_rhs} tcl_file wtis
		// normalize ...
 		# (th_vars,wtis)
 			= sel_type_var_heap wtis
 		# (_,(n_type_vars,th_vars))
 			= mapSt normalize_type_var td_args (0,th_vars)
  		# wtis
 			= { wtis &
 				wtis_type_heaps.th_vars = th_vars
 			,	wtis_n_type_vars		= n_type_vars
 			}
 		// ... normalize
 		
 		# (tcl_file,wtis)
 			= write_type_info td_ident tcl_file wtis
		# (tcl_file,wtis)
 			= write_type_info td_arity tcl_file wtis 				
 		# (tcl_file,wtis)
 			= write_type_info td_args tcl_file wtis	
		# (tcl_file,wtis)
 			= write_type_info td_rhs tcl_file wtis
 			
 		= (tcl_file,wtis)
 	
normalize_type_var :: !ATypeVar (!Int,!*TypeVarHeap) -> (!Int,(!Int,!*TypeVarHeap))
normalize_type_var td_arg=:{atv_variable={tv_info_ptr}} (id,th_vars)
	# th_vars
		= writePtr tv_info_ptr (TVI_Normalized id) th_vars
	= (id,(inc id,th_vars));

sel_type_var_heap :: !*WriteTypeInfoState -> (!*TypeVarHeap,!*WriteTypeInfoState)
sel_type_var_heap wtis=:{wtis_type_heaps}
	# (th_vars,wtis_type_heaps)
		= sel wtis_type_heaps
	= (th_vars,{ wtis & wtis_type_heaps = wtis_type_heaps} )
where
	sel wtis_type_heaps=:{th_vars}
		= (th_vars,{ wtis_type_heaps & th_vars = newHeap } )
 
instance WriteTypeInfo ATypeVar
where 
	write_type_info {atv_variable} tcl_file wtis
 		# (tcl_file,wtis)
 			= write_type_info atv_variable tcl_file wtis
 		= (tcl_file,wtis)

instance WriteTypeInfo TypeVar
where
	write_type_info {tv_info_ptr} tcl_file wtis
		# (th_vars,wtis)
			= sel_type_var_heap wtis
		# ( v,th_vars)
			= readPtr tv_info_ptr th_vars
		# tcl_file
			= fwritei (get_type_var_nf_number v) tcl_file

  		# wtis 
 			= { wtis &
 				wtis_type_heaps.th_vars = th_vars
 			}
 		= (tcl_file,wtis)	
 	where 
 		get_type_var_nf_number (TVI_Normalized i)	= i

instance WriteTypeInfo TypeRhs
where 
	write_type_info (AlgType defined_symbols) tcl_file wtis
 		# tcl_file
 			= fwritec AlgTypeCode tcl_file
		
		# defined_symbols
			= (sortBy (\{ds_ident={id_name=id_name1}} {ds_ident={id_name=id_name2}} -> id_name1 < id_name2) defined_symbols)
		# (tcl_file,wtis)
			= write_type_info defined_symbols tcl_file wtis

		= (tcl_file,wtis)
		
	write_type_info (SynType _) tcl_file wtis
		# tcl_file
 			= fwritec SynTypeCode tcl_file;
  		= (tcl_file,wtis) 
		
	write_type_info (RecordType {rt_constructor,rt_fields}) tcl_file wtis
 		#! tcl_file
 			= fwritec RecordTypeCode tcl_file;
		#! (tcl_file,wtis)
			= write_type_info rt_constructor tcl_file wtis
		#! (tcl_file,wtis)
			= write_type_info rt_fields tcl_file wtis
		= (tcl_file,wtis)

	write_type_info (AbstractType _) tcl_file wtis
 		#! tcl_file
 			= fwritec AbstractTypeCode tcl_file;
 		// unimplemented
		= (tcl_file,wtis)

	write_type_info (AbstractSynType _ _) tcl_file wtis
 		#! tcl_file	= fwritec AbstractTypeCode tcl_file;
 		// unimplemented
		= (tcl_file,wtis)
		
instance WriteTypeInfo DefinedSymbol 
where
	write_type_info {ds_ident,ds_arity,ds_index} tcl_file wtis
		# (tcl_file,wtis)
			= write_type_info ds_ident tcl_file wtis
		# (tcl_file,wtis)
			= write_type_info ds_arity tcl_file wtis
		# (tcl_file,wtis)
			= write_type_info ds_index tcl_file wtis
		= (tcl_file,wtis)

instance WriteTypeInfo Ident 
where
	write_type_info {id_name} tcl_file wtis
		# tcl_file
			= fwritei (size id_name) tcl_file
		= (fwrites id_name tcl_file,wtis)
		
instance WriteTypeInfo FieldSymbol
where
	write_type_info {fs_ident,fs_var,fs_index} tcl_file wtis
		# (tcl_file,wtis)
			= write_type_info fs_ident tcl_file wtis
		# (tcl_file,wtis)
			= write_type_info fs_var tcl_file wtis
		# (tcl_file,wtis)
			= write_type_info fs_index tcl_file wtis
		= (tcl_file,wtis)
		
instance WriteTypeInfo SymbolType
where
	write_type_info symbol_type tcl_file wtis
		#! ({st_vars,st_args,st_args_strictness,st_arity,st_result},wtis)
			= expand_symbol_type symbol_type wtis
		# (tcl_file,wtis)
			= write_type_info st_vars tcl_file wtis
		# (tcl_file,wtis)
			= write_type_info st_args tcl_file wtis
		# (tcl_file,wtis)
			= write_type_info st_args_strictness tcl_file wtis
		# (tcl_file,wtis)
			= write_type_info st_arity tcl_file wtis
		# (tcl_file,wtis)
			= write_type_info st_result tcl_file wtis
		= (tcl_file,wtis)
	where
		expand_symbol_type symbol_type wtis=:{wtis_common_defs,wtis_type_defs,wtis_main_dcl_module_n,wtis_collected_conses,wtis_type_heaps,wtis_var_heap}
			# (expanded_symbol_type,wtis_type_defs,wtis_type_heaps,wtis_var_heap)
				= convertSymbolTypeWithoutCollectingImportedConstructors False wtis_common_defs symbol_type wtis_main_dcl_module_n wtis_type_defs wtis_type_heaps wtis_var_heap;
			# wtis
				= { wtis &
					wtis_type_defs							= wtis_type_defs
				,	wtis_type_heaps							= wtis_type_heaps
				,	wtis_var_heap							= wtis_var_heap
				};
			= (expanded_symbol_type,wtis)
				
instance WriteTypeInfo StrictnessList
where
	write_type_info NotStrict tcl_file wtis
		# tcl_file
			= fwritec NotStrictCode tcl_file
		= (tcl_file,wtis)
	write_type_info (Strict i) tcl_file wtis
		# tcl_file
			= fwritec StrictCode tcl_file
		# tcl_file
			= fwritei i tcl_file
		= (tcl_file,wtis)
	write_type_info (StrictList i tail) tcl_file wtis
		# tcl_file
			= fwritec StrictListCode tcl_file
		# tcl_file
			= fwritei i tcl_file
		= write_type_info tail tcl_file wtis
				
instance WriteTypeInfo AType
where
	write_type_info {at_type} tcl_file wtis
		# (tcl_file,wtis)
			= write_type_info at_type tcl_file wtis
		= (tcl_file,wtis)
		
instance WriteTypeInfo Type
where
	write_type_info (TA type_symb_ident atypes) tcl_file wtis
		# tcl_file
			= fwritec TypeTASCode tcl_file
		# (tcl_file,wtis)
			= write_type_info type_symb_ident tcl_file wtis
		# (tcl_file,wtis)
			= write_type_info atypes tcl_file wtis
		# (tcl_file,wtis)
			= write_type_info NotStrict tcl_file wtis			
		= (tcl_file,wtis)

	write_type_info (TAS type_symb_ident atypes strictness) tcl_file wtis
		# tcl_file
			= fwritec TypeTASCode tcl_file
		# (tcl_file,wtis)
			= write_type_info type_symb_ident tcl_file wtis
		# (tcl_file,wtis)
			= write_type_info atypes tcl_file wtis
		# (tcl_file,wtis)
			= write_type_info strictness tcl_file wtis			
		= (tcl_file,wtis)

	write_type_info (atype1 --> atype2) tcl_file wtis
		# tcl_file
			= fwritec TypeArrowCode tcl_file
		# (tcl_file,wtis)
			= write_type_info atype1 tcl_file wtis
		# (tcl_file,wtis)
			= write_type_info atype2 tcl_file wtis
		= (tcl_file,wtis)
		
	write_type_info (cons_variable :@: atypes) tcl_file wtis
		# tcl_file
			= fwritec TypeConsApplyCode tcl_file
		# (tcl_file,wtis)
			= write_type_info cons_variable tcl_file wtis
		# (tcl_file,wtis)
			= write_type_info atypes tcl_file wtis
		= (tcl_file,wtis)
		
	write_type_info tb=:(TB basic_type) tcl_file wtis
		# (tcl_file,wtis)
			= case basic_type of
				BT_Int		-> (fwritec BT_IntCode tcl_file,wtis)
				BT_Char		-> (fwritec BT_CharCode tcl_file,wtis)
				BT_Real		-> (fwritec BT_RealCode tcl_file,wtis)
				BT_Bool		-> (fwritec BT_BoolCode tcl_file,wtis)
				BT_Dynamic	-> (fwritec BT_DynamicCode tcl_file,wtis)
				BT_File		-> (fwritec BT_FileCode tcl_file,wtis)
				BT_World	-> (fwritec BT_WorldCode tcl_file,wtis)
				BT_String type
					# tcl_file
						= fwritec BT_StringCode tcl_file
					# (tcl_file,wtis)
						= write_type_info type tcl_file wtis
					-> (tcl_file,wtis)
		= (tcl_file,wtis)
	
	write_type_info (GTV type_var) tcl_file wtis
		# tcl_file
			= fwritec TypeGTVCode tcl_file
		# (tcl_file,wtis)
			= write_type_info type_var tcl_file wtis
		= (tcl_file,wtis)

	write_type_info (TV type_var) tcl_file wtis
		# tcl_file
			= fwritec TypeTVCode tcl_file
		# (tcl_file,wtis)
			= write_type_info type_var tcl_file wtis
		= (tcl_file,wtis)
		
	write_type_info (TQV type_var) tcl_file wtis
		# tcl_file
			= fwritec TypeTQVCode tcl_file
		# (tcl_file,wtis)
			= write_type_info type_var tcl_file wtis
		= (tcl_file,wtis)	

	write_type_info TE tcl_file wtis
		# tcl_file
			= fwritec TypeTECode tcl_file
		= (tcl_file,wtis)	

instance WriteTypeInfo ConsVariable
where
	write_type_info (CV type_var) tcl_file wtis
		# tcl_file
			= fwritec ConsVariableCVCode tcl_file
		# (tcl_file,wtis)
			= write_type_info type_var tcl_file wtis
		= (tcl_file,wtis)	

	write_type_info (TempCV temp_var_id) tcl_file wtis
		# tcl_file
			= fwritec ConsVariableTempCVCode tcl_file
		# (tcl_file,wtis)
			= write_type_info temp_var_id tcl_file wtis
		= (tcl_file,wtis)	
		
	write_type_info (TempQCV temp_var_id) tcl_file wtis
		# tcl_file
			= fwritec ConsVariableTempQCVCode tcl_file
		# (tcl_file,wtis)
			= write_type_info temp_var_id tcl_file wtis
		= (tcl_file,wtis)	

instance WriteTypeInfo TypeSymbIdent
where
	write_type_info tsi=:{type_ident,type_arity,type_index={glob_module,glob_object}} tcl_file wtis=:{wtis_predefined_module_def}
		# is_type_without_definition
			= glob_module == wtis_predefined_module_def
		# tcl_file
			= fwritec (if is_type_without_definition TypeSymbIdentWithoutDefinition TypeSymbIdentWithDefinition) tcl_file

		# (tcl_file,wtis)
			= write_type_info type_ident tcl_file wtis
		# (tcl_file,wtis)		 
			= write_type_info type_arity tcl_file wtis
		# (tcl_file,wtis)
			= write_type_info tsi.type_index tcl_file wtis

		= (tcl_file,wtis)

instance WriteTypeInfo (Global object) | WriteTypeInfo object
where
	write_type_info {glob_object,glob_module} tcl_file wtis
		# (tcl_file,wtis)
			= write_type_info glob_object tcl_file wtis
		# (tcl_file,wtis)
			= write_type_info glob_module tcl_file wtis
		= (tcl_file,wtis)
 
// basic and structural write_type_info's
instance WriteTypeInfo Int 
where
	write_type_info i tcl_file wtis
		= (fwritei i tcl_file,wtis)

//1.3
instance WriteTypeInfo {#b} | select_u, size_u, WriteTypeInfo b
//3.1
/*2.0
instance WriteTypeInfo {#b} | Array {#} b & WriteTypeInfo b
0.2*/
where
	write_type_info unboxed_array tcl_file wtis
		# s_unboxed_array
			= size unboxed_array
		# tcl_file
			= fwritei s_unboxed_array tcl_file
			
		= write_type_info_loop 0 s_unboxed_array tcl_file wtis
	where 

		write_type_info_loop i limit tcl_file wtis
			| i == limit
				= (tcl_file,wtis)
			# (tcl_file,wtis)
				= write_type_info unboxed_array.[i] tcl_file wtis
			= write_type_info_loop (inc i) limit tcl_file wtis
			
instance WriteTypeInfo [a] | WriteTypeInfo a
where
	write_type_info l tcl_file wtis
		# tcl_file
			= fwritei (length l) tcl_file
		= write_type_info_loop l tcl_file wtis
	where
		write_type_info_loop []	tcl_file wtis
			= (tcl_file,wtis)
		write_type_info_loop [x:xs] tcl_file wtis
			# (tcl_file,wtis)
				= write_type_info x tcl_file wtis
			= write_type_info_loop xs tcl_file wtis
			
instance WriteTypeInfo Char
where
	write_type_info c tcl_file wtis
		# tcl_file
			= fwritec c tcl_file;
		= (tcl_file,wtis);

instance WriteTypeInfo (a,b) | WriteTypeInfo a & WriteTypeInfo b
where
	write_type_info (c1,c2) tcl_file wtis
		# (tcl_file,wtis)
			= write_type_info c1 tcl_file wtis
		# (tcl_file,wtis)
			= write_type_info c2 tcl_file wtis
		= (tcl_file,wtis)

