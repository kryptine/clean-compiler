//**************************************************************************************
// Generic programming features 
//**************************************************************************************

implementation module generics1

import StdEnv
import check
from checktypes import createClassDictionaries
/*2.0
from transform import ::Group
0.2*/
//1.3
from transform import Group
//3.1

import genericsupport

//**************************************************************************************
// Data types
//**************************************************************************************

:: FunDefs :== {#FunDef}
:: Modules :== {#CommonDefs}
:: DclModules :== {#DclModule}
:: Groups :== {!Group}
:: FunsAndGroups :== (!Index, !Index, ![FunDef], ![Group])

//**************************************************************************************
// Exported functions
//**************************************************************************************

convertGenerics :: 
		!Int 					// index of the main dcl module
		!NumberSet				// set of used modules
		!{#CommonDefs} 			// common definitions of all modules
		!{!Group} 				// groups of functions
		!*{# FunDef} 			// functions
		!*TypeDefInfos 			// type definition information of all modules
		!*Heaps 				// all heaps
		!*HashTable 			// needed for what creating class dictionaries
		!*PredefinedSymbols 	// predefined symbols
		!u:{# DclModule}		// dcl modules
		!*ErrorAdmin 			// to report errors
	->  ( !{#CommonDefs}		// common definitions of all modules
		, !{!Group}				// groups of functions
		, !*{# FunDef}			// function definitions
		, ![IndexRange]			// index ranges of generated functions
		, !*TypeDefInfos		// type definition infos
		, !*Heaps				// all heaps
		, !*HashTable			// needed for creating class dictinaries
		, !*PredefinedSymbols	// predefined symbols	
		, !u:{# DclModule}		// dcl modules
		, !*ErrorAdmin			// to report errors
		)
convertGenerics
		main_dcl_module_n 
		used_module_numbers
		modules 
		groups 
		funs 
		td_infos 
		heaps
		hash_table 
		u_predefs 
		dcl_modules 
		error

	//#! td_infos = td_infos ---> "************************* generic phase started ******************** "
	//#! funs = dump_funs 0 funs
	//#! dcl_modules = dump_dcl_modules 0 dcl_modules
		
	#! modules = {x \\ x <-: modules} 			// unique copy
	#! dcl_modules = { x \\ x <-: dcl_modules } 	// unique copy
	#! size_predefs = size u_predefs
	#! (predefs, u_predefs) = arrayCopyBegin u_predefs size_predefs // non-unique copy

	#! td_infos = clearTypeDefInfos td_infos
		//---> ("used module numbers ", main_dcl_module_n, numberSetToList used_module_numbers)
	#! (modules, heaps) = clearGenericDefs modules heaps 

	#! (iso_range, funs, groups, td_infos, modules, heaps, error)
		= buildGenericRepresentations 
			(main_dcl_module_n /*---> "====================== call buildGenericRepresentations"*/)
			predefs 
			funs groups td_infos modules heaps error
	| not error.ea_ok
		= (modules, groups, funs, [], td_infos, heaps, hash_table, u_predefs, dcl_modules, error)

	// build classes for each kind of each generic function
	#! (modules, dcl_modules, heaps, symbol_table, td_infos, error) 
		= buildClasses 
				main_dcl_module_n used_module_numbers 
				modules dcl_modules heaps hash_table.hte_symbol_heap td_infos error
			//---> ("====================== call buildClasses")
	#! hash_table = { hash_table & hte_symbol_heap = symbol_table }	
	| not error.ea_ok
		= (modules, groups, funs, [], td_infos, heaps, hash_table, u_predefs, dcl_modules, error)

	#! (instance_range, funs, groups, modules, dcl_modules, td_infos, heaps, error)
		= convertGenericCases main_dcl_module_n used_module_numbers predefs funs groups modules dcl_modules td_infos heaps error
			//---> ("====================== call convertGenericCases")

	| not error.ea_ok
		= (modules, groups, funs, [], td_infos, heaps, hash_table, u_predefs, dcl_modules, error)
	
	//#! funs = dump_funs 0 funs
	//#! dcl_modules = dump_dcl_modules 0 dcl_modules
	//#! error = error ---> "************************* generic phase completed ******************** "
	//| True = abort "generic phase aborted for testing\n"		
	= (modules, groups, funs, [iso_range, instance_range], td_infos, heaps, hash_table, u_predefs, dcl_modules, error)
where

	dump_funs n funs 
		| n == size funs
			= funs
			#! ({fun_symb, fun_type, fun_body}, funs) = funs ! [n]
			#! funs = funs
				//---> ("icl function ", fun_symb, n, fun_type, fun_body) 
			=  dump_funs (inc n) funs
	dump_dcl_modules n dcl_modules
		| n == size dcl_modules
			= dcl_modules			
			# ({dcl_functions}, dcl_modules) = dcl_modules ! [n]				
			= dump_dcl_modules (inc n) (dump_dcl_funs 0 dcl_functions dcl_modules)
				//---> ("dcl module", n)		
	dump_dcl_funs n dcl_funs dcl_modules
		| n == size dcl_funs
			= dcl_modules
			# {ft_symb, ft_type} = dcl_funs.[n]
			= dump_dcl_funs (inc n) dcl_funs dcl_modules
				//---> ("dcl function", ft_symb, n, ft_type)


//****************************************************************************************
// clear stuff that might have been left over
// from compilation of other icl modules
//****************************************************************************************

clearTypeDefInfos td_infos
	= clear_modules 0 td_infos
where
	clear_modules n td_infos
		| n == size td_infos
			= td_infos
			#! (td_infos1, td_infos) = replace td_infos n {}
			#! td_infos1 = clear_td_infos 0 td_infos1
			#! (_, td_infos) = replace td_infos n td_infos1
			= clear_modules (inc n) td_infos 
			
	clear_td_infos n td_infos 			
		| n == size td_infos
			= td_infos
			#! (td_info, td_infos) = td_infos![n]
			#! td_infos = {td_infos & [n] = {td_info & tdi_gen_rep = No}}
			= clear_td_infos (inc n) td_infos 

clearGenericDefs modules heaps
	= clear_module 0 modules  heaps
where	
	clear_module n modules heaps
		| n == size modules
			= (modules, heaps)
			#! ({com_generic_defs}, modules) = modules![n]
			#! (com_generic_defs, heaps) = updateArraySt clear_generic_def {x\\x<-:com_generic_defs} heaps 			
			#! modules = {modules & [n].com_generic_defs = com_generic_defs}
			= clear_module (inc n) modules heaps
			
	clear_generic_def _ generic_def=:{gen_name,gen_info_ptr} heaps=:{hp_generic_heap}
		#! (gen_info, hp_generic_heap) = readPtr gen_info_ptr hp_generic_heap
		#! gen_info = 
			{ gen_info 
			& gen_cases = []
			, gen_classes = createArray 32 []
			}	
		#! hp_generic_heap = writePtr gen_info_ptr gen_info hp_generic_heap
		= (generic_def, {heaps & hp_generic_heap = hp_generic_heap})
		
//****************************************************************************************
//	generic type representation
//****************************************************************************************

// generic representation is built for each type argument of
// generic cases of the current module
buildGenericRepresentations ::
		!Index
		!PredefinedSymbols
		!*FunDefs
		!Groups
		!*TypeDefInfos
		!*Modules
		!*Heaps
		!*ErrorAdmin
	->	( !IndexRange
		, !*FunDefs
		, !Groups
		, !*TypeDefInfos
		, !*Modules
		, !*Heaps
		, !*ErrorAdmin
		) 
buildGenericRepresentations main_module_index predefs funs groups td_infos modules heaps error
	
	#! size_funs = size funs
	#! size_groups = size groups
	#! ({com_gencase_defs}, modules) = modules ! [main_module_index]
			
	#! ((new_fun_index, new_group_index, new_funs, new_groups), td_infos, modules, heaps, error) 
		= foldArraySt on_gencase com_gencase_defs ((size_funs, size_groups, [], []), td_infos, modules, heaps, error)

	#! funs = arrayPlusRevList funs new_funs
	#! groups = arrayPlusRevList groups new_groups

	#! range = {ir_from = size_funs, ir_to = new_fun_index}

	= (range, funs, groups, td_infos, modules, heaps, error)
where 

	on_gencase index case_def=:{gc_type_cons,gc_name} st
		= build_generic_rep_if_needed gc_type_cons st 

	build_generic_rep_if_needed :: 
			!TypeCons !((!Index,!Index,![FunDef],![Group]), !*TypeDefInfos, !*{#CommonDefs}, !*Heaps, !*ErrorAdmin)	
		->  (!(!Index, !Index, ![FunDef], ![Group]), !*TypeDefInfos, !*{#CommonDefs}, !*Heaps, !*ErrorAdmin)
	build_generic_rep_if_needed (TypeConsSymb {type_index={glob_module,glob_object}, type_name}) (funs_and_groups, td_infos, modules, heaps, error)
		#! (type_def, modules) = modules![glob_module].com_type_defs.[glob_object]
		#! (td_info, td_infos) = td_infos![glob_module, glob_object]
		#! type_def_gi = {gi_module=glob_module,gi_index=glob_object}
		= case td_info.tdi_gen_rep of
			Yes _ 
				-> (funs_and_groups, td_infos, modules, heaps, error)
					//---> ("generic representation is already built", type_name)
			No 
				#! (gen_type_rep, funs_and_groups, modules, heaps, error)
					= buildGenericTypeRep type_def_gi main_module_index predefs funs_and_groups modules heaps error
							
				#! td_info = {td_info & tdi_gen_rep = Yes gen_type_rep}
				#! td_infos = {td_infos & [glob_module, glob_object] = td_info} 
				-> (funs_and_groups, td_infos, modules, heaps, error)					
					//---> ("build generic representation", type_name)
	build_generic_rep_if_needed _ st = st 
	
buildGenericTypeRep :: 
		!GlobalIndex 			// type def index
		!Index 					// main module index 
		!PredefinedSymbols 	
		!(!Index,!Index,![FunDef],![Group]) 
		!*{#CommonDefs} 
		!*Heaps 
		!*ErrorAdmin 
	->	( !GenericTypeRep
		, !(!Index, !Index, ![FunDef], ![Group])
		, !*{#CommonDefs} 
		, !*Heaps
		, !*ErrorAdmin
		)
buildGenericTypeRep type_index main_module_index predefs funs_and_groups modules heaps error
	# (type_def, modules) = modules![type_index.gi_module].com_type_defs.[type_index.gi_index]
	# (atype, modules,error) = buildStructureType type_index predefs modules error
	
	# (from_fun_ds, funs_and_groups, heaps, error)
		= buildConversionFrom type_index.gi_module type_def main_module_index predefs funs_and_groups heaps error

	# (to_fun_ds, funs_and_groups, heaps, error)
		= buildConversionTo type_index.gi_module type_def main_module_index predefs funs_and_groups heaps error

	# (iso_fun_ds, funs_and_groups, heaps, error)
		= buildConversionIso type_def from_fun_ds to_fun_ds main_module_index predefs funs_and_groups heaps error

	= ({gtr_type=atype,gtr_iso=iso_fun_ds}, funs_and_groups, modules, heaps, error)
		//---> ("buildGenericTypeRep", type_def.td_name, atype)
	
//========================================================================================
//	the structure type
//========================================================================================

buildStructureType :: 
		!GlobalIndex				// type definition module 
		!PredefinedSymbols
		!*{#CommonDefs}
		!*ErrorAdmin
	-> 	( !AType			// the structure type
		, !*{#CommonDefs}
		, !*ErrorAdmin
		)
buildStructureType {gi_module,gi_index} predefs modules error
	# (type_def=:{td_name}, modules) = modules![gi_module].com_type_defs.[gi_index]	
	# (common_defs, modules) = modules ! [gi_module]	
	# (atype, error) = build_type type_def common_defs error	
	= (atype, modules, error)
		//---> ("buildStructureType", td_name, atype)	
where 
	build_type {td_rhs=(AlgType alts)} common_defs error
		# cons_defs = [common_defs.com_cons_defs.[ds_index] \\ {ds_index} <- alts]
		# cons_args = [buildProductType cons_def.cons_type.st_args predefs \\ cons_def <- cons_defs]
		= (buildSumType cons_args predefs, error) 	
	build_type {td_rhs=(RecordType {rt_constructor={ds_index}})} common_defs error
		# cons_def = common_defs.com_cons_defs.[ds_index]
		= (buildProductType cons_def.cons_type.st_args predefs, error)
	build_type {td_rhs=(SynType type)} common_defs error
		= (type /* is that correct ???*/, error)
	build_type td=:{td_rhs=(AbstractType _),td_name, td_arity, td_args, td_pos} common_defs error
		= (makeAType TE TA_Multi, 
			reportError td_name td_pos "cannot build a generic representation of an abstract type" error)
		
// build a product of types
buildProductType :: ![AType] !PredefinedSymbols -> !AType
buildProductType types predefs 
	= listToBin build_pair build_unit types
where
	build_pair x y = buildPredefTypeApp PD_TypePAIR [x, y] predefs	
	build_unit  = buildPredefTypeApp PD_TypeUNIT [] predefs

// build a sum of types		
buildSumType :: ![AType] !PredefinedSymbols -> !AType
buildSumType types predefs 
	= listToBin build_either build_void types
where
	build_either x y = buildPredefTypeApp PD_TypeEITHER [x, y] predefs	
	build_void  = abort "sum of zero types\n"

// build a binary representation of a list
listToBin :: (a a -> a) a [a] -> a 
listToBin bin tip [] = tip
listToBin bin tip [x] = x
listToBin bin tip xs
	# (l,r) = splitAt ((length xs) / 2) xs
	= bin (listToBin bin tip l) (listToBin bin tip r)

// build application of a predefined type constructor 
buildPredefTypeApp :: !Int [AType] !PredefinedSymbols -> !AType
buildPredefTypeApp predef_index args predefs
	# {pds_module, pds_def} = predefs.[predef_index]
	# pds_ident = predefined_idents.[predef_index]
	# global_index = {glob_module = pds_module, glob_object = pds_def}
	# type_symb = MakeTypeSymbIdent global_index pds_ident (length args) 		  
	= makeAType (TA type_symb args) TA_Multi

//========================================================================================
//	conversions functions
//========================================================================================

// buildConversionIso
buildConversionIso :: 
		!CheckedTypeDef		// the type definition
		!DefinedSymbol		// from fun
		!DefinedSymbol	 	// to fun
		!Index				// main module
		!PredefinedSymbols		
		(!Index, !Index, ![FunDef], ![Group])
		!*Heaps
		!*ErrorAdmin
	-> 	( !DefinedSymbol
		, (!Index, !Index, ![FunDef], ![Group])
		, !*Heaps
		, !*ErrorAdmin
		)
buildConversionIso 
		type_def=:{td_name, td_pos}
		from_fun 
		to_fun
		main_dcl_module_n
		predefs
		funs_and_groups
		heaps 
		error
	#! (from_expr, heaps) 	= buildFunApp main_dcl_module_n from_fun [] heaps
	#! (to_expr, heaps) 	= buildFunApp main_dcl_module_n to_fun [] heaps	
	#! (iso_expr, heaps) 	= build_iso to_expr from_expr heaps
	
	#! ident = makeIdent ("iso" +++ td_name.id_name)
	#! (def_sym, funs_and_groups) = buildFunAndGroup ident [] iso_expr No main_dcl_module_n td_pos funs_and_groups
	= (def_sym, funs_and_groups, heaps, error)
		//---> ("buildConversionIso", td_name, let (_,_,fs,_) = funs_and_groups in hd fs)
where
	build_iso to_expr from_expr heaps 
		= buildPredefConsApp PD_ConsBimap [to_expr, from_expr] predefs heaps	
		
// conversion from type to generic
buildConversionTo ::
		!Index				// type def module
		!CheckedTypeDef 	// the type def
		!Index 				// main module
		!PredefinedSymbols
		!(!Index, !Index, ![FunDef], ![Group])
		!*Heaps	
		!*ErrorAdmin
	-> 	( !DefinedSymbol
		, (!Index, !Index, ![FunDef], ![Group])
		, !*Heaps
		, !*ErrorAdmin	
		)
buildConversionTo		
		type_def_mod 
		type_def=:{td_rhs, td_name, td_index, td_pos} 
		main_module_index
		predefs
		funs_and_groups
		heaps
		error
	# (arg_expr, arg_var, heaps) = buildVarExpr "x" heaps 
	# (body_expr, heaps, error) = 
		build_expr_for_type_rhs type_def_mod td_index td_rhs arg_expr heaps error
	# fun_name = makeIdent ("fromGenericTo" +++ td_name.id_name)
	| not error.ea_ok
		# (def_sym, funs_and_groups) 
			= (buildFunAndGroup fun_name [] EE No main_module_index td_pos funs_and_groups)
		= (def_sym, funs_and_groups, heaps, error)	
			//---> ("buildConversionTo failed", td_name)
		# (def_sym, funs_and_groups) 
			= (buildFunAndGroup fun_name [arg_var] body_expr No main_module_index td_pos funs_and_groups)
		= (def_sym, funs_and_groups, heaps, error)
			//---> ("buildConversionTo", td_name, let (_,_,fs,_) = funs_and_groups in hd fs)
where
	// build conversion for type rhs
	build_expr_for_type_rhs :: 
			!Int 				// type def module
			!Int 				// type def index 
			!TypeRhs			// type def rhs 
			!Expression			// expression of the function argument variable   
			!*Heaps 
			!*ErrorAdmin
		-> 	( !Expression		// generated expression
			, !*Heaps	// state
			, !*ErrorAdmin
			)
 	build_expr_for_type_rhs type_def_mod type_def_index (AlgType def_symbols) arg_expr heaps error
		= build_expr_for_conses type_def_mod type_def_index def_symbols arg_expr heaps error
	build_expr_for_type_rhs type_def_mod type_def_index (RecordType {rt_constructor}) arg_expr heaps error		
		= build_expr_for_conses type_def_mod type_def_index [rt_constructor] arg_expr  heaps error
	build_expr_for_type_rhs type_def_mod type_def_index (AbstractType _) arg_expr  heaps error
		#! error = checkErrorWithIdentPos (newPosition td_name td_pos) "cannot build isomorphisms for an abstract type" error
		= (EE, heaps, error)
	build_expr_for_type_rhs type_def_mod type_def_index (SynType _) arg_expr  heaps error
		#! error = checkErrorWithIdentPos (newPosition td_name td_pos) "cannot build isomorphisms for a synonym type" error
		= (EE, heaps, error)
	
	// build conversion for constructors of a type def 	
	build_expr_for_conses type_def_mod type_def_index cons_def_syms arg_expr heaps error
		# (case_alts, heaps, error) = 
			build_exprs_for_conses 0 (length cons_def_syms) type_def_mod cons_def_syms  heaps error
		# case_patterns = AlgebraicPatterns {glob_module = type_def_mod, glob_object = type_def_index} case_alts
		# (case_expr, heaps) = buildCaseExpr arg_expr case_patterns heaps
		= (case_expr, heaps, error)	
			//---> (free_vars, case_expr)		
	
	// build conversions for a constructor 	
	build_exprs_for_conses :: !Int !Int !Int ![DefinedSymbol] !*Heaps !*ErrorAdmin
		-> ([AlgebraicPattern], !*Heaps, !*ErrorAdmin)
	build_exprs_for_conses i n type_def_mod [] heaps error = ([], heaps, error) 	
	build_exprs_for_conses i n type_def_mod [cons_def_sym:cons_def_syms] heaps error
		#! (alt, heaps, error) = build_expr_for_cons i n type_def_mod cons_def_sym heaps error
		#! (alts, heaps, error) =  build_exprs_for_conses (i+1) n type_def_mod cons_def_syms heaps error 		
		= ([alt:alts], heaps, error)
					
	// build conversion for a constructor	
	build_expr_for_cons :: !Int !Int !Int !DefinedSymbol !*Heaps !*ErrorAdmin 
		-> (AlgebraicPattern, !*Heaps, !*ErrorAdmin)
	build_expr_for_cons 	
		i n type_def_mod def_symbol=:{ds_ident, ds_arity}
		heaps error
	
		#! names = ["x" +++ toString (i+1) +++ toString k \\ k <- [1..ds_arity]]
		#! (var_exprs, vars, heaps) = buildVarExprs names heaps 
		#! (expr, heaps) = build_prod var_exprs predefs heaps		
		#! (expr, heaps) = build_sum i n expr predefs heaps
				
		#! alg_pattern = {
			ap_symbol = {glob_module = type_def_mod, glob_object = def_symbol},
			ap_vars = vars,
			ap_expr = expr,
			ap_position = NoPos
			}
		= (alg_pattern, heaps, error)	
	
	build_sum :: !Int !Int !Expression !PredefinedSymbols !*Heaps -> (!Expression, !*Heaps)
	build_sum i n expr predefs heaps
		| n == 0 	= abort "build sum of zero elements\n"
		| i >= n	= abort "error building sum"
		| n == 1 	= (expr, heaps)
		| i < (n/2) 
			# (expr, heaps) = build_sum i (n/2) expr predefs heaps
			= build_left expr heaps
		| otherwise
			# (expr, heaps) = build_sum (i - (n/2)) (n - (n/2)) expr predefs heaps
			= build_right expr heaps
	where
		build_left x heaps = buildPredefConsApp PD_ConsLEFT [x] predefs heaps
		build_right x heaps = buildPredefConsApp PD_ConsRIGHT [x] predefs heaps
				
	build_prod :: ![Expression] !PredefinedSymbols !*Heaps -> (!Expression, !*Heaps)
	build_prod [] predefs heaps = build_unit heaps
	where
		build_unit heaps = buildPredefConsApp PD_ConsUNIT [] predefs heaps 	
	build_prod [expr] predefs heaps = (expr, heaps)
	build_prod exprs predefs heaps
		# (lexprs, rexprs) = splitAt ((length exprs)/2) exprs  
		# (lexpr, heaps) = build_prod lexprs predefs heaps
		# (rexpr, heaps) = build_prod rexprs predefs heaps
		= build_pair lexpr rexpr heaps
	where
		build_pair x y heaps = buildPredefConsApp PD_ConsPAIR [x, y] predefs heaps
			
buildConversionFrom	::	
		!Index				// type def module
		!CheckedTypeDef 	// the type def
		!Index 				// main module
		!PredefinedSymbols
		!(!Index, !Index, ![FunDef], ![Group])
		!*Heaps	
		!*ErrorAdmin
	-> 	( !DefinedSymbol
		, (!Index, !Index, ![FunDef], ![Group])
		, !*Heaps
		, !*ErrorAdmin	
		)
buildConversionFrom		
		type_def_mod 
		type_def=:{td_rhs, td_name, td_index, td_pos} 
		main_module_index
		predefs
		funs_and_groups
		heaps
		error
	# (body_expr, arg_var, heaps, error) = 
		build_expr_for_type_rhs type_def_mod td_rhs heaps error
	# fun_name = makeIdent ("toGenericFrom" +++ td_name.id_name)
	| not error.ea_ok
		# (def_sym, funs_and_groups) 
			= (buildFunAndGroup fun_name [] EE No main_module_index td_pos funs_and_groups)
		= (def_sym, funs_and_groups, heaps, error)	
			//---> ("buildConversionFrom failed", td_name)
		# (def_sym, funs_and_groups) 
			= (buildFunAndGroup fun_name [arg_var] body_expr No main_module_index td_pos funs_and_groups)
		= (def_sym, funs_and_groups, heaps, error)
			//---> ("buildConversionFrom", td_name, let (_,_,fs,_) = funs_and_groups in hd fs)
where
	// build expression for type def rhs
	build_expr_for_type_rhs :: 
			!Index				// type def module
			!TypeRhs			// type rhs
			!*Heaps
			!*ErrorAdmin	
		-> 	( !Expression		// body expresssion
			, !FreeVar
			, !*Heaps
			, !*ErrorAdmin
			)		
	build_expr_for_type_rhs type_def_mod (AlgType def_symbols) heaps error
		= build_sum type_def_mod def_symbols heaps error
	build_expr_for_type_rhs type_def_mod (RecordType {rt_constructor}) heaps error				
		= build_sum type_def_mod [rt_constructor] heaps	error
	build_expr_for_type_rhs type_def_mod (AbstractType _) heaps error
		#! error = reportError td_name td_pos "cannot build isomorphisms for an abstract type" error
		= (EE, undef, heaps, error)
	build_expr_for_type_rhs type_def_mod (SynType _) heaps error
		#! error = reportError td_name td_pos "cannot build isomorphisms for a synonym type" error
		= (EE, undef, heaps, error)
	
	// build expression for sums
	build_sum :: 
			!Index 
			![DefinedSymbol] 
			!*Heaps 
			!*ErrorAdmin
		-> 	( !Expression
			, !FreeVar			// top variable
			, !*Heaps
			, !*ErrorAdmin
			)
	build_sum type_def_mod [] heaps error
		= abort "algebraic type with no constructors!\n"
	build_sum type_def_mod [def_symbol] heaps error
		#! (cons_app_expr, cons_arg_vars, heaps) = build_cons_app type_def_mod def_symbol heaps
		#! (alt_expr, var, heaps) = build_prod cons_app_expr cons_arg_vars heaps 		
		= (alt_expr, var, heaps, error)
	build_sum type_def_mod def_symbols heaps error
		#! (left_def_syms, right_def_syms) = splitAt ((length def_symbols) /2) def_symbols
	
		#! (left_expr, left_var, heaps, error) 
			= build_sum type_def_mod left_def_syms heaps error

		#! (right_expr, right_var, heaps, error) 
			= build_sum type_def_mod right_def_syms heaps error
	
		#! (case_expr, var, heaps) = 
			build_case_either left_var left_expr right_var right_expr heaps
		= (case_expr, var, heaps, error)
	
	// build expression for products
	build_prod :: 
			!Expression   					// result of the case on product
			![FreeVar] 						// list of variables of the constructor pattern
			!*Heaps
		-> 	( !Expression					// generated product
			, !FreeVar						// top variable
			, !*Heaps
			)
	build_prod expr [] heaps
		= build_case_unit expr heaps	
	build_prod expr [cons_arg_var] heaps
		= (expr, cons_arg_var, heaps)	
	build_prod expr cons_arg_vars heaps
		#! (left_vars, right_vars) = splitAt ((length cons_arg_vars) /2) cons_arg_vars		 
		#! (expr, left_var, heaps) = build_prod expr left_vars heaps
		#! (expr, right_var, heaps) = build_prod expr right_vars heaps		
		#! (case_expr, var, heaps) = build_case_pair left_var right_var expr heaps		
		= (case_expr, var, heaps) 
	
	// build constructor applicarion expression
	build_cons_app :: !Index !DefinedSymbol !*Heaps 
		-> (!Expression, ![FreeVar], !*Heaps)
	build_cons_app cons_mod def_symbol=:{ds_arity} heaps
		#! names = ["x"  +++ toString k \\ k <- [1..ds_arity]]
		#! (var_exprs, vars, heaps) = buildVarExprs names heaps 
		#! (expr, heaps) = buildConsApp cons_mod def_symbol var_exprs heaps
	 	= (expr, vars, heaps)

	// build case expressions for PAIR, EITHER and UNIT
	build_case_unit body_expr heaps
		# unit_pat = buildPredefConsPattern PD_ConsUNIT [] body_expr predefs
		# {pds_module, pds_def} = predefs.[PD_TypeUNIT]
		# case_patterns = AlgebraicPatterns {glob_module = pds_module, glob_object = pds_def} [unit_pat]
		= build_case_expr case_patterns heaps
		
	build_case_pair var1 var2 body_expr heaps
		# pair_pat = buildPredefConsPattern PD_ConsPAIR [var1, var2] body_expr predefs	
		# {pds_module, pds_def} = predefs.[PD_TypePAIR]
		# case_patterns = AlgebraicPatterns {glob_module = pds_module, glob_object = pds_def} [pair_pat]	
		= build_case_expr case_patterns heaps
	
	build_case_either left_var left_expr right_var right_expr heaps
		# left_pat = buildPredefConsPattern PD_ConsLEFT [left_var] left_expr predefs
		# right_pat = buildPredefConsPattern PD_ConsRIGHT [right_var] right_expr predefs
		# {pds_module, pds_def} = predefs.[PD_TypeEITHER]
		# case_patterns = AlgebraicPatterns {glob_module = pds_module, glob_object = pds_def} [left_pat, right_pat]
		= build_case_expr case_patterns heaps

	// case with a variable as the selector expression
	build_case_expr case_patterns heaps
		# (var_expr, var, heaps) = buildVarExpr "c" heaps
		# (case_expr, heaps) = buildCaseExpr var_expr case_patterns heaps
		= (case_expr, var, heaps)
		

//****************************************************************************************
// build kind indexed classes 
//****************************************************************************************

buildClasses :: 
		!Int
		!NumberSet 
		!*{#CommonDefs} 
		!*{#.DclModule} 
		!*Heaps 
		!*SymbolTable 
		!*TypeDefInfos
		!*ErrorAdmin 
	->	(.{#CommonDefs}
		,.{#DclModule}
		,.Heaps
		,.SymbolTable
		,.TypeDefInfos
		,.ErrorAdmin
		)
buildClasses main_module_index used_module_numbers modules dcl_modules heaps symbol_table td_infos error
	#! (common_defs=:{com_class_defs, com_member_defs}, modules) = modules ! [main_module_index]
	#! num_classes = size com_class_defs
	#! num_members = size com_member_defs

/*
	#! (modules, (classes, members, new_num_classes, new_num_members, heaps, td_infos, error)) 
		= mapGenericCaseDefs on_gencase modules ([], [], num_classes, num_members, heaps, td_infos, error)
*/
	#! (modules, (classes, members, new_num_classes, new_num_members, heaps, td_infos, error)) 
		= build_modules 0 modules ([], [], num_classes, num_members, heaps, td_infos, error)

	// obtain common definitions again because com_gencase_defs are updated 
	#! (common_defs, modules) = modules ! [main_module_index]	
	# common_defs = 
		{ common_defs 
		& com_class_defs = arrayPlusRevList com_class_defs classes
		, com_member_defs = arrayPlusRevList com_member_defs members
		}
		
	#! (common_defs, dcl_modules, heaps, symbol_table) 
		= build_class_dictionaries common_defs dcl_modules heaps symbol_table
	
	#! modules = {modules & [main_module_index] = common_defs}	
	= (modules, dcl_modules, heaps, symbol_table, td_infos, error)  
where
	build_modules module_index modules st
		| module_index == size modules
			= (modules, st)
			#! (common_defs=:{com_gencase_defs}, modules) = modules![module_index] 
			#! (com_gencase_defs, modules, st) 
				= build_module module_index com_gencase_defs modules st 
			#! modules = 
				{ modules 
				& [module_index] = {common_defs & com_gencase_defs = com_gencase_defs }
				} 
			= build_modules (inc module_index) modules st

	build_module module_index com_gencase_defs modules st
		| inNumberSet module_index used_module_numbers
			#! com_gencase_defs = {x\\x<-:com_gencase_defs} 
			= build_module1 module_index 0 com_gencase_defs modules st
			= (com_gencase_defs, modules, st)

	build_module1 module_index index com_gencase_defs modules st
		| index == size com_gencase_defs
			= (com_gencase_defs, modules, st)
			#! (gencase, com_gencase_defs) = com_gencase_defs ! [index]
			#! (gencase, modules, st) = on_gencase module_index index gencase modules st
			#! com_gencase_defs = {com_gencase_defs & [index] = gencase} 	
			= build_module1 module_index (inc index) com_gencase_defs modules st

	on_gencase :: 
			!Index 
			!Index 
			!GenericCaseDef 
			!*Modules 
			(![ClassDef], ![MemberDef], !Index, Index, !*Heaps, !*TypeDefInfos, !*ErrorAdmin)
		->  ( !GenericCaseDef
			, !*Modules 
			, (![ClassDef], ![MemberDef], !Index, Index, !*Heaps, !*TypeDefInfos, !*ErrorAdmin)
			)
	on_gencase 
			module_index index 
			gencase=:{gc_name,gc_generic, gc_type_cons} 
			modules
			(classes, members, class_index, member_index, heaps, td_infos, error)

		#! (gen_def, modules) = modules ! [gc_generic.gi_module].com_generic_defs.[gc_generic.gi_index] 
		#! (kind, td_infos) = get_kind_of_type_cons gc_type_cons td_infos

		//#! kinds = partially_applied_kinds kind
		#! st = build_class_if_needed gen_def kind (classes, members, class_index, member_index, modules, heaps, error)	

		// build classes needed for shorthand instances
		#! (classes, members, class_index, member_index, modules, heaps, error)
			= case kind of 
				KindConst -> st
				KindArrow ks
					-> foldSt (build_class_if_needed gen_def) [KindConst:ks] st 
				
		#! gencase = { gencase & gc_kind = kind }				
		= (gencase, modules, (classes, members, class_index, member_index, heaps, td_infos, error))

	build_class_if_needed gen_def kind (classes, members, class_index, member_index, modules, heaps, error)
		#! (opt_class_info, heaps) = lookup_generic_class_info gen_def kind heaps
		= case opt_class_info of
			No 
				#! (class_def, member_def, modules, heaps, error) 
					= buildClassAndMember main_module_index class_index member_index kind gen_def modules heaps error 
				#! class_info = 
					{	gci_kind = kind
					,	gci_module = main_module_index
					,	gci_class = class_index
					,	gci_member = member_index
					}
				#! heaps = add_generic_class_info gen_def class_info heaps
				-> ([class_def:classes], [member_def:members], inc class_index, inc member_index, modules, heaps, error)
			Yes class_info	
				-> (classes, members, class_index, member_index, modules, heaps, error)
	
	partially_applied_kinds KindConst 
		= [KindConst]
	partially_applied_kinds (KindArrow kinds) 
		= do_it kinds
	where
		do_it [] = [KindConst]
		do_it all_ks=:[k:ks] = [(KindArrow all_ks) : do_it ks] 
				
	get_kind_of_type_cons :: !TypeCons !*TypeDefInfos -> (!TypeKind, !*TypeDefInfos)
	get_kind_of_type_cons (TypeConsBasic _) td_infos 
		= (KindConst, td_infos)
	get_kind_of_type_cons TypeConsArrow td_infos
		= (KindArrow [KindConst,KindConst], td_infos)
	get_kind_of_type_cons (TypeConsSymb {type_name, type_index}) td_infos
		#! ({tdi_kinds}, td_infos) = td_infos ! [type_index.glob_module,type_index.glob_object]
		= (if (isEmpty tdi_kinds) KindConst (KindArrow tdi_kinds), td_infos)
	get_kind_of_type_cons (TypeConsVar tv) td_infos
		= (KindConst, td_infos)

	lookup_generic_class_info {gen_info_ptr} kind heaps=:{hp_generic_heap}
		#! ({gen_classes}, hp_generic_heap) = readPtr gen_info_ptr hp_generic_heap
		= (lookupGenericClassInfo kind gen_classes
			, {heaps & hp_generic_heap = hp_generic_heap})

	add_generic_class_info	{gen_info_ptr} class_info heaps=:{hp_generic_heap}	
		#! (gen_info=:{gen_classes}, hp_generic_heap) = readPtr gen_info_ptr hp_generic_heap
		#! gen_classes = addGenericClassInfo class_info gen_classes
		#! hp_generic_heap = writePtr gen_info_ptr {gen_info&gen_classes=gen_classes} hp_generic_heap
		= {heaps & hp_generic_heap = hp_generic_heap}
			
	build_class_dictionaries			
			common_defs dcl_modules
			heaps=:{hp_type_heaps=hp_type_heaps=:{th_vars}, hp_var_heap}
			symbol_table 
		#! class_defs = { x \\ x <-: common_defs.com_class_defs } // make unique copy
		#  type_defs = { x \\ x <-: common_defs.com_type_defs } // make unique copy
		#  cons_defs = { x \\ x <-: common_defs.com_cons_defs } // make unique copy
		#  selector_defs = { x \\ x <-: common_defs.com_selector_defs } // make unique copy
		#  (size_type_defs,type_defs) = usize type_defs 
		#! (new_type_defs, new_selector_defs, new_cons_defs,_,type_defs,selector_defs,cons_defs,class_defs, dcl_modules, th_vars, hp_var_heap, symbol_table) =
				createClassDictionaries
					False 
					main_module_index 
					size_type_defs
					(size common_defs.com_selector_defs) 
					(size common_defs.com_cons_defs) 
					type_defs selector_defs cons_defs class_defs dcl_modules th_vars hp_var_heap symbol_table

		#! common_defs = { common_defs & 
			com_class_defs = class_defs, 
			com_type_defs = arrayPlusList type_defs new_type_defs,
			com_selector_defs = arrayPlusList selector_defs new_selector_defs,
			com_cons_defs = arrayPlusList cons_defs new_cons_defs}

		#! heaps = {heaps & hp_var_heap = hp_var_heap, hp_type_heaps = {hp_type_heaps & th_vars = th_vars}} 
		= (common_defs, dcl_modules, heaps, symbol_table)		


// limitations:
// - context restrictions on generic variables are not allowed
buildMemberType :: 
		!GenericDef 
		!TypeKind 
		!TypeVar 
		!*Modules
		!*TypeHeaps 
		!*GenericHeap
		!*ErrorAdmin
	->	( !SymbolType
		, !*Modules
		, !*TypeHeaps
		, !*GenericHeap
		, !*ErrorAdmin
		)
buildMemberType {gen_name,gen_pos,gen_type,gen_vars} kind class_var modules th gh error
	#! (kind_indexed_st, gatvs, th, error) 
		= buildKindIndexedType gen_type gen_vars kind gen_name gen_pos th error
			//---> ("buildMemberType called for", gen_name, kind, gen_type)
	#! (member_st, th, error) 
		= replace_generic_vars_with_class_var kind_indexed_st gatvs kind th error

	#! th = assertSymbolType member_st th
	#! th = assertSymbolType gen_type th
					
	= (member_st, modules, th, gh, error)
		//---> ("buildMemberType returns", gen_name, kind, member_st)
where

	replace_generic_vars_with_class_var st atvs kind th error			
		#! th = subst_gvs atvs th
			//---> ("replace_generic_vars_with_class_var called for", atvs, st)
		#! (new_st, th) = applySubstInSymbolType st th
		= (new_st, th, error)
			//---> ("replace_generic_vars_with_class_var returns", new_st)
	where
		subst_gvs atvs th=:{th_vars, th_attrs}
			#! tvs = [atv_variable \\ {atv_variable} <- atvs ]
			#! avs = [av \\ {atv_attribute=TA_Var av} <- atvs ]
			
			# th_vars = foldSt subst_tv tvs th_vars
		
/*			 			
			# th_attrs = case kind of
					KindConst -> case avs of 
						[av:avs] 	-> foldSt (subst_av av) avs th_attrs
						[] 			-> th_attrs
					_ -> th_attrs	
*/
			# th_attrs = case avs of 
				[av:avs]	-> foldSt (subst_av av) avs th_attrs
				[] 			-> th_attrs

 			= { th & th_vars = th_vars, th_attrs = th_attrs }
		
		subst_tv {tv_info_ptr} th_vars
			= writePtr tv_info_ptr (TVI_Type (TV class_var)) th_vars

		subst_av av {av_info_ptr} th_attrs
			= writePtr av_info_ptr (AVI_Attr (TA_Var av)) th_attrs
				//---> ("(1) writePtr av_info_ptr", ptrToInt av_info_ptr, av)

buildClassAndMember 
		module_index class_index member_index kind 
		gen_def=:{gen_name, gen_pos} modules heaps error
	#! (class_var, heaps) = fresh_class_var heaps
	#! (member_def, modules, heaps, error) 
		= build_class_member class_var modules heaps error	
	#! class_def = build_class class_var member_def
	= (class_def, member_def, modules, heaps, error)
		//---> ("buildClassAndMember", gen_def.gen_name, kind)
where
	fresh_class_var heaps=:{hp_type_heaps=th=:{th_vars}}
		# (tv, th_vars) = freshTypeVar (makeIdent "class_var") th_vars
		= (tv, {heaps & hp_type_heaps = { th & th_vars = th_vars }})

	class_ident = genericIdentToClassIdent gen_def.gen_name kind 
	member_ident = genericIdentToMemberIdent gen_def.gen_name kind 
	class_ds = {ds_index = class_index, ds_ident = class_ident, ds_arity = 1}

	build_class_member class_var modules heaps=:{hp_var_heap, hp_type_heaps, hp_generic_heap} error
		#! (type_ptr, hp_var_heap) = newPtr VI_Empty hp_var_heap 
		#! (tc_var_ptr, hp_var_heap) = newPtr VI_Empty hp_var_heap 
		#! type_context = 
			{	tc_class = {glob_module = module_index, glob_object=class_ds}
			,	tc_types = [ TV class_var ] 
			,	tc_var = tc_var_ptr 
			}
		#! (member_type, modules, hp_type_heaps, hp_generic_heap, error) 
			= buildMemberType gen_def kind class_var modules hp_type_heaps hp_generic_heap error
		#! member_type = { member_type & st_context = [type_context : member_type.st_context] }
		#! member_def = {
			me_symb = member_ident, 
			me_class = {glob_module = module_index, glob_object = class_index},
			me_offset = 0,
			me_type = member_type,
			me_type_ptr = type_ptr,				// empty
			me_class_vars = [class_var], 		// the same variable as in the class
			me_pos = gen_pos,
			me_priority = NoPrio
			}
				//---> ("member_type", member_type)
		= (member_def, modules, {heaps & hp_type_heaps = hp_type_heaps, hp_var_heap = hp_var_heap, hp_generic_heap = hp_generic_heap}, error)
	build_class class_var member_def=:{me_type}
		#! class_member = 
			{ ds_ident = member_ident
			, ds_index = member_index
			, ds_arity = me_type.st_arity
			}
		#! class_dictionary = 
			{ ds_ident = class_ident 
			, ds_arity = 0 
			, ds_index = NoIndex/*index in the type def table, filled in later*/ 
			}
		#! class_def = { 
			class_name = class_ident, 
			class_arity = 1,  
			class_args = [class_var],
		    class_context = [], 
		    class_pos = gen_pos, 
		    class_members = createArray 1 class_member, 
		    class_cons_vars = 0, // dotted class variables
		    class_dictionary = class_dictionary,
		    class_arg_kinds = [kind]
		    }	 
			
		= class_def	

							
//****************************************************************************************
// Convert generic cases 
//****************************************************************************************
convertGenericCases ::
		!Index					// current module
		!NumberSet				// used module numbers
		!PredefinedSymbols
		!*{#FunDef}	
		!{!Group}			
		!*{#CommonDefs}
		!*{#DclModule}
		!*TypeDefInfos
		!*Heaps
		!*ErrorAdmin
	-> 	( !IndexRange			// created instance functions
		, !*{#FunDef}			// added instance functions
		, !{!Group}				// added instance groups
		, !*{#CommonDefs}		// added instances
		, !*{#DclModule}			// updated function types
		, !*TypeDefInfos
		, !*Heaps
		, !*ErrorAdmin
		) 		
convertGenericCases 
		main_module_index used_module_numbers 
		predefs funs groups modules dcl_modules td_infos heaps error

	#! (first_fun_index, funs) = usize funs
	#! first_group_index = size groups
	#! fun_info = (first_fun_index, first_group_index, [], [])

	#! first_instance_index = size main_module_instances	
	#! instance_info = (first_instance_index, [])
	
	#! (modules1, dcl_modules, (fun_info, instance_info, funs, td_infos, heaps, error)) 
		= convert_modules 0 modules1 dcl_modules (fun_info, instance_info, funs, td_infos, heaps, error)
	
	#! (fun_index, group_index, new_funs, new_groups) = fun_info
	#! funs = arrayPlusRevList funs new_funs
	#! groups = arrayPlusRevList groups new_groups
	
	#! (instance_index, new_instances) = instance_info 
	#! com_instance_defs = arrayPlusRevList main_module_instances new_instances

	#! main_common_defs = {main_common_defs & com_instance_defs = com_instance_defs}	
	#! modules1 = {modules1 & [main_module_index] = main_common_defs}
	
	#! instance_fun_range = {ir_from=first_fun_index, ir_to=fun_index}	 
	= (instance_fun_range, funs, groups, modules1, dcl_modules, td_infos, heaps, error)
where

	(main_common_defs, modules1) = modules ! [main_module_index]
	main_module_classes = main_common_defs.com_class_defs
	main_module_members = main_common_defs.com_member_defs
	main_module_instances = main_common_defs.com_instance_defs

	convert_modules ::
			!Index
			!*{#CommonDefs}
			!*{#DclModule}
			( FunsAndGroups
			, (!Index, ![ClassInstance])
			, !*{#FunDef}
			, !*TypeDefInfos
			, !*Heaps
			, !*ErrorAdmin
			)
		-> 	(!*{#CommonDefs}
			,*{#DclModule} 
			,	( FunsAndGroups
				, (!Index, ![ClassInstance])
				, !*{#FunDef}
			 	, !*TypeDefInfos
				, !*Heaps
				, !*ErrorAdmin
				)
			)			
	convert_modules module_index modules dcl_modules st
		| module_index == size modules
			= (modules, dcl_modules, st)
			#! (common_defs=:{com_gencase_defs}, modules) = modules ! [module_index]
			#! (dcl_module=:{dcl_functions}, dcl_modules) = dcl_modules ! [module_index]
			#! (dcl_functions, modules, st) 
				= convert_module module_index com_gencase_defs {x\\x<-:dcl_functions} modules st  
			#! dcl_modules = {dcl_modules & [module_index] = {dcl_module & dcl_functions = dcl_functions}} 
			= convert_modules (inc module_index) modules dcl_modules st

	convert_module module_index com_gencase_defs dcl_functions modules st
		| inNumberSet module_index used_module_numbers		 
			#! dcl_functions = {x\\x<-:dcl_functions}
			= foldArraySt (convert_gencase module_index) 
				com_gencase_defs (dcl_functions, modules, st)
			= (dcl_functions, modules, st)

	convert_gencase :: 
			!Index
			!Index
			!GenericCaseDef
			(!*{#FunType}
			,!*Modules
			,	( FunsAndGroups
			 	, (!Index, ![ClassInstance])
			 	, !*{#FunDef}
			 	, !*TypeDefInfos
			 	, !*Heaps
			 	, !*ErrorAdmin
			 	)
			)
		-> (!*{#FunType}
			,!*Modules
			,	( FunsAndGroups
			 	, (!Index, ![ClassInstance])
			 	, !*{#FunDef}
			 	, !*TypeDefInfos
			 	, !*Heaps
			 	, !*ErrorAdmin
			 	)
			)					
	convert_gencase module_index gc_index gencase=:{gc_name, gc_type} st
		#! st = build_main_instance module_index gc_index gencase st	
		#! st = build_shorthand_instance_if_needed module_index gc_index gencase st	
		= st
			//---> ("convert gencase", gc_name, gc_type)

	build_main_instance module_index gc_index 
			gencase=:{gc_name, gc_kind, gc_generic, gc_pos, gc_type, gc_type_cons, gc_body = GCB_FunIndex fun_index} 
			(dcl_functions, modules, (fun_info, ins_info, fun_defs, td_infos, heaps, error))
		#! ({gen_classes}, modules, heaps) 
			= get_generic_info gc_generic modules heaps			
		#  (Yes class_info) 
			= lookupGenericClassInfo gc_kind gen_classes
			
		#! {class_members} 
			= main_module_classes . [class_info.gci_class] 		
		#! member_def 
			= main_module_members . [class_members.[0].ds_index]

		#! ins_type = 
			{	it_vars	= case gc_type_cons of 
					TypeConsVar tv 	-> [tv]
					_				-> []
			,	it_types = [gc_type]
			,	it_attr_vars = []
			,	it_context = []
			}

		#! (fun_type, heaps, error)
			= determine_type_of_member_instance member_def ins_type heaps error

		#! (dcl_functions, heaps) 
			= update_dcl_function fun_index gencase fun_type dcl_functions heaps

		#! (fun_info, fun_defs, td_infos, modules, heaps, error) 
				= update_icl_function_if_needed 
						module_index 
						fun_index gencase fun_type 
						fun_info fun_defs td_infos modules heaps error

		#! (fun_info, ins_info, heaps)
			= build_instance_and_member module_index class_info.gci_class gencase fun_type ins_type fun_info ins_info heaps  
		
		= (dcl_functions, modules, (fun_info, ins_info, fun_defs, td_infos, heaps, error))

	build_shorthand_instance_if_needed module_index gc_index gencase=:{gc_kind=KindConst} st
		= st
	build_shorthand_instance_if_needed 
			module_index gc_index 
			gencase=:{gc_name, gc_generic, gc_kind=KindArrow arg_kinds, gc_type} 
			(dcl_functions, modules, (fun_info, ins_info, fun_defs, td_infos, heaps, error))

		#! (star_class_info, (modules, heaps)) 
			= get_class_for_kind gc_generic KindConst (modules, heaps)

		#! (arg_class_infos, (modules, heaps)) 
			= mapSt (get_class_for_kind gc_generic) arg_kinds (modules, heaps)

		#! {class_members} 
			= main_module_classes . [star_class_info.gci_class] 		
		#! member_def 
			= main_module_members . [class_members.[0].ds_index]

		#! (ins_type, heaps) 
			= build_instance_type gc_type arg_class_infos heaps

		#! (fun_type, heaps, error)
			= determine_type_of_member_instance member_def ins_type heaps error
		
		#! (memfun_ds, fun_info, heaps) 
			= build_shorthand_instance_member module_index gencase fun_type arg_class_infos fun_info heaps
		
		#! ins_info 
			= build_class_instance star_class_info.gci_class gencase memfun_ds ins_type ins_info
				
		= (dcl_functions, modules, (fun_info, ins_info, fun_defs, td_infos, heaps, error))
	where
		build_instance_type type class_infos heaps=:{hp_type_heaps=th=:{th_vars},hp_var_heap}
			#! arity = length class_infos
			#! type_var_names = [makeIdent ("a" +++ toString i) \\ i <- [1 .. arity]]
			#! (type_vars, th_vars) = mapSt freshTypeVar type_var_names th_vars 
			#! type_var_types = [TV tv \\ tv <- type_vars] 	
			#! new_type_args = [makeAType t TA_Multi \\ t <- type_var_types]
			
			#! type = fill_type_args type new_type_args	
			
			#! (contexts, hp_var_heap) 
				= zipWithSt build_context class_infos type_vars hp_var_heap
			
			#! ins_type = 
				{	it_vars	= type_vars
				,	it_types = [type]
				,	it_attr_vars = []
				,	it_context = contexts
				}
											 
			= (ins_type, {heaps & hp_type_heaps = {th & th_vars = th_vars}, hp_var_heap = hp_var_heap})
				//---> ("instance type for shorthand instance", gc_name, gc_type, ins_type)
		where
			fill_type_args (TA type_symb_ident=:{type_arity} type_args) new_type_args
				#! type_arity = type_arity + length new_type_args 
				#! type_args = type_args ++ new_type_args
				= TA {type_symb_ident & type_arity = type_arity} type_args 
			fill_type_args TArrow [arg_type, res_type]
				= arg_type --> res_type
			fill_type_args (TArrow1 arg_type) [res_type]
				= arg_type --> res_type	 
			fill_type_args type args
				= abort ("fill_type_args\n"---> ("fill_type_args", type, args)) 

			build_context {gci_class, gci_module, gci_kind} tv hp_var_heap
				# (var_info_ptr, hp_var_heap) = newPtr VI_Empty hp_var_heap			
				# type_context =		
					{	tc_class = 
							{ glob_module=gci_module // the same as icl module
							, glob_object =
								{ ds_ident = genericIdentToClassIdent gc_name gci_kind
								, ds_index = gci_class
								, ds_arity = 1
								}
							}
					,	tc_types = [TV tv]
					,	tc_var	 = var_info_ptr
					}
				= (type_context, hp_var_heap)	

	get_generic_info {gi_module, gi_index} modules heaps=:{hp_generic_heap}
		#! ({gen_info_ptr}, modules) 
			= modules ! [gi_module] . com_generic_defs . [gi_index]
		#! (gen_info, hp_generic_heap) = readPtr gen_info_ptr hp_generic_heap	
		= (gen_info, modules, {heaps & hp_generic_heap = hp_generic_heap})

	get_class_for_kind generic_gi kind (modules, heaps)
		#! ({gen_classes}, modules, heaps) = get_generic_info generic_gi modules heaps
		# (Yes class_info) = lookupGenericClassInfo kind gen_classes
		= (class_info, (modules, heaps))	


	determine_type_of_member_instance :: !MemberDef !InstanceType !*Heaps !*ErrorAdmin
		-> (!SymbolType, !*Heaps, !*ErrorAdmin)
	determine_type_of_member_instance {me_type, me_class_vars} ins_type heaps=:{hp_type_heaps, hp_var_heap} error
		#! (symbol_type, _, hp_type_heaps, _, error) 
			= determineTypeOfMemberInstance me_type me_class_vars ins_type SP_None hp_type_heaps No error
		#! (st_context, hp_var_heap) = initializeContextVariables symbol_type.st_context hp_var_heap
		#! hp_type_heaps = clearSymbolType me_type hp_type_heaps
		#! symbol_type = {symbol_type & st_context = st_context}
		#! heaps = {heaps & hp_type_heaps = hp_type_heaps, hp_var_heap = hp_var_heap}
		= (symbol_type, heaps, error)
			//---> ("determine_type_of_member_instance", ins_type, symbol_type) 

	update_dcl_function :: !Index !GenericCaseDef !SymbolType !*{#FunType} !*Heaps
		-> (!*{#FunType}, !*Heaps)
	update_dcl_function fun_index {gc_name, gc_type_cons} symbol_type dcl_functions heaps 
		| fun_index < size dcl_functions
			#! (symbol_type, heaps) = fresh_symbol_type symbol_type heaps			
			#! (fun, dcl_functions) = dcl_functions ! [fun_index]
			#! fun = 
				{ fun 
				& ft_symb = genericIdentToFunIdent gc_name gc_type_cons
				, ft_type = symbol_type
				}
			#! dcl_functions = { dcl_functions & [fun_index] = fun}
			= (dcl_functions, heaps)
				//---> ("update dcl function", fun.ft_symb, fun_index, symbol_type)  
			= (dcl_functions, heaps)
				//---> ("update dcl function: not in the dcl module", fun_index)  

	update_icl_function_if_needed module_index fun_index gencase fun_type fun_info fun_defs td_infos modules heaps error
		| module_index == main_module_index  // current module
			#! (fi, gi, fs, gs) = fun_info
			#! (gi, gs, fun_defs, td_infos, modules, heaps, error) 
				= update_icl_function fun_index gencase fun_type gi gs fun_defs td_infos modules heaps error
			= ((fi, gi, fs, gs), fun_defs, td_infos, modules, heaps, error)
			= (fun_info, fun_defs, td_infos, modules, heaps, error)
			
	update_icl_function :: 
			!Index !GenericCaseDef !SymbolType 
			!Index ![Group] !*{#FunDef} !*TypeDefInfos !*{#CommonDefs} !*Heaps !*ErrorAdmin 
		-> (!Index, ![Group], !*{#FunDef}, !*TypeDefInfos, !*{#CommonDefs}, !*Heaps, !*ErrorAdmin)
	update_icl_function fun_index gencase=:{gc_name, gc_type_cons, gc_pos} st group_index groups fun_defs td_infos modules heaps error
		#! (st, heaps) = fresh_symbol_type st heaps
		#! (fun=:{fun_body, fun_arity}, fun_defs) = fun_defs ! [fun_index] 		
		#! fun_ident = genericIdentToFunIdent gc_name gc_type_cons
		= case fun_body of 
			TransformedBody tb	// user defined case			
				| fun_arity <> st.st_arity						
					# error = reportError gc_name gc_pos 
						("incorrect arity: " +++ toString st.st_arity +++ " expected") error
					-> (group_index, groups, fun_defs, td_infos, modules, heaps, error)	
				#! fun = 
					{ fun 
					& fun_symb = fun_ident 
					, fun_type = Yes st
					, fun_body = fun_body
					}
				#! fun_defs = { fun_defs & [fun_index] = fun }		
				-> (group_index, groups, fun_defs, td_infos, modules, heaps, error)	
					//---> ("update_icl_function, TransformedBody", fun.fun_symb, fun_index, st)
						
			GeneratedBody		// derived case
				#! (TransformedBody {tb_args, tb_rhs}, td_infos, modules, heaps, error)  
						= buildGenericCaseBody main_module_index gencase st predefs td_infos modules heaps error
					//---> ("call buildGenericCaseBody\n")
				#! fun = makeFunction fun_ident fun_index group_index tb_args tb_rhs (Yes st) main_module_index gc_pos
				#! fun_defs = { fun_defs & [fun_index] = fun }
				
				# group = {group_members=[fun_index]}
						
				-> (inc group_index, [group:groups], fun_defs, td_infos, modules, heaps, error)
					//---> ("update_icl_function, GeneratedBody", fun.fun_symb, fun_index, st)
			_ -> abort "update_icl_function: generic case body\n"
	
	// build wrapping instance for the generic case function
	build_instance_and_member :: !Index !Index !GenericCaseDef !SymbolType !InstanceType !FunsAndGroups (!Index, ![ClassInstance]) !*Heaps
		-> (!FunsAndGroups, (!Index, ![ClassInstance]), !*Heaps)
	build_instance_and_member module_index class_index gencase symbol_type ins_type fun_info ins_info heaps
		#! (memfun_ds, fun_info, heaps) 
			= build_instance_member module_index gencase symbol_type fun_info heaps
		#! ins_info = build_class_instance class_index gencase memfun_ds ins_type ins_info
		= (fun_info, ins_info, heaps)
	
	// Creates a function that just calls the generic case function
	// It is needed because the instance member must be in the same
	// module as the instance itself
	build_instance_member module_index gencase st fun_info heaps
	
		# {gc_name, gc_pos, gc_type_cons, gc_kind, gc_body=GCB_FunIndex fun_index} = gencase
		#! arg_var_names = ["x" +++ toString i \\ i <- [1..st.st_arity]]
		#! (arg_var_exprs, arg_vars, heaps) = buildVarExprs arg_var_names heaps
	
		#! (expr_info_ptr, hp_expression_heap) = newPtr EI_Empty heaps.hp_expression_heap
		#! heaps = {heaps & hp_expression_heap = hp_expression_heap}
		#! fun_name = genericIdentToFunIdent gc_name gc_type_cons
		#! expr = App 
			{ app_symb = 
				{ symb_name=fun_name
				, symb_kind=SK_Function {glob_module=module_index, glob_object=fun_index}
				}
			, app_args = arg_var_exprs
			, app_info_ptr = expr_info_ptr
			}
	
		#! (st, heaps) = fresh_symbol_type st heaps
	
		#! memfun_name = genericIdentToMemberIdent gc_name gc_kind
		#! (fun_ds, fun_info) 
			= buildFunAndGroup memfun_name arg_vars expr (Yes st) main_module_index gc_pos fun_info
		= (fun_ds, fun_info, heaps)
	
	build_shorthand_instance_member module_index gencase=:{gc_generic, gc_name, gc_kind, gc_pos} st class_infos fun_info heaps
		#! arg_var_names = ["x" +++ toString i \\ i <- [1..st.st_arity]]
		#! (arg_var_exprs, arg_vars, heaps) = buildVarExprs arg_var_names heaps
	
		#! (expr_info_ptr, hp_expression_heap) = newPtr EI_Empty heaps.hp_expression_heap
		#! heaps = {heaps & hp_expression_heap = hp_expression_heap}
		#! fun_name = genericIdentToMemberIdent gc_name KindConst

		# (gen_exprs, heaps) = mapSt (build_generic_app gc_generic gc_name) class_infos heaps

		# (body_expr, heaps) 
			= buildGenericApp gc_generic.gi_module gc_generic.gi_index 
				gc_name gc_kind (gen_exprs ++ arg_var_exprs) heaps

		#! (st, heaps) = fresh_symbol_type st heaps
	
		#! (fun_ds, fun_info) 
			= buildFunAndGroup fun_name arg_vars body_expr (Yes st) main_module_index gc_pos fun_info

		= (fun_ds, fun_info, heaps)		
			//---> ("shorthand instance body", body_expr)
	where
		build_generic_app {gi_module, gi_index} gc_name {gci_kind} heaps
			= buildGenericApp gi_module gi_index gc_name gci_kind [] heaps	
	
	build_class_instance class_index gencase member_fun_ds ins_type (ins_index, instances) 
		
		# {gc_pos, gc_name, gc_kind} = gencase
		
		#! class_name = genericIdentToClassIdent gc_name gc_kind		
		#! class_ds = {ds_index = class_index, ds_arity=1, ds_ident=class_name}
		#! ins = 
		 	{	ins_class 	= {glob_module=main_module_index, glob_object=class_ds}
			,	ins_ident 	= class_name
			,	ins_type 	= ins_type
			,	ins_members	= {member_fun_ds}
			,	ins_specials = SP_None
			,	ins_pos		= gc_pos
			}
		
		= (inc ins_index, [ins:instances])
	
	fresh_symbol_type :: !SymbolType !*Heaps -> (!SymbolType, !*Heaps)	
	fresh_symbol_type st heaps=:{hp_type_heaps}
		# (fresh_st, hp_type_heaps) = freshSymbolType st hp_type_heaps
		= (fresh_st, {heaps & hp_type_heaps = hp_type_heaps})	
			//---> ("fresh_symbol_type")
		
buildGenericCaseBody :: 
		!Index
		!GenericCaseDef
		!SymbolType
		!PredefinedSymbols
		!*TypeDefInfos
		!*{#CommonDefs} 
		!*Heaps 
		!*ErrorAdmin 
	-> 	( !FunctionBody
		, !*TypeDefInfos
		, !*{#CommonDefs}
		, !*Heaps
		, !*ErrorAdmin
		)
buildGenericCaseBody main_module_index {gc_name,gc_pos, gc_generic, gc_type_cons=TypeConsSymb {type_index}} st predefs td_infos modules heaps error

	// get all the data we need
	#! (gen_def=:{gen_vars, gen_type, gen_bimap}, modules) 	
		= modules ! [gc_generic.gi_module].com_generic_defs.[gc_generic.gi_index] 
	#! (td_info=:{tdi_gen_rep}, td_infos)
		= td_infos ! [type_index.glob_module, type_index.glob_object]
	# ({gtr_iso, gtr_type}) = case tdi_gen_rep of
		Yes x -> x
		No -> abort "no generic representation\n"

	#! (type_def=:{td_args}, modules) 
		= modules ! [type_index.glob_module].com_type_defs.[type_index.glob_object]
	
	#! original_arity 	= gen_type.st_arity 			// arity of generic type
	#! generated_arity 	= st.st_arity - original_arity	// number of added arguments (arity of the kind)	

	// generate variable names and exprs
	#! generated_arg_names = [ "f" +++ toString n \\ n <- [1 .. generated_arity]]
	#! (generated_arg_exprs, generated_arg_vars, heaps) = buildVarExprs generated_arg_names heaps	
	#! original_arg_names = [ "x" +++ toString n \\ n <- [1 .. original_arity]]  
	#! (original_arg_exprs, original_arg_vars, heaps) = buildVarExprs original_arg_names heaps	
	#! arg_vars = generated_arg_vars ++ original_arg_vars

	// create adaptor
	#! (iso_exprs, heaps) 
		= unfoldnSt (buildFunApp main_module_index gtr_iso []) (length gen_vars) heaps	
	#! (bimap_id_exprs, heaps) 
		= unfoldnSt (buildPredefFunApp PD_bimapId [] predefs) (length (gen_type.st_vars -- gen_vars)) heaps 

	//#! (bimap_expr, heaps) 
	//	= buildFunApp main_module_index gen_bimap iso_exprs heaps
	#! spec_env = 
		[(tv,expr)\\tv <- gen_vars & expr <- iso_exprs]	
		++
		[(tv,expr)\\tv <- gen_type.st_vars -- gen_vars & expr <- bimap_id_exprs]
	#! curried_gen_type = curry_symbol_type gen_type
	#! {pds_module = bimap_module, pds_def=bimap_index} = predefs.[PD_GenericBimap]
	
	#! (bimap_expr, (td_infos, heaps, error)) 
		= buildSpecializedExpr1 
			bimap_module bimap_index 
			curried_gen_type spec_env
			gc_name gc_pos 
			(td_infos, heaps, error)	
					
	#! adaptor_expr = buildRecordSelectionExpr bimap_expr PD_map_from predefs	

	// create expression for the generic representation
	#! spec_env = [(atv_variable, expr) \\ {atv_variable} <- td_args & expr <- generated_arg_exprs] 
	#! (specialized_expr, (td_infos, heaps, error)) 
		= buildSpecializedExpr1 
			gc_generic.gi_module gc_generic.gi_index 
			gtr_type spec_env
			gc_name gc_pos 
			(td_infos, heaps, error)

	// create the body expr
	#! body_expr = if (isEmpty original_arg_exprs)
		(adaptor_expr @ [specialized_expr]) 
		((adaptor_expr @ [specialized_expr]) @ original_arg_exprs)
  
	= (TransformedBody {tb_args=arg_vars, tb_rhs=body_expr}, td_infos, modules, heaps, error)	
		//---> (" buildGenericCaseBody", body_expr)
where
	curry_symbol_type {st_args, st_result}
		= foldr (\x y -> makeAType (x --> y) TA_Multi) st_result st_args 	

//buildGenericCaseBody main_module_index {gc_name,gc_pos, gc_generic, gc_type_cons=TypeConsSymb {type_index}} st predefs td_infos modules heaps error
buildGenericCaseBody main_module_index {gc_name,gc_pos} st predefs td_infos modules heaps error
	# error = reportError gc_name gc_pos "cannot specialize to this type" error
	= (TransformedBody {tb_args=[], tb_rhs=EE}, td_infos, modules, heaps, error)
			 							 
//****************************************************************************************
//  specialization
//****************************************************************************************

buildSpecializedExpr1 ::
		!Index					// generic module
		!Index					// generic index
		!AType					// type to specialize to
		![(TypeVar, Expression)] // specialization environment
		!Ident					// generic/generic case
		!Position				// of generic case
		(!*TypeDefInfos, !*Heaps, !*ErrorAdmin)
	->  ( !Expression
		, !(!*TypeDefInfos, !*Heaps, !*ErrorAdmin)
		)
buildSpecializedExpr1 gen_module gen_index atype spec_env ident pos (td_infos, heaps, error)

	#! heaps = set_tvs spec_env heaps
	#! (expr, (td_infos, heaps, error)) 
		= buildSpecializedExpr gen_module gen_index atype ident pos (td_infos, heaps, error)

	#! heaps = clear_tvs spec_env heaps
	= (expr, (td_infos, heaps, error))
where
	set_tvs spec_env heaps=:{hp_type_heaps=hp_type_heaps=:{th_vars}}
		#! th_vars = foldSt write_tv spec_env th_vars
			with write_tv ({tv_info_ptr}, expr) th_vars
					= writePtr tv_info_ptr (TVI_Expr expr) th_vars		
		= {heaps & hp_type_heaps = {hp_type_heaps & th_vars = th_vars }}

	clear_tvs spec_env heaps=:{hp_type_heaps=hp_type_heaps=:{th_vars}}
		#! th_vars = foldSt write_tv spec_env th_vars
			with write_tv ({tv_info_ptr}, _) th_vars
					= writePtr tv_info_ptr TVI_Empty th_vars		
		= {heaps & hp_type_heaps = {hp_type_heaps & th_vars = th_vars }}

// generates an expression that corresponds to a type
buildSpecializedExpr ::
		!Index					// generic module index
		!Index 					// generic index
		!AType					// type to specialize to
								// tv_info_ptr of type variables must contain expressions
								// corresponding to the type variables 
		!Ident					// for error reporting
		!Position				// for error reporting
		!(!*TypeDefInfos, !*Heaps, !*ErrorAdmin)
	->  ( !Expression			// generated expression
		, !(!*TypeDefInfos, !*Heaps, !*ErrorAdmin)
		)
buildSpecializedExpr gen_module gen_index type gen_name pos gs 
	= spec_atype type gs
where
	spec_atype {at_type} gs = spec_type at_type gs 

	spec_atypes [] gs = ([], gs)
	spec_atypes [type:types]  gs
		# (expr, gs) = spec_atype type gs 
		# (exprs, gs) = spec_atypes types gs 
		= ([expr:exprs], gs)

	spec_type :: !Type !(!*TypeDefInfos, !*Heaps, !*ErrorAdmin)
		-> !(Expression, !(!*TypeDefInfos, !*Heaps, !*ErrorAdmin))
	spec_type (TA {type_index, type_name} args) st
		# (arg_exprs, st) = spec_atypes args st
		# (kind, st) = get_kind type_index st 
		= build_generic_app kind arg_exprs st  
	spec_type (TAS {type_index, type_name} args _) st
		# (arg_exprs, st) = spec_atypes args st
		# (kind, st) = get_kind type_index st 
		= build_generic_app kind arg_exprs st  
	spec_type (arg_type --> res_type) st
		#! (arg_expr, st) = spec_atype arg_type st
		#! (res_expr, st) = spec_atype res_type st
		= build_generic_app (KindArrow [KindConst, KindConst]) [arg_expr, res_expr] st
	spec_type ((CV type_var) :@: args) gs 
		#! (expr, gs) = spec_type_var type_var gs
		#! (exprs, gs) = spec_atypes args gs
		= (expr @ exprs, gs)	
	spec_type (TB basic_type) st
		= build_generic_app KindConst [] st
	spec_type (TFA atvs type) (td_infos, heaps, error) 
		#! error = reportError gen_name pos "cannot specialize to forall types" error
		= (EE, (td_infos, heaps, error))
	spec_type (TV type_var) gs  = spec_type_var type_var gs
	//spec_type (GTV type_var) gs = spec_type_var type_var gs
	//spec_type (TQV type_var) gs = spec_type_var type_var gs
	//spec_type (TLifted type_var) gs = spec_type_var type_var gs
	spec_type _ (td_infos, heaps, error)
		#! error = reportError gen_name pos "cannot specialize to this type" error
		= (EE, (td_infos, heaps, error))
	
	spec_type_var tv=:{tv_info_ptr} (td_infos, heaps=:{hp_type_heaps=th=:{th_vars}}, error)		
		#! (TVI_Expr expr, th_vars) = readPtr tv_info_ptr th_vars
		= (expr, (td_infos, {heaps & hp_type_heaps = {th & th_vars = th_vars}}, error))

	build_generic_app kind arg_exprs (td_infos, heaps, error)
		# (expr, heaps) 
			= buildGenericApp gen_module gen_index gen_name kind arg_exprs heaps 
		= (expr, (td_infos, heaps, error))

	get_kind {glob_module, glob_object} (td_infos, heaps, error)
		# (td_info, td_infos) = td_infos ! [glob_module, glob_object]
		= (make_kind td_info.tdi_kinds, (td_infos, heaps, error))
	where	
		make_kind [] = KindConst
		make_kind ks = KindArrow ks
		
//****************************************************************************************
//	kind indexing of generic types
//****************************************************************************************

// kind indexing:
// t_* a1 ... an 			= t a1 ... an 
// t_{k->l} a1 ... an		= forall b1...bn.(t_k b1 ... bn) -> (t_l (a1 b1) ... (an bn)) 
buildKindIndexedType :: 
		!SymbolType			// symbol type to kind-index
		![TypeVar]			// generic type variables
		!TypeKind			// kind index
		!Ident				// name for debugging
		!Position 			// position for debugging
		!*TypeHeaps			// type heaps
		!*ErrorAdmin		
	-> 	( !SymbolType		// instantiated type
		, ![ATypeVar]		// fresh generic type variables
		, !*TypeHeaps		// type heaps
		, !*ErrorAdmin	
		)
buildKindIndexedType st gtvs kind ident pos th error
	
	#! th = clearSymbolType st th
		//---> ("buildKindIndexedType called for", kind, gtvs, st)			 
	#! (fresh_st, fresh_gtvs, th) = fresh_generic_type st gtvs th	

	#! (gatvs, th) = collectAttrsOfTypeVarsInSymbolType fresh_gtvs fresh_st th

	#! (kind_indexed_st, _, th, error) = build_symbol_type fresh_st gatvs kind 1 th error	
	 	 
	#! th = clearSymbolType kind_indexed_st th
	#! th = clearSymbolType st th				// paranoja
	= (kind_indexed_st, gatvs, th, error)
		//---> ("buildKindIndexedType returns", kind_indexed_st)			 
where

	fresh_generic_type st gtvs th
		# (fresh_st, th) = freshSymbolType st th
		# fresh_gtvs = take (length gtvs) fresh_st.st_vars		
		= (fresh_st, fresh_gtvs, th)
			//---> ("fresh_generic_type", fresh_gtvs, fresh_st)

	build_symbol_type :: 
			 !SymbolType 	// generic type, 
			 ![ATypeVar]		// attributed generic variables
			 !TypeKind 		// kind to specialize to 
			 !Int 			// current order (in the sense of the order of the kind)
			 !*TypeHeaps
			 !*ErrorAdmin	
		-> ( !SymbolType	// new generic type
			, ![ATypeVar]	// fresh copies of generic variables created for the 
							// generic arguments
			, !*TypeHeaps
			, !*ErrorAdmin
			)
	build_symbol_type st gatvs KindConst order th error	
		= (st, [], th, error)
	build_symbol_type st gatvs (KindArrow kinds) order th error
		| order > 2
				//---> ("build_symbol_type called for", (KindArrow kinds), gatvs, st)
			# error = reportError ident pos "kinds of order higher then 2 are not supported" error
			= (st, [], th, error)
		
		# (arg_sts, arg_gatvss, th, error) 
			= build_args st gatvs order kinds th error 

		# (body_st, th) 
			= build_body st gatvs (transpose arg_gatvss) th 

		# num_added_args = length kinds
		# new_st = 
			{ st_vars = removeDup (
					foldr (++) body_st.st_vars [st_vars \\ {st_vars}<-arg_sts])
			, st_attr_vars = removeDup (
					foldr (++) body_st.st_attr_vars [st_attr_vars \\ {st_attr_vars}<-arg_sts])
			, st_args = [st_result \\ {st_result}<-arg_sts] ++ body_st.st_args
			, st_result = body_st.st_result 
			, st_arity = body_st.st_arity + num_added_args
			, st_context = removeDup(
				foldr (++) body_st.st_context [st_context \\ {st_context} <- arg_sts])
			, st_attr_env = removeDup(
				foldr (++) body_st.st_attr_env [st_attr_env \\ {st_attr_env} <- arg_sts])
			, st_args_strictness = insert_n_lazy_values_at_beginning num_added_args body_st.st_args_strictness	 
			}
	
		= (new_st, flatten arg_gatvss, th, error)
			//---> ("build_symbol_type returns", arg_gatvss, st)

	build_args st gatvs order kinds th error
		# (arg_sts_and_gatvss, (_,th,error)) 
			= mapSt (build_arg st gatvs order) kinds (1,th,error)
		# (arg_sts, arg_gatvss) = unzip arg_sts_and_gatvss
		= (arg_sts, arg_gatvss, th, error)

	build_arg :: 
			!SymbolType 		// current part of the generic type
			![ATypeVar]			// generic type variables with their attrs
			!Int 				// order
			!TypeKind			// kind corrseponding to the arg
			( !Int				// the argument number
			, !*TypeHeaps
			, !*ErrorAdmin
			)				
		->  ( (!SymbolType, [ATypeVar]) // fresh symbol type and generic variables 
			, 	( !Int			// incremented argument number
				, !*TypeHeaps
				, !*ErrorAdmin
				)
			)
	build_arg st gatvs order kind (arg_num, th, error)		
		#! th = clearSymbolType st th
			//---> ("build_arg called for", arg_num, kind, gatvs, st)
		#! (fresh_gatvs, th) = mapSt subst_gatv gatvs th 
		#! (new_st, th) = applySubstInSymbolType st th
		
		#! (new_st, forall_atvs, th, error) 
			= build_symbol_type new_st fresh_gatvs kind (inc order) th error	
		#! (curry_st, th)	
			= curryGenericArgType1 new_st ("cur" +++ toString order +++ postfix) th 	
		
		#! curry_st = adjust_forall curry_st forall_atvs
				
		= ((curry_st, fresh_gatvs), (inc arg_num, th, error))
			//---> ("build_arg returns", fresh_gatvs, curry_st)		
	where
		postfix = toString arg_num
		 
		subst_gatv atv=:{atv_attribute, atv_variable} th=:{th_attrs, th_vars}			
			# (tv, th_vars) = subst_gtv atv_variable th_vars 
			# (attr, th_attrs) = subst_attr atv_attribute th_attrs 			
			=	( {atv & atv_variable = tv, atv_attribute = attr}
			 	, {th & th_vars = th_vars, th_attrs = th_attrs}
			 	)	
			
		// generic type var is replaced with a fresh one
		subst_gtv {tv_info_ptr, tv_name} th_vars 
			# (tv, th_vars) = freshTypeVar (postfixIdent tv_name postfix) th_vars	
			= (tv, writePtr tv_info_ptr (TVI_Type (TV tv)) th_vars)
		
		subst_attr (TA_Var {av_name, av_info_ptr}) th_attrs 
			# (av, th_attrs) = freshAttrVar (postfixIdent av_name postfix) th_attrs
			= (TA_Var av, writePtr av_info_ptr (AVI_Attr (TA_Var av)) th_attrs)
				//---> ("(2) writePtr av_info_ptr", ptrToInt av_info_ptr, av)
		subst_attr TA_Multi th = (TA_Multi, th)
		subst_attr TA_Unique th = (TA_Unique, th)

		adjust_forall curry_st [] = curry_st
		adjust_forall curry_st=:{st_result} forall_atvs 
			#! st_result = {st_result & at_type = TFA forall_atvs st_result.at_type}
		 	= 	{ curry_st 
				& st_result = st_result
				, st_attr_vars 
					= curry_st.st_attr_vars -- [av \\ {atv_attribute=TA_Var av} <- forall_atvs]
				, st_vars 
					= curry_st.st_vars -- [atv_variable \\ {atv_variable} <- forall_atvs]
				} 
				//---> ("adjust forall", curry_st.st_vars, forall_atvs, curry_st.st_vars -- [atv_variable \\ {atv_variable} <- forall_atvs])								

	build_body :: 
			!SymbolType 
			![ATypeVar]
			![[ATypeVar]]
			!*TypeHeaps
		->	(!SymbolType
			, !*TypeHeaps
			)
	build_body st gatvs arg_gatvss  th
		# th = clearSymbolType st th
		# th = fold2St subst_gatv gatvs arg_gatvss th
		= applySubstInSymbolType st th 
	where
		subst_gatv gatv=:{atv_variable} arg_gatvs th=:{th_vars}
			#! type_args = [ makeAType (TV atv_variable) atv_attribute 
							\\ {atv_variable, atv_attribute} <- arg_gatvs]
			#! type = (CV atv_variable) :@: type_args
			#! th_vars = writePtr atv_variable.tv_info_ptr (TVI_Type type) th_vars
			= {th & th_vars = th_vars}	
		
reportError name pos msg error=:{ea_file} 
	//= checkErrorWithIdentPos (newPosition name pos) msg error
	# ea_file = ea_file <<< "Error " <<< (newPosition name pos) <<< ":" <<< msg <<< '\n'
	= { error & ea_file = ea_file , ea_ok = False }

reportWarning name pos msg error=:{ea_file}
	# ea_file = ea_file <<< "Warning " <<< (newPosition name pos) <<< ":" <<< msg <<< '\n'
	= { error & ea_file = ea_file }
	
//****************************************************************************************
//	Type Helpers
//****************************************************************************************
makeAType :: !Type !TypeAttribute -> !AType
makeAType type attr = {	at_attribute = attr, at_type = type }

makeATypeVar :: !TypeVar !TypeAttribute -> !ATypeVar
makeATypeVar tv attr = {atv_variable = tv, atv_attribute = attr}

//----------------------------------------------------------------------------------------
// folding of a AType, depth first 
//----------------------------------------------------------------------------------------

class foldType t :: (Type  .st -> .st) (AType  .st -> .st) t .st -> .st

instance foldType [a] | foldType a where
	foldType on_type on_atype types st 
		= foldSt (foldType on_type on_atype) types st

instance foldType (a,b) | foldType a & foldType b where
	foldType on_type on_atype (x,y) st 
		= foldType on_type on_atype y (foldType on_type on_atype x st)

instance foldType Type where
	foldType on_type on_atype type st
		# st = fold_type type st
		= on_type type st 
	where
		fold_type (TA type_symb args) st = foldType on_type on_atype args st
		fold_type (TAS type_symb args _) st = foldType on_type on_atype args st
		fold_type (l --> r) st = foldType on_type on_atype (l,r) st
		fold_type (TArrow) st = st
		fold_type (TArrow1 t) st = foldType on_type on_atype t st
		fold_type (_ :@: args) st = foldType on_type on_atype args st
		fold_type (TB _) st = st
		fold_type (TFA tvs type) st = foldType on_type on_atype type st
		fold_type (GTV _) st = st
		fold_type (TV _) st = st		
		fold_type t st = abort "foldType: does not match\n" ---> ("type", t)

instance foldType AType where
	foldType on_type on_atype atype=:{at_type} st 
		# st = foldType on_type on_atype at_type st
		= on_atype atype st 

instance foldType TypeContext where
	foldType on_type on_atype {tc_types} st
		= foldType on_type on_atype tc_types st 

//----------------------------------------------------------------------------------------
// mapping of a AType, depth first 
//----------------------------------------------------------------------------------------
class mapTypeSt type :: 
	(Type  -> u:(.st -> u:(Type, .st))) 			// called on each type before recursion
	(AType -> u:(.st -> u:(AType, .st))) 		// called on each attributed type before recursion
	(Type  -> u:(.st -> u:(Type, .st))) 			// called on each type after recursion
	(AType -> u:(.st -> u:(AType, .st))) 		// called on each attributed type after recursion	
	type .st -> u:(type, .st)

mapTypeBeforeSt :: 
	(Type  -> u:(.st -> u:(Type, .st))) 			// called on each type before recursion
	(AType  -> u:(.st -> u:(AType, .st))) 		// called on each attributed type before recursion
	type .st -> u:(type, .st) | mapTypeSt type
mapTypeBeforeSt on_type_before on_atype_before type st
	= mapTypeSt on_type_before on_atype_before idSt idSt type st
	
mapTypeAfterSt :: 
	(Type  -> u:(.st -> u:(Type, .st))) 			// called on each type after recursion
	(AType  -> u:(.st -> u:(AType, .st))) 		// called on each attributed type after recursion
	type .st -> u:(type, .st) | mapTypeSt type
mapTypeAfterSt on_type_after on_atype_after type st
	= mapTypeSt idSt idSt on_type_after on_atype_after type st

instance mapTypeSt [a] | mapTypeSt a where
	mapTypeSt on_type_before on_atype_before on_type_after on_atype_after type st
		= mapSt (mapTypeSt on_type_before on_atype_before on_type_after on_atype_after) type st

instance mapTypeSt (a, b) | mapTypeSt a & mapTypeSt b where
	mapTypeSt on_type_before on_atype_before on_type_after on_atype_after (x, y) st
		#! (x1, st) = mapTypeSt on_type_before on_atype_before on_type_after on_atype_after x st
		#! (y1, st) = mapTypeSt on_type_before on_atype_before on_type_after on_atype_after y st
		= ((x1,y1), st)

instance mapTypeSt Type where
	mapTypeSt on_type_before on_atype_before on_type_after on_atype_after type st
		#! (type1, st) = on_type_before type st
		#! (type2, st) = map_type type1 st
		#! (type3, st) = on_type_after type2 st
		= (type3, st)
			//---> ("mapTypeSt Type", type, type1, type2, type3) 
	where
	
		map_type (TA type_symb_ident args) st 
			#! (args, st) = mapTypeSt on_type_before on_atype_before on_type_after on_atype_after args st
			= (TA type_symb_ident args, st)
		map_type (TAS type_symb_ident args strictness) st 
			#! (args, st) = mapTypeSt on_type_before on_atype_before on_type_after on_atype_after args st
			= (TAS type_symb_ident args strictness, st)
		map_type (l --> r) st 
			#! ((l,r), st) = mapTypeSt on_type_before on_atype_before on_type_after on_atype_after (l,r) st
			= (l --> r, st)
		map_type TArrow st 	= (TArrow, st)
		map_type (TArrow1 t) st 
			#! (t, st) = mapTypeSt on_type_before on_atype_before on_type_after on_atype_after t st
			= (TArrow1 t, st)
		map_type (cv :@: args) st 
			#! (args, st) = mapTypeSt on_type_before on_atype_before on_type_after on_atype_after args st
			= (cv :@: args, st)
		map_type t=:(TB _) st = (t, st)	
		map_type (TFA tvs type) st 
			#! (type, st) = mapTypeSt on_type_before on_atype_before on_type_after on_atype_after type st
			= (TFA tvs type, st)
		map_type t=:(GTV _) st = (t, st)	
		map_type t=:(TV _) st = (t, st)	
		map_type t st
			= abort "mapTypeSt: type does not match\n" ---> ("type", t)

instance mapTypeSt AType where
	mapTypeSt on_type_before on_atype_before on_type_after on_atype_after atype st
		#! (atype, st) = on_atype_before atype st 
		#! (at_type, st) = mapTypeSt on_type_before on_atype_before on_type_after on_atype_after atype.at_type st
		= on_atype_after {atype & at_type = at_type} st

instance mapTypeSt TypeContext where
	mapTypeSt on_type_before on_atype_before on_type_after on_atype_after tc=:{tc_types} st
		#! (tc_types, st) = mapTypeSt on_type_before on_atype_before on_type_after on_atype_after tc_types st
		= ({tc&tc_types=tc_types}, st)

		
//-----------------------------------------------------------------------
//-----------------------------------------------------------------------

// allocate fresh type variable
freshTypeVar :: !Ident  !*TypeVarHeap -> (!TypeVar, !*TypeVarHeap) 
freshTypeVar name th_vars 
	# (info_ptr, th_vars) = newPtr TVI_Empty th_vars
	= ({tv_name = name, tv_info_ptr = info_ptr}, th_vars)

// allocate fresh attribute variable
freshAttrVar :: !Ident !*AttrVarHeap -> (!AttributeVar, !*AttrVarHeap)
freshAttrVar name th_attrs
	# (info_ptr, th_attrs) = newPtr AVI_Empty th_attrs
	= ({av_name = name, av_info_ptr = info_ptr}, th_attrs)


// take a fresh copy of a SymbolType	  
freshSymbolType :: 
		!SymbolType			// symbol type to take fresh 
		!*TypeHeaps			// variable storage
	->  ( !SymbolType		// fresh symbol type
		, !*TypeHeaps		// variable storage
		) 
freshSymbolType st th=:{th_vars, th_attrs}
	#! (fresh_st_vars, th_vars) = mapSt subst_type_var st.st_vars th_vars
		//---> ("freshSymbolType called for", st)
	#! (fresh_st_attr_vars, th_attrs) = mapSt subst_attr_var st.st_attr_vars th_attrs
	#! th = {th & th_vars = th_vars, th_attrs = th_attrs}

	#! (fresh_st_args, th) 		= fresh_type st.st_args th
	#! (fresh_st_result, th) 	= fresh_type st.st_result th	
	#! (fresh_st_context, th) 	= fresh_type st.st_context th	
	#! (fresh_st_attr_env, th) 	= mapSt fresh_ineq st.st_attr_env th		
			
	#! fresh_st = 
		{ st
		& st_args = fresh_st_args
		, st_result = fresh_st_result
		, st_context = fresh_st_context
		, st_attr_env = fresh_st_attr_env
		, st_vars = fresh_st_vars
		, st_attr_vars = fresh_st_attr_vars 
		}

	#! th = clearSymbolType fresh_st th
	#! th = clearSymbolType st th

	#! th = assertSymbolType fresh_st th
	#! th = assertSymbolType st th

	= (fresh_st, th)
		//---> ("freshSymbolType returns", fresh_st)
where
	subst_type_var :: !TypeVar !*TypeVarHeap -> (!TypeVar, !*TypeVarHeap)
	subst_type_var tv=:{tv_info_ptr} th_vars
		# (new_ptr, th_vars) = newPtr TVI_Empty th_vars  
		= ({tv & tv_info_ptr=new_ptr}, writePtr tv_info_ptr (TVI_TypeVar new_ptr) th_vars)
	subst_attr_var :: !AttributeVar !*AttrVarHeap -> (!AttributeVar, !*AttrVarHeap)
	subst_attr_var av=:{av_info_ptr} th_attrs
		# (new_ptr, th_attrs) = newPtr AVI_Empty th_attrs  
		= ({av & av_info_ptr = new_ptr}, writePtr av_info_ptr (AVI_AttrVar new_ptr) th_attrs)			

	fresh_type :: type !*TypeHeaps -> (type, !*TypeHeaps) | mapTypeSt type 
	fresh_type t st = mapTypeBeforeSt on_type on_atype t st
		
	on_type (TV tv) th
		#! (tv, th) = on_type_var tv th	
		= (TV tv, th)		 			 
	on_type (GTV tv) th
		#! (tv, th) = on_type_var tv th	
		= (GTV tv, th)
	on_type (CV tv=:{tv_info_ptr} :@: args) th=:{th_vars}
		#! (tv, th) = on_type_var tv th	
		= (CV tv :@: args, th)
	on_type (TFA atvs type) th
		#! (fresh_atvs, th) = mapSt subst_atv atvs th
		// the variables in the type will be substituted by
		// the recursive call of mapType 
		= (TFA fresh_atvs type, th)
	where
		subst_atv atv=:{atv_variable, atv_attribute}  th=:{th_vars, th_attrs} 
			#! (atv_variable, th_vars) = subst_type_var atv_variable th_vars 
			# (atv_attribute, th_attrs) = subst_attr atv_attribute th_attrs
			=	( {atv & atv_variable = atv_variable, atv_attribute = atv_attribute}
				, {th & th_vars = th_vars, th_attrs = th_attrs})
		subst_attr (TA_Var av=:{av_info_ptr}) th_attrs
			# (av_info, th_attrs) = readPtr av_info_ptr th_attrs
			= case av_info of
				AVI_Empty
					# (av, th_attrs) = subst_attr_var av th_attrs
					-> (TA_Var av, th_attrs)
				AVI_AttrVar av_info_ptr
					-> (TA_Var {av & av_info_ptr = av_info_ptr}, th_attrs)						   
		subst_attr TA_Unique th_attrs 
			= (TA_Unique, th_attrs)
		subst_attr TA_Multi th_attrs 
			= (TA_Multi, th_attrs)
	on_type type th 
		= (type, th)
	
	on_atype atype=:{at_attribute=TA_Var av} th
		#! (fresh_av, th) = on_attr_var av th 
		= ({atype & at_attribute=TA_Var fresh_av}, th)
			//---> ("on_atype av", av, fresh_av) 			 
	on_atype atype th 
		= (atype, th)

	fresh_ineq :: !AttrInequality !*TypeHeaps -> (!AttrInequality, !*TypeHeaps)
	fresh_ineq 	ai=:{ai_demanded,ai_offered} th
		#! (ai_demanded, th) = on_attr_var ai_demanded th
		#! (ai_offered, th) = on_attr_var ai_offered th
		= ({ai & ai_demanded = ai_demanded, ai_offered = ai_offered}, th)
		
	on_type_var tv=:{tv_info_ptr} th=:{th_vars}
		#! (tv_info, th_vars) = readPtr tv_info_ptr th_vars
		#! tv = case tv_info of
			TVI_TypeVar new_ptr -> {tv & tv_info_ptr = new_ptr} 
			_ 					-> abort ("freshSymbolType, invalid tv_info\n" ---> tv_info)
		= (tv, {th & th_vars = th_vars}) 			 

	on_attr_var av=:{av_info_ptr} th=:{th_attrs}
		#! (av_info, th_attrs) = readPtr av_info_ptr th_attrs 
		#! av = case av_info of
			AVI_AttrVar new_ptr -> {av & av_info_ptr = new_ptr} 			 
					//---> ("fresh attr var", av.av_name, ptrToInt av_info_ptr, ptrToInt new_ptr)			
			_  -> abort ("freshSymbolType, invalid av_info\n" ---> av_info)
		= ( av, {th & th_attrs = th_attrs}) 			 

assertSymbolType :: !SymbolType !*TypeHeaps -> !*TypeHeaps
assertSymbolType {st_args, st_result, st_context} th
	= foldType on_type on_atype ((st_args, st_result), st_context) th	
where
	on_type :: !Type !*TypeHeaps -> !*TypeHeaps
	on_type (TV tv) th=:{th_vars}
		#! (tv_info, th_vars) = readPtr tv.tv_info_ptr th_vars
		#! th = {th & th_vars = th_vars}
		= case tv_info of
			TVI_Empty 	-> th
			_ 			-> (abort "TV  tv_info not empty\n") --->(tv, tv_info)	
	on_type (CV tv :@: _) th=:{th_vars}
		#! (tv_info, th_vars) = readPtr tv.tv_info_ptr th_vars
		#! th = {th & th_vars = th_vars}
		= case tv_info of
			TVI_Empty 	-> th
			_ 			-> (abort "CV tv_info not empty\n") --->(tv, tv_info)			
	on_type (TFA atvs type) th=:{th_attrs, th_vars}		
		#! th_attrs = foldSt on_av [av \\ {atv_attribute=TA_Var av} <- atvs] th_attrs
		#! th_vars = foldSt on_tv [atv_variable\\{atv_variable} <- atvs] th_vars
		= {th & th_attrs = th_attrs, th_vars = th_vars }
	where 		
		on_av av th_attrs 
			#! (av_info, th_attrs) = readPtr av.av_info_ptr th_attrs
			= case av_info of
			AVI_Empty	-> th_attrs
			_ ->  (abort "TFA av_info not empty\n") --->(av, av_info)
		on_tv tv th_vars
			#! (tv_info, th_vars) = readPtr tv.tv_info_ptr th_vars
			= case tv_info of
				TVI_Empty 	-> th_vars
				_ 			-> (abort "TFA tv_info not empty\n") --->(tv, tv_info)					
	on_type _ th = th
		
	on_atype :: !AType !*TypeHeaps -> !*TypeHeaps
	on_atype {at_attribute=TA_Var av} th=:{th_attrs}
		#! (av_info, th_attrs) = readPtr av.av_info_ptr th_attrs
		#! th = {th & th_attrs = th_attrs}
		= case av_info of
			AVI_Empty	-> th
			_ ->  (abort "av_info not empty\n") --->(av, av_info)
	on_atype _ th = th

				
// build curried type out of SymbolType
buildCurriedType :: ![AType] !AType !TypeAttribute ![AttrInequality] ![AttributeVar] !String !Int !*AttrVarHeap 
	-> (!AType, ![AttrInequality], ![AttributeVar], !Int, !*AttrVarHeap)
buildCurriedType [] type cum_attr attr_env attr_vars attr_var_name attr_store th_attrs 
	= (type, attr_env, attr_vars, attr_store, th_attrs)
buildCurriedType [at=:{at_attribute}] type cum_attr attr_env attr_vars attr_var_name attr_store th_attrs
	# atype = makeAType (at --> type) cum_attr
	= (atype, attr_env, attr_vars, attr_store, th_attrs)
buildCurriedType [at=:{at_attribute}:ats] type cum_attr attr_env attr_vars attr_var_name attr_store th_attrs
	# (next_cum_attr, new_attr_env, attr_vars, attr_store, th_attrs) = combine_attributes at_attribute cum_attr attr_env attr_vars attr_store th_attrs
	  (res_type, attr_env, attr_vars, attr_store, th_attrs) = buildCurriedType ats type next_cum_attr attr_env attr_vars attr_var_name attr_store th_attrs
	# atype = makeAType (at --> res_type) cum_attr  
	= (atype, attr_env, attr_vars, attr_store, th_attrs)
where
	combine_attributes TA_Unique cum_attr attr_env attr_vars attr_store th_attrs
		= (TA_Unique, attr_env, attr_vars, attr_store, th_attrs)
	combine_attributes (TA_Var attr_var) (TA_Var cum_attr_var) attr_env attr_vars attr_store th_attrs
		#! (new_attr_var, th_attrs) 
			= freshAttrVar (makeIdent (attr_var_name +++ toString attr_store)) th_attrs	
		# attr_env = 
			[	{ ai_demanded = cum_attr_var,ai_offered = new_attr_var }
			, 	{ ai_demanded = attr_var, ai_offered = new_attr_var }
			: 	attr_env
			]
		= (	TA_Var new_attr_var, attr_env, [new_attr_var:attr_vars], inc attr_store, th_attrs)
	combine_attributes (TA_Var _) cum_attr attr_env attr_vars attr_store th_attrs
		= (cum_attr, attr_env, attr_vars, attr_store, th_attrs)
	combine_attributes _ (TA_Var cum_attr_var) attr_env attr_vars attr_store th_attrs
		#! (new_attr_var, th_attrs) 
			= freshAttrVar (makeIdent (attr_var_name +++ toString attr_store)) th_attrs		
		# attr_env = [	{ ai_demanded = cum_attr_var,ai_offered = new_attr_var }: attr_env]
		= (	TA_Var new_attr_var, attr_env, [new_attr_var:attr_vars], inc attr_store, th_attrs)
	combine_attributes _ cum_attr attr_env attr_vars attr_store th_attrs
		= (cum_attr, attr_env, attr_vars, attr_store, th_attrs)

// Build curried type out of symbol type.
// Starts with TA_Multi cumulative attribute.
// This is the weakest requirement,
// since we do not know how the generic argument will be used
// in the instance functions. It depends on the instance type. 
curryGenericArgType :: !SymbolType !String !*TypeHeaps 
	-> (!SymbolType, !*TypeHeaps)
curryGenericArgType  st=:{st_args, st_result, st_attr_env, st_attr_vars} attr_var_name th=:{th_attrs}
		
	#! (atype, attr_env, attr_vars, attr_store, th_attrs) 
		= buildCurriedType st_args st_result TA_Multi st_attr_env st_attr_vars attr_var_name 1 th_attrs

	# curried_st = 
		{ st 
		& st_args = []
		, st_arity = 0
		, st_result = atype
		, st_attr_env = attr_env
		, st_attr_vars = attr_vars
		}
	= (curried_st, {th & th_attrs = th_attrs})	
		//---> ("curryGenericArgType", st, curried_st)


curryGenericArgType1 :: !SymbolType !String !*TypeHeaps 
	-> (!SymbolType, !*TypeHeaps)
curryGenericArgType1  st=:{st_args, st_result, st_attr_env, st_attr_vars} attr_var_name th=:{th_attrs}
		
	# (atype, attr_vars, av_num, th_attrs) = curry st_args st_result 1 th_attrs

	# curried_st = 
		{ st 
		& st_args = []
		, st_arity = 0
		, st_result = atype
		, st_attr_vars = attr_vars
		}
	= (curried_st, {th & th_attrs = th_attrs})	
		//---> ("curryGenericArgType", st, curried_st)
where
	// outermost closure gets TA_Multi attribute
	curry [] res av_num th_attrs
		= (res, [], av_num, th_attrs)
	curry [arg:args] res av_num th_attrs
		#! (res, avs, av_num, th_attrs) = curry1 args res av_num th_attrs
 		#! atype = makeAType (arg --> res) TA_Multi
		= (atype, avs, av_num, th_attrs)
		
	// inner closures get TA_Var attributes	
	curry1 [] res av_num th_attrs
		= (res, [], av_num, th_attrs)	 	
	curry1 [arg:args] res av_num th_attrs
		#! (res, avs, av_num, th_attrs) = curry1 args res av_num th_attrs
		#! (av, th_attrs) = freshAttrVar (makeIdent (attr_var_name +++ toString av_num)) th_attrs
 		#! atype = makeAType (arg --> res) (TA_Var av)
		= (atype, [av:avs], inc av_num, th_attrs)

//----------------------------------------------------------------------------------------
// write empty value in the variable heaps 
//----------------------------------------------------------------------------------------

clearType t th 
	= foldType clear_type clear_atype t th
where

	clear_type (TV tv) th = clear_type_var tv th	
	clear_type (GTV tv) th = clear_type_var tv th
	clear_type (CV tv :@: _) th = clear_type_var tv th
	clear_type (TFA atvs type) th
		#! th = foldSt clear_attr [atv_attribute \\ {atv_attribute} <- atvs] th
		#! th = foldSt clear_type_var [atv_variable \\ {atv_variable} <- atvs] th
		= th
		 	
	clear_type _ th = th

	clear_atype {at_attribute} th 
		= clear_attr at_attribute th

	clear_attr (TA_Var av) th = clear_attr_var av th
	clear_attr (TA_RootVar av) th = clear_attr_var av th
	clear_attr _ th = th
		
	clear_type_var {tv_info_ptr} th=:{th_vars} 
		= {th & th_vars = writePtr tv_info_ptr TVI_Empty th_vars} 
	clear_attr_var {av_info_ptr} th=:{th_attrs} 
		= {th & th_attrs = writePtr av_info_ptr AVI_Empty th_attrs} 

clearSymbolType st th
	// clears not only st_vars and st_attrs, but also TFA variables
	= clearType ((st.st_result, st.st_args), st.st_context) th

//----------------------------------------------------------------------------------------
// collect variables
//----------------------------------------------------------------------------------------

collectTypeVarsAndAttrVars ::
		!type 
		!*TypeHeaps
	-> 	(![TypeVar]
		,![AttributeVar]
		,!*TypeHeaps
		)
	| foldType type	 
collectTypeVarsAndAttrVars type th
	#! th = clearType type th
	#! (tvs, avs, th) = foldType collect_type_var collect_attr type ([], [], th)
	#! th = clearType type th
	= (tvs, avs, th)
where
	collect_type_var (TV tv) st = add_type_var tv st
	collect_type_var (GTV tv) st = add_type_var tv st
	collect_type_var (CV tv :@: _) st = add_type_var tv st
	collect_type_var (TFA forall_atvs type) (tvs, avs, th_vars) 
		#! forall_tvs = [atv_variable\\{atv_variable}<-forall_atvs]
		#! forall_avs = [av \\ {atv_attribute=TA_Var av}<-forall_atvs]
		= (tvs -- forall_tvs, avs -- forall_avs, th_vars)
				//---> ("collectTypeVarsAndAttrVars TFA", tvs, forall_tvs, tvs -- forall_tvs)
	collect_type_var t st = st
		
	add_type_var tv (tvs, avs, th=:{th_vars})
		# (was_used, th_vars) = markTypeVarUsed tv th_vars
		# th = {th & th_vars = th_vars}
		| was_used 
			= (tvs, avs, th)
				//---> ("collectTypeVarsAndAttrVars: TV was used", tv)
			= ([tv:tvs], avs, th)
				//---> ("collectTypeVarsAndAttrVars: TV was not used", tv)
	
	collect_attr {at_attribute} st = collect_attr_var at_attribute st
	
	collect_attr_var (TA_Var av) st = add_attr_var av st
	collect_attr_var (TA_RootVar av) st = add_attr_var av st
	collect_attr_var _ st = st
				
	add_attr_var av (atvs, avs, th=:{th_attrs})		
		# (was_used, th_attrs) = markAttrVarUsed av th_attrs
		# th = {th & th_attrs = th_attrs}
		| was_used 
			= (atvs, avs, th)
			= (atvs, [av:avs], th)

collectTypeVars type th
	# (tvs, _, th) = collectTypeVarsAndAttrVars type th
	= (tvs, th)
collectAttrVars type th 
	# (_, avs, th) = collectTypeVarsAndAttrVars type th
	= (avs, th)

collectAttrsOfTypeVars :: ![TypeVar] type !*TypeHeaps -> (![ATypeVar], !*TypeHeaps) | foldType type
collectAttrsOfTypeVars tvs type th
	#! (th=:{th_vars}) = clearType type th
		//---> ("collectAttrsOfTypeVars called for", tvs)
	
	# th_vars = foldSt (\{tv_info_ptr} h->writePtr tv_info_ptr TVI_Used h) tvs th_vars 
	
	#! (atvs, th_vars) = foldType on_type on_atype type ([], th_vars)

	# th_vars = foldSt (\{tv_info_ptr} h->writePtr tv_info_ptr TVI_Empty h) tvs th_vars 

 	#! th = clearType type {th & th_vars= th_vars}
	= (atvs, th)
		//---> ("collectAttrsOfTypeVars returns", atvs)
where
	on_type type st = st

	on_atype {at_type=TV tv, at_attribute} st = on_type_var tv at_attribute st				 	 
	on_atype {at_type=GTV tv, at_attribute} st = on_type_var tv at_attribute st				 	 
	on_atype {at_type=(CV tv :@: _), at_attribute} st = on_type_var tv at_attribute st
	//??? TFA -- seems that it is not needed
 	on_atype _ st = st 	

	on_type_var tv=:{tv_info_ptr} attr (atvs, th_vars)	
	 	#! (tvi, th_vars) = readPtr tv_info_ptr th_vars
	 	= case tvi of
	 		TVI_Used
	 			# th_vars = writePtr tv_info_ptr TVI_Empty th_vars
	 			-> ([makeATypeVar tv attr : atvs], th_vars)
	 		TVI_Empty 
	 			-> (atvs, th_vars) 

collectAttrsOfTypeVarsInSymbolType tvs {st_args, st_result} th
 	= collectAttrsOfTypeVars tvs [st_result:st_args] th  

// marks empty type vars used,
// returns whether the type var was already used	 	  
markTypeVarUsed tv=:{tv_info_ptr} th_vars
	# (tv_info, th_vars) = readPtr tv_info_ptr th_vars
	= case tv_info of
		TVI_Empty -> (False, writePtr tv_info_ptr TVI_Used th_vars)
		TVI_Used  -> (True, th_vars)
		_ -> (abort "markTypeVarUsed: wrong tv_info ") ---> (tv, tv_info)

// marks empty attr vars  used
// returns whether the attr var was already used		
markAttrVarUsed {av_info_ptr} th_attrs
	# (av_info, th_attrs) = readPtr av_info_ptr th_attrs
	= case av_info of
		AVI_Empty -> (False, writePtr av_info_ptr AVI_Used th_attrs)
		AVI_Used  -> (True, th_attrs)
		

simplifyTypeApp :: !Type ![AType] -> !Type
simplifyTypeApp (TA type_cons=:{type_arity} cons_args) type_args
	= TA { type_cons & type_arity = type_arity + length type_args } (cons_args ++ type_args)
simplifyTypeApp (TAS type_cons=:{type_arity} cons_args strictness) type_args
	= TAS { type_cons & type_arity = type_arity + length type_args } (cons_args ++ type_args) strictness
simplifyTypeApp (CV tv :@: type_args1) type_args2 = CV tv :@: (type_args1 ++ type_args2)
simplifyTypeApp TArrow [type1, type2] = type1 --> type2
simplifyTypeApp TArrow [type] = TArrow1 type
simplifyTypeApp (TArrow1 type1) [type2] = type1 --> type2
simplifyTypeApp (TV tv) type_args = CV tv :@: type_args
simplifyTypeApp (TB _) type_args = TE
simplifyTypeApp (TArrow1 _) type_args = TE
		
//----------------------------------------------------------------------------------------
// substitutions
//----------------------------------------------------------------------------------------

//
// Uninitialized variables are not substituted, but left intact
//
// This behaviour is needed for kind indexing generic types,
// where generic variables are substituted and non-generic variables
// are not
//
applySubst :: !type !*TypeHeaps -> (!type, !*TypeHeaps) | mapTypeSt type 
applySubst type th
	= mapTypeAfterSt on_type on_atype type th
where
	on_type type=:(TV {tv_info_ptr}) th=:{th_vars}
		# (tv_info, th_vars) = readPtr tv_info_ptr th_vars 
		# th = {th & th_vars = th_vars}
		= case tv_info of
			TVI_Type t -> (t, th)
			TVI_Empty -> (type, th) 
	on_type (GTV _) th 
		= abort "GTV"
	on_type type=:(CV {tv_info_ptr} :@: args) th=:{th_vars}
		# (tv_info, th_vars) = readPtr tv_info_ptr th_vars 
		# th = {th & th_vars = th_vars}
		= case tv_info of
			TVI_Type t -> (simplifyTypeApp t args, th)
			TVI_Empty  -> (type, th) 

	//on_type type=:(TFA atvs t) th=:{th_vars}
	//	= abort "applySubst TFA" 

	on_type type th
		= (type, th)

	on_atype atype=:{at_attribute} th=:{th_attrs}	
		# (at_attribute, th_attrs) = subst_attr at_attribute th_attrs
		= ({atype & at_attribute = at_attribute}, {th & th_attrs = th_attrs})

	subst_attr attr=:(TA_Var {av_info_ptr}) th_attrs
		# (av_info, th_attrs) = readPtr av_info_ptr th_attrs 
		= case av_info of
			AVI_Attr a -> (a, th_attrs)
			AVI_Empty -> (attr, th_attrs) 
	subst_attr TA_Multi th = (TA_Multi, th)
	subst_attr TA_Unique th = (TA_Unique, th)

applySubstInSymbolType st=:{st_args, st_result, st_attr_env, st_context} th
	#! (new_st_args, th) 	= applySubst st.st_args th
	#! (new_st_result, th) 	= applySubst st.st_result th	
	#! (new_st_context, th) 	= applySubst st.st_context th	
	#! (new_st_attr_env, th)	= mapSt subst_ineq st.st_attr_env th		
	
	#! th = clear_type_vars st.st_vars th
	#! th = clear_attr_vars st.st_attr_vars th
		
	#! (new_st_vars, new_st_attr_vars, th) 
		= collectTypeVarsAndAttrVars ((new_st_args,new_st_result), new_st_context) th

	#! new_st = 
		{ st
		& st_args = new_st_args
		, st_result = new_st_result
		, st_context = new_st_context
		, st_attr_env = new_st_attr_env
		, st_vars = new_st_vars
		, st_attr_vars = new_st_attr_vars 
		}
		
	#! th = clearSymbolType st th	

	#! th = assertSymbolType new_st th
	#! th = assertSymbolType st th
		
	= (new_st, th)
		//---> ("applySubstInSymbolType", new_st)
where 
	subst_ineq 	ai=:{ai_demanded,ai_offered} th
		# (ai_demanded, th) = subst_attr_var ai_demanded th
		# (ai_offered, th) = subst_attr_var ai_offered th
		= ({ai & ai_demanded = ai_demanded, ai_offered = ai_offered}, th)
	subst_attr_var  av=:{av_info_ptr} th=:{th_attrs}
		# (av_info, th_attrs) = readPtr av_info_ptr th_attrs
		# th = {th & th_attrs = th_attrs}
		= case av_info of
			AVI_Attr (TA_Var av1) -> (av1, th)
			AVI_Attr _ -> (av, th)
			AVI_Empty -> (av, th)
	clear_type_vars tvs th=:{th_vars}
		#! th_vars = foldSt (\{tv_info_ptr} h->writePtr tv_info_ptr TVI_Empty h) tvs th_vars
		= {th & th_vars = th_vars}
	clear_attr_vars avs th=:{th_attrs}
		#! th_attrs = foldSt (\{av_info_ptr} h->writePtr av_info_ptr AVI_Empty h) avs th_attrs
		= {th & th_attrs = th_attrs}				

//****************************************************************************************
//	Function Helpers
//****************************************************************************************

makeFunction :: !Ident !Index !Index ![FreeVar] !Expression !(Optional SymbolType) !Index !Position
	-> FunDef
makeFunction ident fun_index group_index arg_vars body_expr opt_sym_type main_dcl_module_n fun_pos
	
	#! (arg_vars, local_vars, free_vars) = collectVars body_expr arg_vars	
	| not (isEmpty free_vars)
		= abort "makeFunction: free_vars is not empty\n"  
				
	=	{ fun_symb = ident
		, fun_arity = length arg_vars
		, fun_priority = NoPrio
		, fun_body = TransformedBody {tb_args = arg_vars, tb_rhs = body_expr }
		, fun_type = opt_sym_type
		, fun_pos = fun_pos
		, fun_kind  = FK_Function cNameNotLocationDependent
		, fun_lifted = 0
		, fun_info = 
			{ fi_calls = collectCalls main_dcl_module_n body_expr
			, fi_group_index = group_index
			, fi_def_level = NotALevel
			, fi_free_vars =  []
			, fi_local_vars = local_vars
			, fi_dynamics = []
			, fi_properties = 0
			}	
		}
		//---> ("makeFunction", ident, fun_index)

// build function and
buildFunAndGroup :: 
		!Ident ![FreeVar] !Expression !(Optional SymbolType) !Index !Position 
		!FunsAndGroups
	-> 
		(!DefinedSymbol, FunsAndGroups)
buildFunAndGroup 
		ident arg_vars body_expr opt_sym_type main_dcl_module_n fun_pos 
		(fun_index, group_index, funs, groups)
	# fun = makeFunction ident fun_index group_index arg_vars body_expr opt_sym_type main_dcl_module_n fun_pos	
	# group = {group_members = [fun_index]}
	# def_sym = {ds_ident=ident, ds_arity=fun.fun_arity, ds_index=fun_index}
	= (def_sym, (inc fun_index, inc group_index, [fun:funs], [group:groups]))

buildUndefFunAndGroup ident st main_dcl_module_n fun_pos fun_info predefs heaps
	#! arg_var_names = [ "x" +++ toString i \\ i <- [1 .. st.st_arity]]
	#! (arg_vars,heaps) = mapSt build_free_var arg_var_names  heaps
	#! (expr, heaps) = buildPredefFunApp PD_undef [] predefs heaps
	= buildFunAndGroup ident arg_vars expr (Yes st) main_dcl_module_n fun_pos fun_info		
where
	build_free_var :: !String !*Heaps -> (!FreeVar, !*Heaps)
	build_free_var name heaps=:{hp_var_heap}
		# (var_info_ptr, hp_var_heap) = newPtr VI_Empty hp_var_heap
		# var_name = { id_name = name, id_info = nilPtr }
		# free_var = { fv_def_level = NotALevel, fv_count = 0, fv_info_ptr = var_info_ptr, fv_name = var_name}
		= (free_var, {heaps & hp_var_heap = hp_var_heap})
		
/*
buildIdFunction :: 
		!DefinedSymbol 			// the desired function name and index
		Int 					// group index
		!Index 					// current module number
		!*Heaps					// heaps
	->	( !FunDef				// created function definition
		, !*Heaps				// heaps
		)
buildIdFunction def_sym group_index gs_main_dcl_module_n heaps
	# (arg_expr, arg_var, heaps) = buildVarExpr "x" heaps 
	# fun_def = makeFunction def_sym group_index [arg_var] arg_expr No [] gs_main_dcl_module_n NoPos	
	= (fun_def, heaps)
*/

/*
buildUndefFunction :: 
		!DefinedSymbol 			// the desired function name and index
		!Int 					// group index
		!PredefinedSymbols 		// predefined symbols
		!Index 					// current module number
		!*Heaps					// heaps
	-> 	( !FunDef				// created function definition
		, !*Heaps				// heaps
		)
buildUndefFunction def_sym group_index predefs gs_main_dcl_module_n heaps
	# names = [ "x" +++ toString i \\ i <- [1 .. def_sym.ds_arity]]
	# (arg_vars, heaps) = mapSt build_free_var names heaps
	# (body_expr, heaps) = buildUndefFunApp [] predefs heaps
	//# (body_expr, heaps) = buildUNIT predefs heaps
	# fun_def = makeFunction def_sym group_index arg_vars body_expr No [] gs_main_dcl_module_n NoPos	
	= (fun_def, heaps)
where
	build_free_var :: !String !*Heaps -> (!FreeVar, !*Heaps)
	build_free_var name heaps=:{hp_var_heap}
		# (var_info_ptr, hp_var_heap) = newPtr VI_Empty hp_var_heap
		# var_name = { id_name = name, id_info = nilPtr }
		# free_var = { fv_def_level = NotALevel, fv_count = 0, fv_info_ptr = var_info_ptr, fv_name = var_name}
		= (free_var, {heaps & hp_var_heap = hp_var_heap})
*/
	
//****************************************************************************************
//	Expr Helpers
//****************************************************************************************

//========================================================================================
// Primitive expressions
//========================================================================================

makeIntExpr :: Int -> Expression
makeIntExpr value = BasicExpr (BVI (toString value))

makeStringExpr :: String !PredefinedSymbols -> Expression
makeStringExpr str predefs
	#! {pds_module, pds_def} = predefs.[PD_StringType]
	#! pds_ident = predefined_idents.[PD_StringType]
	#! type_symb = MakeTypeSymbIdent { glob_module = pds_module, glob_object = pds_def } pds_ident 0
	=  BasicExpr (BVS str)
	
/*	
makeListExpr :: [Expression] !PredefinedSymbols !*Heaps -> (Expression, !*Heaps)
makeListExpr [] predefs heaps
	= buildPredefConsApp PD_NilSymbol [] predefs heaps
makeListExpr [expr:exprs] predefs heaps 
	# (list_expr, heaps) = makeListExpr exprs predefs heaps 
	= buildPredefConsApp PD_ConsSymbol [expr, list_expr] predefs heaps
*/

buildConsApp :: !Index DefinedSymbol ![Expression] !*Heaps 
	-> (!Expression, !*Heaps) 
buildConsApp cons_mod {ds_ident, ds_index, ds_arity} arg_exprs heaps=:{hp_expression_heap}
	# (expr_info_ptr, hp_expression_heap) = newPtr EI_Empty hp_expression_heap
	# cons_glob = {glob_module = cons_mod, glob_object = ds_index}
	# expr = App {
		app_symb = {
			symb_name = ds_ident, 
			symb_kind = SK_Constructor cons_glob
			}, 
		app_args = arg_exprs, 
		app_info_ptr = expr_info_ptr} 	
	# heaps = { heaps & hp_expression_heap = hp_expression_heap } 
	= (expr, heaps)	

buildFunApp :: !Index !DefinedSymbol ![Expression] !*Heaps 
	-> (!Expression, !*Heaps) 
buildFunApp fun_mod {ds_ident, ds_index} arg_exprs heaps=:{hp_expression_heap}
	# (expr_info_ptr, hp_expression_heap) = newPtr EI_Empty hp_expression_heap
	# fun_glob = {glob_module = fun_mod, glob_object = ds_index}
	# expr = App {
		app_symb = {
			symb_name = ds_ident, 
			symb_kind = SK_Function fun_glob
			}, 
		app_args = arg_exprs, 
		app_info_ptr = expr_info_ptr} 	
	# heaps = { heaps & hp_expression_heap = hp_expression_heap } 
	= (expr, heaps)	

buildPredefFunApp :: !Int [Expression] !PredefinedSymbols !*Heaps
	-> (!Expression, !*Heaps)
buildPredefFunApp predef_index args predefs heaps
	# {pds_module, pds_def} = predefs.[predef_index]
	# fun_ds = 
		{ ds_index = pds_def
		, ds_ident = predefined_idents.[predef_index]
		, ds_arity = 0 // not used
		}
 	= buildFunApp pds_module fun_ds args heaps

buildGenericApp :: !Index !Index !Ident !TypeKind ![Expression] !*Heaps
	-> (!Expression, !*Heaps)
buildGenericApp gen_module gen_index gen_name kind arg_exprs heaps=:{hp_expression_heap}
	# (expr_info_ptr, hp_expression_heap) = newPtr EI_Empty hp_expression_heap
	# glob_index = {glob_module = gen_module, glob_object = gen_index}
	# expr = App {
		app_symb = {
			symb_name = gen_name, 
			symb_kind = SK_Generic glob_index kind
		}, 
		app_args = arg_exprs, 
		app_info_ptr = expr_info_ptr} 	
	# heaps = { heaps & hp_expression_heap = hp_expression_heap } 
	= (expr, heaps)	

buildPredefConsApp :: !Int [Expression] !PredefinedSymbols !*Heaps
	-> (!Expression, !*Heaps)
buildPredefConsApp predef_index args predefs heaps=:{hp_expression_heap}
	# {pds_module, pds_def} = predefs.[predef_index]
	# pds_ident = predefined_idents.[predef_index]
	# global_index = {glob_module = pds_module, glob_object = pds_def}
	# symb_ident = 
		{ symb_name = pds_ident 
		, symb_kind = SK_Constructor global_index
		}
	# (expr_info_ptr, hp_expression_heap) = newPtr EI_Empty hp_expression_heap
	# app = App {app_symb = symb_ident, app_args = args, app_info_ptr = expr_info_ptr} 
	= (app, {heaps & hp_expression_heap = hp_expression_heap})

buildPredefConsPattern :: !Int ![FreeVar] !Expression !PredefinedSymbols
	-> AlgebraicPattern
buildPredefConsPattern predef_index vars expr predefs
	# {pds_module, pds_def} = predefs.[predef_index]
	# pds_ident = predefined_idents.[predef_index]
	# cons_def_symbol = {
		ds_ident = pds_ident,
		ds_arity = length vars,
		ds_index = pds_def
		}
	# pattern = {
		ap_symbol = {glob_module = pds_module, glob_object = cons_def_symbol},
		ap_vars = vars,
		ap_expr = expr,
		ap_position = NoPos		
		}
	= pattern

buildCaseExpr :: Expression CasePatterns !*Heaps 
	-> (!Expression, !*Heaps)
buildCaseExpr case_arg case_alts heaps=:{hp_expression_heap}	
	# (expr_info_ptr, hp_expression_heap) = newPtr EI_Empty hp_expression_heap
	# expr = Case 
		{ case_expr = case_arg
		, case_guards = case_alts
		, case_default = No
		, case_ident = No
		, case_info_ptr = expr_info_ptr
		, case_explicit = False
		, case_default_pos = NoPos 
		}
	# heaps = { heaps & hp_expression_heap = hp_expression_heap}	
	= (expr, heaps)

buildRecordSelectionExpr :: !Expression !Index !PredefinedSymbols -> Expression
buildRecordSelectionExpr record_expr predef_field predefs 
	# {pds_module, pds_def} = predefs . [predef_field]
	# pds_ident = predefined_idents . [predef_field]
	# selector = { 
		glob_module = pds_module, 
		glob_object = {ds_ident = pds_ident, ds_index = pds_def, ds_arity = 1}}
	= Selection NormalSelector record_expr [RecordSelection selector 1]

//=============================================================================
// variables
//=============================================================================

// build a new variable and an expression associated with it
buildVarExpr :: 
		!String 			// variable name
		!*Heaps	
	-> (!Expression 		// variable expression
		, !FreeVar 			// variable
		, !*Heaps
		)
buildVarExpr name heaps=:{hp_var_heap, hp_expression_heap} 
	# (expr_info_ptr, hp_expression_heap) = newPtr EI_Empty hp_expression_heap
	# (var_info_ptr, hp_var_heap) = newPtr VI_Empty hp_var_heap
	# var_name = makeIdent name
	# var = Var {var_name = var_name, var_expr_ptr = expr_info_ptr, var_info_ptr = var_info_ptr } 
	# hp_var_heap = writePtr var_info_ptr (VI_Expression var) hp_var_heap
	# heaps = { heaps & hp_var_heap = hp_var_heap, hp_expression_heap = hp_expression_heap }
	# fv = {fv_count = 1/* if 0, trans crashes*/, fv_name = var_name, fv_info_ptr = var_info_ptr, fv_def_level = NotALevel} 
	= (var, fv, heaps)

buildVarExprs [] heaps = ([], [], heaps)
buildVarExprs [x:xs] heaps
	# (y, z, heaps) = buildVarExpr x heaps
	# (ys, zs, heaps) = buildVarExprs xs heaps
	= ([y:ys], [z:zs], heaps)
	 
//=============================================================================
// recursion over expressions
//=============================================================================

//-----------------------------------------------------------------------------
// fold expression applies a function to each node of an expression
// recursively:
// first apply the function, then recurse
//-----------------------------------------------------------------------------
foldExpr :: 
		(Expression -> .st -> .st)  	// function to apply at each node
		Expression 						// expression to run throuh
		.st 							// state
	-> 
		.st								// updated state 
foldExpr f expr=:(App {app_args}) st 
	# st = f expr st
	= foldSt (foldExpr f) app_args st
foldExpr f expr1=:(expr@exprs) st
	# st = f expr st	
	= foldSt (foldExpr f) [expr:exprs] st	
foldExpr f expr=:(Let {let_lazy_binds, let_strict_binds, let_expr}) st
	# st = f expr st
	# st = foldSt (fold_let_binds f) let_strict_binds st 
	# st = foldSt (fold_let_binds f) let_lazy_binds st 
	= foldExpr f let_expr st 
where
	fold_let_binds f {lb_src} st = foldExpr f lb_src st 
foldExpr f expr=:(Case {case_expr,case_guards,case_default}) st
	# st = f expr st
	# st = foldExpr f case_expr st
	# st = fold_guards f case_guards st 
	# st = foldOptional (foldExpr f) case_default st
	= st
where
	fold_guards f (AlgebraicPatterns gi aps) st = foldSt (foldExpr f) [ap_expr\\{ap_expr}<-aps] st
	fold_guards f (BasicPatterns gi bps) st = foldSt (foldExpr f) [bp_expr\\{bp_expr}<-bps] st
	fold_guards f (DynamicPatterns dps) st = foldSt (foldExpr f) [dp_rhs\\{dp_rhs}<-dps] st
	fold_guards f NoPattern st = st
foldExpr f expr=:(Update expr1 sels expr2) st
	# st = f expr st
	# st = foldExpr f expr1 st 
	# st = foldSt (fold_sel f) sels st 
	# st = foldExpr f expr2 st 
	= st
where
	fold_sel f (RecordSelection _ _) st = st
	fold_sel f (ArraySelection _ _ expr) st = foldExpr f expr st
	fold_sel f (DictionarySelection _ _ _ expr) st = foldExpr f expr st
foldExpr f expr=:(RecordUpdate _ expr1 binds) st
	# st = f expr st
	# st = foldExpr f expr1 st 
	# st = foldSt (foldExpr f) [bind_src\\{bind_src}<-binds] st
	= st
foldExpr f expr=:(TupleSelect _ _ expr1) st 
	# st = f expr st
	= foldExpr f expr1 st
foldExpr f expr=:(Conditional {if_cond,if_then,if_else}) st
	# st = f expr st
	# st = foldExpr f if_cond st	
	# st = foldExpr f if_then st	
	# st = foldOptional (foldExpr f) if_else st	
	= st
foldExpr f expr=:(MatchExpr _ expr1) st 
	# st = f expr st
	= foldExpr f expr1 st
foldExpr f expr=:(DynamicExpr {dyn_expr}) st 
	# st = f expr st
	= foldExpr f dyn_expr st
foldExpr f expr st 
	= f expr st

//-----------------------------------------------------------------------------
// map expression applies a function to each node of an expression
// recursively:
// first recurse, then apply the function
//-----------------------------------------------------------------------------
mapExprSt :: 
		!(Expression -> w:st -> u:(Expression, w:st)) 
		!Expression 
		w:st
	->  
	v:	( Expression
		, w:st
		)
	, [v<=w,u<=v]	
mapExprSt f (App app=:{app_args}) st
		# (app_args, st) = mapSt (mapExprSt f) app_args st
		= f (App { app & app_args = app_args }) st
				
mapExprSt f (Let lad=:{let_lazy_binds, let_strict_binds, let_expr}) st
	# (let_lazy_binds, st) = mapSt map_bind let_lazy_binds st
	# (let_strict_binds, st) = mapSt map_bind let_strict_binds st
	# (let_expr, st) = mapExprSt f let_expr st
	# lad =
		{ 	lad 
		& 	let_expr = let_expr
		, 	let_lazy_binds = let_lazy_binds
		, 	let_strict_binds = let_strict_binds
		}
	= f (Let lad) st
where
	map_bind b=:{lb_src} st
		# (lb_src, st) = mapExprSt f lb_src st
		= ({b & lb_src = lb_src}, st)

mapExprSt f (Selection a expr b) st
	# (expr, st) = mapExprSt f expr st
	= f (Selection a expr b) st
	
mapExprSt f (Update e1 x e2) st
	# (e1, st) = mapExprSt f e1 st
	# (e2, st) = mapExprSt f e2 st
	= f (Update e1 x e2) st

mapExprSt f (RecordUpdate x expr binds) st
	# (expr, st) = mapExprSt f expr st
	# (binds, st) = mapSt map_bind binds st
	= f (RecordUpdate x expr binds) st
where
	map_bind b=:{bind_src} st
		# (bind_dst, st) = mapExprSt f bind_src st
		= ({b & bind_src = bind_src}, st)	

mapExprSt f (TupleSelect x y expr) st
	# (expr, st) = mapExprSt f expr st
	= f (TupleSelect x y expr) st
	
mapExprSt f (Conditional cond=:{if_cond, if_then, if_else}) st
	# (if_cond, st) = mapExprSt f if_cond st
	# (if_then, st) = mapExprSt f if_then st
	# (if_else, st) = mapOptionalSt (mapExprSt f) if_else st 
/*
	# (if_else, st) = case if_else of
		(Yes x) 
			# (x, st) = mapExprSt f x st
			-> (Yes x, st)
		No  -> (No, st)	
*/
	= f (Conditional {cond & if_cond = if_cond, if_then = if_then, if_else = if_else}) st
		
mapExprSt f (MatchExpr y expr) st
	# (expr, st) = mapExprSt f expr st
	= f (MatchExpr y expr) st

mapExprSt f (DynamicExpr dyn=:{dyn_expr}) st
	# (dyn_expr, st) = mapExprSt f dyn_expr st
	= f (DynamicExpr {dyn& dyn_expr = dyn_expr}) st 

mapExprSt f (Case c=:{case_expr, case_guards, case_default=case_default}) st
	# (case_expr, st) = mapExprSt f case_expr st
	# (case_guards, st) = map_patterns case_guards st
	# (case_default, st) = case case_default of 
		(Yes x) 
			# (x, st) = mapExprSt f x st
			-> (Yes x, st)
		No  -> (No, st)	
	# new_case = {c & case_expr=case_expr, case_guards=case_guards, case_default=case_default} 
	=  f (Case new_case) st 
where
	map_patterns (AlgebraicPatterns index pats) st
		# (pats, st) = mapSt map_alg_pattern pats st
		= (AlgebraicPatterns index pats, st) 
	map_patterns (BasicPatterns bt pats) st 
		# (pats, st) = mapSt map_basic_pattern pats st
		= (BasicPatterns bt pats, st)
	map_patterns (DynamicPatterns pats) st
		# (pats, st) = mapSt map_dyn_pattern pats st	
		= (DynamicPatterns pats, st) 
		
	map_alg_pattern pat=:{ap_expr} st 
		# (ap_expr, st) = mapExprSt f ap_expr st
		= ({pat & ap_expr = ap_expr}, st) 
	map_basic_pattern pat=:{bp_expr} st 
		# (bp_expr, st) = mapExprSt f bp_expr st
		= ({pat & bp_expr = bp_expr}, st) 
	map_dyn_pattern pat=:{dp_rhs} st 
		# (dp_rhs, st) = mapExprSt f dp_rhs	st
		= ({pat & dp_rhs = dp_rhs}, st) 

mapExprSt f expr st = f expr st		

// needed for collectCalls
instance == FunCall where (==) (FunCall x _) (FunCall y _) = x == y

// collect function calls made in the expression
collectCalls :: !Index !Expression -> 	[FunCall]
collectCalls current_module expr = removeDup (foldExpr get_call expr [])
where
	get_call (App {app_symb={symb_kind=SK_Function {glob_module,glob_object}}}) indexes
		| glob_module == current_module
			= [FunCall glob_object NotALevel : indexes]
			= indexes
	get_call _ indexes = indexes

// collects variables and computes the refernce counts
collectVars :: 
		!Expression 	// expression to collect variables in
		![FreeVar] 		// function argument variables
	-> (  ![FreeVar]	// argument variables (with updated ref count)
		, ![FreeVar]	// local variables
		, ![FreeVar]	// free_variables
		)
collectVars expr arg_vars  
	# arg_vars = [ {v & fv_count = 0} \\ v <- arg_vars]
	= foldExpr collect_vars expr (arg_vars, [], [])
where
	collect_vars (Var {var_name, var_info_ptr}) (arg_vars, local_vars, free_vars)
		# var = {fv_name = var_name, fv_count = 1, fv_info_ptr = var_info_ptr, fv_def_level = NotALevel}
		# (added, arg_vars) = add_var var arg_vars
		| added 
			= (arg_vars, local_vars, free_vars)
		# (added, local_vars) = add_var var local_vars
		| added 
			= (arg_vars, local_vars, free_vars)
		# (added, free_vars) = add_var var free_vars
		| added 
			= (arg_vars, local_vars, free_vars)				
		= (arg_vars, local_vars, [var:free_vars])
	where
		add_var var [] = (False, [])
		add_var var [v=:{fv_count,fv_info_ptr}:vs]
			| var.fv_info_ptr == fv_info_ptr
				= (True, [{v&fv_count = inc fv_count}:vs])
				# (added, vs) = add_var var vs
				= (added, [v:vs])	
	collect_vars (Let {let_lazy_binds, let_strict_binds}) (arg_vars, local_vars, free_vars)
		# vars = [{lb_dst&fv_count=0} \\ {lb_dst} <- (let_lazy_binds ++ let_strict_binds)]
		# (local_vars, free_vars) = foldSt add_local_var vars (local_vars, free_vars) 
		= (arg_vars, local_vars, free_vars)
	collect_vars (Case {case_guards}) (arg_vars, local_vars, free_vars)
		# vars = [{v&fv_count=0} \\ v <- collect case_guards]
		# (local_vars, free_vars) = foldSt add_local_var vars (local_vars, free_vars) 
		= (arg_vars, local_vars, free_vars) 
	where
		collect (AlgebraicPatterns _ aps) = flatten [ap_vars\\{ap_vars}<-aps]
		collect (BasicPatterns _ bps) = []
		collect (DynamicPatterns dps) = [dp_var \\ {dp_var}<-dps]
		collect NoPattern = []
	collect_vars expr st = st		

	add_local_var var (local_vars, []) = ([var:local_vars], [])
	add_local_var var (local_vars, free_vars=:[fv:fvs])
		| var.fv_info_ptr == fv.fv_info_ptr 
			= ([fv:local_vars], fvs)
			# (local_vars, fvs1) = add_local_var var (local_vars, fvs)
			= (local_vars, [fv:fvs1])
	
//****************************************************************************************
// Array helpers
//****************************************************************************************

//updateArray :: (Int a  -> a) *{a} -> *{a}
updateArray f xs 
	= map_array 0 xs
where
	map_array n xs
		#! (s, xs) = usize xs
		| n == s
			= xs
			# (x, xs) = xs ! [n]
			= map_array (inc n) {xs & [n] = f n x} 

//updateArray1 :: (Int .a  -> .a) *{.a} .a -> *{.a}
updateArray1 f xs dummy
	# (xs, _) = map_array 0 xs dummy
	= xs
where
	map_array n xs d
		#! (s, xs) = usize xs
		| n == s
			= (xs, d)
			# (x, xs) = replace xs n d	
			# x = f n x
			# (d, xs) = replace xs n x			
			= map_array (inc n) xs d

update2dArray f xss 
	= updateArray1 (\n xs -> updateArray (f n) xs) xss {}


//updateArraySt :: (Int a .st -> (a, .st)) *{a} .st -> (*{a}, .st) 
updateArraySt f xs st
	= map_array 0 xs st
where
	map_array n xs st
		#! (s, xs) = usize xs
		| n == s
			= (xs, st)
			# (x, xs) = xs![n]	
			# (x, st) = f n x st			
			= map_array (inc n) {xs&[n]=x} st


//updateArraySt :: (Int .a .st -> (.a, .st)) *{a} .a .st -> (*{a}, .st) 
updateArray1St f xs dummy st
	# (xs, _, st) = map_array 0 xs dummy st
	= (xs, st)
where
	map_array n xs d st
		#! (s, xs) = usize xs
		| n == s
			= (xs, d, st)
			# (x, xs) = replace xs n d	
			# (x, st) = f n x st
			# (d, xs) = replace xs n x			
			= map_array (inc n) xs d st
 
update2dArraySt f xss st
	= updateArray1St (\n xs st -> updateArraySt (f n) xs st) xss {} st

//foldArraySt :: (Int a .st -> .st) {a} .st -> .st 
foldArraySt f xs st
	= fold_array 0 xs st
where
	fold_array n xs st
		#! (s, xs) = usize xs
		| n == s
			= st	
			# st = f n xs.[n] st
			= fold_array (inc n) xs st

//foldUArraySt :: (Int a .st -> .st) u:{a} .st -> (u:{a}, .st) 
foldUArraySt f array st
	= map_array 0 array st
where
	map_array n array st
		# (s, array) = usize array
		| n == s
			= (array, st)	
			# (x, array) = array ! [n]
			# st = f x st
			= map_array (inc n) array st

//****************************************************************************************
//	General Helpers
//****************************************************************************************

idSt x st = (x, st)

(--) infixl 5 :: u:[a] .[a] -> u:[a] | Eq a
(--) x y = removeMembers x y 

// should actually be in the standard library
transpose []             = []
transpose [[] : xss]     = transpose xss
transpose [[x:xs] : xss] = 
	[[x : [hd l \\ l <- xss]] : transpose [xs : [ tl l \\  l <- xss]]]

unzip3 [] = ([], [], [])
unzip3 [(x1,x2,x3):xs]
	# (x1s, x2s, x3s) = unzip3 xs
	= ([x1:x1s], [x2:x2s], [x3:x3s]) 	
	
foldOptional f No st = st
foldOptional f (Yes x) st = f x st

mapOptional f No = No
mapOptional f (Yes x) = Yes (f x)

mapOptionalSt f No st = (No, st)
mapOptionalSt f (Yes x) st 
	# (y, st) = f x st
	= (Yes y, st)
	
mapSt2 f [] st1 st2 		= ([], st1, st2) 
mapSt2 f [x:xs] st1 st2
	# (y, st1, st2) = f x st1 st2
	# (ys, st1, st2) = mapSt2 f xs st1 st2 	
	= ([y:ys], st1, st2)

zipWith f [] [] = []
zipWith f [x:xs] [y:ys] = [f x y : zipWith f xs ys]

zipWithSt f [] [] st 
	= ([], st)
zipWithSt f [x:xs] [y:ys] st
	# (z, st) = f x y st
	# (zs, st) = zipWithSt f xs ys st
	= ([z:zs], st) 
	
unfoldnSt :: (.st -> (a, .st)) !Int .st -> ([a], .st)
unfoldnSt f 0 st = ([], st)
unfoldnSt f n st
	#! (x, st) = f st
	#! (xs, st) = unfoldnSt f (dec n) st
	= ([x:xs], st)
