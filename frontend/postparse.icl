implementation module postparse

import StdEnv
import syntax, parse, predef, utilities, StdCompare
import RWSDebug

/**
	 
**/

cIsAGlobalDef		:== True
cIsNotAGlobalDef	:== False

::	PredefinedIdents :== {!Ident}

SelectPredefinedIdents :: *PredefinedSymbols -> (!PredefinedIdents, !*PredefinedSymbols)
SelectPredefinedIdents predefs
	=	selectIdents 0 (createArray PD_NrOfPredefSymbols {id_name="", id_info = nilPtr}) predefs
	where
		selectIdents i idents symbols
			| i == PD_NrOfPredefSymbols
				=	(idents, symbols)
			// otherwise
				#!	symbol = symbols.[i]
				=	selectIdents (i+1) {idents & [i] = symbol.pds_ident} symbols

predef :: Int PredefinedIdents -> ParsedExpr
predef index ids
	=	PE_Ident ids.[index]

(##) infixl 9
(##) f a
	:== \idents -> apply (f idents) (toParsedExpr a idents)

(#<) a b
	:==	predef PD_SmallerFun ## a ## b

// apply :: ParsedExpr ParsedExpr -> ParsedExpr

apply :: ParsedExpr ParsedExpr -> ParsedExpr
apply (PE_List application) a
	=	PE_List (application ++ [a])
apply f a
	=	PE_List [f, a]

class toParsedExpr a :: !a !PredefinedIdents -> ParsedExpr

instance toParsedExpr [a] | toParsedExpr a where
	toParsedExpr [] ids
		=	predef PD_NilSymbol ids
	toParsedExpr [hd:tl] ids
		=	(predef PD_ConsSymbol ## hd ## tl) ids

//instance toParsedExpr a where
//	toParsedExpr _ _
//		=	abort "toParsedExpr (a) shouldn't be called"

instance toParsedExpr ParsedExpr where
	toParsedExpr x _
		=	x

instance toParsedExpr Int where
	toParsedExpr x _
		=	PE_Basic (BVI (toString x))

instance toParsedExpr Char where
	toParsedExpr x _
		=	PE_Basic (BVC (toString x))

instance toParsedExpr Ident where
	toParsedExpr x _
		=	PE_Ident x

postParseError pos msg ps=:{ca_error={pea_file}}
	# (filename, line, funname) = get_file_and_line_nr pos
	  pea_file	= pea_file <<< "Post Parse Error [" <<< filename <<< "," <<< line // PK
	  pea_file	= case funname of
	  				Yes name	-> pea_file <<< "," <<< name
	  				No			-> pea_file
	  pea_file	= pea_file <<< "]: " <<< msg <<< ".\n"
	= {ps & ca_error = { pea_file = pea_file, pea_ok = False }}
where
	get_file_and_line_nr (FunPos filename linenr funname)
		= (filename, linenr, Yes funname)
	get_file_and_line_nr (LinePos filename linenr)
		= (filename, linenr, No)

:: *CollectAdmin =
	{	ca_error		:: !ParseErrorAdmin
	,	ca_fun_count	:: !Int
	,	ca_predefs		:: !PredefinedIdents
	}

class collectFunctions a :: a !CollectAdmin -> (a, ![FunDef], !CollectAdmin)

instance collectFunctions ParsedExpr
where
	collectFunctions (PE_List exprs) ca
		# (exprs, fun_defs, ca) = collectFunctions exprs ca
		= (PE_List exprs, fun_defs, ca)
	collectFunctions (PE_Bound bound_expr) ca
		# (bound_expr, fun_defs, ca) = collectFunctions bound_expr ca
		= (PE_Bound bound_expr, fun_defs, ca)
	collectFunctions (PE_Lambda lam_ident args res) ca
		# fun_count = ca.ca_fun_count
		  next_fun_count = inc fun_count
		  ((args,res), fun_defs, ca) = collectFunctions (args,res) {ca & ca_fun_count = next_fun_count}
		  fun_def = transformLambda lam_ident args res
		= (PE_Let cIsStrict (CollectedLocalDefs { loc_functions = { ir_from = fun_count, ir_to = next_fun_count }, loc_nodes = [] })
				(PE_Ident lam_ident), [fun_def : fun_defs], ca)
	collectFunctions (PE_Record rec_expr type_name fields) ca
		# ((rec_expr,fields), fun_defs, ca) = collectFunctions (rec_expr,fields) ca
		= (PE_Record rec_expr type_name fields, fun_defs, ca)
	collectFunctions (PE_Tuple exprs) ca
		# (exprs, fun_defs, ca) = collectFunctions exprs ca
		= (PE_Tuple exprs, fun_defs, ca)
	collectFunctions (PE_Selection is_unique expr selectors) ca
		# ((expr, selectors), fun_defs, ca) = collectFunctions (expr, selectors) ca
		= (PE_Selection is_unique  expr selectors, fun_defs, ca)
	collectFunctions (PE_Update expr1 updates expr2) ca
		# ((expr1, (updates, expr2)), fun_defs, ca) = collectFunctions (expr1, (updates, expr2)) ca
		= (PE_Update expr1 updates expr2, fun_defs, ca)
	collectFunctions (PE_Case case_ident pattern_expr case_alts) ca
		# ((pattern_expr,case_alts), fun_defs, ca) = collectFunctions (pattern_expr,case_alts) ca
		= (PE_Case case_ident pattern_expr case_alts, fun_defs, ca)
	collectFunctions (PE_If if_ident c t e) ca
		# true_pattern		= PE_Basic (BVB True)
		  false_pattern		= PE_WildCard // PE_Basic (BVB False)
		= collectFunctions (PE_Case if_ident c
							[ {calt_pattern = true_pattern , calt_rhs = exprToRhs t}
							, {calt_pattern = false_pattern, calt_rhs = exprToRhs e}
							]) ca
	where
		exprToRhs expr 
		 =	{	rhs_alts	= UnGuardedExpr
		 						{	ewl_nodes	= []
								,	ewl_expr	= expr
								,	ewl_locals	= LocalParsedDefs []
								}
			,	rhs_locals	= LocalParsedDefs []
			}
	collectFunctions (PE_Let strict locals in_expr) ca
		# ((node_defs,in_expr), fun_defs, ca) = collectFunctions (locals,in_expr) ca
		= (PE_Let strict node_defs in_expr, fun_defs, ca)
	collectFunctions (PE_Compr gen_kind expr qualifiers) ca=:{ca_predefs}
		= transformComprehension gen_kind expr qualifiers ca
	collectFunctions (PE_Array expr assignments _) ca=:{ca_predefs}
		= collectFunctions (transformArrayUpdate expr assignments ca_predefs) ca
	collectFunctions (PE_Sequ sequence) ca=:{ca_predefs}
		= collectFunctions (transformSequence sequence ca_predefs) ca
	collectFunctions (PE_ArrayDenot exprs) ca=:{ca_predefs}
		= collectFunctions (transformArrayDenot exprs ca_predefs) ca
	collectFunctions expr ca
		= (expr, [], ca)

instance collectFunctions [a] | collectFunctions a
where
	collectFunctions [x:xs] ca
		# (x, fun_defs_in_x, ca) = collectFunctions x ca
		  (xs, fun_defs_in_xs, ca) = collectFunctions xs ca
		= ([x:xs], fun_defs_in_x ++ fun_defs_in_xs, ca)
	collectFunctions [] ca
		= ([], [], ca)
		
instance collectFunctions (a,b) | collectFunctions a & collectFunctions b
where
	collectFunctions (x,y) ca
		# (x, fun_defs_in_x, ca) = collectFunctions x ca
		  (y, fun_defs_in_y, ca) = collectFunctions y ca
		= ((x,y), fun_defs_in_x ++ fun_defs_in_y, ca)

instance collectFunctions Qualifier
where
	collectFunctions qual=:{qual_generators, qual_filter} ca
		# ((qual_generators, qual_filter), fun_defs, ca) = collectFunctions (qual_generators, qual_filter) ca
		= ({ qual & qual_generators = qual_generators, qual_filter = qual_filter }, fun_defs, ca) 
		
instance collectFunctions Generator
where
	collectFunctions gen=:{gen_pattern,gen_expr} ca
		# ((gen_pattern,gen_expr), fun_defs, ca) = collectFunctions (gen_pattern,gen_expr) ca
		= ({gen & gen_pattern = gen_pattern, gen_expr = gen_expr}, fun_defs, ca) 


instance collectFunctions (Optional a) | collectFunctions a
where
	collectFunctions (Yes expr) ca
		# (expr, fun_defs, ca) = collectFunctions expr ca
		= (Yes expr, fun_defs, ca) 
	collectFunctions No ca
		= (No, [], ca) 

instance collectFunctions ParsedSelection
where
	collectFunctions (PS_Array index_expr) ca
		# (index_expr, fun_defs, ca) = collectFunctions index_expr ca
		= (PS_Array index_expr, fun_defs, ca)
	collectFunctions expr ca
		= (expr, [], ca)

instance collectFunctions CaseAlt
where
	collectFunctions calt=:{calt_pattern,calt_rhs} ca
		# ((calt_pattern,calt_rhs), fun_defs, ca) = collectFunctions (calt_pattern,calt_rhs) ca
		= ({calt & calt_pattern = calt_pattern, calt_rhs = calt_rhs}, fun_defs, ca) 


instance collectFunctions Sequence
where
	collectFunctions (SQ_FromThen from_expr then_expr) ca
		# ((from_expr,then_expr), fun_defs, ca) = collectFunctions (from_expr,then_expr) ca
		= (SQ_FromThen from_expr then_expr, fun_defs, ca) 
	collectFunctions (SQ_FromThenTo from_expr then_expr to_expr) ca
		# ((from_expr,(then_expr,to_expr)), fun_defs, ca) = collectFunctions (from_expr,(then_expr,to_expr)) ca
		= (SQ_FromThenTo from_expr then_expr to_expr, fun_defs, ca) 
	collectFunctions (SQ_FromTo from_expr to_expr) ca
		# ((from_expr,to_expr), fun_defs, ca) = collectFunctions (from_expr,to_expr) ca
		= (SQ_FromTo from_expr to_expr, fun_defs, ca) 
	collectFunctions (SQ_From from_expr) ca
		# (from_expr, fun_defs, ca) = collectFunctions from_expr ca
		= (SQ_From from_expr, fun_defs, ca) 

instance collectFunctions Bind a b | collectFunctions a & collectFunctions b
where
	collectFunctions bind=:{bind_src,bind_dst} ca
		# ((bind_src,bind_dst), fun_defs, ca) = collectFunctions (bind_src,bind_dst) ca
		= ({ bind_src = bind_src, bind_dst = bind_dst }, fun_defs, ca)

instance collectFunctions OptGuardedAlts
where
	collectFunctions (GuardedAlts guarded_exprs (Yes def_expr)) ca
		# ((guarded_exprs, def_expr), fun_defs, ca) = collectFunctions (guarded_exprs, def_expr) ca
		= (GuardedAlts guarded_exprs (Yes def_expr), fun_defs, ca)
	collectFunctions (GuardedAlts guarded_exprs No) ca
		# (guarded_exprs, fun_defs, ca) = collectFunctions guarded_exprs ca
		= (GuardedAlts guarded_exprs No, fun_defs, ca)
	collectFunctions (UnGuardedExpr unguarded_expr) ca
		# (unguarded_expr, fun_defs, ca) = collectFunctions unguarded_expr ca
		= (UnGuardedExpr unguarded_expr, fun_defs, ca)

instance collectFunctions GuardedExpr
where
	collectFunctions alt=:{alt_nodes,alt_guard,alt_expr} ca
		# ((alt_nodes, (alt_guard, alt_expr)), fun_defs, ca) =
				collectFunctions (alt_nodes, (alt_guard, alt_expr)) ca
		= ({alt & alt_nodes = alt_nodes, alt_guard = alt_guard, alt_expr = alt_expr}, fun_defs, ca)

instance collectFunctions ExprWithLocalDefs
where
	collectFunctions expr=:{ewl_nodes, ewl_expr,ewl_locals} ca
		# ((ewl_nodes, (ewl_expr, ewl_locals)), fun_defs, ca) = collectFunctions (ewl_nodes, (ewl_expr, ewl_locals)) ca
		= ({expr & ewl_nodes = ewl_nodes, ewl_expr = ewl_expr, ewl_locals = ewl_locals}, fun_defs, ca)

instance collectFunctions NodeDefWithLocals
where
	collectFunctions node_def=:{ndwl_def, ndwl_locals} ca
		# (( ndwl_def, ndwl_locals), fun_defs, ca) = collectFunctions (ndwl_def, ndwl_locals) ca
		= ({node_def & ndwl_def = ndwl_def, ndwl_locals = ndwl_locals}, fun_defs, ca)

instance collectFunctions Rhs
where
	collectFunctions {rhs_alts, rhs_locals} ca
		# ((rhs_alts, rhs_locals), fun_defs, ca) = collectFunctions (rhs_alts, rhs_locals) ca
		= ({rhs_alts = rhs_alts, rhs_locals = rhs_locals}, fun_defs, ca)

instance collectFunctions LocalDefs
where
	collectFunctions (LocalParsedDefs locals) ca
		# (fun_defs, node_defs, ca) = reorganizeLocalDefinitions locals ca
		  ir_from = ca.ca_fun_count
		  ir_to = ca.ca_fun_count + length fun_defs
		  (node_defs, fun_defs_in_node_defs, ca) = collect_functions_in_node_defs node_defs {ca & ca_fun_count = ir_to}
		  (fun_defs, collected_fun_defs, ca) = reorganizeLocalDefinitionsOfFunctions fun_defs ca
		= (CollectedLocalDefs { loc_functions = { ir_from = ir_from, ir_to = ir_to }, loc_nodes = node_defs },
			fun_defs ++ fun_defs_in_node_defs ++ collected_fun_defs, ca)

	where
		collect_functions_in_node_defs [ (node_def_type, bind) : node_defs ] ca
			# (bind, fun_defs_in_bind, ca) = collectFunctions bind ca
			  (node_defs, fun_defs_in_node_defs, ca) = collect_functions_in_node_defs node_defs ca
			= ([(node_def_type, bind):node_defs], fun_defs_in_bind ++ fun_defs_in_node_defs, ca)
		collect_functions_in_node_defs [] ca
			= ([], [], ca)

instance collectFunctions NodeDef a | collectFunctions a
where
	collectFunctions node_def=:{nd_dst,nd_alts,nd_locals} ca
		# ((nd_dst,(nd_alts,nd_locals)), fun_defs, ca) = collectFunctions (nd_dst,(nd_alts,nd_locals)) ca
		= ({ node_def & nd_dst = nd_dst, nd_alts = nd_alts, nd_locals = nd_locals }, fun_defs, ca)
	
/*
instance collectFunctions a
where
	collectFunctions e ca
		= (e, [], ca)
*/

instance collectFunctions Ident
where
	collectFunctions e ca
		= (e, [], ca)

NoCollectedLocalDefs :== CollectedLocalDefs { loc_functions = { ir_from = 0, ir_to = 0 }, loc_nodes = [] }

transformLambda lam_ident args result
	# lam_rhs = { rhs_alts = UnGuardedExpr { ewl_nodes = [], ewl_expr = result, ewl_locals = NoCollectedLocalDefs },
	  			  rhs_locals = NoCollectedLocalDefs }
	  lam_body = [{pb_args = args, pb_rhs = lam_rhs }]
	  fun_def = MakeNewFunction lam_ident (length args) lam_body FK_Function NoPrio No NoPos
	= fun_def

makeNilExpression ca=:{ca_predefs}
	#! nil_id = ca_predefs.[PD_NilSymbol]
	= (PE_List [PE_Ident nil_id], ca)
makeConsExpression a1 a2 ca=:{ca_predefs}
	#! cons_id = ca_predefs.[PD_ConsSymbol]
	= (PE_List [PE_Ident cons_id, a1, a2], ca)

transformComprehension gen_kind expr qualifiers ca
	| gen_kind == cIsListGenerator
		# (nil_expr, ca) = makeNilExpression ca
		= build_list_comprehension expr nil_expr qualifiers ca
	// gen_kind == cIsArrayGenerator
		= abort "transformComprehension: cIsArrayGenerator NYI" ---> "transformComprehension: cIsArrayGenerator NYI" // PK
where		
		
	build_list_comprehension expr nil_case [] ca
		# (expr, fun_defs, ca) = collectFunctions expr ca
		  (cons_expr, ca) = makeConsExpression expr nil_case ca
		= (cons_expr, fun_defs, ca)
	build_list_comprehension expr nil_case [qual: quals] ca
		# fun_count = ca.ca_fun_count
		  next_fun_count = inc fun_count
		  ({qual_generators,qual_fun_id,qual_filter}, fun_defs, ca) = collectFunctions qual {ca & ca_fun_count = next_fun_count}
		  (cons_patterns, nil_patterns, tail_args, args, arity, opt_index, sizes, selections, ca)
		  		= build_patterns qual_generators ca 
		  (selectId,ca) = get_predef_id PD_AndOp ca /* ????????? */
		  (incId,ca) = get_predef_id PD_IncFun ca
		  (smallerId,ca) = get_predef_id PD_SmallerFun ca
		  (cons_patterns, nil_patterns, tail_args, args, arity)
				= add_index cons_patterns nil_patterns tail_args args arity incId opt_index
  		  tail_call = PE_List [PE_Ident qual_fun_id : tail_args]
		  (compr, tail_fun_defs, ca) = build_list_comprehension expr tail_call quals ca
		  (andId,ca) = get_predef_id PD_AndOp ca
		  bound_checks = make_bounds_check opt_index smallerId andId sizes
		  guard = combine_guards qual_filter bound_checks andId
		  fun_def = build_generator_function guard qual_fun_id compr nil_case arity cons_patterns nil_patterns
		  gen_appl =  PE_List [PE_Ident fun_def.fun_symb : args]
		= (PE_Let cIsStrict (CollectedLocalDefs { loc_functions = { ir_from = fun_count, ir_to = next_fun_count }, loc_nodes = [] }) gen_appl,
				[fun_def : fun_defs ++ tail_fun_defs], ca)
	where  
		// +++ combine
		build_generator_function No qual_fun_id expr nil_case arity cons_patterns nil_patterns
			# cons_rhs = { rhs_alts = UnGuardedExpr { ewl_nodes = [], ewl_expr = expr, ewl_locals = NoCollectedLocalDefs }, rhs_locals = NoCollectedLocalDefs }
			  nil_rhs = { rhs_alts = UnGuardedExpr { ewl_nodes = [], ewl_expr = nil_case, ewl_locals = NoCollectedLocalDefs }, rhs_locals = NoCollectedLocalDefs }
			  body = [{pb_args = cons_patterns, pb_rhs = cons_rhs },{pb_args = nil_patterns, pb_rhs = nil_rhs }]
			  fun_def = MakeNewFunction qual_fun_id arity body FK_Function NoPrio No NoPos
			= fun_def
		build_generator_function (Yes guard) qual_fun_id expr nil_case arity cons_patterns nil_patterns
			# cons_rhs = { rhs_alts = GuardedAlts [{alt_nodes = [], alt_guard = guard, alt_expr = UnGuardedExpr { ewl_nodes = [], ewl_expr = expr, ewl_locals = NoCollectedLocalDefs}}] No, rhs_locals = NoCollectedLocalDefs }
			  nil_rhs = { rhs_alts = UnGuardedExpr { ewl_nodes = [], ewl_expr = nil_case, ewl_locals = NoCollectedLocalDefs }, rhs_locals = NoCollectedLocalDefs }
			  body = [{pb_args = cons_patterns, pb_rhs = cons_rhs },{pb_args = nil_patterns, pb_rhs = nil_rhs }]
			  fun_def = MakeNewFunction qual_fun_id arity body FK_Function NoPrio No NoPos
			= fun_def

	build_patterns [{gen_pattern,gen_expr,gen_var} : gens] ca
		| gen_kind == cIsListGenerator
			# tail_arg = PE_Ident gen_var
			  (cons_pattern, ca) = makeConsExpression gen_pattern tail_arg ca
			  nil_pattern = PE_WildCard
			  (cons_patterns, nil_patterns, tail_args, gen_exprs, nr_of_args, opt_index, sizes, selections, ca)
			  		= build_patterns gens ca
			= ([cons_pattern : cons_patterns], [nil_pattern : nil_patterns], [tail_arg : tail_args], [gen_expr : gen_exprs],
					inc nr_of_args, opt_index, sizes, selections, ca)
		// gen_kind == cIsArrayGenerator
			# array_arg = PE_Ident gen_var
			  (cons_patterns, nil_patterns, tail_args, gen_exprs, nr_of_args, opt_index, sizes, selections, ca)
			  		= build_patterns gens ca
			  index_ident = get_index_ident opt_index gen_var
			  selection = make_selection gen_pattern array index
			= ([array_arg : cons_patterns], [array_arg : nil_patterns], [array_arg : tail_args], [gen_expr : gen_exprs],
					inc nr_of_args, Yes index_ident, sizes, selections, ca)
		where
			get_index_ident No var
				=	PE_Ident var
			get_index_ident (Yes var) _
				=	var
	build_patterns [] ca
		= ([], [], [], [], 0, No, [], [], ca)

	add_index cons_patterns nil_patterns tail_args gen_exprs arity _ _
		= (cons_patterns, nil_patterns, tail_args, gen_exprs, arity)
	add_index cons_patterns nil_patterns tail_args gen_exprs arity incId (Yes index)
		= ([index : cons_patterns], [PE_WildCard : nil_patterns], [next_index : tail_args], [PE_Basic (BVI "0") : gen_exprs], arity+1)
		where
			next_index
				=	PE_List [PE_Ident incId, index]

	make_selection pattern array index
		=	PD_NodeDef (PE_List [Arity2TupleConsIndex, array, pattern]) (PE_List [selectId, array, index])

	combine_guards No No _
		=	No
	combine_guards a No _
		=	a
	combine_guards No b _
		=	b
	combine_guards (Yes a) (Yes b) andId
		=	Yes (PE_List [PE_Ident andId, a, b])

	get_predef_id predef_index ca=:{ca_predefs}
		#! symb = ca_predefs.[predef_index]
		= (symb, ca)

	make_bounds_check _ _ _ []
		=	No
	make_bounds_check (Yes index) andId smallerId [size : sizes]
		= combine_guards (Yes check) (make_bounds_check (Yes index) andId smallerId sizes) andId
		where
			check
				=	PE_List [PE_Ident smallerId, index, size]


transformSequence :: Sequence -> PredefinedIdents -> ParsedExpr
transformSequence (SQ_FromThen frm then)
	=	predef PD_FromThen ## frm ## then
transformSequence (SQ_FromThenTo frm then to)
	=	predef PD_FromThenTo ## frm ## then ## to
transformSequence (SQ_From frm)
	=	predef PD_From ## frm
transformSequence (SQ_FromTo frm to)
	=	predef PD_FromTo ## frm ## to

transformArrayUpdate :: ParsedExpr [ElemAssignment] PredefinedIdents -> ParsedExpr
transformArrayUpdate expr updates pi
	=	foldr (update (predef PD_ArrayUpdateFun)) expr updates
	where
		update updateIdent {bind_src=value, bind_dst=index} expr
			=	(updateIdent ## expr ## index ## value) pi

transformArrayDenot :: [ParsedExpr] PredefinedIdents -> ParsedExpr
transformArrayDenot exprs pi
	=	PE_Array
			((predef PD__CreateArrayFun ## length exprs) pi)
			[{bind_dst=toParsedExpr i pi, bind_src=expr} \\ expr <- exprs & i <- [0..]]
			[]

scanModules [] parsed_modules fun_count hash_table err_file searchPaths predefs files 
	= (True, parsed_modules, [], fun_count, hash_table, err_file, predefs, files)
scanModules [{import_module,import_symbols} : mods] parsed_modules fun_count hash_table err_file searchPaths predefs files 
	# (found, mod) = try_to_find import_module parsed_modules
	| found
		= scanModules mods parsed_modules fun_count hash_table err_file searchPaths predefs files
		# (succ, parsed_modules, local_fun_defs, fun_count, hash_table, err_file, predefs, files)
				= parseAndScanDclModule import_module parsed_modules fun_count hash_table err_file searchPaths predefs files
		  (mods_succ, parsed_modules, local_fun_defs_in_imports, fun_count, hash_table, err_file, predefs, files)
		  		= scanModules mods parsed_modules fun_count hash_table err_file searchPaths predefs files
		= (succ && mods_succ, parsed_modules, local_fun_defs ++ local_fun_defs_in_imports, fun_count, hash_table, err_file, predefs, files)
where
	try_to_find mod_id []
		= (False, abort "module not found")
	try_to_find mod_id [pmod : pmods]
		| mod_id == pmod.mod_name
			= (True, pmod)
			= try_to_find mod_id pmods

MakeEmptyModule name :==  { mod_name = name, mod_type = MK_None, mod_imports = [], mod_imported_objects = [],
	mod_defs = {	def_types = [], def_constructors = [], def_selectors = [], def_classes = [], def_macros = { ir_from = 0, ir_to = 0 },
					def_members = [], def_funtypes = [], def_instances = [] } }

parseAndScanDclModule :: !Ident ![ScannedModule] !Int !*HashTable !*File !SearchPaths !*PredefinedSymbols !*Files
	-> *(!Bool, ![ScannedModule], ![FunDef], !Int, !*HashTable, !*File, !*PredefinedSymbols, !*Files);
parseAndScanDclModule dcl_module parsed_modules fun_count hash_table err_file searchPaths predefs files 
	# (parse_ok, mod, hash_table, err_file, predefs, files) = wantModule cWantDclFile dcl_module hash_table err_file searchPaths predefs files
	| parse_ok
		= scan_dcl_module mod parsed_modules fun_count hash_table err_file searchPaths predefs files
		= (False, [ MakeEmptyModule mod.mod_name : parsed_modules ], [], fun_count, hash_table, err_file, predefs, files)
where
	scan_dcl_module mod=:{mod_defs = pdefs} parsed_modules fun_count hash_table err_file searchPaths predefs files
		# (predefIdents, predefs) = SelectPredefinedIdents predefs
		# state = {ca_error = { pea_file = err_file, pea_ok = True }, ca_fun_count = 0, ca_predefs = predefIdents}
		  (_, defs, imports, imported_objects, state) = reorganizeDefinitions False pdefs 0 0 0 state
		  macro_count = length defs.def_macros + fun_count
	  	  (macro_defs, local_fun_defs, {ca_fun_count=new_fun_count, ca_error={pea_file,pea_ok}, ca_predefs})
	  	  	= reorganizeLocalDefinitionsOfFunctions defs.def_macros {state & ca_fun_count = macro_count}
		  mod = { mod & mod_imports = imports, mod_imported_objects = imported_objects, mod_defs = { defs & def_macros = { ir_from = fun_count, ir_to = macro_count } }}
		  (import_ok, parsed_modules, imported_local_fun_defs, fun_count, hash_table, err_file, predefs, files)
		  		= scanModules imports [mod : parsed_modules] new_fun_count hash_table pea_file searchPaths predefs files
		= (pea_ok && import_ok, parsed_modules, macro_defs ++ local_fun_defs ++ imported_local_fun_defs, fun_count, hash_table, err_file, predefs, files)

scanModule :: !ParsedModule !*HashTable !*File !SearchPaths !*PredefinedSymbols !*Files
	-> (!Bool, !ScannedModule, !Int, ![FunDef], !ScannedModule, !ScannedModule, ![ScannedModule], !*HashTable, !*File, !*PredefinedSymbols, !*Files)
scanModule mod=:{mod_name,mod_type,mod_defs = pdefs} hash_table err_file searchPaths predefs files
	# (predefIdents, predefs) = SelectPredefinedIdents predefs
	# state = {ca_fun_count = 0, ca_error = { pea_file = err_file, pea_ok = True }, ca_predefs = predefIdents}
	  (fun_defs, defs, imports, imported_objects, ca) = reorganizeDefinitions True pdefs 0 0 0 state
	  fun_count = length fun_defs
	  macro_count = length defs.def_macros
	  (fun_defs, local_defs, ca) = reorganizeLocalDefinitionsOfFunctions (fun_defs ++ defs.def_macros) {ca & ca_fun_count = fun_count + macro_count}
	  (def_instances, local_defs_in_insts, {ca_fun_count=tot_fun_count, ca_error = {pea_file,pea_ok}, ca_predefs})
	  		= reorganizeLocalDefinitionsOfInstances defs.def_instances ca
	  (import_ok, parsed_modules, local_defs_in_dcl, tot_fun_count, hash_table, err_file, ca_predefs, files)
	  		= scan_dcl_module mod_name mod_type tot_fun_count hash_table pea_file predefs files
	  (import_ok, parsed_modules, local_defs_in_imports, tot_fun_count, hash_table, err_file, ca_predefs, files)
	  		= scanModules imports parsed_modules tot_fun_count hash_table err_file searchPaths ca_predefs files
	  mod = { mod & mod_imports = imports, mod_imported_objects = imported_objects, mod_defs = { defs & def_instances = def_instances,
	  				def_macros = { ir_from = fun_count, ir_to = fun_count + macro_count } }}
	  [dcl_mod : modules] = reverse parsed_modules
	  all_local_defs = fun_defs ++ local_defs ++ local_defs_in_insts ++ local_defs_in_dcl ++ local_defs_in_imports
	  (pre_def_mod, ca_predefs) = buildPredefinedModule ca_predefs
	= (pea_ok && import_ok, mod, fun_count, all_local_defs, dcl_mod, pre_def_mod, modules, hash_table, err_file, ca_predefs, files)
where
	scan_dcl_module mod_name MK_Main fun_count hash_table err_file predefs files
		= (True, [MakeEmptyModule mod_name ], [], fun_count, hash_table, err_file, predefs, files)
	scan_dcl_module mod_name MK_None fun_count hash_table err_file predefs files
		= (True, [MakeEmptyModule mod_name ], [], fun_count, hash_table, err_file, predefs , files)
	scan_dcl_module mod_name kind fun_count hash_table err_file predefs files
		= parseAndScanDclModule mod_name [] fun_count hash_table err_file searchPaths predefs files 
		
reorganizeLocalDefinitionsOfInstances [] ca
	= ([], [], ca)
reorganizeLocalDefinitionsOfInstances [inst=:{pi_members} : insts] ca
	# (pi_members, local_defs, ca) = reorganizeLocalDefinitionsOfFunctions pi_members ca
	  (insts, local_defs_in_insts, ca) = reorganizeLocalDefinitionsOfInstances insts ca
	= ([{inst & pi_members = pi_members } : insts], local_defs ++ local_defs_in_insts, ca)

reorganizeLocalDefinitionsOfFunction fun_def=:{fun_body = ParsedBody bodies} ca
	# (bodies, rhs_fun_defs, ca) = collect_local_definitions_in_bodies bodies ca
	= ({fun_def & fun_body = ParsedBody bodies}, rhs_fun_defs, ca)
where	
	collect_local_definitions_in_bodies [pb=:{pb_rhs} : bodies] ca
		# (pb_rhs, rhs_fun_defs, ca) = collectFunctions pb_rhs ca
		  (bodies, body_fun_defs, ca) = collect_local_definitions_in_bodies bodies ca
		= ([ { pb & pb_rhs = pb_rhs } : bodies], rhs_fun_defs ++ body_fun_defs, ca)
	collect_local_definitions_in_bodies [] ca
		= ([], [], ca)

reorganizeLocalDefinitionsOfFunctions [] ca
	= ([], [], ca)
reorganizeLocalDefinitionsOfFunctions [fun_def : fun_defs] ca
	# (fun_def, rhs_fun_defs, ca) = reorganizeLocalDefinitionsOfFunction fun_def ca
	  (fun_defs, rhss_fun_defs, ca) = reorganizeLocalDefinitionsOfFunctions fun_defs ca
	= ([fun_def : fun_defs], rhs_fun_defs ++ rhss_fun_defs, ca) 


MakeNewFunction name arity body kind prio opt_type pos
	:== { fun_symb = name, fun_arity = arity, fun_priority = prio, fun_type = opt_type, fun_kind = kind,
		  fun_body = ParsedBody body, fun_pos = pos, fun_lifted = 0, fun_index = NoIndex, fun_info = EmptyFunInfo }

collectFunctionBodies :: !Ident !Int !Priority !FunKind ![ParsedDefinition] !*CollectAdmin
	-> (![ParsedBody], !FunKind, ![ParsedDefinition], !*CollectAdmin)
collectFunctionBodies fun_name fun_arity fun_prio fun_kind all_defs=:[PD_Function pos name is_infix args rhs new_fun_kind : defs] ca
	| belongsToTypeSpec fun_name fun_prio name is_infix
		# (new_fun_kind, ca) = combine_fun_kinds pos fun_kind new_fun_kind ca
		  (bodies, new_fun_kind, rest_defs, ca) = collectFunctionBodies fun_name fun_arity fun_prio new_fun_kind defs ca
		  act_arity	= length args
		| fun_arity == act_arity
			= ([{ pb_args = args, pb_rhs = rhs } : bodies ], new_fun_kind, rest_defs, ca)
			= ([{ pb_args = args, pb_rhs = rhs } : bodies ], new_fun_kind, rest_defs, 
			    postParseError pos	("This alternative has " + toString act_arity +
			  						 (if (act_arity == 1)" argument instead of " " arguments instead of ") + toString fun_arity
			  						) ca
			  )
		= ([], fun_kind, all_defs, ca)
	where
		combine_fun_kinds pos FK_Unknown fun_kind ca
			= (fun_kind, ca)
		combine_fun_kinds pos fun_kind new_fun_kind ca
			| fun_kind == new_fun_kind
				= (fun_kind, ca)
				= (fun_kind, postParseError pos "illegal combination of function alternatives" ca)
collectFunctionBodies fun_name fun_arity fun_prio fun_kind defs ca
	= ([], fun_kind, defs, ca)

reorganizeDefinitions icl_module [PD_Function pos name is_infix args rhs fun_kind : defs] cons_count sel_count mem_count ca
	# prio = if is_infix (Prio NoAssoc 9) NoPrio
	  fun_arity = length args
	  (bodies, fun_kind, defs, ca) = collectFunctionBodies name fun_arity prio fun_kind defs ca
	  (fun_defs, c_defs, imports, imported_objects, ca) = reorganizeDefinitions icl_module defs cons_count sel_count mem_count ca
	  fun = MakeNewFunction name fun_arity [{ pb_args = args, pb_rhs = rhs } : bodies] fun_kind prio No pos
	| fun_kind == FK_Macro
		= (fun_defs, { c_defs & def_macros = [ fun : c_defs.def_macros ]}, imports, imported_objects, ca)
		= ([ fun : fun_defs ], c_defs, imports, imported_objects, ca)
reorganizeDefinitions icl_module [PD_TypeSpec fun_pos fun_name prio No specials : defs] cons_count sel_count mem_count ca
	= case defs of
		[PD_Function pos name is_infix args rhs fun_kind : defs]
			| fun_name <> name
				-> reorganizeDefinitions icl_module defs cons_count sel_count mem_count (postParseError fun_pos ("function alternative for "+++fun_name.id_name+++" expected") ca)
			| not (sameFixity prio is_infix)
				-> reorganizeDefinitions icl_module defs cons_count sel_count mem_count (postParseError fun_pos "infix of type specification and alternative should match" ca)
			//	| belongsToTypeSpec fun_name prio name is_infix
  				# fun_arity = length args
				  (bodies, fun_kind, defs, ca) = collectFunctionBodies name fun_arity prio fun_kind defs ca
	  			  (fun_defs, c_defs, imports, imported_objects, ca) = reorganizeDefinitions icl_module defs cons_count sel_count mem_count ca
				  fun = MakeNewFunction name fun_arity [{ pb_args = args, pb_rhs = rhs } : bodies ] fun_kind prio No pos
				| fun_kind == FK_Macro
					-> (fun_defs, { c_defs & def_macros = [ fun : c_defs.def_macros]}, imports, imported_objects, ca)
					-> ([ fun : fun_defs ], c_defs, imports, imported_objects, ca)
			//	-> reorganizeDefinitions icl_module defs cons_count sel_count mem_count (postParseError fun_pos "function body expected (1)" ca)
		_
			-> reorganizeDefinitions icl_module defs cons_count sel_count mem_count (postParseError fun_pos "function alternative expected (2)" ca)
// ... PK
reorganizeDefinitions icl_module [PD_TypeSpec pos name prio (Yes fun_type=:{st_arity}) specials : defs] cons_count sel_count mem_count ca
	# (bodies, fun_kind, defs, ca) = collectFunctionBodies name st_arity prio FK_Unknown defs ca
	  (fun_defs, c_defs, imports, imported_objects, ca) = reorganizeDefinitions icl_module defs cons_count sel_count mem_count ca
	| isEmpty bodies
		# fun_type = MakeNewFunctionType name st_arity prio fun_type pos specials nilPtr
		  c_defs = { c_defs & def_funtypes = [ fun_type : c_defs.def_funtypes ]}
		| icl_module
			= (fun_defs, c_defs, imports, imported_objects, postParseError pos "function body expected" ca)
			= (fun_defs, c_defs, imports, imported_objects, ca)
		# fun = MakeNewFunction name fun_type.st_arity bodies fun_kind prio (Yes fun_type) pos
		| icl_module
			= ([fun : fun_defs], c_defs, imports, imported_objects, ca)		  
			= ([fun : fun_defs], c_defs, imports, imported_objects, postParseError pos "function body not allowed in definition module" ca)		  
reorganizeDefinitions icl_module [PD_Type type_def=:{td_rhs = ConsList cons_defs} : defs] cons_count sel_count mem_count ca
	# (cons_symbs, cons_count) = determine_symbols_of_conses cons_defs cons_count
	  (fun_defs, c_defs, imports, imported_objects, ca) = reorganizeDefinitions icl_module defs cons_count sel_count mem_count ca
	  type_def = { type_def & td_rhs = AlgType 	cons_symbs }
/* Sjaak ... */
	  c_defs = { c_defs & def_types = [type_def : c_defs.def_types], def_constructors = mapAppend ParsedConstructorToConsDef cons_defs c_defs.def_constructors }
/* ... Sjaak */
	= (fun_defs, c_defs, imports, imported_objects, ca)  
where
	determine_symbols_of_conses [{pc_cons_name,pc_cons_arity} : conses] next_cons_index
		# cons = { ds_ident = pc_cons_name, ds_arity = pc_cons_arity, ds_index = next_cons_index }
		  (conses, next_cons_index) = determine_symbols_of_conses conses (inc next_cons_index)
		= ([cons : conses], next_cons_index)
	determine_symbols_of_conses [] next_cons_index
		= ([], next_cons_index)
reorganizeDefinitions icl_module [PD_Type type_def=:{td_name, td_rhs = SelectorList rec_cons_id exivars sel_defs, td_pos } : defs] cons_count sel_count mem_count ca
	# (sel_syms, new_count) = determine_symbols_of_selectors sel_defs sel_count
	  (fun_defs, c_defs, imports, imported_objects, ca) = reorganizeDefinitions icl_module defs (inc cons_count) new_count mem_count ca
	  cons_arity = new_count - sel_count
	  cons_def = {	pc_cons_name = rec_cons_id, pc_cons_prio = NoPrio, pc_cons_arity = cons_arity, pc_cons_pos = td_pos,
	  				pc_arg_types = [ ps_field_type \\ {ps_field_type} <- sel_defs ], pc_exi_vars = exivars }
// MW was	  type_def = { type_def & td_rhs = RecordType {rt_constructor = { ds_ident = td_name, ds_arity = cons_arity, ds_index = cons_count },
	  type_def = { type_def & td_rhs = RecordType {rt_constructor = { ds_ident = rec_cons_id, ds_arity = cons_arity, ds_index = cons_count },
	  							rt_fields =  { sel \\ sel <- sel_syms }}}
/* Sjaak ... */
	  c_defs = { c_defs & def_types = [type_def : c_defs.def_types], def_constructors = [ParsedConstructorToConsDef cons_def : c_defs.def_constructors],
	  				def_selectors = mapAppend ParsedSelectorToSelectorDef sel_defs c_defs.def_selectors }
/* ... Sjaak */
	= (fun_defs, c_defs, imports, imported_objects, ca)  
where
	determine_symbols_of_selectors [{ps_field_name,ps_field_var} : sels] next_selector_index
		# field = { fs_name = ps_field_name, fs_var = ps_field_var, fs_index = next_selector_index }
		  (fields, next_selector_index) = determine_symbols_of_selectors sels (inc next_selector_index)
		= ([field : fields], next_selector_index)
	determine_symbols_of_selectors [] next_selector_index
		= ([], next_selector_index)

reorganizeDefinitions icl_module [PD_Type type_def=:{td_rhs = TypeSpec type} : defs] cons_count sel_count mem_count ca
	# (fun_defs, c_defs, imports, imported_objects, ca) = reorganizeDefinitions icl_module defs cons_count sel_count mem_count ca
	  type_def = { type_def & td_rhs = SynType type }
	  c_defs = { c_defs & def_types = [type_def : c_defs.def_types] }
	= (fun_defs, c_defs, imports, imported_objects, ca)  
reorganizeDefinitions icl_module [PD_Type type_def=:{td_rhs = EmptyRhs properties} : defs] cons_count sel_count mem_count ca
	# (fun_defs, c_defs, imports, imported_objects, ca) = reorganizeDefinitions icl_module defs cons_count sel_count mem_count ca
	  type_def = { type_def & td_rhs = AbstractType properties }
	  c_defs = { c_defs & def_types = [type_def : c_defs.def_types] }
	= (fun_defs, c_defs, imports, imported_objects, ca)  
reorganizeDefinitions icl_module [PD_Class class_def=:{class_name,class_arity,class_args} members : defs] cons_count sel_count mem_count ca
	# type_context = { tc_class = {glob_module = NoIndex, glob_object = {ds_ident = class_name, ds_arity = class_arity, ds_index = NoIndex }},
					   tc_types = [ TV tv \\ tv <- class_args ], tc_var = nilPtr }
	  (mem_defs, mem_macros, ca) = check_symbols_of_class_members members type_context ca
	  (mem_symbs, mem_defs, class_size) = reorganize_member_defs mem_defs mem_count
	  (fun_defs, c_defs, imports, imported_objects, ca) = reorganizeDefinitions icl_module defs  cons_count sel_count (mem_count + class_size) ca
	  class_def = { class_def & class_members = { member \\ member <- mem_symbs }}
	  c_defs = { c_defs & def_classes = [class_def : c_defs.def_classes], def_macros = mem_macros ++ c_defs.def_macros,
	  			 def_members = mem_defs ++ c_defs.def_members }
	= (fun_defs, c_defs, imports, imported_objects, ca)  
where
	
	check_symbols_of_class_members :: ![ParsedDefinition] !TypeContext !*CollectAdmin -> (![MemberDef], ![FunDef], !*CollectAdmin)
	check_symbols_of_class_members [PD_TypeSpec pos name prio opt_type=:(Yes type=:{st_context,st_arity}) specials : defs] type_context ca
		# (bodies, fun_kind, defs, ca) = collectFunctionBodies name st_arity prio FK_Unknown defs ca
		| isEmpty bodies
			# mem_def = {	me_symb = name, me_type = { type & st_context = [type_context : st_context ]}, me_pos = pos, me_priority = prio,
							me_offset = NoIndex, me_class_vars = [], me_class = { glob_module = NoIndex, glob_object = NoIndex}, me_type_ptr = nilPtr }
			  ( mem_defs, mem_macros, ca) = check_symbols_of_class_members defs type_context ca
			= ([mem_def : mem_defs], mem_macros, ca)
			# macro = MakeNewFunction name st_arity bodies FK_Macro prio opt_type pos
			  (mem_defs, mem_macros,ca) = check_symbols_of_class_members defs type_context ca
			= (mem_defs, [macro : mem_macros], ca)
	check_symbols_of_class_members [PD_TypeSpec fun_pos fun_name prio No specials : defs] type_context ca
		= case defs of
			[PD_Function pos name is_infix args rhs fun_kind : defs]
				| belongsToTypeSpec fun_name prio name is_infix
  					# fun_arity = length args
  					  (bodies, fun_kind, defs, ca) = collectFunctionBodies name fun_arity prio fun_kind defs ca
		  			  (mem_defs, mem_macros, ca) = check_symbols_of_class_members defs type_context ca
					  macro = MakeNewFunction name fun_arity bodies FK_Macro prio No pos
					-> (mem_defs, [macro : mem_macros], ca)
					-> check_symbols_of_class_members defs type_context (postParseError fun_pos "macro body expected" ca)
			_
				-> check_symbols_of_class_members defs type_context (postParseError fun_pos "macro body expected" ca)
	check_symbols_of_class_members [PD_Function fun_pos name is_infix args rhs fun_kind : defs] type_context ca
		# prio = if is_infix (Prio NoAssoc 9) NoPrio
		  fun_arity = length args
		  (bodies, fun_kind, defs, ca) = collectFunctionBodies name fun_arity prio fun_kind defs ca
		  (mem_defs, mem_macros, ca) = check_symbols_of_class_members defs type_context ca
		  macro = MakeNewFunction name fun_arity [{ pb_args = args, pb_rhs = rhs } : bodies] FK_Macro prio No fun_pos
		= (mem_defs, [macro : mem_macros], ca)
	check_symbols_of_class_members [] type_context ca
		= ([], [], ca)
	
	reorganize_member_defs mem_defs first_mem_index
		# mem_defs = sort mem_defs
		= determine_indexes_of_class_members mem_defs first_mem_index 0
		
	determine_indexes_of_class_members [member=:{me_symb,me_type}:members] first_mem_index mem_offset
		#! (member_symbols, member_defs, last_mem_offset) = determine_indexes_of_class_members members first_mem_index (inc mem_offset)
		= ([{ds_ident = me_symb, ds_index = first_mem_index + mem_offset, ds_arity = me_type.st_arity } : member_symbols],
			[ { member & me_offset = mem_offset } : member_defs], last_mem_offset)
	determine_indexes_of_class_members [] first_mem_index last_mem_offset
		= ([], [], last_mem_offset)

	
reorganizeDefinitions icl_module [PD_Instance class_instance=:{pi_members,pi_pos} : defs] cons_count sel_count mem_count ca
	# (fun_defs, c_defs, imports, imported_objects, ca) = reorganizeDefinitions icl_module defs cons_count sel_count mem_count ca
	  (mem_defs, ca) = collect_member_instances pi_members ca
	| icl_module || isEmpty mem_defs
		= (fun_defs, { c_defs & def_instances = [{class_instance & pi_members = mem_defs} : c_defs.def_instances] }, imports, imported_objects, ca)
		= (fun_defs, { c_defs & def_instances = [{class_instance & pi_members = []} : c_defs.def_instances] }, imports, imported_objects,
			postParseError pi_pos "instance specifications of members not allowed" ca)
where	  
	collect_member_instances [PD_Function pos name is_infix args rhs fun_kind : defs] ca
		# fun_arity = length args
		  prio = if is_infix (Prio NoAssoc 9) NoPrio
		  (bodies, fun_kind, defs, ca) = collectFunctionBodies name fun_arity prio fun_kind defs ca
		  (fun_defs, ca) = collect_member_instances defs ca
		  fun = MakeNewFunction name fun_arity [{ pb_args = args, pb_rhs = rhs } : bodies ] fun_kind prio No pos
		= ([ fun : fun_defs ], ca)
	collect_member_instances [PD_TypeSpec fun_pos fun_name prio type specials : defs] ca
		= case defs of
			[PD_Function pos name is_infix args rhs fun_kind : defs]
				| belongsToTypeSpec fun_name prio name is_infix
  					# (fun_arity, ca) = determineArity args type pos ca
  					  (bodies, fun_kind, defs, ca) = collectFunctionBodies name fun_arity prio fun_kind defs ca
		  			  (fun_defs, ca) = collect_member_instances defs ca
					  fun = MakeNewFunction name fun_arity [ { pb_args = args, pb_rhs = rhs } : bodies ] fun_kind prio type pos
					-> ([ fun : fun_defs ], ca)
			_
				-> collect_member_instances defs (postParseError fun_pos "function body expected" ca)
	collect_member_instances [] ca
	    = ([], ca)	
reorganizeDefinitions icl_module [PD_Instances class_instances : defs] cons_count sel_count mem_count ca
	= reorganizeDefinitions icl_module ([PD_Instance class_instance \\ class_instance <- class_instances] ++ defs) cons_count sel_count mem_count ca
reorganizeDefinitions icl_module [PD_Import new_imports : defs] cons_count sel_count mem_count ca
	# (fun_defs, c_defs, imports, imported_objects, ca) = reorganizeDefinitions icl_module defs cons_count sel_count mem_count ca
	= (fun_defs, c_defs, new_imports ++ imports, imported_objects, ca)
// RWS ...
reorganizeDefinitions icl_module [PD_ImportedObjects new_imported_objects : defs] cons_count sel_count mem_count ca
	# (fun_defs, c_defs, imports, imported_objects, ca) = reorganizeDefinitions icl_module defs cons_count sel_count mem_count ca
	= (fun_defs, c_defs, imports, new_imported_objects ++ imported_objects, ca)
// ... RWS
reorganizeDefinitions icl_module [def:defs] _ _ _ ca
	= abort ("reorganizeDefinitions does not match" ---> def)

reorganizeDefinitions icl_module [] _ _ _ ca
	= ([], { def_types = [], def_constructors = [], def_selectors = [], def_macros = [], def_classes = [], def_members = [],
			def_instances = [], def_funtypes = [] }, [], [], ca)

checkRhsOfNodeDef pos { rhs_alts = UnGuardedExpr {ewl_expr,ewl_nodes = [],ewl_locals = LocalParsedDefs []}, rhs_locals = LocalParsedDefs []} ca
	= (ewl_expr, ca)
checkRhsOfNodeDef pos rhs ca
	= (PE_Empty, postParseError pos "illegal node definition" ca)

reorganizeLocalDefinitions [PD_NodeDef pos pattern {rhs_alts,rhs_locals} : defs] ca
	# (fun_defs, node_defs, ca) = reorganizeLocalDefinitions defs ca
	= (fun_defs, [(No, { nd_dst = pattern, nd_alts = rhs_alts, nd_locals = rhs_locals }) : node_defs], ca)
//	= (fun_defs, [(No, { bind_dst = pattern, bind_src = rhs_expr }) : node_defs], ca)
reorganizeLocalDefinitions [PD_Function pos name is_infix args rhs fun_kind : defs] ca
	# prio = if is_infix (Prio NoAssoc 9) NoPrio
	  fun_arity = length args
	  (bodies, fun_kind, defs, ca) = collectFunctionBodies name fun_arity prio fun_kind defs ca
	  (fun_defs, node_defs, ca) = reorganizeLocalDefinitions defs ca
	  fun = MakeNewFunction name fun_arity [{ pb_args = args, pb_rhs = rhs } : bodies ] fun_kind prio No pos
	= ([ fun : fun_defs ], node_defs, ca)
reorganizeLocalDefinitions [PD_TypeSpec pos1 name1 prio type specials : defs] ca
	= case defs of
		[PD_Function pos name is_infix args rhs fun_kind : defs]
			| belongsToTypeSpec name1 prio name is_infix
				# (fun_arity, ca) = determineArity args type pos ca
				# (bodies, fun_kind, defs, ca) = collectFunctionBodies name1 fun_arity prio fun_kind defs ca
				  (fun_defs, node_defs, ca) = reorganizeLocalDefinitions defs ca
				  fun = MakeNewFunction name fun_arity [{ pb_args = args, pb_rhs = rhs } : bodies ] fun_kind prio type pos
				-> ([fun : fun_defs], node_defs, ca)
				-> reorganizeLocalDefinitions defs (postParseError pos "function body expected" ca)
		[PD_NodeDef pos pattern=:(PE_Ident id)  {rhs_alts,rhs_locals} : defs]
			| belongsToTypeSpec name1 prio id False
				# (fun_defs, node_defs, ca) = reorganizeLocalDefinitions defs ca
//	 			  (rhs_expr, ca) = checkRhsOfNodeDef pos rhs ca
				-> (fun_defs, [(type, { nd_dst = pattern, nd_alts = rhs_alts, nd_locals = rhs_locals }) : node_defs], ca)
//				-> (fun_defs, [(type, { bind_dst = pattern, bind_src = rhs_expr }) : node_defs], ca)
				-> reorganizeLocalDefinitions defs (postParseError pos "function body expected" ca)
		_
			-> reorganizeLocalDefinitions defs (postParseError pos1 "function body expected" ca)
reorganizeLocalDefinitions [] ca
	= ([], [], ca)


belongsToTypeSpec name prio new_name is_infix :==
	name == new_name && sameFixity prio is_infix

determineArity args (Yes {st_arity}) pos ca
	# arity = length args
	| arity == st_arity
		= (arity, ca)
determineArity args No pos ca
	= (length args, ca)
	
sameFixity (Prio _ _) is_infix = is_infix
sameFixity NoPrio is_infix = not is_infix


		  
