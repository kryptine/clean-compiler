implementation module postparse

import StdEnv
import syntax, parse, predef, utilities, StdCompare
// import RWSDebug

:: *CollectAdmin =
	{	ca_error		:: !*ParseErrorAdmin
	,	ca_fun_count	:: !Int
	,	ca_rev_fun_defs	:: ![FunDef]
	,	ca_predefs		:: !PredefinedIdents
	,	ca_u_predefs	:: !*PredefinedSymbols
	,	ca_hash_table	:: !*HashTable
	}

cIsAGlobalDef		:== True
cIsNotAGlobalDef	:== False

::	PredefinedIdents :== {!Ident}

SelectPredefinedIdents :: *PredefinedSymbols -> (!PredefinedIdents, !*PredefinedSymbols)
SelectPredefinedIdents predefs
	=	selectIdents 0 (createArray PD_NrOfPredefSymbols {id_name="", id_info = nilPtr}) predefs
	where
		selectIdents :: Int *PredefinedIdents *PredefinedSymbols -> (*PredefinedIdents, *PredefinedSymbols)
		selectIdents i idents symbols
			| i == PD_NrOfPredefSymbols
				=	(idents, symbols)
			// otherwise
				# (symbol, symbols) = symbols![i]
				=	selectIdents (i+1) {idents & [i] = symbol.pds_ident} symbols

predef :: Int PredefinedIdents -> ParsedExpr
predef index ids
	=	PE_Ident ids.[index]

optGuardedAltToRhs :: OptGuardedAlts -> Rhs
optGuardedAltToRhs optGuardedAlt
	=	{	rhs_alts	= optGuardedAlt
		,	rhs_locals	= LocalParsedDefs []
		}

exprToRhs expr 
	:==	{	rhs_alts	= UnGuardedExpr
 						{	ewl_nodes	= []
						,	ewl_expr	= expr
						,	ewl_locals = LocalParsedDefs []
						,	ewl_position= NoPos
						}
		,	rhs_locals	= LocalParsedDefs []
		}

prefixAndPositionToIdent :: !String !LineAndColumn !*CollectAdmin -> (!Ident, !*CollectAdmin)
prefixAndPositionToIdent prefix {lc_line, lc_column} ca=:{ca_hash_table}
//	# (ident, ca_hash_table)	=	putIdentInHashTable (prefix +++ ";" +++ toString lc_line +++ ";" +++ toString lc_column) IC_Expression ca_hash_table
	# ({boxed_ident=ident}, ca_hash_table)	=	putIdentInHashTable (prefix +++ ";" +++ toString lc_line +++ ";" +++ toString lc_column) IC_Expression ca_hash_table
	=	(ident, { ca & ca_hash_table = ca_hash_table } )

(`) infixl 9
(`) f a
	:== \idents -> apply (f idents) (toParsedExpr a idents)

// apply :: ParsedExpr ParsedExpr -> ParsedExpr

apply :: ParsedExpr ParsedExpr -> ParsedExpr
apply (PE_List application) a
	=	PE_List (application ++ [a])
apply f a
	=	PE_List [f, a]

class toParsedExpr a :: !a -> !PredefinedIdents -> ParsedExpr

instance toParsedExpr [a] | toParsedExpr a where
	toParsedExpr []
		=	predef PD_NilSymbol
	toParsedExpr [hd:tl]
		=	predef PD_ConsSymbol ` hd ` tl

instance toParsedExpr ParsedExpr where
	toParsedExpr x
		=	const x

instance toParsedExpr Int where
	toParsedExpr x
		=	const (PE_Basic (BVI (toString x)))

postParseError :: Position {#Char} *CollectAdmin -> *CollectAdmin
postParseError pos msg ps=:{ca_error={pea_file}}
	# (filename, line, funname) = get_file_and_line_nr pos
	  pea_file	= pea_file <<< "Error [" <<< filename <<< "," <<< line
	  pea_file	= case funname of
	  				Yes name	-> pea_file <<< "," <<< name
	  				No			-> pea_file
	  pea_file	= pea_file <<< "]: " <<< msg <<< ".\n"
	= {ps & ca_error = { pea_file = pea_file, pea_ok = False }}
where
	get_file_and_line_nr :: Position -> (FileName, LineNr, Optional FunctName)
	get_file_and_line_nr (FunPos filename linenr funname)
		= (filename, linenr, Yes funname)
	get_file_and_line_nr (LinePos filename linenr)
		= (filename, linenr, No)

addFunctionsRange :: [FunDef] *CollectAdmin -> (IndexRange, *CollectAdmin)
addFunctionsRange fun_defs ca
	# (frm, ca)
	  	=	ca!ca_fun_count
	  ca
		=	foldSt add_function fun_defs ca
	  (to, ca)
	  	=	ca!ca_fun_count
	=	({ir_from = frm, ir_to = to}, ca)
	where
		add_function :: FunDef !*CollectAdmin -> !*CollectAdmin
		add_function fun_def ca=:{ca_fun_count, ca_rev_fun_defs}
			=	{ca & ca_fun_count = ca.ca_fun_count + 1
					, ca_rev_fun_defs = [fun_def : ca.ca_rev_fun_defs]
				}

class collectFunctions a :: a Bool !*CollectAdmin -> (a, !*CollectAdmin)

instance collectFunctions ParsedExpr
where
	collectFunctions (PE_List exprs) icl_module ca
		# (exprs, ca) = collectFunctions exprs icl_module ca
		= (PE_List exprs, ca)
	collectFunctions (PE_Bound bound_expr) icl_module ca
		# (bound_expr, ca) = collectFunctions bound_expr icl_module ca
		= (PE_Bound bound_expr, ca)
	collectFunctions (PE_Lambda lam_ident args res pos) icl_module ca
		# ((args,res), ca) = collectFunctions (args,res) icl_module ca
		# (range, ca) = addFunctionsRange [transformLambda lam_ident args res pos icl_module] ca
		= (PE_Let cIsStrict (CollectedLocalDefs { loc_functions = range, loc_nodes = [] })
				(PE_Ident lam_ident), ca)
	collectFunctions (PE_Record rec_expr type_name fields) icl_module ca
		# ((rec_expr,fields), ca) = collectFunctions (rec_expr,fields) icl_module ca
		= (PE_Record rec_expr type_name fields, ca)
	collectFunctions (PE_Tuple exprs) icl_module ca
		# (exprs, ca) = collectFunctions exprs icl_module ca
		= (PE_Tuple exprs, ca)
	collectFunctions (PE_Selection is_unique expr selectors) icl_module ca
		# ((expr, selectors), ca) = collectFunctions (expr, selectors) icl_module ca
		= (PE_Selection is_unique expr selectors, ca)
	collectFunctions (PE_Update expr1 updates expr2) icl_module ca
		# ((expr1, (updates, expr2)), ca) = collectFunctions (expr1, (updates, expr2)) icl_module ca
		= (PE_Update expr1 updates expr2, ca)
	collectFunctions (PE_Case case_ident pattern_expr case_alts) icl_module ca
		# ((pattern_expr,case_alts), ca) = collectFunctions (pattern_expr,case_alts) icl_module ca
		= (PE_Case case_ident pattern_expr case_alts, ca)
	collectFunctions (PE_If if_ident c t e) icl_module ca
		# true_pattern		= PE_Basic (BVB True)
		  false_pattern		= PE_WildCard // PE_Basic (BVB False)
		= collectFunctions (PE_Case if_ident c
							[ {calt_pattern = true_pattern , calt_rhs = exprToRhs t}
							, {calt_pattern = false_pattern, calt_rhs = exprToRhs e}
							]) icl_module ca
	collectFunctions (PE_Let strict locals in_expr) icl_module ca
		# ((node_defs,in_expr), ca) = collectFunctions (locals,in_expr) icl_module ca
		= (PE_Let strict node_defs in_expr, ca)
	collectFunctions (PE_Compr gen_kind expr qualifiers) icl_module ca
		# (compr, ca)
			= transformComprehension gen_kind expr qualifiers ca
		=	collectFunctions compr icl_module ca
	collectFunctions (PE_UpdateComprehension expr updateExpr identExpr qualifiers) icl_module ca
		# (compr, ca)
			= transformUpdateComprehension expr updateExpr identExpr qualifiers ca
		=	collectFunctions compr icl_module ca
	collectFunctions (PE_Sequ sequence) icl_module ca=:{ca_predefs}
		= collectFunctions (transformSequence sequence ca_predefs) icl_module ca
	collectFunctions (PE_ArrayDenot exprs) icl_module ca=:{ca_predefs}
		= collectFunctions (transformArrayDenot exprs ca_predefs) icl_module ca
	collectFunctions (PE_Dynamic exprs opt_dyn_type) icl_module ca
		# (exprs, ca) = collectFunctions exprs icl_module ca
		= (PE_Dynamic exprs opt_dyn_type, ca)
	collectFunctions expr icl_module ca
		= (expr, ca)

instance collectFunctions [a] | collectFunctions a
where
	collectFunctions l icl_module ca
//		=	mapSt collectFunctions l icl_module ca
		= map_st l ca
		where
			map_st [x : xs] s
			 	# (x, s) = collectFunctions x icl_module s
				  (xs, s) = map_st xs s
				#! s = s
				= ([x : xs], s)
			map_st [] s
			 	= ([], s)

instance collectFunctions (a,b) | collectFunctions a & collectFunctions b
where
	collectFunctions (x,y) icl_module ca
		# (x, ca) = collectFunctions x icl_module ca
		  (y, ca) = collectFunctions y icl_module ca
		= ((x,y), ca)

instance collectFunctions Qualifier
where
	collectFunctions qual=:{qual_generators, qual_filter} icl_module ca
		# ((qual_generators, qual_filter), ca) = collectFunctions (qual_generators, qual_filter) icl_module ca
		= ({ qual & qual_generators = qual_generators, qual_filter = qual_filter }, ca) 

instance collectFunctions Generator
where
	collectFunctions gen=:{gen_pattern,gen_expr} icl_module ca
		# ((gen_pattern,gen_expr), ca) = collectFunctions (gen_pattern,gen_expr) icl_module ca
		= ({gen & gen_pattern = gen_pattern, gen_expr = gen_expr}, ca)

instance collectFunctions (Optional a) | collectFunctions a
where
	collectFunctions (Yes expr) icl_module ca
		# (expr, ca) = collectFunctions expr icl_module ca
		= (Yes expr, ca) 
	collectFunctions No icl_module ca
		= (No, ca) 

instance collectFunctions ParsedSelection
where
	collectFunctions (PS_Array index_expr) icl_module ca
		# (index_expr, ca) = collectFunctions index_expr icl_module ca
		= (PS_Array index_expr, ca)
	collectFunctions expr icl_module ca
		= (expr, ca)

instance collectFunctions CaseAlt
where
	collectFunctions calt=:{calt_pattern,calt_rhs} icl_module ca
		# ((calt_pattern,calt_rhs), ca) = collectFunctions (calt_pattern,calt_rhs) icl_module ca
		= ({calt & calt_pattern = calt_pattern, calt_rhs = calt_rhs}, ca) 

instance collectFunctions (Bind a b) | collectFunctions a & collectFunctions b
where
	collectFunctions bind=:{bind_src,bind_dst} icl_module ca
		# ((bind_src,bind_dst), ca) = collectFunctions (bind_src,bind_dst) icl_module ca
		= ({bind & bind_src = bind_src, bind_dst = bind_dst }, ca)

instance collectFunctions OptGuardedAlts
where
	collectFunctions (GuardedAlts guarded_exprs (Yes def_expr)) icl_module ca
		# ((guarded_exprs, def_expr), ca) = collectFunctions (guarded_exprs, def_expr) icl_module ca
		= (GuardedAlts guarded_exprs (Yes def_expr), ca)
	collectFunctions (GuardedAlts guarded_exprs No) icl_module ca
		# (guarded_exprs, ca) = collectFunctions guarded_exprs icl_module ca
		= (GuardedAlts guarded_exprs No, ca)
	collectFunctions (UnGuardedExpr unguarded_expr) icl_module ca
		# (unguarded_expr, ca) = collectFunctions unguarded_expr icl_module ca
		= (UnGuardedExpr unguarded_expr, ca)

instance collectFunctions GuardedExpr
where
	collectFunctions alt=:{alt_nodes,alt_guard,alt_expr} icl_module ca
		# ((alt_nodes, (alt_guard, alt_expr)), ca) =
				collectFunctions (alt_nodes, (alt_guard, alt_expr)) icl_module ca
		= ({alt & alt_nodes = alt_nodes, alt_guard = alt_guard, alt_expr = alt_expr}, ca)

instance collectFunctions ExprWithLocalDefs
where
	collectFunctions expr=:{ewl_nodes, ewl_expr,ewl_locals} icl_module ca
		# ((ewl_nodes, (ewl_expr, ewl_locals)), ca) = collectFunctions (ewl_nodes, (ewl_expr, ewl_locals)) icl_module ca
		= ({expr & ewl_nodes = ewl_nodes, ewl_expr = ewl_expr, ewl_locals = ewl_locals}, ca)

instance collectFunctions NodeDefWithLocals
where
	collectFunctions node_def=:{ndwl_def, ndwl_locals} icl_module ca
		# (( ndwl_def, ndwl_locals), ca) = collectFunctions (ndwl_def, ndwl_locals) icl_module ca
		= ({node_def & ndwl_def = ndwl_def, ndwl_locals = ndwl_locals}, ca)

instance collectFunctions Rhs
where
	collectFunctions {rhs_alts, rhs_locals} icl_module ca
		# ((rhs_alts, rhs_locals), ca) = collectFunctions (rhs_alts, rhs_locals) icl_module ca
		= ({rhs_alts = rhs_alts, rhs_locals = rhs_locals}, ca)

instance collectFunctions LocalDefs
where
	collectFunctions (LocalParsedDefs locals) icl_module ca
		# (fun_defs, node_defs, ca) = reorganiseLocalDefinitions locals ca
		  (node_defs, ca) = collect_functions_in_node_defs node_defs ca
		  (fun_defs, ca) = collectFunctions fun_defs icl_module ca
		  (range, ca) = addFunctionsRange fun_defs ca
		= (CollectedLocalDefs { loc_functions = range, loc_nodes = node_defs }, ca)
	where
		reorganiseLocalDefinitions :: [ParsedDefinition] *CollectAdmin -> ([FunDef],[NodeDef ParsedExpr],*CollectAdmin)
		reorganiseLocalDefinitions [PD_NodeDef pos pattern {rhs_alts,rhs_locals} : defs] ca
			# (fun_defs, node_defs, ca) = reorganiseLocalDefinitions defs ca
			= (fun_defs, [{ nd_dst = pattern, nd_alts = rhs_alts, nd_locals = rhs_locals, nd_position = pos } : node_defs], ca)
		reorganiseLocalDefinitions [PD_Function pos name is_infix args rhs fun_kind : defs] ca
			# prio = if is_infix (Prio NoAssoc 9) NoPrio
			  fun_arity = length args
			  (bodies, fun_kind, defs, ca) = collectFunctionBodies name fun_arity prio fun_kind defs ca
			  (fun_defs, node_defs, ca) = reorganiseLocalDefinitions defs ca
			  fun = MakeNewImpOrDefFunction icl_module name fun_arity [{ pb_args = args, pb_rhs = rhs, pb_position = pos } : bodies ] fun_kind prio No pos
			= ([ fun : fun_defs ], node_defs, ca)

		reorganiseLocalDefinitions [PD_TypeSpec pos1 name1 prio type specials : defs] ca
			= case defs of
				[PD_Function pos name is_infix args rhs fun_kind : _]
					| belongsToTypeSpec name1 prio name is_infix
						# fun_arity = determineArity args type
						# (bodies, fun_kind, defs, ca) = collectFunctionBodies name1 fun_arity prio fun_kind defs ca
						  (fun_defs, node_defs, ca) = reorganiseLocalDefinitions defs ca
						  fun = MakeNewImpOrDefFunction icl_module name fun_arity bodies fun_kind prio type pos
						-> ([fun : fun_defs], node_defs, ca)
						-> reorganiseLocalDefinitions defs (postParseError pos "function body expected" ca)
				[PD_NodeDef pos pattern=:(PE_Ident id) rhs : defs]
					| not (belongsToTypeSpec name1 prio id False)
						-> reorganiseLocalDefinitions defs (postParseError pos "function body expected" ca)
					| arity type<>0
						-> reorganiseLocalDefinitions defs (postParseError pos "this alternative has not enough arguments" ca)
					# (fun_defs, node_defs, ca) = reorganiseLocalDefinitions defs ca
					  fun = MakeNewImpOrDefFunction icl_module id 0 
					  				[{ pb_args = [], pb_rhs = rhs, pb_position = pos }]
					  				(FK_Function cNameNotLocationDependent) prio type pos
					-> ([fun : fun_defs], node_defs, ca)
				_
					-> reorganiseLocalDefinitions defs (postParseError pos1 "function body expected" ca)
		  where
			arity (Yes {st_arity}) = st_arity
			arity No = 2 // it was specified as infix
		reorganiseLocalDefinitions [] ca
			= ([], [], ca)

		collect_functions_in_node_defs :: [NodeDef ParsedExpr] *CollectAdmin -> ([NodeDef ParsedExpr],*CollectAdmin)
		collect_functions_in_node_defs [ bind : node_defs ] ca
			# (bind, ca) = collectFunctions bind icl_module ca
			  (node_defs, ca) = collect_functions_in_node_defs node_defs ca
			= ([bind:node_defs], ca)
		collect_functions_in_node_defs [] ca
			= ([], ca)
// RWS ... +++ remove recollection
	collectFunctions locals icl_module ca
		=	(locals, ca)
// ... RWS

instance collectFunctions (NodeDef a) | collectFunctions a
where
	collectFunctions node_def=:{nd_dst,nd_alts,nd_locals} icl_module ca
		# ((nd_dst,(nd_alts,nd_locals)), ca) = collectFunctions (nd_dst,(nd_alts,nd_locals)) icl_module ca
		= ({ node_def & nd_dst = nd_dst, nd_alts = nd_alts, nd_locals = nd_locals }, ca)

instance collectFunctions Ident
where
	collectFunctions e icl_module ca
		= (e, ca)

instance collectFunctions (ParsedInstance a) | collectFunctions a where
	collectFunctions inst=:{pi_members} icl_module ca
		# (pi_members, ca) = collectFunctions pi_members icl_module ca
		= ({inst & pi_members = pi_members }, ca)

instance collectFunctions FunDef where
	collectFunctions fun_def=:{fun_body = ParsedBody bodies} icl_module ca
		# (bodies, ca) = collectFunctions bodies icl_module ca
		= ({fun_def & fun_body = ParsedBody bodies}, ca)

instance collectFunctions ParsedBody where
	collectFunctions pb=:{pb_rhs} icl_module ca
		# (pb_rhs, ca) = collectFunctions pb_rhs icl_module ca
		= ({ pb & pb_rhs = pb_rhs }, ca)

NoCollectedLocalDefs :== CollectedLocalDefs { loc_functions = { ir_from = 0, ir_to = 0 }, loc_nodes = [] }

transformLambda :: Ident [ParsedExpr] ParsedExpr Position Bool -> FunDef
transformLambda lam_ident args result pos icl_module
	# lam_rhs = { rhs_alts = UnGuardedExpr { ewl_nodes = [], ewl_expr = result, ewl_locals = NoCollectedLocalDefs, ewl_position = NoPos },
	  					rhs_locals = NoCollectedLocalDefs }
	  lam_body = [{pb_args = args, pb_rhs = lam_rhs, pb_position = pos }]
	= MakeNewImpOrDefFunction icl_module lam_ident (length args) lam_body (FK_Function cNameLocationDependent) NoPrio No pos

makeNilExpression :: *CollectAdmin -> (ParsedExpr,*CollectAdmin)
makeNilExpression ca=:{ca_predefs}
	#! nil_id = ca_predefs.[PD_NilSymbol]
	= (PE_List [PE_Ident nil_id], ca)

makeConsExpression :: ParsedExpr ParsedExpr *CollectAdmin -> (ParsedExpr,*CollectAdmin)
makeConsExpression a1 a2 ca=:{ca_predefs}
	#! cons_id = ca_predefs.[PD_ConsSymbol]
	= (PE_List [PE_Ident cons_id, a1, a2], ca)

// +++ change to accessor functions
:: TransformedGenerator =
	{	tg_expr :: ParsedExpr
	,	tg_lhs_arg :: ParsedExpr
	,	tg_case_end_expr :: ParsedExpr
	,	tg_case_end_pattern :: ParsedExpr
	,	tg_element :: ParsedExpr
	,	tg_pattern :: ParsedExpr
	,	tg_case1 :: Ident
	,	tg_case2 :: Ident
	,	tg_rhs_continuation :: ParsedExpr
	}

transformGenerator :: Generator *CollectAdmin -> (TransformedGenerator, *CollectAdmin)
transformGenerator {gen_kind, gen_expr, gen_pattern, gen_position} ca
	| gen_kind == cIsListGenerator
		# (gen_var, ca) = prefixAndPositionToIdent "g_l" gen_position ca
		  (gen_var_i, ca) = prefixAndPositionToIdent "g_h" gen_position ca
		  (gen_var_n, ca) = prefixAndPositionToIdent "g_t" gen_position ca
		  (gen_var_case1, ca) = prefixAndPositionToIdent "g_c1" gen_position ca
		  (gen_var_case2, ca) = prefixAndPositionToIdent "g_c2" gen_position ca
		# list
			=	PE_Ident gen_var
		  hd
			=	PE_Ident gen_var_i
		  tl
		  	=	PE_Ident gen_var_n
		# (cons, ca)
			=	makeConsExpression hd tl ca
		  transformed_generator
		  	=	{	tg_expr = gen_expr
		  		,	tg_lhs_arg = list
		  		,	tg_case_end_expr = list
		  		,	tg_case_end_pattern = cons
				,	tg_element = hd
				,	tg_case1 = gen_var_case1
				,	tg_case2 = gen_var_case2
				,	tg_pattern = gen_pattern
				,	tg_rhs_continuation = PE_Ident gen_var_n
				}
		=	(transformed_generator, ca)
	// gen_kind == cIsArrayGenerator
		# (gen_var, ca) = prefixAndPositionToIdent "g_a" gen_position ca
		  (gen_var_i, ca) = prefixAndPositionToIdent "g_i" gen_position ca
		  (gen_var_n, ca) = prefixAndPositionToIdent "g_s" gen_position ca
		  (gen_var_case1, ca) = prefixAndPositionToIdent "g_c1" gen_position ca
		  (gen_var_case2, ca) = prefixAndPositionToIdent "g_c2" gen_position ca
		# (inc, ca)
			=	get_predef_id PD_IncFun ca
		  (smaller, ca)
		  	=	get_predef_id PD_SmallerFun ca
		  (usize, ca)
		  	=	get_predef_id PD_UnqArraySizeFun ca
		  (uselect, ca)
		  	=	get_predef_id PD_UnqArraySelectFun ca
		# array
			=	PE_Ident gen_var
		  i
			=	PE_Ident gen_var_i
		  n
		  	=	PE_Ident gen_var_n
		  transformed_generator
		  	=	{	tg_expr = PE_Tuple [PE_Basic (BVI "0"), PE_List [PE_Ident usize, gen_expr]]
		  		,	tg_lhs_arg = PE_Tuple [i, PE_Tuple [n, array]]
		  		,	tg_case_end_expr = PE_List [PE_List [PE_Ident smaller], i, n]
		  		,	tg_case_end_pattern = PE_Basic (BVB True)
				,	tg_element = PE_List [PE_Ident uselect, array, i]
				,	tg_case1 = gen_var_case1
				,	tg_case2 = gen_var_case2
				,	tg_pattern = PE_Tuple [gen_pattern, array]
				,	tg_rhs_continuation = PE_Tuple [PE_List [PE_Ident inc, i], PE_Tuple [n, array]]
				}
		=	(transformed_generator, ca)

::	TransformedQualifier =
	{	tq_generators :: [TransformedGenerator]
	,	tq_call :: ParsedExpr
	,	tq_lhs_args :: [ParsedExpr]
	,	tq_filter :: Optional ParsedExpr
	,	tq_continue :: ParsedExpr
	,	tq_success :: ParsedExpr
	,	tq_end :: ParsedExpr
	,	tq_fun_id :: Ident
	,	tq_fun_pos :: !Position
	}

transformQualifier :: Qualifier *CollectAdmin -> (TransformedQualifier, *CollectAdmin) 
transformQualifier {qual_generators, qual_filter, qual_position, qual_filename} ca
	# (transformedGenerators, ca)
		=	mapSt transformGenerator qual_generators ca
	# (qual_fun_id, ca)
		=	prefixAndPositionToIdent "c" qual_position ca
	=	({	tq_generators = transformedGenerators
		,	tq_call = PE_List [PE_Ident qual_fun_id : [generator.tg_expr \\ generator <- transformedGenerators]]
		,	tq_lhs_args = [generator.tg_lhs_arg \\ generator <- transformedGenerators]
		,	tq_filter = qual_filter
		,	tq_continue = PE_List [PE_Ident qual_fun_id : [generator.tg_rhs_continuation \\ generator <- transformedGenerators]]
		,	tq_success = PE_Empty
		,	tq_end = PE_Empty
		,	tq_fun_id = qual_fun_id
		,	tq_fun_pos = LinePos qual_filename qual_position.lc_line
		}, ca)

// =array&callArray are misnomers (can also be records)
transformUpdateQualifier :: ParsedExpr ParsedExpr Qualifier *CollectAdmin -> (TransformedQualifier, *CollectAdmin) 
transformUpdateQualifier array callArray {qual_generators, qual_filter, qual_position, qual_filename} ca
	# (transformedGenerators, ca)
		=	mapSt transformGenerator qual_generators ca
	# (qual_fun_id, ca)
		=	prefixAndPositionToIdent "cu" qual_position ca
	=	({	tq_generators = transformedGenerators
		,	tq_call = PE_List [PE_Ident qual_fun_id, callArray : [generator.tg_expr \\ generator <- transformedGenerators]]
		,	tq_lhs_args = [array : [generator.tg_lhs_arg \\ generator <- transformedGenerators]]
		,	tq_filter = qual_filter
		,	tq_continue = PE_List [PE_Ident qual_fun_id, array : [generator.tg_rhs_continuation \\ generator <- transformedGenerators]]
		,	tq_success = PE_Empty
		,	tq_end = PE_Empty
		,	tq_fun_id = qual_fun_id
		,	tq_fun_pos = LinePos qual_filename qual_position.lc_line
		}, ca)

transformComprehension :: Bool ParsedExpr [Qualifier] *CollectAdmin -> (ParsedExpr, *CollectAdmin)
transformComprehension gen_kind expr qualifiers ca
	| gen_kind == cIsListGenerator
		# (transformed_qualifiers, ca)
		  	=	mapSt transformQualifier qualifiers ca
		  (success, ca)
			=	makeConsExpression expr (last transformed_qualifiers).tq_continue ca
		  (nil, ca)
			=	makeNilExpression ca
		  transformed_qualifiers
		  	=	[	{qual & tq_success = success, tq_end = end}
		  		\\	qual <- transformed_qualifiers
		  		&	success <- [qual.tq_call \\ qual <- tl transformed_qualifiers] ++ [success]
		  		&	end <- [nil : [qual.tq_continue \\ qual <- transformed_qualifiers]]
		  		]
		=	makeComprehensions transformed_qualifiers success No ca
	// gen_kin == cIsArrayGenerator
		# [hd_qualifier : tl_qualifiers] = qualifiers
		  qual_position = hd_qualifier.qual_position
		  (c_i, ca) = prefixAndPositionToIdent "c_i" qual_position ca
		  (c_a, ca) = prefixAndPositionToIdent "c_a" qual_position ca
		  (frm, ca)
		  	=	get_predef_id PD_From ca
		  index_range
		  	=	PE_List [PE_Ident frm, PE_Basic (BVI "0")]
		  index_generator = {gen_kind=cIsListGenerator, gen_pattern=PE_Ident c_i, gen_expr=index_range, gen_position=qual_position}
		  (create_array, ca)
		  	=	get_predef_id PD__CreateArrayFun ca
		  (length, ca)
		  	=	computeLength qualifiers qual_position hd_qualifier.qual_filename ca
		  new_array
		  	=	PE_List [PE_Ident create_array, length]
		  update
		  	=	PE_Update (PE_Ident c_a) [PS_Array  (PE_Ident c_i)] expr
		  qualifiers
		  	=	[{hd_qualifier & qual_generators = [index_generator : hd_qualifier.qual_generators] } : tl_qualifiers]
		=	transformUpdateComprehension new_array update (PE_Ident c_a) qualifiers ca

computeLength :: [Qualifier] LineAndColumn FileName *CollectAdmin -> (ParsedExpr, *CollectAdmin)
computeLength qualifiers qual_position qual_filename ca
	# (fun_ident, ca)
		=	prefixAndPositionToIdent "c_l" qual_position ca
	  (tail_ident, ca)
		=	prefixAndPositionToIdent "c_l_t" qual_position ca
	  (i_ident, ca)
		=	prefixAndPositionToIdent "c_l_i" qual_position ca
	  (list, ca)
		=	transformComprehension cIsListGenerator (PE_Basic (BVI "0")) qualifiers ca
	  (cons, ca)
	  	=	makeConsExpression PE_WildCard (PE_Ident tail_ident) ca
	  (inc, ca)
		=	get_predef_id PD_IncFun ca
	  new_fun_pos = LinePos qual_filename qual_position.lc_line
	  parsedFunction1
		=	MakeNewParsedDef fun_ident [cons, PE_Ident i_ident] 
						(exprToRhs (PE_List [PE_Ident fun_ident,  PE_Ident tail_ident, PE_List [PE_Ident inc, PE_Ident i_ident]]))
						new_fun_pos
	  parsedFunction2
		=	MakeNewParsedDef fun_ident [PE_WildCard, PE_Ident i_ident] (exprToRhs (PE_Ident i_ident)) new_fun_pos
	= (PE_Let cIsStrict (LocalParsedDefs [parsedFunction1, parsedFunction2])
				(PE_List [PE_Ident fun_ident, list, PE_Basic (BVI "0")]), ca)

transformUpdateComprehension :: ParsedExpr ParsedExpr ParsedExpr [Qualifier] *CollectAdmin -> (ParsedExpr, *CollectAdmin)
transformUpdateComprehension expr updateExpr identExpr [qualifier:qualifiers] ca
	# (transformed_first_qualifier, ca)
	  	=	transformUpdateQualifier identExpr expr qualifier ca
	  (transformed_rest_qualifiers, ca)
	  	=	mapSt (transformUpdateQualifier identExpr identExpr) qualifiers ca
	  transformed_qualifiers
		=	[transformed_first_qualifier : transformed_rest_qualifiers]
	  success
	  	// +++ remove hack
	  	=	this_is_definitely_a_hack (last transformed_qualifiers).tq_continue updateExpr
			with
				this_is_definitely_a_hack (PE_List [f, a : args]) updateExpr
					=	PE_List [f, updateExpr : args]
	  transformed_qualifiers
	  	=	[	{qual & tq_success = success, tq_end = end}
	  		\\	qual <- transformed_qualifiers
	  		&	success <- [qual.tq_call \\ qual <- tl transformed_qualifiers] ++ [success]
	  		&	end <- [identExpr : [qual.tq_continue \\ qual <- transformed_qualifiers]]
	  		]
 	=	makeComprehensions transformed_qualifiers success (Yes identExpr) ca

// +++ rewrite threading
makeComprehensions :: [TransformedQualifier] ParsedExpr (Optional ParsedExpr) *CollectAdmin -> (ParsedExpr, *CollectAdmin)
makeComprehensions [] success _ ca
	=	(success, ca)
makeComprehensions [{tq_generators, tq_filter, tq_end, tq_call, tq_lhs_args, tq_fun_id, tq_fun_pos} : qualifiers] success threading ca
	# (success, ca)
		=	makeComprehensions qualifiers success threading ca
  	=	make_list_comprehension tq_generators tq_lhs_args success tq_end tq_filter tq_call tq_fun_id tq_fun_pos ca
	where
		make_list_comprehension :: [TransformedGenerator] [ParsedExpr] ParsedExpr ParsedExpr
									(Optional ParsedExpr) ParsedExpr Ident Position *CollectAdmin 
								 -> (ParsedExpr, *CollectAdmin)
		make_list_comprehension generators lhsArgs success end optional_filter call_comprehension fun_ident fun_pos ca
			# continue
				=	PE_List (thread (PE_Ident fun_ident) threading [generator.tg_rhs_continuation \\ generator <- generators])
				with
					thread ident No args
						=	[ident : args]
					thread ident (Yes thread) args
						=	[ident, thread : args]
			  failure
				=	continue
			  rhs
			  	=	build_rhs generators success optional_filter failure end fun_pos
			  parsed_def
			  	=	MakeNewParsedDef fun_ident lhsArgs rhs fun_pos
			= (PE_Let cIsStrict (LocalParsedDefs [parsed_def]) call_comprehension, ca)

		build_rhs :: [TransformedGenerator] ParsedExpr (Optional ParsedExpr) ParsedExpr ParsedExpr Position -> Rhs
		build_rhs [generator : generators] success optional_filter failure end fun_pos
			=	case_with_default generator.tg_case1 generator.tg_case_end_expr generator.tg_case_end_pattern
					(foldr (case_end end)
						(case_with_default generator.tg_case2 generator.tg_element generator.tg_pattern
							(foldr (case_pattern failure) rhs generators) failure)
						generators)
					end
			where
				rhs
					=	case optional_filter of
							Yes filter
								->	optGuardedAltToRhs (GuardedAlts [
										{alt_nodes = [], alt_guard = filter, alt_expr = UnGuardedExpr
												{ewl_nodes	= [], ewl_expr	= success, ewl_locals	= LocalParsedDefs [], ewl_position = NoPos },
											alt_ident = { id_name ="_f;" +++ toString line_nr +++ ";", id_info = nilPtr },
											alt_position = NoPos}] No)
							No
								->	exprToRhs success
				(LinePos _ line_nr) = fun_pos

	/* +++ remove code duplication (bug in 2.0 with nested cases)
		case_end :: TransformedGenerator Rhs -> Rhs
		case_end {tg_case1, tg_case_end_expr, tg_case_end_pattern} rhs
			=	single_case tg_case1 tg_case_end_expr tg_case_end_pattern rhs
	
		case_pattern :: TransformedGenerator Rhs -> Rhs
		case_pattern {tg_case2, tg_element, tg_pattern} rhs
			=	single_case tg_case2 tg_element tg_pattern rhs
	*/

		case_end :: ParsedExpr TransformedGenerator Rhs -> Rhs
		case_end end {tg_case1, tg_case_end_expr, tg_case_end_pattern} rhs
			=	case_with_default tg_case1 tg_case_end_expr tg_case_end_pattern rhs end
	
		case_pattern :: ParsedExpr TransformedGenerator Rhs -> Rhs
		case_pattern failure {tg_case2, tg_element, tg_pattern} rhs
			=	case_with_default tg_case2 tg_element tg_pattern rhs failure
	
		single_case :: Ident ParsedExpr ParsedExpr Rhs -> Rhs
		single_case case_ident expr pattern rhs
			=	exprToRhs (PE_Case case_ident expr
					[	{calt_pattern = pattern, calt_rhs = rhs}
					])
	
		case_with_default :: Ident ParsedExpr ParsedExpr Rhs ParsedExpr -> Rhs
		case_with_default case_ident expr pattern rhs default_rhs
			=	exprToRhs (PE_Case case_ident expr
					[	{calt_pattern = pattern, calt_rhs = rhs}
					,	{calt_pattern = PE_WildCard, calt_rhs = exprToRhs default_rhs}
					])

get_predef_id :: Int *CollectAdmin -> (Ident, *CollectAdmin)
get_predef_id predef_index ca=:{ca_predefs}
	= ca!ca_predefs.[predef_index]

transformSequence :: Sequence -> PredefinedIdents -> ParsedExpr
transformSequence (SQ_FromThen frm then)
	=	predef PD_FromThen ` frm ` then
transformSequence (SQ_FromThenTo frm then to)
	=	predef PD_FromThenTo ` frm ` then ` to
transformSequence (SQ_From frm)
	=	predef PD_From ` frm
transformSequence (SQ_FromTo frm to)
	=	predef PD_FromTo ` frm ` to

transformArrayUpdate :: ParsedExpr [Bind ParsedExpr ParsedExpr] PredefinedIdents -> ParsedExpr
transformArrayUpdate expr updates pi
	=	foldr (update pi (predef PD_ArrayUpdateFun)) expr updates
	where
		update :: PredefinedIdents (PredefinedIdents -> ParsedExpr) (Bind ParsedExpr ParsedExpr) ParsedExpr -> ParsedExpr
		update pi updateIdent {bind_src=value, bind_dst=index} expr
			=	(updateIdent ` expr ` index ` value) pi

transformArrayDenot :: [ParsedExpr] PredefinedIdents -> ParsedExpr
transformArrayDenot exprs pi
	=	transformArrayUpdate
			((predef PD__CreateArrayFun ` length exprs) pi)
			[{bind_dst=toParsedExpr i pi, bind_src=expr} \\ expr <- exprs & i <- [0..]]
			pi

scanModules :: [ParsedImport] [ScannedModule] [Ident] SearchPaths *Files *CollectAdmin -> (Bool, [ScannedModule], *Files, *CollectAdmin)
scanModules [] parsed_modules cached_modules searchPaths files ca
	= (True, parsed_modules, files, ca)
scanModules [{import_module,import_symbols,import_file_position} : mods] parsed_modules cached_modules searchPaths files ca
	| in_cache import_module cached_modules
		= scanModules mods parsed_modules cached_modules searchPaths files ca
	| try_to_find import_module parsed_modules
		= scanModules mods parsed_modules cached_modules searchPaths files ca
		# (succ, parsed_modules, files, ca)
				= parseAndScanDclModule import_module import_file_position parsed_modules cached_modules searchPaths files ca
		  (mods_succ, parsed_modules, files, ca)
		  		= scanModules mods parsed_modules cached_modules searchPaths files ca
		= (succ && mods_succ, parsed_modules, files, ca)
where
	in_cache mod_id []
		= False
	in_cache mod_id [cached_module_ident : pmods]
		| mod_id==cached_module_ident
			=True
			= in_cache mod_id pmods

 	try_to_find :: Ident [ScannedModule] -> Bool
	try_to_find mod_id []
		= False
	try_to_find mod_id [pmod : pmods]
		| mod_id == pmod.mod_name
			=True
			= try_to_find mod_id pmods

MakeEmptyModule name :==  { mod_name = name, mod_type = MK_None, mod_imports = [], mod_imported_objects = [],
	mod_defs = {	def_types = [], def_constructors = [], def_selectors = [], def_classes = [], def_macros = { ir_from = 0, ir_to = 0 },
					def_members = [], def_funtypes = [], def_instances = [], /* AA */ def_generics = [] } }

parseAndScanDclModule :: !Ident !Position ![ScannedModule] ![Ident] !SearchPaths !*Files !*CollectAdmin
	-> *(!Bool, ![ScannedModule], !*Files, !*CollectAdmin)
parseAndScanDclModule dcl_module import_file_position parsed_modules cached_modules searchPaths files ca
	# {ca_error, ca_fun_count, ca_rev_fun_defs, ca_predefs, ca_u_predefs, ca_hash_table}
		= ca
	  hash_table = ca_hash_table
	  pea_file = ca_error.pea_file
	  predefs = ca_u_predefs
	# (parse_ok, mod, hash_table, err_file, predefs, files) = wantModule cWantDclFile dcl_module import_file_position hash_table pea_file searchPaths predefs files
	# ca = {ca_hash_table=hash_table, ca_error={pea_file=err_file,pea_ok=True}, ca_u_predefs=predefs, ca_fun_count=ca_fun_count, ca_rev_fun_defs=ca_rev_fun_defs, ca_predefs=ca_predefs}
	| parse_ok
		= scan_dcl_module mod parsed_modules searchPaths files ca
		= (False, [MakeEmptyModule mod.mod_name : parsed_modules], files, ca)
where
	scan_dcl_module :: ParsedModule [ScannedModule] !SearchPaths *Files *CollectAdmin -> (Bool, [ScannedModule], *Files, *CollectAdmin)
	scan_dcl_module mod=:{mod_defs = pdefs} parsed_modules searchPaths files ca
		# (_, defs, imports, imported_objects, ca)
			=	reorganiseDefinitions False pdefs 0 0 0 0 ca
	  	  (macro_defs, ca)
	  	  	=	collectFunctions defs.def_macros False ca
		  (range, ca)
		  	=	addFunctionsRange macro_defs ca
		  (pea_ok,ca)
		  	=	ca!ca_error.pea_ok
		  mod
		  	=	{ mod & mod_imports = imports, mod_imported_objects = imported_objects, mod_defs = { defs & def_macros = range }}
		  (import_ok, parsed_modules, files, ca)
		  		= scanModules imports [mod : parsed_modules] cached_modules searchPaths files ca
		= (pea_ok && import_ok, parsed_modules, files, ca)

scanModule :: !ParsedModule ![Ident] !Int !*HashTable !*File !SearchPaths !*PredefinedSymbols !*Files
	-> (!Bool, !ScannedModule, !IndexRange, ![FunDef], !Optional ScannedModule, ![ScannedModule],!Int,!Int,!*HashTable, !*File, !*PredefinedSymbols, !*Files)
scanModule mod=:{mod_name,mod_type,mod_defs = pdefs} cached_modules first_new_function_or_macro_index hash_table err_file searchPaths predefs files
	# (predefIdents, predefs) = SelectPredefinedIdents predefs
	# ca =	{	ca_error		= {pea_file = err_file, pea_ok = True}
			,	ca_fun_count	= first_new_function_or_macro_index
			,	ca_rev_fun_defs	= []
			,	ca_predefs		= predefIdents
			,	ca_u_predefs	= predefs
			,	ca_hash_table	= hash_table
			}
	  (fun_defs, defs, imports, imported_objects, ca) = reorganiseDefinitions True pdefs 0 0 0 0 ca
	  (reorganise_icl_ok, ca) = ca!ca_error.pea_ok

	  (import_dcl_ok, optional_parsed_dcl_mod,dcl_module_n,parsed_modules, cached_modules,files, ca)
	  		= scan_dcl_module mod_name mod_type files ca
	  (import_dcls_ok, parsed_modules, files, ca)
	  		= scanModules imports parsed_modules cached_modules searchPaths files ca

	  (pea_dcl_ok,optional_dcl_mod,ca) =  collect_main_dcl_module optional_parsed_dcl_mod dcl_module_n ca

	  (n_functions_and_macros_in_dcl_modules,ca) =ca!ca_fun_count

	  modules = reverse parsed_modules

	  import_dcl_ok = import_dcl_ok && pea_dcl_ok;

	  ca = {ca & ca_hash_table=set_hte_mark 1 ca.ca_hash_table}

	  (fun_defs, ca) = collectFunctions fun_defs True ca
	  (fun_range, ca) = addFunctionsRange fun_defs ca
	  (macro_defs, ca) = collectFunctions defs.def_macros True ca
	  (macro_range, ca) = addFunctionsRange macro_defs ca
	  (def_instances, ca) = collectFunctions defs.def_instances True ca

	  ca = {ca & ca_hash_table=set_hte_mark 0 ca.ca_hash_table}

	  (pea_ok, ca) = ca!ca_error.pea_ok

	  {	ca_error = {pea_file = err_file},	ca_predefs	= predefs, ca_rev_fun_defs, ca_u_predefs, ca_hash_table = hash_table } = ca
	  mod = { mod & mod_imports = imports, mod_imported_objects = imported_objects, mod_defs = { defs & def_instances = def_instances,
	  				def_macros = macro_range }}
//	  (pre_def_mod, ca_u_predefs) = buildPredefinedModule ca_u_predefs
	= (reorganise_icl_ok && pea_ok && import_dcl_ok && import_dcls_ok, mod, fun_range, reverse ca_rev_fun_defs, optional_dcl_mod, /*pre_def_mod,*/ modules, dcl_module_n,n_functions_and_macros_in_dcl_modules,hash_table, err_file, ca_u_predefs, files)
where
	scan_dcl_module :: Ident ModuleKind *Files *CollectAdmin -> (!Bool,!Optional (Module (CollectedDefinitions (ParsedInstance FunDef) [FunDef])),!Int,![ScannedModule],![Ident],!*Files,!*CollectAdmin)
	scan_dcl_module mod_name MK_Main files ca
		= (True, No,NoIndex,[], cached_modules,files, ca)
	scan_dcl_module mod_name MK_None files ca
		= (True, No,NoIndex,[], cached_modules,files, ca)
	scan_dcl_module mod_name kind files ca
		# module_n_in_cache = in_cache 0 cached_modules;
			with
			in_cache module_n []
				= NoIndex
			in_cache module_n [cached_module_ident : pmods]
				| mod_name==cached_module_ident
					= module_n
					= in_cache (module_n+1) pmods
		| module_n_in_cache<>NoIndex
			= (True,No,module_n_in_cache,[],cached_modules,files,ca)
		# {ca_error, ca_fun_count, ca_rev_fun_defs, ca_predefs, ca_u_predefs, ca_hash_table} = ca
		  hash_table = ca_hash_table
		  pea_file = ca_error.pea_file
		  predefs = ca_u_predefs
		# (parse_ok, mod, hash_table, err_file, predefs, files) = wantModule cWantDclFile mod_name NoPos hash_table pea_file searchPaths predefs files
		# ca = {ca_hash_table=hash_table, ca_error={pea_file=err_file,pea_ok=True}, ca_u_predefs=predefs, ca_fun_count=ca_fun_count, ca_rev_fun_defs=ca_rev_fun_defs, ca_predefs=ca_predefs}
		| not parse_ok
			= (False, No,NoIndex, [],cached_modules, files, ca)
			# pdefs = mod.mod_defs
			# (_, defs, imports, imported_objects, ca) =	reorganiseDefinitions False pdefs 0 0 0 0 ca
			# mod  = { mod & mod_imports = imports, mod_imported_objects = imported_objects, mod_defs = defs}
			# cached_modules = [mod.mod_name:cached_modules]
			# (import_ok, parsed_modules, files, ca) = scanModules imports [] cached_modules searchPaths files ca
			= (import_ok, Yes mod, NoIndex,parsed_modules, cached_modules,files, ca)

	collect_main_dcl_module (Yes mod=:{mod_defs=defs}) dcl_module_n ca
	 #	(macro_defs, ca)  = collectFunctions defs.def_macros False ca
		(range, ca)	=	addFunctionsRange macro_defs ca
		(pea_ok,ca) =	ca!ca_error.pea_ok
		mod  = { mod & mod_defs = { defs & def_macros = range }}
	 = (pea_ok,Yes mod,ca)
	collect_main_dcl_module No dcl_module_n ca
		| dcl_module_n==NoIndex
			 =	(True,Yes (MakeEmptyModule mod_name),ca)
			 =	(True,No,ca)

MakeNewImpOrDefFunction icl_module name arity body kind prio opt_type pos
	:== { fun_symb = name, fun_arity = arity, fun_priority = prio, fun_type = opt_type, fun_kind = fun_kind_to_def_or_imp_fun_kind icl_module kind,
		  fun_body = ParsedBody body, fun_pos = pos, fun_lifted = 0, fun_index = NoIndex, fun_info = EmptyFunInfo }

fun_kind_to_def_or_imp_fun_kind icl_module (FK_Function b)
	| icl_module
		= FK_ImpFunction b
		= FK_DefFunction b
fun_kind_to_def_or_imp_fun_kind icl_module FK_Macro
	| icl_module
		 = FK_ImpMacro
		 = FK_DefMacro
fun_kind_to_def_or_imp_fun_kind icl_module FK_Caf = FK_ImpCaf
fun_kind_to_def_or_imp_fun_kind icl_module FK_Unknown = FK_DefOrImpUnknown

MakeNewParsedDef ident args rhs pos
	:==	PD_Function pos ident False args rhs (FK_Function cNameLocationDependent)

collectFunctionBodies :: !Ident !Int !Priority !FunKind ![ParsedDefinition] !*CollectAdmin
	-> (![ParsedBody], !FunKind, ![ParsedDefinition], !*CollectAdmin)
collectFunctionBodies fun_name fun_arity fun_prio fun_kind all_defs=:[PD_Function pos name is_infix args rhs new_fun_kind : defs] ca
	| belongsToTypeSpec fun_name fun_prio name is_infix
		# (new_fun_kind, ca) = combine_fun_kinds pos fun_kind new_fun_kind ca
		  (bodies, new_fun_kind, rest_defs, ca) = collectFunctionBodies fun_name fun_arity fun_prio new_fun_kind defs ca
		  act_arity	= length args
		| fun_arity == act_arity
			= ([{ pb_args = args, pb_rhs = rhs, pb_position = pos } : bodies ], new_fun_kind, rest_defs, ca)
			= ([{ pb_args = args, pb_rhs = rhs, pb_position = pos } : bodies ], new_fun_kind, rest_defs, 
			    postParseError pos	("This alternative has " + toString act_arity +
			  						 (if (act_arity == 1)" argument instead of " " arguments instead of ") + toString fun_arity
			  						) ca
			  )
		= ([], fun_kind, all_defs, ca)
	where
		combine_fun_kinds :: Position FunKind FunKind *CollectAdmin -> (FunKind, *CollectAdmin)
		combine_fun_kinds pos FK_Unknown fun_kind ca
			= (fun_kind, ca)
		combine_fun_kinds pos fun_kind new_fun_kind ca
			| fun_kind == new_fun_kind
				= (fun_kind, ca)
				= (fun_kind, postParseError pos "illegal combination of function alternatives" ca)
collectFunctionBodies fun_name fun_arity fun_prio fun_kind defs ca
	= ([], fun_kind, defs, ca)

reorganiseDefinitions :: Bool [ParsedDefinition] Index Index Index Index *CollectAdmin -> (![FunDef],!CollectedDefinitions (ParsedInstance FunDef) [FunDef], ![ParsedImport], ![ImportedObject], !*CollectAdmin)
reorganiseDefinitions icl_module [PD_Function pos name is_infix args rhs fun_kind : defs] cons_count sel_count mem_count type_count ca
	# prio = if is_infix (Prio NoAssoc 9) NoPrio
	  fun_arity = length args
	  (bodies, fun_kind, defs, ca) = collectFunctionBodies name fun_arity prio fun_kind defs ca
	  (fun_defs, c_defs, imports, imported_objects, ca) = reorganiseDefinitions icl_module defs cons_count sel_count mem_count type_count ca
	  fun = MakeNewImpOrDefFunction icl_module name fun_arity [{ pb_args = args, pb_rhs = rhs, pb_position = pos } : bodies] fun_kind prio No pos
	| fun_kind == FK_Macro
		= (fun_defs, { c_defs & def_macros = [ fun : c_defs.def_macros ]}, imports, imported_objects, ca)
		= ([ fun : fun_defs ], c_defs, imports, imported_objects, ca)
reorganiseDefinitions icl_module [PD_TypeSpec fun_pos fun_name prio No specials : defs] cons_count sel_count mem_count type_count ca
	= case defs of
		[PD_Function pos name is_infix args rhs fun_kind : defs]
			| fun_name <> name
				-> reorganiseDefinitions icl_module defs cons_count sel_count mem_count type_count (postParseError fun_pos ("function alternative for "+++fun_name.id_name+++" expected") ca)
			| not (sameFixity prio is_infix)
				-> reorganiseDefinitions icl_module defs cons_count sel_count mem_count type_count (postParseError fun_pos "infix of type specification and alternative should match" ca)
			//	| belongsToTypeSpec fun_name prio name is_infix
  				# fun_arity = length args
				  (bodies, fun_kind, defs, ca) = collectFunctionBodies name fun_arity prio fun_kind defs ca
	  			  (fun_defs, c_defs, imports, imported_objects, ca) = reorganiseDefinitions icl_module defs cons_count sel_count mem_count type_count ca
				  fun = MakeNewImpOrDefFunction icl_module name fun_arity [{ pb_args = args, pb_rhs = rhs, pb_position = pos } : bodies ] fun_kind prio No pos
				| fun_kind == FK_Macro
					-> (fun_defs, { c_defs & def_macros = [ fun : c_defs.def_macros]}, imports, imported_objects, ca)
					-> ([ fun : fun_defs ], c_defs, imports, imported_objects, ca)
			//	-> reorganiseDefinitions icl_module defs cons_count sel_count mem_count (postParseError fun_pos "function body expected (1)" ca)
		_
			-> reorganiseDefinitions icl_module defs cons_count sel_count mem_count type_count (postParseError fun_pos "function alternative expected (2)" ca)
reorganiseDefinitions icl_module [PD_TypeSpec pos name prio (Yes fun_type=:{st_arity}) specials : defs] cons_count sel_count mem_count type_count ca
	# (bodies, fun_kind, defs, ca) = collectFunctionBodies name st_arity prio FK_Unknown defs ca
	  (fun_defs, c_defs, imports, imported_objects, ca) = reorganiseDefinitions icl_module defs cons_count sel_count mem_count type_count ca
	| isEmpty bodies
		# fun_type = MakeNewFunctionType name st_arity prio fun_type pos specials nilPtr
		  c_defs = { c_defs & def_funtypes = [ fun_type : c_defs.def_funtypes ]}
		| icl_module
			= (fun_defs, c_defs, imports, imported_objects, postParseError pos "function body expected" ca)
			= (fun_defs, c_defs, imports, imported_objects, ca)
		# fun = MakeNewImpOrDefFunction icl_module name fun_type.st_arity bodies fun_kind prio (Yes fun_type) pos
		| icl_module
			= ([fun : fun_defs], c_defs, imports, imported_objects, ca)		  
			= ([fun : fun_defs], c_defs, imports, imported_objects, postParseError pos "function body not allowed in definition module" ca)		  
reorganiseDefinitions icl_module [PD_Type type_def=:{td_rhs = ConsList cons_defs} : defs] cons_count sel_count mem_count type_count ca
	# (cons_symbs, cons_count) = determine_symbols_of_conses cons_defs cons_count
	  (fun_defs, c_defs, imports, imported_objects, ca) = reorganiseDefinitions icl_module defs cons_count sel_count mem_count (type_count+1) ca
	  type_def = { type_def & td_rhs = AlgType 	cons_symbs }
	  c_defs = { c_defs & def_types = [type_def : c_defs.def_types], def_constructors = mapAppend ParsedConstructorToConsDef cons_defs c_defs.def_constructors }
	= (fun_defs, c_defs, imports, imported_objects, ca)  
where
	determine_symbols_of_conses :: [ParsedConstructor] Index -> ([DefinedSymbol], Index)
	determine_symbols_of_conses [{pc_cons_name,pc_cons_arity} : conses] next_cons_index
		# cons = { ds_ident = pc_cons_name, ds_arity = pc_cons_arity, ds_index = next_cons_index }
		  (conses, next_cons_index) = determine_symbols_of_conses conses (inc next_cons_index)
		= ([cons : conses], next_cons_index)
	determine_symbols_of_conses [] next_cons_index
		= ([], next_cons_index)
reorganiseDefinitions icl_module [PD_Type type_def=:{td_name, td_rhs = SelectorList rec_cons_id exivars sel_defs, td_pos } : defs] cons_count sel_count mem_count type_count ca
	# (sel_syms, new_count) = determine_symbols_of_selectors sel_defs sel_count
	  (fun_defs, c_defs, imports, imported_objects, ca) = reorganiseDefinitions icl_module defs (inc cons_count) new_count mem_count (type_count+1) ca
	  cons_arity = new_count - sel_count
	  cons_def = {	pc_cons_name = rec_cons_id, pc_cons_prio = NoPrio, pc_cons_arity = cons_arity, pc_cons_pos = td_pos,
	  				pc_arg_types = [ ps_field_type \\ {ps_field_type} <- sel_defs ], pc_exi_vars = exivars }
	  type_def = { type_def & td_rhs = RecordType {rt_constructor = { ds_ident = rec_cons_id, ds_arity = cons_arity, ds_index = cons_count },
	  							rt_fields =  { sel \\ sel <- sel_syms }}}
	  c_defs = { c_defs & def_types = [type_def : c_defs.def_types], def_constructors = [ParsedConstructorToConsDef cons_def : c_defs.def_constructors],
	  				def_selectors = mapAppend (ParsedSelectorToSelectorDef type_count) sel_defs c_defs.def_selectors }
	= (fun_defs, c_defs, imports, imported_objects, ca)  
where
	determine_symbols_of_selectors :: [ParsedSelector] Index -> ([FieldSymbol], Index)
	determine_symbols_of_selectors [{ps_field_name,ps_field_var} : sels] next_selector_index
		# field = { fs_name = ps_field_name, fs_var = ps_field_var, fs_index = next_selector_index }
		  (fields, next_selector_index) = determine_symbols_of_selectors sels (inc next_selector_index)
		= ([field : fields], next_selector_index)
	determine_symbols_of_selectors [] next_selector_index
		= ([], next_selector_index)

reorganiseDefinitions icl_module [PD_Type type_def=:{td_rhs = TypeSpec type} : defs] cons_count sel_count mem_count type_count ca
	# (fun_defs, c_defs, imports, imported_objects, ca) = reorganiseDefinitions icl_module defs cons_count sel_count mem_count (type_count+1) ca
	  type_def = { type_def & td_rhs = SynType type }
	  c_defs = { c_defs & def_types = [type_def : c_defs.def_types] }
	= (fun_defs, c_defs, imports, imported_objects, ca)  
reorganiseDefinitions icl_module [PD_Type type_def=:{td_rhs = EmptyRhs properties} : defs] cons_count sel_count mem_count type_count ca
	# (fun_defs, c_defs, imports, imported_objects, ca) = reorganiseDefinitions icl_module defs cons_count sel_count mem_count (type_count+1) ca
	  type_def = { type_def & td_rhs = AbstractType properties }
	  c_defs = { c_defs & def_types = [type_def : c_defs.def_types] }
	= (fun_defs, c_defs, imports, imported_objects, ca)  
reorganiseDefinitions icl_module [PD_Class class_def=:{class_name,class_arity,class_args} members : defs] cons_count sel_count mem_count type_count ca
	# type_context = { tc_class = {glob_module = NoIndex, glob_object = {ds_ident = class_name, ds_arity = class_arity, ds_index = NoIndex }},
					   tc_types = [ TV tv \\ tv <- class_args ], tc_var = nilPtr }
	  (mem_defs, mem_macros, ca) = check_symbols_of_class_members members type_context ca
	  (mem_symbs, mem_defs, class_size) = reorganise_member_defs mem_defs mem_count
	  (fun_defs, c_defs, imports, imported_objects, ca) = reorganiseDefinitions icl_module defs  cons_count sel_count (mem_count + class_size) type_count ca
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
			# macro = MakeNewImpOrDefFunction icl_module name st_arity bodies FK_Macro prio opt_type pos
			  (mem_defs, mem_macros,ca) = check_symbols_of_class_members defs type_context ca
			= (mem_defs, [macro : mem_macros], ca)
	check_symbols_of_class_members [PD_TypeSpec fun_pos fun_name prio No specials : defs] type_context ca
		= case defs of
			[PD_Function pos name is_infix args rhs fun_kind : defs]
				| belongsToTypeSpec fun_name prio name is_infix
  					# fun_arity = length args
  					  (bodies, fun_kind, defs, ca) = collectFunctionBodies name fun_arity prio fun_kind defs ca
		  			  (mem_defs, mem_macros, ca) = check_symbols_of_class_members defs type_context ca
					  macro = MakeNewImpOrDefFunction icl_module name fun_arity bodies FK_Macro prio No pos
					-> (mem_defs, [macro : mem_macros], ca)
					-> check_symbols_of_class_members defs type_context (postParseError fun_pos "macro body expected" ca)
			_
				-> check_symbols_of_class_members defs type_context (postParseError fun_pos "macro body expected" ca)
	check_symbols_of_class_members [PD_Function fun_pos name is_infix args rhs fun_kind : defs] type_context ca
		# prio = if is_infix (Prio NoAssoc 9) NoPrio
		  fun_arity = length args
		  (bodies, fun_kind, defs, ca) = collectFunctionBodies name fun_arity prio fun_kind defs ca
		  (mem_defs, mem_macros, ca) = check_symbols_of_class_members defs type_context ca
		  macro = MakeNewImpOrDefFunction icl_module name fun_arity [{ pb_args = args, pb_rhs = rhs, pb_position = fun_pos } : bodies] FK_Macro prio No fun_pos
		= (mem_defs, [macro : mem_macros], ca)
	check_symbols_of_class_members [def : _] type_context ca
		= abort "postparse.check_symbols_of_class_members: unknown def"  // <<- def
	check_symbols_of_class_members [] type_context ca
		= ([], [], ca)
	
	reorganise_member_defs :: [MemberDef] Index -> ([DefinedSymbol], [MemberDef], Index)
	reorganise_member_defs mem_defs first_mem_index
		# mem_defs = sort mem_defs
		= determine_indexes_of_class_members mem_defs first_mem_index 0
		
	determine_indexes_of_class_members :: [MemberDef] Index Index -> ([DefinedSymbol], [MemberDef], Index)
	determine_indexes_of_class_members [member=:{me_symb,me_type}:members] first_mem_index mem_offset
		#! (member_symbols, member_defs, last_mem_offset) = determine_indexes_of_class_members members first_mem_index (inc mem_offset)
		= ([{ds_ident = me_symb, ds_index = first_mem_index + mem_offset, ds_arity = me_type.st_arity } : member_symbols],
			[ { member & me_offset = mem_offset } : member_defs], last_mem_offset)
	determine_indexes_of_class_members [] first_mem_index last_mem_offset
		= ([], [], last_mem_offset)

reorganiseDefinitions icl_module [PD_Instance class_instance=:{pi_members,pi_pos} : defs] cons_count sel_count mem_count type_count ca
	# (fun_defs, c_defs, imports, imported_objects, ca) = reorganiseDefinitions icl_module defs cons_count sel_count mem_count type_count ca
	  (mem_defs, ca) = collect_member_instances pi_members ca
	| icl_module || isEmpty mem_defs
		= (fun_defs, { c_defs & def_instances = [{class_instance & pi_members = mem_defs} : c_defs.def_instances] }, imports, imported_objects, ca)
		= (fun_defs, { c_defs & def_instances = [{class_instance & pi_members = []} : c_defs.def_instances] }, imports, imported_objects,
			postParseError pi_pos "instance specifications of members not allowed" ca)
where	  
	collect_member_instances :: [ParsedDefinition] *CollectAdmin -> ([FunDef], *CollectAdmin)
	collect_member_instances [PD_Function pos name is_infix args rhs fun_kind : defs] ca
		# fun_arity = length args
		  prio = if is_infix (Prio NoAssoc 9) NoPrio
		  (bodies, fun_kind, defs, ca) = collectFunctionBodies name fun_arity prio fun_kind defs ca
		  (fun_defs, ca) = collect_member_instances defs ca
		  fun = MakeNewImpOrDefFunction icl_module name fun_arity [{ pb_args = args, pb_rhs = rhs, pb_position = pos } : bodies ] fun_kind prio No pos
		= ([ fun : fun_defs ], ca)
	collect_member_instances [PD_TypeSpec fun_pos fun_name prio type specials : defs] ca
		= case defs of
			[PD_Function pos name is_infix args rhs fun_kind : _]
				| belongsToTypeSpec fun_name prio name is_infix
 					# fun_arity = determineArity args type
  					  (bodies, fun_kind, defs, ca) = collectFunctionBodies name fun_arity prio fun_kind defs ca
		  			  (fun_defs, ca) = collect_member_instances defs ca
					  fun = MakeNewImpOrDefFunction icl_module name fun_arity bodies fun_kind prio type fun_pos
					-> ([ fun : fun_defs ], ca)
			_
				-> collect_member_instances defs (postParseError fun_pos "function body expected" ca)
	collect_member_instances [] ca
	    = ([], ca)	
reorganiseDefinitions icl_module [PD_Instances class_instances : defs] cons_count sel_count mem_count type_count ca
	= reorganiseDefinitions icl_module ([PD_Instance class_instance \\ class_instance <- class_instances] ++ defs) cons_count sel_count mem_count type_count ca
reorganiseDefinitions icl_module [PD_Generic gen : defs] cons_count sel_count mem_count type_count ca
	# 	(fun_defs, c_defs, imports, imported_objects, ca) = reorganiseDefinitions icl_module defs cons_count sel_count mem_count type_count ca
		c_defs = {c_defs & def_generics = [gen : c_defs.def_generics]}
	= (fun_defs, c_defs, imports, imported_objects, ca)
reorganiseDefinitions icl_module [PD_Import new_imports : defs] cons_count sel_count mem_count type_count ca
	# (fun_defs, c_defs, imports, imported_objects, ca) = reorganiseDefinitions icl_module defs cons_count sel_count mem_count type_count ca
	= (fun_defs, c_defs, new_imports ++ imports, imported_objects, ca)
reorganiseDefinitions icl_module [PD_ImportedObjects new_imported_objects : defs] cons_count sel_count mem_count type_count ca
	# (fun_defs, c_defs, imports, imported_objects, ca) = reorganiseDefinitions icl_module defs cons_count sel_count mem_count type_count ca
	= (fun_defs, c_defs, imports, new_imported_objects ++ imported_objects, ca)
reorganiseDefinitions icl_module [def:defs] _ _ _ _ ca
	= abort ("reorganiseDefinitions does not match" ---> def)

reorganiseDefinitions icl_module [] _ _ _ _ ca
	= ([], { def_types = [], def_constructors = [], def_selectors = [], def_macros = [], def_classes = [], def_members = [],
			def_instances = [], def_funtypes = [], /* AA */ def_generics = [] }, [], [], ca)

belongsToTypeSpec name prio new_name is_infix :==
	name == new_name && sameFixity prio is_infix

determineArity :: [ParsedExpr] (Optional SymbolType) -> Int
determineArity args (Yes {st_arity})
	=	st_arity
determineArity args No
	=	length args

sameFixity :: Priority Bool -> Bool
sameFixity (Prio _ _) is_infix
	=	is_infix
sameFixity NoPrio is_infix
	=	not is_infix
