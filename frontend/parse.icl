implementation module parse

import StdEnv
import scanner, syntax, hashtable, utilities, predef, containers, compilerSwitches

ParseOnly :== False

toLineAndColumn {fp_line, fp_col}
	=	{lc_line = fp_line, lc_column = fp_col}

// +++ move to utilities?

groupBy :: (a a -> Bool) [a] -> [[a]]
groupBy eq []
    =   []
groupBy eq [h : t]
    =   [[h : this] : groupBy eq other]
    where
        (this, other)
            =   span (eq h) t

/*

Parser for Clean 2.0

Conventions:

- Parsing funtions with a name of the form try.. can fail without generating an error.
  The parser will try an other alternative.
- Parsing functions with a name of the form want.. should succeed. If these functions
  fail an error message is generated.
- Functions with names containing the character '_' are local functions.
- All functions should consume the tokens taken form the state or given as argument,
  or put these tokens back themselves.
*/

::	*ParseErrorAdmin = 
	{	pea_file	:: !*File
	,	pea_ok		:: !Bool
	}

:: *ParseState =
	{	ps_scanState		:: !ScanState
	,	ps_error			:: !*ParseErrorAdmin
	,	ps_skipping			:: !Bool
	,	ps_hash_table		:: !*HashTable
	,	ps_support_generics :: !Bool // AA: compiler option "-generics"
	}

/*
appScanState :: (ScanState -> ScanState) !ParseState -> ParseState
appScanState f pState=:{ps_scanState}
	#	ps_scanState = f ps_scanState
	=	{	pState & ps_scanState = ps_scanState }
*/
appScanState f pState:==appScanState pState
	where
	appScanState pState=:{ps_scanState}
		#	ps_scanState = f ps_scanState
		=	{	pState & ps_scanState = ps_scanState }

/*
accScanState :: (ScanState -> (.t,ScanState)) !ParseState -> (.t,ParseState)
accScanState f pState=:{ps_scanState}
	#	( x, ps_scanState) = f ps_scanState
	=	( x, {pState & ps_scanState = ps_scanState })
*/
accScanState f pState:== accScanState pState
	where
		accScanState pState=:{ps_scanState}
			#	( x, ps_scanState) = f ps_scanState
			=	( x, {pState & ps_scanState = ps_scanState })

instance getFilename ParseState
where
	getFilename pState = accScanState getFilename pState

makeStringType
	#! string_ident = predefined_idents.[PD_StringType]
	=: TA (MakeNewTypeSymbIdent string_ident 0) []

makeListTypeSymbol :: Int Int -> TypeSymbIdent
makeListTypeSymbol head_strictness arity
	# pre_def_list_index=if (head_strictness==HeadLazy)
							PD_ListType
						(if (head_strictness==HeadStrict)
							PD_StrictListType
							PD_UnboxedListType)
	#! list_ident = predefined_idents.[pre_def_list_index]
	= MakeNewTypeSymbIdent list_ident arity

makeTailStrictListTypeSymbol :: Int Int -> TypeSymbIdent
makeTailStrictListTypeSymbol head_strictness arity
	# pre_def_list_index=if (head_strictness==HeadLazy)
							PD_TailStrictListType
						(if (head_strictness==HeadStrict)
							PD_StrictTailStrictListType
							PD_UnboxedTailStrictListType)
	#! list_ident = predefined_idents.[pre_def_list_index]
	= MakeNewTypeSymbIdent list_ident arity

makeLazyArraySymbol arity
	#! lazy_array_ident = predefined_idents.[PD_LazyArrayType]
	= MakeNewTypeSymbIdent lazy_array_ident arity

makeStrictArraySymbol arity
	#! strict_array_ident = predefined_idents.[PD_StrictArrayType]
	= MakeNewTypeSymbIdent strict_array_ident arity

makeUnboxedArraySymbol arity
	#! unboxed_array_ident = predefined_idents.[PD_UnboxedArrayType]
	= MakeNewTypeSymbIdent unboxed_array_ident arity

makeTupleTypeSymbol form_arity act_arity
	#! tuple_ident = predefined_idents.[GetTupleTypeIndex form_arity]
	= MakeNewTypeSymbIdent tuple_ident act_arity
	
class try a	 :: !Token !*ParseState -> (!Optional a, !*ParseState)
class want a :: !*ParseState -> (!a, !*ParseState)

stringToIdent s i p :== (ident,parse_state)
	where
		({boxed_ident=ident},parse_state) = stringToBoxedIdent s i p

stringToBoxedIdent :: !String !IdentClass !*ParseState -> (!BoxedIdent, !*ParseState)
stringToBoxedIdent ident ident_class pState=:{ps_hash_table}
	# (ident, ps_hash_table) = putIdentInHashTable ident ident_class ps_hash_table
	= (ident, { pState & ps_hash_table = ps_hash_table } )

internalIdent s p :== (ident,parse_state)
	where
		({boxed_ident=ident},parse_state) = internalBoxedIdent s p

internalBoxedIdent :: !String !*ParseState -> (!BoxedIdent, !*ParseState)
internalBoxedIdent prefix pState
	# ({fp_line,fp_col},pState=:{ps_hash_table})	= getPosition pState
	  case_string									= prefix +++ ";" +++ toString fp_line +++ ";" +++ toString fp_col
	  (case_ident, ps_hash_table)					= putIdentInHashTable case_string IC_Expression ps_hash_table
	= (case_ident, { pState & ps_hash_table = ps_hash_table } )

erroneousIdent = { id_name = "", id_info = nilPtr }

/*
	Some general overloaded parsing routines
*/

wantSequence :: !Token !ScanContext !*ParseState -> (!.[a],!*ParseState) | want a
wantSequence separator scanContext pState
	# (first, pState) = want pState
	  (token, pState) = nextToken scanContext pState
	| separator == token
		# (rest, pState) = wantSequence separator scanContext pState
		= ([first : rest], pState)
	// otherwise // separator <> token
	= ([first], tokenBack pState)
/*
optionalSequence start_token separator scanContext pState
	# (token, pState) = nextToken scanContext pState
	| token == start_token
		= wantSequence separator scanContext pState
		= ([], tokenBack pState)
*/
parseList try_fun pState :== parse_list pState // try_fun *
//parseList try_fun pState = parse_list pState
	where
	//	parse_list :: !*ParseState -> (tree, *ParseState)
		parse_list pState
			# (succ, tree, pState) = try_fun pState
			| succ
				# (trees, pState) = parse_list pState
				= ([tree : trees], pState)
			= ([], pState)

//wantSepList msg sep_token scanContext try_fun pState = want_list msg pState
wantSepList msg sep_token scanContext try_fun pState :== want_list msg pState // try_fun (sep_token tryfun)*
	where
		want_list msg pState
			# (succ, tree, pState) = try_fun pState
			| succ
			 	# (token, pState) = nextToken scanContext pState
			 	| token == sep_token
					# (trees, pState) = optSepList sep_token scanContext try_fun pState
					= ([tree : trees], pState)
				// otherwise // token <> sep_token
					= ([tree], tokenBack pState)
				# (token, pState) = nextToken GeneralContext pState
				= ([tree], parseError ("wantList of "+msg) (Yes token) msg pState)

//optSepList sep_token scanContext try_fun pState = want_list msg pState
optSepList sep_token scanContext try_fun pState :== want_list pState // [ try_fun (sep_token tryfun)* ]
	where
		want_list pState
			# (succ, tree, pState) = try_fun pState
			| succ
			 	# (token, pState) = nextToken scanContext pState
			 	| token == sep_token
					# (trees, pState) = want_list pState
					= ([tree : trees], pState)
				// otherwise // token <> sep_token
					= ([tree], tokenBack pState)
			= ([], pState)

//wantList msg try_fun pState = want_list msg pState
wantList msg try_fun pState :== want_list msg pState // try_fun +
	where
		want_list msg pState
			# (succ, tree, pState) = try_fun pState
			| succ
				# (trees, pState) = parseList try_fun pState
				= ([tree : trees], pState)
				# (token, pState) = nextToken GeneralContext pState
				= ([tree], parseError ("wantList of "+msg) (Yes token) msg pState)
/*
instance want (a,b) | want a & want b
where
	want pState
		# (x, pState) = want pState
		  (y, pState) = want pState
		= ((x,y), pState)
*/
wantModuleIdents :: !ScanContext !IdentClass !ParseState -> (![Ident], !ParseState)
wantModuleIdents scanContext ident_class pState
	# (first_name, pState) = wantModuleName pState
	  (first_ident, pState) = stringToIdent first_name ident_class pState
	  (token, pState) = nextToken scanContext pState
	| token == CommaToken
		# (rest, pState) = wantModuleIdents scanContext ident_class pState
		= ([first_ident : rest], pState)
	= ([first_ident], tokenBack pState)

optionalPriority :: !Bool !Token !ParseState -> (Priority, !ParseState)
optionalPriority isinfix (PriorityToken prio) pState
	= (prio, pState)
optionalPriority isinfix token pState
	| isinfix
		= (DummyPriority, tokenBack pState)
		= (NoPrio, tokenBack pState)

/*
	Modules
*/

::	ParseContext			:== Int

cICLContext					:== 1
cGlobalContext				:== 2
cDCLContext					:== 0
cLocalContext				:== 1
cClassOrInstanceDefsContext	:== 4

/*
	A cClassOrInstanceDefsContext is a further restriction on a
	local context, because no local node defs are allowed
	This context stuff is getting far too complicated.
	Possible solution: accept everything in the parser and
	discriminate in postparse, depending on the context.
*/

SetGlobalContext iclmodule
	| iclmodule
		= cICLContext bitor cGlobalContext
		= cDCLContext bitor cGlobalContext

SetLocalContext					parseContext :== parseContext bitand (bitnot cGlobalContext)
SetClassOrInstanceDefsContext	parseContext :== SetLocalContext (parseContext bitor cClassOrInstanceDefsContext)

isLocalContext	parseContext	:== parseContext bitand cGlobalContext == 0
isGlobalContext	parseContext	:== parseContext bitand cGlobalContext <> 0 // not (isLocalContext parseContext)

isDclContext	parseContext	:== parseContext bitand cICLContext == 0
isIclContext	parseContext	:== parseContext bitand cICLContext <> 0	// not (isDclContext parseContext)

isClassOrInstanceDefsContext parseContext			:== parseContext bitand cClassOrInstanceDefsContext <> 0
isGlobalOrClassOrInstanceDefsContext parseContext	:== parseContext bitand (cGlobalContext bitor cClassOrInstanceDefsContext) <> 0

cWantIclFile :== True
cWantDclFile :== False

wantModule :: !Bool !Ident !Position !Bool !*HashTable !*File !SearchPaths (ModTimeFunction *Files) !*Files
	-> (!Bool, !ParsedModule, !*HashTable, !*File, !*Files)
wantModule iclmodule file_id=:{id_name} import_file_position support_generics hash_table error searchPaths modtimefunction files
	= case openScanner file_name searchPaths modtimefunction files of
		(Yes (scanState, modification_time), files)
			# hash_table=set_hte_mark (if iclmodule 1 0) hash_table
			# (ok,mod,hash_table,file,files) = initModule file_name modification_time scanState hash_table error files
			# hash_table=set_hte_mark 0 hash_table
			->(ok,mod,hash_table,file,files)
		(No, files)
			-> let mod = { mod_name = file_id,  mod_modification_time = "", mod_type = MK_None, mod_imports = [], mod_imported_objects = [], mod_defs = [] } in
			  (False, mod, hash_table, error <<< "Error " <<< import_file_position <<< ": "  <<< file_name <<< " could not be imported\n", files)
where
	file_name = if iclmodule (id_name +++ ".icl") (id_name +++ ".dcl")

	initModule :: String String ScanState !*HashTable !*File *Files
				-> (!Bool, !ParsedModule, !*HashTable, !*File, !*Files)
	initModule file_name modification_time scanState hash_table error files
		# (succ, mod_type, mod_name, scanState) = try_module_header iclmodule scanState
		| succ
			# pState				=	{ ps_scanState = scanState
										, ps_error = { pea_file = error, pea_ok = True }
										, ps_skipping = False
										, ps_hash_table = hash_table
										, ps_support_generics = support_generics
										}
			  pState				= verify_name mod_name id_name file_name pState
		  	  (mod_ident, pState)	= stringToIdent mod_name IC_Module pState
		  	  pState				= check_layout_rule pState
		  	  (defs, pState)		= want_definitions (SetGlobalContext iclmodule) pState
// MV ...
			# (defs, pState)		= add_module_id mod_name defs pState;
// ... MV			  				
			  {ps_scanState,ps_hash_table,ps_error}
			  						= pState
			  defs = if (ParseOnly && id_name <> "StdOverloaded" && id_name <> "StdArray" && id_name <> "StdEnum" && id_name <> "StdBool" && id_name <> "StdDynamics" && id_name <> "StdGeneric")
						[PD_Import imports \\ PD_Import imports <- defs]
						defs
			  mod					= { mod_name = mod_ident, mod_modification_time = modification_time, mod_type = mod_type, mod_imports = [], mod_imported_objects = [], mod_defs = defs }
			= ( ps_error.pea_ok
			  , mod, ps_hash_table
			  , ps_error.pea_file
			  , closeScanner ps_scanState files
			  )
		// otherwise // ~ succ
		# ({fp_line}, scanState) = getPosition scanState
		  mod = { mod_name = file_id,  mod_modification_time = modification_time, mod_type = mod_type, mod_imports = [], mod_imported_objects = [], mod_defs = [] }
		= (False, mod, hash_table, error <<< "Error [" <<< file_name <<< ',' <<< fp_line <<< "]: incorrect module header",
			closeScanner scanState files)
	where
// MV...
		add_module_id mod_name defs pState
			| not iclmodule
				= (defs,pState);
	
			// It is essential that the type name denoted by ident is an unique type name within the application. Otherwise
			// the static linker will choose one implementation (because the type names are equal) and map the other to the
			// chosen implementation.
			// The zero arity of the _Module constructor makes the code generator, pre-allocate _Module in .data section of
			// the final executable. The module name needed by the dynamic run-time system can then be determined by looking
			// at the descriptor. If however all implementations were mapped to a single one, the dynamic rts could not use
			// the module name anymore because they are all the same.
			# (ident,   pState)	= stringToIdent ("_" +++ mod_name +++ "_Module") IC_Type pState
			# td				= MakeTypeDef ident [] (ConsList []) TA_None [] NoPos
				
			# (pc_cons_name, pState) = stringToIdent "__Module" IC_Expression pState
			# cons
				= { 
					pc_cons_name		= pc_cons_name
				,	pc_arg_types		= []
				,	pc_args_strictness	= NotStrict
				,	pc_cons_arity		= 0
				,	pc_cons_prio		= NoPrio
				,	pc_exi_vars			= []
				,	pc_cons_pos			= NoPos
				}
			# td
				= { td & td_rhs = ConsList [cons] }
			= ([PD_Type td:defs],pState) 
// ...MV

	try_module_header :: !Bool !ScanState -> (!Bool,!ModuleKind,!String,!ScanState)
	try_module_header is_icl_mod scanState
		# (token, scanState) = nextToken GeneralContext scanState
		| is_icl_mod
			| token == ModuleToken
				# (token, scanState) = nextToken GeneralContext scanState
				= try_module_name token MK_Main scanState
			| token == ImpModuleToken 
				= try_module_token MK_Module scanState
			| token == SysModuleToken
				= try_module_token MK_System scanState
				= (False, MK_None, "", tokenBack scanState)
		| token == DefModuleToken
		  	= try_module_token MK_Module scanState
		| token == SysModuleToken
		  	= try_module_token MK_System scanState
			= (False, MK_None, "", tokenBack scanState)

	try_module_token :: !ModuleKind !ScanState -> (!Bool,!ModuleKind!,!String,!ScanState)
	try_module_token mod_type scanState
		# (token, scanState) = nextToken GeneralContext scanState
		| token == ModuleToken
			# (token, scanState) = nextToken GeneralContext scanState
 			= try_module_name token mod_type scanState
			= (False, mod_type, "", tokenBack scanState)

	try_module_name (IdentToken name) mod_type scanState
		= (True, mod_type, name, scanState)
	try_module_name (UnderscoreIdentToken name) mod_type scanState
		= (True, mod_type, name, setUseUnderscoreIdents True scanState)
	try_module_name token mod_type scanState
		= (False, mod_type, "", tokenBack scanState)
	
	verify_name name id_name file_name pState
		| name == id_name
	  		= pState
			# ({fp_line}, pState=:{ps_error={pea_file}}) = getPosition pState
 			  pea_file = pea_file <<< '[' <<< file_name <<< ',' <<< fp_line <<< "]: module name \"" <<< name 
	  						<<< "\" does not match file name: \"" <<< file_name <<<"\"\n"
			= { pState & ps_error = { pea_file = pea_file, pea_ok = False }}

	check_layout_rule pState
		# (token, pState)	= nextToken GeneralContext pState
		  use_layout		= token <> SemicolonToken && token <> EndOfFileToken // '&& token <> EndOfFileToken' to handle end groups of empty modules
		| use_layout		= appScanState (setUseLayout use_layout) (tokenBack pState)
							= appScanState (setUseLayout use_layout) pState

	want_definitions :: !ParseContext !ParseState -> (![ParsedDefinition], !ParseState)
	want_definitions parseContext pState
		= want_acc_definitions [] pState
	where
		want_acc_definitions :: ![ParsedDefinition] !ParseState -> (![ParsedDefinition], !ParseState)
		want_acc_definitions acc pState
			# (defs, pState)	= wantDefinitions parseContext pState
			  acc				= acc ++ defs
			  pState			= wantEndModule pState
			  (token, pState)	= nextToken FunctionContext pState
			| token == EndOfFileToken
				= (acc,  pState)
				# pState		= parseError "want definitions" (Yes token) "End of file" pState
				  pState		= wantEndOfDefinition "definitions" pState
				= want_acc_definitions acc pState
/*
	[Definition] on local and global level
*/

wantDefinitions :: !ParseContext !ParseState -> (![ParsedDefinition], !ParseState)
wantDefinitions parseContext pState
	= parseList (tryDefinition parseContext) pState

DummyPriority	:== Prio LeftAssoc 9

cHasPriority 	:== True
cHasNoPriority	:== False

tryDefinition :: !ParseContext !ParseState -> (!Bool, ParsedDefinition, !ParseState)
tryDefinition parseContext pState
	# (token, pState)			= nextToken GeneralContext pState
	  (fname, linenr, pState)	= getFileAndLineNr pState
	= try_definition parseContext token (LinePos fname linenr) pState
where
	try_definition :: !ParseContext !Token !Position !ParseState -> (!Bool, ParsedDefinition, !ParseState)
	try_definition parseContext DoubleColonToken pos pState
		| ~(isGlobalContext parseContext)
			= (False,abort "no def(3)",parseError "definition" No "type definitions only at the global level" (tokenBack pState))
			# (def, pState) = wantTypeDef parseContext pos pState
			= (True, def, pState)
	try_definition _ ImportToken pos pState
		| ~(isGlobalContext parseContext)
			= (False,abort "no def(3)",parseError "definition" No "imports only at the global level" pState)
		# (token, pState) = nextToken FunctionContext pState
		| token == CodeToken && isIclContext parseContext
		# (importedObjects, pState) = wantCodeImports pState
		= (True, PD_ImportedObjects importedObjects, pState)
		# pState = tokenBack pState
		# (imports, pState) = wantImports pState
   		= (True, PD_Import imports, pState)
	try_definition _ FromToken pos pState
		| ~(isGlobalContext parseContext)
			= (False,abort "no def(3)",parseError "definition" No "imports only at the global level" pState)
			# (imp, pState) = wantFromImports pState
	   		= (True, PD_Import [imp], pState) -->> imp
/*	try_definition _ ExportToken pos pState
		# (exports, pState) = wantExportDef pState
   		= (True, PD_Export exports, pState)
	try_definition _ ExportAllToken pos pState
   		= (True, PD_Export ExportAll, pState)
*/	try_definition parseContext ClassToken pos pState
		| ~(isGlobalContext parseContext)
			= (False,abort "no def(2)",parseError "definition" No "class definitions are only at the global level" pState)
	   		# (classdef, pState) = wantClassDefinition parseContext pos pState
	   		= (True, classdef, pState)
	// AA..
	try_definition parseContext GenericToken pos pState
		| ~(isGlobalContext parseContext)
			= (False,abort "no def(2)",parseError "definition" No "generic definitions are only at the global level" pState)
	   		# (gendef, pState) = wantGenericDefinition parseContext pos pState
	   		= (True, gendef, pState)
	
	try_definition parseContext DeriveToken pos pState
		| ~(isGlobalContext parseContext)
			= (False,abort "no def(2)",parseError "definition" No "derive declarations are only at the global level" pState)   		
	   		# (gendef, pState) = wantDeriveDefinition parseContext pos pState
	   		= (True, gendef, pState)
	// ..AA 
	 		
	try_definition parseContext InstanceToken pos pState
		| ~(isGlobalContext parseContext)
			= (False,abort "no def(2)",parseError "definition" No "instance declarations are only at the global level" pState)
	   		# (instdef, pState) = wantInstanceDeclaration parseContext pos pState
	   		= (True, instdef, pState)

// AA : new syntax for generics ...
	try_definition parseContext (IdentToken name) pos pState
		# (token, pState) = nextToken FunctionContext pState
		= case token of
			GenericOpenToken // generic function
				# (type, pState) = wantType pState
				# (ident, pState) = stringToIdent name (IC_GenericCase type) pState				
				# (type_CONS_ident, pState) = stringToIdent "CONS" IC_Type pState
				# (type_FIELD_ident, pState)= stringToIdent "FIELD" IC_Type pState
				# (generic_ident, pState) = stringToIdent name IC_Generic pState					

				# (type_cons, pState) = get_type_cons type pState
					with
						get_type_cons (TA type_symb []) pState
								= (TypeConsSymb type_symb, pState)							
						get_type_cons (TA type_symb _) pState
							# pState = parseError "generic type, no constructor arguments allowed" No " |}" pState
							= (abort "no TypeCons", pState)
						get_type_cons (TB tb) pState 
							= (TypeConsBasic tb, pState)
						get_type_cons TArrow pState
							= (TypeConsArrow, pState)				 
						get_type_cons (TV tv) pState
							= (TypeConsVar tv, pState)				 
						get_type_cons _ pState 
							# pState = parseError "generic type" No " |}" pState
							= (abort "no TypeCons", pState)

				# (token, pState) = nextToken GenericContext pState
				# (geninfo_arg, pState) = case token of
					GenericOfToken
						# (ok, geninfo_arg, pState) = trySimpleLhsExpression pState
						# pState = wantToken FunctionContext "type argument" GenericCloseToken pState
						| ok 
							-> case type_cons of
								(TypeConsSymb {type_name})
									| type_name == type_CONS_ident
										# (cons_CONS_ident, pState) = stringToIdent "GenericConsInfo" IC_Expression pState 
										-> (PE_List [PE_Ident cons_CONS_ident, geninfo_arg], pState)
									| type_name == type_FIELD_ident 
										# (cons_FIELD_ident, pState) = stringToIdent "GenericFieldInfo" IC_Expression pState 
										-> (PE_List [PE_Ident cons_FIELD_ident, geninfo_arg], pState) 	
									| otherwise
										-> (geninfo_arg, pState)
						| otherwise
							# pState = parseError "generic case" No "simple lhs expression" pState
							-> (PE_Empty, pState)
						 
					GenericCloseToken
						# (geninfo_ident, pState) =  stringToIdent "geninfo" IC_Expression pState
						-> (PE_Ident geninfo_ident, pState)
					_ 	
						# pState = parseError "generic type" (Yes token) "of or |}" pState
						# (geninfo_ident, pState) =  stringToIdent "geninfo" IC_Expression pState
						-> (PE_Ident geninfo_ident, pState)
																						
				//# pState = wantToken FunctionContext "type argument" GenericCloseToken pState
				# (args, pState) = parseList trySimpleLhsExpression pState

				//# (geninfo_ident, pState) = stringToIdent "geninfo" IC_Expression pState
				# args = SwitchGenericInfo [geninfo_arg :  args] args

				// must be EqualToken or HashToken or ???
				//# pState = wantToken FunctionContext "generic definition" EqualToken pState
				//# pState = tokenBack pState

			  	# (ss_useLayout, pState) = accScanState UseLayout pState
			    # localsExpected = isNotEmpty args || isGlobalContext parseContext || ~ ss_useLayout
			    # (rhs, _, pState) = wantRhs localsExpected (ruleDefiningRhsSymbol parseContext) pState

				# generic_case = 
					{ gc_name = ident
					, gc_gname = generic_ident
					, gc_generic = {gi_module=NoIndex,gi_index=NoIndex}
					, gc_arity = length args
					, gc_pos = pos
					, gc_type = type
					, gc_type_cons = type_cons
					, gc_body = GCB_ParsedBody args rhs
					, gc_kind = KindError	
					}					
				-> (True, PD_GenericCase generic_case, pState)
			_   // normal function
				# pState = tokenBack pState
				# (lhs, pState) = want_lhs_of_def (IdentToken name) pState
			      (token, pState) = nextToken FunctionContext pState
			      (def, pState) = want_rhs_of_def parseContext lhs token (determine_position lhs pos) pState
				-> (True, def, pState)
// ... AA
	   		
	try_definition parseContext token pos pState
		| isLhsStartToken token
			# (lhs, pState) = want_lhs_of_def token pState
		      (token, pState) = nextToken FunctionContext pState
		      (def, pState) = want_rhs_of_def parseContext lhs token (determine_position lhs pos) pState
			= (True, def, pState)
		= (False, abort "no def(1)", tokenBack pState)

	determine_position (Yes (name, _), _)	(LinePos f l) = FunPos f l name.id_name
	determine_position lhs           		pos           = pos

	want_lhs_of_def :: !Token !ParseState -> (!(Optional (Ident, Bool), ![ParsedExpr]), !ParseState)
	want_lhs_of_def token pState
		# (succ, fname, is_infix, pState) = try_function_symbol token pState
		| succ
			# (args, pState) = parseList trySimpleLhsExpression pState
			= ((Yes (fname, is_infix), args), pState)
			# (_, exp, pState) = trySimpleLhsExpression pState
			= ((No, [exp]), pState)
	where
		try_function_symbol :: !Token !ParseState -> (!Bool, Ident, !Bool, !ParseState) // (Success, Ident, Infix, ParseState)
		try_function_symbol (IdentToken name) pState
			# (id, pState) = stringToIdent name IC_Expression pState
			= (True, id, False, pState)
		try_function_symbol OpenToken pState
			# (token, pState) = nextToken FunctionContext pState
			= case token of
				(IdentToken name)
					# (token, pState) = nextToken FunctionContext pState
					| CloseToken == token
						# (id, pState) = stringToIdent name IC_Expression pState
						-> (True, id, True, pState)
						-> (False, abort "no name", False, tokenBack (tokenBack (tokenBack pState)))
				_
					-> (False,  abort "no name", False, tokenBack (tokenBack pState))
		try_function_symbol token pState
			= (False, abort "name", False, tokenBack pState)

	want_rhs_of_def :: !ParseContext !(Optional (Ident, Bool), [ParsedExpr]) !Token !Position !ParseState -> (ParsedDefinition, !ParseState)
	want_rhs_of_def parseContext (opt_name, args) DoubleColonToken pos pState
		# (name, is_infix, pState) = check_name_and_fixity opt_name cHasNoPriority pState
		  (tspec, pState) = want pState		//	SymbolType
		| isDclContext parseContext
			# (specials, pState) = optionalSpecials pState
			= (PD_TypeSpec pos name (if is_infix DummyPriority NoPrio) (Yes tspec) specials, wantEndOfDefinition "type definition (1)" pState)
			= (PD_TypeSpec pos name (if is_infix DummyPriority NoPrio) (Yes tspec) SP_None, wantEndOfDefinition "type definition (2)" pState)
	want_rhs_of_def parseContext (opt_name, args) (PriorityToken prio) pos pState
		# (name, _, pState) = check_name_and_fixity opt_name cHasPriority pState
		  (token, pState) = nextToken TypeContext pState
		| token == DoubleColonToken
		  	# (tspec, pState) = want pState
			| isDclContext parseContext
				# (specials, pState) = optionalSpecials pState
				= (PD_TypeSpec pos name prio (Yes tspec) specials, wantEndOfDefinition "type definition (3)" pState)
				= (PD_TypeSpec pos name prio (Yes tspec) SP_None, wantEndOfDefinition "type definition (4)" pState)
			= (PD_TypeSpec pos name prio No SP_None, wantEndOfDefinition "type defenition (5)" (tokenBack pState))
	want_rhs_of_def parseContext (No, args) token pos pState
		# pState			= want_node_def_token pState token
		# (ss_useLayout, pState) = accScanState UseLayout pState
		  localsExpected	= ~ ss_useLayout
		  (rhs, _, pState)		= wantRhs localsExpected (ruleDefiningRhsSymbol parseContext) (tokenBack pState)
		| isGlobalContext parseContext
 			= (PD_NodeDef pos (combine_args args) rhs, parseError "RHS" No "<global definition>" pState)
 			= (PD_NodeDef pos (combine_args args) rhs, pState)
	where		
		want_node_def_token s EqualToken		= s
		want_node_def_token s DefinesColonToken = s // PK replaceToken EqualToken s
		want_node_def_token s token				= parseError "RHS" (Yes token) "defines token (= or =:)" s

		combine_args [arg]	= arg
		combine_args args	= PE_List args
	want_rhs_of_def parseContext (Yes (name, False), []) definingToken pos pState
		# code_allowed  = definingToken == EqualToken
		| isIclContext parseContext && isLocalContext parseContext && (definingToken == EqualToken || definingToken == DefinesColonToken) &&
		/* PK isLowerCaseName name.id_name && */ not (isClassOrInstanceDefsContext parseContext)
		  	# (token, pState) = nextToken FunctionContext pState
			| code_allowed && token == CodeToken
				# (rhs, pState) = wantCodeRhs pState
				= (PD_Function pos name False [] rhs (FK_Function cNameNotLocationDependent), pState)
			# pState = tokenBack pState
			# (rhs, _, pState) = wantRhs False (RhsDefiningSymbolExact definingToken) (tokenBack pState)
			| token == EqualToken
				= (PD_Function pos name False [] rhs FK_NodeDefOrFunction, pState)
			// otherwise // token == DefinesColonToken
 				| isGlobalContext parseContext
					= (PD_Function pos name False [] rhs FK_Caf, pState)
				// otherwise
					= (PD_NodeDef pos (PE_Ident name) rhs, pState)
	want_rhs_of_def parseContext (Yes (name, is_infix), args) token pos pState
		# code_allowed  = token == EqualToken || token == DoubleArrowToken
		  (token, pState) = nextToken FunctionContext pState
		| isIclContext parseContext && token == CodeToken
			# (rhs, pState) = wantCodeRhs pState
			| code_allowed
				= (PD_Function pos name is_infix args rhs (FK_Function cNameNotLocationDependent), pState)
			// otherwise // ~ code_allowed
				= (PD_Function pos name is_infix args rhs (FK_Function cNameNotLocationDependent), parseError "rhs of def" No "no code" pState)
		# pState = tokenBack (tokenBack pState)
		  (ss_useLayout, pState) = accScanState UseLayout pState
		  localsExpected = isNotEmpty args || isGlobalContext parseContext || ~ ss_useLayout
		  (rhs, defining_symbol, pState)
		  		= wantRhs localsExpected (ruleDefiningRhsSymbol parseContext) pState
		  fun_kind = definingSymbolToFunKind defining_symbol
		= case fun_kind of
			FK_Function _  | isDclContext parseContext
				->	(PD_Function pos name is_infix args rhs fun_kind, parseError "RHS" No "<type specification>" pState)
			FK_Caf | isNotEmpty args
				->	(PD_Function pos name is_infix []   rhs fun_kind, parseError "CAF" No "No arguments for a CAF" pState)
			_	->	(PD_Function pos name is_infix args rhs fun_kind, pState)
	check_name_and_fixity No hasprio pState
		= (erroneousIdent, False, parseError "Definition" No "identifier" pState)
	check_name_and_fixity (Yes (name,is_infix)) hasprio pState
		| not is_infix	&& hasprio
			= (name, False, parseError "Definition" No "Infix operator should be inside parentheses; no infix" pState)
			= (name, is_infix, pState)
/*
isEqualToken :: !Token -> Bool
isEqualToken EqualToken			= True
isEqualToken _					= False
*/
/*
isRhsStartToken :: !ParseContext !Token -> Bool
isRhsStartToken parseContext EqualToken			= True
isRhsStartToken parseContext ColonDefinesToken	= isGlobalOrClassOrInstanceDefsContext parseContext
isRhsStartToken parseContext DefinesColonToken	= True
isRhsStartToken parseContext DoubleArrowToken	= True // PK
isRhsStartToken parseContext _					= False
*/

optionalSpecials :: !ParseState -> (!Specials, !ParseState)
optionalSpecials pState
	# (token, pState) = nextToken TypeContext pState
	| token == SpecialToken
		# (token, pState) = nextToken GeneralContext pState
		  pState = begin_special_group token pState
		# (specials, pState) = wantList "<special statement>" try_substitutions pState
		= (SP_ParsedSubstitutions specials, end_special_group pState)
	// otherwise // token <> SpecialToken
		= (SP_None, tokenBack pState)
where
	try_substitutions pState
		# (succ, type_var, pState) = tryTypeVar pState
		| succ
			# (subst, pState) = want_rest_substitutions type_var pState
			= (True, subst, wantEndOfDefinition "substitution" pState)
			= (False, [], pState)
	
	want_rest_substitutions type_var pState
		# pState = wantToken GeneralContext "specials" EqualToken pState
		  (type, pState) = want pState
		  (token, pState) = nextToken GeneralContext pState
		| token == CommaToken
			# (next_type_var, pState) = want pState
			  (substs, pState) = want_rest_substitutions next_type_var pState
			= ([{ bind_src = type, bind_dst = type_var } : substs], pState)
			= ([{ bind_src = type, bind_dst = type_var }], tokenBack pState)

	begin_special_group token pState // For JvG layout
		# (token, pState)
			= case token of
				SemicolonToken	->	nextToken TypeContext pState
				_				->	(token, pState)
		# (ss_useLayout, pState) = accScanState UseLayout pState
		| ss_useLayout
			| token == CurlyOpenToken 
				= parseError "substitution" (Yes CurlyOpenToken) "in layout mode the keyword where is" pState
			// otherwise
				= tokenBack pState
		// not ss_useLayout
			| token == CurlyOpenToken 
				= pState
			// otherwise
				= tokenBack (parseError "substitution" (Yes token) "{" pState) 

	end_special_group pState
		# (ss_useLayout, pState) = accScanState UseLayout pState
		  (token, pState) = nextToken FunctionContext pState
		| token == EndOfFileToken && ss_useLayout
			= tokenBack pState
		| ss_useLayout
			= case token of
				EndGroupToken	->	pState
				_				->	parseError "substitution" (Yes token) "end of substitution with layout" pState
		// ~ ss_useLayout
		| token == CurlyCloseToken
			= pState
		// otherwise // token <> CurlyCloseToken
			= parseError "substitution" (Yes token) "end of substitution with layout, }," pState

/*
	For parsing right-hand sides of functions only
*/

wantCodeRhs :: !ParseState -> (Rhs, !ParseState)
wantCodeRhs pState
	# (expr, pState)	= want_code_expr pState
	  (file_name, line_nr, pState)	= getFileAndLineNr pState
	= (	{ rhs_alts		= UnGuardedExpr
							{ ewl_nodes		= []
							, ewl_locals	= LocalParsedDefs []
							, ewl_expr		= expr
							, ewl_position	= LinePos file_name line_nr
							}
		, rhs_locals	= LocalParsedDefs []
		}
	  , wantEndCodeRhs pState
	  )
where
	want_code_expr :: !ParseState -> (!ParsedExpr, !ParseState)
	want_code_expr pState
		# (token, pState) = nextToken CodeContext pState
		= case token of
			OpenToken
				#	(input, pState)	= want_bindings [] True pState
					pState			= wantToken CodeContext "input bindings of code block" CloseToken pState
					pState			= wantToken CodeContext "output bindings of code block" OpenToken pState
					(out, pState)	= want_bindings [] False pState
					pState			= wantToken CodeContext "output bindings of code block" CloseToken pState
					(token, pState)	= nextToken CodeContext pState
				->	case token of
						CodeBlockToken the_code
							-> (PE_Any_Code input out the_code, pState)
						_	-> (PE_Any_Code input out []  , parseError "code rhs (any code)" (Yes token) "code block" pState)
			InlineToken
			 	#	(token, pState) = nextToken CodeContext pState
			 	->	case token of
			 			CodeBlockToken the_code
			 				-> (PE_ABC_Code the_code True, pState)
			 			token
			 				-> (PE_ABC_Code [] True,  parseError "inline code" (Yes token) "code block" pState)
			CodeBlockToken the_code
				-> (PE_ABC_Code the_code False, pState)
			token
				-> (PE_Empty, parseError "code rhs" (Yes token) "<code rhs>" pState)

	want_bindings :: !(CodeBinding Ident) !Bool !ParseState -> (!CodeBinding Ident, !ParseState)
	want_bindings acc mayBeEmpty pState
		# (token, pState)	= nextToken CodeContext pState
		= case token of
			IdentToken name
				#	(token, pState)	= nextToken CodeContext pState
				|	token == EqualToken || token == DefinesColonToken
					#	(token, pState)	= nextToken CodeContext pState
					->	case token of
							IdentToken value
								#	(ident, pState)	= stringToIdent name IC_Expression pState
									acc				= [{ bind_dst = ident, bind_src = value }: acc]
									(token, pState)	= nextToken CodeContext pState
								|	token == CommaToken
									->	want_bindings acc mayBeEmpty pState
								//	token <> CommaToken
									->	(reverse acc, tokenBack pState)
							token
								-> (acc, parseError "bindings in code block" (Yes token) "value" pState)
				//	token <> EqualToken && token <> DefinesColonToken
					->	(acc, parseError "bindings in code block" (Yes token) "= or =:" pState)
			CloseToken
				| mayBeEmpty
					-> (acc, tokenBack pState) // to handle empty input bindings
					-> (acc, parseError "code bindings" (Yes token) "output bindings" pState)
			token
				-> (acc, parseError "bindings in code block" (Yes token) "identifier" pState)
/*
	For parsing right-hand sides of functions and case expressions
*/
/* Syntax:
	FunctionAltDefRhs	=	FunctionBody						// Rhs
							[ LocalFunctionAltDefs ]
	FunctionBody		=	exprWithLocals						// OptGuardedAlts	: GuardedAlts
						|	GuardedAlts 						//					: UnGuardedExpr
	GuardedAlts			=	{ [ LetBefore ] '|' [ StrictLet ] Guard FunctionBody }+ [ ExprWithLocals ]
	ExprWithLocals		=	[ LetBefore ] sep RootExpression endOfDefinition [ LocalFunctionDefs ]
*/


isRhsStartToken :: !ParseContext !Token -> Bool
isRhsStartToken parseContext EqualToken			= True
isRhsStartToken parseContext ColonDefinesToken	= isGlobalOrClassOrInstanceDefsContext parseContext
isRhsStartToken parseContext DefinesColonToken	= True
isRhsStartToken parseContext DoubleArrowToken	= True // PK
isRhsStartToken parseContext _					= False

:: RhsDefiningSymbol
	=	RhsDefiningSymbolExact Token
	|	RhsDefiningSymbolCase			// '->' or '='
	|	RhsDefiningSymbolRule			// '=', '=:', '=>'
	|	RhsDefiningSymbolRuleOrMacro	// '=', '=:', '=>', ':=='

ruleDefiningRhsSymbol :: !ParseContext -> RhsDefiningSymbol
ruleDefiningRhsSymbol parseContext
	| isGlobalOrClassOrInstanceDefsContext parseContext
		=	RhsDefiningSymbolRuleOrMacro
	// otherwise
		=	RhsDefiningSymbolRule

isDefiningSymbol :: RhsDefiningSymbol Token -> Bool
isDefiningSymbol (RhsDefiningSymbolExact wanted) observed
	=	wanted == observed
isDefiningSymbol RhsDefiningSymbolCase observed
	=	observed == EqualToken || observed == ArrowToken
isDefiningSymbol RhsDefiningSymbolRule observed
	=	observed == EqualToken || observed == DefinesColonToken || observed == DoubleArrowToken
isDefiningSymbol RhsDefiningSymbolRuleOrMacro observed
	=	observed == ColonDefinesToken || isDefiningSymbol RhsDefiningSymbolRule observed

definingSymbolToFunKind :: RhsDefiningSymbol -> FunKind
definingSymbolToFunKind (RhsDefiningSymbolExact defining_token)
	=	definingTokenToFunKind defining_token
definingSymbolToFunKind _
	=	FK_Unknown

definingTokenToFunKind :: Token -> FunKind
definingTokenToFunKind ColonDefinesToken
	=	FK_Macro
definingTokenToFunKind EqualToken
	=	FK_Function cNameNotLocationDependent
definingTokenToFunKind DoubleArrowToken
	=	FK_Function cNameNotLocationDependent
definingTokenToFunKind DefinesColonToken
	=	FK_Caf
definingTokenToFunKind _
	=	FK_Unknown

wantRhs :: !Bool !RhsDefiningSymbol !ParseState -> (!Rhs, !RhsDefiningSymbol, !ParseState) // FunctionAltDefRhs
wantRhs localsExpected definingSymbol pState
	# (alts, definingSymbol, pState)	= want_LetsFunctionBody definingSymbol pState
	  (locals, pState)	= optionalLocals WhereToken localsExpected pState
	= ({ rhs_alts = alts, rhs_locals = locals}, definingSymbol, pState)
where
	want_LetsFunctionBody :: !RhsDefiningSymbol  !ParseState -> (!OptGuardedAlts, !RhsDefiningSymbol, !ParseState) 
	want_LetsFunctionBody definingSymbol pState
		# (token, pState)			= nextToken FunctionContext pState
		  (nodeDefs, token, pState)	= want_LetBefores token pState
		= want_FunctionBody token nodeDefs [] definingSymbol pState

	want_FunctionBody :: !Token ![NodeDefWithLocals] ![GuardedExpr] !RhsDefiningSymbol !ParseState -> (!OptGuardedAlts, !RhsDefiningSymbol, !ParseState)
	want_FunctionBody BarToken nodeDefs alts definingSymbol pState
//		#	(lets, pState)				= want_StrictLet pState // removed from 2.0
		#	(file_name, line_nr, pState)= getFileAndLineNr pState
			(token, pState)				= nextToken FunctionContext pState
		|	token == OtherwiseToken
			#	(token, pState)				= nextToken FunctionContext pState
				(nodeDefs2, token, pState)	= want_LetBefores token pState
			= want_FunctionBody token (nodeDefs ++ nodeDefs2) alts definingSymbol pState // to allow | otherwise | c1 = .. | c2 = ..
/* PK ??? 
			=	case token of
				BarToken
					#	pState = parseError "RHS: default alternative" No "root expression instead of guarded expression" pState
					->	root_expression True token (nodeDefs ++ nodeDefs2) (reverse alts) sep pState
				_	->	root_expression True token (nodeDefs ++ nodeDefs2) (reverse alts) sep pState
*/		|	token == LetToken True
			#	pState	= parseError "RHS" No "No 'let!' in this version of Clean" pState
			=	root_expression True token nodeDefs (reverse alts) definingSymbol pState
		#	(guard, pState)				= wantRhsExpressionT token pState
			(token, pState)				= nextToken FunctionContext pState
			(nodeDefs2, token, pState)	= want_LetBefores token pState
		|	token == BarToken // nested guard
			#	(position, pState)			= getPosition pState
				offside						= position.fp_col
				(expr, definingSymbol, pState)
											= want_FunctionBody token nodeDefs2 [] definingSymbol pState
				pState						= wantEndNestedGuard (default_found expr) offside pState
				alt							= { alt_nodes = nodeDefs, alt_guard = guard, alt_expr = expr,
												alt_ident = guard_ident line_nr, alt_position = LinePos file_name line_nr }
				(token, pState)				= nextToken FunctionContext pState
				(nodeDefs, token, pState)	= want_LetBefores token pState
			=	want_FunctionBody token nodeDefs [alt:alts] definingSymbol pState
		// otherwise
			#	(expr, definingSymbol, pState)
											= root_expression True token nodeDefs2 [] definingSymbol pState
				alt							= { alt_nodes = nodeDefs, alt_guard = guard, alt_expr = expr,
												alt_ident = guard_ident line_nr, alt_position = LinePos file_name line_nr }
				(token, pState)				= nextToken FunctionContext pState
				(nodeDefs, token, pState)	= want_LetBefores token pState
			=	want_FunctionBody token nodeDefs [alt:alts] definingSymbol pState
	  where
	  	guard_ident line_nr
			= { id_name = "_g;" +++ toString line_nr +++ ";", id_info = nilPtr }
	want_FunctionBody token nodeDefs alts definingSymbol pState
		=	root_expression localsExpected token nodeDefs (reverse alts) definingSymbol pState

	root_expression :: !Bool !Token ![NodeDefWithLocals] ![GuardedExpr] !RhsDefiningSymbol !ParseState -> (!OptGuardedAlts, !RhsDefiningSymbol, !ParseState)
	root_expression withExpected token nodeDefs alts definingSymbol pState
		# (optional_expr,definingSymbol,pState) = want_OptExprWithLocals withExpected token nodeDefs definingSymbol pState
		= build_root token optional_expr alts nodeDefs definingSymbol pState
	where
		build_root :: !Token !(Optional ExprWithLocalDefs) ![GuardedExpr] ![NodeDefWithLocals] !RhsDefiningSymbol !ParseState -> (!OptGuardedAlts, !RhsDefiningSymbol, !ParseState)
		build_root _ (Yes expr) [] _ definingSymbol pState
			= ( UnGuardedExpr expr, definingSymbol, pState)
		build_root _ No alts=:[_:_] [] definingSymbol pState
			= (GuardedAlts alts No, definingSymbol, pState)
		build_root _ optional_expr alts=:[_:_] _ definingSymbol pState
			= (GuardedAlts alts optional_expr, definingSymbol, pState)
		build_root token _ _ _ definingSymbol pState
			# (file_name, line_nr, pState)	= getFileAndLineNr pState
			=	(UnGuardedExpr {ewl_nodes = [], ewl_expr = PE_Empty, ewl_locals = LocalParsedDefs [],
												ewl_position = LinePos file_name line_nr}
							, definingSymbol
							, parseError "RHS: root expression" (Yes token) "= <ExprWithLocals>" pState
							)

	default_found (GuardedAlts _ No)	= False
	default_found _						= True

	want_OptExprWithLocals :: !Bool !Token ![NodeDefWithLocals] !RhsDefiningSymbol !ParseState -> (!Optional !ExprWithLocalDefs, !RhsDefiningSymbol, !ParseState)
//	want_OptExprWithLocals withExpected DoubleArrowToken nodeDefs pState
//		= want_OptExprWithLocals True EqualToken nodeDefs (replaceToken EqualToken pState)
	want_OptExprWithLocals withExpected token nodeDefs definingSymbol pState
		| isDefiningSymbol definingSymbol token
		# (file_name, line_nr, pState)	= getFileAndLineNr pState
		  (expr, pState)	= wantExpression cIsNotAPattern pState
		  pState			= wantEndRootExpression pState
		  (locals,pState)	= optionalLocals WithToken withExpected pState
		= ( Yes	{ ewl_nodes		= nodeDefs
				, ewl_expr		= expr
				, ewl_locals	= locals
				, ewl_position	= LinePos file_name line_nr
				}
		  , RhsDefiningSymbolExact token
		  , pState
		  )
		= (No, definingSymbol, tokenBack pState)


/*	want_StrictLet :: !ParseState -> ([NodeDefWithLocals] , !ParseState) // Removed from the language !?
	want_StrictLet pState
		# (token, pState)	= nextToken FunctionContext pState
		| token == LetToken True
			# (let_defs, pState)	= wantList "<sequential node defs>" (try_LetDef True) pState
			  pState				= wantToken FunctionContext "strict let" InToken pState
			= (let_defs, pState)
		= ([], tokenBack pState)
*/ 
	want_LetBefores :: !Token !ParseState -> (![NodeDefWithLocals], !Token, !ParseState)
	want_LetBefores (SeqLetToken strict) pState
		# (let_defs, pState)				= wantList "<sequential node defs>" (try_LetDef strict) pState
		  (token, pState)					= nextToken FunctionContext pState
		  (token, pState)					= opt_End_Group token pState
		  (more_let_defs, token, pState)	= want_LetBefores token pState
		= (let_defs ++ more_let_defs, token, pState)
		where
			opt_End_Group token pState
			 #	(ss_useLayout, pState) = accScanState UseLayout pState
			 |	ss_useLayout
			 	| token == EndGroupToken
			 		= nextToken FunctionContext pState
			 	// otherwise // token <> EndGroupToken
			 		= (ErrorToken "End group missing in let befores", parseError "RHS: Let befores" (Yes token) "Generated End Group (due to layout)" pState)
			 |	otherwise // not ss_useLayout
			 =	(token, pState)
	want_LetBefores token pState
		= ([], token, pState)
	
	try_LetDef :: !Bool !ParseState -> (!Bool, NodeDefWithLocals, !ParseState)
	try_LetDef strict pState
		# (succ, lhs_exp, pState)	= trySimpleLhsExpression pState
		| succ
			# pState			= wantToken FunctionContext "let definition" EqualToken pState
			  (file_name, line_nr, pState)
			  					= getFileAndLineNr pState
			  (rhs_exp, pState) = wantExpression cIsNotAPattern pState
			  pState			= wantEndRootExpression pState -->> ("#",lhs_exp,"=",rhs_exp)
	  	  	  (locals , pState) = optionalLocals WithToken localsExpected pState
			=	( True
				, {	ndwl_strict	= strict
				  ,	ndwl_def	= { bind_dst = lhs_exp
				  				  , bind_src = rhs_exp
				  				  }
				  , ndwl_locals	= locals
				  , ndwl_position
				  				= LinePos file_name line_nr
				  }
				, pState
				)
		// otherwise // ~ succ
			= (False, abort "no definition", pState)
	
	try_let_lhs pState
		# (succ, lhs_exp, pState) = trySimpleLhsExpression pState
		| succ
			= (True, lhs_exp, pState)
			# (token,pState) = nextToken FunctionContext pState
			= case token of
				_ -> (False, lhs_exp, tokenBack pState)

optionalLocals :: !Token !Bool !ParseState -> (!LocalDefs, !ParseState)
optionalLocals dem_token localsExpected pState
    # (off_token, pState) = nextToken FunctionContext pState
	| dem_token == off_token
		= wantLocals pState
	# (ss_useLayout, pState) = accScanState UseLayout pState
	| off_token == CurlyOpenToken && ~ ss_useLayout && localsExpected
		= wantLocals (tokenBack pState)
	// otherwise
		= (LocalParsedDefs [], tokenBack pState)

wantLocals :: !ParseState -> (LocalDefs, !ParseState)
wantLocals pState
	# pState			= wantBeginGroup "local definitions" pState
	  (defs, pState)	= wantDefinitions cLocalContext pState
	= (LocalParsedDefs defs, wantEndLocals pState)

/*
	imports and exports
*/

wantImports :: !ParseState -> (![ParsedImport], !ParseState)
wantImports pState
	# (names, pState) = wantModuleIdents FunctionContext IC_Module pState
	  (file_name, line_nr, pState)	= getFileAndLineNr pState
	  pState = wantEndOfDefinition "imports" pState
	= (map (\name -> { import_module = name, import_symbols = [], import_file_position = LinePos file_name line_nr}) names, pState)

wantFromImports :: !ParseState -> (!ParsedImport, !ParseState)
wantFromImports pState
	# (mod_name, pState) = wantModuleName pState
	  (mod_ident, pState) = stringToIdent mod_name IC_Module pState
	  pState = wantToken GeneralContext "from imports" ImportToken pState
	  (file_name, line_nr, pState)	= getFileAndLineNr pState
	  (import_symbols, pState) = wantSequence CommaToken GeneralContext pState
	  pState = wantEndOfDefinition "from imports" pState
	= ( { import_module = mod_ident, import_symbols = import_symbols, import_file_position = LinePos file_name line_nr }, pState)

instance want ImportedObject where
	want pState
		# (token, pState) = nextToken GeneralContext pState
		| token == IdentToken "library"
	  		# (token, pState) = nextToken GeneralContext pState
			= want_import_string token cIsImportedLibrary pState
			= want_import_string token cIsImportedObject pState
		where		
			want_import_string :: Token Bool ParseState -> (ImportedObject, ParseState)
			want_import_string (StringToken string) isLibrary pState
				=	({io_is_library = isLibrary, io_name = string}, pState)
			want_import_string token isLibrary pState
				=	({io_is_library = isLibrary, io_name = ""}, parseError "import code declaration" (Yes token) "imported item" pState)

wantCodeImports :: !ParseState -> (![ImportedObject], !ParseState)
wantCodeImports pState
	# pState = wantToken GeneralContext "import code declaration" FromToken pState
	  (importObjects, pState) = wantSequence CommaToken GeneralContext pState
	= (importObjects, wantEndOfDefinition "import code declaration" pState)

instance want ImportDeclaration
where
	want pState
		# (token, pState) = nextToken GeneralContext pState
// MW5..
		= (switch_import_syntax want_1_3_import_declaration want_2_0_import_declaration) token pState

want_1_3_import_declaration token pState
	= case token of
			IdentToken name
				#	(fun_id, pState)		= stringToIdent name IC_Expression pState
					(type_id, pState)		= stringToIdent name IC_Type pState
					(class_id, pState)		= stringToIdent name IC_Class pState
				->	(ID_OldSyntax [fun_id, type_id, class_id], pState)
			token
				#	(fun_id, pState)		= stringToIdent "dummy" IC_Expression pState
				->	( ID_Function { ii_ident = fun_id, ii_extended = False }
					, parseError "from import" (Yes token) "imported item" pState
					)

want_2_0_import_declaration token pState
// ..MW5
		= case token of
			DoubleColonToken
				# (name, pState)				= wantConstructorName "import type" pState
				  (type_id, pState)				= stringToIdent name IC_Type pState
				  (ii_extended, token, pState)	= optional_extension_with_next_token pState
				| token == OpenToken
				  	#	(conses, pState)			= want_names (wantConstructorName "import type (..)") IC_Expression CloseToken pState
				  	->	(ID_Type { ii_ident = type_id, ii_extended = ii_extended } (Yes conses), pState)
				| token == CurlyOpenToken
				  	#	(fields, pState) = want_names (wantLowerCaseName "import record fields") (IC_Field type_id) CurlyCloseToken pState
				  	->	(ID_Record { ii_ident = type_id, ii_extended = ii_extended } (Yes fields), pState)
				  	->	(ID_Type { ii_ident = type_id, ii_extended = ii_extended } No, tokenBack pState)
			ClassToken
				# (name, pState)				= want pState
				  (class_id, pState)			= stringToIdent name IC_Class pState
				  (ii_extended, token, pState)	= optional_extension_with_next_token pState
				| token == OpenToken
				  	#	(members, pState)			= want_names want IC_Expression CloseToken pState
				  	->	(ID_Class { ii_ident = class_id, ii_extended = ii_extended } (Yes members), pState)
				  	->	(ID_Class { ii_ident = class_id, ii_extended = ii_extended } No, tokenBack pState)
			InstanceToken
				#	(class_name, pState)	= want pState
//					(ii_extended, pState)	= optional_extension pState // MW: removed but still not ok
					ii_extended				= False
					(types, pState)			= wantList "instance types" tryBrackType pState
					(class_id, pState)		= stringToIdent class_name IC_Class pState
					(inst_id, pState)		= stringToIdent class_name (IC_Instance types) pState
					(context, pState)		= optionalContext pState
				->	(ID_Instance { ii_ident = class_id, ii_extended = ii_extended } inst_id (types,context), pState)
			IdentToken fun_name
				#	(fun_id, pState)		= stringToIdent fun_name IC_Expression pState
					(ii_extended, pState)	= optional_extension pState
				->	(ID_Function { ii_ident = fun_id, ii_extended = ii_extended }, pState)
			token
				#	(fun_id, pState)		= stringToIdent "dummy" IC_Expression pState
				->	( ID_Function { ii_ident = fun_id, ii_extended = False }
					, parseError "from import" (Yes token) "imported item" pState
					)
	where				
		want_names want_fun ident_kind close_token pState
			# (token, pState) = nextToken FunctionContext pState
			| token == DotDotToken
				= ([], wantToken FunctionContext "import declaration" close_token pState)
				= want_list_of_names want_fun ident_kind close_token (tokenBack pState)

		want_list_of_names want_fun ident_kind close_token pState
			# (name, pState) = want_fun pState
			  (name_id, pState)	= stringToIdent name ident_kind pState
			  (ii_extended, token, pState) = optional_extension_with_next_token pState
			| token == CommaToken
				# (names, pState) = want_list_of_names want_fun ident_kind close_token pState
				= ([{ ii_ident = name_id, ii_extended = ii_extended } : names], pState)
			| token == close_token
				= ([{ ii_ident = name_id, ii_extended = ii_extended }], pState)
				= ([{ ii_ident = name_id, ii_extended = ii_extended }], parseError "ImportDeclaration" (Yes token) ")" pState)
			
		optional_extension pState
			# (token, pState) = nextToken FunctionContext pState
			| token == DotDotToken
				= (True, pState)
				= (False, tokenBack pState)			
			
		optional_extension_with_next_token pState
			# (token, pState) = nextToken FunctionContext pState
			| token == DotDotToken
				# (token, pState) = nextToken FunctionContext pState
				= (True, token, pState)
				= (False, token, pState)

/*						
wantExportDef :: !ParseState -> (!Export, !ParseState)
wantExportDef pState
	# (name, pState) = want pState
	  (ident, pState) = stringToIdent name IC_Class pState
	  (types, pState) = wantList "instance types" trySimpleType pState
	  pState = wantEndOfDefinition "exports" pState
	= ({ export_class = ident, export_types = types}, pState)
*/
/*
	Classes and instances
*/

cIsAGlobalContext		:== True
cIsNotAGlobalContext	:== False

cMightBeAClass			:== True
cIsNotAClass			:== False

		
wantClassDefinition :: !ParseContext !Position !ParseState -> (!ParsedDefinition, !ParseState)
wantClassDefinition parseContext pos pState
	# (might_be_a_class, class_or_member_name, prio, pState) = want_class_or_member_name pState
	  (class_variables, pState) = wantList "class variable(s)" try_class_variable pState
	  (class_arity, class_args, class_cons_vars) = convert_class_variables class_variables 0 0
	  (contexts, pState) = optionalContext pState
  	  (token, pState) = nextToken TypeContext pState
  	| token == DoubleColonToken
		= want_overloaded_function pos class_or_member_name prio class_arity class_args class_cons_vars contexts pState
	| might_be_a_class
		# (begin_members, pState) = begin_member_group token pState
		| begin_members
			# (class_id, pState) = stringToIdent class_or_member_name IC_Class pState
		 	  (members, pState) = wantDefinitions (SetClassOrInstanceDefsContext parseContext) pState
  		  	  class_def = { class_name = class_id, class_arity = class_arity, class_args = class_args,
	    					class_context = contexts, class_pos = pos, class_members = {}, class_cons_vars = class_cons_vars,
	    					class_dictionary = { ds_ident = { class_id & id_info = nilPtr }, ds_arity = 0, ds_index = NoIndex},
							class_arg_kinds = [] }
	    	  pState = wantEndGroup "class" pState
			= (PD_Class class_def members, pState)
		| isEmpty contexts
			= (PD_Erroneous, parseError "Class Definition" (Yes token) "<class definition>: contexts" pState)
		// otherwise
			# pState = tokenBack pState
			  (class_id, pState) = stringToIdent class_or_member_name IC_Class pState
  			  class_def = { class_name = class_id, class_arity = class_arity, class_args = class_args,
							class_context = contexts, class_pos = pos, class_members = {}, class_cons_vars = class_cons_vars, 
							class_dictionary = { ds_ident = { class_id & id_info = nilPtr }, ds_arity = 0, ds_index = NoIndex },
							class_arg_kinds = []}
	  		  pState = wantEndOfDefinition "class definition" pState
			= (PD_Class class_def [], pState)
		= (PD_Erroneous, parseError "Class Definition" (Yes token) "<class definition>" pState)
	where
		begin_member_group token pState // For JvG layout
			# (token, pState)
				= case token of
					SemicolonToken	->	nextToken TypeContext pState
					_				->	(token, pState)
			# (ss_useLayout, pState) = accScanState UseLayout pState
			| token == WhereToken
				# (token, pState) = nextToken TypeContext pState
				| token == CurlyOpenToken
					| ss_useLayout
						= (True, parseError "class definition" No "No { in layout mode" pState) 
						= (True, pState)
					= (True, tokenBack pState)
			| token == CurlyOpenToken 
				| ss_useLayout
					= (True, parseError "class definition" (Yes CurlyOpenToken) "in layout mode the keyword where is" pState) 
					= (True, pState)
				= (False, pState) // token is still known: no tokenBack
		
		want_class_or_member_name pState 
// PK			# (token, pState) = nextToken TypeContext pState
			# (token, pState) = nextToken GeneralContext pState
			| token == OpenToken
				# (member_name, pState) = want pState
				  pState = wantToken GeneralContext "class definition" CloseToken pState
				  (token, pState) = nextToken FunctionContext pState
				  (prio, pState) = optionalPriority cIsInfix token pState  
				= (cIsNotAClass, member_name, prio, pState)
 				# (class_name, pState) = want_name token pState
				= (cMightBeAClass, class_name, NoPrio, pState)
		where
			want_name (IdentToken name) pState
				= (name, pState)
			want_name token pState
				= ("", parseError "Class Definition" (Yes token) "<identifier>" pState)

		want_overloaded_function pos member_name prio class_arity class_args class_cons_vars contexts pState
			# (tspec, pState) = want pState
			  (member_id, pState) = stringToIdent member_name IC_Expression pState
			  (class_id, pState) = stringToIdent member_name IC_Class pState
			  member = PD_TypeSpec pos member_id prio (Yes tspec) SP_None
			  class_def = {	class_name = class_id, class_arity = class_arity, class_args = class_args,
		    				class_context = contexts, class_pos = pos, class_members = {}, class_cons_vars = class_cons_vars,
   							class_dictionary = { ds_ident = { class_id & id_info = nilPtr }, ds_arity = 0, ds_index = NoIndex },
   							class_arg_kinds = []}
	 		  pState = wantEndOfDefinition "overloaded function" pState
			= (PD_Class class_def [member], pState)

		try_class_variable pState
			# (token, pState) = nextToken TypeContext pState
			| token == DotToken
				# (type_var, pState) = wantTypeVar pState
				= (True, (True, type_var), pState)
			# (succ, type_var, pState) = tryTypeVarT token pState
			= (succ, (False, type_var), pState)
		
		convert_class_variables [] arg_nr cons_vars
			= (arg_nr, [], cons_vars)
		convert_class_variables [(annot, var) : class_vars] arg_nr cons_vars
			# (arity, class_vars, cons_vars) = convert_class_variables class_vars (inc arg_nr) cons_vars
			| annot
				= (arity, [var : class_vars], cons_vars bitor (1 << arg_nr))
				= (arity, [var : class_vars], cons_vars)

wantInstanceDeclaration :: !ParseContext !Position !ParseState -> (!ParsedDefinition, !ParseState)
wantInstanceDeclaration parseContext pi_pos pState
	# (class_name, pState) = want pState
	  (pi_class, pState) = stringToIdent class_name IC_Class pState
	  ((pi_types, pi_context), pState) = want_instance_type pState
	  (pi_ident, pState) = stringToIdent class_name (IC_Instance pi_types) pState
// AA..
	# (token, pState) = nextToken TypeContext pState
/*
	| token == GenericToken
		# pState = wantEndOfDefinition "generic instance declaration" pState
		= (PD_Instance {pi_class = pi_class, pi_ident = pi_ident, pi_types = pi_types, pi_context = pi_context,
							pi_members = [], pi_specials = SP_None, pi_pos = pi_pos}, pState)
*/
// ..AA
	| isIclContext parseContext
		# pState = want_begin_group token pState
		  (pi_members, pState) = wantDefinitions (SetClassOrInstanceDefsContext parseContext) pState
		  pState = wantEndGroup "instance" pState

		= (PD_Instance {pi_class = pi_class, pi_ident = pi_ident, pi_types = pi_types, pi_context = pi_context,
						pi_members = pi_members, pi_specials = SP_None, pi_pos = pi_pos}, pState)
	// otherwise // ~ (isIclContext parseContext)
		| token == CommaToken
			# (pi_types_and_contexts, pState)	= want_instance_types pState
			  (idents, pState)		= seqList [stringToIdent class_name (IC_Instance type) \\ (type,context) <- pi_types_and_contexts] pState
			= (PD_Instances
//				[	{ pi_class = pi_class, pi_ident = pi_ident, pi_types = type, pi_context = context // voor martin
				[	{ pi_class = pi_class, pi_ident = ident, pi_types = type, pi_context = context
					, pi_members = [], pi_specials = SP_None, pi_pos = pi_pos}
				\\	(type,context)	<- [ (pi_types, pi_context) : pi_types_and_contexts ]
				&	ident			<- [ pi_ident : idents ]
				]
			  , pState
			  )
		// otherwise // token <> CommaToken
			# (specials, pState) = optionalSpecials (tokenBack pState)
			  pState = wantEndOfDefinition "instance declaration" pState
			= (PD_Instance {pi_class = pi_class, pi_ident = pi_ident, pi_types = pi_types, pi_context = pi_context,
							pi_members = [], pi_specials = specials, pi_pos = pi_pos}, pState)
		
where
	want_begin_group token pState  // For JvG layout
		# // (token, pState) = nextToken TypeContext pState PK
		  (token, pState)
			= case token of
				SemicolonToken	->	nextToken TypeContext pState
				_				->	(token, pState)
		= case token of
			WhereToken	-> wantBeginGroup "instance declaration" pState
			CurlyOpenToken
				# (ss_useLayout, pState) = accScanState UseLayout pState
				| ss_useLayout
					-> parseError "instance declaration" (Yes token) "where" pState
					-> pState
			_	# (ss_useLayout, pState) = accScanState UseLayout pState
				| ss_useLayout
					-> parseError "instance declaration" (Yes token) "where" pState
					-> parseError "instance declaration" (Yes token) "where or {" pState

	want_instance_type pState
		# (pi_types, pState)	= wantList "instance types" tryBrackType pState
//		# (pi_types, pState)	= wantList "instance types" tryType pState	// This accepts 1.3 syntax, but is wrong for multiparameter classes
		  (pi_context, pState)	= optionalContext pState
		= ((pi_types, pi_context), pState)
	want_instance_types pState
		# (type_and_context, pState) = want_instance_type pState
		  (token, pState) = nextToken TypeContext pState
		| token == CommaToken
			# (types, pState) = want_instance_types pState
			= ([type_and_context:types], pState)
		// otherwise // token <> CommaToken
			= ([type_and_context], pState)

optionalContext :: !ParseState -> ([TypeContext],ParseState)
optionalContext pState
	# (token, pState) = nextToken TypeContext pState
	| token == BarToken
		= want_contexts pState
		= ([], tokenBack pState)
where
	want_contexts pState
		# (contexts, pState) = want_context pState
		  (token, pState) = nextToken TypeContext pState
		| token == AndToken
			# (more_contexts, pState) = want_contexts pState
			= (contexts ++ more_contexts, pState)
			= (contexts, tokenBack pState)

/*			
	want_context pState
		# (class_names, pState) = wantSequence CommaToken TypeContext pState
		  (types, pState)	= wantList "type arguments" tryBrackType pState // tryBrackAType ??
		= build_contexts class_names types (length types) pState
	where
		build_contexts [] types arity pState
			= ([], pState)
		build_contexts [class_name : class_names] types arity pState
			# (contexts, pState) = build_contexts class_names types arity pState
			  (class_ident, pState) = stringToIdent class_name IC_Class pState
			  tc_class = { glob_object = MakeDefinedSymbol class_ident NoIndex (length types), glob_module = NoIndex }
			= ([{ tc_class = tc_class, tc_types = types, tc_var = nilPtr } : contexts], pState)
*/
/**/
	want_context pState 
		# (tc_classes, pState) = wantSepList "classes" CommaToken TypeContext try_tc_class pState
		# (types, pState)	= wantList "type arguments" tryBrackType pState // tryBrackAType ??
		# {ps_error} = pState
		#! ok = ps_error.pea_ok
		# pState = {pState & ps_error = ps_error}
		| ok
			= mapSt (build_context types (length types)) tc_classes pState
			= ([], pState)
	
	try_tc_class pState
		# (token, pState) = nextToken GeneralContext pState
		= case token of 
			IdentToken name 
				# (token, pState) = nextToken GeneralContext pState
				-> case token of
					GenericOpenToken 
						# (ident, pState) = stringToIdent name IC_Generic pState			
						# (kind, pState) = wantKind pState						 
			 			# generic_global_ds = { glob_object = MakeDefinedSymbol ident NoIndex 1, glob_module = NoIndex }
						# class_global_ds = { glob_object = MakeDefinedSymbol {id_name="<no class>",id_info=nilPtr} NoIndex 1, glob_module = NoIndex}
						
						# gen_type_context = 
							{ gtc_generic = { glob_object = MakeDefinedSymbol ident NoIndex 1, glob_module = NoIndex }
							, gtc_kind = kind
							, gtc_class = { glob_object = MakeDefinedSymbol {id_name="<no class>",id_info=nilPtr} NoIndex 1, glob_module = NoIndex}
							, gtc_dictionary = { glob_object = MakeDefinedSymbol {id_name="<no generic dictionary>",id_info=nilPtr} NoIndex 1, glob_module = NoIndex} 							
							}
						
						-> (True, TCGeneric gen_type_context, pState)
					_ 
						# pState = tokenBack pState
						# (ident, pState) = stringToIdent name IC_Class pState			
			 			# class_global_ds = { glob_object = MakeDefinedSymbol ident NoIndex (-1), glob_module = NoIndex }
						-> (True, TCClass class_global_ds, pState)
			_ 
				-> (False, abort "no tc_class", tokenBack pState)
	
	build_context types length_types (TCClass class_global_ds=:{glob_object}) pState
		# tc_class = TCClass {class_global_ds & glob_object = {glob_object & ds_arity = length_types}}
		= ({ tc_class = tc_class, tc_var = nilPtr, tc_types = types}, pState)
	build_context types 1 (TCGeneric gtc=:{gtc_generic=gtc_generic=:{glob_object}}) pState
		# gtc = { gtc & gtc_generic = {gtc_generic & glob_object = {glob_object & ds_arity = 1}}} 
		= ({ tc_class = TCGeneric gtc, tc_var = nilPtr, tc_types = types }, pState)

	build_context types length_types tc_class=:(TCGeneric _) pState
		# pState = parseErrorSimple "type context" "generic class can have only one class argument" pState					
		= (abort "No TypeContext", pState)
/**/						 
optionalCoercions :: !ParseState -> ([AttrInequality], ParseState)
optionalCoercions pState 
	# (token, pState) = nextToken TypeContext pState
	| token == CommaToken
		# (token, pState) = nextToken TypeContext pState
		| token == SquareOpenToken
			# (inequals, pState) = want_inequalities pState
			= (inequals, wantToken FunctionContext "coercions" SquareCloseToken pState)
			= ([], parseError "Function type: coersions" (Yes token) "[" pState)
		= ([], tokenBack pState)
	where
		want_inequalities pState
			# (token, pState) = nextToken TypeContext pState
 			  (_, inequals, pState) = want_attr_inequality token pState
			  (token, pState) = nextToken TypeContext pState
			| token == CommaToken
				# (more_inequals, pState) = want_inequalities pState
				= (inequals ++ more_inequals, pState)
				= (inequals, tokenBack pState)
		want_attr_inequality (IdentToken var_name) pState
			| isLowerCaseName var_name
				# (off_ident, pState) = stringToIdent var_name IC_TypeAttr pState
				  (token, pState) = nextToken  TypeContext pState
				| token == LessThanOrEqualToken
					# (var_name, pState) = wantLowerCaseName "attribute inequality" pState
					  (dem_ident, pState) = stringToIdent var_name IC_TypeAttr pState
					  ai_demanded = makeAttributeVar dem_ident
					= (ai_demanded, [{ ai_demanded = ai_demanded, ai_offered = makeAttributeVar off_ident }], pState)				
					# (ai_demanded, inequals, pState) = want_attr_inequality token pState
					= (ai_demanded, [{ ai_demanded = ai_demanded, ai_offered = makeAttributeVar off_ident } : inequals], pState)
		want_attr_inequality token pState
			# erroneous_attr_var = makeAttributeVar erroneousIdent
			= (	erroneous_attr_var
			  , [{ ai_demanded = erroneous_attr_var, ai_offered = erroneous_attr_var }]
			  , parseError "Function type: optional coercions" (Yes token) "<attribute variable>" pState
			  )

// AA..
/*
	Generic definitions
*/

wantGenericDefinition :: !ParseContext !Position !ParseState -> (!ParsedDefinition, !ParseState)
wantGenericDefinition parseContext pos pState
	| SwitchGenerics False True 
		= (PD_Erroneous, parseErrorSimple "generic definition" "generics are not supported by this compiler" pState)
	| not pState.ps_support_generics
		= (PD_Erroneous, parseErrorSimple "generic definition" "to enable generics use the command line flag -generics" pState)
	# (name, pState) = want_name pState
	| name == "" 
		= (PD_Erroneous, pState)
	# (ident, pState) = stringToIdent name IC_Generic/*IC_Class*/ pState
	# (member_ident, pState) = stringToIdent name IC_Expression pState
	# (arg_vars, pState) = wantList "generic variable(s)" try_variable pState
		
	# pState = wantToken TypeContext "generic definition" DoubleColonToken pState
	# (type, pState) = want_type pState		//	SymbolType
	# pState = wantEndOfDefinition "generic definition" pState
	# gen_def = 
		{	gen_name = ident
		,	gen_member_name = member_ident 
		,	gen_type = type
		,	gen_vars = arg_vars
		,	gen_pos = pos
		,	gen_info_ptr = nilPtr
		}
	= (PD_Generic gen_def, pState)	
	where
		want_name pState 
			# (token, pState) = nextToken TypeContext pState
			= 	case token of
				IdentToken name -> (name, pState)
				_ -> ("", parseError "Generic Definition" (Yes token) "<identifier>" pState)
		want_type :: !ParseState -> (!SymbolType, !ParseState)
		want_type pState = want pState // SymbolType 		

		try_variable pState
			# (token, pState) = nextToken TypeContext pState
			= tryTypeVarT token pState
			
wantDeriveDefinition :: !ParseContext !Position !*ParseState -> (!ParsedDefinition, !*ParseState)
wantDeriveDefinition parseContext pos pState
	| SwitchGenerics False True 
		= (PD_Erroneous, parseErrorSimple "generic definition" "generics are not supported by this compiler" pState)
	| not pState.ps_support_generics
		= (PD_Erroneous, parseErrorSimple "generic definition" "to enable generics use the command line flag -generics" pState)
	# (name, pState) = want_name pState
	| name == "" 
		= (PD_Erroneous, pState)
	# (derive_defs, pState) = want_derive_types name pState
	= (PD_Derive derive_defs, pState)
where	
	want_name pState 
		# (token, pState) = nextToken TypeContext pState
		= 	case token of
			IdentToken name -> (name, pState)
			_ -> ("", parseError "Generic Definition" (Yes token) "<identifier>" pState)
	want_derive_types :: String !*ParseState -> ([GenericCaseDef], !*ParseState)			
	want_derive_types name pState
		# (derive_def, pState) = want_derive_type name pState
		# (token, pState) = nextToken TypeContext pState
		| token == CommaToken
			# (derive_defs, pState) = want_derive_types name pState
			= ([derive_def:derive_defs], pState)
			= ([derive_def], pState)
			
	want_derive_type :: String !*ParseState -> (GenericCaseDef, !*ParseState)			
	want_derive_type name pState
		# (type, pState) = wantType pState
		# (ident, pState) = stringToIdent name (IC_GenericCase type) pState
		# (generic_ident, pState) = stringToIdent name IC_Generic pState
		# (type_cons, pState) = get_type_cons type pState
		# derive_def = 
			{	gc_name	= ident
			, 	gc_gname = generic_ident
			, 	gc_generic = {gi_module=NoIndex,gi_index=NoIndex}
			,	gc_arity = 0
			,	gc_pos = pos
			,	gc_type = type
			,	gc_type_cons = type_cons
			,	gc_body = GCB_None
			,	gc_kind = KindError
			}
		= (derive_def, pState) 
	get_type_cons :: Type !*ParseState -> (TypeCons, !*ParseState)	
	get_type_cons (TA type_symb []) pState 
		= (TypeConsSymb type_symb, pState)
	get_type_cons (TB tb) pState 
		= (TypeConsBasic tb, pState)
	get_type_cons TArrow pState
		= (TypeConsArrow, pState)
	get_type_cons (TV tv) pState
		| isDclContext parseContext
			= (TypeConsVar tv, pState)			 
	get_type_cons type pState 
		# pState = parseError "generic type" No " type constructor" pState
		= (abort "no TypeCons", pState)
		
// ..AA

/*
	Type definitions
*/

wantTypeVar :: ! ParseState -> (!TypeVar, !ParseState)
wantTypeVar pState
	# (succ, type_var, pState) = tryTypeVar pState
	| succ
		= (type_var, pState)
		# (token, pState) = nextToken TypeContext pState
		= (MakeTypeVar erroneousIdent, parseError "Type Variable" (Yes token) "type variable" pState)

tryAttributedTypeVar :: !ParseState -> (!Bool, ATypeVar, !ParseState)
tryAttributedTypeVar pState
	# (token, pState) = nextToken TypeContext pState
	| is_type_arg_token token
		# (aOrA, attr, pState)	= warnAnnotAndOptionalAttr (tokenBack pState)
	      (succ, type_var, pState)		= tryTypeVar pState
	    | succ
			= (True, { atv_attribute = attr, atv_variable = type_var }, pState)
		| aOrA // annot <> AN_None || attr <> TA_None
			# (token, pState) = nextToken TypeContext pState
			= (False, no_type_var, parseError "Attributed type var" (Yes token) "type variabele after annotation or attribute" pState)
		// otherwise
	    	= (False, no_type_var, tokenBack pState)
	// otherwise
		= (False, no_type_var, tokenBack pState)
where	
	is_type_arg_token (IdentToken t)	= isLowerCaseName t
	is_type_arg_token DotToken       	= True
	is_type_arg_token AsteriskToken  	= True
	is_type_arg_token t              	= False
	
	no_type_var = abort "tryAttributedTypeVar: No type var"

wantTypeDef ::  !ParseContext !Position !ParseState -> (ParsedDefinition, !ParseState)
wantTypeDef parseContext pos pState
	# (type_lhs, annot, pState)	= want_type_lhs pos pState
	  (token, pState)			= nextToken TypeContext pState
	  (def, pState)				= want_type_rhs parseContext type_lhs token annot pState
  	  pState					= wantEndOfDefinition "type definition (6)" pState
  	= (def, pState)
where
	want_type_lhs :: !Position !ParseState -> (!ParsedTypeDef, !Annotation, !ParseState)
	want_type_lhs pos pState
		# (_, annot, attr, pState)	= optionalAnnotAndAttr pState
		  (name,    pState)			= wantConstructorName "Type name" pState
		  (ident,   pState)			= stringToIdent name IC_Type pState // -->> ("Type name",name)
		  (args,    pState)			= parseList tryAttributedTypeVar pState
		  (contexts, pState)		= optionalContext pState
		= (MakeTypeDef ident args (ConsList []) attr contexts pos, annot, pState)

	want_type_rhs :: !ParseContext !ParsedTypeDef !Token !Annotation !ParseState -> (ParsedDefinition, !ParseState)
	want_type_rhs parseContext td=:{td_name,td_attribute} EqualToken annot pState
		# name					= td_name.id_name
		  pState				= verify_annot_attr annot td_attribute name pState
		  (exi_vars, pState)	= optionalExistentialQuantifiedVariables pState
		  (token, pState)		= nextToken GeneralContext pState // should be TypeContext
 		= case token of
  			CurlyOpenToken
				#	(fields, pState)			= wantFields td_name pState
					pState						= wantToken TypeContext "record type def" CurlyCloseToken pState
				  	(rec_cons_ident, pState)	= stringToIdent ("_" + name) IC_Expression pState
				->	(PD_Type { td & td_rhs = SelectorList rec_cons_ident exi_vars fields }, pState)
/*			ColonToken
				| isEmpty exi_vars
				->	(PD_Erroneous, parseError "Algebraic type" No "no colon, :," pState)
				->	(PD_Erroneous, parseError "Algebraic type" No "in this version of Clean no colon, :, after quantified variables" pState)
*/			_	#	(condefs, pState)	= want_constructor_list exi_vars token pState
					td					= { td & td_rhs = ConsList condefs }
				|	annot == AN_None
	 		  		->	(PD_Type td, pState)
	 		  		->	(PD_Type td, parseError "Algebraic type" No ("No lhs strictness annotation for the algebraic type "+name) pState)
	want_type_rhs parseContext td=:{td_attribute} ColonDefinesToken annot pState // type Macro
		# name				= td.td_name.id_name
		  pState			= verify_annot_attr annot td_attribute name pState
		  (atype, pState)	= want pState // Atype
		  td				= {td & td_rhs = TypeSpec atype}
		|	annot == AN_None
			= (PD_Type td, pState)
			= (PD_Type td, parseError "Type synonym" No ("No lhs strictness annotation for the type synonym "+name) pState)
/*
	want_type_rhs parseContext td=:{td_attribute} token=:DefinesColonToken annot pState
		| isIclContext parseContext
			= (PD_Erroneous, parseError "type RHS" (Yes token) "type definition" pState)
		# name				= td.td_name.id_name
		  (atype, pState)	= want pState // Atype
		# (td_attribute, properties) = determine_properties annot td_attribute
		  td				= {td & td_rhs = AbstractTypeSpec properties atype, td_attribute=td_attribute}
		| annot <> AN_None
			= (PD_Type td, parseError "Type synonym" No ("No lhs strictness annotation for the type synonym "+name) pState)
		| td_attribute == TA_Anonymous || td_attribute == TA_Unique || td_attribute == TA_None
			= (PD_Type td, pState)
			= (PD_Type td, parseError "abstract type" No ("type attribute "+toString td_attribute+" for abstract type "+name+" is not") (tokenBack pState))
*/
	want_type_rhs parseContext td=:{td_attribute} token annot pState
		| isIclContext parseContext
			= (PD_Erroneous, parseError "type RHS" (Yes token) "type definition" pState)
			| td_attribute == TA_Anonymous || td_attribute == TA_Unique || td_attribute == TA_None
				# (td_attribute, properties) = determine_properties annot td_attribute
				# td = { td & td_attribute = td_attribute, td_rhs = EmptyRhs properties}
				= (PD_Type td, tokenBack pState)
				# name = td.td_name.id_name
				= (PD_Type  { td & td_rhs = EmptyRhs cAllBitsClear}, parseError "abstract type" No ("type attribute "+toString td_attribute+" for abstract type "+name+" is not") (tokenBack pState))
	
	verify_annot_attr :: !Annotation !TypeAttribute !String !ParseState -> ParseState
	verify_annot_attr annot attr name pState
		| annot <> AN_None
			= parseError "type definition" No ("No annotation, "+toString annot+", in the lhs of type "+name) pState
		| attr == TA_None || attr == TA_Unique
			= pState
			= parseError "type definition" No ("No attribute, "+toString attr+", in the lhs of type "+name) pState

	determine_properties :: !Annotation !TypeAttribute -> (!TypeAttribute, !BITVECT)
	determine_properties annot attr
		| annot == AN_Strict
			| attr == TA_Anonymous
				= (TA_None, cIsHyperStrict)
				= (attr, cIsHyperStrict bitor cIsNonCoercible)
		| attr == TA_Anonymous
			= (TA_None, cAllBitsClear)
			= (attr, cIsNonCoercible)

	want_constructor_list :: ![ATypeVar] !Token !ParseState -> (.[ParsedConstructor],ParseState)
	want_constructor_list exi_vars token pState
		# token = basic_type_to_constructor token
		# (pc_cons_name,  pc_cons_prio, pc_cons_pos, pState) = want_cons_name_and_prio token pState
		  (pc_arg_types, pState) = parseList tryBrackSAType pState
		  cons = { pc_cons_name = pc_cons_name, pc_arg_types = atypes_from_satypes pc_arg_types, pc_args_strictness=strictness_from_satypes pc_arg_types, pc_cons_arity = length pc_arg_types,
		  			pc_cons_prio = pc_cons_prio, pc_exi_vars = exi_vars, pc_cons_pos = pc_cons_pos}
		  (token, pState) = nextToken TypeContext pState
		| token == BarToken
			# (exi_vars, pState) = optionalExistentialQuantifiedVariables pState
// MW 			  (token, pState) = nextToken TypeContext pState
			  (token, pState) = nextToken GeneralContext pState
			  (cons_list, pState) = want_constructor_list exi_vars token pState
			= ([cons : cons_list], pState)
		// otherwise
			= ([cons], tokenBack pState)
	where
		want_cons_name_and_prio :: !Token !ParseState -> (Ident, !Priority, !Position, !ParseState)
		want_cons_name_and_prio tok=:(IdentToken name) pState
			# (ident, pState) = stringToIdent name IC_Expression pState
		 	  (fname, linenr, pState) = getFileAndLineNr pState
		  	  (token, pState) = nextToken TypeContext pState
		  	  (prio,  pState) = optionalPriority cIsNotInfix token pState
		  	| isLowerCaseName name
				= (ident, prio, LinePos fname linenr, parseError "Algebraic type: constructor definitions" (Yes tok) "constructor name" pState)
				= (ident, prio, LinePos fname linenr, pState)
		want_cons_name_and_prio OpenToken pState
			# (name, pState) = wantConstructorName "infix constructor" pState
		 	  (fname, linenr, pState) = getFileAndLineNr pState
			  (ident, pState) = stringToIdent name IC_Expression pState
		      (token, pState) = nextToken TypeContext (wantToken TypeContext "type: constructor and prio" CloseToken pState)
			  (prio, pState) = optionalPriority cIsInfix token pState
			= (ident, prio, LinePos fname linenr, pState)
		want_cons_name_and_prio DotToken pState
			# (token,pState)	= nextToken GeneralContext pState
			= case token of
				IdentToken name
					| isFunnyIdName name -> want_cons_name_and_prio (IdentToken ("."+name)) pState
				_	-> (erroneousIdent, NoPrio, NoPos, parseError "Algebraic type: constructor list" (Yes DotToken) "constructor name" (tokenBack pState))
		want_cons_name_and_prio token pState
			= (erroneousIdent, NoPrio, NoPos, parseError "Algebraic type: constructor list" (Yes token) "constructor name" pState)

	basic_type_to_constructor IntTypeToken		= IdentToken "Int"
	basic_type_to_constructor CharTypeToken		= IdentToken "Char"
	basic_type_to_constructor RealTypeToken		= IdentToken "Real"
	basic_type_to_constructor BoolTypeToken		= IdentToken "Bool"
	basic_type_to_constructor StringTypeToken	= IdentToken "String"
	basic_type_to_constructor FileTypeToken		= IdentToken "File"
	basic_type_to_constructor WorldTypeToken	= IdentToken "World"
	basic_type_to_constructor DynamicTypeToken	= IdentToken "Dynamic"
	basic_type_to_constructor token				= token

makeAttributeVar name :== { av_name = name, av_info_ptr = nilPtr }

optionalAnnot :: !ParseState -> (!Bool,!Annotation, !ParseState)
optionalAnnot pState
   	# (token, pState) = nextToken TypeContext pState
   	| token == ExclamationToken
	  	# (token, pState) = nextToken TypeContext pState
// JVG added for strict lists:
		| token==SquareCloseToken
			= (False,AN_None,tokenBack (tokenBack pState))
		= (True, AN_Strict, tokenBack pState)
	| otherwise // token <> ExclamationToken
		= (False, AN_None, tokenBack pState)

optionalAnnotWithPosition :: !ParseState -> (!Bool,!AnnotationWithPosition, !ParseState)
optionalAnnotWithPosition pState
   	# (token, pState) = nextToken TypeContext pState
   	| token == ExclamationToken
	  	# (token, pState) = nextToken TypeContext pState
// JVG added for strict lists:
		| token==SquareCloseToken
			= (False,NoAnnot,tokenBack (tokenBack pState))
		# (position,pState) = getPosition pState
		= (True, StrictAnnotWithPosition position, tokenBack pState)
	| otherwise // token <> ExclamationToken
		= (False, NoAnnot, tokenBack pState)

warnAnnotAndOptionalAttr :: !ParseState -> (!Bool, !TypeAttribute, !ParseState)
warnAnnotAndOptionalAttr pState
   	# (token, pState) = nextToken TypeContext pState
   	| token == ExclamationToken
	  	# (token, pState) = nextToken TypeContext pState
// JVG added for strict lists:
		| token==SquareCloseToken
			= (False,TA_None,tokenBack (tokenBack pState))
// Sjaak  (_   , attr, pState)  = optional_attribute token pState
		# (_   , attr, pState)  = tryAttribute token pState
		# pState = parseWarning "" "! ignored" pState
		= (True, attr, pState)
	| otherwise // token <> ExclamationToken
		= tryAttribute token pState

optionalAnnotAndAttr :: !ParseState -> (!Bool, !Annotation, !TypeAttribute, !ParseState)
optionalAnnotAndAttr pState
   	# (token, pState) = nextToken TypeContext pState
   	| token == ExclamationToken
	  	# (token, pState) = nextToken TypeContext pState
// JVG added for strict lists:
		| token==SquareCloseToken
			= (False,AN_None,TA_None,tokenBack (tokenBack pState))
// Sjaak  (_   , attr, pState)  = optional_attribute token pState
		# (_   , attr, pState)  = tryAttribute token pState
		= (True, AN_Strict, attr, pState)
	| otherwise // token <> ExclamationToken
		# (succ, attr, pState)  = tryAttribute token pState
		= (succ, AN_None, attr, pState)

optionalAnnotAndAttrWithPosition :: !ParseState -> (!Bool, !AnnotationWithPosition, !TypeAttribute, !ParseState)
optionalAnnotAndAttrWithPosition pState
   	# (token, pState) = nextToken TypeContext pState
   	| token == ExclamationToken
	  	# (token, pState) = nextToken TypeContext pState
// JVG added for strict lists:
		| token==SquareCloseToken
			= (False,NoAnnot,TA_None,tokenBack (tokenBack pState))
// Sjaak  (_   , attr, pState)  = optional_attribute token pState
		# (position,pState) = getPosition pState
		# (_   , attr, pState)  = tryAttribute token pState
		= (True, StrictAnnotWithPosition position, attr, pState)
	| otherwise // token <> ExclamationToken
		# (succ, attr, pState)  = tryAttribute token pState
		= (succ, NoAnnot, attr, pState)

// Sjaak 210801 ...
		  
tryAttribute :: !Token !ParseState -> (!Bool, !TypeAttribute, !ParseState)
tryAttribute DotToken           pState = (True, TA_Anonymous,    pState)
tryAttribute AsteriskToken      pState = (True, TA_Unique, pState)
tryAttribute (IdentToken id) pState
	| isLowerCaseName id
  	# (token, pState) = nextToken TypeContext pState
	| ColonToken == token
		# (ident, pState) = stringToIdent id IC_TypeAttr pState
		= (True, TA_Var (makeAttributeVar ident), pState)
		= (False, TA_None, tokenBack (tokenBack pState))
tryAttribute _	              pState = (False, TA_None, tokenBack pState)
   
// ... Sjaak

cIsInfix	:== True
cIsNotInfix	:== False

wantFields :: !Ident !*ParseState -> (![ParsedSelector], !*ParseState)
wantFields record_type pState
	# (field, pState) = want_field record_type pState
	  (token, pState) = nextToken TypeContext pState
	| token == CommaToken
		# (fields, pState) = wantFields record_type pState
		= ([field : fields], pState)
		= ([field], tokenBack pState)
	where
		want_field :: !Ident !*ParseState -> *(!ParsedSelector, !*ParseState)
		want_field record_type pState
			# (field_name, pState) 			= wantLowerCaseName "record field" pState
			  (fname, linenr, pState)		= getFileAndLineNr pState
			  (ps_field_name, pState) 		= stringToIdent field_name (IC_Field record_type) pState
			  (ps_selector_name, pState) 	= stringToIdent field_name IC_Selector pState
			  (ps_field_var, pState) 		= stringToIdent field_name IC_Expression pState
			  pState          				= wantToken TypeContext "record field" DoubleColonToken pState
//			  (ps_field_type, pState)  		= want pState // wantAType
			  (annotation,ps_field_type, pState) = wantAnnotatedAType pState
			= ({ ps_field_name = ps_field_name, ps_selector_name = ps_selector_name, ps_field_type = ps_field_type,
					ps_field_annotation = annotation,
					ps_field_var = ps_field_var, ps_field_pos = LinePos fname linenr}, pState)

atypes_from_sptypes_and_warn_if_strict :: ![SATypeWithPosition] !ParseState -> (![AType],!ParseState)
atypes_from_sptypes_and_warn_if_strict [] pState
	= ([],pState)
atypes_from_sptypes_and_warn_if_strict [{sp_type,sp_annotation}:types] pState
	# pState = warnIfStrictAnnot sp_annotation pState
	# (atypes,pState) = atypes_from_sptypes_and_warn_if_strict types pState
	= ([sp_type:atypes],pState)

atypes_from_sptypes :: ![SATypeWithPosition] -> [AType]
atypes_from_sptypes []
	= []
atypes_from_sptypes [{sp_type}:types]
	= [sp_type:atypes_from_sptypes types]

atypes_from_satypes :: ![SAType] -> [AType]
atypes_from_satypes []
	= []
atypes_from_satypes [{s_type}:types]
	= [s_type:atypes_from_satypes types]

strictness_from_satypes types
	= add_strictness_for_arguments types 0 0 NotStrict
where 
	add_strictness_for_arguments :: ![SAType] !Int !Int !StrictnessList -> StrictnessList
	add_strictness_for_arguments [] strictness_index strictness strictness_list
		| strictness==0
			= strictness_list
			= append_strictness strictness strictness_list
	add_strictness_for_arguments [{s_annotation=AN_Strict}:types] strictness_index strictness strictness_list
		# (strictness_index,strictness,strictness_list) = add_next_strict strictness_index strictness strictness_list
		= add_strictness_for_arguments types strictness_index strictness strictness_list
	add_strictness_for_arguments [{s_annotation=AN_None}:types] strictness_index strictness strictness_list
		# (strictness_index,strictness,strictness_list) = add_next_not_strict strictness_index strictness strictness_list
		= add_strictness_for_arguments types strictness_index strictness strictness_list

strictness_from_sptypes types
	= add_strictness_for_arguments types 0 0 NotStrict
where 
	add_strictness_for_arguments :: ![SATypeWithPosition] !Int !Int !StrictnessList -> StrictnessList
	add_strictness_for_arguments [] strictness_index strictness strictness_list
		| strictness==0
			= strictness_list
			= append_strictness strictness strictness_list
	add_strictness_for_arguments [{sp_annotation=StrictAnnotWithPosition _}:types] strictness_index strictness strictness_list
		# (strictness_index,strictness,strictness_list) = add_next_strict strictness_index strictness strictness_list
		= add_strictness_for_arguments types strictness_index strictness strictness_list
	add_strictness_for_arguments [{sp_annotation=NoAnnot}:types] strictness_index strictness strictness_list
		# (strictness_index,strictness,strictness_list) = add_next_not_strict strictness_index strictness strictness_list
		= add_strictness_for_arguments types strictness_index strictness strictness_list

makeSymbolType args result context attr_env :==
	{ st_vars = [], st_args = atypes_from_sptypes args, st_args_strictness = strictness_from_sptypes args,st_arity = length args, st_result = result,
	  st_context = context, st_attr_env = attr_env, st_attr_vars = [] }
 
instance want SymbolType
where
	want pState
		# (vars , pState) = optionalUniversalQuantifiedVariables pState // PK
 		# (types, pState) = parseList tryBrackSATypeWithPosition pState
		  (token, pState) = nextToken TypeContext pState //-->> ("arg types:",types)
   		= want_rest_of_symbol_type token types pState
	where
		want_rest_of_symbol_type :: !Token ![SATypeWithPosition] !ParseState -> (!SymbolType, !ParseState)
		want_rest_of_symbol_type ArrowToken types pState
			# pState				= case types of
										[]	-> parseWarning "want SymbolType" "types before -> expected" pState
										_	-> pState
			# (type, pState)		= want pState
			  (context, pState)		= optionalContext pState
			  (attr_env, pState)	= optionalCoercions pState
			= (makeSymbolType types type context attr_env, pState)
		want_rest_of_symbol_type token [] pState
			= (makeSymbolType [] (MakeAttributedType TE) [] [], parseError "symbol type" (Yes token) "type" pState)
		want_rest_of_symbol_type token [{sp_type=type,sp_annotation}] pState
			# pState = warnIfStrictAnnot sp_annotation pState
			# (context, pState) = optionalContext (tokenBack pState)
			  (attr_env, pState) = optionalCoercions pState
			= (makeSymbolType [] type context attr_env, pState)
		want_rest_of_symbol_type token [{sp_type=type=:{at_type = TA type_symb [] },sp_annotation} : types] pState
			# pState = warnIfStrictAnnot sp_annotation pState
			# (atypes,pState) = atypes_from_sptypes_and_warn_if_strict types pState
		 	# type = { type & at_type = TA { type_symb & type_arity = length atypes } atypes }
			  (context, pState) = optionalContext (tokenBack pState)
			  (attr_env, pState) = optionalCoercions pState
			= (makeSymbolType [] type context attr_env, pState)
		want_rest_of_symbol_type token [{sp_type=type=:{at_type = TV tv},sp_annotation} : types] pState
			# pState = warnIfStrictAnnot sp_annotation pState
			# (atypes,pState) = atypes_from_sptypes_and_warn_if_strict types pState
		 	# type = { type & at_type = CV tv :@: atypes }
			  (context, pState) = optionalContext (tokenBack pState)
			  (attr_env, pState) = optionalCoercions pState
			= (makeSymbolType [] type context attr_env, pState)
		want_rest_of_symbol_type token types pState
			= (makeSymbolType [] (MakeAttributedType TE) [] [], parseError "symbol type" (Yes token) "->" pState) -->> types

/*
	Types
*/

nameToTypeVar name pState
	# last_char_index = size name - 1
	| name.[last_char_index] == '^'
		# new_name = name % (0, last_char_index - 1)
		# (ident, pState) = stringToIdent new_name IC_Type pState
		= (GTV (MakeTypeVar ident), pState)
		# (ident, pState) = stringToIdent name IC_Type pState
		= (TV (MakeTypeVar ident), pState)

instance want TypeVar
where
	want pState
		# (token, pState) = nextToken TypeContext pState
		= case token of
			IdentToken name
				| isLowerCaseName name
					# (ident, pState) = stringToIdent name IC_Type pState
					-> (MakeTypeVar ident, pState)
					-> (MakeTypeVar erroneousIdent, parseError "Type variable" (Yes token) "<type variable>" pState)
			_
				-> (MakeTypeVar erroneousIdent, parseError "Type variable" (Yes token) "<type variable>" pState)

// Sjaak 210801 ...

adjustAttribute :: !TypeAttribute Type *ParseState -> (!TypeAttribute, !*ParseState)
adjustAttribute attr (TV {tv_name}) pState
	= adjustAttributeOfTypeVariable attr tv_name pState
adjustAttribute attr (GTV {tv_name}) pState
	= adjustAttributeOfTypeVariable attr tv_name pState
adjustAttribute attr type pState
	= (attr, pState)

adjustAttributeOfTypeVariable :: !TypeAttribute !Ident !*ParseState -> (!TypeAttribute, !*ParseState)
adjustAttributeOfTypeVariable TA_Anonymous {id_name} pState
	# (ident, pState) = stringToIdent id_name IC_TypeAttr pState
	= (TA_Var (makeAttributeVar ident), pState)
adjustAttributeOfTypeVariable attr _ pState
	= (attr, pState)

// ... Sjaak 210801

stringToType :: !String !ParseState -> (!Type, !ParseState)
stringToType name pState
	| isLowerCaseName name
		= nameToTypeVar name pState
		# (id, pState) = stringToIdent name IC_Type pState
		= (TA (MakeNewTypeSymbIdent id 0) [], pState)
/*	| isUpperCaseName name
		= (TA (MakeNewTypeSymbIdent id 0) [], pState)
		= nameToTypeVar name pState
*/
/*
stringToAType :: !String !Annotation !TypeAttribute !ParseState -> (!AType, !ParseState)
stringToAType name annot attr pState
	# (id, pState) = stringToIdent name IC_Type pState
	| isUpperCaseName name
		= ({ at_annotation = annot, at_attribute = attr, at_type = TA (MakeNewTypeSymbIdent id 0) []}, pState)
		# (type_var, pState) = nameToTypeVar name pState
		= build_attributed_type_var attr annot type_var name pState
where
	build_attributed_type_var TA_Anonymous annot type_var type_var_name pState
		# (attr_id, pState) = stringToIdent type_var_name IC_TypeAttr pState
		= ({ at_annotation = annot, at_attribute = TA_Var (makeAttributeVar attr_id), at_type = type_var }, pState)
	build_attributed_type_var attr annot type_var _ pState
		= ({ at_annotation = annot, at_attribute = attr, at_type = type_var }, pState)
*/

:: SAType = {s_annotation::!Annotation,s_type::!AType}

:: SATypeWithPosition = {sp_annotation::!AnnotationWithPosition,sp_type::!AType}

instance want SAType
where
	want pState
		# (annotation,a_type,pState) = wantAnnotatedAType pState
		= ({s_annotation=annotation,s_type=a_type},pState)

:: AnnotationWithPosition = NoAnnot | StrictAnnotWithPosition !FilePosition;

wantAnnotatedATypeWithPosition :: !ParseState -> (!AnnotationWithPosition,!AType,!ParseState)
wantAnnotatedATypeWithPosition pState
	# (vars , pState)		= optionalUniversalQuantifiedVariables pState	
	# (_,annotation,pState) = optionalAnnotWithPosition pState
	# (succ, atype, pState)	= tryAnnotatedAType True TA_None vars pState
	| succ
		= (annotation, atype, pState)
	// otherwise //~ succ
		# (token, pState) = nextToken TypeContext pState
		= (annotation, atype, parseError "atype" (Yes token) "attributed and annotated type" pState)

wantAnnotatedAType :: !ParseState -> (!Annotation,!AType,!ParseState)
wantAnnotatedAType pState
	# (vars , pState)		= optionalUniversalQuantifiedVariables pState	
	# (_,annotation,pState) = optionalAnnot pState
	# (succ, atype, pState)	= tryAnnotatedAType True TA_None vars pState
	| succ
		= (annotation, atype, pState)
	// otherwise //~ succ
		# (token, pState) = nextToken TypeContext pState
		= (annotation, atype, parseError "atype" (Yes token) "attributed and annotated type" pState)

tryAnnotatedAType :: !Bool !TypeAttribute ![ATypeVar] !ParseState -> (!Bool, !AType,!ParseState)
tryAnnotatedAType tryAA attr vars pState
	| isEmpty vars
		# (types, pState)		= parseList tryBrackAType pState
		| isEmpty types 
			= (False, {at_attribute = attr, at_type = TE}, pState)
		//| othewrise // types not empty
			# (token, pState)		= nextToken TypeContext pState
			| token == ArrowToken						
				# (rtype, pState)	= wantAType pState
		  		# atype = make_curry_type attr types rtype
				= ( True, atype, pState)
		  	//| otherwise // not arrow
				# (atype, pState) = convertAAType types attr (tokenBack pState)
				= (True, atype, pState)
	//| otherwise // vars not empty	  			
		# (atype, pState) = wantForallType attr vars pState
		= (True, atype, pState)
	
/* AA commented out:
	# (types, pState)		= parseList tryBrackAType pState
	| isEmpty types
		| isEmpty vars
			= (False, {at_attribute = attr, at_type = TE}, pState)
		// otherwise // PK
			# (token, pState) = nextToken TypeContext pState
			= (False, {at_attribute = attr, at_type = TFA vars TE}
			  , parseError "annotated type" (Yes token) "type" (tokenBack pState))
	# (token, pState)		= nextToken TypeContext pState
	| token == ArrowToken
		# (rtype, pState)	= wantAType pState
		  atype = make_curry_type attr types rtype
		| isEmpty vars
			= ( True, atype, pState)
			= ( True, { atype & at_type = TFA vars atype.at_type }, pState)
	// otherwise (not that types is non-empty)
// Sjaak	
	# (atype, pState) = convertAAType types attr (tokenBack pState)
	| isEmpty vars
		= (True, atype, pState)
		= (True, { atype & at_type = TFA vars atype.at_type }, pState)
*/

where
	make_curry_type attr [t1] res_type
		= {at_attribute = attr, at_type = t1 --> res_type}
	make_curry_type attr [t1:tr] res_type
		= {at_attribute = attr, at_type = t1 --> make_curry_type TA_None tr res_type}
	make_curry_type _ _ _ = abort "make_curry_type: wrong assumption"

wantForallType :: !TypeAttribute [ATypeVar] !ParseState -> (!AType,!ParseState)
wantForallType attr forall_atvs pState
	# (st, pState) = want pState // want SymbolType 
	# st = 
		{ st 
		& st_vars = [atv_variable\\{atv_variable} <- forall_atvs]
		, st_attr_vars = [av \\ {atv_attribute = TA_Var av} <- forall_atvs]
		, st_result = curry attr st.st_args st.st_result
		, st_args = []
		, st_arity = 0 // forall symbol type must always be curried 
		}
	= ({at_type=TST forall_atvs st, at_attribute=attr}, pState)
where
	curry attr [] res = res // RANKN FIXME: what shall we do with 'attr' and 'res.at_attribute'???
	curry attr [arg:args] res = { at_attribute = attr, at_type = arg --> curry TA_None args res }  	

tryBrackSAType :: !ParseState -> (!Bool, SAType, !ParseState)
tryBrackSAType pState
	# (_, annot, attr, pState)	= optionalAnnotAndAttr pState
	# (succ, atype, pState) = trySimpleType attr pState
	= (succ, {s_annotation=annot,s_type=atype}, pState)

tryBrackSATypeWithPosition :: !ParseState -> (!Bool, SATypeWithPosition, !ParseState)
tryBrackSATypeWithPosition pState
	# (_, annot, attr, pState)	= optionalAnnotAndAttrWithPosition pState
	# (succ, atype, pState) = trySimpleType attr pState
	= (succ, {sp_annotation=annot,sp_type=atype}, pState)

instance want AType
where
	want pState = wantAType pState

instance want Type
where
	want pState = wantType pState

wantType :: !ParseState -> (!Type,!ParseState)
wantType pState
	# (vars, pState)	= optionalUniversalQuantifiedVariables pState
	| isEmpty vars
		# (succ, atype, pState)	= tryAType False TA_None pState
		  (succ2, type, pState)	= tryATypeToType atype pState
		| succ&&succ2
			= (type, pState)
		// otherwise //~ succ
			# (token, pState) = nextToken TypeContext pState
			= (type, parseError "type" (Yes token) "type" pState)
	// ~(isEmpty vars)
		//# (type, pState) = wantType pState
		//= (TFA vars type, pState)
		# (type, pState) = wantForallType TA_None vars pState
		= (type.at_type, pState)

wantAType :: !ParseState -> (!AType,!ParseState)
wantAType pState
	# (succ, atype, pState)	= tryAType True TA_None pState
	| succ
		= (atype, pState)
	// otherwise //~ succ
		# (token, pState) = nextToken TypeContext pState
		= (atype, parseError "atype" (Yes token) "attributed and annotated type" pState)

tryType :: !ParseState -> (!Bool,!Type,!ParseState)
tryType pState
	# (succ, atype, pState)	= tryAType False TA_None pState
	  (succ2, type, pState)	= tryATypeToType atype pState
	= (succ&&succ2, type, pState)

tryAType :: !Bool !TypeAttribute !ParseState -> (!Bool,!AType,!ParseState)
tryAType tryAA attr pState
	# (vars , pState)		= optionalUniversalQuantifiedVariables pState
	| isEmpty vars
		# (types, pState)		= parseList tryBrackAType pState
		| isEmpty types
			= (False, {at_attribute = attr, at_type = TE}, pState)
		//| otherwise // types not empty	
			# (token, pState)		= nextToken TypeContext pState
			| token == ArrowToken
				# (rtype, pState)	= wantAType pState
			  	  atype = make_curry_type attr types rtype
				= ( True, atype, pState)
			//| otherwise // not arrow	
				# (atype, pState) = convertAAType types attr (tokenBack pState)
				= (True, atype, pState)				
	//| otherwise // vars not empty
		# (atype, pState) = wantForallType attr vars pState
		= (True, atype, pState)
				
/* AA commented out:	
	# (types, pState)		= parseList tryBrackAType pState
	| isEmpty types
		| isEmpty vars
			= (False, {at_attribute = attr, at_type = TE}, pState)
		// otherwise // PK
			# (token, pState) = nextToken TypeContext pState
			= (False, {at_attribute = attr, at_type = TFA vars TE}
			  , parseError "annotated type" (Yes token) "type" (tokenBack pState))
	# (token, pState)		= nextToken TypeContext pState
	| token == ArrowToken
		# (rtype, pState)	= wantAType pState
		  atype = make_curry_type attr types rtype
		| isEmpty vars
			= ( True, atype, pState)
			= ( True, { atype & at_type = TFA vars atype.at_type }, pState)
	// otherwise (not that types is non-empty)
// Sjaak	
	# (atype, pState) = convertAAType types attr (tokenBack pState)
	| isEmpty vars
		= (True, atype, pState)
		= (True, { atype & at_type = TFA vars atype.at_type }, pState)
*/


/* PK
tryFunctionType :: ![AType] !Annotation !TypeAttribute !ParseState -> (!Bool,!AType,!ParseState)
tryFunctionType types annot attr pState
	# (rtype, pState)		= wantAType pState
	= ( True
	  , make_curry_type annot attr types rtype
	  , pState
	  )
*/
where
	make_curry_type attr [t1] res_type
		= {at_attribute = attr, at_type = t1 --> res_type}
	make_curry_type attr [t1:tr] res_type
		= {at_attribute = attr, at_type = t1 --> make_curry_type TA_None tr res_type}
	make_curry_type _ _ _ = abort "make_curry_type: wrong assumption"

// Sjaak ...
convertAAType :: ![AType] !TypeAttribute !ParseState -> (!AType,!ParseState)
convertAAType [atype:atypes] attr pState
	#	type			= atype.at_type
		(attr, pState)	= determAttr attr atype.at_attribute type pState
	| isEmpty atypes
		= ( {at_attribute = attr, at_type = type}, pState)
	// otherwise // type application
		# (type, pState)	= convert_list_of_types atype.at_type atypes pState
		= ({at_attribute = attr, at_type = type}, pState)
where
	convert_list_of_types (TA sym []) types pState
		= (TA { sym & type_arity = length types } types, pState)
	convert_list_of_types (TV tv) types pState
		= (CV tv :@: types, pState)
//AA..
	convert_list_of_types TArrow [type1, type2]	pState
		= (type1 --> type2, pState)
	convert_list_of_types TArrow [type1] pState
		= (TArrow1 type1, pState)
	convert_list_of_types (TArrow1 type1) [type2] pState
		= (type1 --> type2, pState)
//..AA
	convert_list_of_types _ types pState
		= (TE, parseError "Type" No "ordinary type variable" pState)
// ... Sjaak
/*
tryApplicationType _ annot attr pState
	= (False, {at_annotation = annot, at_attribute = attr, at_type = TE}, pState)
*/
tryBrackType :: !ParseState -> (!Bool, Type, !ParseState)
tryBrackType pState
	# (succ, atype, pState) 	= trySimpleType TA_None pState
	  (succ2, type, pState)		= tryATypeToType atype pState
	= (succ&&succ2, type, pState)

tryBrackAType :: !ParseState -> (!Bool, AType, !ParseState)
tryBrackAType pState
	# (_, attr, pState)	= warnAnnotAndOptionalAttr pState
	= trySimpleType attr pState

trySimpleType :: !TypeAttribute !ParseState -> (!Bool, !AType, !ParseState)
trySimpleType attr pState
	# (token, pState)		= nextToken TypeContext pState
	= trySimpleTypeT token attr pState

is_tail_strict_list_or_nil pState
	# (square_close_position, pState) = getPosition pState
	# pState=tokenBack pState
	# (exclamation_position, pState) = getPosition pState
	# pState=tokenBack pState
	# (square_open_position, pState) = getPosition pState
	# (exclamation_token,pState) = nextToken TypeContext pState
	# (square_close_token,pState) = nextToken TypeContext pState
	| exclamation_position.fp_col+1==square_close_position.fp_col && exclamation_position.fp_line==square_close_position.fp_line
		&& (square_open_position.fp_col+1<>exclamation_position.fp_col || square_open_position.fp_line<>exclamation_position.fp_line)
		= (True,pState)
		= (False,pState)

trySimpleTypeT :: !Token !TypeAttribute !ParseState -> (!Bool, !AType, !ParseState)
trySimpleTypeT (IdentToken id) attr pState
	| isLowerCaseName id
		# (typevar, pState)	= nameToTypeVar id pState
		  (attr, pState)	= adjustAttribute attr typevar pState
		= (True, {at_attribute = attr, at_type = typevar}, pState)
	| otherwise // | isUpperCaseName id || isFunnyIdName id
	# (type, pState) = stringToType id pState
	= (True, {at_attribute = attr, at_type = type}, pState)
trySimpleTypeT SquareOpenToken attr pState
	# (token, pState) = nextToken TypeContext pState
	# (head_strictness,token,pState) = wantHeadStrictness token pState
		with
			wantHeadStrictness :: Token *ParseState -> *(!Int,!Token,!*ParseState)
			wantHeadStrictness ExclamationToken pState
				# (token,pState) = nextToken TypeContext pState
				= (HeadStrict,token,pState)
			wantHeadStrictness HashToken pState
				# (token,pState) = nextToken TypeContext pState
				= (HeadUnboxed,token,pState)
			wantHeadStrictness token pState
				= (HeadLazy,token,pState)
	| token == SquareCloseToken
		| head_strictness==HeadStrict
			# (tail_strict,pState) = is_tail_strict_list_or_nil pState
			| tail_strict
				# list_symbol = makeTailStrictListTypeSymbol HeadLazy 0
		  		= (True, {at_attribute = attr, at_type = TA list_symbol []}, pState)					
				# list_symbol = makeListTypeSymbol head_strictness 0
		  		= (True, {at_attribute = attr, at_type = TA list_symbol []}, pState)
		# list_symbol = makeListTypeSymbol head_strictness 0
  		= (True, {at_attribute = attr, at_type = TA list_symbol []}, pState)

	| token==ExclamationToken
		# (token,pState) = nextToken TypeContext pState
		| token==SquareCloseToken
			# list_symbol = makeTailStrictListTypeSymbol head_strictness 0
  			= (True, {at_attribute = attr, at_type = TA list_symbol []}, pState)
			= (False, {at_attribute = attr, at_type = TE}, parseError "List type" (Yes token) "]" pState)

	# (type, pState)	= wantAType (tokenBack pState)
	  (token, pState)	= nextToken TypeContext pState
	| token == SquareCloseToken
		# list_symbol = makeListTypeSymbol head_strictness 1
		= (True, {at_attribute = attr, at_type = TA list_symbol [type]}, pState)

	| token==ExclamationToken
		# (token,pState) = nextToken TypeContext pState
		| token==SquareCloseToken
			# list_symbol = makeTailStrictListTypeSymbol head_strictness 1
			= (True, {at_attribute = attr, at_type = TA list_symbol [type]}, pState)
			= (False, {at_attribute = attr, at_type = TE}, parseError "List type" (Yes token) "]" pState)

	// otherwise // token <> SquareCloseToken
		= (False, {at_attribute = attr, at_type = TE}, parseError "List type" (Yes token) "]" pState)
trySimpleTypeT OpenToken attr pState
	# (token, pState) = nextToken TypeContext pState
	| token == CommaToken
		# (tup_arity, pState)		= determine_arity_of_tuple 2 pState
		  tuple_symbol = makeTupleTypeSymbol tup_arity 0
		= (True, {at_attribute = attr, at_type = TA tuple_symbol []}, pState)	
	| token == ArrowToken
		# (token, pState) = nextToken TypeContext pState
		| token == CloseToken
			= (True, {at_attribute = attr, at_type = TArrow}, pState)
			= (False,{at_attribute = attr, at_type = TE},
				parseError "arrow type" (Yes token) ")" pState)
	// otherwise // token <> CommaToken
	# (annot_with_pos,atype, pState) = wantAnnotatedATypeWithPosition (tokenBack pState)
	  (token, pState)	= nextToken TypeContext pState
	| token == CloseToken
		# type				= atype.at_type
		  (attr, pState)	= determAttr  attr  atype.at_attribute type pState
		  pState = warnIfStrictAnnot annot_with_pos pState
		= (True, {at_attribute = attr, at_type = type}, pState)
	| token == CommaToken // TupleType
		# (satypes, pState)	= wantSequence CommaToken TypeContext pState
		  pState			= wantToken TypeContext "tuple type" CloseToken pState
		  satypes			= [{s_annotation=(case annot_with_pos of NoAnnot -> AN_None; StrictAnnotWithPosition _ -> AN_Strict),s_type=atype}:satypes]
		  arity				= length satypes
	 	  tuple_symbol = makeTupleTypeSymbol arity arity
		= (True, {at_attribute = attr, at_type = TAS tuple_symbol (atypes_from_satypes satypes) (strictness_from_satypes satypes)}, pState)
	// otherwise // token <> CloseToken && token <> CommaToken
		= (False, atype, parseError "Simple type" (Yes token) "')' or ','" pState)
where
	determine_arity_of_tuple :: !Int !ParseState -> (!Int, !ParseState)
	determine_arity_of_tuple arity pState
		# (token, pState) = nextToken TypeContext pState
		| CommaToken == token
  			= determine_arity_of_tuple (inc arity) pState
		| CloseToken == token
			= (arity, pState)
			= (arity, parseError "tuple type" (Yes token) ")" pState)
trySimpleTypeT CurlyOpenToken attr pState
	# (token, pState) = nextToken TypeContext pState
	| token == CurlyCloseToken
		# array_symbol = makeLazyArraySymbol 0
		= (True, {at_attribute = attr, at_type = TA array_symbol []}, pState)
	| token == HashToken
		# (token, pState) = nextToken TypeContext pState
		| token == CurlyCloseToken
			# array_symbol = makeUnboxedArraySymbol 0
			= (True, {at_attribute = attr, at_type = TA array_symbol []}, pState)
		// otherwise // token <> CurlyCloseToken
	  		# (atype, pState)			= wantAType (tokenBack pState)
  			  pState					= wantToken TypeContext "unboxed array type" CurlyCloseToken pState
  			  array_symbol = makeUnboxedArraySymbol 1
  			= (True, {at_attribute = attr, at_type = TA array_symbol [atype]}, pState)
	| token == ExclamationToken
		# (token, pState) = nextToken TypeContext pState
		| token == CurlyCloseToken
			# array_symbol = makeStrictArraySymbol 0
			= (True,  {at_attribute = attr, at_type = TA array_symbol []}, pState)
		// otherwise // token <> CurlyCloseToken
	  		# (atype,pState)			= wantAType (tokenBack pState)
  			  pState					= wantToken TypeContext "strict array type" CurlyCloseToken pState
  			  array_symbol = makeStrictArraySymbol 1
  			= (True, {at_attribute = attr, at_type = TA array_symbol [atype]}, pState)
  	// otherwise
  		# (atype,pState)			= wantAType (tokenBack pState)
  		  pState					= wantToken TypeContext "lazy array type" CurlyCloseToken pState
		  array_symbol = makeLazyArraySymbol 1
		= (True, {at_attribute = attr, at_type = TA array_symbol [atype]}, pState)
trySimpleTypeT StringTypeToken attr pState
	# type = makeStringType
	= (True, {at_attribute = attr, at_type = type}, pState)
trySimpleTypeT token attr pState
	# (bt, pState) = try token pState
	= case bt of
		Yes bt	-> (True , {at_attribute = attr, at_type = TB bt}, pState)
		no		-> (False, {at_attribute = attr, at_type = TE}   , pState)

instance try BasicType
where
	try IntTypeToken	 pState = (Yes BT_Int			, pState)
	try CharTypeToken	 pState	= (Yes BT_Char			, pState)
	try BoolTypeToken	 pState	= (Yes BT_Bool			, pState)
	try RealTypeToken	 pState	= (Yes BT_Real			, pState)
	try DynamicTypeToken pState	= (Yes BT_Dynamic		, pState)
	try FileTypeToken	 pState = (Yes BT_File			, pState)
	try WorldTypeToken	 pState = (Yes BT_World			, pState)
	try _				 pState = (No					, tokenBack pState)

determAnnot :: !Annotation !Annotation !ParseState -> (!Annotation, !ParseState)
determAnnot AN_None annot2  pState = (annot2, pState)
determAnnot annot1  AN_None pState = (annot1, pState)
determAnnot annot1  annot2  pState
	= (annot1, parseError "simple type" No ("More type annotations, "+toString annot1+" and "+toString annot2+", than") pState)

determAttr :: !TypeAttribute !TypeAttribute !Type !ParseState -> (!TypeAttribute, !ParseState)
determAttr TA_None  attr2   type pState = adjustAttribute attr2 type pState
determAttr attr1    TA_None type pState = adjustAttribute attr1 type pState
determAttr attr1    attr2   type pState
	= (attr1, parseError "simple type" No ("More type attributes, "+toString attr1+" and "+toString attr2+", than") pState)

wantDynamicType :: !*ParseState -> *(!DynamicType,!*ParseState)
wantDynamicType pState 
	# (type_vars, pState) = optionalUniversalQuantifiedVariables pState
	  (type, pState) = want pState
	= ({ dt_uni_vars = type_vars, dt_type = type, dt_global_vars = [] }, pState)

optionalExistentialQuantifiedVariables :: !*ParseState -> *(![ATypeVar],!*ParseState)
optionalExistentialQuantifiedVariables pState
	# (token, pState) = nextToken TypeContext pState
	= case token of
		ExistsToken
			# (vars, pState) = wantList "existential quantified variable(s)" tryQuantifiedTypeVar pState
			-> (vars, wantToken TypeContext "Existential Quantified Variables" ColonToken pState)
		_	-> ([], tokenBack pState)

/*  Sjaak 041001
where
	try_existential_type_var :: !ParseState -> (Bool,ATypeVar,ParseState)
	try_existential_type_var pState
		# (token, pState)	= nextToken TypeContext pState
		= case token of
			DotToken
				# (typevar, pState)	= wantTypeVar pState
				-> (True, {atv_attribute = TA_Anonymous, atv_annotation = AN_None, atv_variable = typevar}, pState)
			_
				# (succ, typevar, pState)	= tryTypeVarT token pState
				| succ
					#	atypevar = {atv_attribute = TA_None, atv_annotation = AN_None, atv_variable = typevar}
					->	(True,atypevar,pState)
					->	(False,abort "no ATypeVar",pState)
<<<<<<< parse.icl
=======
*/

optionalUniversalQuantifiedVariables :: !*ParseState -> *(![ATypeVar],!*ParseState)
optionalUniversalQuantifiedVariables pState
	# (token, pState) = nextToken TypeContext pState
	= case token of
		ForAllToken
			# (vars, pState) = wantList "universal quantified variable(s)" tryQuantifiedTypeVar pState
			-> (vars, wantToken TypeContext "Universal Quantified Variables" ColonToken pState)
		_	-> ([], tokenBack pState)

tryQuantifiedTypeVar :: !ParseState -> (Bool, ATypeVar, ParseState)
tryQuantifiedTypeVar pState
	# (token, pState)			= nextToken TypeContext pState
 	  (succ, attr, pState)		= try_attribute token pState
 	| succ
		# (typevar, pState)	= wantTypeVar pState
		  (attr, pState)	= adjustAttributeOfTypeVariable attr typevar.tv_name pState
		= (True, {atv_attribute = attr, atv_variable = typevar}, pState)
	# (succ, typevar, pState) = tryTypeVarT token pState
	| succ
		= (True, {atv_attribute = TA_None, atv_variable = typevar}, pState)
		= (False, abort "no ATypeVar", pState)
where			
	try_attribute DotToken      pState = (True,	TA_Anonymous,	pState)
	try_attribute AsteriskToken	pState = (True,	TA_Unique,		pState)
	try_attribute token      	pState = (False,	TA_None,	pState)

tryATypeToType :: !AType !ParseState -> (!Bool, !Type, !ParseState)
tryATypeToType atype pState
/*	| atype.at_annotation <> AN_None
		= ( False
		  , atype.at_type
		  , parseError "simple type" No ("type instead of type annotation "+toString atype.at_annotation) pState
		  )
*/	| atype.at_attribute <> TA_None
		= ( False
		  , atype.at_type
		  , parseError "simple type" No ("type instead of type attribute "+toString atype.at_attribute) pState
		  )
	// otherwise
		= (True, atype.at_type, pState)

/*
	Expressions
*/
cIsAPattern		:== True
cIsNotAPattern	:== False

wantExpression :: !Bool !ParseState -> (!ParsedExpr, !ParseState)
wantExpression is_pattern pState
	# (token, pState) = nextToken FunctionContext pState
	= case token of
		CharListToken charList // To produce a better error message
			->	(PE_Empty,  parseError "Expression" No ("List brackets, [ and ], around charlist '"+charList+"'") pState)
		_	| is_pattern
				->	wantLhsExpressionT token pState
				->	wantRhsExpressionT token pState

wantRhsExpressionT  :: !Token !ParseState -> (!ParsedExpr, !ParseState)
wantRhsExpressionT token pState
	# (succ, expr, pState) = trySimpleRhsExpressionT token pState
	| succ
		# (exprs, pState) = parseList trySimpleRhsExpression pState
		= (combineExpressions expr exprs, pState)
		= case token of
			CharListToken charList
				-> (PE_Empty,  parseError "RHS expression" No ("List brackets, [ and ], around charlist '"+charList+"'") pState)
			_	-> (PE_Empty,  parseError "RHS expression" (Yes token) "<expression>" pState)

wantLhsExpressionT  :: !Token !ParseState -> (!ParsedExpr, !ParseState)
wantLhsExpressionT (IdentToken name) pState /* to make a=:C x equivalent to a=:(C x) */
	| isLowerCaseName name
		# (id, pState)		= stringToIdent name IC_Expression pState
		  (token, pState)	= nextToken FunctionContext pState
		| token == DefinesColonToken 
			# (token, pState)	= nextToken FunctionContext pState
			= case token of
				IdentToken ident
					| ~ (isLowerCaseName ident)
						#	(constructor, pState) = stringToIdent ident IC_Expression pState
							(args, pState)	= parseList trySimpleLhsExpression pState
						->	(PE_Bound { bind_dst = id, bind_src = combineExpressions (PE_Ident constructor) args }, pState)
				_	# (succ, expr, pState) = trySimpleLhsExpressionT token pState
					| succ
						# expr1 = PE_Bound { bind_dst = id, bind_src = expr }
						# (exprs, pState) = parseList trySimpleLhsExpression pState
						->	(combineExpressions expr1 exprs, pState)
					// not succ
						-> (PE_Empty,  parseError "LHS expression" (Yes token) "<expression>" pState)
		| token == DoubleColonToken
			# (dyn_type, pState) = wantDynamicType pState
			= (PE_DynamicPattern (PE_Ident id) dyn_type, pState)
		// token <> DefinesColonToken // token back and call to wantLhsExpressionT2 would do also.
		# (exprs, pState) = parseList trySimpleLhsExpression (tokenBack pState)
		= (combineExpressions (PE_Ident id) exprs, pState)
wantLhsExpressionT token pState
	= wantLhsExpressionT2 token pState

wantLhsExpressionT2  :: !Token !ParseState -> (!ParsedExpr, !ParseState)
wantLhsExpressionT2 token pState
	# (succ, expr, pState) = trySimpleLhsExpressionT token pState
	| succ
		# (exprs, pState) = parseList trySimpleLhsExpression pState
		= (combineExpressions expr exprs, pState)
		= (PE_Empty,  parseError "LHS expression" (Yes token) "<expression>" pState)

combineExpressions expr []
	= expr
combineExpressions expr exprs
	= make_app_exp expr exprs
where
	make_app_exp exp []
		= exp
	make_app_exp exp exprs
		= PE_List [exp : exprs]

trySimpleLhsExpression :: !ParseState -> (!Bool, !ParsedExpr, !ParseState)
trySimpleLhsExpression pState
	# (token, pState) = nextToken FunctionContext pState
	= trySimpleLhsExpressionT token pState

trySimpleLhsExpressionT ::  !Token !ParseState -> (!Bool, !ParsedExpr, !ParseState)
trySimpleLhsExpressionT token pState
	# (succ, expr, pState) = trySimpleExpressionT token cIsAPattern pState
	| succ
		# (token, pState) = nextToken FunctionContext pState
		| token == DoubleColonToken
			# (dyn_type, pState) = wantDynamicType pState
			= (True, PE_DynamicPattern expr dyn_type, pState)
			= (True, expr, tokenBack pState)
		= (False, PE_Empty, pState)

trySimpleRhsExpression :: !ParseState -> (!Bool, !ParsedExpr, !ParseState)
trySimpleRhsExpression pState
	# (token, pState) = nextToken FunctionContext pState
	= trySimpleRhsExpressionT token pState
	
trySimpleRhsExpressionT :: !Token !ParseState -> (!Bool, !ParsedExpr, !ParseState)
trySimpleRhsExpressionT token pState
	# (succ, expr, pState) = trySimpleExpressionT token cIsNotAPattern pState
	| succ
		# (expr, pState) = extend_expr_with_selectors expr pState
		= (True, expr, pState)
		= (False, PE_Empty, pState)
where
	extend_expr_with_selectors :: !ParsedExpr !ParseState -> (!ParsedExpr, !ParseState)
	extend_expr_with_selectors exp pState 
   		# (token, pState) = nextToken FunctionContext pState
		| token == DotToken
			# (token, pState) = nextToken FunctionContext pState
			  (selectors, pState) = wantSelectors token pState
			= (PE_Selection ParsedNormalSelector exp selectors, pState)
		| token == ExclamationToken
			# (token, pState) = nextToken FunctionContext pState
// JVG added for strict lists:
			| token==SquareCloseToken
				= (exp, tokenBack (tokenBack pState))
//			
			#  (selectors, pState) = wantSelectors token pState
			= (PE_Selection (ParsedUniqueSelector False) exp selectors, pState)
		| otherwise
			= (exp, tokenBack pState)

wantSelectors :: Token *ParseState -> *(![ParsedSelection], !*ParseState)
wantSelectors token pState
			# (selector, pState) = want_selector token pState
			  (token, pState) = nextToken FunctionContext pState
			| token == DotToken
				# (token, pState) = nextToken FunctionContext pState
				  (selectors, pState) = wantSelectors token pState
				= (selector ++ selectors, pState)
				= (selector, tokenBack pState)
where
	want_selector :: !Token !*ParseState -> *(![ParsedSelection], !*ParseState)
	want_selector SquareOpenToken pState
		# (array_selectors, pState) = want_array_selectors pState
		= (array_selectors, wantToken FunctionContext "array selector" SquareCloseToken pState)
		where
			want_array_selectors :: !*ParseState -> *(![ParsedSelection], !*ParseState)
			want_array_selectors pState
	  			# (index_expr, pState) = wantExpression cIsNotAPattern pState
				  selector = PS_Array index_expr
	  			  (token, pState) = nextToken  FunctionContext pState
				| token == CommaToken
					# (selectors, pState) = want_array_selectors pState
					= ([selector : selectors], pState)
					= ([selector], tokenBack pState)

	want_selector (IdentToken name) pState
		| isUpperCaseName name
	  		# (field, pState) = want (wantToken FunctionContext "array selector" DotToken pState)
	  		  (field_id, pState) = stringToIdent field IC_Selector pState
	  		  (type_id, pState) = stringToIdent name IC_Type pState
			= ([PS_Record field_id (Yes type_id)], pState)
	  		# (field_id, pState) = stringToIdent name IC_Selector pState
			= ([PS_Record field_id No], pState)
	want_selector token pState
		= ([PS_Erroneous], parseError "simple RHS expression" (Yes token) "<selector>" pState)

trySimpleExpression :: !Bool !ParseState -> (!Bool, !ParsedExpr, !ParseState)
trySimpleExpression is_pattern pState
	| is_pattern
		= trySimpleLhsExpression pState
		= trySimpleRhsExpression pState

trySimpleExpressionT :: !Token !Bool !ParseState -> (!Bool, !ParsedExpr, !ParseState)
trySimpleExpressionT (IdentToken name) is_pattern pState
	| isLowerCaseName name
	# (id, pState) = stringToIdent name IC_Expression pState
	| is_pattern
		# (token, pState) = nextToken FunctionContext pState
		| token == DefinesColonToken
			# (succ, expr, pState) = trySimpleExpression is_pattern pState
			| succ
				= (True, PE_Bound { bind_dst = id, bind_src = expr }, pState)
				= (True, PE_Empty, parseError "simple expression" No "expression" pState)
			// token <> DefinesColonToken
			= (True, PE_Ident id, tokenBack pState)
		// not is_pattern
		# (token, pState) = nextToken FunctionContext pState
		| token == GenericOpenToken
			# (kind, pState) = wantKind pState	
			= (True, PE_Generic id kind, pState)
			= (True, PE_Ident id, tokenBack pState)			
			
trySimpleExpressionT (IdentToken name) is_pattern pState
//	| isUpperCaseName name || ~ is_pattern
	# (id, pState) = stringToIdent name IC_Expression pState
	# (token, pState) = nextToken FunctionContext pState
	| token == GenericOpenToken
		# (kind, pState) = wantKind pState	
		= (True, PE_Generic id kind, pState)
		= (True, PE_Ident id, tokenBack pState)

trySimpleExpressionT SquareOpenToken is_pattern pState
	# (list_expr, pState) = wantListExp is_pattern pState
	= (True, list_expr, pState)
trySimpleExpressionT OpenToken is_pattern pState
	# (args=:[exp:exps], pState) = want_expression_list is_pattern pState
	  pState = wantToken FunctionContext "expression list" CloseToken pState
	| isEmpty exps
		= case exp of
			PE_Ident id
				-> (True, PE_List [exp], pState)
			_
				-> (True, exp, pState)
		= (True, PE_Tuple args, pState)
where
	want_expression_list is_pattern pState
		# (expr, pState) = wantExpression is_pattern pState
		  (token, pState) = nextToken FunctionContext pState
		| token == CommaToken
			# (exprs, pState) = want_expression_list is_pattern pState
			= ([expr : exprs], pState)
			= ([expr], tokenBack pState)
trySimpleExpressionT CurlyOpenToken is_pattern pState
	# (rec_or_aray_exp, pState) = wantRecordOrArrayExp is_pattern pState 
	= (True, rec_or_aray_exp, pState)
trySimpleExpressionT (IntToken int_string) is_pattern pState
	# (ok,int) = string_to_int int_string
		with
		string_to_int s
			| len==0
				= (False,0)
			| s.[0] == '-'
				| len>2 && s.[1]=='0' /* octal */
					= (False,0)
					# (ok,int) = (string_to_int2 1 0 s)
					=	(ok,~int)
			| s.[0] == '+'
				| len>2&& s.[1]=='0' /* octal */
					= (False,0)
					=	string_to_int2 1 0 s
			| s.[0]=='0' && len>1 /* octal */
				= (False,0)
				=	string_to_int2 0 0 s
		 where
			len = size s

			string_to_int2:: !Int !Int !{#Char} -> (!Bool,!Int)
			string_to_int2 posn val s
				| len==posn
					= (True,val)
				# n =	toInt (s.[posn]) - toInt '0'
				|	0<=n && n<= 9
					=	string_to_int2 (posn+1) (n+val*10) s
					=	(False,0)
	| ok
		= (True, PE_Basic (BVInt int), pState)
		= (True, PE_Basic (BVI int_string), pState)
trySimpleExpressionT (StringToken string) is_pattern pState
	= (True, PE_Basic (BVS string), pState)
trySimpleExpressionT (BoolToken bool) is_pattern pState
	= (True, PE_Basic (BVB bool), pState)
trySimpleExpressionT (CharToken char) is_pattern pState
	= (True, PE_Basic (BVC char), pState)
trySimpleExpressionT (RealToken real) is_pattern pState
	= (True, PE_Basic (BVR real), pState)
trySimpleExpressionT token is_pattern pState
	| is_pattern
		| token == WildCardToken
			= (True, PE_WildCard, pState)
			= (False, PE_Empty, tokenBack pState)
		= trySimpleNonLhsExpressionT token pState

trySimpleNonLhsExpressionT :: !Token *ParseState -> *(!Bool,!ParsedExpr,!*ParseState)
trySimpleNonLhsExpressionT BackSlashToken pState
	# (lam_ident, pState)	= internalIdent (toString backslash) pState
	  (lam_args, pState) 	= wantList "arguments" trySimpleLhsExpression pState
	  pState				= want_lambda_sep pState
	  (exp, pState)			= wantExpression cIsNotAPattern pState
	  (file_name, line_nr, pState)	
	  						= getFileAndLineNr pState
	  position				= FunPos file_name line_nr lam_ident.id_name
	= (True, PE_Lambda lam_ident lam_args exp position, pState)
	where
		want_lambda_sep pState
			# (token, pState) = nextToken FunctionContext pState
			= case token of
				ArrowToken	-> pState
				EqualToken	-> pState
				DotToken	-> pState
	  			_			-> parseError "lambda expression" (Yes token) "-> or =" (tokenBack pState)
trySimpleNonLhsExpressionT (LetToken strict) pState // let! is not supported in Clean 2.0
	| strict				= (False, PE_Empty, parseError "Expression" No "let! (strict let) not supported in this version of Clean, expression" pState)
	// otherwise
	# (let_binds, pState)	= wantLocals pState
	  pState				= wantToken FunctionContext "let expression" InToken pState
	  (let_expr, pState)	= wantExpression cIsNotAPattern pState
	= (True, PE_Let strict let_binds let_expr, pState)
trySimpleNonLhsExpressionT CaseToken pState
   	# (case_exp, pState)		= wantCaseExp pState
	= (True, case_exp, pState)
trySimpleNonLhsExpressionT IfToken pState
	# (if_ident, pState) 		= internalIdent "_if" pState
   	  (cond_exp, pState)		= want_simple_expression "condition of if" pState
   	  (then_exp, pState)		= want_simple_expression "then-part of if" pState
   	  (else_exp, pState)		= want_simple_expression "else-part of if" pState
	= (True, PE_If if_ident cond_exp then_exp else_exp, pState)
where
	want_simple_expression error pState
		# (succ, expr, pState) = trySimpleRhsExpression pState
		| succ
			= (expr, pState)
			= (PE_Empty,  parseError error No "<expression>" pState)
trySimpleNonLhsExpressionT DynamicToken pState
	# (dyn_expr, pState) = wantExpression cIsNotAPattern pState
	  (token, pState) = nextToken FunctionContext pState
	| token == DoubleColonToken
		# (dyn_type, pState) = wantDynamicType pState
		= (True, PE_Dynamic dyn_expr (Yes dyn_type), pState)
		= (True, PE_Dynamic dyn_expr No, tokenBack pState)
trySimpleNonLhsExpressionT token pState
	= (False, PE_Empty, tokenBack pState)

HeadLazy:==0
HeadStrict:==1
HeadUnboxed:==2
HeadOverloaded:==3;
HeadUnboxedAndTailStrict:==4;

wantListExp :: !Bool !ParseState -> (ParsedExpr, !ParseState)
wantListExp is_pattern pState
	# pState=appScanState setNoNewOffsideForSeqLetBit pState
	# (token, pState) = nextToken FunctionContext pState
	# pState=appScanState clearNoNewOffsideForSeqLetBit pState	
	# (head_strictness,token,pState) = want_head_strictness token pState
		with
			want_head_strictness :: Token *ParseState -> *(!Int,!Token,!*ParseState)
			want_head_strictness ExclamationToken pState
				# (token,pState) = nextToken FunctionContext pState
				= (HeadStrict,token,pState)
			want_head_strictness (SeqLetToken strict) pState
				# (token,pState) = nextToken FunctionContext pState
				| strict
					= (HeadUnboxedAndTailStrict,token,pState);
					= (HeadUnboxed,token,pState)
			want_head_strictness BarToken pState
				# (token,pState) = nextToken FunctionContext pState
				= (HeadOverloaded,token,pState)
			want_head_strictness token pState
				= (HeadLazy,token,pState)
	| token==ExclamationToken && (head_strictness<>HeadOverloaded && head_strictness<>HeadUnboxedAndTailStrict)
		# (token, pState) = nextToken FunctionContext pState
		| token==SquareCloseToken
			= (makeTailStrictNilExpression head_strictness is_pattern,pState)
			= (PE_Empty,parseError "list" (Yes token) (toString SquareCloseToken) pState)
	| token==SquareCloseToken
		| head_strictness==HeadUnboxedAndTailStrict
			= (makeTailStrictNilExpression HeadUnboxed is_pattern,pState)
		| head_strictness==HeadStrict
			# (tail_strict,pState) = is_tail_strict_list_or_nil pState
			| tail_strict
				= (makeTailStrictNilExpression HeadLazy is_pattern,pState)
				= (makeNilExpression head_strictness is_pattern,pState)
			= (makeNilExpression head_strictness is_pattern,pState)
	| head_strictness==HeadUnboxedAndTailStrict
		= (PE_Empty,parseError "list" (Yes token) (toString SquareCloseToken) pState)
	| head_strictness==HeadLazy && (case token of (IdentToken "!!") -> True; _ -> False)
		# (next_token,pState) = nextToken FunctionContext pState
		| next_token==SquareCloseToken
			= (makeTailStrictNilExpression HeadStrict is_pattern,pState)
			= want_LGraphExpr token [] head_strictness (tokenBack pState)
		= want_LGraphExpr token [] head_strictness pState
	where
		want_LGraphExpr token acc head_strictness pState
			= case token of
				CharListToken chars
					->	want_list (add_chars (fromString chars) acc) pState
					with
						add_chars [] 			acc	= acc
						add_chars ['\\',c1,c2,c3:r] acc
							| c1>='0' && c1<='7'
								= add_chars r [PE_Basic (BVC (toString ['\'','\\',c1,c2,c3,'\''])): acc]
						add_chars ['\\',c:r] acc = add_chars r [PE_Basic (BVC (toString ['\'','\\',c,'\''])): acc]
						add_chars [c:r] 		acc	= add_chars r [PE_Basic (BVC (toString ['\'',c,'\''])): acc]
				_	#	(exp, pState) = (if is_pattern (wantLhsExpressionT token) (wantRhsExpressionT token)) pState
					->	want_list [exp: acc] pState
		where
			want_list acc pState
				# (token, pState) = nextToken FunctionContext pState
				= case token of
					SquareCloseToken
						#	nil_expr = makeNilExpression head_strictness is_pattern
						->	(gen_cons_nodes acc nil_expr,pState)
					ExclamationToken
						| head_strictness<>HeadOverloaded
							# (token, pState) = nextToken FunctionContext pState
							| token==SquareCloseToken
								# nil_expr = makeTailStrictNilExpression head_strictness is_pattern
								->	(gen_tail_strict_cons_nodes acc nil_expr,pState)
								-> (PE_Empty,parseError "list" (Yes token) (toString SquareCloseToken) pState)
					CommaToken
						#	(token, pState)	= nextToken FunctionContext pState
						->	want_LGraphExpr token acc head_strictness pState
					ColonToken
						# (exp, pState)		= wantExpression is_pattern pState
						# (token,pState)	= nextToken FunctionContext pState
						| token==SquareCloseToken
							-> (gen_cons_nodes acc exp,pState)
						| token==ExclamationToken && head_strictness<>HeadOverloaded
							# pState = wantToken FunctionContext "list" SquareCloseToken pState
							-> (gen_tail_strict_cons_nodes acc exp,pState)
						| token==ColonToken // to allow [1:2:[]] etc.
							-> want_list [exp:acc] (tokenBack pState)
							# pState = parseError "list" (Yes token) "] or :" pState
							-> (gen_cons_nodes acc exp,pState)
					DotDotToken
						| is_pattern
						->	(PE_Empty, parseError "want list expression" No "No dot dot expression in a pattern" pState)
						| length acc > 2 || isEmpty acc
						#	nil_expr = makeNilExpression head_strictness is_pattern
							pState				= parseError "list expression" No "one or two expressions before .." pState
						->	(gen_cons_nodes acc nil_expr,pState)
						#	(token, pState)		= nextToken FunctionContext pState
						->	case token of
							 SquareCloseToken
								->	case acc of
										[e]	-> (PE_Sequ (SQ_From e), pState)
										[e2,e1]
											-> (PE_Sequ (SQ_FromThen e1 e2), pState)
										_	-> abort "Error 1 in WantListExp"
							 _	#	(exp, pState)	= wantRhsExpressionT token pState
									pState			= wantToken FunctionContext "dot dot expression" SquareCloseToken pState
								->	case acc of
										[e]	-> (PE_Sequ (SQ_FromTo e exp), pState)
										[e2,e1]
											-> (PE_Sequ (SQ_FromThenTo e1 e2 exp), pState)
										_	-> abort "Error 2 in WantListExp"
					DoubleBackSlashToken
						| is_pattern
						->	(PE_Empty, parseError "want list expression" No "No \\\\ expression in a pattern" pState)
						| length acc == 1
						->	wantListComprehension head_strictness (acc!!0)  pState
						// otherwise // length acc <> 1
						#	nil_expr = makeNilExpression head_strictness is_pattern
							pState				= parseError "list comprehension" No "one expressions before \\\\" pState
						->	(gen_cons_nodes acc nil_expr,pState)
					_	#	nil_expr = makeNilExpression head_strictness is_pattern
							pState	= parseError "list" (Yes token) "list element separator" pState
						->	(gen_cons_nodes acc nil_expr,pState)
			
			gen_cons_nodes [] exp
				= exp
			gen_cons_nodes l exp
				= gen_cons_nodes l exp
			where
				cons_ident_exp = makeConsIdentExpression head_strictness is_pattern
				
				gen_cons_nodes [e:r] exp
					= gen_cons_nodes r (PE_List [cons_ident_exp,e,exp])
				gen_cons_nodes [] exp
					= exp
	
			gen_tail_strict_cons_nodes [] exp
				= exp
			gen_tail_strict_cons_nodes r exp
				= gen_tail_strict_cons_nodes r exp
			where
				tail_strict_cons_ident_exp = makeTailStrictConsIdentExpression head_strictness is_pattern
				
				gen_tail_strict_cons_nodes [e:r] exp
					= gen_tail_strict_cons_nodes r (PE_List [tail_strict_cons_ident_exp,e,exp])
				gen_tail_strict_cons_nodes [] exp
					= exp

makeNilExpression :: Int Bool -> ParsedExpr
makeNilExpression head_strictness is_pattern
	# pre_def_nil_index= if (head_strictness==HeadLazy)
							PD_NilSymbol
						(if (head_strictness==HeadStrict)
							PD_StrictNilSymbol
						(if (head_strictness==HeadOverloaded)
							(if is_pattern PD_OverloadedNilSymbol PD_nil)
							(if is_pattern PD_UnboxedNilSymbol PD_nil_u)))
	#! nil_ident = predefined_idents.[pre_def_nil_index]
	= PE_Ident nil_ident

makeTailStrictNilExpression :: Int Bool -> ParsedExpr
makeTailStrictNilExpression head_strictness is_pattern
	# pre_def_nil_index= if (head_strictness==HeadLazy)
							PD_TailStrictNilSymbol
						(if (head_strictness==HeadStrict)
							PD_StrictTailStrictNilSymbol
							(if is_pattern PD_UnboxedTailStrictNilSymbol PD_nil_uts))
	#! nil_ident = predefined_idents.[pre_def_nil_index]
	= PE_Ident nil_ident

makeConsIdentExpression :: Int Bool -> ParsedExpr
makeConsIdentExpression head_strictness is_pattern
	# pre_def_cons_index=if (head_strictness==HeadLazy)
							PD_ConsSymbol
						(if (head_strictness==HeadStrict)
							PD_StrictConsSymbol
						(if (head_strictness==HeadOverloaded)
							(if is_pattern PD_OverloadedConsSymbol PD_cons)
							(if is_pattern PD_UnboxedConsSymbol PD_cons_u)))
	#! cons_ident = predefined_idents.[pre_def_cons_index]
	= PE_Ident cons_ident

cons_and_nil_symbol_index HeadLazy = (PD_ConsSymbol,PD_NilSymbol)
cons_and_nil_symbol_index HeadStrict = (PD_StrictConsSymbol,PD_StrictNilSymbol)
cons_and_nil_symbol_index HeadUnboxed = (PD_cons_u,PD_nil_u)
cons_and_nil_symbol_index HeadOverloaded = (PD_cons,PD_nil)

makeTailStrictConsIdentExpression :: Int Bool -> ParsedExpr
makeTailStrictConsIdentExpression head_strictness is_pattern
	# pre_def_cons_index=if (head_strictness==HeadLazy)
							PD_TailStrictConsSymbol
						(if (head_strictness==HeadStrict)
							PD_StrictTailStrictConsSymbol
							(if is_pattern PD_UnboxedTailStrictConsSymbol PD_cons_uts))
	#! cons_ident = predefined_idents.[pre_def_cons_index]
	= PE_Ident cons_ident

tail_strict_cons_and_nil_symbol_index HeadLazy = (PD_TailStrictConsSymbol,PD_TailStrictNilSymbol)
tail_strict_cons_and_nil_symbol_index HeadStrict = (PD_StrictTailStrictConsSymbol,PD_StrictTailStrictNilSymbol)
tail_strict_cons_and_nil_symbol_index HeadUnboxed = (PD_cons_uts,PD_nil_uts)

/*
	(List and Array) Comprehensions
*/

wantArrayComprehension :: !ParsedExpr !ParseState -> (!ParsedExpr, !ParseState)
wantArrayComprehension exp pState
	# (qualifiers, pState) = wantQualifiers pState
	= (PE_ArrayCompr exp qualifiers, wantToken FunctionContext "array comprehension" CurlyCloseToken pState)

wantListComprehension :: !Int !ParsedExpr !ParseState -> (!ParsedExpr, !ParseState)
wantListComprehension head_strictness exp pState
	# (qualifiers, pState) = wantQualifiers pState
	# (token, pState) = nextToken FunctionContext pState
	| token==SquareCloseToken
		# (cons_index,nil_index) = cons_and_nil_symbol_index head_strictness
		= (PE_ListCompr cons_index nil_index exp qualifiers, pState)
	| token==ExclamationToken && head_strictness<>HeadOverloaded
		# pState = wantToken FunctionContext "list comprehension" SquareCloseToken pState
		# (tail_strict_cons_index,tail_strict_nil_index) = tail_strict_cons_and_nil_symbol_index head_strictness
		= (PE_ListCompr tail_strict_cons_index tail_strict_nil_index exp qualifiers, pState)
		# pState = parseError "list" (Yes token) (toString SquareCloseToken) pState
		# (cons_index,nil_index) = cons_and_nil_symbol_index head_strictness
		= (PE_ListCompr cons_index nil_index exp qualifiers, pState)

wantQualifiers :: !ParseState -> (![Qualifier], !ParseState)
wantQualifiers pState
	# (qual, pState) = want_qualifier pState
	  (token, pState) = nextToken FunctionContext pState
	| token == CommaToken
		# (quals, pState) = wantQualifiers pState
		= ([qual : quals], pState)
		= ([qual], tokenBack pState)
where
	want_qualifier :: !ParseState -> (!Qualifier, !ParseState)
	want_qualifier pState
		# (qual_position, pState) = getPosition pState
		  (qual_filename, pState) = accScanState getFilename pState
		  (lhs_expr, pState) = wantExpression cIsAPattern pState
		  (token, pState) = nextToken FunctionContext pState
		| token == LeftArrowToken
			= want_generators IsListGenerator (toLineAndColumn qual_position) qual_filename lhs_expr pState
		| token == LeftArrowColonToken
			= want_generators IsArrayGenerator (toLineAndColumn qual_position) qual_filename lhs_expr pState
		| token == LeftArrowWithBarToken
			= want_generators IsOverloadedListGenerator (toLineAndColumn qual_position) qual_filename lhs_expr pState
			= ({qual_generators = [], qual_filter = No, qual_position = {lc_line = 0, lc_column = 0}, qual_filename = "" },
					parseError "comprehension: qualifier" (Yes token) "qualifier(s)" pState)

	want_generators :: !GeneratorKind !LineAndColumn !FileName !ParsedExpr !ParseState -> (!Qualifier, !ParseState)
	want_generators gen_kind qual_position qual_filename pattern_exp pState
		# (gen_position, pState)			= getPosition pState
		# (gen_expr, pState) = wantExpression cIsNotAPattern pState
		  (token, pState) = nextToken FunctionContext pState
		  generator = { gen_kind = gen_kind, gen_expr = gen_expr, gen_pattern = pattern_exp,
							gen_position = toLineAndColumn gen_position
			}
		| token == BarToken
			# (filter_expr, pState) = wantExpression cIsNotAPattern pState
			= ( { qual_generators = [generator], qual_filter = Yes filter_expr
				, qual_position = qual_position, qual_filename = qual_filename }
			  , pState
			  )
		| token == AndToken
			# (qualifier, pState) = want_qualifier pState
			= ({qualifier & qual_generators = [ generator : qualifier.qual_generators] }, pState)
		= ( {qual_generators = [generator], qual_filter = No, qual_position = qual_position, qual_filename = qual_filename}
		  ,	tokenBack pState
		  )

/**
	Case Expressions
**/

wantCaseExp :: !ParseState -> (ParsedExpr, !ParseState)
wantCaseExp pState
	# (case_ident, pState) = internalIdent "_c" pState
	  (case_exp, pState)	= wantExpression cIsNotAPattern pState
	  pState				= wantToken FunctionContext "case expression" OfToken pState
	  pState				= wantBeginGroup "case" pState
	  (case_alts, (definingSymbol,pState))
	  						= parseList tryCaseAlt (RhsDefiningSymbolCase, pState)
	  (found, alt, pState)	= tryLastCaseAlt definingSymbol pState
	| found
		= (PE_Case case_ident case_exp (case_alts++[alt]), wantEndCase pState)
		= (PE_Case case_ident case_exp case_alts, wantEndCase pState)
where
	tryCaseAlt :: (!RhsDefiningSymbol, !ParseState) -> (!Bool, CaseAlt, (!RhsDefiningSymbol, !ParseState))
	tryCaseAlt (definingSymbol, pState)
		# (succ, pattern, pState) = try_pattern pState
		| succ
			# (rhs, definingSymbol, pState) = wantRhs True definingSymbol pState
			= (True, { calt_pattern = pattern, calt_rhs = rhs }, (definingSymbol, pState))
		// otherwise // ~ succ
			= (False, abort "no case alt", (definingSymbol, pState))
	
	tryLastCaseAlt ::  !RhsDefiningSymbol !ParseState -> (!Bool, CaseAlt, !ParseState)
	tryLastCaseAlt definingSymbol pState
		# (token, pState)	= nextToken FunctionContext pState
		| isDefiningSymbol definingSymbol token
			#	pState			= tokenBack pState
				(rhs, _, pState)
								= wantRhs True definingSymbol pState
			= (True, { calt_pattern = PE_WildCard, calt_rhs = rhs }, pState)
		| token == OtherwiseToken
			# (token, pState)	= nextToken FunctionContext pState
			  pState			= tokenBack pState
			| isDefiningSymbol definingSymbol token
				# (rhs, _, pState) = wantRhs True definingSymbol pState
				= (True, { calt_pattern = PE_WildCard, calt_rhs = rhs }, pState)
				= (False, abort "no case alt", pState)
			= (False, abort "no case alt", tokenBack pState)

//	caseSeperator t = t == EqualToken || t == ArrowToken // to enable Clean 1.3.x case expressions

	try_pattern :: !ParseState -> (!Bool, ParsedExpr, !ParseState)
	try_pattern pState
		# (succ, expr, pState) = trySimpleLhsExpression pState
		| succ
			# (succ, expr2, pState) = trySimpleLhsExpression pState
			| succ
				# (exprs, pState) = parseList trySimpleLhsExpression pState
				= (True, PE_List [expr,expr2 : exprs], pState)
				= (True, expr, pState)
			= (False, abort "no expression", pState)

:: NestedUpdate =
	{	nu_selectors :: ![ParsedSelection]
	,	nu_update_expr :: !ParsedExpr
	}

errorIdent :: Ident
errorIdent
	=	{id_name = "<<error>>", id_info = nilPtr}

buildNodeDef :: ParsedExpr ParsedExpr -> ParsedDefinition
buildNodeDef lhsExpr rhsExpr
	=	PD_NodeDef NoPos lhsExpr rhs
	where
		rhs	=
			{ rhs_alts
				= UnGuardedExpr
					{ ewl_nodes		= []
					, ewl_locals	= LocalParsedDefs []
					, ewl_expr		= rhsExpr
					, ewl_position	= NoPos
					}
			, rhs_locals
				= LocalParsedDefs []
			}

/**
	Record expressions
**/

wantRecordOrArrayExp :: !Bool !ParseState -> (ParsedExpr, !ParseState)
wantRecordOrArrayExp is_pattern pState
	# (token, pState) = nextToken FunctionContext pState
	| is_pattern
		| token == SquareOpenToken
			# (elems, pState) =  want_array_assignments cIsAPattern pState
			= (PE_ArrayPattern elems, wantToken FunctionContext "array selections in pattern" CurlyCloseToken pState)
		| token == CurlyCloseToken
			= (PE_Empty, parseError "record or array pattern" No "Array denotation not" pState)
		// otherwise // is_pattern && token <> SquareOpenToken
			= want_record_pattern token pState
	// otherwise // ~ is_pattern
	| token == CurlyCloseToken
		= (PE_ArrayDenot [], pState)		
		# (opt_type, pState) = try_type_specification token pState
		= case opt_type of
			Yes _
				-> want_record opt_type pState
			_
				# (succ, field, pState) = try_field_assignment token pState
				| succ
					# (token, pState) = nextToken FunctionContext pState
					| token == CommaToken
						# (token, pState) = nextToken FunctionContext pState
						  (fields, pState) = want_field_assignments cIsNotAPattern token pState
						-> (PE_Record PE_Empty No [ field : fields ], wantToken FunctionContext "record or array" CurlyCloseToken pState)
					| token == CurlyCloseToken
						-> (PE_Record PE_Empty No [ field ], pState)
						-> (PE_Record PE_Empty No [ field ], parseError "record or array" (Yes token) "}" pState)
				# (expr, pState) = wantRhsExpressionT token pState
				  (token, pState) = nextToken FunctionContext pState
				| token == AndToken
					# (token, pState) = nextToken FunctionContext pState
					-> want_record_or_array_update token expr pState
				| token == DoubleBackSlashToken
					-> wantArrayComprehension expr pState
				# (elems, pState) = want_array_elems token pState
				-> (PE_ArrayDenot [expr : elems], pState)
where
	want_array_elems CurlyCloseToken pState
		= ([], pState)
	want_array_elems CommaToken pState
		# (elem, pState) = wantExpression cIsNotAPattern pState
		  (token, pState) = nextToken FunctionContext pState
		  (elems, pState) = want_array_elems token pState
		= ([elem : elems], pState)
	want_array_elems token pState
		= ([], parseError "array elements" (Yes token) "<array denotation>" pState)
	
	want_record_pattern (IdentToken ident) pState
		| isUpperCaseName ident
			# pState = wantToken FunctionContext "record pattern" BarToken pState
			  (type_id, pState) = stringToIdent ident IC_Type pState
			  (token, pState) = nextToken FunctionContext pState
			  (fields, pState) = want_field_assignments cIsAPattern token pState
			= (PE_Record PE_Empty (Yes type_id) fields, wantToken FunctionContext "record pattern" CurlyCloseToken pState) 
	want_record_pattern token pState
		# (fields, pState) =  want_field_assignments cIsAPattern token pState
		= (PE_Record PE_Empty No fields, wantToken FunctionContext "record pattern" CurlyCloseToken pState) 

	try_type_specification (IdentToken ident) pState
		| isUpperCaseName ident || isFunnyIdName ident
			# (token, pState) = nextToken FunctionContext pState
			| token == BarToken
				# (type_id, pState) = stringToIdent ident IC_Type pState
				= (Yes type_id, pState)
				= (No, tokenBack pState)
			= (No, pState)
	try_type_specification _ pState
		= (No, pState)

	want_updates :: !(Optional Ident) Token ParseState -> ([NestedUpdate], ParseState)
	want_updates type token pState
		# (updates, pState)
			= parse_updates token pState
// RWS FIXME error message if updates == []
		= (updates, pState)
	where
		parse_updates :: Token ParseState -> ([NestedUpdate], ParseState)
		parse_updates token pState
				# (update, pState) = want_update token pState
				  (token, pState) = nextToken FunctionContext pState
				| token == CommaToken
					# (token, pState) = nextToken FunctionContext pState
					  (updates, pState) = parse_updates token pState 
					= ([update : updates], pState)
				// otherwise
					= ([update], tokenBack pState)

		want_update :: Token ParseState -> (NestedUpdate, ParseState)
		want_update token pState
			# (selectors, pState) = wantSelectors token pState
			  (token, pState) = nextToken FunctionContext pState
			| token == EqualToken
				# (expr, pState) = wantExpression cIsNotAPattern pState
				= ({nu_selectors = selectors, nu_update_expr = expr}, pState)
				= ({nu_selectors = selectors, nu_update_expr = PE_Empty}, parseError "field assignment" (Yes token) "=" pState)

	transform_record_or_array_update :: !(Optional Ident) ParsedExpr [NestedUpdate] !Int ParseState -> (ParsedExpr, ParseState)
	transform_record_or_array_update type expr updates level pState
		| is_record_update sortedUpdates
			=	transform_record_update type expr groupedUpdates level pState
		// otherwise
			=	transform_array_update expr updates level pState
		where
			sortedUpdates
				// sort updates by first field name, array updates last
				=	sortBy smaller_update updates
				where
					smaller_update :: NestedUpdate NestedUpdate -> Bool
					smaller_update a b
				 		=	smaller_selector (hd a.nu_selectors) (hd b.nu_selectors)
			 			where
							smaller_selector :: ParsedSelection ParsedSelection -> Bool
							smaller_selector (PS_Record ident1 _) (PS_Record ident2 _)
								=	ident1.id_name < ident2.id_name
							smaller_selector (PS_Record _ _) _
								=	True
							smaller_selector _ _
								=	False

			groupedUpdates
				// group nested updates by first field name
				=	groupBy equal_update sortedUpdates
				where
					equal_update :: NestedUpdate NestedUpdate -> Bool
					equal_update a b
						=	equal_selectors a.nu_selectors b.nu_selectors
			 			where
							equal_selectors :: [ParsedSelection] [ParsedSelection] -> Bool
							equal_selectors [PS_Record ident1 _ ,_ : _] [PS_Record ident2 _ ,_: _]
								=	ident1.id_name == ident2.id_name
							equal_selectors _ _
								=	False
		
			is_record_update [{nu_selectors=[select : _]} : _]
				=	is_record_select select
			is_record_update updates
				=	False

			is_record_select (PS_Record _ _)
				=	True
			is_record_select _
				=	False

			transform_record_update :: (Optional Ident) ParsedExpr ![[NestedUpdate]] !Int ParseState -> (ParsedExpr, ParseState)
			transform_record_update record_type expr groupedUpdates level pState
				=	(updateExpr, pState2)
				where
					/* final_record_type on a cycle */
					(assignments, (optionalIdent, final_record_type,pState2))
						= mapSt (transform_update level) groupedUpdates (No, record_type,pState)
					updateExpr
						= build_update final_record_type optionalIdent expr assignments
					// transform one group of nested updates with the same first field
					//  for example: f.g1 = e1, f.g2 = e2 -> f = {id.f & g1 = e1, g2 = e2},
					//  (id is ident to shared expression that's being updated)

					transform_update :: !Int [NestedUpdate] (Optional Ident,Optional Ident,ParseState) -> (FieldAssignment, !(!Optional Ident,!Optional Ident,ParseState))
					transform_update _ [{nu_selectors=[PS_Record fieldIdent field_record_type], nu_update_expr}] (shareIdent,record_type,pState)
						# (record_type,pState) = check_field_and_record_types field_record_type record_type pState;
						= ({bind_dst = fieldIdent, bind_src = nu_update_expr},(shareIdent,record_type,pState))
					transform_update level updates=:[{nu_selectors=[PS_Record fieldIdent field_record_type : _]} : _] (optionalIdent,record_type,pState)
						# (record_type,pState) = check_field_and_record_types field_record_type record_type pState;
						# (shareIdent, pState)
							=	make_ident optionalIdent level pState
						  select
						  	=	PE_Selection ParsedNormalSelector (PE_Ident shareIdent) [PS_Record fieldIdent final_record_type]
						  (update_expr, pState)
						  	=	transform_record_or_array_update No select (map sub_update updates) (level+1) pState
						=	({bind_dst = fieldIdent, bind_src = update_expr}, (Yes shareIdent,record_type,pState))
						where
							make_ident :: (Optional Ident) !Int ParseState -> (Ident, ParseState)
							make_ident (Yes ident) _ pState
								=	(ident, pState)
							make_ident No level pState
								=	internalIdent ("s" +++ toString level +++ ";") pState

							sub_update :: NestedUpdate -> NestedUpdate
							sub_update update=:{nu_selectors}
								=	{update & nu_selectors = tl nu_selectors}
					transform_update _ _ (_, record_type,pState)
						# pState
							=	parseError "record or array" No "field assignments mixed with array assignments not" pState
						=	({bind_dst = errorIdent, bind_src = PE_Empty}, (No,record_type,pState))

					build_update :: !(Optional Ident) !(Optional Ident) !ParsedExpr ![FieldAssignment] -> ParsedExpr
					build_update record_type No expr assignments
						=	PE_Record expr record_type assignments
					build_update record_type (Yes ident) expr assignments
						=	PE_Let False (LocalParsedDefs [buildNodeDef (PE_Ident ident) expr])
									(PE_Record (PE_Ident ident) record_type assignments)
					
					check_field_and_record_types :: (Optional Ident) (Optional Ident) ParseState -> (!Optional Ident,!ParseState);
					check_field_and_record_types No record_type pState
						= (record_type,pState);
					check_field_and_record_types field_record_type=:(Yes _) No pState
						= (field_record_type,pState);
					check_field_and_record_types (Yes field_record_type_name) record_type=:(Yes record_type_name) pState
						| field_record_type_name==record_type_name
							= (record_type,pState);
							# error_message = "record type in update: "+++field_record_type_name.id_name+++" where "+++record_type_name.id_name+++" was"
							= (record_type,parseError "record or array" No error_message pState);

			transform_array_update :: ParsedExpr [NestedUpdate] !Int ParseState -> (ParsedExpr, ParseState)
			transform_array_update expr updates level pState
				// transform {<e> & [i].<...> = e1, ... } to  {{<e> & [i1].<...> = e1} & ...}
				=	foldSt (transform_update level) updates (expr, pState)
				where
					transform_update :: !Int NestedUpdate (ParsedExpr, ParseState) -> (ParsedExpr, ParseState)
					transform_update level {nu_selectors, nu_update_expr} (expr1, pState)
						=	build_update expr1 (split_selectors nu_selectors) nu_update_expr level pState
						where
							// split selectors into final record selectors and initial selectors
							//  (resulting selectors are reversed)
							//		for example: [i1].[i2].f.[i3].g.h -> (h.g, [i3].f.[i2].[i1])
							split_selectors selectors
								=	span is_record_select (reverse selectors)

							build_update :: ParsedExpr ([ParsedSelection], [ParsedSelection]) ParsedExpr !Int ParseState -> (ParsedExpr, ParseState)
							build_update expr ([], initial_selectors) update_expr _ pState
								=	(PE_Update expr (reverse initial_selectors) update_expr, pState)
							// transform {<e> & <...>.[i].f.g. = e1} to
							//     let
							//		index_id = i
							//		(element_id, array_id) = <e>!<...>.[index_id]
							//	   in {array_id & [index_id] = {element_id & f.g = e1}}
							build_update expr (record_selectors, [PS_Array index : initial_selectors]) update_expr level pState
								# (index_id, pState)
									=	internalIdent ("i" +++ toString level +++ ";") pState
								# (element_id, pState)
									=	internalIdent ("e" +++ toString level +++ ";") pState
								# (array_id, pState)
									=	internalIdent ("a" +++ toString level +++ ";") pState
								  index_def
								  	=	buildNodeDef (PE_Ident index_id) index
								  select_def
								  	=	buildNodeDef
								  			(PE_Tuple [PE_Ident element_id, PE_Ident array_id])
								  			(PE_Selection (ParsedUniqueSelector True) expr (reverse [PS_Array (PE_Ident index_id) : initial_selectors]))
								  (updated_element, pState)
									= transform_record_update No
										(PE_Ident element_id)
										[[{nu_selectors=(reverse record_selectors), nu_update_expr=update_expr}]] (level+1) pState
								=	(PE_Let False
										(LocalParsedDefs [index_def, select_def])
										(PE_Update (PE_Ident array_id) (reverse [PS_Array (PE_Ident index_id) : initial_selectors]) updated_element), pState)

	want_field_assignments is_pattern token=:(IdentToken ident) pState
		| isLowerCaseName ident
			# (field, pState) = want_field_expression is_pattern ident pState
			  (token, pState) = nextToken FunctionContext pState
			| token == CommaToken
				# (token, pState) = nextToken FunctionContext pState
				  (fields, pState) = want_field_assignments is_pattern token pState 
				= ([ field : fields ], pState)
				= ([ field ], tokenBack pState)
	where
		want_field_expression is_pattern ident pState
			# (field_id, pState) = stringToIdent ident IC_Selector pState
			  (token, pState) = nextToken FunctionContext pState
			| token == EqualToken
				# (field_expr, pState) = wantExpression is_pattern pState
				= ({ bind_src = field_expr, bind_dst = field_id}, pState)
				= ({ bind_src = PE_Empty, bind_dst = field_id}, tokenBack pState)
	want_field_assignments is_pattern token pState
		= ([], parseError "record or array field assignments" (Yes token) "field name" pState)

	try_field_assignment (IdentToken ident) pState
		| isLowerCaseName ident
			# (token, pState) = nextToken FunctionContext pState
			| token == EqualToken
				# (field_expr, pState) = wantExpression cIsNotAPattern pState
				  (field_id, pState) = stringToIdent ident IC_Selector pState
				= (True, { bind_src = field_expr, bind_dst = field_id}, pState) 
				= (False, abort "no field", tokenBack pState)
			= (False, abort "no field", pState)
	try_field_assignment _ pState
		= (False, abort "no field", pState)
			
	want_record type pState
		# (token1, pState) = nextToken FunctionContext pState
  		  (token2, pState) = nextToken FunctionContext pState
		| isDefinesFieldToken token2
			# (fields, pState) = want_field_assignments cIsNotAPattern token1 (tokenBack pState)
			= (PE_Record PE_Empty type fields, wantToken FunctionContext "record" CurlyCloseToken pState)
			= want_record_update type token1 (tokenBack pState)
	where
		want_record_update :: !(Optional Ident) !Token !ParseState -> (!ParsedExpr, !ParseState)
		want_record_update type token pState
			# (expr,  pState)	= wantRhsExpressionT token pState
			  pState			= wantToken FunctionContext "record update" AndToken pState
			  (token, pState)	= nextToken FunctionContext pState
			= want_update type expr token pState

	want_update :: !(Optional Ident) !ParsedExpr !Token !ParseState -> (!ParsedExpr, !ParseState)
	want_update type expr token pState
		# (position, pState) = getPosition pState
		  (updates, pState)	= want_updates type token pState
		  (qualifiers, pState) = try_qualifiers pState
		  (updatable_expr, pState) = test_qualifiers expr (toLineAndColumn position) qualifiers pState
		  (updated_expr, pState) = transform_record_or_array_update type updatable_expr updates 0 pState
		= (add_qualifiers qualifiers expr updated_expr updatable_expr, wantToken FunctionContext "update" CurlyCloseToken pState)
		where
			try_qualifiers :: !ParseState -> (![Qualifier], !ParseState)
			try_qualifiers pState
				# (token, pState) = nextToken FunctionContext pState
				| token == DoubleBackSlashToken
					= wantQualifiers pState
					= ([], tokenBack pState)

			test_qualifiers :: !ParsedExpr !LineAndColumn [Qualifier] !ParseState -> (!ParsedExpr, !ParseState)
			test_qualifiers updateExpr _ [] pState
				=	(updateExpr, pState)
			test_qualifiers updateExpr {lc_line, lc_column} qualifiers pState
				# (ident, pState)
					=	stringToIdent ("a;" +++ toString lc_line +++ ";" +++ toString lc_column) IC_Expression pState
				=	(PE_Ident ident, pState)

			add_qualifiers :: ![Qualifier] !ParsedExpr !ParsedExpr !ParsedExpr -> ParsedExpr
			add_qualifiers [] _ update_expr _
				=	update_expr
			add_qualifiers qualifiers expr update_expr ident_expr
				=	PE_UpdateComprehension expr update_expr ident_expr qualifiers

	want_record_or_array_update token expr pState
		= want_update No expr token pState

	want_array_assignments is_pattern pState
		# (assign, pState) = want_array_assignment is_pattern pState
		  (token, pState) = nextToken FunctionContext pState
		| token == CommaToken
			# pState = wantToken FunctionContext "array assignments" SquareOpenToken pState
			  (assigns, pState) = want_array_assignments is_pattern pState 
			= ([ assign : assigns ], pState)
			= ([ assign ], tokenBack pState)
	where
		want_array_assignment is_pattern pState
			# (index_exprs, pState) = want_index_exprs pState
			  pState = wantToken FunctionContext "array assignment" EqualToken pState
			  (pattern_exp, pState) = wantExpression is_pattern pState
			= ({bind_dst = index_exprs, bind_src = pattern_exp}, pState)

		want_index_exprs pState
			# (index_expr,  pState) = wantExpression cIsNotAPattern pState
			  (token, pState) = nextToken GeneralContext pState
			| token==CommaToken
				# (index_exprs, pState) = want_index_exprs pState
				= ([index_expr:index_exprs], pState)
			| token==SquareCloseToken
				= ([index_expr], pState)
			= ([], parseError "" (Yes token) "] or ," pState)
/**
	End of definitions
**/

skipToEndOfDefinition :: !ParseState -> (!Token, !ParseState)
skipToEndOfDefinition pState
	# (token, pState)		= nextToken FunctionContext pState
	= case token of
		NewDefinitionToken	-> (token, pState)
		EndGroupToken		-> (token, pState)
		EndOfFileToken		-> (token, pState)
//		SemicolonToken		-> (token, pState) // might be useful in non layout mode.
		_					-> skipToEndOfDefinition pState -->> (token,"skipped")

wantEndCodeRhs :: !ParseState -> ParseState
wantEndCodeRhs pState
	# (ss_useLayout, pState) = accScanState UseLayout pState
	| ss_useLayout
		= wantEndOfDefinition "code rhs" pState
	# (token, pState) = nextToken FunctionContext pState
	| token == SemicolonToken
		= pState
		= tokenBack pState

wantEndOfDefinition :: String !ParseState -> ParseState
wantEndOfDefinition msg pState=:{ps_skipping}
	| ps_skipping
		#	(token, pState) = skipToEndOfDefinition {pState & ps_skipping = False}
		= want_end_of_definition token msg pState
	# (token, pState) = nextToken FunctionContext pState
	= want_end_of_definition token msg pState
where
	want_end_of_definition :: !Token String !ParseState -> ParseState
	want_end_of_definition token msg pState
		# (ss_useLayout, pState) = accScanState UseLayout pState
		| ss_useLayout
			= case token of
				NewDefinitionToken	->	pState 
				EndOfFileToken		->	tokenBack pState
				EndGroupToken 		->	tokenBack pState
				InToken		 		->	tokenBack pState
				WhereToken			->	tokenBack pState
				BarToken			->	tokenBack pState
				EqualToken			->	tokenBack pState
				ArrowToken			->	tokenBack pState
				SeqLetToken _		->	tokenBack pState
				SemicolonToken		#	(token, pState) = nextToken FunctionContext pState
									->	case token of
											NewDefinitionToken	->	pState
											_					->	tokenBack pState
				token				->	wantEndOfDefinition "" (parseError msg (Yes token) "end of definition" pState)
		// otherwise // ~ ss_useLayout
			= case token of
				CurlyCloseToken		->	tokenBack pState
				SemicolonToken		->	pState
	 			EndOfFileToken		->	tokenBack pState
				token				->	wantEndOfDefinition "" (parseError msg (Yes token) "end of definition" pState)

wantEndRootExpression :: !ParseState -> ParseState
wantEndRootExpression pState=:{ps_skipping}
	| ps_skipping
		=	wantEndOfDefinition "root expression" pState
		#	(token, pState)			= nextToken FunctionContext pState
			(ss_useLayout, pState)	= accScanState UseLayout pState
		| ss_useLayout
			= case token of
				NewDefinitionToken	->	pState
				EndOfFileToken		->	tokenBack pState
				EndGroupToken 		->	tokenBack pState
				EqualToken 			->	tokenBack pState
				ArrowToken 			->	tokenBack pState
				WhereToken			->	tokenBack pState
				WithToken			->	tokenBack pState
				BarToken			->	tokenBack pState
				InToken		 		->	tokenBack pState
				CloseToken	 		->	tokenBack pState
				SquareCloseToken	->	tokenBack pState
				CommaToken	 		->	tokenBack pState
				ColonToken	 		->	tokenBack pState
				(SeqLetToken _)		->	tokenBack pState
				SemicolonToken		#	(token, pState) = nextToken FunctionContext pState
									->	case token of
											NewDefinitionToken	->	pState
											_					->	tokenBack pState
				CurlyCloseToken		->	tokenBack pState 
				token				->	wantEndOfDefinition "root expression" (parseError "root expression" (Yes token) "end of root expression" pState)
		// otherwise // ~ ss_useLayout
			= case token of
				SemicolonToken		->	pState
				CurlyCloseToken		->	tokenBack pState
				EqualToken 			->	tokenBack pState
				ArrowToken 			->	tokenBack pState
				(SeqLetToken _)		->	tokenBack pState
				WhereToken			->	tokenBack pState
				WithToken			->	tokenBack pState
				BarToken			->	tokenBack pState
	 			EndOfFileToken		->	tokenBack pState
				token				->	wantEndOfDefinition "root expression" (parseError "root expression" (Yes token) "end of root expression" pState)

wantEndGroup :: String !ParseState -> ParseState
wantEndGroup msg pState
	# (token, pState) = nextToken FunctionContext pState
	| token == EndOfFileToken
		= tokenBack pState
	# (ss_useLayout, pState) = accScanState UseLayout pState
	| ss_useLayout
		= case token of
			EndGroupToken	->	pState
			InToken			->	tokenBack pState
			_				->	parseError msg (Yes token) "end of group with layout" pState
	// ~ ss_useLayout
	| token == CurlyCloseToken
		# (token, pState) = nextToken FunctionContext pState
		| token == SemicolonToken
			= pState
			= tokenBack pState
		= parseError msg (Yes token) "end of group without layout, }," pState

wantEndModule :: !ParseState -> ParseState
wantEndModule pState
	# (token, pState) = nextToken FunctionContext pState
	| token == EndOfFileToken
		= tokenBack pState
	# (ss_useLayout, pState) = accScanState UseLayout pState
	| ss_useLayout && token == EndGroupToken
		= pState
		= parseError "Definition" (Yes token) "Unexpected token in input: definition" pState

wantEndNestedGuard :: !Bool !Int !ParseState -> ParseState
wantEndNestedGuard defaultFound offside pState
	| ~ defaultFound
		= parseError "nested guards" No "sorry, but for the time being there is a default alternative for nested guards" pState
	# (token, pState)			= nextToken FunctionContext pState
	| token == EndOfFileToken
		= tokenBack pState
	# (ss_useLayout, pState)	= accScanState UseLayout pState
	| ss_useLayout
		# ({fp_col}, pState)	= getPosition pState
		|  fp_col < offside || (end_Nested_Guard token && fp_col == offside)
			= tokenBack pState
		// otherwise
			= parseError "nested guards" (Yes token) "=, ->, | or # at offside position, or end of function definition" pState
	// ~ ss_useLayout
	| token == SemicolonToken
		= pState
	| defaultFound
		= tokenBack pState
	// otherwise
		= parseError "nested guards" (Yes token) "End of nested guards, ;," pState
where
	end_Nested_Guard EqualToken			= True
	end_Nested_Guard BarToken			= True
	end_Nested_Guard ArrowToken			= True
	end_Nested_Guard (SeqLetToken _)	= True
	end_Nested_Guard _					= False

wantEndLocals :: !ParseState -> ParseState
wantEndLocals pState
	# (ss_useLayout, pState) = accScanState UseLayout pState
	  (token, pState) = nextToken FunctionContext pState
	| token == EndOfFileToken && ss_useLayout
		= tokenBack pState
	| ss_useLayout
		= case token of
			EndGroupToken	->	pState
			InToken			->	tokenBack pState	// For let expressions with cases
			_				->	parseError "local definitions" (Yes token) "end of locals with layout" pState
	// ~ ss_useLayout
	| token == CurlyCloseToken
		# (token, pState) = nextToken FunctionContext pState
		| token == SemicolonToken
			= pState
			= tokenBack pState
	// otherwise // token <> CurlyCloseToken
		= parseError "local definitions" (Yes token) "end of locals without layout, }," pState

wantEndCase :: !ParseState -> ParseState
wantEndCase pState
	# (ss_useLayout, pState) = accScanState UseLayout pState
	  (token, pState) = nextToken FunctionContext pState
	| token == EndOfFileToken
		= tokenBack pState
	| ss_useLayout
		= case token of
			EndGroupToken		->	pState
			CloseToken			->	tokenBack (appScanState dropOffsidePosition pState)
			SquareCloseToken	->	tokenBack (appScanState dropOffsidePosition pState)
			SemicolonToken		->	tokenBack (appScanState dropOffsidePosition pState)
			CommaToken			->	tokenBack (appScanState dropOffsidePosition pState)
			ColonToken			->	tokenBack (appScanState dropOffsidePosition pState)
			InToken				->	tokenBack (appScanState dropOffsidePosition pState)
			CurlyCloseToken		->	tokenBack (appScanState dropOffsidePosition pState) // PK
			_					->	parseError "case expression" (Yes token) "end of case with layout" pState
	// ~ ss_useLayout
	| token == CurlyCloseToken
		= pState
	// otherwise // token <> CurlyCloseToken
		= parseError "case expression" (Yes token) "end of group without layout, }," pState

wantBeginGroup :: String !ParseState -> ParseState
wantBeginGroup msg pState
	# (ss_useLayout, pState) = accScanState UseLayout pState
	| ss_useLayout
		= pState
	// otherwise // ~ ss_uselayout
		# (token, pState)	= nextToken FunctionContext pState
		= case token of
			CurlyOpenToken
				->	pState
			_	->	parseError msg (Yes token) "begin group without layout, {," pState

// AA..
wantKind :: !ParseState -> !(!TypeKind, !ParseState)
wantKind pState
	| SwitchGenerics False True 
		= (KindConst, parseErrorSimple "kind" "generics are not supported by this compiler" pState)
	| not pState.ps_support_generics
		= (KindConst, parseErrorSimple "kind" "to enable generics use -generics command line flag" pState)
	# (token, pState) = nextToken TypeContext pState
	# (kind, pState) = want_simple_kind token pState
	# (token, pState) = nextToken TypeContext pState
	= want_kind kind token pState
	where
		want_simple_kind AsteriskToken pState		= (KindConst, pState)
		want_simple_kind (IntToken str) pState
			# n = toInt str
			| n == 0	= (KindConst, pState)
			| n > 0 	= (KindArrow (repeatn n KindConst), pState)
			| otherwise = (KindConst, parseError "invalid kind" No "positive integer expected" pState)
		want_simple_kind OpenToken pState 			= wantKind pState
		want_simple_kind GenericOpenToken pState 	= wantKind pState
		want_simple_kind token pState 
			= (KindConst, parseError "invalid kind" (Yes token) "* or (" pState)

		want_kind kind ArrowToken pState
			# (rhs, pState) = wantKind pState
			= 	case rhs of
				(KindArrow ks) 	-> (KindArrow [kind : ks], pState)
				KindConst 		-> (KindArrow [kind], pState) 
				//_				-> (KindArrow [kind, rhs], pState)
		want_kind kind CloseToken pState 				= (kind, pState)
		want_kind kind GenericCloseToken pState 		= (kind, pState)
		want_kind kind token pState	
			= (kind, parseError "invalid kind" (Yes token) ")" pState)
// ..AA 

/*
	Functions on the parse pState
*/
/*
instance insertToken ParseState
where
	insertToken t c pState = appScanState (insertToken t c) pState

instance currentToken ParseState
where
	currentToken pState = accScanState currentToken pState
	
instance replaceToken ParseState
where
	replaceToken t pState = appScanState (replaceToken t) pState
*/
instance tokenBack ParseState
where
	tokenBack pState=:{ps_skipping}
		| ps_skipping
			= pState
			= appScanState tokenBack pState

instance nextToken ParseState
where
	nextToken :: !ScanContext !ParseState -> (!Token, !ParseState)
	nextToken scanContext pState
		| pState.ps_skipping // in error recovery from parse error
			= (ErrorToken "Skipping", pState)
			= accScanState (nextToken scanContext) pState

instance getPosition ParseState
where
	getPosition pState = accScanState getPosition pState

warnIfStrictAnnot NoAnnot pState = pState
warnIfStrictAnnot (StrictAnnotWithPosition position) pState = parseWarningWithPosition "" "! ignored" position pState

parseWarningWithPosition :: !{# Char} !{# Char} !FilePosition !ParseState -> ParseState
parseWarningWithPosition act msg position pState
	| pState.ps_skipping
		= pState
	| otherwise // not pState.ps_skipping
		# (filename,pState=:{ps_error={pea_file,pea_ok}})	= getFilename pState
		  pea_file 	= 	pea_file
		  				<<< "Parse warning ["
		  				<<< filename <<< ","
		  				<<< position
		  				<<< (if (size act > 0) ("," + act) "") <<< "]: "
		  				<<< msg
		  				<<< "\n"
		=	{ pState
			& ps_error		= { pea_file = pea_file, pea_ok = pea_ok }
			}

parseWarning :: !{# Char} !{# Char} !ParseState -> ParseState
parseWarning act msg pState
	| pState.ps_skipping
		= pState
	| otherwise // not pState.ps_skipping
		# (pos,pState) 	= getPosition pState
		  (filename,pState=:{ps_error={pea_file,pea_ok}})	= getFilename pState
		  pea_file 	= 	pea_file
		  				<<< "Parse warning ["
		  				<<< filename <<< ","
		  				<<< pos 
		  				<<< (if (size act > 0) ("," + act) "") <<< "]: "
		  				<<< msg
		  				<<< "\n"
		=	{ pState
			& ps_error		= { pea_file = pea_file, pea_ok = pea_ok }
			}

parseError :: !{# Char} !(Optional Token) !{# Char} !ParseState -> ParseState
parseError act opt_token msg pState
	| pState.ps_skipping
		= pState
	| otherwise // not pState.ps_skipping
		# (pos,pState) 	= getPosition pState
		  (filename,pState=:{ps_error={pea_file}})	= getFilename pState
		  pea_file 	= 	pea_file
		  				<<< "Parse error ["
		  				<<< filename <<< ","
		  				<<< pos 
		  				<<< (if (size act > 0) ("," + act) "") <<< "]: "
		  				<<< msg
		  pea_file	= case opt_token of
		  				Yes token	-> pea_file <<< " expected instead of " <<< token <<< "\n"
		  				No			-> pea_file <<< " expected\n"
		  pState 	=	{ pState
						& ps_skipping	= True
						, ps_error		= { pea_file = pea_file, pea_ok = False }
						}
		= case opt_token of
			Yes _	-> tokenBack pState
			No		-> pState

parseErrorSimple :: !{# Char} !{# Char} !ParseState -> ParseState
parseErrorSimple act msg pState
	| pState.ps_skipping
		= pState
	| otherwise // not pState.ps_skipping
		# (pos,pState) 	= getPosition pState
		  (filename,pState=:{ps_error={pea_file}})	= getFilename pState
		  pea_file 	= 	pea_file
		  				<<< "Parse error ["
		  				<<< filename <<< ","
		  				<<< pos 
		  				<<< (if (size act > 0) ("," + act) "") <<< "]: "
		  				<<< msg
		  				<<< '\n'
		  pState 	=	{ pState
						& ps_skipping	= True
						, ps_error		= { pea_file = pea_file, pea_ok = False }
						}
		= pState

getFileAndLineNr :: !ParseState -> (!String, !Int, !ParseState)
getFileAndLineNr pState =: {ps_scanState}
	# (filename,scanState)	= getFilename ps_scanState
	  ({fp_line},scanState)	= getPosition scanState
	= (filename, fp_line, {pState & ps_scanState = scanState} )

/*
	Simple parse functions
*/

wantToken :: !ScanContext !{#Char} !Token !ParseState ->  ParseState
wantToken scanContext act dem_token pState
	# (token, pState) = nextToken scanContext pState
	| dem_token == token
		= pState
		= parseError act (Yes token) (toString dem_token) pState

instance want Priority
where
	want pState
		# (token, pState) = nextToken FunctionContext pState
		= case token of
			PriorityToken prio
				-> (prio, pState)
			_
				-> (NoPrio, parseError "Priority" (Yes token) "with" pState)

instance want {# Char}
where
	want pState
		# (token, pState) = nextToken GeneralContext pState
		= case token of
			IdentToken name -> (name, pState)
			_				-> ("", parseError "String" (Yes token) "identifier" pState)

wantModuleName :: !*ParseState -> (!{# Char}, !*ParseState)
wantModuleName pState
	# (token, pState) = nextToken GeneralContext pState
	= case token of
		IdentToken name -> (name, pState)
		UnderscoreIdentToken name -> (name, pState)
		_				-> ("", parseError "String" (Yes token) "module name" pState)

tryTypeVar :: !ParseState -> (!Bool, TypeVar, !ParseState)
tryTypeVar pState
	# (token, pState) = nextToken TypeContext pState
	= tryTypeVarT token pState

tryTypeVarT :: !Token !ParseState -> (!Bool, TypeVar, !ParseState)
tryTypeVarT (IdentToken name) pState
	| isLowerCaseName name
		# (id, pState) = stringToIdent name IC_Type pState
		= (True, MakeTypeVar id, pState)
		= (False, abort "no UC ident", tokenBack pState)
tryTypeVarT token pState
		= (False, abort "no type variable", tokenBack pState)

wantUpperCaseName :: !String !ParseState -> (!String, !ParseState)
wantUpperCaseName string pState
	# (token, pState) = nextToken GeneralContext pState
	= case token of
		IdentToken name 
			| isUpperCaseName name
				-> (name, pState)
		_	-> ("dummy uppercase name", parseError string (Yes token) "upper case ident" pState)
/*
wantNonUpperCaseName :: !String !ParseState -> (!String, !ParseState)
wantNonUpperCaseName string pState
	# (token, pState) = nextToken GeneralContext pState
	= case token of
		IdentToken name 
			| ~ (isUpperCaseName name)
				-> (name, pState)
		_	-> ("dummy non uppercase name", parseError string (Yes token) "non upper case ident" pState)
*/
wantLowerCaseName :: !String !ParseState -> (!String, !ParseState)
wantLowerCaseName string pState
	# (token, pState) = nextToken GeneralContext pState
	= case token of
		IdentToken name 
			| isLowerCaseName name
				-> (name, pState)
		_
			-> ("dummy lowercase name", parseError string (Yes token) "lower case ident" pState)

wantConstructorName :: !String !ParseState -> (!String, !ParseState)
wantConstructorName string pState
	# (token, pState) = nextToken GeneralContext pState
	= case token of
		IdentToken name 
			| isUpperCaseName name || isFunnyIdName name
				-> (name, pState)
		_
			-> ("", parseError string (Yes token) "upper case ident" pState)

isDefinesFieldToken :: ! Token -> Bool
isDefinesFieldToken EqualToken    = True
isDefinesFieldToken CurlyCloseToken = True
isDefinesFieldToken CommaToken      = True
isDefinesFieldToken token           = False

  //---------------//
 //--- Tracing ---//
//---------------//

(-->>) val _ :== val
//(-->>) val message :== val ---> ("Parser",message)
