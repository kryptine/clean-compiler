implementation module explicitimports

import StdEnv

import syntax, typesupport, parse, checksupport, utilities, checktypes, transform, predef, RWSDebug


temporary_import_solution_XXX yes no :== yes
// to switch between importing modes.
// iff this is yes, then explicit imports happen in the old Clean 1.3 fashion.
// This feature will be removed, when all programs are ported to Clean 2.0. The last Constructors of AtomType
// and StructureType should then be removed also
do_temporary_import_solution_XXX :== temporary_import_solution_XXX True False

::	ExplicitImports	:==	(![AtomicImport], ![StructureImport])
::	AtomicImport	:==	(!Ident, !AtomType)
::	StructureImport	:==	(!Ident, !StructureInfo, !StructureType, !OptimizeInfo)

::	AtomType		=	AT_Function | AT_Class | AT_Instance | AT_RecordType | AT_AlgType | AT_Type
						| AT_stomme_funktion_die_alle_symbolen_kann_importeren_omdat_niemand_zin_heft_oude_pragrammen_naar_de_nieuwe_syntax_te_vertalen Bool // XXX
::	StructureInfo	= SI_DotDot
					// The .. notation was used for the structure
					// (currently nothing is known about the elements)
					| SI_Elements ![Ident] !Bool
					// list of elements, that were not imported yet.
					// Bool: the elements were listed explicitly in the structure
::	StructureType	= ST_AlgType | ST_RecordType | ST_Class
					| ST_stomm_stomm_stomm String
::	IdentWithKind	:==	(!Ident, !STE_Kind)
::	IdentWithCKind	:==	(!Ident, !ConsequenceKind)

::	OptimizeInfo	:==	(Optional !Index)

::	ConsequenceKind	= CK_Function !(Global Index)
					| CK_DynamicPatternType ExprInfoPtr
					| CK_Macro
					| CK_Constructor
					| CK_Selector !(Global DefinedSymbol)
					| CK_Type
					| CK_Class

::	FunctionConsequence	:==	Optional !(!Int, !Optional ![IdentWithCKind])
	// Int i: The consequences of this function/macro have already been considered for all dcl modules with indices <= i

check_completeness_of_all_dcl_modules	:: !*{#DclModule} !*{#FunDef} !*ExpressionHeap !*CheckState
									-> (!Int, !(!*{!FunctionConsequence}, !*{#DclModule}, !*{#FunDef}, !*ExpressionHeap, !*CheckState))
check_completeness_of_all_dcl_modules modules icl_functions expr_heap cs
	#	(nr_modules, modules)	= usize modules
		(nr_functions, icl_functions)	= usize icl_functions
		f_consequences	= f_consequences nr_functions
		result
			= iFoldSt check_completeness_of_dcl_module 0 (nr_modules) (f_consequences, modules, icl_functions, expr_heap, cs)
	= (nr_modules, result)
  where
	f_consequences :: !Int -> *{!FunctionConsequence}
	f_consequences i = createArray i No

check_completeness_of_dcl_module mod_index (f_consequences, modules, icl_functions, expr_heap, cs=:{cs_predef_symbols})
	#	pre_mod = cs_predef_symbols.[PD_PredefinedModule]
	|	pre_mod.pds_def == mod_index
		= (f_consequences, modules, icl_functions, expr_heap, cs)	// predefined module should not be checked for completeness of explicit imports
	#	(modul=:{ dcl_name, dcl_declared=dcl_declared=:{dcls_import,dcls_local, dcls_explicit}}, modules)
			= modules![mod_index]
		cs	= addDeclaredSymbolsToSymbolTable cIsADclModule mod_index dcls_local dcls_import cs
		(f_consequences, modules, icl_functions, expr_heap, cs)
			= check_completeness_of_module mod_index dcls_explicit (dcl_name.id_name+++".dcl") (f_consequences, modules, icl_functions, expr_heap, cs)
		(_, cs_symbol_table) = retrieveAndRemoveImportsFromSymbolTable [(mod_index, dcl_declared)] [] cs.cs_symbol_table
		cs	= { cs & cs_symbol_table=cs_symbol_table }
	= (f_consequences, modules, icl_functions, expr_heap, cs)

possibly_filter_decls :: .[ImportDeclaration] u:[w:(.Index,y:Declarations)] (.FileName,.LineNr) *{#.DclModule} *CheckState -> (v:[x:(Index,z:Declarations)],.{#DclModule},.CheckState), [y <= z, w <= x, u <= v];
possibly_filter_decls [] decls_of_imported_module	_ modules cs // implicit import can't go wrong
	= (decls_of_imported_module, modules, cs)
possibly_filter_decls listed_symbols decls_of_imported_module (file_name, line_nr) modules cs
	// explicit import
	#!	ident_pos	=	{	ip_ident= { id_name="", id_info=nilPtr }
						,	ip_line	= line_nr
						,	ip_file	= file_name
						}
		cs	= { cs & cs_error	= pushErrorAdmin ident_pos cs.cs_error }
		(result, modules, cs)	= filter_explicitly_imported_decl listed_symbols decls_of_imported_module [] line_nr modules cs
		cs	= { cs & cs_error	= popErrorAdmin cs.cs_error }
	= (result, modules, cs)

filter_explicitly_imported_decl _ [] akku _ modules cs
	= (akku, modules, cs)
filter_explicitly_imported_decl import_symbols [(index,{dcls_import,dcls_local,dcls_explicit}):new_decls] akku
								line_nr modules cs
	#	undefined = -1
		atoms = flatten (map toAtom import_symbols)
		structures = flatten (map toStructure import_symbols)
		(checked_atoms, cs)	= checkAtoms atoms cs
		unimported = (checked_atoms, structures)
		((dcls_import,unimported), modules, cs)	
			= filter_decl dcls_import unimported undefined modules cs
		((dcls_local,unimported), modules, cs)	
			= filter_decl dcls_local unimported index modules cs
		cs_error = foldSt checkAtomError (fst unimported) cs.cs_error
		cs_error = foldSt checkStructureError (snd unimported) cs_error
		cs	= { cs & cs_error=cs_error }
	|	(isEmpty dcls_import && isEmpty dcls_local && isEmpty dcls_explicit)
		= filter_explicitly_imported_decl import_symbols new_decls akku line_nr modules cs
	#	local_imports	= [ { declaration & dcl_kind = STE_Imported declaration.dcl_kind index }
							 \\ declaration <- dcls_local]
		new_dcls_explicit	= [ (dcls, line_nr) \\ dcls<-dcls_import++local_imports ]
		newAkku	= [(index, { dcls_import=dcls_import, dcls_local=dcls_local , dcls_explicit=new_dcls_explicit}) : akku]
	= filter_explicitly_imported_decl import_symbols new_decls newAkku line_nr modules cs
  where
	toAtom (ID_Function {ii_ident})				
		= [(ii_ident, temporary_import_solution_XXX 
							(AT_stomme_funktion_die_alle_symbolen_kann_importeren_omdat_niemand_zin_heft_oude_pragrammen_naar_de_nieuwe_syntax_te_vertalen False)
							AT_Function)]
	toAtom (ID_Class {ii_ident} _)
		= [(ii_ident, AT_Class)]
	toAtom (ID_Type {ii_ident} (Yes _))
		= [(ii_ident, AT_AlgType)]
	toAtom (ID_Type {ii_ident} No)
		= [(ii_ident, AT_Type)]
	toAtom (ID_Record {ii_ident} yesOrNo)
		= [(ii_ident, AT_RecordType)]
	toAtom (ID_Instance _ ident _)
		= [(ident, AT_Instance)]
	toAtom _
		= []

	atomTypeString	AT_Function		= "function"
	atomTypeString	AT_Class		= "class"
	atomTypeString	AT_Instance		= "instance"
	atomTypeString	_				= "type"

	toStructure (ID_Class {ii_ident} yesOrNo)
		= to_structure ii_ident yesOrNo ST_Class
	toStructure (ID_Type {ii_ident} yesOrNo)
		= to_structure ii_ident yesOrNo ST_AlgType
	toStructure (ID_Record {ii_ident} yesOrNo)
		= to_structure ii_ident yesOrNo ST_RecordType
// MW added
	toStructure (ID_Function {ii_ident})
		| do_temporary_import_solution_XXX
			= [(ii_ident, SI_DotDot, ST_stomm_stomm_stomm ii_ident.id_name, No)]
// ..MW
	toStructure _
		= []
		
	to_structure _ No _
		= []
	to_structure ident (Yes []) structureType
		= [(ident, SI_DotDot, structureType, No)]
	to_structure ident (Yes elements) structureType
		# element_idents	= removeDup [ ii_ident \\ {ii_ident}<-elements]
		= [(ident, (SI_Elements element_idents True),structureType, No)]

	checkAtoms l cs
		#	groups	= grouped l
			wrong	= filter isErrornous groups
			unique	= map hd groups
		| isEmpty wrong
			= (unique, cs)
		= (unique, foldSt error wrong cs)
	  where
		isErrornous l=:[(_,AT_Type),_:_]		= True
		isErrornous l=:[(_,AT_AlgType),_:_]		= True
		isErrornous l=:[(_,AT_RecordType),_:_]	= True
		isErrornous _							= False
		
		error [(ident, atomType):_] cs
			= { cs & cs_error = checkError ("type "+++ident.id_name) "imported more than once in one from statement"
										cs.cs_error }

	checkAtomError (id, AT_Instance) cs_error
		= checkError ("specified instance of class "+++id.id_name) "not exported by the specified module" cs_error
	checkAtomError (id, AT_stomme_funktion_die_alle_symbolen_kann_importeren_omdat_niemand_zin_heft_oude_pragrammen_naar_de_nieuwe_syntax_te_vertalen was_imported_at_least_once) cs_error
		| do_temporary_import_solution_XXX
			= case was_imported_at_least_once of
				True -> cs_error
				_    -> checkError id ("not exported by the specified module") cs_error
	checkAtomError (id, atomType) cs_error
		= checkError id ("not exported as a "+++atomTypeString atomType+++" by the specified module") cs_error

// MW remove this later..
	checkStructureError (_,_, ST_stomm_stomm_stomm _, _) cs_error
		| do_temporary_import_solution_XXX
			= cs_error
		// further with next alternative
// ..MW
	checkStructureError (struct_id, (SI_Elements wrong_elements _), st, _) cs_error
		= foldSt err wrong_elements cs_error
	  where
		err element_id cs_error
			#	(element_type, structure_type)	= case st of
													ST_AlgType		->	("constructor",	"algebraic type")
													ST_RecordType	->	("field",		"record type")
													ST_Class		->	("member",		"class")
			= checkError element_id (	"not a "+++element_type+++" of "+++structure_type
									 +++" "+++struct_id.id_name) cs_error
	checkStructureError _ cs_error
		= cs_error
	
	// collect groups, e.g. grouped [3,5,1,3,1] = [[1,1],[3,3],[5]]
	grouped []
		= []
	grouped l
		#	sorted	= qsort l
		= grouped_ [hd sorted] (tl sorted) []
	  where
		grouped_ group [] akku
			= [group:akku]
		grouped_ group=:[x:_] [h:t] akku
			|	x==h	= grouped_ [h:group] t akku
						= grouped_ [h] t [group:akku]
	
	qsort []	= []
	qsort [h:t] = qsort left++[h: qsort right]
	  where
		left	= [x \\ x<-t | greater x h]
		right	= [x \\ x<-t | not (greater x h) || x==h]
		greater ({id_name=id_name_l}, atomType_l) ({id_name=id_name_r}, atomType_r)
			|	id_name_l >id_name_r 	= True
			|	id_name_l==id_name_r 	= toInt atomType_l > toInt atomType_r
										= False

instance == AtomType
  where
	(==) l r = toInt l==toInt r
	
instance toInt AtomType
  where
	toInt AT_Function	= 0
	toInt AT_Class		= 1
	toInt AT_Instance	= 2
	toInt AT_RecordType	= 3
	toInt AT_AlgType	= 3
	toInt AT_Type		= 3	// AT_RecordType, AT_AlgType & AT_Type are in one class !!!
	toInt (AT_stomme_funktion_die_alle_symbolen_kann_importeren_omdat_niemand_zin_heft_oude_pragrammen_naar_de_nieuwe_syntax_te_vertalen _)
						= 0

instance == ConsequenceKind
  where
	(==) CK_Type		c = case c of	CK_Type	-> True
										_		-> False
	(==) CK_Constructor	c = case c of	CK_Constructor	-> True
										_		-> False
	(==) (CK_Selector globDefinedSymb1)
						c = case c of	CK_Selector globDefinedSymb2 -> globDefinedSymb1==globDefinedSymb2
										_		-> False
	(==) CK_Class		c = case c of	CK_Class-> True
										_		-> False
	(==) (CK_Function globIndex1)
						c = case c of	(CK_Function	globIndex2) -> globIndex1==globIndex2
										_		-> False
	(==) CK_Macro		c = case c of	CK_Macro-> True
										_		-> False

NoPosition :== -1

filter_decl [] unimported _ modules cs
	= (([], unimported), modules, cs)
filter_decl [decl:decls] unimported index modules cs
	# ((appears,unimported), modules, cs) = decl_appears decl unimported index modules cs
	  (r=:((recurs, unimported), modules, cs)) = filter_decl decls unimported index modules cs
	| appears
		= (([decl:recurs],unimported), modules, cs)
	= r
	
decl_appears :: !Declaration !ExplicitImports !Index !*{#DclModule} !*CheckState
			 -> (!(!Bool, !ExplicitImports), !*{#DclModule}, !*CheckState)
decl_appears dec=:{dcl_kind=STE_Imported ste_Kind def_index} unimported _ modules cs
	= decl_appears {dec & dcl_kind=ste_Kind} unimported def_index modules cs
/* MW2 was:
decl_appears {dcl_ident,dcl_kind=STE_Constructor,dcl_index} unimported index modules cs
	= elementAppears ST_AlgType dcl_ident dcl_index unimported index modules cs
*/
decl_appears {dcl_ident,dcl_kind=STE_Constructor,dcl_index} unimported index modules cs
	# (result=:((appears, unimported), modules, cs))
		 = elementAppears ST_AlgType dcl_ident dcl_index unimported index modules cs
	| appears || not do_temporary_import_solution_XXX
		= result
	= atomAppears dcl_ident dcl_index unimported index modules cs
/* MW2 was
decl_appears { dcl_ident,dcl_kind=(STE_Field _),dcl_index} unimported index modules cs 
	= elementAppears ST_RecordType dcl_ident dcl_index unimported index modules cs
*/
decl_appears { dcl_ident,dcl_kind=(STE_Field _),dcl_index} unimported index modules cs 
	# (result=:((appears, unimported), modules, cs))
		= elementAppears ST_RecordType dcl_ident dcl_index unimported index modules cs
	| appears || not do_temporary_import_solution_XXX
		= result
	= atomAppears dcl_ident dcl_index unimported index modules cs
/* MW2 was
decl_appears { dcl_ident,dcl_kind=STE_Member,dcl_index} unimported index modules cs 
	= elementAppears ST_Class dcl_ident dcl_index unimported index modules cs
*/
decl_appears { dcl_ident,dcl_kind=STE_Member,dcl_index} unimported index modules cs 
	# (result=:((appears, unimported), modules, cs))
		= elementAppears ST_Class dcl_ident dcl_index unimported index modules cs
	| appears || not do_temporary_import_solution_XXX
		= result
	= atomAppears dcl_ident dcl_index unimported index modules cs
decl_appears {dcl_ident, dcl_kind, dcl_index} unimported index modules cs 
	| isAtom dcl_kind
		=  atomAppears dcl_ident dcl_index unimported index modules cs
  where
	isAtom STE_DclFunction			= True
	isAtom (STE_FunctionOrMacro	_)	= True
	isAtom STE_Class				= True
	isAtom STE_Type					= True
	isAtom STE_Instance				= True


elementAppears imported_st dcl_ident dcl_index (atomicImports, structureImports) index modules cs
	#	((result, structureImports), modules, cs)
			=  element_appears imported_st dcl_ident dcl_index structureImports structureImports 0 index modules cs
	= ((result, (atomicImports, structureImports)), modules, cs)

atomAppears dcl_ident dcl_index (atomicImports, structureImports) index modules cs
	#	((result, atomicImports), modules, cs)
			= atom_appears dcl_ident dcl_index atomicImports atomicImports 0 index modules cs
	= ((result, (atomicImports, structureImports)), modules, cs)


atom_appears _ _ [] atomic_imports _ _ modules cs
  	= ((False, atomic_imports), modules, cs)
atom_appears ident dcl_index [h=:(import_ident, atomType):t] atomic_imports unimp_index index modules cs
// MW2..
	|		do_temporary_import_solution_XXX
		&&	ident.id_name==import_ident.id_name 
		&&	atomType==(AT_stomme_funktion_die_alle_symbolen_kann_importeren_omdat_niemand_zin_heft_oude_pragrammen_naar_de_nieuwe_syntax_te_vertalen True) // True or False doesn't matter in this line
		#	new_h = (import_ident, AT_stomme_funktion_die_alle_symbolen_kann_importeren_omdat_niemand_zin_heft_oude_pragrammen_naar_de_nieuwe_syntax_te_vertalen True)
		=  ((True, [new_h: removeAt unimp_index atomic_imports]), modules, cs)
// ..MW2
	|	ident==import_ident
		# (modules, cs) = checkRecordError atomType import_ident dcl_index index modules cs
		= ((True, removeAt unimp_index atomic_imports), modules, cs)
	// goes further with next alternative
  where
	checkRecordError atomType import_ident dcl_index index modules cs
		#	(td_rhs, modules, cs) = lookup_type dcl_index index modules cs
			cs_error	= cs.cs_error
			cs_error	= case atomType of
							AT_RecordType
								-> case td_rhs of
									RecordType _	-> cs_error
									_				-> checkError import_ident "imported as a record type" cs_error
							AT_AlgType
								-> case td_rhs of
									AlgType _		-> cs_error
									_				-> checkError import_ident "imported as an algebraic type" cs_error
							_	-> cs_error
		= (modules, { cs & cs_error=cs_error })
atom_appears ident dcl_index [h:t] atomic_imports unimp_index index modules cs
	= atom_appears ident dcl_index t atomic_imports (inc unimp_index) index modules cs

instance == StructureType
  where
	(==) ST_AlgType		ST_AlgType		= True
	(==) ST_RecordType	ST_RecordType	= True
	(==) ST_Class		ST_Class		= True
	(==) _ _							= False

element_appears _ _ _ [] atomic_imports _ _ modules cs
	= ((False, atomic_imports), modules, cs)
// MW2 remove this later ..
element_appears imported_st element_ident dcl_index
				[h=:(_, SI_DotDot, ST_stomm_stomm_stomm type_name_string, optInfo):t] atomic_imports unimp_index
				index modules cs
	| do_temporary_import_solution_XXX
		#	(appears, modules, cs)
			= element_appears_in_stomm_struct imported_st element_ident dcl_index index type_name_string modules cs
		| appears
			= ((appears, atomic_imports), modules, cs)
		= element_appears imported_st element_ident dcl_index t atomic_imports (inc unimp_index) index modules cs
	// otherwise go further with next alternative
// ..MW2
element_appears imported_st element_ident dcl_index
				[h=:(_, _, st, _):t] atomic_imports unimp_index
				index modules cs
	|	imported_st<>st
		= element_appears imported_st element_ident dcl_index t atomic_imports (inc unimp_index) index modules cs
	// goes further with next alternative
element_appears imported_st element_ident dcl_index
				[h=:(_, _, _, (Yes notDefinedHere)):t] atomic_imports unimp_index
				index modules cs
	|	notDefinedHere==dcl_index 
		= element_appears imported_st element_ident dcl_index t atomic_imports (inc unimp_index) index modules cs
	// goes further with next alternative
element_appears	imported_st element_ident dcl_index
				[h=:(struct_id, (SI_Elements elements explicit), st, optInfo):t] atomic_imports unimp_index
				index modules cs
	| not (isMember element_ident elements)
		= element_appears imported_st element_ident dcl_index t atomic_imports (inc unimp_index) index modules cs
	#	(l,r)	= span ((<>) element_ident) elements
		oneLess	= l++(tl r)
		newStructure = (struct_id, (SI_Elements oneLess explicit), st, optInfo)
		atomic_imports_1 = removeAt unimp_index atomic_imports
	|	not explicit
		= ((True, [newStructure: atomic_imports_1]), modules, cs)
	// the found element was explicitly specified by the programmer: check it
	#	(appears, _, _, modules, cs)
			= element_appears_in_struct imported_st element_ident dcl_index struct_id index modules cs
	|	appears
		= ((True, [newStructure: atomic_imports_1]), modules, cs)
	#	message	= "does not belong to specified "+++(case st of
														ST_Class	-> "class."
														_			-> "type.")
		cs	= { cs & cs_error= checkError element_ident message  cs.cs_error}
	= ((False, atomic_imports_1), modules, cs)
element_appears imported_st element_ident dcl_index
				[h=:(struct_id, SI_DotDot, st, optInfo):t] atomic_imports unimp_index
				index modules cs
	| (case st of
			ST_stomm_stomm_stomm _
				-> True
			_ 	-> False) && (False->>"element_appears weird case")
		= undef
	#	(appears, defined, opt_element_idents, modules, cs)
			= element_appears_in_struct imported_st element_ident dcl_index struct_id index modules cs
	|	not appears
		#	structureInfo	= case opt_element_idents of
								No					-> SI_DotDot
								Yes element_idents	-> (SI_Elements element_idents False)
			newStructure	= (struct_id, structureInfo, st, (if defined No (Yes dcl_index)))
			new_atomic_imports = [newStructure : removeAt unimp_index atomic_imports]
		= element_appears imported_st element_ident dcl_index t new_atomic_imports (inc unimp_index) index modules cs
	#	(Yes element_idents)	= opt_element_idents
		oneLess	= filter ((<>) element_ident) element_idents
		newStructure = (struct_id, (SI_Elements oneLess False), st, No)
		new_atomic_imports = [newStructure : removeAt unimp_index atomic_imports]
	= ((True,new_atomic_imports), modules, cs)
element_appears imported_st element_ident dcl_index [h:t] atomic_imports unimp_index index modules cs
	= element_appears imported_st element_ident dcl_index t atomic_imports (inc unimp_index) index modules cs

lookup_type dcl_index index modules cs
	#	(dcl_module=:{dcl_name=dcl_name=:{id_info}}, modules) = modules ! [index]
		(module_entry, cs_symbol_table) = readPtr id_info cs.cs_symbol_table
		cs	= { cs & cs_symbol_table=cs_symbol_table }
	= continuation module_entry.ste_kind dcl_module modules cs
  where
	continuation (STE_OpenModule _ modul) _ modules cs
		#	allTypes	= modul.mod_defs.def_types
		= ((allTypes !! dcl_index).td_rhs, modules, cs)
	continuation STE_ClosedModule dcl_module modules cs
		#	com_type_def	= dcl_module.dcl_common.com_type_defs.[dcl_index]
		= (com_type_def.td_rhs, modules, cs)

// MW remove this later CCC
element_appears_in_stomm_struct imported_st element_ident dcl_index index type_name_string modules cs
	| not do_temporary_import_solution_XXX
		= abort "element_appears_in_stomm_struct will be never called, when the above guard holds. This statement is only to remind people to remove this function."
	#	(dcl_module=:{dcl_name=dcl_name=:{id_info}}, modules)		= modules ! [index]
		(module_entry, cs_symbol_table)				= readPtr id_info cs.cs_symbol_table
	#!	cs	= { cs & cs_symbol_table=cs_symbol_table }
	= continuation imported_st module_entry.ste_kind dcl_module modules cs
  where
	continuation ST_RecordType (STE_OpenModule _ modul) _ modules cs
		//	lookup the constructors/fields for the algebraic type/record
		#	allTypes	= modul.mod_defs.def_types
			search		= dropWhile (\{td_name} -> td_name.id_name<>type_name_string) allTypes
		|	isEmpty search
			= (False, modules, cs)
		#	{td_rhs}	= hd search
		|	not (isRecordType td_rhs)
			= (False, modules, cs)
		#	element_idents	= getElements td_rhs
		= (isMember element_ident element_idents, modules, cs)
	continuation ST_RecordType STE_ClosedModule dcl_module modules cs
		// lookup the type of the constructor and compare
		#	type_index		= dcl_module.dcl_common.com_selector_defs.[dcl_index].sd_type_index
			com_type_def	= dcl_module.dcl_common.com_type_defs.[type_index]
			appears	= com_type_def.td_name.id_name==type_name_string
		= (appears, modules, cs)
	continuation ST_Class (STE_OpenModule _ modul) _ modules cs
		//	lookup the members for the class
		#	allClasses	= modul.mod_defs.def_classes
			search		= dropWhile (\{class_name} -> class_name.id_name<>type_name_string) allClasses
		|	isEmpty search
			= (False, modules, cs)
		#	{class_members}	= hd search
			element_idents	= [ ds_ident \\ {ds_ident} <-:class_members ]
		= (isMember element_ident element_idents, modules, cs)
	continuation ST_Class STE_ClosedModule dcl_module modules cs
		// lookup the class and compare
		#	com_member_def	= dcl_module.dcl_common.com_member_defs.[dcl_index]
			{glob_object}	= com_member_def.me_class
			com_class_def	= dcl_module.dcl_common.com_class_defs.[glob_object]
			appears	= com_class_def.class_name.id_name==type_name_string
		= (appears, modules, cs)
	continuation _ _ _ modules cs
		= (False, modules, cs)
	getElements (RecordType {rt_fields})
		= [ fs_name \\ {fs_name}<-:rt_fields ]
	getElements _
		= []
	isRecordType (RecordType _)	= True
	isRecordType _				= False
// ..MW

/*	1st result: whether the element appears in the structure
	2nd result: whether the structure is defined at all in the module
	3rd result: Yes: a list of all idents of the elements of the structure
the first bool implies the second
*/
element_appears_in_struct imported_st element_ident dcl_index struct_ident index modules cs
	#	(dcl_module=:{dcl_name=dcl_name=:{id_info}}, modules)		= modules ! [index]
		(module_entry, cs_symbol_table)				= readPtr id_info cs.cs_symbol_table
		cs	= { cs & cs_symbol_table=cs_symbol_table }
	= continuation imported_st module_entry.ste_kind dcl_module modules cs
  where
	continuation ST_Class (STE_OpenModule _ modul) _ modules cs
		//	lookup the members for the class
		#	allClasses	= modul.mod_defs.def_classes
			search		= dropWhile (\{class_name} -> class_name<>struct_ident) allClasses
		|	isEmpty search
			= (False, False, No, modules, cs)
		#	{class_members}	= hd search
			element_idents	= [ ds_ident \\ {ds_ident} <-:class_members ]
		= (isMember element_ident element_idents, True, Yes element_idents, modules, cs)
	continuation imported_st (STE_OpenModule _ modul) _ modules cs
		//	lookup the constructors/fields for the algebraic type/record
		#	allTypes	= modul.mod_defs.def_types
			search		= dropWhile (\{td_name} -> td_name<>struct_ident) allTypes
		|	isEmpty search
			= (False, False, No, modules, cs)
		#	{td_rhs}	= hd search
		|	not (isAlgOrRecordType td_rhs)
			= (False, True, No, modules, cs)
		#	element_idents	= getElements td_rhs
		= (isMember element_ident element_idents, True, Yes element_idents, modules, cs)
	continuation ST_Class STE_ClosedModule dcl_module modules cs
		// lookup the class and compare
		#	com_member_def	= dcl_module.dcl_common.com_member_defs.[dcl_index]
			{glob_object}	= com_member_def.me_class
			com_class_def	= dcl_module.dcl_common.com_class_defs.[glob_object]
			allMembers		= com_class_def.class_members
			member_idents	= [ ds_ident \\ {ds_ident} <-: allMembers]
			appears	= com_class_def.class_name==struct_ident
		= (appears, True, if appears (Yes member_idents) No, modules, cs)
	continuation imported_st STE_ClosedModule dcl_module modules cs
		// lookup the type of the constructor and compare
		#	type_index	= if (imported_st==ST_AlgType)
								 dcl_module.dcl_common.com_cons_defs.[dcl_index].cons_type_index 
								 dcl_module.dcl_common.com_selector_defs.[dcl_index].sd_type_index
			com_type_def	= dcl_module.dcl_common.com_type_defs.[type_index]
			element_idents	= getElements com_type_def.td_rhs
			appears	= com_type_def.td_name==struct_ident
		= (appears, True, if appears (Yes element_idents) No, modules, cs)
	isAlgOrRecordType (AlgType _)		= True
	isAlgOrRecordType (RecordType _)	= True
	isAlgOrRecordType _					= False
	getElements (AlgType constructor_symbols)
		= [ds_ident \\ {ds_ident} <- constructor_symbols]
	getElements (RecordType {rt_fields})
		= [ fs_name \\ {fs_name}<-:rt_fields ]
	getElements _
		= []

check_completeness_of_module :: .Index [(.Declaration,.Int)] .String *(*{!.FunctionConsequence},*{#.DclModule},*{#FunDef},*ExpressionHeap,*CheckState) -> (.{!FunctionConsequence},.{#DclModule},.{#FunDef},.ExpressionHeap,.CheckState);
check_completeness_of_module mod_index dcls_explicit file_name (f_consequences, modules, icl_functions, expr_heap, cs)
	#	dcls_imp	= [((dcl_ident, kind), (dcl_index, mod_index), (file_name, line_nr))
						\\ ({dcl_ident, dcl_index, dcl_kind=STE_Imported kind mod_index}, line_nr) <- dcls_explicit]
		(conseqs, (f_consequences, modules, icl_functions, expr_heap))
				= mapSt (consequences_of mod_index) dcls_imp (f_consequences, modules, icl_functions, expr_heap)
		conseqs	= flatten conseqs
	#!	(modules, cs)	= foldr checkConsequenceError (modules, cs) conseqs
	= (f_consequences, modules, icl_functions, expr_heap, cs)

consequences_of ::	!Index
					(!IdentWithKind, !(!Index,!Index), !(!String, !Int)) !(!*{!FunctionConsequence}, !*{#DclModule}, !*{#FunDef}, !*ExpressionHeap)
 				->	(![(!IdentWithKind, !IdentWithCKind, !(!String, !Int))], !(*{!FunctionConsequence}, !*{#DclModule}, !*{#FunDef}, !*ExpressionHeap))
consequences_of count (expl_imp_ident_kind=:(_,expl_imp_kind), (dcl_index, mod_index), errMsgInfo) 
				(f_consequences, modules, icl_functions, expr_heap)
	= case expl_imp_kind of
			STE_FunctionOrMacro _
				# (consequences, (f_consequences, icl_functions, expr_heap)) = consequences_of_macro count dcl_index f_consequences icl_functions expr_heap
				-> (add_kind_and_error_info_to_consequences consequences, (f_consequences, modules, icl_functions, expr_heap))
			_
				# (modul, modules)	= modules![mod_index]
				-> (add_kind_and_error_info_to_consequences (consequences_of_simple_symbol expl_imp_kind modul dcl_index), (f_consequences, modules, icl_functions, expr_heap))
	where
		add_kind_and_error_info_to_consequences consequences
			= [(expl_imp_ident_kind, conseq, errMsgInfo) \\ conseq<-removeDup consequences]
	
consequences_of_macro count dcl_index f_consequences icl_functions expr_heap
	#	(icl_function, icl_functions)	= icl_functions![dcl_index]
		{fun_body}	= icl_function
		result = consequences fun_body
	= expand_functions_and_dynamics result [] (f_consequences, icl_functions, expr_heap)
  where
	expand_functions_and_dynamics [] akku unique_stuff
		= (akku, unique_stuff)
	expand_functions_and_dynamics [(_,CK_DynamicPatternType exprInfoPtr):t] akku (f_consequences, icl_functions, expr_heap)
		#	(conseqs, expr_heap)	= expand_dynamic exprInfoPtr expr_heap
		= expand_functions_and_dynamics t (conseqs++akku) (f_consequences, icl_functions, expr_heap)
	expand_functions_and_dynamics [(ident,(CK_Function globIndex)):t] akku unique_stuff
		#	(conseqs, unique_stuff) = expand_function ident globIndex unique_stuff
		= expand_functions_and_dynamics t (conseqs++akku) unique_stuff
	expand_functions_and_dynamics [h:t] akku unique_stuff
		= expand_functions_and_dynamics t [h:akku] unique_stuff

	expand_dynamic :: ExprInfoPtr *ExpressionHeap -> ([IdentWithCKind], *ExpressionHeap)
	expand_dynamic exprInfoPtr expr_heap
	// it is assumed, that the pointer structure from the fi_dynamics field (of record FunInfo)
	// is a tree
		#	(exprInfo, expr_heap)	= readPtr exprInfoPtr expr_heap
			(conseqs, expr_heap)
			 	= case exprInfo of
							(EI_Dynamic No)	
								-> ([], expr_heap)
							(EI_Dynamic (Yes dynamicType))
								-> (consequences dynamicType, expr_heap)
							(EI_DynamicType dynamicType further_dynamic_ptrs)
								#	(further_conseqs, expr_heap)	= expand_dynamics further_dynamic_ptrs [] expr_heap
								-> (further_conseqs++consequences dynamicType, expr_heap)
							(EI_DynamicTypeWithVars _ dynamicType further_dynamic_ptrs)
								#	(further_conseqs, expr_heap)	= expand_dynamics further_dynamic_ptrs [] expr_heap
								-> (further_conseqs++consequences dynamicType, expr_heap)
		= (conseqs, expr_heap)
	
	expand_dynamics [] akku expr_heap
		= (akku, expr_heap)
	expand_dynamics [h:t] akku expr_heap
		#	(dyn, expr_heap)	= expand_dynamic h expr_heap
		= expand_dynamics t (dyn++akku) expr_heap


	expand_function ident globIndex=:{glob_object,glob_module} (f_consequences, icl_functions, expr_heap)
		|	glob_module<>cIclModIndex	// the function that is referred from within a macro is a DclFunction
										// -> must be global -> is a consequence
			= ([(ident, CK_Function globIndex)], (f_consequences, icl_functions, expr_heap))
		#	(fun_def, icl_functions)	= icl_functions![glob_object]
		|	fun_def.fun_info.fi_def_level==cGlobalScope	// the function is defined in the icl module in the global scope
														// -> it's not a consequence
			= ([], (f_consequences, icl_functions, expr_heap))
		// otherwise the function was defined locally in a macro and stored in the IclModule object.
		// it is not a consequence, but it's type and body are consequences !
		#	(opt_f_consequences, f_consequences)	= f_consequences![glob_object]
		= case opt_f_consequences of
			No 	#	type_consequences	= consequences fun_def.fun_type
					body_consequences	= consequences fun_def.fun_body
					dynamic_pointers	= fun_def.fun_info.fi_dynamics
				#	(dynamic_consequences, expr_heap)
										= expand_dynamics dynamic_pointers [] expr_heap
					f_consequences		= { f_consequences & [glob_object]=Yes (count, No) }
					(cons, (f_consequences, icl_functions, expr_heap))
										= expand_functions_and_dynamics body_consequences [] (f_consequences, icl_functions,expr_heap)
					cons_of_function	= type_consequences++cons++dynamic_consequences
					f_consequences		= { f_consequences & [glob_object]=Yes (count, Yes cons_of_function) }
				-> (cons_of_function, (f_consequences, icl_functions, expr_heap))
			Yes (j, opt_consequences)
				|	j==count	// the consequences of the function are already considered
				-> ([], (f_consequences, icl_functions, expr_heap))
			Yes (j, Yes cons)
				|	j<count	// always True
				-> (cons, (f_consequences, icl_functions, expr_heap))

consequences_of_simple_symbol STE_Type {dcl_common} dcl_index
	= consequences dcl_common.com_type_defs.[dcl_index]
consequences_of_simple_symbol STE_Constructor {dcl_common} dcl_index
	= consequences dcl_common.com_cons_defs.[dcl_index]
consequences_of_simple_symbol STE_DclFunction {dcl_functions} dcl_index
	= consequences dcl_functions.[dcl_index]
consequences_of_simple_symbol (STE_Field _) {dcl_common} dcl_index
	= consequences dcl_common.com_selector_defs.[dcl_index]
consequences_of_simple_symbol STE_Class {dcl_common} dcl_index
	= consequences dcl_common.com_class_defs.[dcl_index]
consequences_of_simple_symbol STE_Member {dcl_common} dcl_index
	= consequences dcl_common.com_member_defs.[dcl_index]
consequences_of_simple_symbol STE_Instance {dcl_common} dcl_index
	= consequences dcl_common.com_instance_defs.[dcl_index]

checkConsequenceError :: !((Ident,.STE_Kind),!.(Ident,ConsequenceKind),!(.{#Char},.Int)) !*(*{#DclModule},!*CheckState) -> (!*{#DclModule},!.CheckState)
checkConsequenceError (expl_imp_ident_kind, conseq_ident_kind=:(conseq_ident, conseq_kind), (file_name, line_nr))
					 (modules, cs=:{cs_symbol_table, cs_error})
	#	(c_ident, modules)
			= case conseq_kind of
				CK_Selector {glob_object,glob_module}				// if a selector is a consequence of an imported macro the
					#	(modul, modules)	= modules![glob_module]	// it's FIELD has to be looked up
						com_selector_def	= modul.dcl_common.com_selector_defs.[glob_object.ds_index]
					-> (com_selector_def.sd_field, modules)
				_	-> (conseq_ident, modules)
		({ste_kind}, cs_symbol_table)				= readPtr c_ident.id_info cs_symbol_table
		cs_error
			= case ste_kind of
				STE_Empty
							-> cError expl_imp_ident_kind
									  (   "explicitly imported without importing "
									   +++cIdent_kind_to_string conseq_ident_kind)
									  cs_error
				_			-> cs_error
	= (modules, { cs & cs_symbol_table=cs_symbol_table, cs_error=cs_error })
  where
	ident_kind_to_string ({id_name}, kind)
		= kind_to_string kind+++" "+++id_name
	cIdent_kind_to_string ({id_name}, cKind)
		= cKind_to_string cKind+++" "+++id_name
	cError expl_imp_ident_kind=:(expl_ident,_) s2 cs_error
		#	identPos	= {	ip_ident = expl_ident, ip_line = line_nr, ip_file = file_name } 
			cs_error	= pushErrorAdmin identPos cs_error
			cs_error	= checkError (ident_kind_to_string expl_imp_ident_kind) s2 cs_error
			cs_error	= popErrorAdmin cs_error
		= cs_error

kind_to_string (STE_FunctionOrMacro _)	= "function"
kind_to_string STE_Type					= "type"
kind_to_string STE_Constructor			= "constructor"
kind_to_string (STE_Field _)			= "field"
kind_to_string STE_Class				= "class"
kind_to_string STE_Member				= "member"
kind_to_string STE_Instance				= "instance"
kind_to_string STE_DclFunction			= "function"

cKind_to_string (CK_Function _)			= "function"
cKind_to_string CK_Macro				= "macro"
cKind_to_string CK_Type					= "type"
cKind_to_string CK_Constructor			= "constructor"
cKind_to_string (CK_Selector _)			= "appropriate record field"
cKind_to_string CK_Class				= "class"

class consequences x :: x -> [IdentWithCKind]

instance consequences App
  where consequences {app_symb, app_args}	= consequences app_symb++consequences app_args
	
instance consequences AlgebraicPattern
  where consequences {ap_symbol, ap_expr} = [ (ap_symbol.glob_object.ds_ident, CK_Constructor) : consequences ap_expr]

instance consequences AType
  where
	consequences {at_type}	= consequences at_type

instance consequences BasicPattern
  where consequences {bp_expr} = consequences bp_expr

instance consequences Case
  where	consequences { case_expr, case_guards, case_default, case_ident }
		= consequences case_expr++consequences case_guards++consequences case_default

instance consequences CasePatterns
  where
	consequences (AlgebraicPatterns _ algebraicPatterns)	= consequences algebraicPatterns
	consequences (BasicPatterns _ basicPatterns)	= consequences basicPatterns
	consequences (DynamicPatterns dynamicPatterns)	= consequences dynamicPatterns
	consequences NoPattern	= []

instance consequences CheckedBody
  where consequences {cb_rhs} = consequences cb_rhs

instance consequences ClassDef
  where
	consequences {class_context}	= consequences class_context	

instance consequences ClassInstance
  where
	consequences {ins_type}	= consequences ins_type	

instance consequences ConsDef
  where
	consequences {cons_type}	= consequences cons_type	

instance consequences DynamicPattern // the types, that are found via dp_type are checked later
  where	consequences { dp_rhs, dp_type } = [({ id_name="", id_info=nilPtr}, CK_DynamicPatternType dp_type): consequences dp_rhs]

instance consequences DynamicExpr
  where	consequences { dyn_expr, dyn_opt_type } = consequences dyn_expr++consequences dyn_opt_type

instance consequences DynamicType
  where	consequences { dt_type } = consequences dt_type

instance consequences Expression
  where
	consequences (Var _)	= []
	consequences (App app)	= consequences app
	consequences (expression @ expressions)	= consequences expression++consequences expressions
	consequences (Let let_)	= consequences let_
	consequences (Case case_)	= consequences case_
	consequences (Selection _ expression selections)	= consequences expression++consequences selections
	consequences (TupleSelect _ _ expression)	= consequences expression
	consequences (BasicExpr _ _)		= []
	consequences (AnyCodeExpr _ _ _)	= []
	consequences (ABCCodeExpr _ _)	= []
	consequences (MatchExpr _ constructor expression)
		= [(constructor.glob_object.ds_ident,CK_Constructor):consequences expression]
	consequences (FreeVar _) 	= []
	consequences (DynamicExpr dynamicExpr)	= consequences dynamicExpr
	consequences EE	= []
	consequences (Update expr1 selections expr2)	=  consequences expr1++consequences selections++consequences expr2
	consequences expr	= abort "explicitimports:consequences (Expression) does not match" <<- expr

instance consequences FunctionBody
  where	consequences (CheckedBody body) = consequences body
		consequences (TransformedBody body) = consequences body
		consequences (RhsMacroBody body) = consequences body
		
instance consequences FunType
  where
	consequences {ft_type}	= consequences ft_type	

instance consequences (Global x) | consequences x
  where	consequences { glob_object } = consequences glob_object

instance consequences InstanceType
  where
	consequences {it_types, it_context}	= consequences it_types++consequences it_context	

instance consequences Let
  where	consequences { let_strict_binds, let_lazy_binds, let_expr }
  			= consequences let_expr++(flatten [consequences bind_src \\ {bind_src}<-let_strict_binds ++ let_lazy_binds] )

instance consequences MemberDef
  where
	consequences {me_type}	= consequences me_type	

instance consequences (Optional x) | consequences x
  where	consequences (Yes x) = consequences x
  		consequences No = []

instance consequences Selection
  where consequences (RecordSelection globDefinedSymbol=:{glob_object={ds_ident}} _)
  			= [(ds_ident, CK_Selector globDefinedSymbol)]
		consequences (ArraySelection {glob_object={ds_ident={id_name}}} _ _)
  			= []

instance consequences SelectorDef
  where consequences {sd_type}	= consequences sd_type	

instance consequences SymbIdent
  where consequences {symb_name, symb_kind}
  			= case symb_kind of
  					SK_Constructor _		-> [(symb_name, CK_Constructor)]
  			  		SK_Function	globalIndex	-> [(symb_name, CK_Function globalIndex)]
  			  		SK_OverloadedFunction globalIndex
  			  								-> [(symb_name, CK_Function globalIndex)]
  			  		SK_Macro globalIndex	-> [(symb_name, CK_Macro)]
  			  		_						-> []

instance consequences SymbolType
  where
	consequences {st_args, st_result, st_context}
		= consequences st_args++consequences st_result++consequences st_context

instance consequences TransformedBody
  where consequences {tb_rhs} = consequences tb_rhs

instance consequences Type
  where
	consequences (TA {type_name} arguments)
		= [(type_name, CK_Type):consequences arguments]
	consequences (l --> r)
		= consequences l++consequences r
	consequences (_ :@: arguments)
		= consequences arguments
	consequences _
		= []


instance consequences TypeContext
  where
	consequences {tc_class= {glob_object={ds_ident}}, tc_types}
		= [(ds_ident,CK_Class):consequences tc_types]

instance consequences (TypeDef TypeRhs)  // ==CheckedTypeDef
  where
	consequences {td_rhs, td_context}	= consequences td_rhs++consequences td_context

instance consequences TypeRhs
  where
	consequences (SynType aType)	= consequences aType
	consequences _					= []

instance consequences [a]	| consequences a
  where
	consequences l	= flatten (map consequences l)
  
