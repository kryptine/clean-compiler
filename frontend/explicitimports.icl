implementation module explicitimports
// compile using the "reuse unique nodes" option

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

::	OptimizeInfo	:==	Optional Index

possibly_filter_decls :: ![ImportDeclaration] ![(!Index,!Declarations)] !(!FileName,!LineNr) !*{#DclModule} !*CheckState 
						-> (![(!Index,!Declarations)],!.{#DclModule},!.CheckState)
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

NoPosition :== -1

filter_decl :: [.Declaration] ([(Ident,AtomType)],[(Ident,StructureInfo,StructureType,Optional Int)]) Int *{#DclModule} *CheckState -> (!(!.[Declaration],!([(Ident,AtomType)],![(Ident,StructureInfo,StructureType,Optional Int)])),!.{#DclModule},!.CheckState);
filter_decl [] unimported _ modules cs
	= (([], unimported), modules, cs)
filter_decl [decl:decls] unimported index modules cs
	# ((appears,unimported), modules, cs) = decl_appears decl unimported index modules cs
	| appears
		# ((recurs, unimported), modules, cs) = filter_decl decls unimported index modules cs

		= (([decl:recurs],unimported), modules, cs)
	= 	filter_decl decls unimported index modules cs
	
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


elementAppears :: .StructureType Ident !.Int !(.a,![(Ident,.StructureInfo,.StructureType,Optional .Int)]) !.Int !*{#.DclModule} !*CheckState -> (!(!Bool,(!.a,![(Ident,StructureInfo,StructureType,Optional Int)])),!.{#DclModule},!.CheckState);
elementAppears imported_st dcl_ident dcl_index (atomicImports, structureImports) index modules cs
	#	((result, structureImports), modules, cs)
			=  element_appears imported_st dcl_ident dcl_index structureImports structureImports 0 index modules cs
	= ((result, (atomicImports, structureImports)), modules, cs)

atomAppears dcl_ident dcl_index (atomicImports, structureImports) index modules cs
	#	((result, atomicImports), modules, cs)
			= atom_appears dcl_ident dcl_index atomicImports atomicImports 0 index modules cs
	= ((result, (atomicImports, structureImports)), modules, cs)

atom_appears :: Ident !.Int [(Ident,.AtomType)] w:[y:(Ident,u1:AtomType)] !Int !.Int !u:{#u3:DclModule} !*CheckState -> (!(.Bool,x:[z:(Ident,u2:AtomType)]),!v:{#DclModule},!.CheckState) , [u <= v, u1 <= u2, y <= z, w <= x, u <= u3];
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

element_appears :: StructureType Ident !Int [(Ident,.StructureInfo,u2:StructureType,z:Optional .Int)] u:[w:(Ident,u5:StructureInfo,u3:StructureType,y:Optional Int)] !Int !Int !*{#DclModule} !*CheckState -> (!(!Bool,!v:[x:(Ident,u6:StructureInfo,u4:StructureType,u1:Optional Int)]),!.{#DclModule},!.CheckState), [y z <= u1, u3 <= u4, u5 <= u6, w <= x, u <= v, u2 <= u3];
element_appears _ _ _ [] atomic_imports _ _ modules cs
	= ((False, atomic_imports), modules, cs)
// MW2 remove this later ..
element_appears imported_st element_ident dcl_index
				[(_, SI_DotDot, ST_stomm_stomm_stomm type_name_string, optInfo):t] atomic_imports unimp_index
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
				[(_, _, st, _):t] atomic_imports unimp_index
				index modules cs
	|	imported_st<>st
		= element_appears imported_st element_ident dcl_index t atomic_imports (inc unimp_index) index modules cs
	// goes further with next alternative
element_appears imported_st element_ident dcl_index
				[(_, _, _, (Yes notDefinedHere)):t] atomic_imports unimp_index
				index modules cs
	|	notDefinedHere==dcl_index 
		= element_appears imported_st element_ident dcl_index t atomic_imports (inc unimp_index) index modules cs
	// goes further with next alternative
element_appears	imported_st element_ident dcl_index
				[(struct_id, (SI_Elements elements explicit), st, optInfo):t] atomic_imports unimp_index
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
				[(struct_id, SI_DotDot, st, optInfo):t] atomic_imports unimp_index
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

element_appears_in_stomm_struct :: .StructureType Ident .Int .Int .String *{#DclModule} !*CheckState -> (!Bool,!.{#DclModule},!.CheckState)
// MW remove this later CCC
element_appears_in_stomm_struct imported_st element_ident dcl_index index type_name_string modules cs
	| not do_temporary_import_solution_XXX
		= abort "element_appears_in_stomm_struct will be never called, when the above guard holds. This statement is only to remind people to remove this function."
	#	(dcl_module=:{dcl_name=dcl_name=:{id_info}}, modules)		= modules ! [index]
		(module_entry, cs_symbol_table)				= readPtr id_info cs.cs_symbol_table
	#!	cs	= { cs & cs_symbol_table=cs_symbol_table }
//	= continuation imported_st module_entry.ste_kind dcl_module modules cs
	= (appears imported_st module_entry.ste_kind dcl_module.dcl_common,modules,cs);
  where
	appears ST_RecordType (STE_OpenModule _ modul) _
		//	lookup the constructors/fields for the algebraic type/record
		#	allTypes	= modul.mod_defs.def_types
			search		= dropWhile (\{td_name} -> td_name.id_name<>type_name_string) allTypes
		|	isEmpty search
			= False
		#	{td_rhs}	= hd search
		|	not (isRecordType td_rhs)
			= False
		#	element_idents	= getElements td_rhs
		= isMember element_ident element_idents
	appears ST_RecordType STE_ClosedModule dcl_common
		// lookup the type of the constructor and compare
		#	type_index		= dcl_common.com_selector_defs.[dcl_index].sd_type_index
			com_type_def	= dcl_common.com_type_defs.[type_index]
			appears	= com_type_def.td_name.id_name==type_name_string
		= appears
	appears ST_Class (STE_OpenModule _ modul) _
		//	lookup the members for the class
		#	allClasses	= modul.mod_defs.def_classes
			search		= dropWhile (\{class_name} -> class_name.id_name<>type_name_string) allClasses
		|	isEmpty search
			= False
		#	{class_members}	= hd search
			element_idents	= [ ds_ident \\ {ds_ident} <-:class_members ]
		= isMember element_ident element_idents
	appears ST_Class STE_ClosedModule dcl_common
		// lookup the class and compare
		#	com_member_def	= dcl_common.com_member_defs.[dcl_index]
			{glob_object}	= com_member_def.me_class
			com_class_def	= dcl_common.com_class_defs.[glob_object]
			appears	= com_class_def.class_name.id_name==type_name_string
		= appears
	appears _ _ _
		= False

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

:: CheckCompletenessState =
	{	ccs_dcl_modules				:: !.{#DclModule}
	,	ccs_icl_functions			:: !.{#FunDef}
	,	ccs_set_of_visited_icl_funs	:: !.{#Bool}		// ccs_set_of_visited_icl_funs.[i] <=> function nr i has been considered
	,	ccs_expr_heap				:: !.ExpressionHeap
	,	ccs_symbol_table			:: !.SymbolTable
	,	ccs_error					:: !.ErrorAdmin
	,	ccs_heap_changes_accu		:: ![SymbolPtr]
	}
:: *CheckCompletenessStateBox = { box_ccs :: !*CheckCompletenessState }

:: CheckCompletenessInput =
	{	cci_line_nr				:: !Int
	,	cci_filename			:: !String
	,	cci_expl_imported_ident	:: !Ident
	}
:: CheckCompletenessInputBox = { box_cci :: !CheckCompletenessInput }

checkExplicitImportCompleteness :: !String ![(!Declaration,!Int)]
								!*{#DclModule} !*{#FunDef} !*ExpressionHeap !*CheckState 
								-> (!.{#DclModule},!.{#FunDef},!.ExpressionHeap,!.CheckState)
checkExplicitImportCompleteness filename dcls_explicit dcl_modules icl_functions expr_heap 
								cs=:{cs_symbol_table, cs_error}
	#! nr_icl_functions = size icl_functions
	   box_ccs = { ccs_dcl_modules = dcl_modules, ccs_icl_functions = icl_functions,
	   			ccs_set_of_visited_icl_funs = createArray nr_icl_functions False,
				ccs_expr_heap = expr_heap, ccs_symbol_table = cs_symbol_table,
				ccs_error = cs_error, ccs_heap_changes_accu = [] }
	   ccs = foldSt (checkCompleteness filename) dcls_explicit { box_ccs = box_ccs }
	   { ccs_dcl_modules, ccs_icl_functions, ccs_expr_heap, ccs_symbol_table, ccs_error, ccs_heap_changes_accu }
	   		= ccs.box_ccs
	// repair heap contents
	   ccs_symbol_table = foldSt replace_ste_with_previous ccs_heap_changes_accu ccs_symbol_table
	   cs = { cs & cs_symbol_table = ccs_symbol_table, cs_error = ccs_error }
	= (ccs_dcl_modules, ccs_icl_functions, ccs_expr_heap, cs)
  where
	checkCompleteness :: !String !(!Declaration, !Int) *CheckCompletenessStateBox -> *CheckCompletenessStateBox
	checkCompleteness filename ({dcl_ident, dcl_index, dcl_kind=STE_FunctionOrMacro _}, line_nr) ccs 
		= checkCompletenessOfMacro filename dcl_ident dcl_index line_nr ccs
	checkCompleteness filename ({dcl_ident, dcl_index, dcl_kind=STE_Imported (STE_FunctionOrMacro _) mod_index}, line_nr) ccs 
		= checkCompletenessOfMacro filename dcl_ident dcl_index line_nr ccs
	checkCompleteness filename ({dcl_ident, dcl_index, dcl_kind=STE_Imported expl_imp_kind mod_index}, line_nr) ccs 
		#! ({dcl_common,dcl_functions}, ccs) = ccs!box_ccs.ccs_dcl_modules.[mod_index]
		   cci = { box_cci = { cci_line_nr = line_nr, cci_filename = filename, cci_expl_imported_ident = dcl_ident }}
		= case expl_imp_kind of
			STE_Type			-> check_completeness dcl_common.com_type_defs.[dcl_index] cci ccs
			STE_Constructor		-> check_completeness dcl_common.com_cons_defs.[dcl_index] cci ccs
			(STE_Field _)		-> check_completeness dcl_common.com_selector_defs.[dcl_index] cci ccs
			STE_Class			-> check_completeness dcl_common.com_class_defs.[dcl_index] cci ccs
			STE_Member			-> check_completeness dcl_common.com_member_defs.[dcl_index] cci ccs
			STE_Instance		-> check_completeness dcl_common.com_instance_defs.[dcl_index] cci ccs
			STE_DclFunction		-> check_completeness dcl_functions.[dcl_index] cci ccs
	
	checkCompletenessOfMacro :: !String !Ident !Index !Int *CheckCompletenessStateBox -> *CheckCompletenessStateBox
	checkCompletenessOfMacro filename dcl_ident dcl_index line_nr ccs
		#! ({fun_body}, ccs) = ccs!box_ccs.ccs_icl_functions.[dcl_index]
		   ccs = { ccs & box_ccs.ccs_set_of_visited_icl_funs.[dcl_index] = True }
		   cci = { box_cci = { cci_line_nr = line_nr, cci_filename = filename, cci_expl_imported_ident = dcl_ident }}
		= check_completeness fun_body cci ccs

	replace_ste_with_previous :: !SymbolPtr !*SymbolTable -> .SymbolTable
	replace_ste_with_previous changed_ste_ptr symbol_table
		#! ({ste_previous}, symbol_table) = readPtr changed_ste_ptr symbol_table
		= writePtr changed_ste_ptr ste_previous symbol_table
	
instance toString STE_Kind where
	toString (STE_FunctionOrMacro _)	= "function/macro"
	toString STE_Type 					= "type"
	toString STE_Constructor 			= "constructor"
	toString (STE_Field _) 				= "field"
	toString STE_Class 					= "class"
	toString STE_Member 				= "class member"

check_whether_ident_is_imported :: !Ident !STE_Kind !CheckCompletenessInputBox !*CheckCompletenessStateBox 
								-> *CheckCompletenessStateBox
check_whether_ident_is_imported ident wanted_ste_kind cci ccs=:{box_ccs=box_ccs=:{ccs_symbol_table}}
	#! (ste=:{ste_kind}, ccs_symbol_table) = readPtr ident.id_info ccs_symbol_table
	   ccs = { ccs & box_ccs = { box_ccs & ccs_symbol_table = ccs_symbol_table } }
	| is_imported ste_kind wanted_ste_kind
		= ccs
	#! (ccs=:{box_ccs=box_ccs=:{ccs_symbol_table, ccs_error, ccs_heap_changes_accu}}) = ccs
	   {box_cci={cci_line_nr, cci_filename, cci_expl_imported_ident}} = cci
	   ident_pos = {ip_ident= { id_name="import", id_info=nilPtr }, ip_line=cci_line_nr, ip_file=cci_filename}
	   ccs_error = checkErrorWithIdentPos ident_pos
	  				(cci_expl_imported_ident.id_name+++" explicitly imported without importing "
	  				 +++toString wanted_ste_kind+++" "+++ident.id_name)
	  				ccs_error
	   // pretend that the unimported symbol was imported to prevent doubling error mesages
	   ccs_symbol_table = writePtr ident.id_info { ste & ste_kind = wanted_ste_kind, ste_previous = ste } ccs_symbol_table
	= { ccs & box_ccs = { box_ccs & ccs_error = ccs_error, ccs_symbol_table = ccs_symbol_table, 
									ccs_heap_changes_accu = [ident.id_info:ccs_heap_changes_accu] }}
  where
	is_imported (STE_Imported ste_kind _) wanted_ste_kind
		= ste_kind==wanted_ste_kind
	is_imported ste_kind wanted_ste_kind
		= ste_kind==wanted_ste_kind

class check_completeness x :: !x !CheckCompletenessInputBox !*CheckCompletenessStateBox -> *CheckCompletenessStateBox

instance check_completeness App where
	check_completeness {app_symb, app_args}	cci ccs
		= check_completeness app_symb cci
		  (check_completeness app_args cci ccs)
	
instance check_completeness AlgebraicPattern where
	check_completeness {ap_symbol, ap_expr} cci ccs
		= check_completeness ap_expr cci
		  (check_whether_ident_is_imported ap_symbol.glob_object.ds_ident STE_Constructor cci ccs)

instance check_completeness AType where
	check_completeness {at_type} cci ccs
		= check_completeness at_type cci ccs

instance check_completeness BasicPattern where
	check_completeness {bp_expr} cci ccs
		= check_completeness bp_expr cci ccs

instance check_completeness (Bind Expression FreeVar) where
	check_completeness {bind_src} cci ccs
		= check_completeness bind_src cci ccs

instance check_completeness Case where
	check_completeness { case_expr, case_guards, case_default } cci ccs
		= ( (check_completeness case_expr cci)
		  o (check_completeness case_guards cci)
		  o (check_completeness case_default cci)
		  ) ccs

instance check_completeness CasePatterns where
	check_completeness (AlgebraicPatterns _ algebraicPatterns) cci ccs
		= check_completeness algebraicPatterns cci ccs
	check_completeness (BasicPatterns _ basicPatterns) cci ccs
		= check_completeness basicPatterns cci ccs
	check_completeness (DynamicPatterns dynamicPatterns) cci ccs
		= check_completeness dynamicPatterns cci ccs
	check_completeness NoPattern _ ccs
		= ccs

instance check_completeness CheckedBody where
	check_completeness {cb_rhs} cci ccs
		= check_completeness cb_rhs cci ccs

instance check_completeness ClassDef where
	check_completeness {class_context} cci ccs
		= check_completeness class_context cci ccs

instance check_completeness ClassInstance where
	check_completeness {ins_type} cci ccs
		= check_completeness ins_type cci ccs

instance check_completeness ConsDef
  where
	check_completeness {cons_type} cci ccs
		= check_completeness cons_type cci ccs

instance check_completeness DynamicPattern where
	check_completeness { dp_rhs, dp_type } cci ccs
		= check_completeness dp_rhs cci
		  (check_completeness_of_dyn_expr_ptr dp_type cci ccs)
	
instance check_completeness DynamicExpr where
	check_completeness { dyn_expr, dyn_opt_type } cci ccs
		= check_completeness dyn_expr cci
		  (check_completeness dyn_opt_type cci ccs)

instance check_completeness DynamicType where
	check_completeness { dt_type } cci ccs
		= check_completeness dt_type cci ccs

instance check_completeness Expression where
	check_completeness (Var _) cci ccs
		= ccs
	check_completeness (App app) cci ccs
		= check_completeness app cci ccs
	check_completeness (expression @ expressions) cci ccs
		= check_completeness expression cci
		  (check_completeness expressions cci ccs)
	check_completeness (Let lad) cci ccs
		= check_completeness lad cci ccs
	check_completeness (Case keesje) cci ccs
		= check_completeness keesje cci ccs
	check_completeness (Selection _ expression selections) cci ccs
		= check_completeness expression cci
		  (check_completeness selections cci ccs)
	check_completeness (TupleSelect _ _ expression) cci ccs
		= check_completeness expression cci ccs
	check_completeness (BasicExpr _ _) _ ccs
		= ccs
	check_completeness (AnyCodeExpr _ _ _) _ ccs
		= ccs
	check_completeness (ABCCodeExpr _ _) _ ccs
		= ccs
	check_completeness (MatchExpr _ constructor expression) cci ccs
		= check_completeness expression cci
		  (check_whether_ident_is_imported constructor.glob_object.ds_ident STE_Constructor cci ccs)
	check_completeness (FreeVar _) _ ccs
		= ccs
	check_completeness (DynamicExpr dynamicExpr) cci ccs
		= check_completeness dynamicExpr cci ccs
	check_completeness EE _ ccs
		= ccs
	check_completeness (Update expr1 selections expr2) cci ccs
		= ( (check_completeness expr1 cci)
		  o (check_completeness selections cci)
		  o (check_completeness expr2) cci
		  ) ccs
	check_completeness expr _ _
		= abort "explicitimports:check_completeness (Expression) does not match" <<- expr

instance check_completeness FunctionBody where
	check_completeness (CheckedBody body) cci ccs
		= check_completeness body cci ccs
	check_completeness (TransformedBody body) cci ccs
		= check_completeness body cci ccs
	check_completeness (RhsMacroBody body) cci ccs
		= check_completeness body cci ccs
			
instance check_completeness FunDef where
	check_completeness {fun_type, fun_body, fun_info} cci ccs
		= ( (check_completeness fun_type cci)
		  o (check_completeness fun_body cci)
		  o (foldSt (flipM check_completeness_of_dyn_expr_ptr cci) fun_info.fi_dynamics)
		  ) ccs

instance check_completeness FunType where
	check_completeness {ft_type} cci ccs
		= check_completeness ft_type cci ccs

instance check_completeness (Global x) | check_completeness x where
	check_completeness { glob_object } cci ccs
		= check_completeness glob_object cci ccs

instance check_completeness InstanceType where
	check_completeness {it_types, it_context} cci ccs
		= check_completeness it_types cci
		  (check_completeness it_context cci ccs)

instance check_completeness Let where
	check_completeness { let_strict_binds, let_lazy_binds, let_expr } cci ccs
  		= ( (check_completeness let_expr cci)
  		  o (check_completeness let_strict_binds cci)
  		  o (check_completeness let_lazy_binds cci)
  		  ) ccs

instance check_completeness MemberDef where
  	check_completeness {me_type} cci ccs 
  		= check_completeness me_type cci ccs

instance check_completeness (Optional x) | check_completeness x where
	check_completeness (Yes x) cci ccs
		= check_completeness x cci ccs
	check_completeness No _ ccs
		= ccs

instance check_completeness Selection where
	check_completeness (RecordSelection {glob_object,glob_module} _) cci ccs
		#! ({dcl_common}, ccs)	= ccs!box_ccs.ccs_dcl_modules.[glob_module]	// the selector's filed has to be looked up
		   ({sd_field}) = dcl_common.com_selector_defs.[glob_object.ds_index]
		= check_whether_ident_is_imported sd_field ste_field cci ccs
	check_completeness (ArraySelection _ _ index_expr) cci ccs
		= check_completeness index_expr cci ccs
	check_completeness (DictionarySelection _ selections _ index_expr) cci ccs
		= check_completeness selections cci
		  (check_completeness index_expr cci ccs)

instance check_completeness SelectorDef where
	check_completeness {sd_type} cci ccs
		= check_completeness sd_type cci ccs

instance check_completeness SymbIdent where
	check_completeness {symb_name, symb_kind} cci ccs
		= case symb_kind of
			SK_Constructor _
				-> check_whether_ident_is_imported symb_name STE_Constructor cci ccs
			SK_Function global_index
				-> check_completeness_for_function symb_name global_index ste_fun_or_macro cci ccs
			SK_OverloadedFunction global_index
				-> check_completeness_for_function symb_name global_index STE_Member cci ccs
  			SK_Macro global_index
  				-> check_completeness_for_function symb_name global_index ste_fun_or_macro cci ccs
  	  where
		check_completeness_for_function symb_name {glob_object,glob_module} wanted_ste_kind cci ccs
			| glob_module<>cIclModIndex	
				// the function that is referred from within a macro is a DclFunction
				// -> must be global -> has to be imported
				= check_whether_ident_is_imported symb_name wanted_ste_kind cci ccs
			#! (fun_def, ccs)	= ccs!box_ccs.ccs_icl_functions.[glob_object]
			// otherwise the function was defined locally in a macro
			// it is not a consequence, but it's type and body are consequences !
			#! (already_visited, ccs) = ccs!box_ccs.ccs_set_of_visited_icl_funs.[glob_object]
			| already_visited
				= ccs
			#! ccs = { ccs & box_ccs.ccs_set_of_visited_icl_funs.[glob_object] = True }
			= check_completeness fun_def cci ccs

instance check_completeness SymbolType where
	check_completeness {st_args, st_result, st_context} cci ccs
		= ( (check_completeness st_args cci)
		  o (check_completeness st_result cci)
		  o (check_completeness st_context cci)
		  ) ccs

instance check_completeness TransformedBody where
	check_completeness {tb_rhs} cci ccs
		= check_completeness tb_rhs cci ccs

instance check_completeness Type where
	check_completeness (TA {type_name} arguments) cci ccs
		= check_completeness arguments cci
		  (check_whether_ident_is_imported type_name STE_Type cci ccs)
	check_completeness (l --> r) cci ccs
		= check_completeness l cci
		  (check_completeness r cci ccs)
	check_completeness (_ :@: arguments) cci ccs
		= check_completeness arguments cci ccs
	check_completeness _ _ ccs
		= ccs

instance check_completeness TypeContext where
	check_completeness {tc_class, tc_types} cci ccs
		= check_completeness tc_types cci
		  (check_whether_ident_is_imported tc_class.glob_object.ds_ident STE_Class cci ccs)

instance check_completeness (TypeDef TypeRhs) where
	check_completeness {td_rhs, td_context}	cci ccs
		= check_completeness td_rhs cci 
		  (check_completeness td_context cci ccs)

instance check_completeness TypeRhs where
	check_completeness (SynType aType) cci ccs
		= check_completeness aType cci ccs
	check_completeness _ _ ccs
		= ccs

instance check_completeness [a]	| check_completeness a
  where
	check_completeness [] _ ccs
		= ccs
	check_completeness [h:t] cci ccs
		= check_completeness h cci
		  (check_completeness t cci ccs)

check_completeness_of_dyn_expr_ptr :: !ExprInfoPtr !CheckCompletenessInputBox !*CheckCompletenessStateBox
								-> *CheckCompletenessStateBox 
check_completeness_of_dyn_expr_ptr dyn_expr_ptr cci ccs=:{box_ccs=box_ccs=:{ccs_expr_heap}}
	#! (expr_info, ccs_expr_heap) = readPtr dyn_expr_ptr ccs_expr_heap
	   ccs = { ccs & box_ccs = { box_ccs & ccs_expr_heap = ccs_expr_heap }}
 	= case expr_info of
		(EI_Dynamic No)	
			-> ccs
		(EI_Dynamic (Yes dynamic_type))
			-> check_completeness dynamic_type cci ccs
		(EI_DynamicType dynamic_type further_dynamic_ptrs)
			-> check_completeness dynamic_type cci
			   (foldSt (flipM check_completeness_of_dyn_expr_ptr cci) further_dynamic_ptrs ccs)
		(EI_DynamicTypeWithVars _ dynamic_type further_dynamic_ptrs)
			-> check_completeness dynamic_type cci
			   (foldSt (flipM check_completeness_of_dyn_expr_ptr cci) further_dynamic_ptrs ccs)

flipM f a b :== f b a

// STE_Kinds just for comparision
ste_field =: STE_Field { id_name="", id_info=nilPtr }
ste_fun_or_macro =: STE_FunctionOrMacro []
