implementation module portToNewSyntax

import StdEnv, scanner, Directory, merge, checksupport

switch_port_to_new_syntax port dont_port :== port

cTabWidth :== 4

resultFolderName =: "PortedModules"		

createPortedFiles :: !String !SearchPaths !*Files -> (!Bool, !*Files)
createPortedFiles fileName searchPaths files
	# (ok, files)
			= case findDirOfModule fileName searchPaths files of
				(No, files)
					-> (False, files)
				(Yes path, files)
					# (ok, files) 
							= ensureSubDirExists path fileName files
					| not ok
						-> (ok, files)
					# (ok1, files)
							= tryToCreatePortedFile fileName "icl" path files
					  (ok2, files)
							= tryToCreatePortedFile fileName "dcl" path files
					-> (ok1&&ok2, files)
	  (_, files)
	  		= fremove (RelativePath [PathDown "icl.txt"]) files
	  (_, files)
	  		= fremove (RelativePath [PathDown "dcl.txt"]) files
	= (ok, files)

				
tryToCreatePortedFile :: !String !String !Path !*Files -> (!Bool,!*Files)
tryToCreatePortedFile file_name suffix path ms_files
	# with_suffix 
			= file_name+++"."+++suffix
	# (old_module_filename, ms_files) 
			= pathToPD_String (pathAppend path [PathDown with_suffix]) ms_files
	  (ok, old, ms_files) = fopen old_module_filename FReadData ms_files
	| not ok
		= (ok, ms_files)
	# (new_module_filename, ms_files) 
			= pathToPD_String (pathAppend path [PathDown  resultFolderName,
												PathDown with_suffix]) ms_files
	  inferred_filename = suffix+++".txt"
	  (ok1, inferred, ms_files) = fopen inferred_filename FReadText ms_files
	  (ok2, new, ms_files) = fopen new_module_filename FWriteText ms_files 
	| not (ok1&&ok2)
		= (False, ms_files)
	# (old, inferred, new) = mergeFiles old inferred new
	  (ok3, ms_files) = fclose old ms_files
	  (ok4, ms_files) = fclose inferred ms_files
	  (ok5, ms_files) = fclose new ms_files
	= (ok3&&ok4&&ok5, ms_files)

findDirOfModule :: !{#Char} !SearchPaths *Files -> (!Optional Path, !*Files)
findDirOfModule fileName searchPaths files
	# filtered_locations
		=	filter (\(moduleName,pd_path) -> moduleName == fileName) searchPaths.sp_locations
	| not (isEmpty filtered_locations)
		# ((ok, path), files)
				= pd_StringToPath (snd (hd filtered_locations)) files
		| not ok
			= (No, files)
		= (Yes path, files)
	= loop searchPaths.sp_paths (fileName+++".icl") files
  where
	loop :: ![String] !String !*Files -> (!Optional Path, !*Files)
	loop [] _ files
		= (No, files)
	loop [pd_path:pd_paths] fileName files
		# ((ok, path), files)
				= pd_StringToPath pd_path files
		| not ok
			= (No, files)
		# ((dir_error, _), files)
				= getFileInfo (pathAppend path [PathDown fileName]) files
		| dir_error == NoDirError
			= (Yes path, files)
		= loop pd_paths fileName files

pathAppend (RelativePath p) x = RelativePath (p++x)
pathAppend (AbsolutePath diskname p) x = AbsolutePath diskname (p++x)

ensureSubDirExists path fileName files
	# path_result_folder = pathAppend path [PathDown resultFolderName]
	  ((err_code, _), files) = getFileInfo path_result_folder files
	  (errorCode, files) = case err_code of
		  				NoDirError	-> (NoDirError, files)
		  				_			-> createDirectory path_result_folder files
	= (errorCode==NoDirError, files)




writeExplImportsToFile :: !String ![([Declaration],a)] !{#u:DclModule} !*CheckState 
		-> (!{#u:DclModule},!.CheckState)
writeExplImportsToFile file_name si_explicit dcl_modules cs
	# (file, cs)
			= openFile file_name cs
	  (dcl_modules, file)
	  		= foldSt (write_expl_import (flatten (map fst si_explicit))) (reverse si_explicit) (dcl_modules, file)
	= (dcl_modules, closeFile file cs)
	
write_expl_import all_expl_imp_decls (declarations, _) (dcl_modules, file)
	# (declaration_strings, dcl_modules)
			= mapFilterYesSt (decl_to_opt_string all_expl_imp_decls) (reverse declarations) dcl_modules
	= (dcl_modules, fwriteNewSyntax declaration_strings file)

// only for portToNewSyntax
decl_to_opt_string all_expl_imp_decls decl=:{dcl_ident, dcl_index, dcl_kind=STE_Imported ste_kind def_mod_index}
			dcl_modules
	= imported_decl_to_opt_string all_expl_imp_decls dcl_ident dcl_index ste_kind def_mod_index
			dcl_modules
decl_to_opt_string _ {dcl_ident, dcl_kind=STE_FunctionOrMacro _} dcl_modules
	= (Yes dcl_ident.id_name, dcl_modules)
decl_to_opt_string all_expl_imp_decls decl dcl_modules
	= abort ("decl_to_opt_string failed"--->decl)
	
// only for portToNewSyntax
imported_decl_to_opt_string all_expl_imp_decls dcl_ident dcl_index STE_Constructor def_mod_index
		dcl_modules
	= (No, dcl_modules)
imported_decl_to_opt_string all_expl_imp_decls dcl_ident dcl_index STE_Member def_mod_index
		dcl_modules
	= (No, dcl_modules)
imported_decl_to_opt_string all_expl_imp_decls dcl_ident dcl_index STE_DclFunction def_mod_index
		dcl_modules
	= (Yes dcl_ident.id_name, dcl_modules)
imported_decl_to_opt_string all_expl_imp_decls dcl_ident dcl_index STE_Class def_mod_index
		dcl_modules
	= (Yes ("class "+++dcl_ident.id_name+++"(..)"), dcl_modules)
imported_decl_to_opt_string all_expl_imp_decls dcl_ident dcl_index (STE_Instance _) def_mod_index
		dcl_modules
	# ({ins_type}, dcl_modules)
			 = dcl_modules![def_mod_index].dcl_common.com_instance_defs.[dcl_index]
	= (Yes ("instance "+++dcl_ident.id_name+++" "+++
		separated " " (map type_to_string ins_type.it_types)), dcl_modules)
imported_decl_to_opt_string all_expl_imp_decls dcl_ident dcl_index STE_Type def_mod_index
		dcl_modules
	# ({td_rhs}, dcl_modules)
			 = dcl_modules![def_mod_index].dcl_common.com_type_defs.[dcl_index]
	  dcl_string
		  	= ":: "+++(case td_rhs of
						AlgType constructors
							-> dcl_ident.id_name+++constructor_bracket def_mod_index all_expl_imp_decls constructors
						RecordType _
							-> dcl_ident.id_name+++"{..}"
						_
							-> dcl_ident.id_name)
	= (Yes dcl_string, dcl_modules)

// only for portToNewSyntax
type_to_string (TA {type_name} _) = possibly_replace_predef_symbols type_name.id_name
type_to_string (TB type) = toString type
type_to_string (TV {tv_name}) = tv_name.id_name
type_to_string x = abort ("bug nr 945 in module check"--->x)

possibly_replace_predef_symbols s
	| s=="_list"
		= "[]"
	| s % (0,5) == "_tuple"
		= (toString ['(':repeatn ((toInt (s%(6, (size s) - 1))) - 1) ','])+++")"
	| s=="_array"
		= "{}"
	| s=="_!array"
		= "{!}"
	| s=="_#array"
		= "{#}"
	= s

instance toString BasicType
  where
	toString BT_Int = "Int"
	toString BT_Char = "Char"
	toString BT_Real = "Real"
	toString BT_Bool = "Bool"
	toString BT_Dynamic = "Dynamic"
	toString BT_File = "File"
	toString BT_World = "World"
	toString _ = abort "bug nr 346 in module check"

// only for portToNewSyntax
separated _ []
	= ""
separated separator [h:t]
	= foldl (\l r->l+++separator+++r) h t

constructor_bracket def_mod_index all_expl_imp_decls constructors
	# expl_imp_constructor_strings
			= [ ds_ident.id_name \\ {ds_ident} <- constructors
				| is_expl_imported_constructor def_mod_index ds_ident all_expl_imp_decls ]
	| isEmpty expl_imp_constructor_strings
		= ""
	= "("+++separated "," expl_imp_constructor_strings+++")"
	
// only for portToNewSyntax
is_expl_imported_constructor def_mod_index ds_ident []
	= False
is_expl_imported_constructor def_mod_index ds_ident [{dcl_ident, dcl_kind=STE_Imported STE_Constructor def_mod_index2}:_]
	| dcl_ident==ds_ident && def_mod_index==def_mod_index2
		= True
	// GOTO next alternative
is_expl_imported_constructor def_mod_index ds_ident [h:t]
	= is_expl_imported_constructor def_mod_index ds_ident t

fwriteNewSyntax importStrings file
	| isEmpty importStrings
		= fwrites "import @#$@@!!" file
	# with_commas = (map (\s->s+++", ") (butLast importStrings))++[last importStrings+++";"]
	  lines = split_in_lines 12 with_commas [] []
	  lines = [hd lines:[["\t":line]\\ line<-tl lines]]
	  line_strings = [ foldl (+++) " " (line++["\n"]) \\ line<-lines ]
	= fwrites (foldl (+++) "import" line_strings) file
  where
 	max_line_length = 80
	split_in_lines i [] inner_accu outer_accu
		# accu = if (isEmpty inner_accu) outer_accu [reverse inner_accu:outer_accu]
		= reverse accu
	split_in_lines i [h:t] inner_accu outer_accu
		# s = size h
		| s+i>max_line_length
			| isEmpty inner_accu
				= split_in_lines (s+i) t [h] outer_accu
			= split_in_lines (s+cTabWidth) t [h] [inner_accu:outer_accu]
		= split_in_lines (s+i) t [h:inner_accu] outer_accu
// only for portToNewSyntax

butLast [] = []
butLast [x] = []
butLast [h:t] = [h: butLast t]

// MW: fake..
openFile file_name cs
	# world							= bigBang
	  (ok, newFile, world)			= fopen file_name FWriteText world
	  cs							= forget world cs
	  cs = case ok of
			True	-> cs
			_		# cs_error = checkError "" ("can't open file \""+++file_name+++" in current directory.") cs.cs_error
					-> { cs & cs_error=cs_error }
	= (newFile, cs)

closeFile file cs
	# world				= bigBang
	  (ok, world)		= fclose file world
	= forget world cs

bigBang :: .World
bigBang = cast 1
// creates a world from scratch

forget :: !.x !.y -> .y
forget x y = y

cast :: !.a -> .b
cast a
	= code
		{
			pop_a 0
		}
// ..fake
