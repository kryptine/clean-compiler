implementation module gensapl

// Generation of Sapl definition from Clean definition
// JMJ: May 2007
// L�szl� Domoszlai: 2011 - 

import StdEnv, StdMaybe, syntax, transform, backend, backendinterface, containers

instance toString SaplConsDef  
where 
	toString (SaplConsDef mod t name alt nrargs strictness nralt) 
		= makePrintableName (mod +++ "." +++ name) 
			+++ makeString [(if (arg_is_strict (n-1) strictness) " !a" " a") +++ toString n \\ n <- [1..nrargs]]

instance toString SaplFuncDef  
where 
	toString (SaplFuncDef name nrargs args body kind) 
		= makePrintableName name +++ makeArgs args +++ toString kind +++ toString body

instance toString SaplRecordDef
where 
	toString (SaplRecordDef mod recname strictness fields) = makeGetSets mod recname strictness fields

instance toString FunKind
where 
	toString FK_Macro = " = "
	toString FK_Caf = " =: "
	toString x = " = "

instance == SaplConsDef
where 
	== (SaplConsDef _ _ name1 _ _ _ _) (SaplConsDef _ _ name2 _ _ _ _) = name1 == name2
 
// only used for comparing vars
instance == SaplExp
where 
	== var1=:(SaplVar _ _ _ _) var2=:(SaplVar _ _ _ _) = cmpvar var1 var2
    == _ _                                     		   = False

instance == SaplAnnotation
where
	== SA_None   SA_None   = True
    == SA_Strict SA_Strict = True
    == _         _         = False

instance toString SaplAnnotation
where
	toString SA_None = ""
	toString SA_Strict = "!"

makeString :: [String] -> String
makeString [] = ""
makeString [a:as] = a +++ makeString as 

fmap f (Yes a) = Yes (f a)
fmap _ No = No

instance toString SaplLiteral
where
	toString (LInt i) 		= toString i
	toString (LReal r) 		= toString r
	toString (LBool b) 		= toString b
	toString (LChar c) 		= c
	toString (LString s) 	= s

instance toString SaplPattern
where
	toString (PCons name args) = makePrintableName name +++ makeString [" "+++arg\\ SaplVar arg _ _ _<- args]
	toString (PLit lit) = toString lit

instance toString SaplExp
where 
	toString e = exp2string False e
	where
		exp2string b (SaplApp left right)   = bracks b (exp2string False left +++ " " +++ exp2string True right)
		exp2string b (SaplLit l)            = toString l
		exp2string b (SaplFun f)            = makePrintableName f
		exp2string b (SaplVar n vi a mbt)   = makePrintableName n
		exp2string b e=:(SaplSelect _ _ _)  = bracks b (selectToString e)
		exp2string b (SaplIf c l r)   		= bracks b ("if " +++ exp2string True c +++ " " +++ exp2string True l +++ " " +++ exp2string True r)		
		exp2string b (SaplLet ves body)     = "" +++ bracks b ("let " +++ multiLet ves body) 
		exp2string b (SaplError m)          = bracks b ("error \"" +++ m +++ "\"")

		bracks b e | b = "(" +++ e +++ ")" 
    		           = e
        
        selectToString :: !SaplExp -> String       
		selectToString (SaplSelect e ps def) = "select " +++ exp2string True e +++ " " +++ dopats ps +++ dodef def
		where dopats [] = ""
		      dopats [(p,exp):pats] = "(" +++ toString p +++ " -> " +++ toString exp +++ ") " +++ dopats pats
		                                                 		                                                 
		      dodef No = ""
		      dodef (Yes def) = "(_ -> " +++ toString def +++ ")"
        
		multiLet :: ![(SaplAnnotation,SaplExp,SaplExp)] !SaplExp -> String
		multiLet []                          body  =  toString body // empty let
		multiLet [(annotation, arg, e)]      body  =  toString annotation +++ toString arg +++ " = " +++ toString e +++ " in " +++ toString body
		multiLet [(annotation, arg, e): ves] body  =  toString annotation +++ toString arg +++ " = " +++ toString e +++ ", " +++ multiLet ves body

		makeCodeString :: ![String] -> String
		makeCodeString []     = ""
		makeCodeString [c:cs] = c +++ ";" +++ makeCodeString cs 

makeArgs :: [SaplExp] -> String
makeArgs []                         = ""
makeArgs [SaplVar arg _ a mbt]      = " " +++ makePrintableAnnotatedName (toString arg) a
makeArgs [SaplVar arg _ a mbt:args] = " " +++ makePrintableAnnotatedName (toString arg) a +++ makeArgs args 

counterMap :: (a Int -> b) [a] Int -> [b]
counterMap f [] c = []
counterMap f [x:xs] c = [f x c : counterMap f xs (c+1)]

// Converting a single Clean function to a Sapl function (case is only pre-transformed)
CleanFunctoSaplFunc  :: Int Int Int FunDef String {#DclModule} [IndexRange] !*BackEnd -> *(!*BackEnd, !SaplFuncDef)
CleanFunctoSaplFunc main_dcl_module_n modindex funindex 
                    {fun_ident,fun_body=TransformedBody {tb_args,tb_rhs},fun_info={fi_free_vars,fi_local_vars,fi_def_level,fi_calls},fun_type,fun_kind} 
                    mymod dcl_mods icl_function_indices backEnd

		// Add derived strictness from backEnd
        # (backEnd, strictnessList, tupleReturn) = case fun_type of
				No = (backEnd, NotStrict, No)
        		Yes ft   
        			# (_, ft, backEnd) = addStrictnessFromBackEnd funindex fun_ident.id_name backEnd ft
					// If the return type is a strict tuple, a special name is generated for it,
					// indicating which argument is strict. Later the references to the orignal
					// Tuple constructor must be replaced by the special one (see changeTuple).
					// The necessity of the change is indicated by the Optional (from, to) value.
					# pf = case ft of 
								{st_result = {at_type = TAS ti _ (Strict x)}} 
									| startsWith "_Tuple" ti.type_ident.id_name
										= Yes (ti.type_ident.id_name, ti.type_ident.id_name+++"!"+++toString x)
										= No
								= No
        			= (backEnd, ft.st_args_strictness, pf)
	
        # funDef = SaplFuncDef (mymod +++ "." +++ makeFuncName main_dcl_module_n (getName fun_ident) main_dcl_module_n funindex dcl_mods icl_function_indices mymod)
                   		       (length tb_args) (counterMap (getFreeFuncArgName strictnessList) tb_args 0)  
                       		   (cleanExpToSaplExp tupleReturn tb_rhs) fun_kind
        
        = (backEnd, funDef)

where
	cleanExpToSaplExp tupleReturn (Var ident) = getBoundVarName ident
			
	cleanExpToSaplExp tupleReturn (App {app_symb, app_args, app_info_ptr})
	        = case app_symb.symb_kind of
	            SK_Generic _ kind
	                -> printApplicGen app_symb kind app_args  //  does not apply?
	            _   -> multiApp [SaplFun (changeTuple tupleReturn app_symb) : map (cleanExpToSaplExp No) app_args]

	cleanExpToSaplExp tupleReturn (f_exp @ a_exp) = multiApp [cleanExpToSaplExp tupleReturn f_exp: map (cleanExpToSaplExp No) a_exp]

	cleanExpToSaplExp tupleReturn (Let {let_info_ptr, let_strict_binds, let_lazy_binds, let_expr}) 
			= SaplLet (map letToSapl bindings) (cleanExpToSaplExp tupleReturn let_expr)
	where
		bindings = zip2 (repeat SA_Strict) let_strict_binds ++ 
				   zip2 (repeat SA_None) (reverse let_lazy_binds)
		letToSapl (annotation, binding) = (annotation, getFreeVarName binding.lb_dst, cleanExpToSaplExp No binding.lb_src)
				
	cleanExpToSaplExp tupleReturn (Case {case_expr,case_guards,case_default,case_explicit}) 
			= genSaplCase case_expr case_guards case_default case_explicit
	where
		// Converting Case definitions
		genSaplCase case_exp (AlgebraicPatterns gindex pats) def explicit = SaplSelect (cleanExpToSaplExp No case_exp) (map getCasePat pats) (handleDef def explicit) 
		genSaplCase case_exp (OverloadedListPatterns listtype exp pats) def explicit = SaplSelect (cleanExpToSaplExp No case_exp) (map getCasePat pats) (handleDef def explicit)
		genSaplCase case_exp (BasicPatterns gindex pats) def explicit = SaplSelect (cleanExpToSaplExp No case_exp) (map getConstPat pats) (handleDef def explicit)
		genSaplCase case_exp  _ _ _ = SaplError "no matching rule found" 

		handleDef (Yes def) _ 	= Yes (cleanExpToSaplExp tupleReturn def)
		handleDef _ True 		= Yes (SaplFun "nomatch")
		handleDef _ _ 			= No		
		
		getConstPat pat = (PLit (basicValueToSapl pat.bp_value), cleanExpToSaplExp tupleReturn pat.bp_expr) 			
		getCasePat pat = (PCons (printConsName pat.ap_symbol.glob_object.ds_ident (getmodnr pat.ap_symbol))
					 		(map getFreeVarName pat.ap_vars),
					  cleanExpToSaplExp tupleReturn pat.ap_expr)	
			
	cleanExpToSaplExp tupleReturn (BasicExpr basic_value)                                   
			= SaplLit (basicValueToSapl basic_value)
	cleanExpToSaplExp tupleReturn (FreeVar var)                                             
			= getFreeVarName var
	cleanExpToSaplExp tupleReturn (Conditional {if_cond,if_then,if_else=No})                
			= SaplSelect (cleanExpToSaplExp No if_cond) [(PLit (LBool True), cleanExpToSaplExp tupleReturn if_then)] No
	cleanExpToSaplExp tupleReturn (Conditional {if_cond,if_then,if_else=Yes else_exp})      
			= SaplIf (cleanExpToSaplExp No if_cond) (cleanExpToSaplExp tupleReturn if_then) (cleanExpToSaplExp tupleReturn else_exp)
	cleanExpToSaplExp tupleReturn (Selection _ expr selectors)                              
			= makeSelector selectors (cleanExpToSaplExp No expr)  
	cleanExpToSaplExp tupleReturn (Update expr1 selections expr2)                           
			= makeArrayUpdate (cleanExpToSaplExp No expr1) selections (cleanExpToSaplExp No expr2)  
	cleanExpToSaplExp tupleReturn (RecordUpdate cons_symbol expression expressions)         
			= makeRecordUpdate (cleanExpToSaplExp No expression) expressions 
	cleanExpToSaplExp tupleReturn (TupleSelect cons field_nr expr)                          
			= SaplApp (SaplFun ("_predefined.tupsels" +++ toString cons.ds_arity +++ "v" +++ toString field_nr)) (cleanExpToSaplExp No expr)
	cleanExpToSaplExp tupleReturn (MatchExpr cons expr)  
			| cons.glob_object.ds_arity == 1 
				= SaplApp (SaplFun ("_predefined.tupsels1v0"))(cleanExpToSaplExp No expr) 
	            = cleanExpToSaplExp tupleReturn expr
	            
	cleanExpToSaplExp _ EE                                                        = SaplError "no EE"  
	cleanExpToSaplExp _ (DynamicExpr {dyn_expr,dyn_type_code})                    = SaplError "no DynamicExpr"   
	cleanExpToSaplExp _ (TypeCodeExpression type_code)                            = SaplError "no TypeCodeExpression" 
	
	cleanExpToSaplExp _ (ABCCodeExpr code_sequence do_inline)                     = SaplError "no AnyCodeExpr" //SaplABCCode code_sequence
	cleanExpToSaplExp _ (AnyCodeExpr input output code_sequence)                  = SaplError "no AnyCodeExpr" 
	
	cleanExpToSaplExp _ (FailExpr _)                                              = SaplError "no FailExpr" 
	
	cleanExpToSaplExp _ (ClassVariable info_ptr)                                  = SaplError "ClassVariable may not occur"
	cleanExpToSaplExp _ (NoBind _)                                                = SaplError "noBind may not occur" 
	cleanExpToSaplExp _ (Constant symb _ _)                                       = SaplError "Constant may not occur"
	cleanExpToSaplExp _ expr                                                      = SaplError "no cleanToSapl for this case"  

	// See the comment above
	changeTuple (Yes (fromi, toi)) {symb_ident={id_name}} | fromi == id_name
		= toi
	changeTuple _ app_symb = getSymbName app_symb 	

	printApplicGen app_symb kind args   = multiApp [SaplFun (getSymbName app_symb  +++ "_generic"):map (cleanExpToSaplExp No) args]	
	                                                
	// Array and Record updates
	makeArrayUpdate expr1 sels expr2  = SaplApp (makeSelector sels expr1) expr2
	
	/* 
	TODO: DictionarySelection is possibly broken. The following example (without the type) generates
	wrong code:
	
	//g :: {!e} -> [e]
	g {[0]=x} = [x]

	a :: {Int}
	a = {2}

	Start :: [Int]
	Start = g a
	*/
	
	makeSelector  [] e = e
	makeSelector  [selector:sels] e  = makeSelector  sels (mksel selector e)
	where mksel (RecordSelection globsel ind)     exp = SaplApp (SaplFun (dcl_mods.[globsel.glob_module].dcl_name.id_name +++ ".get_" +++ toString globsel.glob_object.ds_ident +++ "_" +++ toString globsel.glob_object.ds_index)) e 
	      mksel (ArraySelection globsel _ e)      exp = multiApp [SaplFun (dcl_mods.[globsel.glob_module].dcl_name.id_name +++ "." +++ toString globsel.glob_object.ds_ident +++ "_" +++ toString globsel.glob_object.ds_index),exp, cleanExpToSaplExp No e]  
	      mksel (DictionarySelection var sels _ e)exp = multiApp [makeSelector sels (getBoundVarName var),exp,cleanExpToSaplExp No e]
	
	// backendconvert.convertSelector (BESelect)
	makeRecordUpdate expression [         ]                      = expression
	makeRecordUpdate expression [upbind:us] | not(isNoBind value)= makeRecordUpdate (multiApp [SaplFun (field_mod +++ ".set_" +++ field +++ "_" +++ index),expression,cleanExpToSaplExp No value]) us
	                                                             = makeRecordUpdate expression us
	where field               = toString upbind.bind_dst.glob_object.fs_ident
	      index               = toString upbind.bind_dst.glob_object.fs_index
	      field_mod           = dcl_mods.[upbind.bind_dst.glob_module].dcl_name.id_name
	      value               = upbind.bind_src
	      isNoBind (NoBind _) = True
	      isNoBind _          = False

	// It uses the stricness bitmap to extract annotation
	getFreeFuncArgName :: StrictnessList FreeVar Int -> SaplExp 
	getFreeFuncArgName strictness {fv_ident,fv_info_ptr,fv_count} c | arg_is_strict c strictness
                       = SaplVar (toString fv_ident) fv_info_ptr SA_Strict Nothing
	getFreeFuncArgName strictness {fv_ident,fv_info_ptr,fv_count} c
                       = SaplVar (toString fv_ident) fv_info_ptr SA_None Nothing
                              
	// FreeVar e.g. the name of a let binding                                  
	getFreeVarName :: FreeVar -> SaplExp 
	getFreeVarName {fv_ident,fv_info_ptr,fv_count} = SaplVar (toString fv_ident) fv_info_ptr SA_None Nothing
	                                                                                    
	ptrToString ptr = toString (ptrToInt ptr)

	getBoundVarName {var_ident,var_info_ptr} = SaplVar (toString var_ident) var_info_ptr SA_None Nothing
	
	// Function names at declaratio (on the left)
	getName :: Ident -> String
	getName {id_name} = id_name
	
	getSymbName :: SymbIdent -> String
	getSymbName symb=:{symb_kind = SK_Function symb_index} = printOverloaded symb.symb_ident symb_index.glob_object symb_index.glob_module
	getSymbName symb=:{symb_kind = SK_LocalMacroFunction symb_index} = printGeneratedFunction symb.symb_ident symb_index
	getSymbName symb=:{symb_kind = SK_GeneratedFunction _ symb_index} = printGeneratedFunction symb.symb_ident symb_index
	getSymbName symb=:{symb_kind = SK_LocalDclMacroFunction symb_index} = printOverloaded symb.symb_ident symb_index.glob_object symb_index.glob_module
	getSymbName symb=:{symb_kind = SK_OverloadedFunction symb_index} = printOverloaded symb.symb_ident symb_index.glob_object symb_index.glob_module
	getSymbName symb=:{symb_kind = SK_Constructor symb_index} = printConsName symb.symb_ident symb_index.glob_module
	getSymbName symb             = getName symb.symb_ident
	
	// For example: test._f3_3
	printGeneratedFunction symbol symb_index  = decsymbol (toString symbol)
	where decsymbol s                         = mymod +++ "."  +++ makeFuncName main_dcl_module_n s main_dcl_module_n symb_index dcl_mods icl_function_indices mymod
	
	// Normal case
	printOverloaded symbol symb_index modnr   = decsymbol (toString symbol)
//	where decsymbol s | startsWith "c;" s     = mymod +++ "._lc_"  +++ toString symb_index 
//	                  | startsWith "g_c;" s   = mymod +++ "._lc_"  +++ toString symb_index 
//	                                          = makemod modnr +++ makeFuncName main_dcl_module_n 0 s modnr symb_index dcl_mods icl_function_indices mymod
	where decsymbol s = makemod modnr +++ makeFuncName main_dcl_module_n s modnr symb_index dcl_mods icl_function_indices mymod

	printConsName symbol modnr
		| startsWith "_Tuple" symbstr
			= symbstr
			= makemod modnr +++ symbstr
	where
		symbstr = toString symbol
	
	getmodnr sym = sym.glob_module
	makemod n = dcl_mods.[n].dcl_name.id_name +++ "."
		
fromYes (Yes x) = x

basicValueToSapl :: BasicValue -> SaplLiteral
basicValueToSapl (BVI int)      = LInt (toInt int)
basicValueToSapl (BVInt int)    = LInt int
basicValueToSapl (BVC char)     = LChar (toSAPLString '\'' char)
basicValueToSapl (BVB bool)     = LBool bool
basicValueToSapl (BVR real)     = LReal (toReal real)
basicValueToSapl (BVS str)      = LString (toSAPLString '"' str)

cmpvar  (SaplVar n1 ip1 _ _) (SaplVar n2 ip2 _ _) | isNilPtr ip1 || isNilPtr ip2 = n1 == n2	                                                                           = ip1 == ip2

getVarPrefix varname  =toString (takeWhile (\a -> a <> 'I' && a <> ';') lname)
where lname = [c\\c <-: varname]      
	
renameVars :: SaplFuncDef -> SaplFuncDef
renameVars (SaplFuncDef name nrargs args body kind) 
	= SaplFuncDef name nrargs (map snd renargs) (doVarRename 1 renargs body) kind
where
	renargs = renamevars args 0

	renamevars vars 0 = [(SaplVar v ip a mbt, SaplVar (getVarPrefix v +++ "_" +++ toString k) ip a mbt) \\ (SaplVar v ip a mbt,k) <- zip(vars,[0..])]
	renamevars vars n = [(SaplVar v ip a mbt, SaplVar (getVarPrefix v +++ "_" +++ toString n +++ "_" +++ toString k) ip a mbt) \\ (SaplVar v ip a mbt,k) <- zip(vars,[0..])]

	doVarRename level rens (SaplApp left right)		= SaplApp (doVarRename level rens left) (doVarRename level rens right)
	doVarRename level rens var=:(SaplVar _ _ _ _)   = findvar var rens
	doVarRename level rens (SaplLet ves body)		= doletrename level rens [] ves body
	doVarRename level rens (SaplSelect e cases def) = doselectrename level rens e cases def
	doVarRename level rens (SaplIf c l r) 			= SaplIf (doVarRename level rens c) (doVarRename level rens l) (doVarRename level rens r)
	doVarRename level rens e                    	= e

	doselectrename level rens e cases def = SaplSelect e` (map renamecase cases) def`
	where
		e` = doVarRename level rens e
		def` = fmap (doVarRename level rens) def
	
		renamecase (PCons mexpr args, body) 
			= (PCons mexpr (map snd args`), doVarRename (level+1) (args`++rens) body)
		where
			args` = renamevars args level

		renamecase (p, body) 
			= (p, doVarRename (level+1) rens body)
	
	doletrename level rens _ bindings body = removeVarBodyLets (SaplLet renlets renbody)	
	where
		// extract annotations from let bindings
		annotations   = map fst3 bindings
		// apply variable renaming to vars of let bindings, bodies of let bindings and body of let
		renletvars    = renamevars (map snd3 bindings) level
		renletbodies  = [doVarRename (level+1) (renletvars++rens) b \\ (_, _ ,b) <- bindings]
		renbody       = doVarRename (level+1) (renletvars++rens) body
		// zip them again
		renlets 	  = [(a,rv,b) \\ a <- annotations & (v, rv) <- renletvars & b <- renletbodies]

	// Sapl does not allow let's with only a var on the right hand side
	removeVarBodyLets (SaplLet bindings body) 
		# (SaplLet bindings body) = varrename varbindings (SaplLet nonvarbindings body)
		| bindings == [] = body 
    	                 = SaplLet bindings body
	where
		// filter bindings by their body
		varbindings    = [(var, SaplVar n ip a mbt) \\ (_, var, SaplVar n ip a mbt) <- bindings]
		nonvarbindings = filter (noVar o thd3) bindings

		noVar (SaplVar _ _ _ _) = False
		noVar _                 = True

	// Simple var renaming
	varrename rens (SaplApp left right)  = SaplApp (varrename rens left) (varrename rens right)
	varrename rens (SaplVar n ip a mbt)  = findvar (SaplVar n ip a mbt) (rens++[(SaplVar n ip a mbt,SaplVar n ip a mbt)])
	varrename rens (SaplLet ves body)    = SaplLet [(a,v,varrename rens e)\\ (a,v,e) <- ves] (varrename rens body)
	varrename rens (SaplIf c l r)  		 = SaplIf (varrename rens c) (varrename rens l) (varrename rens r)	
	varrename rens (SaplSelect expr patterns mbDef) 
			= SaplSelect (varrename rens expr) [(p,varrename rens e)\\ (p,e) <- patterns] (fmap (varrename rens) mbDef)	
	varrename rens e                     = e

findvar (SaplVar n ip a mbt) rens = hd ([renvar\\ (var,renvar) <- rens| cmpvar (SaplVar n ip a mbt) var]++[SaplVar ("error, " +++ n +++ " not found") nilPtr SA_None Nothing])

makeFuncName main_dcl_module_n name mod_index func_index dcl_mods ranges mymod
              | name.[0] == '\\' = "anon_" +++ toString func_index
              //| startsWith "c;" name = "_lc_" +++ toString func_index
              //| startsWith "g_" name = "_lc_" +++ toString func_index
              // used for dynamic desription, there is only one per type, no need for numbering
              | startsWith "TD;" name = name
                                     = genFunctionExtension main_dcl_module_n name mod_index func_index dcl_mods ranges mymod
                                 
multiApp [a]       = a
multiApp [a:b:as]  = multiApp [(SaplApp a b): as]        

startsWith :: String String -> Bool
startsWith s1 s2 = s1 == s2%(0,size s1-1)
                                 
// Record access defintions
makeGetSets mod recname strictness fields 
	= ":: " +++ recname_pr +++ " = {" +++ makeconsargs fields +++ "}\n" 
			+++ mGets 1 (length fields) fields 
			+++ mSets 1 (length fields) fields
where
	mGets _ _ [] = ""
	mGets k nf [(field,idx):fields] 
		= makePrintableName (mod +++ ".get_" +++ field +++ "_" +++ toString idx) +++ 
		  " rec = select rec (" +++ recname_pr +++ makeargs nf +++ " -> a" +++ toString k +++ ")\n" +++ mGets (k+1) nf fields
		  
	mSets _ _ [] = ""
	mSets k nf [(field,idx):fields] 
		= makePrintableName (mod +++ ".set_" +++ field +++ "_" +++ toString idx) +++ 
		  " rec " +++ annotate idx "val" +++ " = select rec (" +++ recname_pr +++ " " +++ makeargs nf +++ " -> " +++ 
          recname_pr +++ makerepargs k nf +++ ")\n"  +++ mSets (k+1) nf fields

	recname_pr = makePrintableName (mod +++ "." +++ recname)

	makeconsargs [     ]  			= ""
	makeconsargs [(field,idx)]      = annotate idx (makePrintableName (mod +++ "." +++ field))
	makeconsargs [(field,idx):args] = annotate idx (makePrintableName (mod +++ "." +++ field)) +++ ", " +++ makeconsargs args 
 
 	annotate idx name | arg_is_strict idx strictness
 		= "!" +++ name
 		= name
 	
	makeargs 0 = ""
	makeargs n = makeargs (n-1) +++ " a" +++ toString n 
 
	makerepargs _ 0 = ""
	makerepargs k n | k == n = makerepargs k (n-1) +++ " val"
     	                     = makerepargs k (n-1) +++ " a" +++ toString n

makePrintableAnnotatedName :: String SaplAnnotation -> String
makePrintableAnnotatedName f SA_None = makePrintableName f
makePrintableAnnotatedName f SA_Strict = "!" +++ makePrintableName f

makePrintableName f | ss f = "<{" +++ f +++ "}>"
                           = f
                           
where ss f = or [is_ss c \\ c <-: f]
      is_ss c = not (isAlphanum c || c == '_' || c == '.')          

// Replace non toplevel if & select by a function call
checkIfSelect :: SaplFuncDef -> [SaplFuncDef]
checkIfSelect (SaplFuncDef fname nrargs vs body kind) 
	# (newbody,_,newdefs) = rntls vs 0 body
	= [SaplFuncDef fname nrargs vs newbody kind:newdefs]
where 
	rntls vs nr (SaplLet ves body)   
	# (newbody,newnr,newdefs) = rntls (map snd3 ves++vs) nr body                               
	= (SaplLet ves newbody,newnr,newdefs)

	rntls vs nr (SaplSelect expr patterns defpattern)
	# (newexpr,newnr,newdefs1) = maylift vs nr expr // in pattern expression lifting may necessary

	# (newdefpattern,newnr,newdefs2) = case defpattern of
					No = (No, newnr, [])
					Yes dp = let (a,b,c) = rntls vs newnr dp in (Yes a,b,c)

	# (newpatterns,newnr,newdefs3) = foldl walkPattern ([],newnr,[]) patterns
	= (SaplSelect newexpr (reverse newpatterns) newdefpattern,newnr,newdefs1++newdefs2++newdefs3)
	where
		walkPattern (ps, nr, defs) (p=:(PCons pat args), body) 
			= let (np,newnr,newdefs) = rntls (args++vs) nr body in ([(p, np):ps], newnr, defs++newdefs)
		walkPattern (ps, nr, defs) (p, body) 
			= let (np,newnr,newdefs) = rntls vs nr body in ([(p, np):ps], newnr, defs++newdefs)

	rntls vs nr (SaplIf c l r)
	# (newc,newnr,newdefsc) = maylift vs nr c // in condition lifting may necessary
	# (newl,newnr,newdefsl) = rntls vs newnr l
	# (newr,newnr,newdefsr) = rntls vs newnr r	
	= (SaplIf newc newl newr,newnr,newdefsc++newdefsl++newdefsr)

	rntls vs nr (SaplApp l r)
	# (newl,newnr,newdefsl) = rntls vs nr l
	# (newr,newnr,newdefsr) = rntls vs newnr r	
	= (SaplApp newl newr,newnr,newdefsl++newdefsr)

	rntls vs nr exp = (exp,nr,[])

	// These expressions must be lifted only	
	maylift vs nr e=:(SaplIf _ _ _) = lift vs nr e	
	maylift vs nr e=:(SaplSelect _ _ _) = lift vs nr e	
	maylift vs nr e = rntls vs nr e
	
	// lift the given expression into a new top level function
	lift vs nr e
	# (newe,newnr,newdefse) = rntls vs nr e
	= (multiApp [SaplFun (callname newnr):vs],newnr+1,newdefse++
				[SaplFuncDef (callname newnr) (length vs) vs newe FK_Unknown])
	where
		callname newnr = (fname+++"_select" +++ toString newnr)    
	
// Which functions must be extended with a number 
genFunctionExtension :: !Int !String !Int !Int {#DclModule} [IndexRange] !String -> String
genFunctionExtension main_dcl_module_n name mod_index func_index dcl_mods ranges mymod
| mod_index == main_dcl_module_n = genFunctionExtForMain name func_index ranges
| otherwise                      = genFunctionExtForDCL name mod_index func_index dcl_mods
where
	genFunctionExtForDCL name mod_index func_index dcl_mods = gfn dcl_mods.[mod_index]
	where
	 	gfn {dcl_name, dcl_common, dcl_functions, dcl_type_funs, dcl_instances}
			=	functionName name func_index [{ir_from = 0, ir_to = dcl_instances.ir_from}, dcl_type_funs]                                                                           
	
	genFunctionExtForMain name func_index ranges = functionName name func_index ranges                                                                           
	
	functionName  name func_index ranges 
		| index_in_ranges func_index ranges
		=	name
		=	(name +++ "_" +++ toString func_index)
	
	index_in_ranges index [{ir_from, ir_to}:ranges] = (index>=ir_from && index < ir_to) || index_in_ranges index ranges
	index_in_ranges index [] = False

// Change String literal representation from ABC to SAPL (JavaScript):
//
// For ABC see scanner.icl/ScanChar:
//
// Non printable characters are converted to one of them:
// \n, \r, \f, \t, \", \' and \nnn (octal)

cb :: Int
cb =: fromChar '\b'
cv :: Int
cv =: fromChar '\v' 

toSAPLString :: Char String -> String
toSAPLString qc str = toString [qc: flatten (fromABCString (tl (init (fromString str))))]
where
	fromABCString :: [Char] -> [[Char]]
	fromABCString [] = [[qc]]
	fromABCString ['\\':chars] = let (c,chars2) = scanBSChar chars in [c: fromABCString chars2]
	fromABCString [c   :chars] = [[c]    : fromABCString chars] 

	toHex i
		| i == 0  = ['\\0']
		| i == 7  = ['\\a']		
		| i == cb = ['\\b']
		| i == cv = ['\\v']	

	toHex i = ['\\x'] ++ ['0' \\ a <- [1..2-length letters]] ++ reverse (toHex` i)
	where
		letters = reverse (toHex` i)
	
		toHex` 0 = []
		toHex` i = [hex.[i bitand 15]:toHex` (i >> 4)]  
		where
			hex = "0123456789ABCDEF" 

	scanBSChar ['\\':chars] = (['\\\\'], chars)
	// These are handled by the +1 case at the end
	//scanBSChar ['n' :chars] = (['\\n'] , chars)
	//scanBSChar ['r' :chars] = (['\\r'] , chars)
	//scanBSChar ['f' :chars] = (['\\f'] , chars)
	//scanBSChar ['t' :chars] = (['\\t'] , chars)
	//scanBSChar ['"' :chars] = (['\\"'] , chars)
	//scanBSChar ['\'':chars] = (['\\\''], chars)
	scanBSChar [f:s:t:chars] | isOctDigit f && isOctDigit s && isOctDigit t
			= (toHex (digitToInt f << 6 + digitToInt s << 3 + digitToInt t), chars)
	scanBSChar [c: chars] = (['\\',c], chars)

                                    
                     
