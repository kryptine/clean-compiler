definition module gensapl

import StdEnv,syntax,transform,backend
  
:: SaplAnnotation = SA_None | SA_Strict  
  
:: SaplExp = SaplApp SaplExp SaplExp 
		   | SaplLit SaplLiteral
           | SaplFun String 
           | SaplVar String VarInfoPtr SaplAnnotation 
           | SaplIf SaplExp SaplExp SaplExp
           | SaplSelect SaplExp [(SaplPattern,SaplExp)] (Optional SaplExp)
           | SaplLet [(SaplAnnotation,SaplExp,SaplExp)] SaplExp 
           | SaplError String 

:: SaplLiteral = LInt Int
			   | LReal Real
			   | LBool Bool
			   | LChar String
			   | LString String

:: SaplPattern = PCons String [SaplExp]
			   | PLit SaplLiteral
//			   | PDefault

// module name, type name, constructor name, ?alt?, nrargs, strictness info, nrconstructors
::SaplConsDef = SaplConsDef !String !String !String !Int !Int !StrictnessList !Int
::SaplFuncDef = SaplFuncDef !String !Int ![SaplExp] !SaplExp !FunKind
// module name, type name, list of field names and global field indeces
::SaplRecordDef = SaplRecordDef !String !String !StrictnessList [(!String, !Int)] 

instance toString SaplExp
instance toString SaplConsDef
instance toString SaplFuncDef
instance toString SaplRecordDef

renameVars 		:: SaplFuncDef -> SaplFuncDef
checkIfSelect 	:: SaplFuncDef -> [SaplFuncDef]

CleanFunctoSaplFunc  :: Int Int FunDef  [String] String  {#DclModule} [IndexRange] !*BackEnd -> *(!*BackEnd, !SaplFuncDef)



