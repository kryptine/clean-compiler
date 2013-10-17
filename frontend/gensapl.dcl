definition module gensapl

import StdEnv,syntax,transform,backend
  
:: SaplAnnotation = SA_None | SA_Strict  
  
:: SaplExp = SaplApp SaplExp SaplExp 
		   | SaplInt Int 
		   | SaplReal Real 
		   | SaplBool Bool
           | SaplChar String 		   
           | SaplString String 
           | SaplFun String 
           | AnFunc [SaplExp] SaplExp 
           | SaplVar String VarInfoPtr SaplAnnotation 
           | SaplSelect SaplExp [(SaplMatchExp,[SaplExp],SaplExp)] [SaplExp] 
           | SaplLet [(SaplAnnotation,SaplExp,SaplExp)] SaplExp 
           | SaplError String 
           | SaplABCCode [String]

::SaplMatchExp = MatchCons String 
			   | MatchInt Int 
			   | MatchChar String 
			   | MatchBool Bool 
			   | MatchReal Real 
			   | MatchString String 
			   | MatchSingleIf

// module name,  type name, constructor name, ?alt?, nrargs, nrconstructors
::SaplConsDef = SaplConsDef String String String Int Int Int
::SaplFuncDef = SaplFuncDef String Int [SaplExp] SaplExp FunKind
// module name, type name, list of field names and global field indeces
::SaplRecordDef = SaplRecordDef String String [(String, Int)] 

instance toString SaplExp
instance toString SaplConsDef
instance toString SaplFuncDef
instance toString SaplRecordDef

convertSelects :: [SaplFuncDef] [SaplConsDef] -> [SaplFuncDef]
renameVars :: SaplFuncDef -> SaplFuncDef
checkIfSelect :: SaplFuncDef -> [SaplFuncDef]

CleanFunctoSaplFunc  :: Int Int FunDef  [String] String  {#DclModule} [IndexRange] !*BackEnd -> *(!*BackEnd, !SaplFuncDef)

