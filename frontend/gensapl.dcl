definition module gensapl

import StdEnv,syntax,transform  
  
:: SaplAnnotation = SA_None | SA_Strict  
  
:: SaplExp = SaplApp SaplExp SaplExp | SaplInt Int |SaplReal Real | SaplBool Bool |
             SaplString String | SaplFun String | AnFunc [SaplExp] SaplExp | SaplVar String VarInfoPtr SaplAnnotation | 
             SaplChar String |
             SaplSelect SaplExp [(SaplMatchExp,[SaplExp],SaplExp)] [SaplExp] | 
             SaplLet [(SaplAnnotation,SaplExp,SaplExp)] SaplExp | 
             SaplError String | SaplABCCode [String]

::SaplConsDef = SaplConsDef String String String Int Int Int
::SaplFuncDef = SaplFuncDef String Int [SaplExp] SaplExp FunKind
// module name, type name, list of field names and global field indeces
::SaplRecordDef = SaplRecordDef String String [(String, Int)] 
::SaplMatchExp = MatchCons String | MatchInt Int | MatchChar String | MatchBool Bool | MatchReal Real | MatchString String | MatchSingleIf

instance toString SaplExp
instance toString SaplConsDef
instance toString SaplFuncDef
instance toString SaplRecordDef

convertSelects :: [SaplFuncDef] [SaplConsDef] -> [SaplFuncDef]
renameVars :: SaplFuncDef -> SaplFuncDef
checkIfSelect :: SaplFuncDef -> [SaplFuncDef]

CleanFunctoSaplFunc  :: Int Int FunDef  [String] String  {#DclModule} [IndexRange] -> SaplFuncDef

