implementation module Tonic.Util

import StdEnv
import Data.Func
import Data.Functor
import Data.List
import Data.Maybe
import Data.Map
import syntax
import Tonic.AbsSyn
import Tonic.Pretty
import Text
import iTasks.Framework.Tonic.AbsSyn

foldrArr :: (a b -> b) b (arr a) -> b | Array arr a
foldrArr f b arr = foldrArr` 0 f b arr
  where
  arrSz = size arr
  foldrArr` n f b arr
    | n < arrSz  = f (select arr n) (foldrArr` (n + 1) f b arr)
    | otherwise  = b

findInArr :: (e -> Bool) (a e) -> Maybe (Int, e) | Array a e
findInArr p arr = findInArr` 0 p arr
  where
  arrSz = size arr
  findInArr` n p arr
    | n < arrSz
      #  elem = select arr n
      =  if (p elem) (Just (n, elem)) (findInArr` (n + 1) p arr)
    | otherwise  = Nothing

concatStrings :: [String] -> .String
concatStrings l = updateS 0 l (createArray (sum [size s \\ s <- l]) ' ')
  where
    updateS :: !Int [{#Char}] *{#Char} -> *{#Char}
    updateS i [] s
      =  s
    updateS i [h : t] s
      =  updateS (i + size h) t {s & [pos] = c \\ c <-: h & pos <- [i..]}

intercalateString :: String [String] -> String
intercalateString xs xss = concatStrings (intersperse xs xss)

//import StdDebug

dropAppContexts :: App *ModuleEnv -> *(([Expression], [Expression]), *ModuleEnv)
dropAppContexts app menv
  # (mcd, menv) = reifyConsDef app.app_symb menv
  = case mcd of
      Just cd = (dropContexts cd.cons_type app.app_args, menv)
      Nothing
        # (funTy, menv) = reifySymbIdentType app.app_symb menv
        = (dropContexts funTy app.app_args, menv)

extractFunDefs :: !*{#FunDef} -> *(!{#FunDef}, !*{#FunDef})
extractFunDefs fun_defs
  # defs = {d \\ d <-: fun_defs}
  = (defs, {d \\ d <-: defs})

// TODO Get rid of this in favour of a more general reification?
reifyConsDef :: SymbIdent *ModuleEnv -> *(Maybe ConsDef, *ModuleEnv)
reifyConsDef si menv
  //= case (symbIdentModuleIdx si, symbIdentObjectIdx si) of
      //(Just mi, Just oi)
        //# (ft, menv) = reifyDclModulesIdxFunType` mi oi menv
        //= (Just ft, menv)
      //_ = (Nothing, menv)

  # (common, iclmod) = (menv.me_icl_module)!icl_common
  # dcls             = menv.me_dcl_modules
  # menv             = {menv & me_icl_module=iclmod}
  = case searchConsDefs ident common.com_cons_defs of
      Just cd = (Just cd, menv)
      _
        # cds = [cd \\ Just cd <- [searchConsDefs ident common.com_cons_defs \\ common <- [dclmod.dcl_common \\ dclmod <-: dcls]]]
        = (listToMaybe cds, menv)

  where
    searchConsDefs :: String .{# ConsDef} -> Maybe ConsDef
    searchConsDefs ident defs = listToMaybe [cd \\ cd <-: defs | cd.cons_ident.id_name == ident]

    ident = si.symb_ident.id_name

reifyFunType :: SymbIdent *ModuleEnv -> *(Maybe FunType, *ModuleEnv)
reifyFunType si menv=:{me_dcl_modules}
  = case (symbIdentModuleIdx si, symbIdentObjectIdx si) of
      (Just mi, Just oi)
        # (ft, menv) = reifyDclModulesIdxFunType` mi oi menv
        = (Just ft, menv)
      _ = (Nothing, menv)

symbIdentModuleIdx :: SymbIdent -> Maybe Index
symbIdentModuleIdx {symb_kind=SK_Function glob}              = Just glob.glob_module
symbIdentModuleIdx {symb_kind=SK_DclMacro glob}              = Just glob.glob_module
symbIdentModuleIdx {symb_kind=SK_LocalDclMacroFunction glob} = Just glob.glob_module
symbIdentModuleIdx {symb_kind=SK_OverloadedFunction glob}    = Just glob.glob_module
symbIdentModuleIdx {symb_kind=SK_Constructor glob}           = Just glob.glob_module
symbIdentModuleIdx {symb_kind=SK_NewTypeConstructor globi}   = abort "symbIdentModuleIdx: SK_NewTypeConstructor"
symbIdentModuleIdx {symb_kind=SK_Generic glob tk}            = Just glob.glob_module
symbIdentModuleIdx {symb_kind=SK_OverloadedConstructor glob} = Just glob.glob_module
symbIdentModuleIdx _                                         = Nothing

symbIdentObjectIdx :: SymbIdent -> Maybe Index
symbIdentObjectIdx {symb_kind=SK_Function glob}              = Just glob.glob_object
symbIdentObjectIdx {symb_kind=SK_IclMacro idx}               = Just idx
symbIdentObjectIdx {symb_kind=SK_LocalMacroFunction idx}     = Just idx
symbIdentObjectIdx {symb_kind=SK_DclMacro glob}              = Just glob.glob_object
symbIdentObjectIdx {symb_kind=SK_LocalDclMacroFunction glob} = Just glob.glob_object
symbIdentObjectIdx {symb_kind=SK_OverloadedFunction glob}    = Just glob.glob_object
symbIdentObjectIdx {symb_kind=SK_GeneratedFunction fip idx}  = Just idx
symbIdentObjectIdx {symb_kind=SK_Constructor glob}           = Just glob.glob_object
symbIdentObjectIdx {symb_kind=SK_NewTypeConstructor globi}   = abort "symbIdentObjectIdx: SK_NewTypeConstructor"
symbIdentObjectIdx {symb_kind=SK_Generic glob tk}            = Just glob.glob_object
symbIdentObjectIdx {symb_kind=SK_OverloadedConstructor glob} = Just glob.glob_object
symbIdentObjectIdx _                                         = Nothing

reifyFunDef :: SymbIdent *ModuleEnv -> *(Maybe FunDef, *ModuleEnv)
reifyFunDef si menv
  = case symbIdentObjectIdx si of
      Just idx
        # (fd, menv) = reifyFunDefsIdxFunDef idx menv
        = (Just fd, menv)
      _ = (Nothing, menv)

optionalToMaybe :: (Optional a) -> Maybe a
optionalToMaybe (Yes x) = Just x
optionalToMaybe No      = Nothing

symbIdentInMain :: SymbIdent *ModuleEnv -> *(Bool, *ModuleEnv)
symbIdentInMain {symb_kind=SK_Function glob}              menv = globIdxInMain glob menv
symbIdentInMain {symb_kind=SK_DclMacro glob}              menv = globIdxInMain glob menv
symbIdentInMain {symb_kind=SK_LocalDclMacroFunction glob} menv = globIdxInMain glob menv
symbIdentInMain {symb_kind=SK_OverloadedFunction glob}    menv = globIdxInMain glob menv
symbIdentInMain {symb_kind=SK_Constructor glob}           menv = globIdxInMain glob menv
symbIdentInMain {symb_kind=SK_Generic glob _}             menv = globIdxInMain glob menv
symbIdentInMain {symb_kind=SK_OverloadedConstructor glob} menv = globIdxInMain glob menv
symbIdentInMain _                                         menv = (False, menv)

globIdxInMain :: (Global Index) *ModuleEnv -> *(Bool, *ModuleEnv)
globIdxInMain glob menv
  # (main_dcl_module_n, menv) = menv!me_main_dcl_module_n
  = (glob.glob_module == main_dcl_module_n, menv)

reifySymbIdentType :: SymbIdent *ModuleEnv -> *(SymbolType, *ModuleEnv)
reifySymbIdentType {symb_kind=SK_Function glob} menv
  | glob.glob_module == menv.me_main_dcl_module_n                 = reifyFunDefsIdxSymbolType glob.glob_object menv
  | otherwise                                                     = reifyDclModulesIdxSymbolType glob menv
reifySymbIdentType {symb_kind=SK_IclMacro idx}               menv = reifyFunDefsIdxSymbolType idx menv
reifySymbIdentType {symb_kind=SK_LocalMacroFunction idx}     menv = reifyFunDefsIdxSymbolType idx menv
reifySymbIdentType {symb_kind=SK_DclMacro glob}              menv = reifyDclModulesIdxSymbolType glob menv
reifySymbIdentType {symb_kind=SK_LocalDclMacroFunction glob} menv = reifyDclModulesIdxSymbolType glob menv
reifySymbIdentType {symb_kind=SK_OverloadedFunction glob}    menv = reifyDclModulesIdxSymbolType glob menv
reifySymbIdentType {symb_kind=SK_GeneratedFunction fip idx}  menv = reifyFunDefsIdxSymbolType idx menv
reifySymbIdentType {symb_kind=SK_Constructor glob}           menv = reifyDclModulesIdxSymbolType glob menv
reifySymbIdentType {symb_kind=SK_NewTypeConstructor globi}   menv = abort "reifySymbIdentType: SK_NewTypeConstructor" // reifyDclModulesIdx` globi.gi_module globi.gi_index menv
reifySymbIdentType {symb_kind=SK_Generic glob tk}            menv = reifyDclModulesIdxSymbolType glob menv
reifySymbIdentType {symb_kind=SK_OverloadedConstructor glob} menv = reifyDclModulesIdxSymbolType glob menv
reifySymbIdentType si menv = abort "reifySymbIdentType: unsupported"

reifyDclModulesIdxSymbolType :: (Global Index) *ModuleEnv -> *(SymbolType, *ModuleEnv)
reifyDclModulesIdxSymbolType {glob_module,glob_object} menv = reifyDclModulesIdxSymbolType` glob_module glob_object menv

reifyDclModulesIdxSymbolType` :: Index Index *ModuleEnv -> *(SymbolType, *ModuleEnv)
reifyDclModulesIdxSymbolType` glob_module glob_object menv
  # (funTy, menv) = reifyDclModulesIdxFunType` glob_module glob_object menv
  = (funTy.ft_type, menv)

reifyDclModulesIdxFunType :: (Global Index) *ModuleEnv -> *(FunType, *ModuleEnv)
reifyDclModulesIdxFunType {glob_module,glob_object} menv = reifyDclModulesIdxFunType` glob_module glob_object menv

reifyDclModulesIdxFunType` :: Index Index *ModuleEnv -> *(FunType, *ModuleEnv)
reifyDclModulesIdxFunType` glob_module glob_object menv
  # (dcl, dcls) = (menv.me_dcl_modules)![glob_module]
  # funTy       = dcl.dcl_functions.[glob_object]
  = (funTy, {menv & me_dcl_modules = dcls})

  //# (common, iclmod) = (menv.me_icl_module)!icl_common
  //# dcls             = menv.me_dcl_modules
  //# menv             = {menv & me_icl_module=iclmod}
  //= case searchConsDefs ident common.com_cons_defs of
      //Just cd = (Just cd, menv)
      //_
        //# cds = [cd \\ Just cd <- [searchConsDefs ident common.com_cons_defs \\ common <- [dclmod.dcl_common \\ dclmod <-: dcls]]]
        //= (listToMaybe cds, menv)

  //where
    //searchConsDefs :: String .{# ConsDef} -> Maybe ConsDef
    //searchConsDefs ident defs = listToMaybe [cd \\ cd <-: defs | cd.cons_ident.id_name == ident]

    //ident = si.symb_ident.id_name
reifyIclModuleGlobConsDef :: (Global Index) *ModuleEnv -> *(ConsDef, *ModuleEnv)
reifyIclModuleGlobConsDef {glob_object} menv = reifyIclModuleIdxConsDef glob_object menv

reifyIclModuleIdxConsDef :: Index *ModuleEnv -> *(ConsDef, *ModuleEnv)
reifyIclModuleIdxConsDef glob_object menv
  # (icl, menv) = menv!me_icl_module
  # cd          = icl.icl_common.com_cons_defs.[glob_object]
  = (cd, menv)

reifyFunDefsIdxSymbolType :: Index *ModuleEnv -> *(SymbolType, *ModuleEnv)
reifyFunDefsIdxSymbolType idx menv
  # (fd, fds) = (menv.me_fun_defs)![idx]
  = case fd.fun_type of
      Yes st -> (st, {menv & me_fun_defs = fds})
      _      -> abort "reifyFunDefsIdxSymbolType: No fun type"

reifyFunDefsIdxFunDef :: Index *ModuleEnv -> *(FunDef, *ModuleEnv)
reifyFunDefsIdxFunDef idx menv
  # (fd, fds) = (menv.me_fun_defs)![idx]
  = (fd, {menv & me_fun_defs = fds})

//import StdDebug

foldUArr :: (Int a v:(w:b, u:(arr a)) -> v:(w:b, u:(arr a))) v:(w:b, u:(arr a))
         -> v:(w:b, u:(arr a)) | Array arr a, [v <= u, v <= w]
foldUArr f (b, arr)
  # (sz, arr) = usize arr
  = foldUArr` sz 0 b arr
  where foldUArr` sz idx b arr
          | idx < sz
              # (elem, arr) = uselect arr idx
              # (res, arr) = foldUArr` sz (idx + 1) b arr
              = f idx elem (res, arr)
          | otherwise = (b, arr)

fdArrToMap :: .{#FunDef} -> Map String FunDef
fdArrToMap fds = fromList [(d.fun_ident.id_name, d) \\ d <-: fds]

isCons :: String -> Bool
isCons str = str == "_Cons"

isNil :: String -> Bool
isNil str = str == "_Nil"

appIsList :: App -> Bool
appIsList app = isCons ident || isNil ident
  where ident = app.app_symb.symb_ident.id_name

exprIsListConstr :: Expression -> Bool
exprIsListConstr (App app) = appIsList app
exprIsListConstr _         = False

exprIsListCompr :: Expression -> Bool
exprIsListCompr (App app)  = appIsListComp app
exprIsListCompr _          = False

appIsListComp :: App -> Bool
appIsListComp app = isListCompr app.app_symb.symb_ident.id_name

isListCompr :: String -> Bool
isListCompr str = startsWith "c;" str // TODO: Verify

safeHead :: [a] -> Maybe a
safeHead []    = Nothing
safeHead [x:_] = Just x

fromOptional :: a (Optional a) -> a
fromOptional x  No       = x
fromOptional _  (Yes x)  = x

optional :: b (a -> b) (Optional a) -> b
optional b  _  No       = b
optional _  f  (Yes x)  = f x

appFunName :: App -> String
appFunName app = app.app_symb.symb_ident.id_name

freeVarName :: FreeVar -> String
freeVarName fv = fv.fv_ident.id_name

dropContexts :: SymbolType [a] -> ([a], [a])
dropContexts st xs
  # args    = keep st.st_arity xs
  # numargs = length args
  = splitAt (length xs - numargs) xs

numContexts :: SymbolType -> Int
numContexts st = length st.st_context

funIsTask :: FunDef -> Bool
funIsTask fd =
  case (fd.fun_type, fd.fun_kind) of
    (Yes st, FK_Function _)  -> symTyIsTask st
    _                        -> False

identIsLambda :: Ident -> Bool
identIsLambda ident
  | size fnm > 0  = fnm.[0] == '\\'
  | otherwise     = False
  where fnm = ident.id_name

exprIsLambda :: Expression -> Bool
exprIsLambda (Var bv)  = identIsLambda bv.var_ident
exprIsLambda (App app) = identIsLambda app.app_symb.symb_ident
exprIsLambda _         = False

ppType (TA tsi ats) = "TA"
ppType (TAS tsi ats sl) = "TAS"
ppType (at1 --> at2) = "-->"
ppType (TArrow) = "TArrow"
ppType (TArrow1	at) = "TArrow1"
ppType (cv :@: ats) = ":@:"
ppType (TB bt) = "TB"
ppType (TFA ats t) = "TFA"
ppType (GTV tv) = "GTV"
ppType (TV tv) = "TV"
ppType (TFAC atvs t tcs) = "TFAC"
ppType (TempV tvi) = "TempV"
ppType (TQV tv) = "TQV"
ppType (TempQV tvi) = "TempQV"
ppType (TempQDV tvi) = "TempQDV"
ppType (TLifted tv) = "TypeVar"
ppType (TQualifiedIdent i s ats) = "TQualifiedIdent"
ppType (TGenericFunctionInDictionary gds tk gi) = "TGenericFunctionInDictionary"
ppType (TLiftedSubst t) = "TLiftedSubst"
ppType TE = "TE"

symTyIsTask :: SymbolType -> Bool
symTyIsTask st =
  case st.st_result.at_type of
    TA   tsi _     -> symTyIsTask` tsi
    TAS  tsi _  _  -> symTyIsTask` tsi
    _              -> False
  where symTyIsTask` tsi = tsi.type_ident.id_name == "Task"

symbIdentIsTask :: SymbIdent *ModuleEnv -> *(Bool, *ModuleEnv)
symbIdentIsTask si menv
  # (st, menv) = reifySymbIdentType si menv
  = (symTyIsTask st, menv)

isInfix :: SymbIdent *ModuleEnv -> *(Bool, *ModuleEnv)
isInfix si menv
  # (mfd, menv) = reifyFunDef si menv
  = case mfd of
      Just fd = (prioIsInfix fd.fun_priority, menv)
      Nothing
        # (mft, menv) = reifyFunType si menv
        = case mft of
            Just ft  = (prioIsInfix ft.ft_priority, menv)
            _
              # (mcd, menv) = reifyConsDef si menv
              = case mcd of
                  Just cd -> (prioIsInfix cd.cons_priority, menv)
                  Nothing -> abort ("Failed to determine fixity for " +++ si.symb_ident.id_name)

prioIsInfix :: Priority -> Bool
prioIsInfix prio =
  case prio of
    Prio _ _  -> True
    _         -> False

getFunName :: FunDef -> String
getFunName fd = fd.fun_ident.id_name

getFunArgs :: FunDef -> [FreeVar]
getFunArgs {fun_body = TransformedBody tb} = tb.tb_args
getFunArgs _                               = abort "getFunArgs: need a TransformedBody"

getFunRhs :: FunDef -> Expression
getFunRhs {fun_body = TransformedBody tb} = tb.tb_rhs
getFunRhs _                               = abort "getFunRhs: need a TransformedBody"

updateWithAnnot :: Int (Maybe Expression) *ModuleEnv -> *ModuleEnv
updateWithAnnot fidx (Just e) menv
  # fun_defs = menv.me_fun_defs
  # fun_defs = updateFunRhs fidx fun_defs e
  = { menv & me_fun_defs = fun_defs}
updateWithAnnot _ _ menv = menv

updateFunRhs :: Int !*{#FunDef} Expression -> !*{#FunDef}
updateFunRhs n fun_defs e
  # (fd, fun_defs) = fun_defs![n]
  # tb = case fd.fun_body of
           TransformedBody fb -> { fb & tb_rhs = e }
           _                  -> abort "updateFunRhs: need a TransformedBody"
  # fd = { fd & fun_body = TransformedBody tb }
  = { fun_defs & [n] = fd}

emptyEdge :: GEdge
emptyEdge = {GEdge | edge_pattern = Nothing }

mkEdge :: String -> GEdge
mkEdge str = {GEdge | edge_pattern = Just str }

getLetBinds :: Let -> [LetBind]
getLetBinds lt = lt.let_strict_binds ++ lt.let_lazy_binds

mkGLetBinds :: Let *ModuleEnv -> *([(String, String)], *ModuleEnv)
mkGLetBinds lt menv
  = foldrSt f (getLetBinds lt) ([], menv)
  where f bnd (xs, menv)
          # (pprhs, menv) = ppExpression bnd.lb_src menv
          = ([(bnd.lb_dst.fv_ident.id_name, ppCompact pprhs):xs], menv)

foldrSt :: !(.a -> .(.st -> .st)) ![.a] !.st -> .st
foldrSt op l st = foldr_st l
  where
    foldr_st []     = st
    foldr_st [a:as] = op a (foldr_st as)


