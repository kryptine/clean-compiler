implementation module Tonic.Util

import StdEnv
import Data.Func
import Data.Functor
import Data.List
import Data.Maybe
import Data.Map
import syntax, predef
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

dropAppContexts :: App *ModuleEnv -> *(([Expression], [Expression]), *ModuleEnv)
dropAppContexts app menv
  # (mcd, menv) = reifyConsDef app.app_symb menv
  = case mcd of
      Just cd = (dropContexts cd.cons_type app.app_args, menv)
      Nothing
        # (mFunTy, menv) = reifySymbIdentSymbolType app.app_symb menv
        = case mFunTy of
            Just funTy -> (dropContexts funTy app.app_args, menv)
            _          -> abort "dropAppContexts: no function type"

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
      (Just mi, Just oi) -> reifyDclModulesIdxFunType` mi oi menv
      _                  -> (Nothing, menv)

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
      Just idx -> reifyFunDefsIdxFunDef idx menv
      _        -> (Nothing, menv)

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

idxIsMain :: Index *ModuleEnv -> *(Bool, *ModuleEnv)
idxIsMain idx menv
  # (main_dcl_module_n, menv) = menv!me_main_dcl_module_n
  = (idx == main_dcl_module_n, menv)

reifySymbIdentSymbolType :: SymbIdent *ModuleEnv -> *(Maybe SymbolType, *ModuleEnv)
reifySymbIdentSymbolType {symb_kind=SK_Function glob} menv
  | glob.glob_module == menv.me_main_dcl_module_n                       = reifyFunDefsIdxSymbolType glob.glob_object menv
  | otherwise                                                           = reifyDclModulesIdxSymbolType glob menv
reifySymbIdentSymbolType {symb_kind=SK_IclMacro idx}               menv = reifyFunDefsIdxSymbolType idx menv
reifySymbIdentSymbolType {symb_kind=SK_LocalMacroFunction idx}     menv = reifyFunDefsIdxSymbolType idx menv
reifySymbIdentSymbolType {symb_kind=SK_DclMacro glob}              menv = reifyDclModulesIdxSymbolType glob menv
reifySymbIdentSymbolType {symb_kind=SK_LocalDclMacroFunction glob} menv = reifyDclModulesIdxSymbolType glob menv
reifySymbIdentSymbolType {symb_kind=SK_OverloadedFunction glob}    menv = reifyDclModulesIdxSymbolType glob menv
reifySymbIdentSymbolType {symb_kind=SK_GeneratedFunction fip idx}  menv = reifyFunDefsIdxSymbolType idx menv
reifySymbIdentSymbolType {symb_kind=SK_Constructor glob}           menv = reifyDclModulesIdxSymbolType glob menv
reifySymbIdentSymbolType {symb_kind=SK_NewTypeConstructor globi}   menv = abort "reifySymbIdentType: SK_NewTypeConstructor" // reifyDclModulesIdx` globi.gi_module globi.gi_index menv
reifySymbIdentSymbolType {symb_kind=SK_Generic glob tk}            menv = reifyDclModulesIdxSymbolType glob menv
reifySymbIdentSymbolType {symb_kind=SK_OverloadedConstructor glob} menv = reifyDclModulesIdxSymbolType glob menv
reifySymbIdentSymbolType si menv = abort "reifySymbIdentSymbolType: unsupported"

reifyDclModulesIdxSymbolType :: (Global Index) *ModuleEnv -> *(Maybe SymbolType, *ModuleEnv)
reifyDclModulesIdxSymbolType {glob_module,glob_object} menv = reifyDclModulesIdxSymbolType` glob_module glob_object menv

reifyDclModulesIdxSymbolType` :: Index Index *ModuleEnv -> *(Maybe SymbolType, *ModuleEnv)
reifyDclModulesIdxSymbolType` glob_module glob_object menv
  # (mFunTy, menv) = reifyDclModulesIdxFunType` glob_module glob_object menv
  = case mFunTy of
      Just funTy -> (Just funTy.ft_type, menv)
      _          -> (Nothing, menv)

reifyDclModulesIdxFunType :: (Global Index) *ModuleEnv -> *(Maybe FunType, *ModuleEnv)
reifyDclModulesIdxFunType {glob_module,glob_object} menv = reifyDclModulesIdxFunType` glob_module glob_object menv

reifyDclModulesIdxFunType` :: Index Index *ModuleEnv -> *(Maybe FunType, *ModuleEnv)
reifyDclModulesIdxFunType` glob_module glob_object menv
  | glob_module == menv.me_main_dcl_module_n = (Nothing, menv)
  | otherwise
    # (mdcl, dcls) = muselect menv.me_dcl_modules glob_module
    # menv         = {menv & me_dcl_modules = dcls}
    = case mdcl of
        Just dcl -> (mselect dcl.dcl_functions glob_object, menv)
        _        -> (Nothing, menv)

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

arrHasIdx :: (a e) Int -> Bool | Array a e
arrHasIdx arr idx = idx < size arr

muselect :: !u:(a e) !Int -> *(Maybe e, !u:(a e)) | Array a e
muselect arr idx
  | arrHasIdx arr idx
    # (sz, arr)   = usize arr
    # (elem, arr) = arr![idx]
    = (Just elem, arr)
  | otherwise     = (Nothing, arr)

mselect :: (a e) !Int -> Maybe e | Array a e
mselect arr idx
  | arrHasIdx arr idx = Just arr.[idx]
  | otherwise         = Nothing

reifyIclModuleGlobConsDef :: (Global Index) *ModuleEnv -> *(Maybe ConsDef, *ModuleEnv)
reifyIclModuleGlobConsDef {glob_object} menv = reifyIclModuleIdxConsDef glob_object menv

reifyIclModuleIdxConsDef :: Index *ModuleEnv -> *(Maybe ConsDef, *ModuleEnv)
reifyIclModuleIdxConsDef glob_object menv
  # (icl, menv) = menv!me_icl_module
  = (mselect icl.icl_common.com_cons_defs glob_object, menv)

reifyFunDefsIdxSymbolType :: Index *ModuleEnv -> *(Maybe SymbolType, *ModuleEnv)
reifyFunDefsIdxSymbolType idx menv
  # (mfd, fds) = muselect menv.me_fun_defs idx
  # menv = {menv & me_fun_defs = fds}
  = case mfd of
      Just fd -> case fd.fun_type of
                   Yes st -> (Just st, menv)
                   _      -> (Nothing, menv)
      _       -> (Nothing, menv)

reifyFunDefsIdxFunDef :: Index *ModuleEnv -> *(Maybe FunDef, *ModuleEnv)
reifyFunDefsIdxFunDef idx menv
  # (mfd, fds) = muselect menv.me_fun_defs idx
  = (mfd, {menv & me_fun_defs = fds})

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

reifyArgsAndDef :: SymbIdent *ModuleEnv -> *(([FreeVar], FunDef), *ModuleEnv)
reifyArgsAndDef app_symb menv
  # (mfd, menv)      = reifyFunDef app_symb menv
  # (rSym, menv)     = ppSymbIdent app_symb menv
  # (mFArgTy, menv)  = reifySymbIdentSymbolType app_symb menv
  # rhsfd            = fromMaybe (abort $ "reifyArgs failed to find function definition for " +++ ppCompact rSym) mfd
  # args             = getFunArgs rhsfd
  # rhsTy            = fromMaybe (abort "reifyArgs failed to reify SymbolType") mFArgTy
  = ((snd (dropContexts rhsTy args), rhsfd), menv)

fdArrToMap :: .{#FunDef} -> Map String FunDef
fdArrToMap fds = fromList [(d.fun_ident.id_name, d) \\ d <-: fds]

isCons :: String -> Bool
isCons str = str == PD_ConsSymbol_String

isNil :: String -> Bool
isNil str = str == PD_NilSymbol_String

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

funTy :: FunDef -> Type
funTy {fun_type=Yes {st_result={at_type}}} = at_type
funTy {fun_ident={id_name}} = abort ("Tonic.Util.funTy: type of " +++ id_name +++ " is unknown.")

functorContent :: Type -> Maybe Type
functorContent (TA _ [{at_type}:_])    = Just at_type
functorContent (TAS _ [{at_type}:_] _) = Just at_type
functorContent _                       = Nothing

funArgTys :: FunDef -> [Type]
funArgTys {fun_type=Yes {st_args}} = map (\x -> x.at_type) st_args
funArgTys {fun_ident={id_name}} = abort ("Tonic.Util.funArgTys argument types of " +++ id_name +++ " are unknown.")


identIsLambda :: Ident -> Bool
identIsLambda ident
  | size fnm > 0  = fnm.[0] == '\\'
  | otherwise     = False
  where fnm = ident.id_name

exprIsLambda :: Expression -> Bool
exprIsLambda (Var bv)  = identIsLambda bv.var_ident
exprIsLambda (App app) = identIsLambda app.app_symb.symb_ident
exprIsLambda _         = False

ppAType :: AType -> String
ppAType {at_type} = ppType at_type

ppTypeSymbIdent :: TypeSymbIdent -> String
ppTypeSymbIdent tsi = tsi.type_ident.id_name


intersperse` :: String (a -> String) [a] -> String
intersperse` _ _ [] = ""
intersperse` _ pp [x] = pp x
intersperse` sep pp [x:xs] = pp x +++ sep +++ intersperse` sep pp xs

ppType :: Type -> String
ppType (TA tsi ats)      = ppTypeSymbIdent tsi +++ (intersperse` " " ppAType ats)
ppType (TAS tsi ats sl)  = ppTypeSymbIdent tsi +++ (intersperse` " " ppAType ats)
ppType (at1 --> at2)     = ppAType at1 +++ " --> " +++ ppAType at2
ppType (TArrow)          = "->"
ppType (TArrow1	at)      = "TArrow1"
ppType (cv :@: ats)      = ":@:"
ppType (TB bt)           = "TB"
ppType (TFA ats t)       = "TFA"
ppType (GTV tv)          = tv.tv_ident.id_name
ppType (TV tv)           = tv.tv_ident.id_name
ppType (TFAC atvs t tcs) = "TFAC"
ppType (TempV tvi)       = "TempV"
ppType (TQV tv)          = "TQV"
ppType (TempQV tvi)      = "TempQV"
ppType (TempQDV tvi)     = "TempQDV"
ppType (TLifted tv)      = "TypeVar"
ppType (TQualifiedIdent i s ats) = "TQualifiedIdent"
ppType (TGenericFunctionInDictionary gds tk gi) = "TGenericFunctionInDictionary"
ppType (TLiftedSubst t) = "TLiftedSubst"
ppType TE = "TE"

symTyIsTask :: SymbolType -> Bool
symTyIsTask st = atypeIsTask st.st_result

atypeIsTask :: AType -> Bool
atypeIsTask aty =
  case aty.at_type of
    TA   tsi _     -> symTyIsTask` tsi
    TAS  tsi _  _  -> symTyIsTask` tsi
    _              -> False
  where symTyIsTask` tsi = tsi.type_ident.id_name == "Task"

symbIdentIsTask :: SymbIdent *ModuleEnv -> *(Bool, *ModuleEnv)
symbIdentIsTask si menv
  # (mst, menv) = reifySymbIdentSymbolType si menv
  = case mst of
      Just st -> (symTyIsTask st, menv)
      _       -> abort "symbIdentIsTask: failed to reify smybIdent"

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

getFunArgs :: FunDef -> [FreeVar]
getFunArgs {fun_body = TransformedBody tb} = tb.tb_args
getFunArgs _                               = abort "getFunArgs: need a TransformedBody"

getFunRhs :: FunDef -> Expression
getFunRhs {fun_body = TransformedBody tb} = tb.tb_rhs
getFunRhs _                               = abort "getFunRhs: need a TransformedBody"

updateWithAnnot :: SymbIdent Expression *ModuleEnv -> *ModuleEnv
updateWithAnnot si expr menv =
  case (symbIdentModuleIdx si, symbIdentObjectIdx si) of
    (Just midx, Just oidx) -> if (midx == menv.me_main_dcl_module_n)
                                (doUpdate oidx)
                                menv
    _                      -> menv
  where
  doUpdate oidx
    # fds = menv.me_fun_defs
    # fds = updateFunRhs oidx fds expr
    = {menv & me_fun_defs = fds}

updateFunRhs :: Index !*{#FunDef} Expression -> !*{#FunDef}
updateFunRhs idx fun_defs e
  # (mfd, fun_defs) = muselect fun_defs idx
  = case mfd of
      Just fd
        # tb = case fd.fun_body of
                 TransformedBody fb -> { fb & tb_rhs = e }
                 _                  -> abort "updateFunRhs: need a TransformedBody"
        # fd = { fd & fun_body = TransformedBody tb }
        = { fun_defs & [idx] = fd}
      _ = fun_defs

//emptyEdge :: GEdge
//emptyEdge = {GEdge | edge_pattern = Nothing }

//mkEdge :: String -> GEdge
//mkEdge str = {GEdge | edge_pattern = Just str }

getLetBinds :: Let -> [LetBind]
getLetBinds lt = lt.let_strict_binds ++ lt.let_lazy_binds

mkGLetBinds :: Let *ModuleEnv -> *([(String, PPOr TExpr)], *ModuleEnv)
mkGLetBinds lt menv
  = foldrSt f (getLetBinds lt) ([], menv)
  where f bnd (xs, menv)
          # (pprhs, menv) = ppExpression bnd.lb_src menv
          = ([(bnd.lb_dst.fv_ident.id_name, PP (ppCompact pprhs)):xs], menv)

foldrSt :: !(.a -> .(.st -> .st)) ![.a] !.st -> .st
foldrSt op l st = foldr_st l
  where
    foldr_st []     = st
    foldr_st [a:as] = op a (foldr_st as)

addInhId :: InhExpression Int -> InhExpression
addInhId inh n = {inh & inh_ids = inh.inh_ids ++ [n]}

predefIsUndefined :: PredefinedSymbol -> Bool
predefIsUndefined pds = pds.pds_def == NoIndex || pds.pds_module == NoIndex

symbIdentArity :: SymbIdent *ModuleEnv -> *(Maybe Int, *ModuleEnv)
symbIdentArity si menv
  # (mft, menv) = reifyFunType si menv
  = case mft of
      Just ft
        = (Just ft.ft_arity, menv)
      _
        # (mfd, menv) = reifyFunDef si menv
        = case mfd of
            Just fd -> (Just fd.fun_arity, menv)
            _       -> (Nothing, menv)

isPartialApp :: App *ModuleEnv -> *(Bool, *ModuleEnv)
isPartialApp app menv
  # ((_, args), menv) = dropAppContexts app menv
  # (marity, menv)    = symbIdentArity app.app_symb menv
  = case marity of
      Just arity -> (length args < arity, menv)
      _          -> (True, menv) // True: better safe than sorry

exprIsTask :: Expression *ModuleEnv -> *(Bool, *ModuleEnv)
exprIsTask (App app) menv = symbIdentIsTask app.app_symb menv
exprIsTask _         menv = (False, menv) // False: better safe than sorry

mkStr :: String -> Expression
mkStr str = BasicExpr (BVS ("\"" +++ str +++ "\""))

mkInt :: Int -> Expression
mkInt i   = BasicExpr (BVInt i)

appPredefinedSymbol :: Int [Expression] ((Global Index) -> SymbKind) *PredefinedSymbols -> *(App, *PredefinedSymbols)
appPredefinedSymbol pds_idx args mkKind pdss
  # (pds, pdss) = pdss![pds_idx]
  # ident       = predefined_idents.[pds_idx]
  = (
    { App
    | app_symb     = mkPredefSymbIdent ident pds mkKind
    , app_args     = args
    , app_info_ptr = nilPtr
    }, pdss)

mkPredefSymbIdent :: Ident PredefinedSymbol ((Global Index) -> SymbKind) -> SymbIdent
mkPredefSymbIdent ident pds mkKind
  = { SymbIdent
    | symb_ident = ident
    , symb_kind  = mkKind
                     { Global
                     | glob_object = pds.pds_def
                     , glob_module = pds.pds_module
                     }
    }

class ToStatic a where
  toStatic :: a *PredefinedSymbols -> *(Expression, *PredefinedSymbols)

class FromStatic a where
  fromStatic :: Expression -> a

instance ToStatic [Expression] where
  toStatic xs pdss = listToListExpr xs pdss

instance FromStatic [Expression] where
  fromStatic expr = listExprToList expr

instance ToStatic (Expression, Expression) where
  toStatic tup pdss = tupleToTupleExpr tup pdss

listExprToList :: Expression -> [Expression]
listExprToList (App app) =
  case app.app_symb.symb_ident.id_name of
    PD_ConsSymbol_String ->
      case app.app_args of
        [head:tail:_] -> [head : listExprToList tail]
        _             -> abort "listExprToList should not happen"
    PD_NilSymbol_String  -> []
    _       -> abort "listExprToList: App is not a list"
listExprToList _ = []

listToListExpr :: [Expression] *PredefinedSymbols -> *(Expression, *PredefinedSymbols)
listToListExpr [] pdss
  # (app, pdss) = appPredefinedSymbol PD_NilSymbol [] SK_Constructor pdss
  = (App app, pdss)
listToListExpr [x:xs] pdss
  # (texpr, pdss)  = listToListExpr xs pdss
  # (cons, pdss)   = appPredefinedSymbol PD_ConsSymbol [x,texpr] SK_Constructor pdss
  = (App cons, pdss)

tupleToTupleExpr :: (Expression, Expression) *PredefinedSymbols -> *(Expression, *PredefinedSymbols)
tupleToTupleExpr (e1, e2) pdss
  # (tup, pdss) = appPredefinedSymbol PD_Arity2TupleSymbol [e1, e2] SK_Constructor pdss
  = (App tup, pdss)

freeVarToVar :: FreeVar -> BoundVar
freeVarToVar {fv_ident, fv_info_ptr}
  = { var_ident = fv_ident,  var_info_ptr = fv_info_ptr, var_expr_ptr = nilPtr}
