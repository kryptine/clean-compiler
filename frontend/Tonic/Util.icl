implementation module Tonic.Util

import StdEnv
from Data.Func import $
import Data.Functor
import Data.List
import Data.Maybe
from Data.Map import :: Map
import qualified Data.Map as DM
import syntax, predef, typesupport, overloading, unitype, generics1
import Tonic.AbsSyn
import Tonic.Pretty
import Text
import iTasks._Framework.Tonic.AbsSyn

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

copyFunDefs :: !*{#FunDef} -> *(!*{#FunDef}, !*{#FunDef})
copyFunDefs fun_defs
  # defs = {d \\ d <-: fun_defs}
  # l = mkCopy defs
  # r = mkCopy defs
  = (l, r)
  where
  mkCopy :: !{#FunDef} -> *{#FunDef}
  mkCopy defs = {d \\ d <-: defs}

// TODO Get rid of this in favour of a more general reification?
reifyConsDef :: SymbIdent *ModuleEnv -> *(Maybe ConsDef, *ModuleEnv)
reifyConsDef si menv
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
      (Just mi, oi)
        = reifyDclModulesIdxFunType` mi oi menv
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

symbIdentObjectIdx :: SymbIdent -> Index
symbIdentObjectIdx {symb_kind=SK_Function glob}              = glob.glob_object
symbIdentObjectIdx {symb_kind=SK_IclMacro idx}               = idx
symbIdentObjectIdx {symb_kind=SK_LocalMacroFunction idx}     = idx
symbIdentObjectIdx {symb_kind=SK_DclMacro glob}              = glob.glob_object
symbIdentObjectIdx {symb_kind=SK_LocalDclMacroFunction glob} = glob.glob_object
symbIdentObjectIdx {symb_kind=SK_OverloadedFunction glob}    = glob.glob_object
symbIdentObjectIdx {symb_kind=SK_GeneratedFunction fip idx}  = idx
symbIdentObjectIdx {symb_kind=SK_Constructor glob}           = glob.glob_object
symbIdentObjectIdx {symb_kind=SK_Generic glob tk}            = glob.glob_object
symbIdentObjectIdx {symb_kind=SK_OverloadedConstructor glob} = glob.glob_object

reifyFunDef :: SymbIdent *ModuleEnv -> *(Maybe FunDef, *ModuleEnv)
reifyFunDef si menv = reifyFunDefsIdxFunDef (symbIdentObjectIdx si) menv

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

reifyFunDefsIdxPriority :: Index *ModuleEnv -> *(Maybe Priority, *ModuleEnv)
reifyFunDefsIdxPriority idx menv
  # (mfd, fds) = muselect menv.me_fun_defs_cpy idx
  # menv = {menv & me_fun_defs_cpy = fds}
  = case mfd of
      Just fd -> (Just fd.fun_priority, menv)
      _       -> (Nothing, menv)

reifyDclModulesIdxPriority :: (Global Index) *ModuleEnv -> *(Maybe Priority, *ModuleEnv)
reifyDclModulesIdxPriority {glob_module,glob_object} menv = reifyDclModulesIdxPriority` glob_module glob_object menv

reifyDclModulesIdxPriority` :: Index Index *ModuleEnv -> *(Maybe Priority, *ModuleEnv)
reifyDclModulesIdxPriority` glob_module glob_object menv
  # (mFunTy, menv) = reifyDclModulesIdxFunType` glob_module glob_object menv
  = case mFunTy of
      Just funTy -> (Just funTy.ft_priority, menv)
      _          -> (Nothing, menv)

reifySymbIdentPriority :: SymbIdent *ModuleEnv -> *(Maybe Priority, *ModuleEnv)
reifySymbIdentPriority {symb_ident, symb_kind=SK_Function glob} menv
  | glob.glob_module == menv.me_main_dcl_module_n = reifyFunDefsIdxPriority glob.glob_object menv
  | otherwise                                     = reifyDclModulesIdxPriority glob menv
reifySymbIdentPriority {symb_ident, symb_kind=SK_IclMacro idx}           menv = reifyFunDefsIdxPriority idx menv
reifySymbIdentPriority {symb_ident, symb_kind=SK_LocalMacroFunction idx} menv = reifyFunDefsIdxPriority idx menv
reifySymbIdentPriority {symb_ident, symb_kind=SK_DclMacro glob} menv
  | glob.glob_module == menv.me_main_dcl_module_n = reifyFunDefsIdxPriority glob.glob_object menv
  | otherwise                                     = reifyDclModulesIdxPriority glob menv
reifySymbIdentPriority {symb_ident, symb_kind=SK_LocalDclMacroFunction glob} menv
  | glob.glob_module == menv.me_main_dcl_module_n = reifyFunDefsIdxPriority glob.glob_object menv
  | otherwise                                     = reifyDclModulesIdxPriority glob menv
reifySymbIdentPriority {symb_ident, symb_kind=SK_OverloadedFunction {glob_module, glob_object} } menv
  | glob_module == menv.me_main_dcl_module_n
      # (icl, menv) = menv!me_icl_module
      # md          = icl.icl_common.com_member_defs.[glob_object]
      = (Just md.me_priority, menv)
  | otherwise
      # (dcls, menv) = menv!me_dcl_modules
      # md           = dcls.[glob_module].dcl_common.com_member_defs.[glob_object]
      = (Just md.me_priority, menv)
reifySymbIdentPriority {symb_ident, symb_kind=SK_GeneratedFunction fip idx} menv = reifyFunDefsIdxPriority idx menv
reifySymbIdentPriority {symb_ident, symb_kind=SK_Constructor {glob_module, glob_object}} menv
  | glob_module == menv.me_main_dcl_module_n
      # (icl, menv) = menv!me_icl_module
      # md          = icl.icl_common.com_cons_defs.[glob_object]
      = (Just md.cons_priority, menv)
  | otherwise
      # (dcls, menv) = menv!me_dcl_modules
      # md           = dcls.[glob_module].dcl_common.com_cons_defs.[glob_object]
      = (Just md.cons_priority, menv)
reifySymbIdentPriority {symb_ident, symb_kind=SK_NewTypeConstructor globi} menv = abort "reifySymbIdentType: SK_NewTypeConstructor" // reifyDclModulesIdx` globi.gi_module globi.gi_index menv
reifySymbIdentPriority {symb_ident, symb_kind=SK_Generic {glob_module, glob_object} _} menv
  = (Nothing, menv)
reifySymbIdentPriority {symb_ident, symb_kind=SK_OverloadedConstructor glob} menv
  | glob.glob_module == menv.me_main_dcl_module_n = reifyFunDefsIdxPriority glob.glob_object menv
  | otherwise                                     = reifyDclModulesIdxPriority glob menv
reifySymbIdentPriority si menv = abort "reifySymbIdentPriority: unsupported"

reifySymbIdentSymbolType :: SymbIdent *ModuleEnv -> *(Maybe SymbolType, *ModuleEnv)
reifySymbIdentSymbolType {symb_ident, symb_kind=SK_Function glob} menv
  | glob.glob_module == menv.me_main_dcl_module_n = reifyFunDefsIdxSymbolType symb_ident glob.glob_object menv
  | otherwise                                     = reifyDclModulesIdxSymbolType glob menv
reifySymbIdentSymbolType {symb_ident, symb_kind=SK_IclMacro idx}           menv = reifyFunDefsIdxSymbolType symb_ident idx menv
reifySymbIdentSymbolType {symb_ident, symb_kind=SK_LocalMacroFunction idx} menv = reifyFunDefsIdxSymbolType symb_ident idx menv
reifySymbIdentSymbolType {symb_ident, symb_kind=SK_DclMacro glob} menv
  | glob.glob_module == menv.me_main_dcl_module_n = reifyFunDefsIdxSymbolType symb_ident glob.glob_object menv
  | otherwise                                     = reifyDclModulesIdxSymbolType glob menv
reifySymbIdentSymbolType {symb_ident, symb_kind=SK_LocalDclMacroFunction glob} menv
  | glob.glob_module == menv.me_main_dcl_module_n = reifyFunDefsIdxSymbolType symb_ident glob.glob_object menv
  | otherwise                                     = reifyDclModulesIdxSymbolType glob menv
reifySymbIdentSymbolType {symb_ident, symb_kind=SK_OverloadedFunction {glob_module, glob_object} } menv
  | glob_module == menv.me_main_dcl_module_n
      # (icl, menv) = menv!me_icl_module
      # md          = icl.icl_common.com_member_defs.[glob_object]
      = (Just md.me_type, menv)
  | otherwise
      # (dcls, menv) = menv!me_dcl_modules
      # md           = dcls.[glob_module].dcl_common.com_member_defs.[glob_object]
      = (Just md.me_type, menv)
reifySymbIdentSymbolType {symb_ident, symb_kind=SK_GeneratedFunction fip idx} menv = reifyFunDefsIdxSymbolType symb_ident idx menv
reifySymbIdentSymbolType {symb_ident, symb_kind=SK_Constructor {glob_module, glob_object}} menv
  | glob_module == menv.me_main_dcl_module_n
      # (icl, menv) = menv!me_icl_module
      # md          = icl.icl_common.com_cons_defs.[glob_object]
      = (Just md.cons_type, menv)
  | otherwise
      # (dcls, menv) = menv!me_dcl_modules
      # md           = dcls.[glob_module].dcl_common.com_cons_defs.[glob_object]
      = (Just md.cons_type, menv)
reifySymbIdentSymbolType {symb_ident, symb_kind=SK_NewTypeConstructor globi} menv = abort "reifySymbIdentType: SK_NewTypeConstructor" // reifyDclModulesIdx` globi.gi_module globi.gi_index menv
reifySymbIdentSymbolType {symb_ident, symb_kind=SK_Generic {glob_module, glob_object} _} menv
  | glob_module == menv.me_main_dcl_module_n
      # (icl, menv) = menv!me_icl_module
      # md          = icl.icl_common.com_generic_defs.[glob_object]
      = (Just md.gen_type, menv)
  | otherwise
      # (dcls, menv) = menv!me_dcl_modules
      # md           = dcls.[glob_module].dcl_common.com_generic_defs.[glob_object]
      = (Just md.gen_type, menv)
reifySymbIdentSymbolType {symb_ident, symb_kind=SK_OverloadedConstructor glob} menv
  | glob.glob_module == menv.me_main_dcl_module_n = reifyFunDefsIdxSymbolType symb_ident glob.glob_object menv
  | otherwise                                     = reifyDclModulesIdxSymbolType glob menv
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

reifyDclModule :: SymbIdent *ModuleEnv -> *(Maybe DclModule, *ModuleEnv)
reifyDclModule si menv =
  case symbIdentModuleIdx si of
    Just mi -> reifyDclModule` mi menv
    _       -> (Nothing, menv)

reifyDclModule` :: Index *ModuleEnv -> *(Maybe DclModule, *ModuleEnv)
reifyDclModule` glob_module menv
  | glob_module == menv.me_main_dcl_module_n = (Nothing, menv)
  | otherwise
    # (mdcl, dcls) = muselect menv.me_dcl_modules glob_module
    # menv         = {menv & me_dcl_modules = dcls}
    = case mdcl of
        Just dcl -> (Just dcl, menv)
        _        -> (Nothing, menv)

arrHasIdx :: (a e) Int -> Bool | Array a e
arrHasIdx arr idx = idx < size arr

muselect :: !u:(a e) !Int -> *(Maybe e, !u:(a e)) | Array a e
muselect arr idx
  | arrHasIdx arr idx
    # (elem, arr) = arr![idx]
    = (Just elem, arr)
  | otherwise     = (Nothing, arr)

mselect :: (a e) !Int -> Maybe e | Array a e
mselect arr idx
  | arrHasIdx arr idx = Just arr.[idx]
  | otherwise         = Nothing

reifyFunDefsIdxSymbolType :: Ident Index *ModuleEnv -> *(Maybe SymbolType, *ModuleEnv)
reifyFunDefsIdxSymbolType ident idx menv
  # (mfd, fds) = muselect menv.me_fun_defs_cpy idx
  # menv = {menv & me_fun_defs_cpy = fds}
  = case mfd of
      Just fd -> case fd.fun_type of
                   Yes st -> (Just st, menv)
                   _      -> (Nothing, menv)
      _       -> (Nothing, menv)

reifyFunDefsIdxFunDef :: Index *ModuleEnv -> *(Maybe FunDef, *ModuleEnv)
reifyFunDefsIdxFunDef idx menv
  # (mfd, fds) = muselect menv.me_fun_defs_cpy idx
  = (mfd, {menv & me_fun_defs_cpy = fds})

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
  # rSym             = ppSymbIdent app_symb
  # (mFArgTy, menv)  = reifySymbIdentSymbolType app_symb menv
  # rhsfd            = fromMaybe (abort $ "reifyArgs failed to find function definition for " +++ ppCompact rSym) mfd
  # args             = getFunArgs rhsfd
  # rhsTy            = fromMaybe (abort "reifyArgs failed to reify SymbolType") mFArgTy
  = ((snd (dropContexts rhsTy args), rhsfd), menv)

fdArrToMap :: .{#FunDef} -> Map String FunDef
fdArrToMap fds = 'DM'.fromList [(d.fun_ident.id_name, d) \\ d <-: fds]

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

isListCompr :: !String -> Bool
isListCompr str = startsWith "c;" str // TODO: Verify

isLambda :: !String -> Bool
isLambda str = startsWith "\\\;" str // TODO: Verify

isTD :: !String -> Bool
isTD str = startsWith "TD;" str // TODO: Verify

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

funIsTopLevelBlueprint :: FunDef InhExpression *ChnExpression -> *(Bool, *ChnExpression)
funIsTopLevelBlueprint fd inh chn =
  case (fd.fun_type, fd.fun_kind) of
    (Yes {st_result={at_type}}, FK_Function _)
      # (hasTLBPInst, chn) = typeHasClassInstance at_type PD_TonicTopLevelBlueprintClass inh chn
      = (  hasTLBPInst
        && fd.fun_info.fi_def_level > 0
        && not (isLambda fd.fun_ident.id_name)
        && not (isListCompr fd.fun_ident.id_name)
        && not (isTD fd.fun_ident.id_name), chn)
    _ = (False, chn)

funIsBlueprintPart :: FunDef InhExpression *ChnExpression -> *(Bool, *ChnExpression)
funIsBlueprintPart fd inh chn =
  case (fd.fun_type, fd.fun_kind) of
    (Yes {st_result={at_type}}, FK_Function _)
      # (hasTLBPInst, chn) = typeHasClassInstance at_type PD_TonicBlueprintPartClass inh chn
      = (  hasTLBPInst
        && fd.fun_info.fi_def_level > 0
        && not (isLambda fd.fun_ident.id_name)
        && not (isListCompr fd.fun_ident.id_name)
        && not (isTD fd.fun_ident.id_name), chn)
    _ = (False, chn)

typeIsBlueprintPart :: Type InhExpression *ChnExpression -> *(Bool, *ChnExpression)
typeIsBlueprintPart ty inh chn
  = typeHasClassInstance ty PD_TonicBlueprintPartClass inh chn

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

identIsListComprehension :: Ident -> Bool
identIsListComprehension ident
  | size fnm > 0  = fnm.[0] == 'c' && fnm.[1] == ';'
  | otherwise     = False
  where fnm = ident.id_name


exprIsLambda :: Expression -> Bool
exprIsLambda (Var bv)  = identIsLambda bv.var_ident
exprIsLambda (App app) = identIsLambda app.app_symb.symb_ident
exprIsLambda _         = False

intersperse` :: String (a -> String) [a] -> String
intersperse` _ _ [] = ""
intersperse` _ pp [x] = pp x
intersperse` sep pp [x:xs] = pp x +++ sep +++ intersperse` sep pp xs

symbIdentIsBPPart :: SymbIdent InhExpression *ChnExpression -> *(Bool, *ChnExpression)
symbIdentIsBPPart {symb_ident, symb_kind=SK_OverloadedFunction {glob_module, glob_object} } inh chn
  # menv = chn.chn_module_env
  # (md, menv) = case glob_module == menv.me_main_dcl_module_n of
                   True
                     # (icl, menv) = menv!me_icl_module
                     = (icl.icl_common.com_member_defs.[glob_object], menv)
                   False
                     # (dcls, menv) = menv!me_dcl_modules
                     = (dcls.[glob_module].dcl_common.com_member_defs.[glob_object], menv)
  # chn  = {chn & chn_module_env = menv}
  # pdss = chn.chn_predef_symbols
  # (tmpds, pdss) = pdss![PD_TMonadClass]
  # (tapds, pdss) = pdss![PD_TApplicativeClass]
  # (tfpds, pdss) = pdss![PD_TFunctorClass]
  = (  (md.me_class.glob_module == tmpds.pds_module && md.me_class.glob_object == tmpds.pds_def)
    || (md.me_class.glob_module == tapds.pds_module && md.me_class.glob_object == tapds.pds_def)
    || (md.me_class.glob_module == tfpds.pds_module && md.me_class.glob_object == tfpds.pds_def)
    , {chn & chn_predef_symbols = pdss})
symbIdentIsBPPart si inh chn
  # (mst, menv) = reifySymbIdentSymbolType si chn.chn_module_env
  = case mst of
     Just st
       = typeHasClassInstance st.st_result.at_type PD_TonicBlueprintPartClass inh {chn & chn_module_env = menv}
     _ = abort ("symbIdentIsBPPart: failed to reify symbIdent '" +++ si.symb_ident.id_name +++ "'")

typeHasClassInstance :: Type Int InhExpression *ChnExpression -> *(Bool, *ChnExpression)
typeHasClassInstance (TA tsi args)    lookup_symbol inh chn = typeHasClassInstance` (TA tsi (init args)) lookup_symbol inh chn
typeHasClassInstance (TAS tsi args _) lookup_symbol inh chn = typeHasClassInstance` (TA tsi (init args)) lookup_symbol inh chn
typeHasClassInstance _             _             _   chn = (False, chn)

typeHasClassInstance` :: Type Int InhExpression *ChnExpression -> *(Bool, *ChnExpression)
typeHasClassInstance` ty lookup_symbol inh chn
  # (lookup_def, predefined_symbols) = (chn.chn_predef_symbols)![lookup_symbol]
  # instance_tree = inh.inh_instance_tree.[lookup_def.pds_module].[lookup_def.pds_def]
  # coercions     = { Coercions
                    | coer_demanded = {}
                    , coer_offered  = {}
                    }
  # heaps = chn.chn_heaps
  # (inst, ctxs, uni_ok, hp_type_heaps, coercions) = find_instance [ty] instance_tree inh.inh_common_defs heaps.hp_type_heaps coercions
  # chn   = {chn & chn_heaps = {heaps & hp_type_heaps = hp_type_heaps}}
  # defs  = inh.inh_common_defs.[lookup_def.pds_module].com_class_defs.[lookup_def.pds_def]
  = (inst.glob_module <> NotFound && inst.glob_object <> NotFound, chn)

typeHasClassSynonymInstance :: Type Int InhExpression *ChnExpression -> *(Bool, *ChnExpression)
typeHasClassSynonymInstance ty lookup_symbol inh chn
  # (lookup_def, predefined_symbols) = (chn.chn_predef_symbols)![lookup_symbol]
  # chn                  = {chn & chn_predef_symbols = predefined_symbols}
  # defs                 = inh.inh_common_defs.[lookup_def.pds_module].com_class_defs.[lookup_def.pds_def]
  # gtcClasses           = [gtc_class \\ {tc_class = TCGeneric {gtc_class}} <- defs.class_context]
  # contextClasses       = [] // [class_ref \\ {tc_class = TCClass class_ref} <- defs.class_context]
  # heaps                = chn.chn_heaps
  # (has, hp_type_heaps) = tyHasClasses inh.inh_instance_tree (gtcClasses ++ contextClasses) ty heaps.hp_type_heaps
  = (has, {chn & chn_heaps = {heaps & hp_type_heaps = hp_type_heaps}})
  where
  tyHasClasses :: {#{!InstanceTree}} [Global DefinedSymbol] Type *TypeHeaps -> *(Bool, *TypeHeaps)
  tyHasClasses class_instances []     at_type hp_type_heaps = (False, hp_type_heaps)
  tyHasClasses class_instances [x]    at_type hp_type_heaps = tyHasClasses` class_instances x at_type hp_type_heaps
  tyHasClasses class_instances [x:xs] at_type hp_type_heaps
    # (f, hp_type_heaps) = tyHasClasses` class_instances x at_type hp_type_heaps
    | f         = tyHasClasses class_instances xs at_type hp_type_heaps
    | otherwise = (False, hp_type_heaps)

  tyHasClasses` :: {#{!InstanceTree}} (Global DefinedSymbol) Type *TypeHeaps -> *(Bool, *TypeHeaps)
  tyHasClasses` class_instances {glob_module, glob_object} at_type hp_type_heaps
    # instance_tree = class_instances.[glob_module].[glob_object.ds_index]
    # coercions     = { Coercions
                      | coer_demanded = {}
                      , coer_offered  = {}
                      }
    # (inst, ctxs, uni_ok, hp_type_heaps, coercions) = find_instance [at_type] instance_tree inh.inh_common_defs hp_type_heaps coercions
    = (inst.glob_module <> NotFound && inst.glob_object <> NotFound, hp_type_heaps)

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

updateWithAnnot :: Int Expression InhExpression *ChnExpression -> *ChnExpression
updateWithAnnot fidx e inh chn
  # menv = chn.chn_module_env
  # fun_defs = menv.me_fun_defs
  # (fun_def, fun_defs) = fun_defs![fidx]
  = case fun_def of
      {fun_body = TransformedBody fb}
        # (argVars, localVars, freeVars) = collectVars e fb.tb_args
        # fun_def = { fun_def & fun_info = { fun_def.fun_info
                                           & fi_free_vars = freeVars
                                           , fi_local_vars = localVars
                                           }
                              , fun_body = TransformedBody { tb_args = argVars
                                                           , tb_rhs  = e
                                                           }
                    }
        # fun_defs = {fun_defs & [fidx] = fun_def}
        # menv     = { menv & me_fun_defs = fun_defs}
        = {chn & chn_module_env = menv}

updateFun :: Index !*{#FunDef} (FunDef -> FunDef) -> *{#FunDef}
updateFun idx fun_defs f
  # (mfd, fun_defs) = muselect fun_defs idx
  = case mfd of
      Just fd
        = { fun_defs & [idx] = f fd }
      _ = fun_defs


updateFunRhs :: Index !*{#FunDef} Expression -> *{#FunDef}
updateFunRhs idx fun_defs e
  # (mfd, fun_defs) = muselect fun_defs idx
  = case mfd of
      Just fd
        # tb = case fd.fun_body of
                 TransformedBody fb -> { fb & tb_rhs = e }
                 _                  -> abort "updateFunRhs: need a TransformedBody"
        = { fun_defs & [idx] = { fd & fun_body = TransformedBody tb }}
      _ = fun_defs

foldrSt :: !(.a -> .(.st -> .st)) ![.a] !.st -> .st
foldrSt op l st = foldr_st l
  where
    foldr_st []     = st
    foldr_st [a:as] = op a (foldr_st as)

predefIsUndefined :: PredefinedSymbol -> Bool
predefIsUndefined pds = pds.pds_def == NoIndex || pds.pds_module == NoIndex

symbIdentArity :: SymbIdent *ModuleEnv -> *(Maybe Int, *ModuleEnv)
symbIdentArity si menv
  # (mFunTy, menv) = reifySymbIdentSymbolType si menv
  = case mFunTy of
      Just funTy = (Just funTy.st_arity, menv)
      _
        # (mft, menv) = reifyFunType si menv
        = case mft of
            Just ft
              = (Just ft.ft_arity, menv)
            _ = (Nothing, menv)

argsRemaining :: App *ModuleEnv -> *(Int, *ModuleEnv)
argsRemaining app menv
  # ((ctxs, args), menv) = dropAppContexts app menv
  # argsLength        = length args
  # (marity, menv)    = symbIdentArity app.app_symb menv
  = case marity of
      Just arity
        # n = (arity - argsLength)
        = (if (n < 0) 0 n, menv) // TODO FIXME hack :(
      _ = (0, menv)

isPartialApp :: App *ModuleEnv -> *(Bool, *ModuleEnv)
isPartialApp app menv
  # (rem, menv) = argsRemaining app menv
  = (rem > 0, menv)

stringContents :: String -> String
stringContents str
  # sz = size str
  | sz > 1 && str.[0] == '"' && str.[sz - 1] == '"' = str % (1, sz - 2)
  | otherwise                                       = str

mkStr :: String -> Expression
mkStr str = BasicExpr (BVS ("\"" +++ str +++ "\""))

mkInt :: Int -> Expression
mkInt i   = BasicExpr (BVInt i)

mkBool :: Bool -> Expression
mkBool b = BasicExpr (BVB b)

appPredefinedSymbolWithEI :: Int [Expression] ((Global Index) -> SymbKind) *Heaps *PredefinedSymbols
                          -> *(App, *Heaps, *PredefinedSymbols)
appPredefinedSymbolWithEI pds_idx args mkKind heaps pdss
  # (ptr, expr_heap) = newPtr EI_Empty heaps.hp_expression_heap
  # heaps            = { heaps & hp_expression_heap = expr_heap }
  # (app, pdss)      = appPredefinedSymbol` pds_idx args mkKind ptr pdss
  = (app, heaps, pdss)

appPredefinedSymbol :: Int [Expression] ((Global Index) -> SymbKind) *PredefinedSymbols
                    -> *(App, *PredefinedSymbols)
appPredefinedSymbol pds_idx args mkKind pdss
  = appPredefinedSymbol` pds_idx args mkKind nilPtr pdss

appPredefinedSymbol` :: Int [Expression] ((Global Index) -> SymbKind) ExprInfoPtr *PredefinedSymbols
                     -> *(App, *PredefinedSymbols)
appPredefinedSymbol` pds_idx args mkKind ptr pdss
  # (size_pdss, pdss) = usize pdss
  | pds_idx >= size_pdss              = abort ("appPredefinedSymbol`: pds_idx = " +++ toString pds_idx +++ ", size_pdss = " +++ toString size_pdss)
  | pds_idx >= size predefined_idents = abort ("appPredefinedSymbol`: pds_idx = " +++ toString pds_idx +++ ", size_pdss = " +++ toString (size predefined_idents))
  # (pds, pdss)       = pdss![pds_idx]
  # ident             = predefined_idents.[pds_idx]
  = (
    { App
    | app_symb     = mkPredefSymbIdent ident pds mkKind
    , app_args     = args
    , app_info_ptr = ptr
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

instance FromStatic String where
  fromStatic (BasicExpr (BVS str)) = str
  fromStatic _                     = ""

instance ToStatic (Expression, Expression) where
  toStatic tup pdss = tupleToTupleExpr tup pdss

instance FromStatic (Expression, Expression) where
  fromStatic expr = tupleExprToTuple expr

instance ToStatic (Expression, Expression, Expression) where
  toStatic tup pdss = tuple3ToTupleExpr tup pdss

instance FromStatic (Expression, Expression, Expression) where
  fromStatic expr = tuple3ExprToTuple expr

listExprToList :: Expression -> [Expression]
listExprToList expr=:(App app) =
  case app.app_symb.symb_ident.id_name of
    PD_ConsSymbol_String ->
      case app.app_args of
        [head:tail:_]   -> [head : listExprToList tail]
        _               -> abort "listExprToList should not happen"
    PD_NilSymbol_String -> []
    _                   -> [expr]
listExprToList _ = []

listToListExpr :: [Expression] *PredefinedSymbols -> *(Expression, *PredefinedSymbols)
listToListExpr [] pdss
  # (app, pdss) = appPredefinedSymbol PD_NilSymbol [] SK_Constructor pdss
  = (App app, pdss)
listToListExpr [x:xs] pdss
  # (texpr, pdss) = listToListExpr xs pdss
  # (app, pdss)   = appPredefinedSymbol PD_ConsSymbol [x,texpr] SK_Constructor pdss
  = (App app, pdss)

tupleToTupleExpr :: (Expression, Expression) *PredefinedSymbols -> *(Expression, *PredefinedSymbols)
tupleToTupleExpr (e1, e2) pdss
  # (tup, pdss) = appPredefinedSymbol PD_Arity2TupleSymbol [e1, e2] SK_Constructor pdss
  = (App tup, pdss)

tupleExprToTuple :: Expression -> (Expression, Expression)
tupleExprToTuple (App app=:{app_args = [l : r : _]}) = (l, r)
tupleExprToTuple _ = abort "tupleExprToTuple"

tuple3ToTupleExpr :: (Expression, Expression, Expression) *PredefinedSymbols -> *(Expression, *PredefinedSymbols)
tuple3ToTupleExpr (e1, e2, e3) pdss
  # (tup, pdss) = appPredefinedSymbol (GetTupleConsIndex 3) [e1, e2, e3] SK_Constructor pdss
  = (App tup, pdss)

tuple3ExprToTuple :: Expression -> (Expression, Expression, Expression)
tuple3ExprToTuple (App app=:{app_args = [l : c : r : _]}) = (l, c, r)
tuple3ExprToTuple _ = abort "tuple3ExprToTuple"

freeVarToVar :: FreeVar *Heaps -> *(BoundVar, *Heaps)
freeVarToVar {fv_ident, fv_info_ptr} heaps
  # (ptr, expr_heap) = newPtr EI_Empty heaps.hp_expression_heap
  # heaps = { heaps & hp_expression_heap = expr_heap }
  = ({ var_ident = fv_ident,  var_info_ptr = fv_info_ptr, var_expr_ptr = ptr}, heaps)

pdssAreDefined :: [Int] *PredefinedSymbols -> *(Bool, *PredefinedSymbols)
pdssAreDefined [] pdss = (True, pdss)
pdssAreDefined [pds:xs] pdss
  # (pdss_size, pdss) = usize pdss
  | pds >= pdss_size  = (False, pdss)
  # (tune_symb, predefs)        = pdss![pds]
  | predefIsUndefined tune_symb = (False, pdss)
  | otherwise                   = pdssAreDefined xs pdss

mkTAssoc :: (Maybe FunType) -> TPriority
mkTAssoc Nothing = TNoPrio
mkTAssoc (Just ft) = fromPriority ft.ft_priority

fromPriority :: Priority -> TPriority
fromPriority (Prio LeftAssoc n)  = TPrio TLeftAssoc n
fromPriority (Prio RightAssoc n) = TPrio TRightAssoc n
fromPriority (Prio NoAssoc n)    = TPrio TNoAssoc n
fromPriority _                   = TNoPrio

//exprToTCleanExpr :: Expression *ModuleEnv -> *(TCleanExpr, *ModuleEnv)
//exprToTCleanExpr (App app) menv
  //# ((_, args), menv) = dropAppContexts app menv
  //= case args of
      //[] = (PPCleanExpr app.app_symb.symb_ident.id_name, menv)
      //xs
        //# (mft, menv)  = reifyFunType app.app_symb menv
        //# (tces, menv) = mapSt exprToTCleanExpr args menv
        //= (AppCleanExpr (mkTAssoc mft) app.app_symb.symb_ident.id_name tces, menv)
//exprToTCleanExpr expr menv
  //# (doc, menv) = ppExpression expr menv
  //= (PPCleanExpr (ppCompact doc), menv)

// TODO Associativity?
atypeToTCleanExpr :: AType -> TExpr
atypeToTCleanExpr {at_type} = typeToTCleanExpr at_type

typeToTCleanExpr :: Type -> TExpr
typeToTCleanExpr (TA tsi []) = TPPExpr tsi.type_ident.id_name
typeToTCleanExpr (TA tsi args)
  # tces = map (typeToTCleanExpr o \arg -> arg.at_type) args
  = TFApp tsi.type_ident.id_name tces TNoPrio
typeToTCleanExpr (TAS tsi [] _) = TPPExpr tsi.type_ident.id_name
typeToTCleanExpr (TAS tsi args _)
  # tces = map (typeToTCleanExpr o \arg -> arg.at_type) args
  = TFApp tsi.type_ident.id_name tces TNoPrio
typeToTCleanExpr (l --> r) = TFApp "->" [atypeToTCleanExpr l, atypeToTCleanExpr r] (TPrio TNoAssoc 0)
typeToTCleanExpr ty
  = TPPExpr (ppCompact (ppType ty))

allVarsBound :: !InhExpression !(Map Int BoundVar) -> Bool
allVarsBound inh bound = 'DM'.null ('DM'.difference bound inh.inh_tyenv)

varToFreeVar :: BoundVar -> FreeVar
varToFreeVar {var_ident, var_info_ptr}
  = {fv_def_level = NotALevel, fv_ident = var_ident, fv_info_ptr = var_info_ptr, fv_count = 0}

tfCase :: !ExprId !Case *ChnExpression -> *(Case, *ChnExpression)
tfCase eid cs=:{case_guards, case_default} chn
  # (guards, chn) = tfGuards case_guards chn
  # (def, chn)    = tfDefault case_default chn
  = ({cs & case_guards = guards, case_default = def}, chn)
  where
  tfGuards (AlgebraicPatterns idx as)       chn
    # (as, chn) = mapSt tfA (zip2 as [0..]) chn
    = (AlgebraicPatterns idx as, chn)
  tfGuards (BasicPatterns bt bs)            chn
    # (bs, chn) = mapSt tfB (zip2 bs [0..]) chn
    = (BasicPatterns bt bs, chn)
  tfGuards (NewTypePatterns idx as)         chn
    # (as, chn) = mapSt tfA (zip2 as [0..]) chn
    = (NewTypePatterns idx as, chn)
  tfGuards (OverloadedListPatterns ot e as) chn
    # (as, chn) = mapSt tfA (zip2 as [0..]) chn
    = (OverloadedListPatterns ot e as, chn)
  tfA (ap, n) chn
    # (pair, chn) = mkTuple (BVInt n) chn
    = ({ap & ap_expr = pair}, chn)
  tfB (bp, n) chn
    # (pair, chn) = mkTuple (BVInt n) chn
    = ({bp & bp_expr = pair}, chn)
  tfDefault (Yes def) chn
    # (pair, chn) = mkTuple (BVInt -1) chn
    = (Yes pair, chn)
  tfDefault _ chn = (No, chn)
  mkTuple nexpr chn
    # heaps               = chn.chn_heaps
    # pdss                = chn.chn_predef_symbols
    # (eidExpr, pdss)     = listToListExpr (map mkInt eid) pdss
    # (pair, heaps, pdss) = appPredefinedSymbolWithEI (GetTupleConsIndex 2)
                                  [ eidExpr
                                  , BasicExpr nexpr
                                  ] SK_Constructor heaps pdss
    = (App pair, {chn & chn_heaps = heaps
                      , chn_predef_symbols = pdss })

mkCaseDetFun :: !ExprId !Int ![BoundVar] !Expression !InhExpression !*ChnExpression -> *(Expression, *ChnExpression)
mkCaseDetFun eid exprPtr boundArgs bdy inh chn = (bdy, chn)
  //# freeArgs           = map varToFreeVar boundArgs
  //# name               = "_f_case_" +++ toString exprPtr
  //# (bdy`, chn)        = case bdy of
                           //Case cs
                             //# (cs, chn) = tfCase eid cs chn
                             //= (Case cs, chn)
                           //Let lt=:{let_expr = Case cs}
                             //# (cs, chn) = tfCase eid cs chn
                             //= (Let {lt & let_expr = Case cs}, chn)
                           //_ = abort "mkCaseDetFun shouldn't happen"
  //# arity              = length freeArgs
  //# funIdent           = { id_name = name
                         //, id_info = nilPtr
                         //}
  //# menv               = chn.chn_module_env
  //# fun_defs           = menv.me_fun_defs
  //# mainDclN           = menv.me_main_dcl_module_n
  //# (nextFD, fun_defs) = usize fun_defs
  //# (argVars, localVars, freeVars) = collectVars bdy` freeArgs
  //# newFunDef          = { fun_docs     = ""
                         //, fun_ident    = funIdent
                         //, fun_arity    = arity
                         //, fun_priority = NoPrio
                         //, fun_body     = TransformedBody { tb_args = argVars
                                                          //, tb_rhs  = bdy` }
                         //, fun_type     = No
                         //, fun_pos      = NoPos
                         //, fun_kind     = FK_Function cNameNotLocationDependent
                         //, fun_lifted   = 0
                         //, fun_info     = {EmptyFunInfo & fi_calls = collectCalls mainDclN bdy`
                                                        //, fi_free_vars = freeVars
                                                        //, fi_local_vars = localVars
                                                        //}
                         //}
  //# funDefs            = [fd \\ fd <-: fun_defs] ++ [newFunDef]
  //# fun_defs           = {fd \\ fd <- funDefs}

  //# fun_def            = chn.chn_fundef
  //# groups             = menv.me_groups
  //# groups             = [{group_members = [nextFD]} : [grp \\ grp <-: groups]]
  //# groups             = {grp \\ grp <- groups}
  //# fun_def            = {fun_def & fun_info = {fun_def.fun_info & fi_calls = [FunCall nextFD cGlobalScope : fun_def.fun_info.fi_calls]}}
  //# symb               = { symb_ident = funIdent
                         //, symb_kind  = SK_Function { glob_module = mainDclN
                                                    //, glob_object = nextFD }
                         //}
  //# menv               = {menv & me_fun_defs = fun_defs
                               //, me_groups = groups}
  //# chn                = {chn & chn_module_env = menv
                              //, chn_fundef = fun_def}
  //# heaps              = chn.chn_heaps
  //# (ptr, expr_heap)   = newPtr EI_Empty heaps.hp_expression_heap
  //# heaps              = { heaps & hp_expression_heap = expr_heap }
  //# chn                = { chn & chn_heaps = heaps }
  //# app                = { app_symb     = symb
                         //, app_args     = map Var boundArgs
                         //, app_info_ptr = ptr }
  //= (App app, chn)

wrapBody :: InhExpression SynExpression Bool *ChnExpression -> *(SynExpression, *ChnExpression)
wrapBody inh syn is_itasks_mod chn
  # pdss = chn.chn_predef_symbols
  # (ok, pdss) = pdssAreDefined [PD_tonicExtWrapArg, PD_tonicExtWrapBody] pdss
  # chn = {chn & chn_predef_symbols = pdss}
  | not ok     = (syn, chn)
  | otherwise
      # menv                 = chn.chn_module_env
      # fun_defs             = menv.me_fun_defs
      # (fun_def, fun_defs)  = fun_defs![inh.inh_fun_idx]
      # menv                 = {menv & me_fun_defs = fun_defs}
      # (mfdt, fun_defs_cpy) = muselect menv.me_fun_defs_cpy inh.inh_fun_idx
      # menv                 = {menv & me_fun_defs_cpy = fun_defs_cpy}
      # chn = {chn & chn_module_env = menv}
      = case mfdt of
          Just fdt
            = case (fun_def.fun_body, fdt.fun_type) of
                (TransformedBody fb, Yes symbty)
                  # menv = chn.chn_module_env
                  # (isPA, menv) = case syn.syn_annot_expr of
                                     App app -> isPartialApp app menv
                                     _       -> (False, menv)
                  # chn = {chn & chn_module_env = menv}
                  = if isPA (syn, chn) (doAddRefl fun_def.fun_ident fb.tb_args symbty inh.inh_common_defs chn)
                _ = (syn, chn)
          _ = (syn, chn)
  where
  doAddRefl fun_ident tb_args symbty common_defs chn
    # pdss = chn.chn_predef_symbols
    # (ok, pdss) = pdssAreDefined [ PD_tonicExtWrapArg
                                  , PD_tonicExtWrapBody
                                  , PD_tonicExtWrapBodyLam1
                                  , PD_tonicExtWrapBodyLam2
                                  , PD_tonicExtWrapBodyLam3
                                  , PD_ConsSymbol
                                  , PD_NilSymbol] pdss
    # chn = {chn & chn_predef_symbols = pdss}
    | not ok     = (syn, chn)
    # (args, chn) = foldr (mkArg symbty is_itasks_mod inh.inh_instance_tree) ([], chn) (zip2 tb_args symbty.st_args)
    | length args == length tb_args
        # evalableCases  = [(eid, 'DM'.elems vars, cs) \\ (eid, vars, cs) <- syn.syn_cases | allVarsBound inh vars]
        # (evalableCases, chn) = mapSt (\(eid, bvs, cs) chn -> mkCaseDetFun eid inh.inh_fun_idx bvs cs inh chn) evalableCases chn

        # menv = chn.chn_module_env
        # (icl, menv) = menv!me_icl_module
        # iclname = icl.icl_name.id_name
        # (rem, menv)  = case syn.syn_annot_expr of
                           App {app_symb = {symb_ident}}
                             | symb_ident == predefined_idents.[PD_tonicExtWrapBodyLam1] = (1, menv)
                             | symb_ident == predefined_idents.[PD_tonicExtWrapBodyLam2] = (2, menv)
                             | symb_ident == predefined_idents.[PD_tonicExtWrapBodyLam3] = (3, menv)
                           App app
                             = argsRemaining app menv
                           _ = (0, menv)
        # (xs, pdss) = toStatic args chn.chn_predef_symbols
        //# (casesExpr, pdss) = listToListExpr evalableCases pdss
        # (casesExpr, pdss) = listToListExpr [] pdss
        # (wrap, heaps, pdss) = appPredefinedSymbolWithEI (findBodyWrap rem)
                                  [ mkStr iclname
                                  , mkStr fun_ident.id_name
                                  , xs
                                  , casesExpr
                                  , syn.syn_annot_expr
                                  ] SK_Function chn.chn_heaps pdss
        = ({syn & syn_annot_expr = App wrap}, {chn & chn_module_env = menv
                                                   , chn_heaps = heaps
                                                   , chn_predef_symbols = pdss})
    | otherwise = (syn, chn)
    where
    findBodyWrap :: Int -> Int
    findBodyWrap 0 = PD_tonicExtWrapBody
    findBodyWrap 1 = PD_tonicExtWrapBodyLam1
    findBodyWrap 2 = PD_tonicExtWrapBodyLam2
    findBodyWrap 3 = PD_tonicExtWrapBodyLam3
    findBodyWrap n = abort ("No PD_tonicExtWrapBodyLam" +++ toString n)

    mkArg :: SymbolType Bool {#{!InstanceTree}} (FreeVar, AType) ([Expression], *ChnExpression) -> *([Expression], *ChnExpression)
    mkArg symty is_itasks_mod class_instances (arg=:{fv_info_ptr, fv_ident}, {at_type}) (xs, chn)
      # pdss = chn.chn_predef_symbols
      # heaps = chn.chn_heaps
      # (itask_class_symbol, pdss) = pdss![PD_ITaskClass]
      # gtcClasses  = [gtc_class \\ {tc_class = TCGeneric {gtc_class}} <- common_defs.[itask_class_symbol.pds_module].com_class_defs.[itask_class_symbol.pds_def].class_context] 
      # (hasITasks, hp_type_heaps) = tyHasITaskClasses class_instances gtcClasses at_type heaps.hp_type_heaps
      # heaps         = {heaps & hp_type_heaps = hp_type_heaps}
      # (noCtx, pdss) = noITaskCtx arg symty.st_context pdss
      # (bv, heaps)   = freeVarToVar arg heaps
      # (viewApp, heaps, pdss) = appPredefinedSymbolWithEI PD_tonicExtWrapArg
                                   [ mkStr fv_ident.id_name
                                   , mkInt (ptrToInt fv_info_ptr)
                                   , if (is_itasks_mod || (not hasITasks && noCtx))
                                       (mkStr fv_ident.id_name)
                                       (Var bv)
                                   ] SK_Function heaps pdss
      # (texpr, pdss) = toStatic (mkStr fv_ident.id_name, mkInt (ptrToInt fv_info_ptr), App viewApp) pdss
      = ([texpr:xs], {chn & chn_predef_symbols = pdss, chn_heaps = heaps })
    tyHasITaskClasses :: {#{!InstanceTree}} [Global DefinedSymbol] Type *TypeHeaps -> *(Bool, *TypeHeaps)
    tyHasITaskClasses class_instances []     at_type hp_type_heaps = (False, hp_type_heaps)
    tyHasITaskClasses class_instances [x]    at_type hp_type_heaps = tyHasITaskClasses` class_instances x at_type hp_type_heaps
    tyHasITaskClasses class_instances [x:xs] at_type hp_type_heaps
      # (f, hp_type_heaps) = tyHasITaskClasses` class_instances x at_type hp_type_heaps
      | f         = tyHasITaskClasses class_instances xs at_type hp_type_heaps
      | otherwise = (False, hp_type_heaps)

    tyHasITaskClasses` :: {#{!InstanceTree}} (Global DefinedSymbol) Type *TypeHeaps -> *(Bool, *TypeHeaps)
    tyHasITaskClasses` class_instances {glob_module, glob_object} at_type hp_type_heaps
      # instance_tree = class_instances.[glob_module].[glob_object.ds_index]
      # coercions     = { Coercions
                        | coer_demanded = {}
                        , coer_offered  = {}
                        }
      # (inst, ctxs, uni_ok, hp_type_heaps, coercions) = find_instance [at_type] instance_tree common_defs hp_type_heaps coercions
      = (inst.glob_module <> NotFound && inst.glob_object <> NotFound, hp_type_heaps)

    noITaskCtx :: FreeVar [TypeContext] *PredefinedSymbols -> *(Bool, *PredefinedSymbols)
    noITaskCtx fv tcs pdss
      # (pds, pdss) = pdss![PD_ITaskClass]
      = ( isEmpty [0 \\ {tc_var, tc_class = (TCClass {glob_object, glob_module})} <- tcs
                      |  fv.fv_info_ptr == tc_var
                      && glob_module == pds.pds_module
                      && glob_object.ds_index == pds.pds_def]
        , pdss)

instance == (Global a) | == a where
  (==) g1 g2 = g1.glob_module == g2.glob_module && g1.glob_object == g2.glob_object

instance toString IdentOrQualifiedIdent where
  toString (Ident ident) = ident.id_name
  toString (QualifiedIdent _ str) = str
