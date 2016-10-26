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

dropAppContexts :: App *ChnExpression -> *(([Expression], [Expression]), *ChnExpression)
dropAppContexts app chn
  # (mcd, chn) = reifyConsDef app.app_symb chn
  = case mcd of
      Just cd = (dropContexts cd.cons_type app.app_args, chn)
      Nothing
        # (mFunTy, chn) = reifySymbIdentSymbolType app.app_symb chn
        = case mFunTy of
            Just funTy -> (dropContexts funTy app.app_args, chn)
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
reifyConsDef :: SymbIdent *ChnExpression -> *(Maybe ConsDef, *ChnExpression)
reifyConsDef si chn
  # (common, iclmod) = (chn.chn_icl_module)!icl_common
  # dcls             = chn.chn_dcl_modules
  # chn             = {chn & chn_icl_module=iclmod}
  = case searchConsDefs ident common.com_cons_defs of
      Just cd = (Just cd, chn)
      _
        # cds = [cd \\ Just cd <- [searchConsDefs ident common.com_cons_defs \\ common <- [dclmod.dcl_common \\ dclmod <-: dcls]]]
        = (listToMaybe cds, chn)

  where
    searchConsDefs :: String .{# ConsDef} -> Maybe ConsDef
    searchConsDefs ident defs = listToMaybe [cd \\ cd <-: defs | cd.cons_ident.id_name == ident]

    ident = si.symb_ident.id_name

reifyFunType :: SymbIdent *ChnExpression -> *(Maybe FunType, *ChnExpression)
reifyFunType si chn=:{chn_dcl_modules}
  = case (symbIdentModuleIdx si, symbIdentObjectIdx si) of
      (Just mi, oi)
        = reifyDclModulesIdxFunType` mi oi chn
      _ = (Nothing, chn)

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

reifyFunDef :: SymbIdent *ChnExpression -> *(Maybe FunDef, *ChnExpression)
reifyFunDef si chn = reifyFunDefsIdxFunDef (symbIdentObjectIdx si) chn

optionalToMaybe :: (Optional a) -> Maybe a
optionalToMaybe (Yes x) = Just x
optionalToMaybe No      = Nothing

symbIdentInMain :: SymbIdent *ChnExpression -> *(Bool, *ChnExpression)
symbIdentInMain {symb_kind=SK_Function glob}              chn = globIdxInMain glob chn
symbIdentInMain {symb_kind=SK_DclMacro glob}              chn = globIdxInMain glob chn
symbIdentInMain {symb_kind=SK_LocalDclMacroFunction glob} chn = globIdxInMain glob chn
symbIdentInMain {symb_kind=SK_OverloadedFunction glob}    chn = globIdxInMain glob chn
symbIdentInMain {symb_kind=SK_Constructor glob}           chn = globIdxInMain glob chn
symbIdentInMain {symb_kind=SK_Generic glob _}             chn = globIdxInMain glob chn
symbIdentInMain {symb_kind=SK_OverloadedConstructor glob} chn = globIdxInMain glob chn
symbIdentInMain _                                         chn = (False, chn)

globIdxInMain :: (Global Index) *ChnExpression -> *(Bool, *ChnExpression)
globIdxInMain glob chn
  # (main_dcl_module_n, chn) = chn!chn_main_dcl_module_n
  = (glob.glob_module == main_dcl_module_n, chn)

idxIsMain :: Index *ChnExpression -> *(Bool, *ChnExpression)
idxIsMain idx chn
  # (main_dcl_module_n, chn) = chn!chn_main_dcl_module_n
  = (idx == main_dcl_module_n, chn)

reifyFunDefsIdxPriority :: Index *ChnExpression -> *(Maybe Priority, *ChnExpression)
reifyFunDefsIdxPriority idx chn
  # (mfd, fds) = muselect chn.chn_fun_defs_cpy idx
  # chn = {chn & chn_fun_defs_cpy = fds}
  = case mfd of
      Just fd -> (Just fd.fun_priority, chn)
      _       -> (Nothing, chn)

reifyDclModulesIdxPriority :: (Global Index) *ChnExpression -> *(Maybe Priority, *ChnExpression)
reifyDclModulesIdxPriority {glob_module,glob_object} chn = reifyDclModulesIdxPriority` glob_module glob_object chn

reifyDclModulesIdxPriority` :: Index Index *ChnExpression -> *(Maybe Priority, *ChnExpression)
reifyDclModulesIdxPriority` glob_module glob_object chn
  # (mFunTy, chn) = reifyDclModulesIdxFunType` glob_module glob_object chn
  = case mFunTy of
      Just funTy -> (Just funTy.ft_priority, chn)
      _          -> (Nothing, chn)

reifySymbIdentPriority :: SymbIdent *ChnExpression -> *(Maybe Priority, *ChnExpression)
reifySymbIdentPriority {symb_ident, symb_kind=SK_Function glob} chn
  | glob.glob_module == chn.chn_main_dcl_module_n = reifyFunDefsIdxPriority glob.glob_object chn
  | otherwise                                     = reifyDclModulesIdxPriority glob chn
reifySymbIdentPriority {symb_ident, symb_kind=SK_IclMacro idx}           chn = reifyFunDefsIdxPriority idx chn
reifySymbIdentPriority {symb_ident, symb_kind=SK_LocalMacroFunction idx} chn = reifyFunDefsIdxPriority idx chn
reifySymbIdentPriority {symb_ident, symb_kind=SK_DclMacro glob} chn
  | glob.glob_module == chn.chn_main_dcl_module_n = reifyFunDefsIdxPriority glob.glob_object chn
  | otherwise                                     = reifyDclModulesIdxPriority glob chn
reifySymbIdentPriority {symb_ident, symb_kind=SK_LocalDclMacroFunction glob} chn
  | glob.glob_module == chn.chn_main_dcl_module_n = reifyFunDefsIdxPriority glob.glob_object chn
  | otherwise                                     = reifyDclModulesIdxPriority glob chn
reifySymbIdentPriority {symb_ident, symb_kind=SK_OverloadedFunction {glob_module, glob_object} } chn
  | glob_module == chn.chn_main_dcl_module_n
      # (icl, chn) = chn!chn_icl_module
      # md          = icl.icl_common.com_member_defs.[glob_object]
      = (Just md.me_priority, chn)
  | otherwise
      # (dcls, chn) = chn!chn_dcl_modules
      # md           = dcls.[glob_module].dcl_common.com_member_defs.[glob_object]
      = (Just md.me_priority, chn)
reifySymbIdentPriority {symb_ident, symb_kind=SK_GeneratedFunction fip idx} chn = reifyFunDefsIdxPriority idx chn
reifySymbIdentPriority {symb_ident, symb_kind=SK_Constructor {glob_module, glob_object}} chn
  | glob_module == chn.chn_main_dcl_module_n
      # (icl, chn) = chn!chn_icl_module
      # md          = icl.icl_common.com_cons_defs.[glob_object]
      = (Just md.cons_priority, chn)
  | otherwise
      # (dcls, chn) = chn!chn_dcl_modules
      # md           = dcls.[glob_module].dcl_common.com_cons_defs.[glob_object]
      = (Just md.cons_priority, chn)
reifySymbIdentPriority {symb_ident, symb_kind=SK_NewTypeConstructor globi} chn = abort "reifySymbIdentType: SK_NewTypeConstructor" // reifyDclModulesIdx` globi.gi_module globi.gi_index chn
reifySymbIdentPriority {symb_ident, symb_kind=SK_Generic {glob_module, glob_object} _} chn
  = (Nothing, chn)
reifySymbIdentPriority {symb_ident, symb_kind=SK_OverloadedConstructor glob} chn
  | glob.glob_module == chn.chn_main_dcl_module_n = reifyFunDefsIdxPriority glob.glob_object chn
  | otherwise                                     = reifyDclModulesIdxPriority glob chn
reifySymbIdentPriority si chn = abort "reifySymbIdentPriority: unsupported"

reifySymbIdentSymbolType :: SymbIdent *ChnExpression -> *(Maybe SymbolType, *ChnExpression)
reifySymbIdentSymbolType {symb_ident, symb_kind=SK_Function glob} chn
  | glob.glob_module == chn.chn_main_dcl_module_n = reifyFunDefsIdxSymbolType symb_ident glob.glob_object chn
  | otherwise                                     = reifyDclModulesIdxSymbolType glob chn
reifySymbIdentSymbolType {symb_ident, symb_kind=SK_IclMacro idx}           chn = reifyFunDefsIdxSymbolType symb_ident idx chn
reifySymbIdentSymbolType {symb_ident, symb_kind=SK_LocalMacroFunction idx} chn = reifyFunDefsIdxSymbolType symb_ident idx chn
reifySymbIdentSymbolType {symb_ident, symb_kind=SK_DclMacro glob} chn
  | glob.glob_module == chn.chn_main_dcl_module_n = reifyFunDefsIdxSymbolType symb_ident glob.glob_object chn
  | otherwise                                     = reifyDclModulesIdxSymbolType glob chn
reifySymbIdentSymbolType {symb_ident, symb_kind=SK_LocalDclMacroFunction glob} chn
  | glob.glob_module == chn.chn_main_dcl_module_n = reifyFunDefsIdxSymbolType symb_ident glob.glob_object chn
  | otherwise                                     = reifyDclModulesIdxSymbolType glob chn
reifySymbIdentSymbolType {symb_ident, symb_kind=SK_OverloadedFunction {glob_module, glob_object} } chn
  | glob_module == chn.chn_main_dcl_module_n
      # (icl, chn) = chn!chn_icl_module
      # md          = icl.icl_common.com_member_defs.[glob_object]
      = (Just md.me_type, chn)
  | otherwise
      # (dcls, chn) = chn!chn_dcl_modules
      # md           = dcls.[glob_module].dcl_common.com_member_defs.[glob_object]
      = (Just md.me_type, chn)
reifySymbIdentSymbolType {symb_ident, symb_kind=SK_GeneratedFunction fip idx} chn = reifyFunDefsIdxSymbolType symb_ident idx chn
reifySymbIdentSymbolType {symb_ident, symb_kind=SK_Constructor {glob_module, glob_object}} chn
  | glob_module == chn.chn_main_dcl_module_n
      # (icl, chn) = chn!chn_icl_module
      # md          = icl.icl_common.com_cons_defs.[glob_object]
      = (Just md.cons_type, chn)
  | otherwise
      # (dcls, chn) = chn!chn_dcl_modules
      # md           = dcls.[glob_module].dcl_common.com_cons_defs.[glob_object]
      = (Just md.cons_type, chn)
reifySymbIdentSymbolType {symb_ident, symb_kind=SK_NewTypeConstructor globi} chn = abort "reifySymbIdentType: SK_NewTypeConstructor" // reifyDclModulesIdx` globi.gi_module globi.gi_index chn
reifySymbIdentSymbolType {symb_ident, symb_kind=SK_Generic {glob_module, glob_object} _} chn
  | glob_module == chn.chn_main_dcl_module_n
      # (icl, chn) = chn!chn_icl_module
      # md          = icl.icl_common.com_generic_defs.[glob_object]
      = (Just md.gen_type, chn)
  | otherwise
      # (dcls, chn) = chn!chn_dcl_modules
      # md           = dcls.[glob_module].dcl_common.com_generic_defs.[glob_object]
      = (Just md.gen_type, chn)
reifySymbIdentSymbolType {symb_ident, symb_kind=SK_OverloadedConstructor glob} chn
  | glob.glob_module == chn.chn_main_dcl_module_n = reifyFunDefsIdxSymbolType symb_ident glob.glob_object chn
  | otherwise                                     = reifyDclModulesIdxSymbolType glob chn
reifySymbIdentSymbolType si chn = abort "reifySymbIdentSymbolType: unsupported"

reifyDclModulesIdxSymbolType :: (Global Index) *ChnExpression -> *(Maybe SymbolType, *ChnExpression)
reifyDclModulesIdxSymbolType {glob_module,glob_object} chn = reifyDclModulesIdxSymbolType` glob_module glob_object chn

reifyDclModulesIdxSymbolType` :: Index Index *ChnExpression -> *(Maybe SymbolType, *ChnExpression)
reifyDclModulesIdxSymbolType` glob_module glob_object chn
  # (mFunTy, chn) = reifyDclModulesIdxFunType` glob_module glob_object chn
  = case mFunTy of
      Just funTy -> (Just funTy.ft_type, chn)
      _          -> (Nothing, chn)

reifyDclModulesIdxFunType :: (Global Index) *ChnExpression -> *(Maybe FunType, *ChnExpression)
reifyDclModulesIdxFunType {glob_module,glob_object} chn = reifyDclModulesIdxFunType` glob_module glob_object chn

reifyDclModulesIdxFunType` :: Index Index *ChnExpression -> *(Maybe FunType, *ChnExpression)
reifyDclModulesIdxFunType` glob_module glob_object chn
  | glob_module == chn.chn_main_dcl_module_n = (Nothing, chn)
  | otherwise
    # (mdcl, dcls) = muselect chn.chn_dcl_modules glob_module
    # chn         = {chn & chn_dcl_modules = dcls}
    = case mdcl of
        Just dcl -> (mselect dcl.dcl_functions glob_object, chn)
        _        -> (Nothing, chn)

  //# (common, iclmod) = (chn.chn_icl_module)!icl_common
  //# dcls             = chn.chn_dcl_modules
  //# chn             = {chn & chn_icl_module=iclmod}
  //= case searchConsDefs ident common.com_cons_defs of
      //Just cd = (Just cd, chn)
      //_
        //# cds = [cd \\ Just cd <- [searchConsDefs ident common.com_cons_defs \\ common <- [dclmod.dcl_common \\ dclmod <-: dcls]]]
        //= (listToMaybe cds, chn)

  //where
    //searchConsDefs :: String .{# ConsDef} -> Maybe ConsDef
    //searchConsDefs ident defs = listToMaybe [cd \\ cd <-: defs | cd.cons_ident.id_name == ident]

    //ident = si.symb_ident.id_name

reifyDclModule :: SymbIdent *ChnExpression -> *(Maybe DclModule, *ChnExpression)
reifyDclModule si chn =
  case symbIdentModuleIdx si of
    Just mi -> reifyDclModule` mi chn
    _       -> (Nothing, chn)

reifyDclModule` :: Index *ChnExpression -> *(Maybe DclModule, *ChnExpression)
reifyDclModule` glob_module chn
  | glob_module == chn.chn_main_dcl_module_n = (Nothing, chn)
  | otherwise
    # (mdcl, dcls) = muselect chn.chn_dcl_modules glob_module
    # chn         = {chn & chn_dcl_modules = dcls}
    = case mdcl of
        Just dcl -> (Just dcl, chn)
        _        -> (Nothing, chn)

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

reifyFunDefsIdxSymbolType :: Ident Index *ChnExpression -> *(Maybe SymbolType, *ChnExpression)
reifyFunDefsIdxSymbolType ident idx chn
  # (mfd, fds) = muselect chn.chn_fun_defs_cpy idx
  # chn = {chn & chn_fun_defs_cpy = fds}
  = case mfd of
      Just fd -> case fd.fun_type of
                   Yes st -> (Just st, chn)
                   _      -> (Nothing, chn)
      _       -> (Nothing, chn)

reifyFunDefsIdxFunDef :: Index *ChnExpression -> *(Maybe FunDef, *ChnExpression)
reifyFunDefsIdxFunDef idx chn
  # (mfd, fds) = muselect chn.chn_fun_defs_cpy idx
  = (mfd, {chn & chn_fun_defs_cpy = fds})

reifyArgsAndDef :: SymbIdent *ChnExpression -> *(([FreeVar], FunDef), *ChnExpression)
reifyArgsAndDef app_symb chn
  # (mfd, chn)     = reifyFunDef app_symb chn
  # rSym           = ppSymbIdent app_symb
  # (mFArgTy, chn) = reifySymbIdentSymbolType app_symb chn
  # rhsfd          = fromMaybe (abort $ "reifyArgs failed to find function definition for " +++ ppCompact rSym) mfd
  # args           = getFunArgs rhsfd
  # rhsTy          = fromMaybe (abort "reifyArgs failed to reify SymbolType") mFArgTy
  = ((snd (dropContexts rhsTy args), rhsfd), chn)

isCons :: String -> Bool
isCons str = str == PD_ConsSymbol_String

isNil :: String -> Bool
isNil str = str == PD_NilSymbol_String

appIsList :: App -> Bool
appIsList app = isCons ident || isNil ident
  where ident = app.app_symb.symb_ident.id_name

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

funIsTopLevelBlueprintOrLam :: FunDef InhExpression *ChnExpression -> *(Bool, *ChnExpression)
funIsTopLevelBlueprintOrLam fd inh chn =
  case (fd.fun_type, fd.fun_kind) of
    (Yes {st_result={at_type}}, FK_Function _)
      # (hasTLBPInst, chn) = typeHasClassInstance at_type PD_TonicTopLevelBlueprintClass inh chn
      = (  hasTLBPInst
        && fd.fun_info.fi_def_level > 0
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

funArgTys :: FunDef -> [Type]
funArgTys {fun_type=Yes {st_args}} = map (\x -> x.at_type) st_args
funArgTys {fun_ident={id_name}} = abort ("Tonic.Util.funArgTys argument types of " +++ id_name +++ " are unknown.")

funContext :: FunDef -> [TypeContext]
funContext {fun_type=Yes {st_context}} = st_context
funContext _ = []

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
  # (md, chn) = case glob_module == chn.chn_main_dcl_module_n of
                   True
                     # (icl, chn) = chn!chn_icl_module
                     = (icl.icl_common.com_member_defs.[glob_object], chn)
                   False
                     # (dcls, chn) = chn!chn_dcl_modules
                     = (dcls.[glob_module].dcl_common.com_member_defs.[glob_object], chn)
  # pdss = chn.chn_predef_symbols
  # (tmpds, pdss) = pdss![PD_TMonadClass]
  # (tapds, pdss) = pdss![PD_TApplicativeClass]
  = (  (md.me_class.glob_module == tmpds.pds_module && md.me_class.glob_object == tmpds.pds_def)
    || (md.me_class.glob_module == tapds.pds_module && md.me_class.glob_object == tapds.pds_def)
    , {chn & chn_predef_symbols = pdss})
symbIdentIsBPPart si inh chn
  # (mst, chn) = reifySymbIdentSymbolType si chn
  = case mst of
     Just st
       = typeHasClassInstance st.st_result.at_type PD_TonicBlueprintPartClass inh chn
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

isInfix :: SymbIdent *ChnExpression -> *(Bool, *ChnExpression)
isInfix si chn
  # (mfd, chn) = reifyFunDef si chn
  = case mfd of
      Just fd = (prioIsInfix fd.fun_priority, chn)
      Nothing
        # (mft, chn) = reifyFunType si chn
        = case mft of
            Just ft  = (prioIsInfix ft.ft_priority, chn)
            _
              # (mcd, chn) = reifyConsDef si chn
              = case mcd of
                  Just cd -> (prioIsInfix cd.cons_priority, chn)
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
  # fun_defs = chn.chn_fun_defs
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
        = { chn & chn_fun_defs = fun_defs}

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

symbIdentArity :: SymbIdent *ChnExpression -> *(Maybe Int, *ChnExpression)
symbIdentArity si chn
  # (mFunTy, chn) = reifySymbIdentSymbolType si chn
  = case mFunTy of
      Just funTy = (Just funTy.st_arity, chn)
      _
        # (mft, chn) = reifyFunType si chn
        = case mft of
            Just ft
              = (Just ft.ft_arity, chn)
            _ = (Nothing, chn)

argsRemaining :: App *ChnExpression -> *(Int, *ChnExpression)
argsRemaining app chn
  # ((ctxs, args), chn) = dropAppContexts app chn
  # argsLength        = length args
  # (marity, chn)    = symbIdentArity app.app_symb chn
  = case marity of
      Just arity
        # n = (arity - argsLength)
        = (if (n < 0) 0 n, chn) // TODO FIXME hack :(
      _ = (0, chn)

isPartialApp :: App *ChnExpression -> *(Bool, *ChnExpression)
isPartialApp app chn
  # (rem, chn) = argsRemaining app chn
  = (rem > 0, chn)

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

fromPriority :: Priority -> TPriority
fromPriority (Prio LeftAssoc n)  = TPrio TLeftAssoc n
fromPriority (Prio RightAssoc n) = TPrio TRightAssoc n
fromPriority (Prio NoAssoc n)    = TPrio TNoAssoc n
fromPriority _                   = TNoPrio

atypeToTCleanExpr :: AType -> TExpr
atypeToTCleanExpr {at_type} = typeToTCleanExpr at_type

typeToTCleanExpr :: Type -> TExpr
typeToTCleanExpr (TA tsi []) = TPPExpr tsi.type_ident.id_name
typeToTCleanExpr (TA tsi args)
  # tces = map (typeToTCleanExpr o \arg -> arg.at_type) args
  = TFApp [] tsi.type_ident.id_name tces TNoPrio
typeToTCleanExpr (TAS tsi [] _) = TPPExpr tsi.type_ident.id_name
typeToTCleanExpr (TAS tsi args _)
  # tces = map (typeToTCleanExpr o \arg -> arg.at_type) args
  = TFApp [] tsi.type_ident.id_name tces TNoPrio
typeToTCleanExpr (l --> r) = TFApp [] "->" [atypeToTCleanExpr l, atypeToTCleanExpr r] (TPrio TNoAssoc 0)
typeToTCleanExpr ty
  = TPPExpr (ppCompact (ppType ty))

allVarsBound :: !InhExpression !(Map Int BoundVar) -> Bool
allVarsBound inh bound = 'DM'.null ('DM'.difference bound inh.inh_tyenv)

varToFreeVar :: BoundVar -> FreeVar
varToFreeVar {var_ident, var_info_ptr}
  = {fv_def_level = NotALevel, fv_ident = var_ident, fv_info_ptr = var_info_ptr, fv_count = 0}

tfCase :: !ExprId !Case -> Case
tfCase eid cs = fst (tfCase` eid cs [0..])

tfCase` eid cs=:{case_guards, case_default} branchNums
  # (gs, branchNums) = tfGuards case_guards branchNums
  # (d, branchNums)  = tfDefault case_default branchNums
  = ({cs & case_guards = gs, case_default = d}, branchNums)
  where
  tfGuards (AlgebraicPatterns idx as) branchNums
    # (as, branchNums) = foldr tfA ([], branchNums) as
    = (AlgebraicPatterns idx as, branchNums)
  tfGuards (BasicPatterns bt bs) branchNums
    # (bs, branchNums) = foldr tfB ([], branchNums) bs
    = (BasicPatterns bt bs, branchNums)
  tfGuards (NewTypePatterns idx as) branchNums
    # (as, branchNums) = foldr tfA ([], branchNums) as
    = (NewTypePatterns idx as, branchNums)
  tfGuards (DynamicPatterns ds) branchNums
    # (ds, branchNums) = foldr tfD ([], branchNums) ds
    = (DynamicPatterns ds, branchNums)
  tfGuards (OverloadedListPatterns ot e as) branchNums
    # (as, branchNums) = foldr tfA ([], branchNums) as
    = (OverloadedListPatterns ot e as, branchNums)
  tfGuards p branchNums = (p, branchNums)
  tfA ap (acc, [num : branchNums])
    = case ap.ap_expr of
        Case cs`=:{case_explicit = False}
          # (cs`, branchNums) = tfCase` eid cs` [num:branchNums]
          = ([{ap & ap_expr = Case cs`} : acc], branchNums)
        _ = ([{ap & ap_expr = BasicExpr (BVInt num)} : acc], branchNums)
  tfB bp (acc, [num : branchNums])
    = case bp.bp_expr of
        Case cs`=:{case_explicit = False}
          # (cs`, branchNums) = tfCase` eid cs` [num:branchNums]
          = ([{bp & bp_expr = Case cs`} : acc], branchNums)
        _ = ([{bp & bp_expr = BasicExpr (BVInt num)} : acc], branchNums)
  tfD dp (acc, [num : branchNums])
    = case dp.dp_rhs of
        Case cs`=:{case_explicit = False}
          # (cs`, branchNums) = tfCase` eid cs` [num:branchNums]
          = ([{dp & dp_rhs = Case cs`} : acc], branchNums)
        _ = ([{dp & dp_rhs = BasicExpr (BVInt num)} : acc], branchNums)
  tfDefault (Yes def) [num : branchNums]
    = case def of
        Case cs`=:{case_explicit = False}
          # (cs`, branchNums) = tfCase` eid cs` [num:branchNums]
          = (Yes (Case cs`), branchNums)
        _ = (Yes (BasicExpr (BVInt num)), branchNums)
  tfDefault _ branchNums = (No, branchNums)

refreshVariables :: [FreeVar] Expression *ChnExpression -> *([FreeVar], Expression, *ChnExpression)
refreshVariables fvs e chn
  # heaps           = chn.chn_heaps
  # var_heap        = heaps.hp_var_heap
  # expr_heap       = heaps.hp_expression_heap
  # (fvs, var_heap) = mapSt refreshFreeVar fvs var_heap
  # (e, (var_heap, expr_heap))   = refreshVariables` e (var_heap, expr_heap)
  # heaps    = {heaps & hp_var_heap = var_heap
                      , hp_expression_heap = expr_heap }
  = (fvs, e, {chn & chn_heaps = heaps})
  where
  refreshFreeVar :: FreeVar *VarHeap -> *(FreeVar, *VarHeap)
  refreshFreeVar fv var_heap
    # (newPtr, var_heap) = newPtr VI_Empty var_heap
    # var_heap = var_heap <:= (fv.fv_info_ptr, VI_ForwardClassVar newPtr)
    = ({fv & fv_info_ptr = newPtr}, var_heap)

  refreshVariables` :: Expression *(*VarHeap, *ExpressionHeap) -> *(Expression, *(*VarHeap, *ExpressionHeap))
  refreshVariables` (Var bv) (var_heap, expr_heap)
    # (newExprPtr, expr_heap) = newPtr EI_Empty expr_heap
    # (newVarPtr, var_heap)   = readPtr bv.var_info_ptr var_heap
    # newVarPtr               = case newVarPtr of
                                  VI_ForwardClassVar newVarPtr -> newVarPtr
                                  _                            -> abort "refreshVariables` (1)"
    = (Var {bv & var_info_ptr = newVarPtr
               , var_expr_ptr = newExprPtr}, (var_heap, expr_heap))

  refreshVariables` (App app) (var_heap, expr_heap)
    # (args, (var_heap, expr_heap)) = mapSt refreshVariables` app.app_args (var_heap, expr_heap)
    = (App {app & app_args = args}, (var_heap, expr_heap))
  refreshVariables` (e @ es) (var_heap, expr_heap)
    # (e, (var_heap, expr_heap))  = refreshVariables` e (var_heap, expr_heap)
    # (es, (var_heap, expr_heap)) = mapSt refreshVariables` es (var_heap, expr_heap)
    = (e @ es, (var_heap, expr_heap))
  refreshVariables` (Let lt) (var_heap, expr_heap)
    # (newPtr, expr_heap)                   = newPtr EI_Empty expr_heap
    # (strict_binds, (var_heap, expr_heap)) = mapSt refreshBind lt.let_strict_binds (var_heap, expr_heap)
    # (lazy_binds, (var_heap, expr_heap))   = mapSt refreshBind lt.let_lazy_binds (var_heap, expr_heap)
    # (e, (var_heap, expr_heap))            = refreshVariables` lt.let_expr (var_heap, expr_heap)
    = (Let {lt & let_strict_binds = strict_binds
               , let_lazy_binds   = lazy_binds
               , let_expr         = e
               , let_info_ptr     = newPtr }, (var_heap, expr_heap))
    where
    refreshBind lb (var_heap, expr_heap)
      # (fv, var_heap)               = refreshFreeVar lb.lb_dst var_heap
      # (rhs, (var_heap, expr_heap)) = refreshVariables` lb.lb_src (var_heap, expr_heap)
      = ({lb & lb_dst = fv
             , lb_src = rhs}, (var_heap, expr_heap))
  refreshVariables` (Case cs) (var_heap, expr_heap)
    # (newPtr, expr_heap)                   = newPtr EI_Empty expr_heap
    # (case_expr, (var_heap, expr_heap))    = refreshVariables` cs.case_expr (var_heap, expr_heap)
    # (case_guards, (var_heap, expr_heap))  = refreshGuards cs.case_guards (var_heap, expr_heap)
    # (case_default, (var_heap, expr_heap)) = case cs.case_default of
                                                Yes e
                                                  # (e, (var_heap, expr_heap)) = refreshVariables` e (var_heap, expr_heap)
                                                  = (Yes e, (var_heap, expr_heap))
                                                _ = (No, (var_heap, expr_heap))
    = (Case {cs & case_expr = case_expr
                , case_guards = case_guards
                , case_default = case_default
                , case_info_ptr = newPtr}, (var_heap, expr_heap))
    where
    refreshGuards (AlgebraicPatterns idx as) (var_heap, expr_heap)
      # (as, (var_heap, expr_heap)) = mapSt refreshA as (var_heap, expr_heap)
      = (AlgebraicPatterns idx as, (var_heap, expr_heap))
    refreshGuards (BasicPatterns bt bs) (var_heap, expr_heap)
      # (bs, (var_heap, expr_heap)) = mapSt refreshB bs (var_heap, expr_heap)
      = (BasicPatterns bt bs, (var_heap, expr_heap))
    refreshGuards (NewTypePatterns idx as) (var_heap, expr_heap)
      # (as, (var_heap, expr_heap)) = mapSt refreshA as (var_heap, expr_heap)
      = (NewTypePatterns idx as, (var_heap, expr_heap))
    refreshGuards (DynamicPatterns ds) (var_heap, expr_heap)
      # (ds, (var_heap, expr_heap)) = mapSt refreshD ds (var_heap, expr_heap)
      = (DynamicPatterns ds, (var_heap, expr_heap))
    refreshGuards (OverloadedListPatterns ot e as) (var_heap, expr_heap)
      # (as, (var_heap, expr_heap)) = mapSt refreshA as (var_heap, expr_heap)
      = (OverloadedListPatterns ot e as, (var_heap, expr_heap))
    refreshA ap (var_heap, expr_heap)
      # (ap_vars, var_heap) = mapSt refreshFreeVar ap.ap_vars var_heap
      # (ap_expr, (var_heap, expr_heap)) = refreshVariables` ap.ap_expr (var_heap, expr_heap)
      = ({ap & ap_vars = ap_vars, ap_expr = ap_expr}, (var_heap, expr_heap))
    refreshB bp (var_heap, expr_heap)
      # (bp_expr, (var_heap, expr_heap)) = refreshVariables` bp.bp_expr (var_heap, expr_heap)
      = ({bp & bp_expr = bp_expr}, (var_heap, expr_heap))
    refreshD dp (var_heap, expr_heap)
      # (dp_rhs, (var_heap, expr_heap)) = refreshVariables` dp.dp_rhs (var_heap, expr_heap)
      = ({dp & dp_rhs = dp_rhs}, (var_heap, expr_heap))
  refreshVariables` (Selection sk e ss) (var_heap, expr_heap)
    # (e,  (var_heap, expr_heap)) = refreshVariables` e (var_heap, expr_heap)
    # (ss, (var_heap, expr_heap)) = mapSt refreshSelection ss (var_heap, expr_heap)
    = (Selection sk e ss, (var_heap, expr_heap))
  refreshVariables` (Update e1 ss e2) (var_heap, expr_heap)
    # (e1, (var_heap, expr_heap)) = refreshVariables` e1 (var_heap, expr_heap)
    # (ss, (var_heap, expr_heap)) = mapSt refreshSelection ss (var_heap, expr_heap)
    # (e2, (var_heap, expr_heap)) = refreshVariables` e2 (var_heap, expr_heap)
    = (Update e1 ss e2, (var_heap, expr_heap))
  refreshVariables` (RecordUpdate gds e bs) (var_heap, expr_heap)
    # (e, (var_heap, expr_heap))  = refreshVariables` e (var_heap, expr_heap)
    # (bs, (var_heap, expr_heap)) = mapSt refreshBind bs (var_heap, expr_heap)
    = (RecordUpdate gds e bs, (var_heap, expr_heap))
    where
    refreshBind bnd (var_heap, expr_heap)
      # (bnd_src, (var_heap, expr_heap)) = refreshVariables` bnd.bind_src (var_heap, expr_heap)
      = ({bnd & bind_src = bnd_src}, (var_heap, expr_heap))
  refreshVariables` (TupleSelect ds n e) (var_heap, expr_heap)
    # (e, (var_heap, expr_heap)) = refreshVariables` e (var_heap, expr_heap)
    = (TupleSelect ds n e, (var_heap, expr_heap))
  refreshVariables` (MatchExpr gds e) (var_heap, expr_heap)
    # (e, (var_heap, expr_heap)) = refreshVariables` e (var_heap, expr_heap)
    = (MatchExpr gds e, (var_heap, expr_heap))
  refreshVariables` (IsConstructor e gds n gi ident pos) (var_heap, expr_heap)
    # (e, (var_heap, expr_heap)) = refreshVariables` e (var_heap, expr_heap)
    = (IsConstructor e gds n gi ident pos, (var_heap, expr_heap))
  refreshVariables` (FreeVar fv) (var_heap, expr_heap)
    # (fv, var_heap)     = refreshFreeVar fv var_heap
    # (newPtr, var_heap) = readPtr fv.fv_info_ptr var_heap
    # newPtr             = case newPtr of
                             VI_ForwardClassVar newPtr -> newPtr
                             _                         -> abort "refreshVariables` (2)"
    = (FreeVar {fv & fv_info_ptr = newPtr}, (var_heap, expr_heap))
  refreshVariables` (DictionariesFunction as e aty) (var_heap, expr_heap)
    # (e, (var_heap, expr_heap)) = refreshVariables` e (var_heap, expr_heap)
    = (DictionariesFunction as e aty, (var_heap, expr_heap))

  refreshVariables` e (var_heap, expr_heap) = (e, (var_heap, expr_heap))

  refreshSelection (ArraySelection gds eip e) (var_heap, expr_heap)
    # (e, (var_heap, expr_heap)) = refreshVariables` e (var_heap, expr_heap)
    = (ArraySelection gds eip e, (var_heap, expr_heap))
  refreshSelection (DictionarySelection bv ss eip e) (var_heap, expr_heap)
    # (Var bv, (var_heap, expr_heap)) = refreshVariables` (Var bv) (var_heap, expr_heap)
    # (ss, (var_heap, expr_heap))     = mapSt refreshSelection ss (var_heap, expr_heap)
    # (e, (var_heap, expr_heap))      = refreshVariables` e (var_heap, expr_heap)
    = (DictionarySelection bv ss eip e, (var_heap, expr_heap))
  refreshSelection s (var_heap, expr_heap) = (s, (var_heap, expr_heap))

mkCaseDetFun :: !(Maybe FreeVar) !ExprId !Int ![BoundVar] !Expression !InhExpression !*ChnExpression -> *(Expression, *ChnExpression)
mkCaseDetFun mbindfv eid exprPtr boundArgs bdy inh chn
  # freeArgs           = map varToFreeVar boundArgs
  # freeArgs           = case mbindfv of
                           Just bindfv -> [arg \\ arg <- freeArgs | arg.fv_info_ptr <> bindfv.fv_info_ptr] ++ [bindfv]
                           _           -> freeArgs
  # name               = "_f_case_" +++ toString exprPtr
  # bdy`               = case bdy of
                           Case cs
                             = Case (tfCase eid cs)
                           Let lt=:{let_expr = Case cs}
                             = Let {lt & let_expr = Case (tfCase eid cs)}
                           _ = abort "mkCaseDetFun shouldn't happen"
  # (freeArgs, bdy`, chn) = refreshVariables freeArgs bdy` chn

  # arity              = length freeArgs
  # funIdent           = { id_name = name
                         , id_info = nilPtr
                         }
  # fun_defs           = chn.chn_fun_defs
  # (fun_def, fun_defs) = fun_defs![inh.inh_fun_idx]
  # groups             = chn.chn_groups
  # groups`            = [grp \\ grp <-: groups]
  # mainDclN           = chn.chn_main_dcl_module_n
  # (nextFD, fun_defs) = usize fun_defs
  # (argVars, localVars, freeVars) = collectVars bdy` freeArgs
  # newFunDef          = { fun_docs     = ""
                         , fun_pragmas  = []
                         , fun_ident    = funIdent
                         , fun_arity    = arity
                         , fun_priority = NoPrio
                         , fun_body     = TransformedBody { tb_args = argVars
                                                          , tb_rhs  = bdy` }
                         , fun_type     = No
                         , fun_pos      = NoPos
                         , fun_kind     = FK_Function cNameNotLocationDependent
                         , fun_lifted   = 0
                         , fun_info     = { fi_calls       = collectCalls mainDclN bdy`
                                          , fi_group_index = fun_def.fun_info.fi_group_index
                                          , fi_def_level   = NotALevel
                                          , fi_free_vars   = freeVars
                                          , fi_local_vars  = localVars
                                          , fi_dynamics    = []
                                          , fi_properties  = FI_IsNonRecursive
                                          }
                         }
  # funDefs            = [fd \\ fd <-: fun_defs] ++ [newFunDef]
  # fun_defs           = {{fd & fun_info = {fd.fun_info & fi_group_index = if (fd.fun_info.fi_group_index > fun_def.fun_info.fi_group_index) (fd.fun_info.fi_group_index + 1) fd.fun_info.fi_group_index}} \\ fd <- funDefs}
  # (lgrps, rgrps)     = splitAt fun_def.fun_info.fi_group_index groups`
  # group              = {group_members = [nextFD]}
  # groups             = {grp \\ grp <- lgrps ++ [group : rgrps]}
  # fun_def            = {fun_def & fun_info = {fun_def.fun_info & fi_calls = [FunCall nextFD NotALevel : fun_def.fun_info.fi_calls]}}
  # symb               = { symb_ident = funIdent
                         , symb_kind  = SK_Function { glob_module = mainDclN
                                                    , glob_object = nextFD }
                         }
  # fun_defs           = { fun_defs & [inh.inh_fun_idx] = fun_def}
  # chn                = {chn & chn_fun_defs = fun_defs
                              , chn_groups = groups}
  # heaps              = chn.chn_heaps
  # (ptr, expr_heap)   = newPtr EI_Empty heaps.hp_expression_heap
  # heaps              = { heaps & hp_expression_heap = expr_heap }
  # chn                = { chn & chn_heaps = heaps }
  # appArgs            = case mbindfv of
                           Just _ -> init boundArgs
                           _      -> boundArgs
  # app                = { app_symb     = symb
                         , app_args     = map Var appArgs
                         , app_info_ptr = ptr }

  # heaps               = chn.chn_heaps
  # pdss                = chn.chn_predef_symbols
  # (eidExpr, pdss)     = listToListExpr (map mkInt eid) pdss
  # (pair, heaps, pdss) = appPredefinedSymbolWithEI (GetTupleConsIndex 2)
                                [ eidExpr
                                , App app
                                ] SK_Constructor heaps pdss
  = (App pair, {chn & chn_heaps = heaps
                    , chn_predef_symbols = pdss })

wrapBody :: InhExpression SynExpression Bool *ChnExpression -> *(SynExpression, *ChnExpression)
wrapBody inh syn hasTonic chn
  # pdss       = chn.chn_predef_symbols
  # (ok, pdss) = pdssAreDefined [PD_tonicExtWrapArg, PD_tonicExtWrapBody] pdss
  # chn        = {chn & chn_predef_symbols = pdss}
  | not ok     = (syn, chn)
  | otherwise
      # fun_defs             = chn.chn_fun_defs
      # (fun_def, fun_defs)  = fun_defs![inh.inh_fun_idx]
      # chn                 = {chn & chn_fun_defs = fun_defs}
      # (mfdt, fun_defs_cpy) = muselect chn.chn_fun_defs_cpy inh.inh_fun_idx
      # chn                 = {chn & chn_fun_defs_cpy = fun_defs_cpy}
      = case mfdt of
          Just fdt
            = case (fun_def.fun_body, fdt.fun_type) of
                (TransformedBody fb, Yes symbty)
                  # (isPA, chn) = case syn.syn_annot_expr of
                                     App app -> isPartialApp app chn
                                     _       -> (False, chn)
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
    # (args, chn) = foldr (mkArg symbty hasTonic inh.inh_instance_tree) ([], chn) (zip2 tb_args symbty.st_args)
    | length args == length tb_args
        # evalableCases  = [(eid, 'DM'.elems vars, cs) \\ (eid, (True, vars, cs)) <- 'DM'.toList syn.syn_cases | allVarsBound inh vars]
        # (evalableCases, chn) = mapSt (\(eid, bvs, cs) chn -> mkCaseDetFun Nothing eid inh.inh_fun_idx bvs cs inh chn) evalableCases chn

        # (icl, chn) = chn!chn_icl_module
        # iclname = icl.icl_name.id_name
        # (rem, chn)  = case syn.syn_annot_expr of
                           App {app_symb = {symb_ident}}
                             | symb_ident == predefined_idents.[PD_tonicExtWrapBodyLam1] = (1, chn)
                             | symb_ident == predefined_idents.[PD_tonicExtWrapBodyLam2] = (2, chn)
                             | symb_ident == predefined_idents.[PD_tonicExtWrapBodyLam3] = (3, chn)
                           App app
                             = argsRemaining app chn
                           _ = (0, chn)
        # (xs, pdss) = toStatic args chn.chn_predef_symbols
        # (casesExpr, pdss) = listToListExpr evalableCases pdss
        //# (casesExpr, pdss) = listToListExpr [] pdss
        # (wrap, heaps, pdss) = appPredefinedSymbolWithEI (findBodyWrap rem)
                                  [ mkStr iclname
                                  , mkStr fun_ident.id_name
                                  , xs
                                  , casesExpr
                                  , syn.syn_annot_expr
                                  ] SK_Function chn.chn_heaps pdss
        = ({syn & syn_annot_expr = App wrap}, {chn & chn_heaps = heaps
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
    mkArg symty hasTonic class_instances (arg=:{fv_info_ptr, fv_ident}, {at_type}) (xs, chn)
      # pdss = chn.chn_predef_symbols
      # heaps = chn.chn_heaps
      # (itask_class_symbol, pdss) = pdss![PD_ITaskClass]
      # gtcClasses  = [gtc_class \\ {tc_class = TCGeneric {gtc_class}} <- common_defs.[itask_class_symbol.pds_module].com_class_defs.[itask_class_symbol.pds_def].class_context] 
      # (hasITasks, hp_type_heaps) = tyHasITaskClasses class_instances gtcClasses at_type heaps.hp_type_heaps
      # heaps         = {heaps & hp_type_heaps = hp_type_heaps}
      # (varNoCtx, pdss) = varNoITaskCtx arg symty.st_context pdss
      # (tvNoITaskCtxs, pdss) = mapSt (tvNoITaskCtx symty.st_context) (getTyVars at_type) pdss
      # tvNoITaskCtx  = or tvNoITaskCtxs
      # (bv, heaps)   = freeVarToVar arg heaps
      # (viewApp, heaps, pdss) = appPredefinedSymbolWithEI PD_tonicExtWrapArg
                                   [ mkStr fv_ident.id_name
                                   , mkInt (ptrToInt fv_info_ptr)
                                   , if (not hasTonic || (not hasITasks && (varNoCtx || tvNoITaskCtx)))
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

    varNoITaskCtx :: FreeVar [TypeContext] *PredefinedSymbols -> *(Bool, *PredefinedSymbols)
    varNoITaskCtx fv tcs pdss
      # (pds, pdss) = pdss![PD_ITaskClass]
      = ( isEmpty [0 \\ {tc_var, tc_class = (TCClass {glob_object, glob_module})} <- tcs
                      |  fv.fv_info_ptr == tc_var
                      && glob_module == pds.pds_module
                      && glob_object.ds_index == pds.pds_def]
        , pdss)
    tvNoITaskCtx :: [TypeContext] TypeVar *PredefinedSymbols -> *(Bool, *PredefinedSymbols)
    tvNoITaskCtx tcs tv pdss
      # (pds, pdss) = pdss![PD_ITaskClass]
      = ( isEmpty [0 \\ {tc_types = [ty], tc_class = (TCClass {glob_object, glob_module})} <- tcs
                      |  getTyVars ty == [tv]
                      && glob_module == pds.pds_module
                      && glob_object.ds_index == pds.pds_def]
        , pdss)

    getTyVars :: Type -> [TypeVar]
    getTyVars (TA _ atys) = concatMap getTyVars` atys
    getTyVars (TAS _ atys _) = concatMap getTyVars` atys
    getTyVars (l --> r) = getTyVars` l ++ getTyVars` r
    getTyVars (TArrow1 aty) = getTyVars` aty
    getTyVars (_ :@: atys) = concatMap getTyVars` atys
    getTyVars (TFA _ t) = getTyVars t
    getTyVars (GTV t) = [t]
    getTyVars (TV t) = [t]
    getTyVars (TLifted t) = [t]
    getTyVars (TQualifiedIdent _ _ atys) = concatMap getTyVars` atys
    getTyVars (TLiftedSubst t) = getTyVars t
    getTyVars _ = []

    getTyVars` :: AType -> [TypeVar]
    getTyVars` {at_type} = getTyVars at_type

instance == TypeVar where
  (==) l r = l.tv_info_ptr == r.tv_info_ptr

instance == (Global a) | == a where
  (==) g1 g2 = g1.glob_module == g2.glob_module && g1.glob_object == g2.glob_object

instance toString IdentOrQualifiedIdent where
  toString (Ident ident) = ident.id_name
  toString (QualifiedIdent _ str) = str
