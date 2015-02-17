implementation module Tonic.CompilerInterface

import Tonic.Util
import Tonic.GraphGen
import Tonic.Pretty
//import Tonic.Tonic
import syntax, checksupport, StdFile
from CoclSystemDependent import DirectorySeparator
from filesystem import ensureDirectoryExists
import Text
import Data.Func
import Data.Functor
import Data.Graph
import Data.Maybe
import Data.Map
import Text.JSON
import iTasks.Framework.Tonic.AbsSyn

ginTonic :: ModuleN !*{#FunDef} !*{#FunDef} IclModule {#DclModule} !{#CommonDefs} !*PredefinedSymbols *HashTable !*Files !*Heaps -> *(!*{#FunDef}, !*PredefinedSymbols, *HashTable, !*Files, !*Heaps)
ginTonic main_dcl_module_n fun_defs fun_defs_cpy icl_module dcl_modules common_defs predef_symbols hash_table files heaps
// FIXME Start Tonic presence check hack
  # (tonic_module, predef_symbols) = predef_symbols![PD_iTasks_Framework_Tonic]
  | predefIsUndefined tonic_module = (fun_defs, predef_symbols, hash_table, files, heaps)
  # tonicImp = [0 \\ Declaration imp <-: icl_module.icl_import | imp.decl_ident.id_name == predefined_idents.[PD_tonicWrapTaskBody].id_name]
  | tonicImp == [] = (fun_defs, predef_symbols, hash_table, files, heaps)
// FIXME End Tonic presence check hack
  # iclname                        = icl_module.icl_name.id_name
  | isSystemModule iclname         = (fun_defs, predef_symbols, hash_table, files, heaps)
  # (ok, files)                    = ensureDirectoryExists csf_directory_path files
  | not ok                         = (fun_defs, predef_symbols, hash_table, files, heaps)
  # (tstr, fun_defs, predef_symbols, heaps) = ginTonic` (isITasksModule iclname) main_dcl_module_n fun_defs fun_defs_cpy icl_module dcl_modules common_defs predef_symbols heaps
  # files                                   = writeTonicFile iclname tstr files
  = (fun_defs, predef_symbols, hash_table, files, heaps)
  where
  csf_directory_path = "tonic"
  isITasksModule nm = startsWith "iTasks" nm
  isSystemModule nm = foldr (\x b -> startsWith x nm || b) False sysmods
    where sysmods = [ "Sapl", "sapl"
                    , "Std", "_", "graph_to_", "dynamic_string", "tcp", "ostcp"
                    , "GenLexOrd", "GenEq"
                    , "Control", "Crypto", "Data", "Database", "Deprecated"
                    , "Email", "Graphics.Scalable", "GUI", "Internet", "Math"
                    , "Network", "System", "TCP", "Test", "Text"
                    ]
  writeTonicFile iclname tstr files
    | isITasksModule iclname  = files
    | otherwise
        # (ok, tonicf, files) = fopen (csf_directory_path +++ {DirectorySeparator} +++ iclname +++ ".tonic") FWriteText files
        | not ok              = files
        # tonicf              = fwrites tstr tonicf
        # (_, files)          = fclose tonicf files
        = files

foldUArr :: (Int a v:(w:b, u:(arr a)) -> v:(w:b, u:(arr a))) v:(w:b, u:(arr a))
         -> v:(w:b, u:(arr a)) | Array arr a, [v <= u, v <= w]
foldUArr f (b, arr)
  # (sz, arr) = usize arr
  = foldUArr` sz 0 b arr
  where foldUArr` sz idx b arr
          | idx < sz
              #! (elem, arr) = uselect arr idx
              #! (res, arr)  = foldUArr` sz (idx + 1) b arr
              = f idx elem (res, arr)
          | otherwise = (b, arr)

toJSONString :: (Map String TonicTask) IclModule *ModuleEnv -> *(String, *ModuleEnv)
toJSONString rs icl_module menv
  = (toString $ toJSON { TonicModule
                       | tm_name  = icl_module.icl_name.id_name
                       , tm_tasks = rs}
    , menv)

ginTonic` :: Bool ModuleN !*{#FunDef} !*{#FunDef} IclModule {#DclModule}
             !{#CommonDefs} !*PredefinedSymbols *Heaps
          -> *(String, !*{#FunDef}, !*PredefinedSymbols, !*Heaps)
ginTonic` is_itasks_mod main_dcl_module_n fun_defs fun_defs_cpy icl_module dcl_modules common_defs predef_symbols heaps
  # ((reps, heaps, predef_symbols, fun_defs_cpy), fun_defs) = foldUArr appDefInfo ((newMap, heaps, predef_symbols, fun_defs_cpy), fun_defs)
  # menv        = mkModuleEnv main_dcl_module_n fun_defs fun_defs_cpy icl_module dcl_modules
  # (str, menv) = toJSONString reps icl_module menv
  = (str, menv.me_fun_defs, predef_symbols, heaps)
  where
  appDefInfo idx fd ((reps, heaps, predef_symbols, fun_defs_cpy), fun_defs)
    # menv = mkModuleEnv main_dcl_module_n fun_defs fun_defs_cpy icl_module dcl_modules
    | not is_itasks_mod && funIsTask fd && fd.fun_info.fi_def_level == 1
      # (mres, menv, heaps, predef_symbols) = funToGraph fd menv heaps predef_symbols
      # menv = case mres of
                 Just (_, _, e)
                   -> updateWithAnnot idx e menv
                 _ -> menv
      # (menv, heaps, predef_symbols) = addTonicWrap icl_module idx menv heaps predef_symbols
      = ((case mres of
            Just (args, g, _)
              -> put fd.fun_ident.id_name {TonicTask | tt_name = fd.fun_ident.id_name, tt_resty = fromMaybe "" (fmap (ppCompact o ppType) (functorContent (funTy fd))), tt_args = args, tt_body = g} reps
            _ -> reps
        , heaps, predef_symbols, menv.me_fun_defs_cpy), menv.me_fun_defs)
    | is_itasks_mod && funIsTask fd && fd.fun_info.fi_def_level == 1
      # (menv, heaps, predef_symbols) = addTonicWrap icl_module idx menv heaps predef_symbols
      = ((reps, heaps, predef_symbols, menv.me_fun_defs_cpy), menv.me_fun_defs)
    | otherwise = ((reps, heaps, predef_symbols, fun_defs_cpy), fun_defs)

updateWithAnnot :: Int Expression *ModuleEnv -> *ModuleEnv
updateWithAnnot fidx e menv
  # fun_defs = menv.me_fun_defs
  # fun_defs = updateFunRhs fidx fun_defs e
  = { menv & me_fun_defs = fun_defs}

addTonicWrap :: IclModule Index *ModuleEnv !*Heaps *PredefinedSymbols -> *(*ModuleEnv, *Heaps, *PredefinedSymbols)
addTonicWrap icl_module idx menv heaps pdss
  # (ok, pdss) = pdssAreDefined [PD_tonicViewInformation, PD_tonicWrapTaskBody] pdss
  | not ok     = (menv, heaps, pdss)
  | otherwise
      # (mfdnt, fun_defs)    = muselect menv.me_fun_defs idx
      # menv                 = {menv & me_fun_defs = fun_defs}
      # (mfdt, fun_defs_cpy) = muselect menv.me_fun_defs_cpy idx
      # menv                 = {menv & me_fun_defs_cpy = fun_defs_cpy}
      = case (mfdnt, mfdt) of
          (Just fdnt, Just fdt)
            = case (fdnt.fun_body, fdt.fun_type) of
                (TransformedBody fb, Yes _)
                  # (isPA, menv) = case fb.tb_rhs of
                                     App app -> isPartialApp app menv
                                     // TODO Add a case for @ ?
                                     _       -> (False, menv)
                  = if isPA (menv, heaps, pdss) (doAddRefl fdnt fdt.fun_type menv heaps pdss)
                _ = (menv, heaps, pdss)
          _ = (menv, heaps, pdss)
  where
  doAddRefl {fun_ident, fun_body=TransformedBody { tb_args, tb_rhs }} (Yes symbty) menv heaps pdss
    # (ok, pdss) = pdssAreDefined [PD_tonicViewInformation, PD_tonicWrapTaskBody, PD_ConsSymbol, PD_NilSymbol] pdss
    | not ok     = (menv, heaps, pdss)
    # fun_defs   = menv.me_fun_defs
    # (args, heaps, pdss) = foldr mkArg ([], heaps, pdss) (zip2 tb_args symbty.st_args)
    | length args == length tb_args
        # (xs, pdss)  = toStatic args pdss
        # (wrap, heaps, pdss) = appPredefinedSymbolWithEI PD_tonicWrapTaskBody
                                  [ mkStr icl_module.icl_name.id_name
                                  , mkStr fun_ident.id_name
                                  , xs
                                  , tb_rhs
                                  ] SK_Function heaps pdss
        # fun_defs     = updateFunRhs idx fun_defs (App wrap)
        = ({ menv & me_fun_defs = fun_defs}, heaps, pdss)
    | otherwise = (menv, heaps, pdss)
    where
    mkArg :: (FreeVar, AType) ([Expression], *Heaps, *PredefinedSymbols) -> *([Expression], *Heaps, *PredefinedSymbols)
    mkArg (arg=:{fv_ident}, {at_type}) (xs, heaps, pdss)
      # (bv, heaps) = freeVarToVar arg heaps
      # (viewApp, heaps, pdss) = appPredefinedSymbolWithEI PD_tonicViewInformation
                                   [ mkStr fv_ident.id_name
                                   , Var bv
                                   ] SK_Function heaps pdss
      # (texpr, pdss) = toStatic (mkStr fv_ident.id_name, App viewApp) pdss
      = ([texpr:xs], heaps, pdss)
  doAddRefl _ _ menv heaps pdss = (menv, heaps, pdss)
