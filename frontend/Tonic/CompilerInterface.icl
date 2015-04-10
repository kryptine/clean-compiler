implementation module Tonic.CompilerInterface

import Tonic.Util
import Tonic.GraphGen
import Tonic.Pretty
//import Tonic.Tonic
import syntax, checksupport, compile, unitype
from overloading import :: InstanceTree (..), find_instance
import StdFile
from CoclSystemDependent import DirectorySeparator, ensureCleanSystemFilesExists
import Text
import Data.Func
import Data.Functor
import Data.Graph
import Data.Maybe
import Data.Map
import Text.JSON
import iTasks.Framework.Tonic.AbsSyn

ginTonic :: String ModuleN !*{#FunDef} !*{#FunDef} IclModule {#DclModule} !{#CommonDefs} [(String, ParsedExpr)] !*PredefinedSymbols !{#{!InstanceTree}} *HashTable !*File !*Files !*Heaps -> *(!*{#FunDef}, !*PredefinedSymbols, *HashTable, !*File, !*Files, !*Heaps)
ginTonic mod_dir main_dcl_module_n fun_defs fun_defs_cpy icl_module dcl_modules common_defs list_comprehensions predef_symbols class_instances hash_table error files heaps
// FIXME Start Tonic presence check hack
  # (tonic_module, predef_symbols) = predef_symbols![PD_iTasks_Framework_Tonic]
  | predefIsUndefined tonic_module = (fun_defs, predef_symbols, hash_table, error, files, heaps)
  # tonicImp = [0 \\ Declaration imp <-: icl_module.icl_import | imp.decl_ident.id_name == predefined_idents.[PD_tonicWrapTaskBody].id_name]
  | tonicImp == [] = (fun_defs, predef_symbols, hash_table, error, files, heaps)
// FIXME End Tonic presence check hack
  # iclname                        = icl_module.icl_name.id_name
  | isSystemModule iclname         = (fun_defs, predef_symbols, hash_table, error, files, heaps)
  # (tstr, fun_defs, predef_symbols, heaps) = ginTonic` (isITasksModule iclname) main_dcl_module_n fun_defs fun_defs_cpy icl_module dcl_modules common_defs list_comprehensions predef_symbols class_instances heaps
  # (error, files)                 = writeTonicFile mod_dir iclname tstr error files
  = (fun_defs, predef_symbols, hash_table, error, files, heaps)
  where
  isITasksModule nm = startsWith "iTasks" nm
  isSystemModule nm = foldr (\x b -> startsWith x nm || b) False sysmods
    where sysmods = [ "Sapl", "sapl"
                    , "Std", "_", "graph_to_", "dynamic_string", "tcp", "ostcp"
                    , "GenLexOrd", "GenEq"
                    , "Control", "Crypto", "Data", "Database", "Deprecated"
                    , "Email", "Graphics.Scalable", "GUI", "Internet", "Math"
                    , "Network", "System", "TCP", "Test", "Text"
                    ]
  writeTonicFile :: String String String *File *Files -> *(*File, *Files)
  writeTonicFile mod_dir iclname tstr error files
    | isITasksModule iclname  = (error, files)
    | otherwise
        # targetDir              = mod_dir +++ {DirectorySeparator} +++ "tonic"
        # (ok, files)            = ensureCleanSystemFilesExists targetDir files
        | not ok                 = (error, files)
        # targetFile             = targetDir +++ {DirectorySeparator} +++ iclname +++ ".tonic"
        # (ok, tonicFile, files) = fopen targetFile FWriteData files
        | not ok                 = (error, files)
        # tonicFile              = fwrites tstr tonicFile
        # (_, files)             = fclose tonicFile files
        = (error, files)

openTonicFile :: !String !String !*File !*Files -> (!Bool, !Optional .File, !*File, !*Files)
openTonicFile mod_dir mod_name error files
  = open_file_in_clean_system_files_folder mod_dir mod_name ".tonic" FWriteData error files

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
import StdDebug
ginTonic` :: Bool ModuleN !*{#FunDef} !*{#FunDef} IclModule {#DclModule}
             !{#CommonDefs} [(String, ParsedExpr)] !*PredefinedSymbols
             !{#{!InstanceTree}} *Heaps
          -> *(String, !*{#FunDef}, !*PredefinedSymbols, !*Heaps)
ginTonic` is_itasks_mod main_dcl_module_n fun_defs fun_defs_cpy icl_module dcl_modules common_defs list_comprehensions predef_symbols class_instances heaps
  # ((reps, heaps, predef_symbols, fun_defs_cpy), fun_defs) = foldUArr appDefInfo ((newMap, heaps, predef_symbols, fun_defs_cpy), fun_defs)
  # menv        = mkModuleEnv main_dcl_module_n fun_defs fun_defs_cpy icl_module dcl_modules
  # (str, menv) = toJSONString reps icl_module menv
  = (str, menv.me_fun_defs, predef_symbols, heaps)
  where
  // fd does not always have a fun_type = Yes
  appDefInfo idx fd ((reps, heaps, predef_symbols, fun_defs_cpy), fun_defs)
    # (fd_cpy, fun_defs_cpy) = fun_defs_cpy![idx]
    # menv = mkModuleEnv main_dcl_module_n fun_defs fun_defs_cpy icl_module dcl_modules
    | (not is_itasks_mod) && funIsTask fd_cpy
      # (mres, menv, heaps, predef_symbols) = funToGraph fd fd_cpy list_comprehensions menv heaps predef_symbols
      # menv = case mres of
                 Just (_, _, e)
                   -> updateWithAnnot idx e menv
                 _ -> menv
      # (menv, heaps, predef_symbols) = addTonicWrap is_itasks_mod icl_module class_instances idx menv heaps predef_symbols common_defs
      = ((case mres of
            Just (args, g, _)
              -> put fd.fun_ident.id_name { TonicTask
                                          | tt_module = icl_module.icl_name.id_name
                                          , tt_name   = fd.fun_ident.id_name
                                          , tt_resty  = fromMaybe (PPCleanExpr "") (fmap typeToTCleanExpr (functorContent (funTy fd_cpy)))
                                          , tt_args   = args
                                          , tt_body   = g} reps
            _ -> reps
        , heaps, predef_symbols, menv.me_fun_defs_cpy), menv.me_fun_defs)
    | otherwise = ((reps, heaps, predef_symbols, fun_defs_cpy), fun_defs)


updateWithAnnot :: Int Expression *ModuleEnv -> *ModuleEnv
updateWithAnnot fidx e menv
  # fun_defs = menv.me_fun_defs
  # fun_defs = updateFunRhs fidx fun_defs e
  = { menv & me_fun_defs = fun_defs}

addTonicWrap :: Bool IclModule {#{!InstanceTree}} Index *ModuleEnv !*Heaps *PredefinedSymbols !{#CommonDefs} -> *(*ModuleEnv, *Heaps, *PredefinedSymbols)
addTonicWrap is_itasks_mod icl_module class_instances idx menv heaps pdss common_defs
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
                (TransformedBody fb, Yes symbty)
                  # (isPA, menv) = case fb.tb_rhs of
                                     App app -> isPartialApp app menv
                                     _       -> (False, menv)
                  = if isPA (menv, heaps, pdss) (doAddRefl fdnt symbty menv heaps pdss common_defs)
                _ = (menv, heaps, pdss)
          _ = (menv, heaps, pdss)
  where
  doAddRefl {fun_ident, fun_body=TransformedBody { tb_args, tb_rhs }} symbty menv heaps pdss common_defs
    # (ok, pdss) = pdssAreDefined [ PD_tonicViewInformation
                                  , PD_tonicWrapTaskBody
                                  , PD_tonicWrapTaskBodyLam1
                                  , PD_tonicWrapTaskBodyLam2
                                  , PD_tonicWrapTaskBodyLam3
                                  , PD_ConsSymbol
                                  , PD_NilSymbol] pdss
    | not ok     = (menv, heaps, pdss)
    # (args, heaps, pdss, menv) = foldr (mkArg symbty is_itasks_mod class_instances) ([], heaps, pdss, menv) (zip2 tb_args symbty.st_args)
    | length args == length tb_args
        # (rem, menv)  = case tb_rhs of
                           App {app_symb = {symb_ident}}
                            | symb_ident == predefined_idents.[PD_tonicWrapAppLam1] = (1, menv)
                            | symb_ident == predefined_idents.[PD_tonicWrapAppLam2] = (2, menv)
                            | symb_ident == predefined_idents.[PD_tonicWrapAppLam3] = (3, menv)
                           App app
                             = argsRemaining app menv
                           _ = (0, menv)
        # (xs, pdss) = toStatic args pdss
        # (wrap, heaps, pdss) = appPredefinedSymbolWithEI (findBodyWrap rem)
                                  [ mkStr icl_module.icl_name.id_name
                                  , mkStr fun_ident.id_name
                                  , xs
                                  , tb_rhs
                                  ] SK_Function heaps pdss
        # fun_defs = updateFunRhs idx menv.me_fun_defs (App wrap)
        = ({ menv & me_fun_defs = fun_defs}, heaps, pdss)
    | otherwise = (menv, heaps, pdss)
    where
    findBodyWrap :: Int -> Int
    findBodyWrap 0 = PD_tonicWrapTaskBody
    findBodyWrap 1 = PD_tonicWrapTaskBodyLam1
    findBodyWrap 2 = PD_tonicWrapTaskBodyLam2
    findBodyWrap 3 = PD_tonicWrapTaskBodyLam3
    findBodyWrap n = abort ("No PD_tonicWrapTaskBodyLam" +++ toString n)

    mkArg :: SymbolType Bool {#{!InstanceTree}} (FreeVar, AType) ([Expression], *Heaps, *PredefinedSymbols, *ModuleEnv) -> *([Expression], *Heaps, *PredefinedSymbols, *ModuleEnv)
    mkArg symty is_itasks_mod class_instances (arg=:{fv_ident}, {at_type}) (xs, heaps, pdss, menv)
      # (pds, pdss) = pdss![PD_ITaskClass]
      # gtcClasses  = [gtc_class \\ {tc_class = TCGeneric {gtc_class}} <- common_defs.[pds.pds_module].com_class_defs.[pds.pds_def].class_context] 
      # (hasITasks, hp_type_heaps) = tyHasITaskClasses class_instances gtcClasses at_type heaps.hp_type_heaps
      # heaps         = {heaps & hp_type_heaps = hp_type_heaps}
      # (noCtx, pdss) = noITaskCtx arg symty.st_context pdss
      # (bv, heaps)   = freeVarToVar arg heaps
      # (viewApp, heaps, pdss) = appPredefinedSymbolWithEI PD_tonicViewInformation
                                   [ mkStr fv_ident.id_name
                                   , if (is_itasks_mod || (not hasITasks && noCtx))
                                       (mkStr fv_ident.id_name)
                                       (Var bv)
                                   ] SK_Function heaps pdss
      # (texpr, pdss) = toStatic (mkStr fv_ident.id_name, App viewApp) pdss
      = ([texpr:xs], heaps, pdss, menv)
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
  doAddRefl _ _ menv heaps pdss _ = (menv, heaps, pdss)

instance == (Global a) | == a where
  (==) g1 g2 = g1.glob_module == g2.glob_module && g1.glob_object == g2.glob_object

instance toString IdentOrQualifiedIdent where
  toString (Ident ident) = ident.id_name
  toString (QualifiedIdent _ str) = str
