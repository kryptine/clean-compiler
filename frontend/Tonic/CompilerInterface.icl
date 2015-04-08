implementation module Tonic.CompilerInterface

import Tonic.Util
import Tonic.GraphGen
import Tonic.Pretty
//import Tonic.Tonic
import syntax, checksupport, compile, StdFile
from CoclSystemDependent import DirectorySeparator, ensureCleanSystemFilesExists
import Text
import Data.Func
import Data.Functor
import Data.Graph
import Data.Maybe
import Data.Map
import Text.JSON
import iTasks.Framework.Tonic.AbsSyn

ginTonic :: String ModuleN !*{#FunDef} !*{#FunDef} IclModule {#DclModule} !{#CommonDefs} [(String, ParsedExpr)] !*PredefinedSymbols *HashTable !*File !*Files !*Heaps -> *(!*{#FunDef}, !*PredefinedSymbols, *HashTable, !*File, !*Files, !*Heaps)
ginTonic mod_dir main_dcl_module_n fun_defs fun_defs_cpy icl_module dcl_modules common_defs list_comprehensions predef_symbols hash_table error files heaps
// FIXME Start Tonic presence check hack
  # (tonic_module, predef_symbols) = predef_symbols![PD_iTasks_Framework_Tonic]
  | predefIsUndefined tonic_module = (fun_defs, predef_symbols, hash_table, error, files, heaps)
  # tonicImp = [0 \\ Declaration imp <-: icl_module.icl_import | imp.decl_ident.id_name == predefined_idents.[PD_tonicWrapTaskBody].id_name]
  | tonicImp == [] = (fun_defs, predef_symbols, hash_table, error, files, heaps)
// FIXME End Tonic presence check hack
  # iclname                        = icl_module.icl_name.id_name
  | isSystemModule iclname         = (fun_defs, predef_symbols, hash_table, error, files, heaps)
  # (tstr, fun_defs, predef_symbols, heaps) = ginTonic` (isITasksModule iclname) main_dcl_module_n fun_defs fun_defs_cpy icl_module dcl_modules common_defs list_comprehensions predef_symbols heaps
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
             !{#CommonDefs} [(String, ParsedExpr)] !*PredefinedSymbols *Heaps
          -> *(String, !*{#FunDef}, !*PredefinedSymbols, !*Heaps)
ginTonic` is_itasks_mod main_dcl_module_n fun_defs fun_defs_cpy icl_module dcl_modules common_defs list_comprehensions predef_symbols heaps
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
      # (menv, heaps, predef_symbols) = addTonicWrap is_itasks_mod icl_module idx menv heaps predef_symbols common_defs
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

addTonicWrap :: Bool IclModule Index *ModuleEnv !*Heaps *PredefinedSymbols !{#CommonDefs} -> *(*ModuleEnv, *Heaps, *PredefinedSymbols)
addTonicWrap is_itasks_mod icl_module idx menv heaps pdss common_defs
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
    # (args, heaps, pdss, menv) = foldr (mkArg symbty is_itasks_mod) ([], heaps, pdss, menv) (zip2 tb_args symbty.st_args)
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

    mkArg :: SymbolType Bool (FreeVar, AType) ([Expression], *Heaps, *PredefinedSymbols, *ModuleEnv) -> *([Expression], *Heaps, *PredefinedSymbols, *ModuleEnv)
    mkArg symty is_itasks_mod (arg=:{fv_ident}, {at_type}) (xs, heaps, pdss, menv)
      # (bv, heaps)       = freeVarToVar arg heaps
      # (hasITasks, menv) = hasITaskInstance at_type menv
      # (viewApp, heaps, pdss) = appPredefinedSymbolWithEI PD_tonicViewInformation
                                   [ mkStr fv_ident.id_name
                                   , if (is_itasks_mod || (not hasITasks && noITaskCtx arg symty.st_context))
                                       (mkStr fv_ident.id_name)
                                       (Var bv)
                                   ] SK_Function heaps pdss
      # (texpr, pdss) = toStatic (mkStr fv_ident.id_name, App viewApp) pdss
      = ([texpr:xs], heaps, pdss, menv)
    hasITaskInstance :: Type *ModuleEnv -> *(Bool, *ModuleEnv)
    hasITaskInstance (TA tsi _)         menv = tsiHasITasks tsi menv
    hasITaskInstance (TAS tsi _ _)      menv = tsiHasITasks tsi menv
    hasITaskInstance (TB BT_Int)        menv = (True, menv)
    hasITaskInstance (TB BT_Char)       menv = (True, menv)
    hasITaskInstance (TB BT_Real)       menv = (True, menv)
    hasITaskInstance (TB BT_Bool)       menv = (True, menv)
    hasITaskInstance (TB (BT_String _)) menv = (True, menv)
    hasITaskInstance _                  menv = (False, menv)
    tsiHasITasks tsi=:{type_index = {glob_module, glob_object}} menv
      | glob_module == menv.me_main_dcl_module_n
         # cids = icl_module.icl_common.com_instance_defs
         = cidsHaveITasks tsi cids menv
      | otherwise
         # cids = common_defs.[glob_module].com_instance_defs
         = cidsHaveITasks tsi cids menv
    cidsHaveITasks tsi cids menv // FIXME This doesn't work for {#Char} and the likes yet...
      = case [() \\ {ClassInstance | ins_class_ident, ins_ident, ins_type = {it_types = [insTy:_]}} <-: cids | ins_ident.id_name == "gEditor_s" && tsisMatch insTy tsi] of
          [] -> (False, menv)
          //xs  -> (True, snd (mapSt (\x menv -> ((), trace_n x menv)) xs menv))
          _  -> (True, menv)
      where
      tsisMatch (TA tsi _)    tsi` = tsi.type_index == tsi`.type_index
      tsisMatch (TAS tsi _ _) tsi` = tsi.type_index == tsi`.type_index
      tsisMatch _             _    = False
    ctdHasITasks ctd menv
      = (False, menv)
    noITaskCtx :: FreeVar [TypeContext] -> Bool
    noITaskCtx fv tcs = isEmpty [tc \\ tc <- tcs | fv.fv_info_ptr == tc.tc_var && isITaskClass tc.tc_class]
    isITaskClass :: TCClass -> Bool
    isITaskClass (TCClass gds) = gds.glob_object.ds_ident.id_name == "iTask" // TODO Make this nicer
    isITaskClass _             = False
  doAddRefl _ _ menv heaps pdss _ = (menv, heaps, pdss)

instance == (Global a) | == a where
  (==) g1 g2 = g1.glob_module == g2.glob_module && g1.glob_object == g2.glob_object
import StdDebug
instance toString IdentOrQualifiedIdent where
  toString (Ident ident) = ident.id_name
  toString (QualifiedIdent _ str) = str
