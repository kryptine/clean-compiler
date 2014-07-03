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
import Data.Graph
import Data.Maybe
import Data.Map
import Text.JSON
import iTasks.Framework.Tonic.AbsSyn

ginTonic :: ModuleN !*{#FunDef} IclModule {#DclModule} !{#CommonDefs} !*PredefinedSymbols !*Files !*Heaps -> *(!*{#FunDef}, !*PredefinedSymbols, !*Files, !*Heaps)
ginTonic main_dcl_module_n fun_defs icl_module dcl_modules common_defs predef_symbols files heaps
  # iclname                                 = icl_module.icl_name.id_name
  | isSystemModule iclname                  = (fun_defs, predef_symbols, files, heaps)
  # (ok, files)                             = ensureDirectoryExists csf_directory_path files
  | not ok                                  = (fun_defs, predef_symbols, files, heaps)
  # (tstr, fun_defs, predef_symbols, heaps) = ginTonic` (isITasksModule iclname) main_dcl_module_n toJSONString fun_defs icl_module dcl_modules common_defs predef_symbols heaps
  # files                                   = writeTonicFile iclname tstr files
  = (fun_defs, predef_symbols, files, heaps)
  where
  csf_directory_path = "tonic"
  isITasksModule nm = startsWith "iTasks" nm
  isSystemModule nm = foldr (\x b -> startsWith x nm || b) False sysmods
    where sysmods = [ "Sapl"
                    , "Std", "_"
                    , "Control", "Crypto", "Data", "Database", "Deprecated"
                    , "GUI", "Internet", "Math", "Network", "System", "TCP"
                    , "Test", "Text"
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

toDotString :: (Map String TonicTask) IclModule *ModuleEnv -> *(String, *ModuleEnv)
toDotString rs icl_module menv
  # (dots, menv) = foldrWithKey tf ([], menv) rs
  = ( "digraph " +++ icl_module.icl_name.id_name +++ "{\n" +++ foldr (\x str -> x +++ "\n" +++ str) "" dots +++ "\n}"
    , menv)
  where tf tn {tt_graph=g} (xs, menv)
          # (dot, menv) = mkTaskDot tn g menv
          = ([dot : xs], menv)

ginTonic` :: Bool ModuleN ((Map String TonicTask) IclModule *ModuleEnv -> *(String, *ModuleEnv))
             !*{#FunDef} IclModule {#DclModule} !{#CommonDefs} !*PredefinedSymbols *Heaps
          -> *(String, !*{#FunDef}, !*PredefinedSymbols, !*Heaps)
ginTonic` is_itasks_mod main_dcl_module_n repsToString fun_defs icl_module dcl_modules common_defs predef_symbols heaps
  # ((reps, heaps, predef_symbols), fun_defs) = foldUArr appDefInfo ((newMap, heaps, predef_symbols), fun_defs)
  # menv                                      = mkModuleEnv main_dcl_module_n fun_defs icl_module dcl_modules
  # (str, menv)                               = repsToString reps icl_module menv
  = (str, menv.me_fun_defs, predef_symbols, heaps)
  where
  appDefInfo idx fd ((reps, heaps, predef_symbols), fun_defs)
    | not is_itasks_mod && funIsTask fd && fd.fun_info.fi_def_level == 1
      # menv = mkModuleEnv main_dcl_module_n fun_defs icl_module dcl_modules
      # ((args, mg, me), menv, heaps, predef_symbols) = funToGraph fd menv heaps predef_symbols
      # menv = updateWithAnnot idx me menv
      # (menv, predef_symbols) = addTonicWrap icl_module idx menv predef_symbols
      = (( case mg of
             Just g -> put fd.fun_ident.id_name {TonicTask | tt_name = fd.fun_ident.id_name, tt_resty = ppType (funTy fd), tt_args = args, tt_graph = g} reps
             _      -> reps
        , heaps, predef_symbols), menv.me_fun_defs)
    // TODO FIXME There are still some problems with this when compiling iTasks itself
    //| is_itasks_mod && funIsTask fd && fd.fun_info.fi_def_level == 1
      //# menv = mkModuleEnv main_dcl_module_n fun_defs icl_module dcl_modules
      //# menv = addTonicWrap icl_module idx menv
      //= ((reps, heaps), menv.me_fun_defs)
    | otherwise        = ((reps, heaps, predef_symbols), fun_defs)

updateWithAnnot :: Int (Maybe Expression) *ModuleEnv -> *ModuleEnv
updateWithAnnot fidx (Just e) menv
  # fun_defs = menv.me_fun_defs
  # fun_defs = updateFunRhs fidx fun_defs e
  = { menv & me_fun_defs = fun_defs}
updateWithAnnot _ _ menv = menv

addTonicWrap :: IclModule Index *ModuleEnv *PredefinedSymbols -> *(*ModuleEnv, *PredefinedSymbols)
addTonicWrap icl_module idx menv pdss
  # (tonicWrapTask, pdss) = pdss![PD_tonicWrapTaskBody]
  | predefIsUndefined tonicWrapTask = (menv, pdss)
  | otherwise
      # (mfd, fun_defs) = muselect menv.me_fun_defs idx
      # menv            = {menv & me_fun_defs = fun_defs}
      = case mfd of
          Just fd
            = case (fd.fun_body, fd.fun_type) of
                (TransformedBody fb, Yes _)
                  # (isPA, menv) = case fb.tb_rhs of
                                     App app -> isPartialApp app menv
                                     // TODO Add a case for @ ?
                                     _       -> (False, menv)
                  = if isPA (menv, pdss) (doAddRefl fd menv pdss)
                _ = (menv, pdss)
          _ = (menv, pdss)
  where
  doAddRefl {fun_ident, fun_body=TransformedBody { tb_args, tb_rhs }, fun_type=Yes symbty} menv pdss
    # fun_defs    = menv.me_fun_defs
    //# args = symbty.st_args
    # (args, pdss) = foldr mkArg ([], pdss) (zip2 tb_args symbty.st_args)
    # (xs, pdss)   = toStatic args pdss
    # (dict, pdss) = appPredefinedSymbol (luDict ("tonicTaskDict" +++ ppType symbty.st_result.at_type)) [] SK_Function pdss
    # (wrap, pdss) = appPredefinedSymbol PD_tonicWrapTaskBody
                       [ mkStr icl_module.icl_name.id_name
                       , mkStr fun_ident.id_name
                       , xs
                       , App dict
                       , tb_rhs
                       ] SK_Function pdss
    # fun_defs    = updateFunRhs idx fun_defs (App wrap)
    = ({ menv & me_fun_defs = fun_defs}, pdss)
    where
    mkArg (arg=:{fv_ident}, {at_type}) (xs, pdss)
      # (viewApp, pdss) = appPredefinedSymbol (luPD ("tonicViewInformation" +++ ppType at_type))
                            [ Var (freeVarToVar arg)
                            ] SK_Function pdss
      # (texpr, pdss) = toStatic (mkStr fv_ident.id_name, App viewApp) pdss
      = ([texpr:xs], pdss)
      where
      luPD "tonicViewInformationEmergency"     = PD_tonicViewInformationEmergency
      luPD "tonicViewInformationCallInfo"      = PD_tonicViewInformationCallInfo
      luPD "tonicViewInformationAddress"       = PD_tonicViewInformationAddress
      luPD "tonicViewInformationAuthority"     = PD_tonicViewInformationAuthority
      luPD "tonicViewInformationPhoneNo"       = PD_tonicViewInformationPhoneNo
      luPD "tonicViewInformationVerdict"       = PD_tonicViewInformationVerdict
      luPD "tonicViewInformation_ListVerdict"  = PD_tonicViewInformation_ListVerdict
      luPD "tonicViewInformationTaskEmergency" = PD_tonicViewInformationTaskEmergency
      luPD "tonicViewInformationDateTime"      = PD_tonicViewInformationDateTime
      luPD str = abort ("luPD " +++ str)

    luDict "tonicTaskDictTaskEmergency"     = PD_tonicTaskDictTaskEmergency
    luDict "tonicTaskDictTaskCallInfo"      = PD_tonicTaskDictTaskCallInfo
    luDict "tonicTaskDictTaskAddress"       = PD_tonicTaskDictTaskAddress
    luDict "tonicTaskDictTaskAuthority"     = PD_tonicTaskDictTaskAuthority
    luDict "tonicTaskDictTaskPhoneNo"       = PD_tonicTaskDictTaskPhoneNo
    luDict "tonicTaskDictTaskVerdict"       = PD_tonicTaskDictTaskVerdict
    luDict "tonicTaskDictTask_ListVerdict"  = PD_tonicTaskDictTask_ListVerdict
    luDict "tonicTaskDictTaskTaskEmergency" = PD_tonicTaskDictTaskTaskEmergency
    luDict "tonicTaskDictTaskDateTime"      = PD_tonicTaskDictTaskDateTime
    luDict "tonicTaskDictTask_Unit"         = PD_tonicTaskDictTask_Unit
    luDict str = abort ("luDict " +++ str)
  doAddRefl _ menv pdss = (menv, pdss)
