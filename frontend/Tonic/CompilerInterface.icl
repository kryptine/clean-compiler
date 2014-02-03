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
  # iclname                                  = icl_module.icl_name.id_name
  | isSystemModule iclname                   = (fun_defs, predef_symbols, files, heaps)
  # (ok, files)                              = ensureDirectoryExists csf_directory_path files
  | not ok                                   = (fun_defs, predef_symbols, files, heaps)
  # (ok, tonicf, files)                      = fopen (csf_directory_path +++ {DirectorySeparator} +++ iclname +++ ".tonic") FWriteText files
  | not ok                                   = (fun_defs, predef_symbols, files, heaps)
  # (tstr, fun_defs, predef_symbols, heaps)  = ginTonic` main_dcl_module_n toJSONString fun_defs icl_module dcl_modules common_defs predef_symbols heaps
  # tonicf                                   = fwrites tstr tonicf
  # (_, files)                               = fclose tonicf files
  = (fun_defs, predef_symbols, files, heaps)
  where
  csf_directory_path = "tonic"
  isSystemModule nm = foldr (\x b -> startsWith x nm || b) False sysmods
    where sysmods = [ "iTasks", "Sapl"
                    , "Std", "_"
                    , "Control", "Crypto", "Data", "Database", "Deprecated"
                    , "GUI", "Internet", "Math", "Network", "System", "TCP"
                    , "Test", "Text"
                    ]

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

ginTonic` :: ModuleN ((Map String TonicTask) IclModule *ModuleEnv -> *(String, *ModuleEnv))
             !*{#FunDef} IclModule {#DclModule} !{#CommonDefs} !*PredefinedSymbols *Heaps
          -> *(String, !*{#FunDef}, !*PredefinedSymbols, !*Heaps)
ginTonic` main_dcl_module_n repsToString fun_defs icl_module dcl_modules common_defs predef_symbols heaps
  # (pss, predef_symbols)        = usize predef_symbols
  # (tonicTune, predef_symbols)  = predef_symbols![PD_tonicTune]
  # (tonicBind, predef_symbols)  = predef_symbols![PD_tonicBind]
  # ((reps, heaps), fun_defs)    = foldUArr (appDefInfo tonicTune tonicBind) ((newMap, heaps), fun_defs)
  # menv                         = mkModuleEnv main_dcl_module_n fun_defs icl_module dcl_modules
  # (str, menv)                  = repsToString reps icl_module menv
  = (str, menv.me_fun_defs, predef_symbols, heaps)
  where
  appDefInfo tonicTune tonicBind idx fd ((reps, heaps), fun_defs)
    | funIsTask fd && fd.fun_info.fi_def_level == 1
      # menv                          = mkModuleEnv main_dcl_module_n fun_defs icl_module dcl_modules
      # ((args, mg, me), menv, heaps) = funToGraph tonicTune tonicBind fd menv heaps
      # menv                          = updateWithAnnot idx me menv
      = ( (case mg of
            Just g -> put fd.fun_ident.id_name {TonicTask | tt_args = args, tt_graph = g} reps
            _      -> reps
        , heaps), menv.me_fun_defs)
    | otherwise        = ((reps, heaps), fun_defs)

updateWithAnnot :: Int (Maybe Expression) *ModuleEnv -> *ModuleEnv
updateWithAnnot fidx (Just e) menv
  # fun_defs = menv.me_fun_defs
  # fun_defs = updateFunRhs fidx fun_defs e
  = { menv & me_fun_defs = fun_defs}
updateWithAnnot _ _ menv = menv

