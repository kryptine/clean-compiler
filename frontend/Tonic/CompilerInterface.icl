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

ginTonic :: !*{#FunDef} IclModule {#DclModule} !{#CommonDefs} !*PredefinedSymbols !*Files -> *(!*{#FunDef}, !*PredefinedSymbols, !*Files)
ginTonic fun_defs icl_module dcl_modules common_defs predef_symbols files
  # iclname                           = icl_module.icl_name.id_name
  | isSystemModule iclname            = (fun_defs, predef_symbols, files)
  # (ok, files)                       = ensureDirectoryExists csf_directory_path files
  | not ok                            = (fun_defs, predef_symbols, files)
  # (ok, tonicf, files)               = fopen (csf_directory_path +++ {DirectorySeparator} +++ iclname +++ ".tonic") FWriteText files
  | not ok                            = (fun_defs, predef_symbols, files)
  # (tstr, fun_defs, predef_symbols)  = ginTonic` toJSONString fun_defs icl_module dcl_modules common_defs predef_symbols
  # tonicf                            = fwrites tstr tonicf
  # (_, files)                        = fclose tonicf files
  = (fun_defs, predef_symbols, files)
  where
  csf_directory_path = "tonic"
  isSystemModule nm = foldr (\x b -> startsWith x nm || b) False sysmods
    where sysmods = [ "iTasks", "Sapl"
                    , "Std", "_"
                    , "Control", "Crypto", "Data", "Database", "Deprecated"
                    , "GUI", "Internet", "Math", "Network", "System", "Test"
                    , "Text"
                    ]

foldUArr :: (Int a v:(b, u:(arr a)) -> v:(b, u:(arr a))) v:(b, u:(arr a))
         -> v:(b, u:(arr a)) | Array arr a, [v <= u]
foldUArr f (b, arr)
  # (sz, arr) = usize arr
  = foldUArr` sz 0 b arr
  where foldUArr` sz idx b arr
          | idx < sz
              # (elem, arr) = uselect arr idx
              # (res, arr) = foldUArr` sz (idx + 1) b arr
              = f idx elem (res, arr)
          | otherwise = (b, arr)

toJSONString :: (Map String GinGraph) IclModule *ModuleEnv -> *(String, *ModuleEnv)
toJSONString rs icl_module menv
  = (toString $ toJSON { TonicModule
                       | tm_name  = icl_module.icl_name.id_name
                       , tm_tasks = rs}
    , menv)

toDotString :: (Map String GinGraph) IclModule *ModuleEnv -> *(String, *ModuleEnv)
toDotString rs icl_module menv
  # (dots, menv) = foldrWithKey tf ([], menv) rs
  = ( "digraph " +++ icl_module.icl_name.id_name +++ "{\n" +++ foldr (\x str -> x +++ "\n" +++ str) "" dots +++ "\n}"
    , menv)
  where tf tn g (xs, menv)
          # (dot, menv) = mkTaskDot tn g menv
          = ([dot : xs], menv)

ginTonic` :: ((Map String GinGraph) IclModule *ModuleEnv -> *(String, *ModuleEnv))
             !*{#FunDef} IclModule {#DclModule} !{#CommonDefs} !*PredefinedSymbols
          -> *(String, !*{#FunDef}, !*PredefinedSymbols)
ginTonic` repsToString fun_defs icl_module dcl_modules common_defs predef_symbols
  # (pds, predef_symbols)  = predef_symbols![PD_tonicTune]
  # (reps, fun_defs)       = foldUArr (appDefInfo pds) (newMap, fun_defs)
  # menv                   = mkModuleEnv fun_defs icl_module dcl_modules
  # (str, menv)            = repsToString reps icl_module menv
  = (str, menv.me_fun_defs, predef_symbols)
  where
  appDefInfo pds idx fd (reps, fun_defs)
    | funIsTask fd && fd.fun_info.fi_def_level == 1
      # menv             = mkModuleEnv fun_defs icl_module dcl_modules
      # ((mg, me), menv) = funToGraph pds fd menv
      # menv             = updateWithAnnot idx me menv
      = ( case mg of
            Just g -> put fd.fun_ident.id_name g reps
            _      -> reps
        , menv.me_fun_defs)
    | otherwise        = (reps, fun_defs)
