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
  # (tstr, fun_defs, predef_symbols, heaps) = ginTonic` (isITasksModule iclname) main_dcl_module_n toTikzString fun_defs icl_module dcl_modules common_defs predef_symbols heaps
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

toTikzString :: (Map String TonicTask) IclModule *ModuleEnv -> *(String, *ModuleEnv)
toTikzString rs icl_module menv
  # (tikzs, menv) = foldrWithKey tf ([], menv) rs
  = (foldr (\x str -> x +++ "\n\n" +++ str) "" tikzs, menv)
  where
  tf tn {tt_args, tt_graph} (xs, menv)
    # (tikz, menv) = mkTaskTikz tn tt_args tt_graph menv
    = ([tikz : xs], menv)
  tikzPicture str = "\\begin{tikzpicture}\n" +++ str +++ "\n\\end{tikzpicture}"
  tikzDef str [] bdy = "\tonicdefnoarg{td}{0,0}{$\mbox{" +++ str +++ "}$}"
  tikzDef str xs bdy = "\tonicdef{td}{0,0}{$\mbox{" +++ str +++ "}$}{" +++ foldr (\x xs -> x +++ "\n" xs) "" xs +++ "}"

mkTaskTikz :: String [String] GinGraph *ModuleEnv -> *(String, *ModuleEnv)
mkTaskTikz tn args g menv = (tn +++ " " +++ (foldr (+++) "" args), menv)

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
  # (tonicWrap, predef_symbols)               = predef_symbols![PD_tonicWrapTask]
  # ((reps, heaps, predef_symbols), fun_defs) = foldUArr (appDefInfo tonicWrap) ((newMap, heaps, predef_symbols), fun_defs)
  # menv                                      = mkModuleEnv main_dcl_module_n fun_defs icl_module dcl_modules
  # (str, menv)                               = repsToString reps icl_module menv
  = (str, menv.me_fun_defs, predef_symbols, heaps)
  where
  appDefInfo tonicWrap idx fd ((reps, heaps, predef_symbols), fun_defs)
    | not is_itasks_mod && funIsTask fd && fd.fun_info.fi_def_level == 1
      # menv = mkModuleEnv main_dcl_module_n fun_defs icl_module dcl_modules
      # ((args, mg, me), menv, heaps, predef_symbols) = funToGraph fd menv heaps predef_symbols
      # menv = updateWithAnnot idx me menv
      # (menv, predef_symbols) = addTonicWrap icl_module idx tonicWrap menv predef_symbols
      = (( case mg of
             Just g -> put fd.fun_ident.id_name {TonicTask | tt_args = args, tt_graph = g} reps
             _      -> reps
        , heaps, predef_symbols), menv.me_fun_defs)
    // TODO FIXME There are still some problems with this when compiling iTasks itself
    //| is_itasks_mod && funIsTask fd && fd.fun_info.fi_def_level == 1
      //# menv = mkModuleEnv main_dcl_module_n fun_defs icl_module dcl_modules
      //# menv = addTonicWrap icl_module idx tonicWrap menv
      //= ((reps, heaps), menv.me_fun_defs)
    | otherwise        = ((reps, heaps, predef_symbols), fun_defs)

updateWithAnnot :: Int (Maybe Expression) *ModuleEnv -> *ModuleEnv
updateWithAnnot fidx (Just e) menv
  # fun_defs = menv.me_fun_defs
  # fun_defs = updateFunRhs fidx fun_defs e
  = { menv & me_fun_defs = fun_defs}
updateWithAnnot _ _ menv = menv

addTonicWrap :: IclModule Index PredefinedSymbol *ModuleEnv *PredefinedSymbols -> *(*ModuleEnv, *PredefinedSymbols)
addTonicWrap icl_module idx tonic_wraptask menv pdss
  | predefIsUndefined tonic_wraptask = (menv, pdss)
  | otherwise
      # (mfd, fun_defs) = muselect menv.me_fun_defs idx
      # menv            = {menv & me_fun_defs = fun_defs}
      = case mfd of
          Just fd
            = case fd.fun_body of
                TransformedBody fb
                  # (isPA, menv)   = case fb.tb_rhs of
                                       App app -> isPartialApp app menv
                                       // TODO Add a case for @ ?
                                       _       -> (False, menv)
                  = if isPA (menv, pdss) (doAddRefl fd fb menv pdss)
                _ = (menv, pdss)
          _ = (menv, pdss)
  where
  addTonicWrap` fd { tb_args, tb_rhs } pdss
    # (args, pdss) = foldr mkArgs ([], pdss) tb_args
    # (xs, pdss) = listToListExpr args pdss
    = (App (appPredefinedSymbol "tonicWrapTask" tonic_wraptask
              [ mkStr icl_module.icl_name.id_name
              , mkStr fd.fun_ident.id_name
              , xs
              , tb_rhs
              ]), pdss)
    where
    mkArgs arg=:{fv_ident} (xs, pdss)
      # (texpr, pdss) = tupleToTupleExpr (mkStr fv_ident.id_name, FreeVar arg) pdss
      = ([texpr:xs], pdss)

  doAddRefl fd fb menv pdss
    # fun_defs    = menv.me_fun_defs
    # (app, pdss) = addTonicWrap` fd fb pdss
    # fun_defs    = updateFunRhs idx fun_defs app
    = ({ menv & me_fun_defs = fun_defs}, pdss)
