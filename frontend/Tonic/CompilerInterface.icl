implementation module Tonic.CompilerInterface

import Tonic.Util
//import Tonic.GraphGen
import Tonic.Tonic
import syntax, checksupport, StdFile
from CoclSystemDependent import DirectorySeparator, ensureCleanSystemFilesExists
import Text
import Data.Func
import Data.Graph
import Data.Maybe

//from Text.PPrint import class Pretty(..), instance Pretty [a], :: Doc
//import qualified Text.PPrint as PP

//import Data.Func, Data.Functor, Data.Graph, Data.Maybe, Text
//from Data.List import zipWith
//import StdDebug

ginTonic :: IclModule {#DclModule} *FrontendTuple !*Files -> *(*FrontendTuple, !*Files)
ginTonic icl_module dcl_modules tpl files
  # iclname                = icl_module.icl_name.id_name
  | isSystemModule iclname = (tpl, files)
  # (ok, files)            = ensureCleanSystemFilesExists csf_directory_path files
  # (ok, tonicf, files)    = fopen (csf_directory_path +++ {DirectorySeparator} +++ ("tonic-" +++ iclname +++ ".dot")) FWriteText files
  # (tstr, tpl)            = ginTonic` icl_module dcl_modules tpl
  //| True = abort tstr
  # tonicf                 = fwrites tstr tonicf
  # (ok, files)            = fclose tonicf files
  = (tpl, files)
  where
  csf_directory_path = "Clean System Files"
  isSystemModule nm = isSystemModule` ["iTasks", "Std", "_"]
    where isSystemModule` = foldr (\x b -> startsWith x nm || b) False

ginTonic` :: IclModule {#DclModule} *FrontendTuple -> *(String, *FrontendTuple)
ginTonic` icl_module dcl_modules tpl=:(ok, fun_defs, array_instances, common_defs, imported_funs, type_def_infos, heaps, predef_symbols, error,out)
  = (mkDotGraph $ foldrArr appDefInfo "" fun_defs, tpl)
  where
  appDefInfo fd rest
    | funIsTask fd && fd.fun_info.fi_def_level == 1  = defToStr fd +++ "\n" +++ rest
    | otherwise                                      = rest
  defToStr fd  = optional "Nothing happened" f (funToGraph fd fun_defs icl_module dcl_modules)
    where f g  = mkTaskDot (mkModuleEnv fun_defs icl_module dcl_modules) fd.fun_ident.id_name g
  mkDotGraph subgraphs = "digraph " +++ icl_module.icl_name.id_name +++ "{\n" +++ subgraphs +++ "\n}"


