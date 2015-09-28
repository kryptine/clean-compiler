implementation module Tonic.CompilerInterface

import Tonic.Util
import Tonic.GraphGen
import Tonic.Pretty
import syntax, checksupport, compile, unitype, generics1
from overloading import :: InstanceTree (..), find_instance
import StdFile
from CoclSystemDependent import DirectorySeparator, ensureCleanSystemFilesExists
import Text
import Data.Array
import Data.Func
import Data.Functor
import Data.Graph
import Data.Maybe
import Data.List
import qualified Data.Map as DM
import qualified Data.Set as DS
import Text.JSON
import iTasks._Framework.Tonic.AbsSyn
import System.Directory
import System.OSError
import System.FilePath
import Data.Error

import StdDebug

ginTonic :: ScannedModule String ModuleN !*{#FunDef} !*{#FunDef} !{!Group} IclModule {#DclModule} !{#CommonDefs} [(String, ParsedExpr)] !*PredefinedSymbols !{#{!InstanceTree}} *HashTable !*File !*Files !*Heaps
         -> *(!*{#FunDef}, !*PredefinedSymbols, !{!Group}, *HashTable, !*File, !*Files, !*Heaps)
ginTonic mod mod_dir main_dcl_module_n fun_defs fun_defs_cpy groups icl_module dcl_modules common_defs list_comprehensions predef_symbols class_instances hash_table error files heaps
  | icl_module.icl_name == predefined_idents.[PD_iTasks_Framework_Tonic] = (fun_defs, predef_symbols, groups, hash_table, error, files, heaps)
  # (tonic_module, predef_symbols) = predef_symbols![PD_iTasks_Framework_Tonic]
  | predefIsUndefined tonic_module = (fun_defs, predef_symbols, groups, hash_table, error, files, heaps)
  # hasTonic                   = [0 \\ {import_module} <- mod.mod_imports | import_module.id_name == predefined_idents.[PD_iTasks_Framework_Tonic].id_name] <> []
  # (tonicFiles, files)        = readTonicFiles mod_dir files
  # tonicFiles                 = [icl_module.icl_name.id_name : tonicFiles]
  # ((reps, heaps, predef_symbols, groups, fun_defs_cpy), fun_defs) = foldrUArrWithKey (appDefInfo hasTonic tonicFiles) ('DM'.newMap, heaps, predef_symbols, groups, fun_defs_cpy) fun_defs
  # (error, files)             = if (hasTonic && not ('DM'.null reps))
                                   (writeTonicFile hasTonic mod_dir icl_module.icl_name.id_name (toString (toJSON { TonicModule
                                                                                                                  | tm_name  = icl_module.icl_name.id_name
                                                                                                                  , tm_funcs = reps})) error files)
                                   (error, files)
  = (fun_defs, predef_symbols, groups, hash_table, error, files, heaps)
  where
  // fd does not always have a fun_type = Yes
  appDefInfo hasTonic tonicFiles idx fd=:{fun_pos,fun_ident=fun_ident, fun_body = TransformedBody tb} (reps, heaps, predef_symbols, groups, fun_defs_cpy) fun_defs
    # (fd_cpy, fun_defs_cpy) = fun_defs_cpy![idx]
    # inh             = mkInhExpr idx list_comprehensions class_instances common_defs tonicFiles
    # chn             = mkChnExpr main_dcl_module_n fun_defs fun_defs_cpy groups icl_module dcl_modules predef_symbols heaps
    # (argTys, tyenv) = zipWithSt (\arg t st -> ((arg, t), 'DM'.put (ptrToInt arg.fv_info_ptr) (t, funContext fd) st)) tb.tb_args (funArgTys fd_cpy) 'DM'.newMap
    # (isTopLeveLBlueprint, chn) = funIsTopLevelBlueprint fd_cpy inh chn
    | hasTonic && isTopLeveLBlueprint
      # inh        = {inh & inh_tyenv = tyenv}
      # (syn, chn) = mkBlueprint inh tb.tb_rhs chn
      # (syn, chn) = wrapBody inh syn hasTonic chn
      # chn        = updateWithAnnot idx syn.syn_annot_expr inh chn
      # args       = map (\(arg, ty) -> (mkArgPP syn.syn_pattern_match_vars arg, typeToTCleanExpr ty)) argTys
      = (('DM'.put fd.fun_ident.id_name { TonicFunc
                                        | tf_comments  = fd.fun_docs
                                        , tf_module    = icl_module.icl_name.id_name
                                        , tf_name      = fd.fun_ident.id_name
                                        , tf_iclLineNo = mkFunPos fun_pos
                                        , tf_resty     = typeToTCleanExpr (funTy fd_cpy)
                                        , tf_args      = args
                                        , tf_body      = syn.syn_texpr} reps
        , chn.chn_heaps, chn.chn_predef_symbols, chn.chn_groups, chn.chn_fun_defs_cpy), chn.chn_fun_defs)
    | not hasTonic && isTopLeveLBlueprint
      # args = map (\(arg, ty) -> (mkArgPP [] arg, typeToTCleanExpr ty)) argTys
      = (('DM'.put fd.fun_ident.id_name { TonicFunc
                                        | tf_comments  = fd.fun_docs
                                        , tf_module    = icl_module.icl_name.id_name
                                        , tf_name      = fd.fun_ident.id_name
                                        , tf_iclLineNo = mkFunPos fun_pos
                                        , tf_resty     = typeToTCleanExpr (funTy fd_cpy)
                                        , tf_args      = args
                                        , tf_body      = TLit (TString "Unable to capture function body")} reps
        , chn.chn_heaps, chn.chn_predef_symbols, chn.chn_groups, chn.chn_fun_defs_cpy), chn.chn_fun_defs)
    | otherwise
      = ((reps, chn.chn_heaps, chn.chn_predef_symbols, chn.chn_groups, chn.chn_fun_defs_cpy), chn.chn_fun_defs)
  appDefInfo _ _ _ _ (reps, heaps, predef_symbols, groups, fun_defs_cpy) fun_defs = ((reps, heaps, predef_symbols, groups, fun_defs_cpy), fun_defs)

  mkFunPos (FunPos _ n _) = n
  mkFunPos (LinePos _ n)  = n
  mkFunPos _              = -1

  mkArgPP pmvars arg
    = case arg.fv_ident.id_name of
        "_x"
          = case [clexpr \\ (bv, clexpr) <- pmvars | bv.var_info_ptr == arg.fv_info_ptr] of
              []    -> TPPExpr "(shouldn't happen)"
              [x:_] -> x
        idnm
          = TVar [] idnm (ptrToInt arg.FreeVar.fv_info_ptr)

  writeTonicFile :: Bool String String String *File *Files -> *(*File, *Files)
  writeTonicFile hasTonic mod_dir iclname tstr error files
    # targetDir              = mkTargetDir mod_dir
    # (ok, files)            = ensureCleanSystemFilesExists targetDir files
    | not ok                 = (error, files)
    # targetFile             = targetDir +++ {DirectorySeparator} +++ iclname +++ ".tonic"
    # (ok, tonicFile, files) = fopen targetFile FWriteData files
    | not ok                 = (error, files)
    # tonicFile              = fwrites tstr tonicFile
    # (_, files)             = fclose tonicFile files
    = (error, files)

  // TODO FIXME: Simply reading Tonic files in the current directory isn't
  // sufficient. Tonic files may be located elsewhere on the filesystem as
  // well. We need to find them using the compiler's include path.
  readTonicFiles :: String *Files -> *([String], *Files)
  readTonicFiles mod_dir files
    # (mfs, files) = readDirectory (mkTargetDir mod_dir) files
    = case mfs of
        Ok fs -> (map (dropDots o dropExtension) fs, files)
        _     -> ([], files)

  dropDots :: String -> String
  dropDots str
    | size str > 0 && str.[0] == '.' = dropDots (str % (1, size str))
    | otherwise = str

  mkTargetDir mod_dir = mod_dir +++ {DirectorySeparator} +++ "tonic"
