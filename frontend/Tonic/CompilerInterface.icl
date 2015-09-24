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

import StdDebug
ginTonic :: ScannedModule String ModuleN !*{#FunDef} !*{#FunDef} !{!Group} IclModule {#DclModule} !{#CommonDefs} [(String, ParsedExpr)] !*PredefinedSymbols !{#{!InstanceTree}} *HashTable !*File !*Files !*Heaps -> *(!*{#FunDef}, !*PredefinedSymbols, !{!Group}, *HashTable, !*File, !*Files, !*Heaps)
ginTonic mod mod_dir main_dcl_module_n fun_defs fun_defs_cpy groups icl_module dcl_modules common_defs list_comprehensions predef_symbols class_instances hash_table error files heaps
  | icl_module.icl_name == predefined_idents.[PD_iTasks_Framework_Tonic] = (fun_defs, predef_symbols, groups, hash_table, error, files, heaps)
  # (tonic_module, predef_symbols) = predef_symbols![PD_iTasks_Framework_Tonic]
  | predefIsUndefined tonic_module = (fun_defs, predef_symbols, groups, hash_table, error, files, heaps)
  # tonicImp = [0 \\  {import_module} <- mod.mod_imports | import_module.id_name == predefined_idents.[PD_iTasks_Framework_Tonic].id_name]
  # hasTonic = tonicImp <> []
  # (reps, fun_defs, groups, predef_symbols, heaps) = ginTonic` hasTonic main_dcl_module_n fun_defs fun_defs_cpy groups icl_module dcl_modules common_defs list_comprehensions predef_symbols class_instances heaps
  # (error, files) = if ('DM'.null reps)
                       (error, files)
                       (writeTonicFile hasTonic mod_dir icl_module.icl_name.id_name (toJSONString reps icl_module) error files)
  = (fun_defs, predef_symbols, groups, hash_table, error, files, heaps)
  where
  writeTonicFile :: Bool String String String *File *Files -> *(*File, *Files)
  writeTonicFile hasTonic mod_dir iclname tstr error files
    | not hasTonic = (error, files)
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

toJSONString :: (Map String TonicFunc) IclModule -> String
toJSONString rs icl_module
  = toString $ toJSON { TonicModule
                      | tm_name  = icl_module.icl_name.id_name
                      , tm_funcs = rs}

ginTonic` :: Bool ModuleN !*{#FunDef} !*{#FunDef} !{!Group} IclModule {#DclModule}
             !{#CommonDefs} [(String, ParsedExpr)] !*PredefinedSymbols
             !{#{!InstanceTree}} *Heaps
          -> *(Map String TonicFunc, !*{#FunDef}, !{!Group}, !*PredefinedSymbols, !*Heaps)
ginTonic` hasTonic main_dcl_module_n fun_defs fun_defs_cpy groups icl_module dcl_modules common_defs list_comprehensions predef_symbols class_instances heaps
  # ((reps, heaps, predef_symbols, groups, fun_defs_cpy), fun_defs) = foldrUArrWithKey appDefInfo ('DM'.newMap, heaps, predef_symbols, groups, fun_defs_cpy) fun_defs
  # chn = mkChnExpr main_dcl_module_n fun_defs fun_defs_cpy groups icl_module dcl_modules predef_symbols heaps
  = (reps, chn.chn_fun_defs, chn.chn_groups, chn.chn_predef_symbols, chn.chn_heaps)
  where
  // fd does not always have a fun_type = Yes
  appDefInfo idx fd=:{fun_pos,fun_ident=fun_ident, fun_body = TransformedBody tb} (reps, heaps, predef_symbols, groups, fun_defs_cpy) fun_defs
    # (fd_cpy, fun_defs_cpy) = fun_defs_cpy![idx]
    # inh             = mkInhExpr idx list_comprehensions class_instances common_defs
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
                                        , tf_body      = TLit (TString "Internal iTasks function")} reps
        , chn.chn_heaps, chn.chn_predef_symbols, chn.chn_groups, chn.chn_fun_defs_cpy), chn.chn_fun_defs)
    | otherwise
      = ((reps, chn.chn_heaps, chn.chn_predef_symbols, chn.chn_groups, chn.chn_fun_defs_cpy), chn.chn_fun_defs)
  appDefInfo _ _ (reps, heaps, predef_symbols, groups, fun_defs_cpy) fun_defs = ((reps, heaps, predef_symbols, groups, fun_defs_cpy), fun_defs)
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

