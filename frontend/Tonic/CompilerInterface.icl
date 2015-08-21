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

ginTonic :: String ModuleN !*{#FunDef} !*{#FunDef} !{!Group} IclModule {#DclModule} !{#CommonDefs} [(String, ParsedExpr)] !*PredefinedSymbols !{#{!InstanceTree}} *HashTable !*File !*Files !*Heaps -> *(!*{#FunDef}, !*PredefinedSymbols, !{!Group}, *HashTable, !*File, !*Files, !*Heaps)
ginTonic mod_dir main_dcl_module_n fun_defs fun_defs_cpy groups icl_module dcl_modules common_defs list_comprehensions predef_symbols class_instances hash_table error files heaps
// FIXME Start Tonic presence check hack
  # (tonic_module, predef_symbols) = predef_symbols![PD_iTasks_Framework_Tonic]
  | predefIsUndefined tonic_module = (fun_defs, predef_symbols, groups, hash_table, error, files, heaps)
  # tonicImp = [0 \\ Declaration imp <-: icl_module.icl_import | imp.decl_ident.id_name == predefined_idents.[PD_tonicExtWrapBody].id_name]
  | tonicImp == [] = (fun_defs, predef_symbols, groups, hash_table, error, files, heaps)
// FIXME End Tonic presence check hack
  # iclname                        = icl_module.icl_name.id_name
  | isSystemModule iclname         = (fun_defs, predef_symbols, groups, hash_table, error, files, heaps)
  # (tstr, fun_defs, groups, predef_symbols, heaps) = ginTonic` (isITasksModule iclname) main_dcl_module_n fun_defs fun_defs_cpy groups icl_module dcl_modules common_defs list_comprehensions predef_symbols class_instances heaps
  # (error, files)                 = writeTonicFile mod_dir iclname tstr error files
  = (fun_defs, predef_symbols, groups, hash_table, error, files, heaps)
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

toJSONString :: (Map String TonicFunc) IclModule *ChnExpression -> *(String, *ChnExpression)
toJSONString rs icl_module chn
  = (toString $ toJSON { TonicModule
                       | tm_name  = icl_module.icl_name.id_name
                       , tm_funcs = rs}
    , chn)
import StdDebug

ginTonic` :: Bool ModuleN !*{#FunDef} !*{#FunDef} !{!Group} IclModule {#DclModule}
             !{#CommonDefs} [(String, ParsedExpr)] !*PredefinedSymbols
             !{#{!InstanceTree}} *Heaps
          -> *(String, !*{#FunDef}, !{!Group}, !*PredefinedSymbols, !*Heaps)
ginTonic` is_itasks_mod main_dcl_module_n fun_defs fun_defs_cpy groups icl_module dcl_modules common_defs list_comprehensions predef_symbols class_instances heaps
  # ((reps, heaps, predef_symbols, groups, fun_defs_cpy), fun_defs) = foldrUArrWithKey appDefInfo ('DM'.newMap, heaps, predef_symbols, groups, fun_defs_cpy) fun_defs
  # chn        = mkChnExpr main_dcl_module_n fun_defs fun_defs_cpy groups icl_module dcl_modules predef_symbols heaps
  # (str, chn) = toJSONString reps icl_module chn
  = (str, chn.chn_fun_defs, chn.chn_groups, chn.chn_predef_symbols, chn.chn_heaps)
  where
  // fd does not always have a fun_type = Yes
  appDefInfo idx fd=:{fun_pos,fun_ident=fun_ident, fun_body = TransformedBody tb} (reps, heaps, predef_symbols, groups, fun_defs_cpy) fun_defs
    # (fd_cpy, fun_defs_cpy) = fun_defs_cpy![idx]
    # inh             = mkInhExpr idx list_comprehensions class_instances common_defs
    # chn             = mkChnExpr main_dcl_module_n fun_defs fun_defs_cpy groups icl_module dcl_modules predef_symbols heaps
    # (argTys, tyenv) = zipWithSt (\arg t st -> ((arg, t), 'DM'.put (ptrToInt arg.fv_info_ptr) (t, funContext fd) st)) tb.tb_args (funArgTys fd_cpy) 'DM'.newMap
    # (isTopLeveLBlueprint, chn) = funIsTopLevelBlueprint fd_cpy inh chn
    | (not is_itasks_mod) && isTopLeveLBlueprint
      # inh        = {inh & inh_tyenv = tyenv}
      # (syn, chn) = mkBlueprint inh tb.tb_rhs chn
      # (syn, chn) = wrapBody inh syn is_itasks_mod chn
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
    //| is_itasks_mod && isTopLeveLBlueprint
      //# args = map (\(arg, ty) -> (mkArgPP [] arg, typeToTCleanExpr ty)) argTys
      //= (('DM'.put fd.fun_ident.id_name { TonicTask
                                        //| tt_comments  = fd.fun_docs
                                        //, tt_module    = icl_module.icl_name.id_name
                                        //, tt_name      = fd.fun_ident.id_name
                                        //, tt_iclLineNo = mkFunPos fun_pos
                                        //, tt_resty     = typeToTCleanExpr (funTy fd_cpy)
                                        //, tt_args      = args
                                        //, tt_body      = TLit "Internal iTasks function"} reps
        //, chn.chn_heaps, chn.chn_predef_symbols, chn.chn_fun_defs_cpy), chn.chn_fun_defs)
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

