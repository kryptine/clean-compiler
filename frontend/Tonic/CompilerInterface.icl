implementation module Tonic.CompilerInterface

import Tonic.Util
import Tonic.GraphGen
import Tonic.Pretty
import syntax, checksupport, compile, unitype
from overloading import :: InstanceTree (..), find_instance
import StdFile
from CoclSystemDependent import DirectorySeparator, ensureCleanSystemFilesExists
import Text
import Data.Func
import Data.Functor
import Data.Graph
import Data.Maybe
import Data.List
import qualified Data.Map as DM
import qualified Data.Set as DS
import Text.JSON
import iTasks._Framework.Tonic.AbsSyn

ginTonic :: String ModuleN !*{#FunDef} !*{#FunDef} IclModule {#DclModule} !{#CommonDefs} [(String, ParsedExpr)] !*PredefinedSymbols !{#{!InstanceTree}} *HashTable !*File !*Files !*Heaps -> *(!*{#FunDef}, !*PredefinedSymbols, *HashTable, !*File, !*Files, !*Heaps)
ginTonic mod_dir main_dcl_module_n fun_defs fun_defs_cpy icl_module dcl_modules common_defs list_comprehensions predef_symbols class_instances hash_table error files heaps
// FIXME Start Tonic presence check hack
  # (tonic_module, predef_symbols) = predef_symbols![PD_iTasks_Framework_Tonic]
  | predefIsUndefined tonic_module = (fun_defs, predef_symbols, hash_table, error, files, heaps)
  # tonicImp = [0 \\ Declaration imp <-: icl_module.icl_import | imp.decl_ident.id_name == predefined_idents.[PD_tonicExtWrapBody].id_name]
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

toJSONString :: (Map String TonicFunc) IclModule *ModuleEnv -> *(String, *ModuleEnv)
toJSONString rs icl_module menv
  = (toString $ toJSON { TonicModule
                       | tm_name  = icl_module.icl_name.id_name
                       , tm_funcs = rs}
    , menv)
import StdDebug
ginTonic` :: Bool ModuleN !*{#FunDef} !*{#FunDef} IclModule {#DclModule}
             !{#CommonDefs} [(String, ParsedExpr)] !*PredefinedSymbols
             !{#{!InstanceTree}} *Heaps
          -> *(String, !*{#FunDef}, !*PredefinedSymbols, !*Heaps)
ginTonic` is_itasks_mod main_dcl_module_n fun_defs fun_defs_cpy icl_module dcl_modules common_defs list_comprehensions predef_symbols class_instances heaps
  # ((reps, heaps, predef_symbols, fun_defs_cpy), fun_defs) = foldUArr appDefInfo (('DM'.newMap, heaps, predef_symbols, fun_defs_cpy), fun_defs)
  # menv        = mkModuleEnv main_dcl_module_n fun_defs fun_defs_cpy icl_module dcl_modules
  # (str, menv) = toJSONString reps icl_module menv
  = (str, menv.me_fun_defs, predef_symbols, heaps)
  where
  // fd does not always have a fun_type = Yes
  appDefInfo idx fd=:{fun_pos,fun_ident=fun_ident, fun_body = TransformedBody tb} ((reps, heaps, predef_symbols, fun_defs_cpy), fun_defs)
    # (fd_cpy, fun_defs_cpy) = fun_defs_cpy![idx]
    # inh         = mkInhExpr list_comprehensions class_instances common_defs
    # menv        = mkModuleEnv main_dcl_module_n fun_defs fun_defs_cpy icl_module dcl_modules
    # chn         = mkChnExpr predef_symbols menv heaps
    # (argTys, tyenv) = zipWithSt (\arg t st -> ((arg, t), 'DM'.put arg.fv_ident.id_name t st)) tb.tb_args (funArgTys fd_cpy) 'DM'.newMap
    # (isTopLeveLBlueprint, chn) = funIsTopLevelBlueprint fd_cpy inh chn
    | (not is_itasks_mod) && isTopLeveLBlueprint
      # (syn, chn) = mkBlueprint {inh & inh_tyenv = tyenv} tb.tb_rhs chn
      # menv       = updateWithAnnot idx syn.syn_annot_expr chn.chn_module_env
      # chn        = {chn & chn_module_env = menv}
      # chn        = addTonicWrap is_itasks_mod icl_module class_instances idx common_defs chn
      # menv       = chn.chn_module_env
      # args       = map (\(arg, ty) -> (mkArgPP syn.syn_pattern_match_vars arg, typeToTCleanExpr ty)) argTys
      = (('DM'.put fd.fun_ident.id_name { TonicFunc
                                        | tf_comments  = fd.fun_docs
                                        , tf_module    = icl_module.icl_name.id_name
                                        , tf_name      = fd.fun_ident.id_name
                                        , tf_iclLineNo = mkFunPos fun_pos
                                        , tf_resty     = typeToTCleanExpr (funTy fd_cpy)
                                        , tf_args      = args
                                        , tf_body      = syn.syn_texpr} reps
        , chn.chn_heaps, chn.chn_predef_symbols, menv.me_fun_defs_cpy), menv.me_fun_defs)
    //| is_itasks_mod && isTopLeveLBlueprint
      //# menv = chn.chn_module_env
      //# args = map (\(arg, ty) -> (mkArgPP [] arg, typeToTCleanExpr ty)) argTys
      //= (('DM'.put fd.fun_ident.id_name { TonicTask
                                        //| tt_comments  = fd.fun_docs
                                        //, tt_module    = icl_module.icl_name.id_name
                                        //, tt_name      = fd.fun_ident.id_name
                                        //, tt_iclLineNo = mkFunPos fun_pos
                                        //, tt_resty     = typeToTCleanExpr (funTy fd_cpy)
                                        //, tt_args      = args
                                        //, tt_body      = TLit "Internal iTasks function"} reps
        //, chn.chn_heaps, chn.chn_predef_symbols, menv.me_fun_defs_cpy), menv.me_fun_defs)
    | otherwise
      # menv = chn.chn_module_env
      = ((reps, chn.chn_heaps, chn.chn_predef_symbols, menv.me_fun_defs_cpy), menv.me_fun_defs)
  appDefInfo _ _ ((reps, heaps, predef_symbols, fun_defs_cpy), fun_defs) = ((reps, heaps, predef_symbols, fun_defs_cpy), fun_defs)
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

updateWithAnnot :: Int Expression *ModuleEnv -> *ModuleEnv
updateWithAnnot fidx e menv
  # fun_defs = menv.me_fun_defs
  # fun_defs = updateFunRhs fidx fun_defs e
  = { menv & me_fun_defs = fun_defs}

addTonicWrap :: Bool IclModule {#{!InstanceTree}} Index !{#CommonDefs} *ChnExpression -> *ChnExpression
addTonicWrap is_itasks_mod icl_module class_instances idx common_defs chn
  # pdss = chn.chn_predef_symbols
  # (ok, pdss) = pdssAreDefined [PD_tonicExtWrapArg, PD_tonicExtWrapBody] pdss
  # chn = {chn & chn_predef_symbols = pdss}
  | not ok     = chn
  | otherwise
      # menv = chn.chn_module_env
      # (mfdnt, fun_defs)    = muselect menv.me_fun_defs idx
      # menv                 = {menv & me_fun_defs = fun_defs}
      # (mfdt, fun_defs_cpy) = muselect menv.me_fun_defs_cpy idx
      # menv                 = {menv & me_fun_defs_cpy = fun_defs_cpy}
      # chn = {chn & chn_module_env = menv}
      = case (mfdnt, mfdt) of
          (Just fdnt, Just fdt)
            = case (fdnt.fun_body, fdt.fun_type) of
                (TransformedBody fb, Yes symbty)
                  # menv = chn.chn_module_env
                  # (isPA, menv) = case fb.tb_rhs of
                                     App app -> isPartialApp app menv
                                     _       -> (False, menv)
                  # chn = {chn & chn_module_env = menv}
                  = if isPA chn (doAddRefl fdnt symbty common_defs chn)
                _ = chn
          _ = chn
  where
  doAddRefl {fun_ident, fun_body=TransformedBody { tb_args, tb_rhs }} symbty common_defs chn
    # pdss = chn.chn_predef_symbols
    # (ok, pdss) = pdssAreDefined [ PD_tonicExtWrapArg
                                  , PD_tonicExtWrapBody
                                  , PD_tonicExtWrapBodyLam1
                                  , PD_tonicExtWrapBodyLam2
                                  , PD_tonicExtWrapBodyLam3
                                  , PD_ConsSymbol
                                  , PD_NilSymbol] pdss
    # chn = {chn & chn_predef_symbols = pdss}
    | not ok     = chn
    # (args, chn) = foldr (mkArg symbty is_itasks_mod class_instances) ([], chn) (zip2 tb_args symbty.st_args)
    | length args == length tb_args
        # menv = chn.chn_module_env
        # (rem, menv)  = case tb_rhs of
                           App {app_symb = {symb_ident}}
                            | symb_ident == predefined_idents.[PD_tonicExtWrapBodyLam1] = (1, menv)
                            | symb_ident == predefined_idents.[PD_tonicExtWrapBodyLam2] = (2, menv)
                            | symb_ident == predefined_idents.[PD_tonicExtWrapBodyLam3] = (3, menv)
                           App app
                             = argsRemaining app menv
                           _ = (0, menv)
        # (xs, pdss) = toStatic args chn.chn_predef_symbols
        # (wrap, heaps, pdss) = appPredefinedSymbolWithEI (findBodyWrap rem)
                                  [ mkStr icl_module.icl_name.id_name
                                  , mkStr fun_ident.id_name
                                  , xs
                                  , tb_rhs
                                  ] SK_Function chn.chn_heaps pdss
        # fun_defs = updateFunRhs idx menv.me_fun_defs (App wrap)
        = {chn & chn_module_env = { menv & me_fun_defs = fun_defs}
               , chn_heaps = heaps
               , chn_predef_symbols = pdss}
    | otherwise = chn
    where
    findBodyWrap :: Int -> Int
    findBodyWrap 0 = PD_tonicExtWrapBody
    findBodyWrap 1 = PD_tonicExtWrapBodyLam1
    findBodyWrap 2 = PD_tonicExtWrapBodyLam2
    findBodyWrap 3 = PD_tonicExtWrapBodyLam3
    findBodyWrap n = abort ("No PD_tonicExtWrapBodyLam" +++ toString n)

    mkArg :: SymbolType Bool {#{!InstanceTree}} (FreeVar, AType) ([Expression], *ChnExpression) -> *([Expression], *ChnExpression)
    mkArg symty is_itasks_mod class_instances (arg=:{fv_info_ptr, fv_ident}, {at_type}) (xs, chn)
      # pdss = chn.chn_predef_symbols
      # heaps = chn.chn_heaps
      # (itask_class_symbol, pdss) = pdss![PD_ITaskClass]
      # gtcClasses  = [gtc_class \\ {tc_class = TCGeneric {gtc_class}} <- common_defs.[itask_class_symbol.pds_module].com_class_defs.[itask_class_symbol.pds_def].class_context] 
      # (hasITasks, hp_type_heaps) = tyHasITaskClasses class_instances gtcClasses at_type heaps.hp_type_heaps
      # heaps         = {heaps & hp_type_heaps = hp_type_heaps}
      # (noCtx, pdss) = noITaskCtx arg symty.st_context pdss
      # (bv, heaps)   = freeVarToVar arg heaps
      # (viewApp, heaps, pdss) = appPredefinedSymbolWithEI PD_tonicExtWrapArg
                                   [ mkStr fv_ident.id_name
                                   , mkInt (ptrToInt fv_info_ptr)
                                   , if (is_itasks_mod || (not hasITasks && noCtx))
                                       (mkStr fv_ident.id_name)
                                       (Var bv)
                                   ] SK_Function heaps pdss
      # (texpr, pdss) = toStatic (mkStr fv_ident.id_name, mkInt (ptrToInt fv_info_ptr), App viewApp) pdss
      = ([texpr:xs], {chn & chn_predef_symbols = pdss, chn_heaps = heaps })
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
  doAddRefl _ _ _ chn = chn

instance == (Global a) | == a where
  (==) g1 g2 = g1.glob_module == g2.glob_module && g1.glob_object == g2.glob_object

instance toString IdentOrQualifiedIdent where
  toString (Ident ident) = ident.id_name
  toString (QualifiedIdent _ str) = str
