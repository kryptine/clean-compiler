implementation module Tonic.GraphGen

// Task Oriented Notation Illustrated on a Canvas

//import syntax, checksupport, StdFile
//from CoclSystemDependent import DirectorySeparator, ensureCleanSystemFilesExists

import syntax, predef, checksupport

import StdFunc
from StdList import last
////import Tonic.TonicAG
import Tonic.Util
import Tonic.AbsSyn
import Tonic.Pretty

import Data.Func
import Data.Maybe
import Data.List
import Data.Graph
from Data.Map import :: Map
import qualified Data.Map as DM
from Data.Set import :: Set
import qualified Data.Set as DS

import qualified Text.PPrint as PPrint
import iTasks._Framework.Tonic.AbsSyn

import StdMisc

/*

[(x, y) \\ x <- xs & y <- ys]
==
for each x in xs
together with y in ys
(x, y)

[(x, y, z) \\ x <- xs & y <- ys & z <- zs]
==
for each x in xs
together with y in ys
together with z in zs
(x, y, z)

[(x, y, z) \\ x <- xs & y <- ys & z <- zs | x == y && y == z]
==
for each x in xs
together with y in ys
together with z in zs
given x == y && y == z
(x, y, z)


[(x, y) \\ x <- xs, y <- ys]
==
for each x in xs
after y in ys
(x, y)

[(x, y, z) \\ x <- xs, y <- ys, z <- zs]
==
for each x in xs
after y in ys
after z in zs
(x, y, z)

[(x, y, z) \\ x <- xs, y <- ys, z <- zs | x == y && y == z]
==
for each x in xs
after y in ys
after z in zs
given x == y && y == z
(x, y, z)
*/
//mkCompr :: ParsedExpr -> TExpr
//mkCompr (PE_ListCompr _ _ expr qualifiers) = TListCompr (TCleanExpr [] (mkLCExpr expr)) [] (PPCleanExpr "TODO GUARDS")
  //where
  //mkLCExpr (PE_Ident ident) = PPCleanExpr ident.id_name
  //mkLCExpr (PE_Basic b)     = PPCleanExpr (ppCompact (ppBasicValue b))
  //mkLCExpr (PE_Tuple es)    = AppCleanExpr TNoAssoc (predefined_idents.[GetTupleConsIndex (length es)].id_name) (map mkLCExpr es)
  //mkLCExpr _                = PPCleanExpr "TODO"
  //mkLCExpr lc=:(PE_ListCompr _ _ _ _) = "PE_ListCompr"
  //mkLCExpr (PE_List _) = "PE_List"
  //mkLCExpr (PE_Bound be) = "PE_Bound"
  //mkLCExpr (PE_Lambda _ _ _ _) = "PE_Lambda"
  //mkLCExpr (PE_Record _ _ _) = "PE_Record"
  //mkLCExpr (PE_ArrayPattern _) = "PE_ArrayPattern"
  //mkLCExpr (PE_UpdateComprehension _ _ _ _) = "PE_UpdateComprehension"
  //mkLCExpr (PE_ArrayDenot _ _) = "PE_ArrayDenot"
  //mkLCExpr (PE_Selection _ _ _) = "PE_Selection"
  //mkLCExpr (PE_Update _ _ _) = "PE_Update"
  //mkLCExpr (PE_Case _ _ _) = "PE_Case"
  //mkLCExpr (PE_If _ _ _ _) = "PE_If"
  //mkLCExpr (PE_Let _ _) = "PE_Let"
  //mkLCExpr (PE_ArrayCompr _ _ _) = "PE_ArrayCompr"
  //mkLCExpr (PE_Sequ _) = "PE_Sequ"
  //mkLCExpr (PE_WildCard) = "PE_WildCard"
  //mkLCExpr (PE_Matches _ _ _ _) = "PE_Matches"
  //mkLCExpr (PE_QualifiedIdent _ _) = "PE_QualifiedIdent"
  //mkLCExpr (PE_ABC_Code _ _) = "PE_ABC_Code"
  //mkLCExpr (PE_Any_Code _ _ _) = "PE_Any_Code"
  //mkLCExpr (PE_DynamicPattern _ _) = "PE_DynamicPattern"
  //mkLCExpr (PE_Dynamic _ _) = "PE_Dynamic"
  //mkLCExpr (PE_Generic _ _) = "PE_Generic"
  //mkLCExpr (PE_TypeSignature _ _) = "PE_TypeSignature"
  //mkLCExpr (PE_Empty) = "PE_Empty"

//ppPE lc=:(PE_ListCompr _ _ _ _) = "PE_ListCompr"
//ppPE (PE_List _) = "PE_List"
//ppPE (PE_Ident ident) = ident.id_name
//ppPE (PE_Basic _) = "PE_Basic"
//ppPE (PE_Bound _) = "PE_Bound"
//ppPE (PE_Lambda _ _ _ _) = "PE_Lambda"
//ppPE (PE_Tuple es) = predefined_idents.[GetTupleConsIndex (length es)].id_name
//ppPE (PE_Record _ _ _) = "PE_Record"
//ppPE (PE_ArrayPattern _) = "PE_ArrayPattern"
//ppPE (PE_UpdateComprehension _ _ _ _) = "PE_UpdateComprehension"
//ppPE (PE_ArrayDenot _ _) = "PE_ArrayDenot"
//ppPE (PE_Selection _ _ _) = "PE_Selection"
//ppPE (PE_Update _ _ _) = "PE_Update"
//ppPE (PE_Case _ _ _) = "PE_Case"
//ppPE (PE_If _ _ _ _) = "PE_If"
//ppPE (PE_Let _ _) = "PE_Let"
//ppPE (PE_ArrayCompr _ _ _) = "PE_ArrayCompr"
//ppPE (PE_Sequ _) = "PE_Sequ"
//ppPE (PE_WildCard) = "PE_WildCard"
//ppPE (PE_Matches _ _ _ _) = "PE_Matches"
//ppPE (PE_QualifiedIdent _ _) = "PE_QualifiedIdent"
//ppPE (PE_ABC_Code _ _) = "PE_ABC_Code"
//ppPE (PE_Any_Code _ _ _) = "PE_Any_Code"
//ppPE (PE_DynamicPattern _ _) = "PE_DynamicPattern"
//ppPE (PE_Dynamic _ _) = "PE_Dynamic"
//ppPE (PE_Generic _ _) = "PE_Generic"
//ppPE (PE_TypeSignature _ _) = "PE_TypeSignature"
//ppPE (PE_Empty) = "PE_Empty"

wrapTMApp :: ExprId String Expression [Expression] InhExpression *ChnExpression -> *(Expression, *ChnExpression)
wrapTMApp uid wrappedFnNm origExpr evalableCases inh chn
  # (ok, pdss) = pdssAreDefined [PD_tonicExtWrapApp, PD_tonicExtWrapAppLam1, PD_tonicExtWrapAppLam2, PD_tonicExtWrapAppLam3, PD_ConsSymbol, PD_NilSymbol] chn.chn_predef_symbols
  # chn =  {chn & chn_predef_symbols = pdss}
  | not ok     = (origExpr, chn)
  | otherwise
      # (rem, chn)    = case origExpr of
                           App app
                             = argsRemaining app chn
                           _ = (0, chn)
      # (icl, chn)    = chn!chn_icl_module
      # iclName        = icl.icl_name.id_name
      # (wrappedFnModNm, chn) = case origExpr of
                                   App app
                                     # (mdcl, chn) = reifyDclModule app.app_symb chn
                                     = case mdcl of
                                         Just dcl -> (dcl.dcl_name.id_name, chn)
                                         _        -> (iclName, chn)
                                   _ = (iclName, chn)
      # heaps = chn.chn_heaps
      # (eidExpr, pdss) = listToListExpr (map mkInt uid) chn.chn_predef_symbols
      # (casesExpr, pdss) = listToListExpr evalableCases pdss
      # (expr, heaps, pdss) = appPredefinedSymbolWithEI (findWrap rem)
                                [ mkStr wrappedFnModNm
                                , mkStr wrappedFnNm
                                , eidExpr
                                , casesExpr
                                , origExpr
                                ] SK_Function heaps pdss
      = ( App expr
        , {chn & chn_predef_symbols = pdss
               , chn_icl_module = icl
               , chn_heaps = heaps
               })
  where
  findWrap :: Int -> Int
  findWrap 0 = PD_tonicExtWrapApp
  findWrap 1 = PD_tonicExtWrapAppLam1
  findWrap 2 = PD_tonicExtWrapAppLam2
  findWrap 3 = PD_tonicExtWrapAppLam3
  findWrap n = abort ("No tonicExtWrapAppLam" +++ toString n)
import StdDebug

getAssoc app_symb chn
  # (mPrio, chn) = reifySymbIdentPriority app_symb chn
  = case mPrio of
      Just prio -> (fromPriority prio, chn)
      _         -> (TNoPrio, chn)

mkBlueprint :: !InhExpression !Expression !*ChnExpression -> *(!SynExpression, !*ChnExpression)
mkBlueprint inh expr=:(App app=:{app_symb}) chn
  # (isTonicFunctor, chn) = symbIdentIsBPPart app.app_symb inh chn
  # ((ctxs, args), chn)  = dropAppContexts app chn
  | identIsLambda app_symb.symb_ident
      # ((args, tFd), chn) = reifyArgsAndDef app_symb chn
      # tyenv               = foldr (\(arg, t) st -> 'DM'.put (ptrToInt arg.fv_info_ptr) t st) 'DM'.newMap (zip2 args (funArgTys tFd))
      # tyenv               = 'DM'.union tyenv inh.inh_tyenv
      # inh                 = {inh & inh_tyenv = tyenv}
      # (syne, chn)         = mkBlueprint {inh & inh_fun_idx = symbIdentObjectIdx app_symb} (getFunRhs tFd) chn
      # pats                = [case freeVarName x of
                                 "_x" -> case syne.syn_pattern_match_vars of
                                           [(_, e):_] -> e
                                           _          -> TVar [] "_x" (ptrToInt x.fv_info_ptr)
                                 x`    -> TVar [] x` (ptrToInt x.fv_info_ptr)
                              \\ x <- args | x.fv_def_level == -1]

      # (syne, chn)         = case (isTonicFunctor, symbIdentObjectIdx app_symb) of
                                (True, idx)
                                  = wrapBody {inh & inh_fun_idx = idx} syne True chn
                                _ = (syne, chn)
      # chn                 = updateWithAnnot (symbIdentObjectIdx app_symb) syne.syn_annot_expr inh chn
      # (app`, chn)         = if isTonicFunctor
                                (wrapTMApp inh.inh_uid app_symb.symb_ident.id_name (App app) [] inh chn)
                                (App app, chn)
      = ( { syn_annot_expr = app`
          , syn_texpr      = TLam pats syne.syn_texpr
          , syn_pattern_match_vars = []
          , syn_bound_vars = foldr (\x vs -> 'DM'.del (ptrToInt x.fv_info_ptr) vs) syne.syn_bound_vars [x \\ x <- args | x.fv_def_level == -1]
          , syn_cases      = syne.syn_cases
          }
        , chn)
  | isTonicFunctor = mkMApp app ctxs args inh chn
  | appIsListComp app
      = case [orig \\ (ident, orig) <- inh.inh_list_compr
                    | app.app_symb.symb_ident.id_name == ident] of
          [] = mkFApp app ctxs args inh chn
          [orig:_]
            = ({ syn_annot_expr = expr
               , syn_texpr      = TPPExpr (ppCompact (ppParsedExpr orig))
               , syn_pattern_match_vars = []
               , syn_bound_vars = 'DM'.newMap
               , syn_cases      = []}, chn)
  | otherwise      = mkFApp app ctxs args inh chn
  where
  mkMApp app ctxs args inh chn
    # predef_symbols               = chn.chn_predef_symbols
    # (bindSymbol, predef_symbols) = predef_symbols![PD_TMonadBind]
    # chn                          = {chn & chn_predef_symbols = predef_symbols}
    # (dcls, chn)                  = chn!chn_dcl_modules
    # bindMemberDef                = dcls.[bindSymbol.pds_module].dcl_common.com_member_defs.[bindSymbol.pds_def]
    # appIsBind                    = app.app_symb.symb_ident.id_info == bindMemberDef.me_ident.id_info
    # appName                      = app.app_symb.symb_ident.id_name
    = case (appIsBind, args) of
        (True, [lhsExpr, rhsExpr=:(App rhsApp) : _])
          | identIsLambda rhsApp.app_symb.symb_ident
          # ((rhsArgs, rhsFd), chn) = reifyArgsAndDef rhsApp.app_symb chn
          # bindLamArgFV            = last rhsArgs
          # (mFunTy, chn)           = reifyFunType app.app_symb chn
          # (assoc, chn)            = getAssoc app.app_symb chn
          # (mst, chn)              = reifySymbIdentSymbolType app.app_symb chn
          # mTyStr                   = case mst of
                                         Just st -> symTyStr st
                                         _       -> Nothing
          # (dclnm, chn)            = case reifyDclModule app.app_symb chn of
                                         (Just dcl, chn) = (dcl.dcl_name.id_name, chn)
                                         (_       , chn)
                                           # (iclmod, chn) = chn!chn_icl_module
                                           = (iclmod.icl_name.id_name, chn)

          # (synr, chn)              = mkBlueprint (addUnique 1 inh) rhsExpr chn
          # (synl, chn)              = mkBlueprint (addUnique 0 {inh & inh_bind_var = Just (bindLamArgFV, symbIdentObjectIdx rhsApp.app_symb)
                                                                     , inh_cases    = synr.syn_cases}) lhsExpr chn
          # ps                       = [synl, synr]


          //# allCases                 = flatten (map (\syn -> syn.syn_cases) ps)
          //# evalableCases            = [(eid, 'DM'.elems vars, cs) \\ (eid, vars, cs) <- allCases | allVarsBound inh vars]
          //# (evalableCases, chn)     = mapSt (\(eid, bvs, cs) chn -> mkCaseDetFun (Just bindLamArgFV) eid (ptrToInt app.app_info_ptr) bvs cs inh chn) evalableCases chn
          # args`                    = [synl.syn_annot_expr, synr.syn_annot_expr]
          # (app`, chn)              = (App {app & app_args = args`}, chn)
          # (app`, chn)              = wrapTMApp inh.inh_uid appName app` [] inh chn
          = ({ syn_annot_expr = app`
             , syn_texpr      = TMApp inh.inh_uid mTyStr dclnm (appFunName app) [synl.syn_texpr, synr.syn_texpr] assoc
             , syn_pattern_match_vars = []
             , syn_bound_vars = 'DM'.union synl.syn_bound_vars synr.syn_bound_vars
             , syn_cases = synl.syn_cases ++ synr.syn_cases}, chn)
        _
          # (mFunTy, chn) = reifyFunType app.app_symb chn
          # (assoc, chn)  = getAssoc app.app_symb chn
          # (mst, chn)    = reifySymbIdentSymbolType app.app_symb chn
          # mTyStr         = case mst of
                               Just st -> symTyStr st
                               _       -> Nothing
          # (dclnm, chn)  = case reifyDclModule app.app_symb chn of
                               (Just dcl, chn) = (dcl.dcl_name.id_name, chn)
                               (_       , chn)
                                 # (iclmod, chn) = chn!chn_icl_module
                                 = (iclmod.icl_name.id_name, chn)
          # evalableCases  = case inh.inh_bind_var of
                               Just (var, lamIdx)
                                 = [(eid, 'DM'.elems vars, cs) \\ (eid, vars, cs) <- inh.inh_cases | allVarsBound` var inh vars]
                               _ = []
          # (evalableCases, chn) = ([], chn) // mapSt (\(eid, bvs, cs) chn -> mkCaseDetFun inh.inh_bind_var eid (ptrToInt app.app_info_ptr) bvs cs inh chn) evalableCases chn
          # (ps, chn)      = mapSt (\(x, n) chn -> mkBlueprint (addUnique n {inh & inh_bind_var = Nothing}) x chn) (zip2 args [0..]) chn
          # args`          = map (\syn -> syn.syn_annot_expr) ps
          # (app`, chn)    = (App {app & app_args = args`}, chn)
          # (app`, chn)    = wrapTMApp inh.inh_uid appName app` evalableCases inh chn
          = ({ syn_annot_expr = app`
             , syn_texpr      = TMApp inh.inh_uid mTyStr dclnm (appFunName app) (map (\syn -> syn.syn_texpr) ps) assoc
             , syn_pattern_match_vars = []
             , syn_bound_vars = 'DM'.unions (map (\syn -> syn.syn_bound_vars) ps)
             , syn_cases = flatten (map (\syn -> syn.syn_cases) ps)}, chn)
          where
          allVarsBound` fv inh bound
            # diff = 'DM'.difference bound inh.inh_tyenv
            = case 'DM'.toList diff of
                [(k, _)] -> k == ptrToInt fv.fv_info_ptr
                _ -> False

  mkFApp app ctxs args inh chn
    # appName       = app.app_symb.symb_ident.id_name
    # (dclnm, chn) = case reifyDclModule app.app_symb chn of
                        (Just dcl, chn) = (dcl.dcl_name.id_name, chn)
                        (_       , chn)
                          # (iclmod, chn) = chn!chn_icl_module
                          = (iclmod.icl_name.id_name, chn)
    # (assoc, chn) = getAssoc app.app_symb chn
    # (ps, chn)     = mapSt (\(x, n) chn -> mkBlueprint (addUnique n inh) x chn) (zip2 args [0..]) chn
    = ({ syn_annot_expr = App {app & app_args = ctxs ++ map (\syn -> syn.syn_annot_expr) ps}
       , syn_texpr      = TFApp appName (map (\syn -> syn.syn_texpr) ps) assoc
       , syn_pattern_match_vars = []
       , syn_bound_vars = 'DM'.unions (map (\syn -> syn.syn_bound_vars) ps)
       , syn_cases = flatten (map (\syn -> syn.syn_cases) ps) }, chn)

  // Transformation for higher-order function application
  // E.g. f g x = g x becomes f = g @ x
  // In GiN, there are two ways to introduce a lambda function: either write one
  // as a host-language expression, or "update a variable", in which case a
  // lambda is introduced to shadow an existing variable and apply some function
  // to it.
  // For Tonic, we need to inspect the lambda and its application. If a lambda
  // expression can be reduced, we generate a Let block, like GiN would have. E.g.
  //  [[ (\x -> e) a ]] = let x = a in e
  //  [[ (\x y -> e) a ]] = let x = a in \y -> e
  //  [[ (\x y -> e) a b ]] = let x = a; y = b in e
  // We then also need to continue including the lambda in the graph, as it can
  // lead to a recursive function application.
mkBlueprint inh (e @ []) chn = abort "atC: no args"
mkBlueprint inh (e=:(App app) @ es) chn
  # (mfd, chn) = reifyFunDef app.app_symb chn
  # fd          = fromMaybe (abort ("atC: failed to reify " +++ app.app_symb.symb_ident.id_name)) mfd
  | identIsLambda app.app_symb.symb_ident
      # ((args, _), chn) = reifyArgsAndDef app.app_symb chn
      # letargs       = drop (length app.app_args) (getFunArgs fd)
      # (binds, chn) = zipWithSt zwf letargs es chn
      # tyenv         = foldr (\(arg, t) st -> 'DM'.put (ptrToInt arg.fv_info_ptr) t st) 'DM'.newMap (zip2 args (funArgTys fd))
      # tyenv         = 'DM'.union tyenv inh.inh_tyenv
      # (syne, chn)   = mkBlueprint (addUnique 0 {inh & inh_tyenv = tyenv}) (getFunRhs fd) chn
      # chn           = updateWithAnnot (symbIdentObjectIdx app.app_symb) syne.syn_annot_expr inh chn
      = ({ syn_annot_expr = e @ es
         , syn_texpr      = TPPExpr "TODO @"
         , syn_pattern_match_vars = syne.syn_pattern_match_vars
         , syn_bound_vars = foldr (\x vs -> 'DM'.del (ptrToInt x.fv_info_ptr) vs) syne.syn_bound_vars [x \\ x <- args | x.fv_def_level == -1]
         , syn_cases      = syne.syn_cases
         }, chn)
  | otherwise
      # (assoc, chn)     = getAssoc app.app_symb chn
      # (isPart, chn)     = funIsBlueprintPart fd inh chn
      # (texpr, es`, chn) = case fd.fun_type of
                              Yes ft | isPart
                                # (es`, chn)    = mapSt (\(e, n) chn -> mkBlueprint (addUnique n inh) e chn) (zip2 es [0..]) chn
                                # (mst, chn)   = reifySymbIdentSymbolType app.app_symb chn
                                # mTyStr        = case mst of
                                                    Just st -> symTyStr st
                                                    _       -> Nothing
                                # (dclnm, chn) = case reifyDclModule app.app_symb chn of
                                                    (Just dcl, chn) = (dcl.dcl_name.id_name, chn)
                                                    (_       , chn)
                                                      # (iclmod, chn) = chn!chn_icl_module
                                                      = (iclmod.icl_name.id_name, chn)
                                = ( TMApp inh.inh_uid mTyStr dclnm (appFunName app) (map (\syn -> syn.syn_texpr) es`) assoc
                                  , es`, chn)
                              _
                                # (es`, chn) = mapSt (\(e, n) chn -> mkBlueprint (addUnique n inh) e chn) (zip2 es [0..]) chn
                                = ( TFApp app.app_symb.symb_ident.id_name (map (\x -> x.syn_texpr) es`) assoc
                                  , es`, chn)
      = ({ syn_annot_expr = e @ (map (\x -> x.syn_annot_expr) es`)
         , syn_texpr      = texpr
         , syn_pattern_match_vars = []
         , syn_bound_vars = 'DM'.unions (map (\syn -> syn.syn_bound_vars) es`)
         , syn_cases      = flatten (map (\syn -> syn.syn_cases) es`) }, chn)
  where
    zwf eVar eVal chn
      # fvl         = ppFreeVar eVar
      # (fvr, chn) = ppExpression eVal chn
      = ((ppCompact fvl, ppCompact fvr), chn)
mkBlueprint inh (e=:(Var bv) @ es) chn
  # (bps, chn)    = mapSt (\(e, n) chn -> mkBlueprint (addUnique n inh) e chn) (zip2 es [0..]) chn
  # bvs           = 'DM'.unions (map (\syn -> syn.syn_bound_vars) bps)
  # cs            = flatten (map (\syn -> syn.syn_cases) bps)
  # (isPart, chn) = varIsTask bv inh chn
  | isPart
      # (var`, chn) = wrapTMApp inh.inh_uid "(Var @ es)" (e @ es) [] inh chn
      # mTyStr      = case 'DM'.get (ptrToInt bv.var_info_ptr) inh.inh_tyenv of
                        Just x -> symTyStr` x
                        _      -> Nothing
      = ({ syn_annot_expr = var`
         , syn_texpr      = TMApp inh.inh_uid mTyStr "" bv.var_ident.id_name (map (\syn -> syn.syn_texpr) bps) TNoPrio
         , syn_pattern_match_vars = []
         , syn_bound_vars = bvs
         , syn_cases = cs}, chn)
  | otherwise
      = ({ syn_annot_expr = Var bv @ es
         , syn_texpr      = TFApp bv.var_ident.id_name (map (\syn -> syn.syn_texpr) bps) TNoPrio
         , syn_pattern_match_vars = []
         , syn_bound_vars = bvs
         , syn_cases = cs}, chn)
mkBlueprint inh (e @ es) chn = ({ syn_annot_expr = e @ es
                              , syn_texpr      = TPPExpr "TODO @"
                              , syn_pattern_match_vars = []
                              , syn_bound_vars = 'DM'.newMap
                              , syn_cases      = []}, chn)
mkBlueprint inh (Let lt) chn
  # boundVars = [bnd.lb_dst.fv_info_ptr \\ bnd <- getLetBinds lt]
  # mexpr     = listToMaybe [ bnd.lb_src \\ bnd <- getLetBinds lt
                            | bnd.lb_dst.fv_ident.id_name == "_case_var"]
  # (syn, chn) = mkLet mexpr lt inh chn
  # syn        = {syn & syn_bound_vars = foldr (\x vs -> 'DM'.del (ptrToInt x) vs) syn.syn_bound_vars boundVars}
  = (syn, chn)
  where
  mkLet (Just expr=:(App app)) lt inh chn
    | appIsListComp app
        = case [orig \\ (ident, orig) <- inh.inh_list_compr
                      | app.app_symb.symb_ident.id_name == ident] of
            []
              # (syn, chn) = mkBlueprint (addUnique 0 {inh & inh_case_expr = Just expr}) lt.let_expr chn
              # l          = {lt & let_expr = syn.syn_annot_expr}
              = ({syn & syn_annot_expr = Let l}, chn)
            [orig:_]
              # (syn, chn) = mkBlueprint (addUnique 0 {inh & inh_case_expr = Just expr}) lt.let_expr chn
              # l          = {lt & let_expr = syn.syn_annot_expr}
              = ({ syn
                 & syn_annot_expr = Let l
                 , syn_texpr = TPPExpr (ppCompact (ppParsedExpr orig))}, chn)
  mkLet (Just expr) lt inh chn
    # (syn, chn) = mkBlueprint (addUnique 0 {inh & inh_case_expr = Just expr}) lt.let_expr chn
    # l          = {lt & let_expr = syn.syn_annot_expr}
    = ({syn & syn_annot_expr = Let l}, chn)
  mkLet Nothing lt inh chn
    # (tys, chn)      = letTypes lt.let_info_ptr chn
    # (binds, _, chn) = flattenBinds lt chn
    # tyenv           = zipSt (\(TVar _ _ ptr, _) t tyenv -> 'DM'.put ptr t tyenv) binds tys inh.inh_tyenv // TODO This probably won't work for arbitrary patterns, so we actually need to be a bit smarter here and extract all variables from the patterns, instead of just PP'ing the pattern and using that as index
    # (syn, chn)      = mkBlueprint (addUnique 0 {inh & inh_tyenv = tyenv}) lt.let_expr chn
    = ({ syn_annot_expr = Let {lt & let_expr = syn.syn_annot_expr}
       , syn_texpr      = TLet binds syn.syn_texpr
       , syn_pattern_match_vars = syn.syn_pattern_match_vars
       , syn_bound_vars = syn.syn_bound_vars
       , syn_cases      = syn.syn_cases}, chn)
    where
    letTypes :: ExprInfoPtr *ChnExpression -> *([Type], *ChnExpression)
    letTypes exprPtr chn
      # heaps = chn.chn_heaps
      # (ei, expr_heap) = readPtr exprPtr heaps.hp_expression_heap
      # chn = {chn & chn_heaps = {heaps & hp_expression_heap = expr_heap}}
      = case ei of
          EI_LetType atys -> (map (\x -> x.at_type) atys, chn)
          _               -> ([], chn)

    flattenBinds lt chn
      = foldrSt f (getLetBinds lt) ([], 1, chn)
      where
      f bnd (xs, n, chn)
        # (rhs, chn) = mkBlueprint (addUnique n inh) bnd.lb_src chn
        = ([(TVar [] bnd.lb_dst.fv_ident.id_name (ptrToInt bnd.lb_dst.fv_info_ptr), rhs.syn_texpr):xs], n + 1, chn)
   getLetBinds lt = lt.let_strict_binds ++ lt.let_lazy_binds
  // TODO: For cases, the compiler introduces a fresh variable in a let for the
  // matches expression. E.g.
  //   case x > y of ....
  // becomes
  //   let _case_var = x > y
  //   in case _case_var of ...
  // We need to reify the fresh z and substitute it in the graphical
  // representation. These fresh variables can be recognized by an underscore
  // prefix. We may, however, need to be a bit more clever about this in case
  // someone actually prefixes their own variables with an underscore.
  // There is one exception to this rule, and that is if the case already matches
  // on exactly one _variable_:
  //   let x = True
  //   in case x of ....
  // Howerver, the following code
  //   case True of ...
  // Will still be converted to a case with a variable:
  //   let _case_var = True
  //   in case _case_var of ...

  // TODO Refactor this. Also persist numbering?
mkBlueprint inh (Case cs) chn
  # caseExpr     = case inh.inh_case_expr of
                     Just e -> e
                     _      -> cs.case_expr
  # (cesyn, chn) = mkBlueprint (addUnique 0 inh) caseExpr chn
  = case (cs.case_explicit, cs.case_expr, cs.case_guards) of
      (False, Var bv, AlgebraicPatterns gi [ap:_])
        # (fvds, chn)   = mapSt (mkBlueprint (addUnique 1 inh) o FreeVar) ap.ap_vars chn
        # (clexpr, chn) = case fvds of
                            [] = (TPPExpr "", chn)
                            args
                              # (mprio, chn) = if (ap.ap_symbol.glob_module == chn.chn_main_dcl_module_n)
                                                  (reifyFunDefsIdxPriority ap.ap_symbol.glob_object.ds_index chn)
                                                  (reifyDclModulesIdxPriority` ap.ap_symbol.glob_module ap.ap_symbol.glob_object.ds_index chn)
                              # assoc         = case mprio of
                                                  Just p -> fromPriority p
                                                  _      -> TNoPrio
                              = (TFApp ap.ap_symbol.glob_object.ds_ident.id_name (map (\x -> x.syn_texpr) args) assoc, chn)
        # (syn, chn)    = mkAlts` inh 0 ap.ap_expr chn
        = ({ syn_annot_expr = Case {cs & case_guards = AlgebraicPatterns gi [{ap & ap_expr = syn.syn_annot_expr}]}
           , syn_texpr      = syn.syn_texpr
           , syn_pattern_match_vars = [(bv, clexpr) : syn.syn_pattern_match_vars]
           , syn_bound_vars = 'DM'.unions [syn.syn_bound_vars : map (\x -> x.syn_bound_vars) fvds]
           , syn_cases      = syn.syn_cases}, chn)
      _
        # ((guards, syns), chn)    = mkAlts cs.case_guards chn
        # ((def, syns, isIf), chn) = case cs.case_default of
                                       Yes def
                                         # (syn, chn) = mkAlts` inh (numGuards cs.case_guards) def chn
                                         = case syns of
                                             [(TLit (TBool True), _)]
                                               = ((Yes syn.syn_annot_expr, [(TLit (TBool False), syn):syns], True), chn)
                                             _ = ((Yes syn.syn_annot_expr, [(TPPExpr "_", syn):syns], False), chn)
                                       _ = ((No, syns, False), chn)
        # (syncase, chn) = case inh.inh_case_expr of
                             Just e
                               # heaps              = chn.chn_heaps
                               # (vptr, var_heap)   = newPtr VI_Empty heaps.hp_var_heap
                               # heaps              = { heaps & hp_var_heap = var_heap }
                               # fv                 = { fv_def_level = 0
                                                      , fv_ident     = { id_name = "_case_var"
                                                                       , id_info = nilPtr }
                                                      , fv_info_ptr  = vptr
                                                      , fv_count     = 1
                                                      }
                               # casebind           = { lb_dst      = fv
                                                      , lb_src      = e
                                                      , lb_position = NoPos }
                               # (ltptr, expr_heap) = newPtr EI_Empty heaps.hp_expression_heap
                               # heaps              = { heaps & hp_expression_heap = expr_heap }
                               # (bv, heaps)        = freeVarToVar fv heaps
                               # lt = { let_strict_binds  = []
                                      , let_lazy_binds    = [casebind]
                                      , let_expr          = Case {cs & case_expr = Var bv}
                                      , let_info_ptr      = ltptr
                                      , let_expr_position = NoPos
                                      }
                               = (Let lt, {chn & chn_heaps = heaps})
                             _ = (Case cs, chn)
        # bvs = 'DM'.unions [cesyn.syn_bound_vars : map (\(_, x) -> x.syn_bound_vars) syns]
        = ({ syn_annot_expr = Case {cs & case_default = def, case_guards = guards}
           , syn_texpr      = case (isIf, syns) of
                                (True, [(_, be), (_, bt)]) -> TIf inh.inh_uid cesyn.syn_texpr bt.syn_texpr be.syn_texpr
                                _                          -> TCase inh.inh_uid cesyn.syn_texpr (reverse (map (\(d, s) -> (d, s.syn_texpr)) syns))
           , syn_pattern_match_vars = foldr (\(_, syn) acc -> syn.syn_pattern_match_vars ++ acc) [] syns
           , syn_bound_vars = bvs
           , syn_cases      = [(inh.inh_uid, bvs, syncase) : flatten (map (\(_, x) -> x.syn_cases) syns)]
           }, chn)
  where
  numGuards (AlgebraicPatterns _ ps)        = length ps
  numGuards (BasicPatterns _ ps)            = length ps
  numGuards (NewTypePatterns _ ps)          = length ps
  numGuards (DynamicPatterns ps)            = length ps
  numGuards (OverloadedListPatterns _ _ ps) = length ps
  numGuards NoPattern                       = 0
  mkAlts c=:(AlgebraicPatterns gi aps) chn
    # ((aps, syns, _), chn) = foldr f (([], [], 0), chn) aps
    = ((AlgebraicPatterns gi aps, syns), chn)
    where
      f ap ((aps, syns, n), chn)
        # (apd, chn) = mkAp ap.ap_symbol ap.ap_vars chn
        # (syn, chn) = mkAlts` inh n ap.ap_expr chn
        # ap         = {ap & ap_expr = syn.syn_annot_expr}
        = (([ap:aps], [(apd, syn):syns], n + 1), chn)
        where
        mkAp sym []   chn = (TPPExpr (ppCompact ('PPrint'.text sym.glob_object.ds_ident.id_name)), chn)
        mkAp sym vars chn
          # (fvds, chn) = mapSt (mkBlueprint (addUnique n inh) o FreeVar) vars chn
          = (TFApp (ppCompact ('PPrint'.text sym.glob_object.ds_ident.id_name)) (map (\x -> x.syn_texpr) fvds) TNoPrio, chn)
  mkAlts c=:(BasicPatterns bt bps) chn
    # ((bps, syns, _), chn) = foldr f (([], [], 0), chn) bps
    = ((BasicPatterns bt bps, syns), chn)
    where
      f bp ((bps, syns, n), chn)
        # (syn, chn)  = mkAlts` inh n bp.bp_expr chn
        # bp          = {bp & bp_expr = syn.syn_annot_expr}
        = (([bp:bps], [(TLit (fromBasicValue bp.bp_value), syn):syns], n + 1), chn)
  mkAlts c chn = ((c, []), chn)

  mkAlts` :: InhExpression Int Expression *ChnExpression -> *(SynExpression, *ChnExpression)
  mkAlts` inh n expr chn
    # inh = {inh & inh_case_expr = Nothing }
    = mkBlueprint (addUnique n inh) expr chn

mkBlueprint inh (Var bv) chn
  # (isPart, chn) = varIsTask bv inh chn
  # ptrInt        = ptrToInt bv.var_info_ptr
  | isPart
      # (var`, chn) = wrapTMApp inh.inh_uid "(Var)" (Var bv) [] inh chn
      = ({ syn_annot_expr = var`
         , syn_texpr      = TVar inh.inh_uid bv.var_ident.id_name ptrInt
         , syn_pattern_match_vars = []
         , syn_bound_vars = 'DM'.singleton ptrInt bv
         , syn_cases      = []}, chn)
  | otherwise
      = ({ syn_annot_expr = Var bv
         , syn_texpr      = TVar [] bv.var_ident.id_name ptrInt
         , syn_pattern_match_vars = []
         , syn_bound_vars = 'DM'.singleton ptrInt bv
         , syn_cases      = []}, chn)
mkBlueprint _ expr=:(FreeVar fv) chn
  = ({ syn_annot_expr = expr
     , syn_texpr      = TVar [] fv.fv_ident.id_name (ptrToInt fv.fv_info_ptr)
     , syn_pattern_match_vars = []
     , syn_cases = []
     , syn_bound_vars = 'DM'.newMap}, chn)
mkBlueprint _ expr=:(BasicExpr bv) chn
  = ({ syn_annot_expr = expr
     , syn_texpr      = TLit (fromBasicValue bv)
     , syn_pattern_match_vars = []
     , syn_bound_vars = 'DM'.newMap
     , syn_cases = []}, chn)
mkBlueprint inh expr=:(Selection st selExpr sels) chn
  # (syn, chn)      = mkBlueprint (addUnique 0 inh) selExpr chn
  # (selExprs, chn) = mapSt (mkSelExprs) sels chn
  = ({ syn_annot_expr = Selection st selExpr sels
     , syn_texpr      = TSel syn.syn_texpr selExprs
     , syn_pattern_match_vars = []
     , syn_bound_vars = 'DM'.newMap
     , syn_cases = []}, chn)
  where
  mkSelExprs (RecordSelection gds _) chn
    # d = ppDefinedSymbol gds.glob_object
    = (TPPExpr (ppCompact d), chn)
  mkSelExprs (ArraySelection gds _ e) chn // TODO use e
    # d = ppDefinedSymbol gds.glob_object
    = (TPPExpr (ppCompact d), chn)
  mkSelExprs (DictionarySelection bv sels _ e) chn
    = (TPPExpr "TODO mkSelExprs DictionarySelection ", chn)
mkBlueprint inh expr=:(TupleSelect _ i e) chn
  # (syn, chn) = mkBlueprint (addUnique 0 inh) e chn
  # te         = TSel syn.syn_texpr [TPPExpr (toString i)]
  = ({ syn_annot_expr = expr
     , syn_texpr      = te
     , syn_pattern_match_vars = []
     , syn_bound_vars = 'DM'.newMap
     , syn_cases = []}, chn)
mkBlueprint inh expr=:(RecordUpdate {glob_object={ds_ident}} expression expressions) chn
  # (syn, chn)  = mkBlueprint (addUnique 0 inh) expression chn
  # (syns, chn) = mapSt (\(n, e) -> mkBlueprint (addUnique n inh) e.bind_src) (zip2 [1..] expressions) chn
  # te          = TRecUpd ds_ident.id_name syn.syn_texpr (map (\x -> x.syn_texpr) syns)
  = ({ syn_annot_expr = expr
     , syn_texpr      = te
     , syn_pattern_match_vars = []
     , syn_bound_vars = 'DM'.newMap
     , syn_cases = []}, chn)
mkBlueprint _ expr=:(NoBind _) chn
  = ({ syn_annot_expr = expr
     , syn_texpr      = TNoBind
     , syn_pattern_match_vars = []
     , syn_bound_vars = 'DM'.newMap
     , syn_cases = []}, chn)

mkBlueprint _ expr=:(Update _ _ _) chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TPPExpr "(mkBlueprint Update fallthrough)"
                          , syn_pattern_match_vars = []
                          , syn_cases = []
                          , syn_bound_vars = 'DM'.newMap}, chn)
mkBlueprint _ expr=:(Conditional _) chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TPPExpr "(mkBlueprint Conditional fallthrough)"
                          , syn_pattern_match_vars = []
                          , syn_cases = []
                          , syn_bound_vars = 'DM'.newMap}, chn)
mkBlueprint _ expr=:(AnyCodeExpr _ _ _) chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TPPExpr "(mkBlueprint AnyCodeExpr fallthrough)"
                          , syn_pattern_match_vars = []
                          , syn_cases = []
                          , syn_bound_vars = 'DM'.newMap}, chn)
mkBlueprint _ expr=:(ABCCodeExpr _ _) chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TPPExpr "(mkBlueprint ABCCodeExpr fallthrough)"
                          , syn_pattern_match_vars = []
                          , syn_cases = []
                          , syn_bound_vars = 'DM'.newMap}, chn)
mkBlueprint _ expr=:(MatchExpr _ _) chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TPPExpr "(mkBlueprint MatchExpr fallthrough)"
                          , syn_pattern_match_vars = []
                          , syn_cases = []
                          , syn_bound_vars = 'DM'.newMap}, chn)
mkBlueprint _ expr=:(IsConstructor _ _ _ _ _ _) chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TPPExpr "(mkBlueprint IsConstructor fallthrough)"
                          , syn_pattern_match_vars = []
                          , syn_cases = []
                          , syn_bound_vars = 'DM'.newMap}, chn)
mkBlueprint _ expr=:(DictionariesFunction _ _ _) chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TPPExpr "(mkBlueprint DictionariesFunction fallthrough)"
                          , syn_pattern_match_vars = []
                          , syn_cases = []
                          , syn_bound_vars = 'DM'.newMap}, chn)
mkBlueprint _ expr=:(Constant _ _ _) chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TPPExpr "(mkBlueprint Constant fallthrough)"
                          , syn_pattern_match_vars = []
                          , syn_cases = []
                          , syn_bound_vars = 'DM'.newMap}, chn)
mkBlueprint _ expr=:(ClassVariable _) chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TPPExpr "(mkBlueprint ClassVariable fallthrough)"
                          , syn_pattern_match_vars = []
                          , syn_cases = []
                          , syn_bound_vars = 'DM'.newMap}, chn)
mkBlueprint _ expr=:(DynamicExpr _) chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TPPExpr "(mkBlueprint DynamicExpr fallthrough)"
                          , syn_pattern_match_vars = []
                          , syn_cases = []
                          , syn_bound_vars = 'DM'.newMap}, chn)
mkBlueprint _ expr=:(TypeCodeExpression _) chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TPPExpr "(mkBlueprint TypeCodeExpression fallthrough)"
                          , syn_pattern_match_vars = []
                          , syn_cases = []
                          , syn_bound_vars = 'DM'.newMap}, chn)
mkBlueprint _ expr=:(TypeSignature _ _) chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TPPExpr "(mkBlueprint TypeSignature fallthrough)"
                          , syn_pattern_match_vars = []
                          , syn_cases = []
                          , syn_bound_vars = 'DM'.newMap}, chn)
mkBlueprint _ expr=:EE chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TPPExpr "(mkBlueprint EE fallthrough)"
                          , syn_pattern_match_vars = []
                          , syn_cases = []
                          , syn_bound_vars = 'DM'.newMap}, chn)
mkBlueprint _ expr=:(FailExpr _) chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TPPExpr "(mkBlueprint FailExpr fallthrough)"
                          , syn_pattern_match_vars = []
                          , syn_cases = []
                          , syn_bound_vars = 'DM'.newMap}, chn)
mkBlueprint _ expr chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TPPExpr "(mkBlueprint fallthrough)"
                          , syn_pattern_match_vars = []
                          , syn_cases = []
                          , syn_bound_vars = 'DM'.newMap}, chn)

fromBasicValue :: !BasicValue -> TLit
fromBasicValue (BVI str) = TInt (toInt str)
fromBasicValue (BVInt n) = TInt n
fromBasicValue (BVC c)   = TString c
fromBasicValue (BVB b)   = TBool b
fromBasicValue (BVR r)   = TReal (toReal r)
fromBasicValue (BVS str) = TString str

addUnique :: !Int !InhExpression -> InhExpression
addUnique n inh = {inh & inh_uid = inh.inh_uid ++ [n]}

symTyStr {st_result = {at_type}} = symTyStr` at_type
symTyStr` (TA tsi _)    = Just tsi.type_ident.id_name
symTyStr` (TAS tsi _ _) = Just tsi.type_ident.id_name
symTyStr` (_ --> t)     = symTyStr` t.at_type
symTyStr` (TFA _ t)     = symTyStr` t
symTyStr` (TFAC _ t _)  = symTyStr` t
symTyStr` _             = Nothing

varIsTask :: BoundVar InhExpression *ChnExpression -> *(Bool, *ChnExpression)
varIsTask bv inh chn
  = case 'DM'.get (ptrToInt bv.var_info_ptr) inh.inh_tyenv of
      Nothing -> (False, chn)
      Just t  -> typeIsBlueprintPart t inh chn
