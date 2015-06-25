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

withTwo :: App [Expression] (Expression Expression *ChnExpression -> *(SynExpression, *ChnExpression)) InhExpression *ChnExpression -> *(SynExpression, *ChnExpression)
withTwo app []        _ _   chn = ({syn_annot_expr = App app, syn_texpr = TLit "TODO withTwo []", syn_pattern_match_vars = []}, chn)
withTwo app [_]       _ _   chn = ({syn_annot_expr = App app, syn_texpr = TLit "TODO withTwo [_]", syn_pattern_match_vars = []}, chn)
withTwo app [x1:x2:_] f inh chn = f x1 x2 chn

wrapTraversable :: Int App [Expression] InhExpression *ChnExpression -> *(Expression, *ChnExpression)
wrapTraversable uid app args inh chn
  # (ok, pdss) = pdssAreDefined [PD_tonicExtWrapTraversable, PD_ConsSymbol, PD_NilSymbol] chn.chn_predef_symbols
  | not ok     = (App app, {chn & chn_predef_symbols = pdss})
  | otherwise
      # (icl, menv)  = (chn.chn_module_env)!me_icl_module
      # iclName      = icl.icl_name.id_name
      # (mdcl, menv) = reifyDclModule app.app_symb menv
      # (wrappedFnModNm, menv) = case mdcl of
                                     Just dcl -> (dcl.dcl_name.id_name, menv)
                                     _        -> (iclName, menv)
      # wrappedFnNm  = app.app_symb.symb_ident.id_name
      # (modCtx, fnCtx) = inh.inh_app_ctx
      # tuple2Idx = GetTupleConsIndex 2
      # heaps = chn.chn_heaps
      # (parentInfo, heaps, pdss) = appPredefinedSymbolWithEI tuple2Idx
                                    [ mkStr iclName
                                    , mkStr inh.inh_curr_task_name
                                    ] SK_Constructor heaps pdss
      # (appInfo, heaps, pdss) = appPredefinedSymbolWithEI tuple2Idx
                                    [ mkStr modCtx
                                    , mkStr fnCtx
                                    ] SK_Constructor heaps pdss
      # (wrapInfo, heaps, pdss) = appPredefinedSymbolWithEI tuple2Idx
                                    [ mkStr wrappedFnModNm
                                    , mkStr wrappedFnNm
                                    ] SK_Constructor heaps pdss
      # (expr, heaps, pdss) = appPredefinedSymbolWithEI PD_tonicExtWrapTraversable
                                [ App parentInfo
                                , App appInfo
                                , App wrapInfo
                                , mkInt uid
                                , App {app & app_args = []}
                                ] SK_Function heaps pdss
      = ( (App expr) @ args
        , {chn & chn_predef_symbols = pdss
               , chn_module_env = {menv & me_icl_module = icl}
               , chn_heaps = heaps})

wrapTaskApp :: Int String Expression InhExpression *ChnExpression -> *(Expression, *ChnExpression)
wrapTaskApp uid wrappedFnNm origExpr inh chn
  # (ok, pdss) = pdssAreDefined [PD_tonicExtWrapApp, PD_tonicExtWrapAppLam1, PD_tonicExtWrapAppLam2, PD_tonicExtWrapAppLam3, PD_ConsSymbol, PD_NilSymbol] chn.chn_predef_symbols
  | not ok     = (origExpr, {chn & chn_predef_symbols = pdss})
  | otherwise
      # (rem, menv)    = case origExpr of
                           App app
                             = argsRemaining app chn.chn_module_env
                           _ = (0, chn.chn_module_env)
      # (icl, menv)    = menv!me_icl_module
      # iclName        = icl.icl_name.id_name
      # (wrappedFnModNm, menv) = case origExpr of
                                   App app
                                     # (mdcl, menv) = reifyDclModule app.app_symb menv
                                     = case mdcl of
                                         Just dcl -> (dcl.dcl_name.id_name, menv)
                                         _        -> (iclName, menv)
                                   _ = (iclName, menv)
      # (modCtx, fnCtx) = inh.inh_app_ctx
      # tuple2Idx = GetTupleConsIndex 2
      # heaps = chn.chn_heaps
      # (parentInfo, heaps, pdss) = appPredefinedSymbolWithEI tuple2Idx
                                    [ mkStr iclName
                                    , mkStr inh.inh_curr_task_name
                                    ] SK_Constructor heaps pdss
      # (appInfo, heaps, pdss) = appPredefinedSymbolWithEI tuple2Idx
                                    [ mkStr modCtx
                                    , mkStr fnCtx
                                    ] SK_Constructor heaps pdss
      # (wrapInfo, heaps, pdss) = appPredefinedSymbolWithEI tuple2Idx
                                    [ mkStr wrappedFnModNm
                                    , mkStr wrappedFnNm
                                    ] SK_Constructor heaps pdss
      # (expr, heaps, pdss) = appPredefinedSymbolWithEI (findWrap rem)
                                [ App parentInfo
                                , App appInfo
                                , App wrapInfo
                                , mkInt inh.inh_parent_uid
                                , mkInt uid
                                , origExpr
                                ] SK_Function heaps pdss
      = ( App expr
        , {chn & chn_predef_symbols = pdss
               , chn_module_env = {menv & me_icl_module = icl}
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

getAssoc app_symb menv
  # (mPrio, menv) = reifySymbIdentPriority app_symb menv
  = case mPrio of
      Just prio -> (fromPriority prio, menv)
      _         -> (TNoPrio, menv)

mkBlueprint :: !InhExpression !Expression !*ChnExpression -> *(!SynExpression, !*ChnExpression)
mkBlueprint inh expr=:(App app=:{app_symb}) chn
  # (isTonicFunctor, chn) = symbIdentIsTask app.app_symb chn
  # ((ctxs, args), menv)  = dropAppContexts app chn.chn_module_env
  # chn                   = { chn & chn_module_env = menv }
  | identIsLambda app_symb.symb_ident
      # ((args, tFd), menv) = reifyArgsAndDef app_symb chn.chn_module_env
      # (syne, chn)         = mkBlueprint inh (getFunRhs tFd) { chn & chn_module_env = menv }
      # pats                = [case freeVarName x of
                                 "_x" -> case syne.syn_pattern_match_vars of
                                           [(_, e):_] -> e
                                           _          -> TVar Nothing "_x"
                                 x    -> TVar Nothing x
                              \\ x <- args | x.fv_def_level == -1]
      # menv                = updateWithAnnot app_symb syne.syn_annot_expr chn.chn_module_env
      = ( { syn_annot_expr = App app
          , syn_texpr      = TLam pats syne.syn_texpr
          , syn_pattern_match_vars = []
          }
        , {chn & chn_module_env = menv})
  | isTonicFunctor = mkMApp app ctxs args inh chn
  | appIsListComp app
      = case [orig \\ (ident, orig) <- inh.inh_list_compr
                    | app.app_symb.symb_ident.id_name == ident] of
          [] = mkFApp app ctxs args inh chn
          [orig:_]
            = ({ syn_annot_expr = expr
               , syn_texpr      = TLit (ppCompact (ppParsedExpr orig))
               , syn_pattern_match_vars = []}, chn)
  | otherwise      = mkFApp app ctxs args inh chn
  where
  mkMApp app ctxs args inh chn
    # appName       = app.app_symb.symb_ident.id_name
    # (uid, chn)    = dispenseUnique chn
    # (mFunTy, menv) = reifyFunType app.app_symb chn.chn_module_env
    # (assoc, menv)  = getAssoc app.app_symb menv
    # (mst, menv)   = reifySymbIdentSymbolType app.app_symb menv
    # mTyStr        = case mst of
                        Just st -> symTyStr st
                        _       -> Nothing
    # chn           = {chn & chn_module_env = menv}
    # (dclnm, menv) = case reifyDclModule app.app_symb chn.chn_module_env of
                        (Just dcl, menv) = (dcl.dcl_name.id_name, menv)
                        (_       , menv)
                          # (iclmod, menv) = menv!me_icl_module
                          = (iclmod.icl_name.id_name, menv)
    # chn           = {chn & chn_module_env = menv}
    # (ps, chn)     = mapSt (\x chn -> mkBlueprint {inh & inh_parent_uid = uid, inh_app_ctx = (dclnm, appName)} x chn) args chn
    # args`         = map (\syn -> syn.syn_annot_expr) ps
    # (isTraversable, chn) = mkTrav mst ctxs args inh chn
    # (app`, chn)   = if isTraversable
                        (wrapTraversable uid app args` inh chn)
                        (App {app & app_args = args`}, chn)
    # (app`, chn)   = wrapTaskApp uid appName app` inh chn
    = ({ syn_annot_expr = app`
       , syn_texpr      = TMApp (Just uid) Nothing mTyStr dclnm (appFunName app) (map (\syn -> syn.syn_texpr) ps) assoc
       , syn_pattern_match_vars = []}, chn)
    where
    // TODO FIXME This check is horribly broken
    mkTrav (Just {st_args = [{at_type}]}) ctxs [arg] inh chn
      = (isListTy at_type, chn)
          //= typeHasClassInstance at_type PD_TraversableClass inh chn
      //| (False, chn)
      where
      isListTy :: Type -> Bool
      isListTy (TA tsi [at])    = tsi.type_ident.id_name == PD_ListType_String && atypeIsTask at
      isListTy (TAS tsi [at] _) = tsi.type_ident.id_name == PD_ListType_String && atypeIsTask at
      isListTy _                = False
    mkTrav _ _ _ _ chn = (False, chn)

  mkFApp app ctxs args inh chn
    # appName       = app.app_symb.symb_ident.id_name
    # (dclnm, menv) = case reifyDclModule app.app_symb chn.chn_module_env of
                        (Just dcl, menv) = (dcl.dcl_name.id_name, menv)
                        (_       , menv)
                          # (iclmod, menv) = menv!me_icl_module
                          = (iclmod.icl_name.id_name, menv)
    # (assoc, menv) = getAssoc app.app_symb menv
    # (ps, chn)     = mapSt (\x chn -> mkBlueprint inh x chn) args {chn & chn_module_env = menv}
    = ({ syn_annot_expr = App {app & app_args = ctxs ++ map (\syn -> syn.syn_annot_expr) ps}
       , syn_texpr      = TFApp appName (map (\syn -> syn.syn_texpr) ps) assoc
       , syn_pattern_match_vars = []}, chn)

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
mkBlueprint inh (e @ []) chn = abort "atC: no args" // TODO e is a non-applied higher order function. What do we do with this?
mkBlueprint inh (e=:(App app) @ es) chn
  # (mfd, menv) = reifyFunDef app.app_symb chn.chn_module_env
  # fd          = fromMaybe (abort ("atC: failed to reify " +++ app.app_symb.symb_ident.id_name)) mfd
  | identIsLambda app.app_symb.symb_ident
      # letargs       = drop (length app.app_args) (getFunArgs fd)
      # (binds, menv) = zipWithSt zwf letargs es menv
      # chn           = { chn & chn_module_env = menv }
      # (syne, chn)   = mkBlueprint inh (getFunRhs fd) chn
      # menv          = updateWithAnnot app.app_symb syne.syn_annot_expr chn.chn_module_env
      # chn           = { chn & chn_module_env = menv}
      = ({ syn_annot_expr = e @ es
         , syn_texpr      = TLit "TODO @"
         , syn_pattern_match_vars = syne.syn_pattern_match_vars}, chn)
  | otherwise
      # (assoc, menv)     = getAssoc app.app_symb menv
      # (texpr, es`, chn) = case fd.fun_type of
                              Yes ft | symTyIsTask ft
                                # (uid, chn)    = dispenseUnique {chn & chn_module_env = menv}
                                # (es`, chn)    = mapSt (mkBlueprint {inh & inh_parent_uid = uid}) es chn
                                # (mst, menv)   = reifySymbIdentSymbolType app.app_symb chn.chn_module_env
                                # mTyStr        = case mst of
                                                    Just st -> symTyStr st
                                                    _       -> Nothing
                                # (dclnm, menv) = case reifyDclModule app.app_symb menv of
                                                    (Just dcl, menv) = (dcl.dcl_name.id_name, menv)
                                                    (_       , menv)
                                                      # (iclmod, menv) = menv!me_icl_module
                                                      = (iclmod.icl_name.id_name, menv)
                                = ( TMApp (Just uid) Nothing mTyStr dclnm (appFunName app) (map (\syn -> syn.syn_texpr) es`) assoc
                                  , es`, {chn & chn_module_env = menv})
                              _
                                # (es`, chn) = mapSt (mkBlueprint inh) es {chn & chn_module_env = menv}
                                = ( TFApp app.app_symb.symb_ident.id_name (map (\x -> x.syn_texpr) es`) assoc
                                  , es`, chn)
      = ({ syn_annot_expr = e @ (map (\x -> x.syn_annot_expr) es`)
         , syn_texpr      = texpr
         , syn_pattern_match_vars = []}, chn)
  where
    zwf eVar eVal menv
      # fvl         = ppFreeVar eVar
      # (fvr, menv) = ppExpression eVal menv
      = ((ppCompact fvl, ppCompact fvr), menv)
mkBlueprint inh (e=:(Var bv) @ es) chn
  # (bps, chn) = mapSt (mkBlueprint inh) es chn
  | varIsTask bv inh
      # (uid, chn)  = dispenseUnique chn
      # (var`, chn) = wrapTaskApp uid "(Var @ es)" (e @ es) inh chn
      # mTyStr      = case 'DM'.get bv.var_ident.id_name inh.inh_tyenv of
                        Just x -> symTyStr` x
                        _      -> Nothing
      = ({ syn_annot_expr = var`
         , syn_texpr      = TMApp (Just uid) Nothing mTyStr "" bv.var_ident.id_name (map (\syn -> syn.syn_texpr) bps) TNoPrio
         , syn_pattern_match_vars = []}, chn)
  | otherwise
      = ({ syn_annot_expr = Var bv @ es
         , syn_texpr      = TFApp bv.var_ident.id_name (map (\syn -> syn.syn_texpr) bps) TNoPrio
         , syn_pattern_match_vars = []}, chn)
mkBlueprint inh (e @ es) chn = ({ syn_annot_expr = e @ es
                              , syn_texpr      = TLit "TODO @"
                              , syn_pattern_match_vars = []}, chn)
mkBlueprint inh (Let lt) chn
  # boundVars = [bnd.lb_dst.fv_ident.id_name \\ bnd <- getLetBinds lt]
  # mexpr     = listToMaybe [ bnd.lb_src \\ bnd <- getLetBinds lt
                            | bnd.lb_dst.fv_ident.id_name == "_case_var"]
  = mkLet mexpr lt {inh & inh_vars_in_scope = 'DS'.union inh.inh_vars_in_scope ('DS'.fromList boundVars)} chn
  where
  mkLet (Just expr=:(App app)) lt inh chn
    | appIsListComp app
        = case [orig \\ (ident, orig) <- inh.inh_list_compr
                      | app.app_symb.symb_ident.id_name == ident] of
            []
              # (syn, chn) = mkBlueprint {inh & inh_case_expr = Just expr} lt.let_expr chn
              # l          = {lt & let_expr = syn.syn_annot_expr}
              = ({syn & syn_annot_expr = Let l}, chn)
              // TODO Reconstruct the LC
            [orig:_]
              # (syn, chn) = mkBlueprint {inh & inh_case_expr = Just expr} lt.let_expr chn
              # l          = {lt & let_expr = syn.syn_annot_expr}
              = ({syn & syn_annot_expr = Let l, syn_texpr = TLit (ppCompact (ppParsedExpr orig))}, chn)
  mkLet (Just expr) lt inh chn
    # (syn, chn) = mkBlueprint {inh & inh_case_expr = Just expr} lt.let_expr chn
    # l          = {lt & let_expr = syn.syn_annot_expr}
    = ({syn & syn_annot_expr = Let l}, chn)
  mkLet Nothing lt inh chn
    # (tys, chn)   = letTypes lt.let_info_ptr chn
    # (binds, chn) = flattenBinds lt chn
    # tyenv        = zipSt (\(TLit v, _) t tyenv -> 'DM'.put v t tyenv) binds tys inh.inh_tyenv // TODO This probably won't work for arbitrary patterns, so we actually need to be a bit smarter here and extract all variables from the patterns, instead of just PP'ing the pattern and using that as index
    # (syn, chn)   = mkBlueprint {inh & inh_tyenv = tyenv} lt.let_expr chn
    = ({ syn_annot_expr = Let {lt & let_expr = syn.syn_annot_expr}
       , syn_texpr      = TLet binds syn.syn_texpr
       , syn_pattern_match_vars = syn.syn_pattern_match_vars}, chn)
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
      = foldrSt f (getLetBinds lt) ([], chn)
      where
      f bnd (xs, chn)
        # (rhs, chn) = mkBlueprint inh bnd.lb_src chn
        = ([(TLit bnd.lb_dst.fv_ident.id_name, rhs.syn_texpr):xs], chn)
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
  # caseExpr     = fromMaybe cs.case_expr inh.inh_case_expr
  # (cesyn, chn) = mkBlueprint inh caseExpr chn
  = case (cs.case_explicit, cs.case_expr, cs.case_guards) of
      (False, Var bv, AlgebraicPatterns gi [ap:_])
        # (fvds, chn)   = mapSt (mkBlueprint inh o FreeVar) ap.ap_vars chn
        # (clexpr, chn) = case fvds of
                            [] = (TLit "", chn)
                            args
                              # menv          = chn.chn_module_env
                              # (mprio, menv) = if (ap.ap_symbol.glob_module == chn.chn_module_env.me_main_dcl_module_n)
                                                  (reifyFunDefsIdxPriority ap.ap_symbol.glob_object.ds_index menv)
                                                  (reifyDclModulesIdxPriority` ap.ap_symbol.glob_module ap.ap_symbol.glob_object.ds_index menv)
                              # assoc         = case mprio of
                                                  Just p -> fromPriority p
                                                  _      -> TNoPrio
                              # chn           = {chn & chn_module_env = menv}
                              = (TFApp ap.ap_symbol.glob_object.ds_ident.id_name (map (\x -> x.syn_texpr) args) assoc, chn)
        # (syn, chn)    = mkAlts` inh 0 ap.ap_expr chn
        = ({ syn_annot_expr = Case {cs & case_guards = AlgebraicPatterns gi [{ap & ap_expr = syn.syn_annot_expr}]}
           , syn_texpr      = syn.syn_texpr
           , syn_pattern_match_vars = [(bv, clexpr) : syn.syn_pattern_match_vars]}, chn)
      _
        # ((guards, syns), chn) = mkAlts cs.case_guards chn
        # ((def, syns), chn)    = case cs.case_default of
                                    Yes def
                                      # (syn, chn) = mkAlts` inh (numGuards cs.case_guards) def chn
                                      = case syns of
                                          [(TLit "True", _)]
                                            = ((Yes syn.syn_annot_expr, [(TLit "False", syn):syns]), chn)
                                          _ = ((Yes syn.syn_annot_expr, [(TLit "_", syn):syns]), chn)
                                    _ = ((No, syns), chn)
        = ({ syn_annot_expr = Case {cs & case_default = def, case_guards = guards}
           , syn_texpr      = TCaseOrIf cesyn.syn_texpr (reverse (map (\(d, s) -> (d, s.syn_texpr)) syns))
           , syn_pattern_match_vars = foldr (\(_, syn) acc -> syn.syn_pattern_match_vars ++ acc) [] syns}, chn)
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
        mkAp sym []   chn = (TLit (ppCompact ('PPrint'.text sym.glob_object.ds_ident.id_name)), chn)
        mkAp sym vars chn
          # (fvds, chn) = mapSt (mkBlueprint inh o FreeVar) vars chn
          = (TFApp (ppCompact ('PPrint'.text sym.glob_object.ds_ident.id_name)) (map (\x -> x.syn_texpr) fvds) TNoPrio, chn)
  mkAlts c=:(BasicPatterns bt bps) chn
    # ((bps, syns, _), chn) = foldr f (([], [], 0), chn) bps
    = ((BasicPatterns bt bps, syns), chn)
    where
      f bp ((bps, syns, n), chn)
        # (syn, chn)  = mkAlts` inh n bp.bp_expr chn
        # bp          = {bp & bp_expr = syn.syn_annot_expr}
        = (([bp:bps], [(TLit (ppCompact (ppBasicValue bp.bp_value)), syn):syns], n + 1), chn)
  mkAlts c chn = ((c, []), chn)

  mkAlts` :: InhExpression Int Expression *ChnExpression -> *(SynExpression, *ChnExpression)
  mkAlts` inh n expr chn
    # inh = {inh & inh_case_expr = Nothing }
    = mkBlueprint inh expr chn

mkBlueprint inh (Var bv) chn
  | varIsTask bv inh
      # (uid, chn)  = dispenseUnique chn
      # (var`, chn) = wrapTaskApp uid "(Var)" (Var bv) inh chn
      = ({ syn_annot_expr = var`
         , syn_texpr      = TVar (Just uid) bv.var_ident.id_name
         , syn_pattern_match_vars = []}, chn)
  | otherwise
      = ({ syn_annot_expr = Var bv
         , syn_texpr      = TVar Nothing bv.var_ident.id_name
         , syn_pattern_match_vars = []}, chn)
mkBlueprint _ expr=:(FreeVar fv) chn
  = ({ syn_annot_expr = expr
     , syn_texpr      = TVar Nothing fv.fv_ident.id_name
     , syn_pattern_match_vars = []}, chn)
mkBlueprint _ expr=:(BasicExpr bv) chn
  = ({ syn_annot_expr = expr
     , syn_texpr      = TLit (ppCompact (ppBasicValue bv))
     , syn_pattern_match_vars = []}, chn)
mkBlueprint inh expr=:(Selection st selExpr sels) chn
  # (syn, chn)      = mkBlueprint inh selExpr chn
  # (selExprs, chn) = mapSt (mkSelExprs) sels chn
  = ({ syn_annot_expr = Selection st selExpr sels
     , syn_texpr      = TSel syn.syn_texpr selExprs
     , syn_pattern_match_vars = []}, chn)
  where
  mkSelExprs (RecordSelection gds _) chn
    # d = ppDefinedSymbol gds.glob_object
    = (TLit (ppCompact d), chn)
  mkSelExprs (ArraySelection gds _ e) chn // TODO use e
    # d = ppDefinedSymbol gds.glob_object
    = (TLit (ppCompact d), chn)
  mkSelExprs (DictionarySelection bv sels _ e) chn
    = (TLit "TODO mkSelExprs DictionarySelection ", chn)
mkBlueprint inh expr=:(TupleSelect _ i e) chn
  # (syn, chn) = mkBlueprint inh e chn
  # te         = TSel syn.syn_texpr [TLit (toString i)]
  = ({ syn_annot_expr = expr
     , syn_texpr      = te
     , syn_pattern_match_vars = []}, chn)
mkBlueprint inh expr=:(RecordUpdate {glob_object={ds_ident}} expression expressions) chn
  # (syn, chn)  = mkBlueprint inh expression chn
  # (syns, chn) = mapSt (\e -> mkBlueprint inh e.bind_src) expressions chn
  # te          = TRecUpd ds_ident.id_name syn.syn_texpr (map (\x -> x.syn_texpr) syns)
  = ({ syn_annot_expr = expr
     , syn_texpr      = te
     , syn_pattern_match_vars = []}, chn)
mkBlueprint _ expr=:(NoBind _) chn
  = ({ syn_annot_expr = expr
     , syn_texpr      = TNoBind
     , syn_pattern_match_vars = []}, chn)

mkBlueprint _ expr=:(Update _ _ _) chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TLit "(mkBlueprint Update fallthrough)"
                          , syn_pattern_match_vars = []}, chn)
mkBlueprint _ expr=:(Conditional _) chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TLit "(mkBlueprint Conditional fallthrough)"
                          , syn_pattern_match_vars = []}, chn)
mkBlueprint _ expr=:(AnyCodeExpr _ _ _) chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TLit "(mkBlueprint AnyCodeExpr fallthrough)"
                          , syn_pattern_match_vars = []}, chn)
mkBlueprint _ expr=:(ABCCodeExpr _ _) chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TLit "(mkBlueprint ABCCodeExpr fallthrough)"
                          , syn_pattern_match_vars = []}, chn)
mkBlueprint _ expr=:(MatchExpr _ _) chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TLit "(mkBlueprint MatchExpr fallthrough)"
                          , syn_pattern_match_vars = []}, chn)
mkBlueprint _ expr=:(IsConstructor _ _ _ _ _ _) chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TLit "(mkBlueprint IsConstructor fallthrough)"
                          , syn_pattern_match_vars = []}, chn)
mkBlueprint _ expr=:(DictionariesFunction _ _ _) chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TLit "(mkBlueprint DictionariesFunction fallthrough)"
                          , syn_pattern_match_vars = []}, chn)
mkBlueprint _ expr=:(Constant _ _ _) chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TLit "(mkBlueprint Constant fallthrough)"
                          , syn_pattern_match_vars = []}, chn)
mkBlueprint _ expr=:(ClassVariable _) chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TLit "(mkBlueprint ClassVariable fallthrough)"
                          , syn_pattern_match_vars = []}, chn)
mkBlueprint _ expr=:(DynamicExpr _) chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TLit "(mkBlueprint DynamicExpr fallthrough)"
                          , syn_pattern_match_vars = []}, chn)
mkBlueprint _ expr=:(TypeCodeExpression _) chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TLit "(mkBlueprint TypeCodeExpression fallthrough)"
                          , syn_pattern_match_vars = []}, chn)
mkBlueprint _ expr=:(TypeSignature _ _) chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TLit "(mkBlueprint TypeSignature fallthrough)"
                          , syn_pattern_match_vars = []}, chn)
mkBlueprint _ expr=:EE chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TLit "(mkBlueprint EE fallthrough)"
                          , syn_pattern_match_vars = []}, chn)
mkBlueprint _ expr=:(FailExpr _) chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TLit "(mkBlueprint FailExpr fallthrough)"
                          , syn_pattern_match_vars = []}, chn)
mkBlueprint _ expr chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TLit "(mkBlueprint fallthrough)"
                          , syn_pattern_match_vars = []}, chn)

symTyStr {st_result = {at_type}} = symTyStr` at_type
symTyStr` (TA tsi _)    = Just tsi.type_ident.id_name
symTyStr` (TAS tsi _ _) = Just tsi.type_ident.id_name
symTyStr` (_ --> t)     = symTyStr` t.at_type
symTyStr` (TFA _ t)     = symTyStr` t
symTyStr` (TFAC _ t _)  = symTyStr` t
symTyStr` _             = Nothing

varIsTask :: BoundVar InhExpression -> Bool
varIsTask bv inh
  = case 'DM'.get bv.var_ident.id_name inh.inh_tyenv of
      Nothing -> False
      Just t  -> typeIsTask t

// TODO Relate the match_vars from the body to the vars from the arguments
funToGraph :: FunDef FunDef [(String, ParsedExpr)] !{#{!InstanceTree}} !{#CommonDefs} InhExpression *ChnExpression
           -> *(Maybe ([(TExpr, TExpr)], TExpr, Expression), *ChnExpression)
funToGraph fd=:{fun_ident=fun_ident, fun_body = TransformedBody tb} fd_cpy list_comprehensions instance_tree common_defs inh chn = mkBody
  where
  mkBody
    # (argTys, tyenv) = zipWithSt (\arg t st -> ((arg, t), 'DM'.put arg.fv_ident.id_name t st)) tb.tb_args (funArgTys fd_cpy) 'DM'.newMap
    # (syn, chn)      = mkBlueprint {inh & inh_tyenv = tyenv} tb.tb_rhs chn
    = ( Just (map (\(arg, ty) -> (mkArgPP syn.syn_pattern_match_vars arg, typeToTCleanExpr ty)) argTys, syn.syn_texpr, syn.syn_annot_expr)
      , chn)
  mkArgPP pmvars arg
    = case arg.fv_ident.id_name of
        "_x"
          = case [clexpr \\ (bv, clexpr) <- pmvars | bv.var_info_ptr == arg.fv_info_ptr] of
              []    -> TLit "(shouldn't happen)"
              [x:_] -> x
        idnm
          = TVar Nothing idnm
funToGraph _ _ _ _ _ _ chn = (Nothing, chn)
