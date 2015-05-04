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
  //mkLCExpr (PE_Tuple es)    = AppCleanExpr TNonAssoc (predefined_idents.[GetTupleConsIndex (length es)].id_name) (map mkLCExpr es)
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

wrapTaskApp :: Expression InhExpression *ChnExpression -> *(Expression, *ChnExpression)
wrapTaskApp origExpr inh chn
  # (ok, pdss) = pdssAreDefined [PD_tonicWrapApp, PD_tonicWrapAppLam1, PD_tonicWrapAppLam2, PD_tonicWrapAppLam3, PD_ConsSymbol, PD_NilSymbol] chn.chn_predef_symbols
  # chn        = {chn & chn_predef_symbols = pdss}
  | not ok     = (origExpr, chn)
  | otherwise
      # (rem, menv)    = case origExpr of
                           App app
                             = argsRemaining app chn.chn_module_env
                           _ = (0, chn.chn_module_env)
      # (icl, menv)    = menv!me_icl_module
      # nm             = icl.icl_name.id_name
      # (wrappedFnModNm, menv) = case origExpr of
                                   App app
                                     # (mdcl, menv) = reifyDclModule app.app_symb menv
                                     = case mdcl of
                                         Just dcl -> (dcl.dcl_name.id_name, menv)
                                         _        -> (nm, menv)
                                   _ = (nm, menv)
      # wrappedFnNm    = case origExpr of
                           App app -> app.app_symb.symb_ident.id_name
                           _       -> ""
      # (ids, pdss)    = toStatic (map mkInt inh.inh_ids) chn.chn_predef_symbols
      # (expr, heaps, pdss) = appPredefinedSymbolWithEI (findWrap rem)
                         [ mkStr nm
                         , mkStr inh.inh_curr_task_name
                         , mkStr wrappedFnModNm
                         , mkStr wrappedFnNm
                         , ids
                         , origExpr
                         ] SK_Function chn.chn_heaps pdss
      = ( App expr
        , {chn & chn_predef_symbols = pdss
               , chn_module_env = {menv & me_icl_module = icl}
               , chn_heaps = heaps})
  where
  findWrap :: Int -> Int
  findWrap 0 = PD_tonicWrapApp
  findWrap 1 = PD_tonicWrapAppLam1
  findWrap 2 = PD_tonicWrapAppLam2
  findWrap 3 = PD_tonicWrapAppLam3
  findWrap n = abort ("No tonicWrapLam" +++ toString n)

mkBlueprint :: !Expression !InhExpression !*ChnExpression -> *(!SynExpression, !*ChnExpression)
mkBlueprint (App app=:{app_symb}) inh chn
  # (isTonicFunctor, chn) = symbIdentIsTask app.app_symb chn
  # ((ctxs, args), menv)  = dropAppContexts app chn.chn_module_env
  # chn                   = { chn & chn_module_env = menv }
  | identIsLambda app_symb.symb_ident
      # ((args, tFd), menv) = reifyArgsAndDef app_symb chn.chn_module_env
      # (syne, chn)         = mkBlueprint (getFunRhs tFd) inh { chn & chn_module_env = menv }
      # menv                = updateWithAnnot app_symb syne.syn_annot_expr chn.chn_module_env
      = ( { syn_annot_expr = App app
          , syn_texpr      = TLam [freeVarName x \\ x <- args | x.fv_def_level == -1] syne.syn_texpr
          , syn_pattern_match_vars = []
          }
        , {chn & chn_module_env = menv})
  | isTonicFunctor = mkMApp app ctxs args inh chn
  | otherwise      = mkFApp app ctxs args inh chn
  where
  mkMApp app ctxs args inh chn
    # (dclnm, menv) = case reifyDclModule app.app_symb chn.chn_module_env of
                        (Just dcl, menv) = (dcl.dcl_name.id_name, menv)
                        (_       , menv)
                          # (iclmod, menv) = menv!me_icl_module
                          = (iclmod.icl_name.id_name, menv)
    # (mst, menv)   = reifySymbIdentSymbolType app.app_symb menv
    # mTyStr        = case mst of
                        Just st -> symTy st
                        _       -> Nothing
    # chn           = {chn & chn_module_env = menv}
    # (ps, chn)     = mapSt (\(n, arg) -> mkBlueprint arg (addInhId inh n)) (zip2 [0..] args) chn
    # (app`, chn)   = wrapTaskApp (App {app & app_args = map (\syn -> syn.syn_annot_expr) ps}) inh chn
    = ({ syn_annot_expr = app`
       , syn_texpr      = TMApp inh.inh_ids mTyStr dclnm (appFunName app) (map (\syn -> syn.syn_texpr) ps)
       , syn_pattern_match_vars = []}, chn)
    where
    symTy {st_result = {at_type}} = symTy` at_type
    symTy` (TA tsi _)    = Just tsi.type_ident.id_name
    symTy` (TAS tsi _ _) = Just tsi.type_ident.id_name
    symTy` (_ --> t)     = symTy` t.at_type
    symTy` (TFA _ t)     = symTy` t
    symTy` (TFAC _ t _)  = symTy` t
    symTy` _             = Nothing

  mkFApp app ctxs args inh chn
    # (mFunTy, menv) = reifyFunType app.app_symb chn.chn_module_env
    # (ps, chn)      = mapSt (\arg -> mkBlueprint arg inh) args {chn & chn_module_env = menv}
    # assoc          = case mFunTy of
                         Just {ft_priority = Prio assoc n} -> case assoc of
                                                                LeftAssoc  -> TLeftAssoc n
                                                                RightAssoc -> TRightAssoc n
                                                                NoAssoc    -> TNonAssoc
                         _ -> TNonAssoc
    = ({ syn_annot_expr = App {app & app_args = ctxs ++ map (\syn -> syn.syn_annot_expr) ps}
       , syn_texpr      = TFApp assoc (appFunName app) (map (\syn -> syn.syn_texpr) ps)
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
mkBlueprint (e @ []) inh chn = abort "atC: no args" // TODO e is a non-applied higher order function. What do we do with this?
mkBlueprint (e=:(App app) @ es) inh chn
  // TODO : Introduce lets in the graph for all variables that are being applied
  | identIsLambda app.app_symb.symb_ident
      # (mfd, menv)   = reifyFunDef app.app_symb chn.chn_module_env
      # fd            = fromMaybe (abort ("atC: failed to reify " +++ app.app_symb.symb_ident.id_name)) mfd
      # letargs       = drop (length app.app_args) (getFunArgs fd)
      # (binds, menv) = zipWithSt zwf letargs es menv
      # chn           = { chn & chn_module_env = menv }
      //# (syne, chn)   = mkBlueprint (getFunRhs fd) (addInhId inh 0) chn
      # (syne, chn)   = mkBlueprint (getFunRhs fd) inh chn
      # menv          = updateWithAnnot app.app_symb syne.syn_annot_expr chn.chn_module_env
      # chn           = { chn & chn_module_env = menv}
      = ({ syn_annot_expr = e @ es
         , syn_texpr      = TLit "TODO @"
         , syn_pattern_match_vars = syne.syn_pattern_match_vars}, chn)
  | otherwise
      # (mFunTy, menv) = reifyFunType app.app_symb chn.chn_module_env
      # assoc          = case mFunTy of
                           Just {ft_priority = Prio assoc n} -> case assoc of
                                                                  LeftAssoc  -> TLeftAssoc n
                                                                  RightAssoc -> TRightAssoc n
                                                                  NoAssoc    -> TNonAssoc
                           _ -> TNonAssoc
      # (es`, chn)     = mapSt (\arg -> mkBlueprint arg inh) es {chn & chn_module_env = menv}
      = ({ syn_annot_expr = e @ (map (\x -> x.syn_annot_expr) es`)
         , syn_texpr      = TFApp assoc app.app_symb.symb_ident.id_name (map (\x -> x.syn_texpr) es`)
         , syn_pattern_match_vars = []}, chn)
  where
    zwf eVar eVal menv
      # (fvl, menv) = ppFreeVar eVar menv
      # (fvr, menv) = ppExpression eVal menv
      = ((ppCompact fvl, ppCompact fvr), menv)
mkBlueprint (e @ es) _ chn = ({ syn_annot_expr = e @ es
                              , syn_texpr      = TLit "TODO @"
                              , syn_pattern_match_vars = []}, chn)
mkBlueprint (Let lt) inh chn
  # mexpr = listToMaybe [ bnd.lb_src \\ bnd <- getLetBinds lt
                        | bnd.lb_dst.fv_ident.id_name == "_case_var"]
  = mkLet mexpr lt inh chn
  where
  mkLet (Just expr=:(App app)) lt inh chn
    | appIsListComp app
        = case [orig \\ (ident, orig) <- inh.inh_list_compr
                      | app.app_symb.symb_ident.id_name == ident] of
            []
              # (syn, chn) = mkBlueprint lt.let_expr (addInhId {inh & inh_case_expr = Just expr} 0) chn
              # l          = {lt & let_expr = syn.syn_annot_expr}
              = ({syn & syn_annot_expr = Let l}, chn)
              // TODO Reconstruct the LC
            [orig:_]
              # (syn, chn) = mkBlueprint lt.let_expr (addInhId {inh & inh_case_expr = Just expr} 0) chn
              # l          = {lt & let_expr = syn.syn_annot_expr}
              = ({syn & syn_annot_expr = Let l}, chn)
  mkLet (Just expr) lt inh chn
    # (syn, chn) = mkBlueprint lt.let_expr (addInhId {inh & inh_case_expr = Just expr} 0) chn
    # l          = {lt & let_expr = syn.syn_annot_expr}
    = ({syn & syn_annot_expr = Let l}, chn)
  mkLet Nothing lt inh chn
    # (tys, chn)   = letTypes lt.let_info_ptr chn
    # (binds, chn) = flattenBinds lt chn
    # tyenv        = zipSt (\(TLit v, _) t tyenv -> 'DM'.put v t tyenv) binds tys inh.inh_tyenv // TODO This probably won't work for arbitrary patterns, so we actually need to be a bit smarter here and extract all variables from the patterns, instead of just PP'ing the pattern and using that as index
    # (syn, chn)   = mkBlueprint lt.let_expr (addInhId {inh & inh_tyenv = tyenv} 0) chn
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
        # (rhs, chn) = mkBlueprint bnd.lb_src inh chn
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
mkBlueprint (Case cs) inh chn
  # caseExpr   = fromMaybe cs.case_expr inh.inh_case_expr
  # (ed, menv) = ppExpression caseExpr chn.chn_module_env
  # chn        = {chn & chn_module_env = menv}
  = case (ppCompact ed, cs.case_expr, cs.case_guards) of
      ("_x", Var bv, AlgebraicPatterns gi [ap])
        # (syn, chn)  = mkAlts` 0 ap.ap_expr chn
        # (fvds, chn) = mapSt (\x chn -> mkBlueprint (FreeVar x) inh chn) ap.ap_vars chn
        # clexpr      = case fvds of
                          []   -> TLit ""
                          args -> TFApp TNonAssoc ap.ap_symbol.glob_object.ds_ident.id_name (map (\x -> x.syn_texpr) args) // TODO Associativity
        = ({ syn_annot_expr = Case {cs & case_guards = AlgebraicPatterns gi [{ap & ap_expr = syn.syn_annot_expr}]}
           , syn_texpr      = syn.syn_texpr
           , syn_pattern_match_vars = [(bv, clexpr) : syn.syn_pattern_match_vars]}, chn)
      _
        # ((guards, syns), chn) = mkAlts cs.case_guards chn
        # ((def, syns), chn)    = case cs.case_default of
                                    Yes def
                                      # (syn, chn) = mkAlts` (numGuards cs.case_guards) def chn
                                      = case syns of
                                          [(TVar _ "True", _)]
                                            = ((Yes syn.syn_annot_expr, [(TLit "False", syn):syns]), chn)
                                          _ = ((Yes syn.syn_annot_expr, [(TLit "_", syn):syns]), chn)
                                    _ = ((No, syns), chn)
        = ({ syn_annot_expr = Case {cs & case_default = def, case_guards = guards}
           , syn_texpr      = TCaseOrIf (TVar [] (ppCompact ed)) (map (\(d, s) -> (d, s.syn_texpr)) syns)
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
        # (syn, chn) = mkAlts` n ap.ap_expr chn
        # ap         = {ap & ap_expr = syn.syn_annot_expr}
        = (([ap:aps], [(apd, syn):syns], n + 1), chn)
        where
        mkAp sym []   chn = (TLit (ppCompact ('PPrint'.text sym.glob_object.ds_ident.id_name)), chn)
        mkAp sym vars chn
          # (fvds, chn) = mapSt (\x chn -> mkBlueprint (FreeVar x) inh chn) vars chn
          // TODO TNonAssoc?
          = (TFApp TNonAssoc (ppCompact ('PPrint'.text sym.glob_object.ds_ident.id_name)) (map (\x -> x.syn_texpr) fvds), chn)
  mkAlts c=:(BasicPatterns bt bps) chn
    # ((bps, syns, _), chn) = foldr f (([], [], 0), chn) bps
    = ((BasicPatterns bt bps, syns), chn)
    where
      f bp ((bps, syns, n), chn)
        # (syn, chn)  = mkAlts` n bp.bp_expr chn
        # bp          = {bp & bp_expr = syn.syn_annot_expr}
        = (([bp:bps], [(TLit (ppCompact (ppBasicValue bp.bp_value)), syn):syns], n + 1), chn)
  mkAlts c chn = ((c, []), chn)

  mkAlts` :: Int Expression *ChnExpression -> *(SynExpression, *ChnExpression)
  mkAlts` n expr chn
    # inh = {inh & inh_case_expr = Nothing }
    = mkBlueprint expr (addInhId inh n) chn

mkBlueprint (Var bv) inh chn
  | varIsTask bv inh
      # (var`, chn) = wrapTaskApp (Var bv) inh chn
      = ({ syn_annot_expr = var`
         , syn_texpr      = TVar inh.inh_ids bv.var_ident.id_name
         , syn_pattern_match_vars = []}, chn)
  | otherwise
      = ({ syn_annot_expr = Var bv
         , syn_texpr      = TVar [] bv.var_ident.id_name
         , syn_pattern_match_vars = []}, chn)
  where
  varIsTask :: BoundVar InhExpression -> Bool
  varIsTask bv inh
    = case 'DM'.get bv.var_ident.id_name inh.inh_tyenv of
        Nothing -> False
        Just t  -> typeIsTask t

mkBlueprint expr=:(FreeVar fv) _ chn
  = ({ syn_annot_expr = expr
     , syn_texpr      = TVar [] fv.fv_ident.id_name
     , syn_pattern_match_vars = []}, chn)
mkBlueprint expr=:(BasicExpr bv) _ chn
  = ({ syn_annot_expr = expr
     , syn_texpr      = TLit (ppCompact (ppBasicValue bv))
     , syn_pattern_match_vars = []}, chn)
mkBlueprint expr=:(Selection st selExpr sels) inh chn
  # (syn, chn)      = mkBlueprint selExpr inh chn
  # (selExprs, chn) = mapSt (mkSelExprs) sels chn
  = ({ syn_annot_expr = Selection st selExpr sels
     , syn_texpr      = TSel syn.syn_texpr selExprs
     , syn_pattern_match_vars = []}, chn)
  where
  mkSelExprs (RecordSelection gds _) chn
    # (d, menv) = ppDefinedSymbol gds.glob_object chn.chn_module_env
    = (TLit (ppCompact d), {chn & chn_module_env = menv})
  mkSelExprs (ArraySelection gds _ e) chn // TODO use e
    # (d, menv) = ppDefinedSymbol gds.glob_object chn.chn_module_env
    = (TLit (ppCompact d), {chn & chn_module_env = menv})
  mkSelExprs (DictionarySelection bv sels _ e) chn
    = (TLit "TODO mkSelExprs DictionarySelection ", chn)
mkBlueprint expr=:(Update _ _ _) _ chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TLit "(mkBlueprint Update fallthrough)"
                          , syn_pattern_match_vars = []}, chn)
mkBlueprint expr=:(RecordUpdate _ _ _) _ chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TLit "(mkBlueprint RecordUpdate fallthrough)"
                          , syn_pattern_match_vars = []}, chn)
mkBlueprint expr=:(TupleSelect _ _ _) _ chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TLit "(mkBlueprint TupleSelect fallthrough)"
                          , syn_pattern_match_vars = []}, chn)
mkBlueprint expr=:(Conditional _) _ chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TLit "(mkBlueprint Conditional fallthrough)"
                          , syn_pattern_match_vars = []}, chn)
mkBlueprint expr=:(AnyCodeExpr _ _ _) _ chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TLit "(mkBlueprint AnyCodeExpr fallthrough)"
                          , syn_pattern_match_vars = []}, chn)
mkBlueprint expr=:(ABCCodeExpr _ _) _ chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TLit "(mkBlueprint ABCCodeExpr fallthrough)"
                          , syn_pattern_match_vars = []}, chn)
mkBlueprint expr=:(MatchExpr _ _) _ chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TLit "(mkBlueprint MatchExpr fallthrough)"
                          , syn_pattern_match_vars = []}, chn)
mkBlueprint expr=:(IsConstructor _ _ _ _ _ _) _ chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TLit "(mkBlueprint IsConstructor fallthrough)"
                          , syn_pattern_match_vars = []}, chn)
mkBlueprint expr=:(DictionariesFunction _ _ _) _ chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TLit "(mkBlueprint DictionariesFunction fallthrough)"
                          , syn_pattern_match_vars = []}, chn)
mkBlueprint expr=:(Constant _ _ _) _ chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TLit "(mkBlueprint Constant fallthrough)"
                          , syn_pattern_match_vars = []}, chn)
mkBlueprint expr=:(ClassVariable _) _ chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TLit "(mkBlueprint ClassVariable fallthrough)"
                          , syn_pattern_match_vars = []}, chn)
mkBlueprint expr=:(DynamicExpr _) _ chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TLit "(mkBlueprint DynamicExpr fallthrough)"
                          , syn_pattern_match_vars = []}, chn)
mkBlueprint expr=:(TypeCodeExpression _) _ chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TLit "(mkBlueprint TypeCodeExpression fallthrough)"
                          , syn_pattern_match_vars = []}, chn)
mkBlueprint expr=:(TypeSignature _ _) _ chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TLit "(mkBlueprint TypeSignature fallthrough)"
                          , syn_pattern_match_vars = []}, chn)
mkBlueprint expr=:EE _ chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TLit "(mkBlueprint EE fallthrough)"
                          , syn_pattern_match_vars = []}, chn)
mkBlueprint expr=:(NoBind _) _ chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TLit "(mkBlueprint NoBind fallthrough)"
                          , syn_pattern_match_vars = []}, chn)
mkBlueprint expr=:(FailExpr _) _ chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TLit "(mkBlueprint FailExpr fallthrough)"
                          , syn_pattern_match_vars = []}, chn)
mkBlueprint expr _ chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TLit "(mkBlueprint fallthrough)"
                          , syn_pattern_match_vars = []}, chn)

// TODO Relate the match_vars from the body to the vars from the arguments
funToGraph :: FunDef FunDef [(String, ParsedExpr)] !{#{!InstanceTree}} !{#CommonDefs} InhExpression *ChnExpression
           -> *(Maybe ([(TExpr, TExpr)], TExpr, Expression), *ChnExpression)
funToGraph fd=:{fun_ident=fun_ident, fun_body = TransformedBody tb} fd_cpy list_comprehensions instance_tree common_defs inh chn = mkBody
  where
  mkBody
    # (argTys, tyenv) = zipWithSt (\arg t st -> ((arg, t), 'DM'.put arg.fv_ident.id_name t st)) tb.tb_args (funArgTys fd_cpy) 'DM'.newMap
    # (syn, chn)      = mkBlueprint tb.tb_rhs {inh & inh_tyenv = tyenv} chn
    = ( Just (map (\(arg, ty) -> (mkArgPP syn.syn_pattern_match_vars arg, typeToTCleanExpr ty)) argTys, syn.syn_texpr, syn.syn_annot_expr)
      , chn)
  mkArgPP pmvars arg
    = case arg.fv_ident.id_name of
        "_x"
          = case [clexpr \\ (bv, clexpr) <- pmvars | bv.var_info_ptr == arg.fv_info_ptr] of
              []    -> TLit "(shouldn't happen)"
              [x:_] -> x
        idnm
          = TVar [] idnm
funToGraph _ _ _ _ _ _ chn = (Nothing, chn)
