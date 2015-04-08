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
import iTasks.Framework.Tonic.AbsSyn

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
withTwo app []        _ _   chn = ({syn_annot_expr = App app, syn_texpr = TVar [] "TODO withTwo []", syn_pattern_match_vars = []}, chn)
withTwo app [_]       _ _   chn = ({syn_annot_expr = App app, syn_texpr = TVar [] "TODO withTwo [_]", syn_pattern_match_vars = []}, chn)
withTwo app [x1:x2:_] f inh chn = f x1 x2 chn

wrapTaskApp :: Expression InhExpression *ChnExpression -> *(Expression, *ChnExpression)
wrapTaskApp origExpr inh chn
  # (ok, pdss) = pdssAreDefined [PD_tonicWrapApp, PD_tonicWrapAppLam1, PD_tonicWrapAppLam2, PD_tonicWrapAppLam3, PD_ConsSymbol, PD_NilSymbol] chn.chn_predef_symbols
  # chn        = {chn & chn_predef_symbols = pdss}
  | not ok     = (origExpr, chn)
  | otherwise
      # (rem, menv)  = case origExpr of
                         App app
                           = argsRemaining app chn.chn_module_env
                         _ = (0, chn.chn_module_env)
      # icl          = menv.me_icl_module
      # nm           = icl.icl_name.id_name
      # (ids, pdss)  = toStatic (map mkInt inh.inh_ids) chn.chn_predef_symbols
      # (expr, heaps, pdss) = appPredefinedSymbolWithEI (findWrap rem)
                         [ mkStr nm
                         , mkStr inh.inh_curr_task_name
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

wrapParallelN :: Expression InhExpression *ChnExpression -> *(Expression, *ChnExpression)
wrapParallelN origExpr=:(App app=:{app_args=[xs:_]}) inh chn
  # (ok, pdss) = pdssAreDefined [PD_tonicWrapParallel, PD_ConsSymbol, PD_NilSymbol] chn.chn_predef_symbols
  # chn        = {chn & chn_predef_symbols = pdss}
  | not ok     = (origExpr, chn)
  | otherwise
      # menv         = chn.chn_module_env
      # icl          = menv.me_icl_module
      # nm           = icl.icl_name.id_name
      # (ids, pdss)  = toStatic (map mkInt inh.inh_ids) chn.chn_predef_symbols
      # (expr, heaps, pdss) = appPredefinedSymbolWithEI PD_tonicWrapParallel
                         [ mkStr nm
                         , mkStr inh.inh_curr_task_name
                         , ids
                         , App {app & app_args = []}
                         , xs
                         ] SK_Function chn.chn_heaps pdss
      = ( App expr
        , {chn & chn_predef_symbols = pdss
               , chn_module_env = {menv & me_icl_module = icl}
               , chn_heaps      = heaps})
wrapParallelN origExpr inh chn = (origExpr, chn)

letTypes :: ExprInfoPtr *ChnExpression -> *([Type], *ChnExpression)
letTypes exprPtr chn
  # heaps = chn.chn_heaps
  # (ei, expr_heap) = readPtr exprPtr heaps.hp_expression_heap
  # chn = {chn & chn_heaps = {heaps & hp_expression_heap = expr_heap}}
  = case ei of
      EI_LetType atys -> (map (\x -> x.at_type) atys, chn)
      _               -> ([], chn)

varIsTask :: BoundVar InhExpression -> Bool
varIsTask bv inh
  = case 'DM'.get bv.var_ident.id_name inh.inh_tyenv of
      Nothing -> False
      Just t  -> typeIsTask t

varIsListOfTask :: BoundVar InhExpression -> Bool
varIsListOfTask bv inh
  = case 'DM'.get bv.var_ident.id_name inh.inh_tyenv of
      Nothing -> False
      Just t  -> typeIsListOfTask t

exprToTCleanExpr :: Expression *ModuleEnv -> *(TCleanExpr, *ModuleEnv)
exprToTCleanExpr (App app) menv
  # ((_, args), menv) = dropAppContexts app menv
  = case args of
      [] = (PPCleanExpr app.app_symb.symb_ident.id_name, menv)
      xs
        # (tces, menv) = mapSt exprToTCleanExpr args menv
        = (AppCleanExpr TNonAssoc app.app_symb.symb_ident.id_name tces, menv)
exprToTCleanExpr expr menv
  # (doc, menv) = ppExpression expr menv
  = (PPCleanExpr (ppCompact doc), menv)

mkBlueprint :: Expression InhExpression *ChnExpression -> *(SynExpression, *ChnExpression)
mkBlueprint (App app) inh chn
  # (idIsTask, menv) = symbIdentIsTask app.app_symb chn.chn_module_env
  | idIsTask
    # ((ctxs, args), menv) = dropAppContexts app menv
    # chn                  = { chn & chn_module_env = menv }
    = case appFunName app of
        ">>="      -> mkBind      app ctxs args inh chn
        ">>|"      -> mkBind      app ctxs args inh chn
        "@:"       -> mkAssign    app ctxs args inh chn
        "@"        -> mkTransform app ctxs args inh chn
        ">>*"      -> mkStep      app ctxs args inh chn
        "anyTask"  -> mkParSumN   app ctxs args inh chn
        "-||-"     -> mkParSum2   app ctxs args inh chn
        "||-"      -> mkParSumR   app ctxs args inh chn
        "-||"      -> mkParSumL   app ctxs args inh chn
        "allTasks" -> mkParProdN  app ctxs args inh chn
        "-&&-"     -> mkParProd2  app ctxs args inh chn
        "get"      -> mkGetShare  app ctxs args inh chn
        "set"      -> mkSetShare  app ctxs args inh chn
        "upd"      -> mkUpdShare  app ctxs args inh chn
        _          -> mkTaskApp   app ctxs args inh chn
  | otherwise
      # (apptcle, menv) = exprToTCleanExpr (App app) menv
      # chn             = {chn & chn_module_env = menv}
      = ({ syn_annot_expr = App app
         , syn_texpr      = TCleanExpr [] apptcle
         , syn_pattern_match_vars = []}, chn)
  where
  mkBind app ctxs args inh chn
    = withTwo app args f inh chn
    where
    f lhsExpr rhsExpr=:(App rhsApp) chn
      # (synl, chnl)      = mkBlueprint lhsExpr (addInhId inh 0) chn
      # (lbl, synr, chnr) = mkEdge rhsApp 1 inh chnl
      = ({ syn_annot_expr = App { app & app_args = ctxs ++ [synl.syn_annot_expr, synr.syn_annot_expr] }
         , syn_texpr      = TBind synl.syn_texpr lbl synr.syn_texpr
         , syn_pattern_match_vars = synl.syn_pattern_match_vars ++ synr.syn_pattern_match_vars}, chnr)
    f lhsExpr rhsExpr chn
      # (synl, chn)  = mkBlueprint lhsExpr (addInhId inh 0) chn
      # (synr, chn)  = mkBlueprint rhsExpr (addInhId inh 1) chn
      = ({ syn_annot_expr = App { app & app_args = ctxs ++ [synl.syn_annot_expr, synr.syn_annot_expr] }
         , syn_texpr      = TBind synl.syn_texpr Nothing synr.syn_texpr
         , syn_pattern_match_vars = []}, chn)

  mkAssign app ctxs args inh chn
    = withTwo app args f inh chn
    where
    f u=:(App a) t chn
      | a.app_symb.symb_ident ==
        predefined_idents.[GetTupleConsIndex 2]
          # (usr, str) = tupleExprToTuple u
          = case usr of
              App a
                # (syn, chn) = mkBlueprint t (addInhId inh 0) chn
                # menv       = chn.chn_module_env
                # (tu, menv) = case (a.app_symb.symb_ident.id_name, a.app_args) of
                                 ("AnyUser", _)
                                   = (TUAnyUser, menv)
                                 ("UserWithId", [uid:_])
                                   # (ed, menv) = ppExpression uid menv
                                   = (TUUserWithIdent (stringContents (ppCompact ed)), menv)
                                 ("UserWithRole", [r:_])
                                   # (rd, menv) = ppExpression r menv
                                   = (TUUserWithRole (stringContents (ppCompact rd)), menv)
                                 ("SystemUser", _)
                                   = (TUSystemUser, menv)
                                 ("AnonymousUser", _)
                                   = (TUAnonymousUser, menv)
                                 ("AuthenticatedUser", [uid:rs:_])
                                   # (d, menv)    = ppExpression uid menv
                                   # (rsds, menv) = mapSt ppExpression (listExprToList rs) menv
                                   = (TUAuthenticatedUser (stringContents (ppCompact d)) (map (stringContents o ppCompact) rsds), menv)
                                 (usr, _)
                                   = (TUVariableUser usr, menv)
                # chn        = {chn & chn_module_env = menv}
                = ({ syn_annot_expr = App {app & app_args = ctxs ++ [u, syn.syn_annot_expr]}
                   , syn_texpr      = TAssign tu (fromStatic str) syn.syn_texpr
                   , syn_pattern_match_vars = syn.syn_pattern_match_vars}, chn)
              expr = mkAssDef u usr (fromStatic str) t chn
      | otherwise = mkAssDef u u "" t chn
    f u t chn = mkAssDef u u "" t chn
    mkAssDef lhs u str t chn
      # (syn, chn)  = mkBlueprint t (addInhId inh 0) chn
      # (ppu, menv) = ppExpression u chn.chn_module_env
      # chn         = {chn & chn_module_env = menv}
      # (app`, chn) = wrapTaskApp (App {app & app_args = ctxs ++ [lhs, syn.syn_annot_expr]}) inh chn
      = ({ syn_annot_expr = app`
         , syn_texpr      = TAssign (TUVariableUser (ppCompact ppu)) str syn.syn_texpr
         , syn_pattern_match_vars = syn.syn_pattern_match_vars}, chn)

  // TODO : Test
  mkStep app ctxs args inh chn
    = withTwo app args f inh chn
    where
    f l r chn
      # (synl, chn) = mkBlueprint l (addInhId inh 0) chn
      = case r of
          (arg=:(App _))
            | exprIsListConstr arg
                # exprs              = fromStatic arg
                // TODO FIXME : RHS of step is not updated properly
                # (scs, aes, chn, _) = let f e=:(App a=:{app_args=[App btnOrCont:asTl]}) (scs, aes, chn, n)
                                             | appFunName a == "OnAction"
                                             # [App contApp:_]     = asTl // TODO Bah
                                             # (sf, contApp`, chn) = mkStepCont contApp n chn
                                             # action              = extractAction btnOrCont
                                             = ([StepOnAction (stringContents action) sf:scs], [App {a & app_args = [App btnOrCont, App contApp`]} : aes], chn, n + 1)
                                             | appFunName a == "OnValue"
                                             # (sf, btnOrCont`, chn)  = mkStepCont btnOrCont n chn
                                             = ([StepOnValue sf:scs], [App {a & app_args = [App btnOrCont`]} : aes], chn, n + 1)
                                             | appFunName a == "OnException"
                                             # (lbl, syn, chn) = mkEdge btnOrCont n inh chn
                                             = ([StepOnException lbl syn.syn_texpr:scs], [App {a & app_args = [syn.syn_annot_expr]} : aes], chn, n + 1)
                                             | appFunName a == "OnAllExceptions"
                                             # (lbl, syn, chn) = mkEdge btnOrCont n inh chn
                                             = ([StepOnException lbl syn.syn_texpr:scs], [App {a & app_args = [syn.syn_annot_expr]} : aes], chn, n + 1)
                                           f _ (scs, aes, chn, n) = (scs, aes, chn, n + 1)
                                       in  foldr f ([], [], chn, 1) exprs
                # (stArgs, pdss) = toStatic aes chn.chn_predef_symbols
                = ({syn_annot_expr = App {app & app_args = ctxs ++ [synl.syn_annot_expr, stArgs]}
                  , syn_texpr      = TStep synl.syn_texpr (map T scs)
                  , syn_pattern_match_vars = synl.syn_pattern_match_vars}
                  , {chn & chn_predef_symbols = pdss})
            | otherwise = doPP synl chn arg
          (arg=:(Var _)) = doPP synl chn arg
      where
      doPP synl chn arg
        # (doc, menv) = ppExpression arg chn.chn_module_env
        # ppStr       = ppCompact doc
        # chn         = {chn & chn_module_env = menv}
        = ({syn_annot_expr = App {app & app_args = ctxs ++ [synl.syn_annot_expr, arg]}
          , syn_texpr      = TStep synl.syn_texpr [PP ppStr]
          , syn_pattern_match_vars = []}, chn)
    extractAction app=:{app_args=[BasicExpr (BVS str):_]}
      | app.app_symb.symb_ident.id_name == "Action" = str
    extractAction _ = "(no action)"
    mkStepCont contApp n chn =
      case (appFunName contApp, contApp.app_args) of
      // TODO FIXME Get rid of copy/paste job
        ("ifValue", [e1=:((App fApp) @ fAppArgs):(App tApp):_])
          # ((_, fAppArgs), menv)     = dropAppContexts fApp chn.chn_module_env
          # (ppFAppArgs, menv)        = mapSt ppExpression fAppArgs menv
          # ((fArgFunArgs, _), menv)  = reifyArgsAndDef fApp.app_symb menv
          # remFArgs                  = drop (length fAppArgs) fArgFunArgs
          # ((ppHdRemFArgs, ppTlRemFArgs), menv) = case remFArgs of
                                                     [x:xs]
                                                       # (ppHdRemFArgs, menv) = ppFreeVar x menv
                                                       # (ppTlRemFArgs, menv) = mapSt ppFreeVar xs menv
                                                       = ((ppHdRemFArgs, ppTlRemFArgs), menv)
                                                     _ = (('PPrint'.text "FIXME", ['PPrint'.text "FIXME"]), menv)
          # (lbl, syn, chn)           = mkEdge tApp n inh {chn & chn_module_env = menv}
          = (IfValue (PPCleanExpr (ppCompact ppHdRemFArgs)) fApp.app_symb.symb_ident.id_name
              (map ppCompact (ppFAppArgs ++ [ppHdRemFArgs:ppTlRemFArgs])) lbl syn.syn_texpr
            , {contApp & app_args = [e1, syn.syn_annot_expr]}, chn)
        ("ifValue", [(App fApp):(App tApp):_])
          # ((_, fAppArgs), menv)     = dropAppContexts fApp chn.chn_module_env
          # (ppFAppArgs, menv)        = mapSt ppExpression fAppArgs menv
          # ((fArgFunArgs, _), menv)  = reifyArgsAndDef fApp.app_symb menv
          # remFArgs                  = drop (length fAppArgs) fArgFunArgs
          # ((ppHdRemFArgs, ppTlRemFArgs), menv) = case remFArgs of
                                                     [x:xs]
                                                       # (ppHdRemFArgs, menv) = ppFreeVar x menv
                                                       # (ppTlRemFArgs, menv) = mapSt ppFreeVar xs menv
                                                       = ((ppHdRemFArgs, ppTlRemFArgs), menv)
                                                     _ = (('PPrint'.text "FIXME", ['PPrint'.text "FIXME"]), menv)
          # (lbl, syn, chn)           = mkEdge tApp n inh {chn & chn_module_env = menv}
          = (IfValue (PPCleanExpr (ppCompact ppHdRemFArgs)) fApp.app_symb.symb_ident.id_name
              (map ppCompact (ppFAppArgs ++ [ppHdRemFArgs:ppTlRemFArgs])) lbl syn.syn_texpr
            , {contApp & app_args = [App fApp, syn.syn_annot_expr]}, chn)
        ("hasValue", [(App tApp):_])
          # (lbl, syn, chn) = mkEdge tApp n inh chn
          = (HasValue lbl syn.syn_texpr, {contApp & app_args = [syn.syn_annot_expr]}, chn)
        ("ifStable", [(App tApp):_])
          # (lbl, syn, chn) = mkEdge tApp n inh chn
          = (IfStable lbl syn.syn_texpr, {contApp & app_args = [syn.syn_annot_expr]}, chn)
        ("ifUnstable", [(App tApp):_])
          # (lbl, syn, chn) = mkEdge tApp n inh chn
          = (IfUnstable lbl syn.syn_texpr, {contApp & app_args = [syn.syn_annot_expr]}, chn)
        ("ifCond", [cond:(App tApp):_])
          # (lbl, syn, chn)     = mkEdge tApp n inh chn
          # (d, menv)           = ppExpression cond chn.chn_module_env
          = (IfCond (ppCompact d) lbl syn.syn_texpr, {contApp & app_args = [cond, syn.syn_annot_expr]}, { chn & chn_module_env = menv })
        ("always", [x:_])
          # (syn, chn) = mkBlueprint x (addInhId inh n) chn
          = (Always syn.syn_texpr, {contApp & app_args = [syn.syn_annot_expr]}, chn)
        (fn, _)
          = (CustomFilter fn, contApp, chn)

  mkTaskApp app ctxs args inh chn
    # (dclnm, menv) = case reifyDclModule app.app_symb chn.chn_module_env of
                        (Just dcl, menv) = (dcl.dcl_name.id_name, menv)
                        (_       , menv)
                          # (iclmod, menv) = menv!me_icl_module
                          = (iclmod.icl_name.id_name, menv)
    # (ps, menv)    = mapSt exprToTCleanExpr args menv
    # chn           = {chn & chn_module_env = menv}
    # (app`, chn)   = wrapTaskApp (App app) inh chn
    = ({ syn_annot_expr = app`
       , syn_texpr      = TTaskApp inh.inh_ids dclnm (appFunName app) (map (TCleanExpr []) ps)
       , syn_pattern_match_vars = []}, chn)

  mkTransform app ctxs args inh chn
    = withTwo app args f inh chn
    where
    f l r=:(App {app_symb, app_args}) chn
      # (syn, chn)           = mkBlueprint l (addInhId inh 0) chn
      # (ppl, menv)          = mapSt ppExpression app_args chn.chn_module_env
      # ((funArgs, _), menv) = reifyArgsAndDef app_symb menv
      # patId                = case drop (length app_args) [freeVarName x \\ x <- funArgs | x.fv_def_level == -1] of
                                 []    -> []
                                 [x:_] -> [x]
      # chn                  = {chn & chn_module_env = menv}
      = ({ syn_annot_expr = App {app & app_args = ctxs ++ [syn.syn_annot_expr, r]}
         , syn_texpr      = TTransform syn.syn_texpr app_symb.symb_ident.id_name (map ppCompact ppl ++ patId)
         , syn_pattern_match_vars = syn.syn_pattern_match_vars}, chn)

  mkParSumN = mkParN ParSumN

  mkParSum2 = mkParBin (\l r -> ParSumN (T [l, r]))

  mkParSumR = mkParBin ParSumR

  mkParSumL = mkParBin ParSumL

  mkParProdN = mkParN ParProd

  mkParProd2 = mkParBin (\l r -> ParProd (T [l, r]))

  mkParBin mkPar app ctxs args inh chn
    = withTwo app args f inh chn
    where
    f l r chn
      # (synl, chnl) = mkBlueprint l (addInhId inh 0) chn
      # (synr, chnr) = mkBlueprint r (addInhId inh 1) chnl
      = ( { syn_annot_expr = App {app & app_args = ctxs ++ [synl.syn_annot_expr, synr.syn_annot_expr]}
          , syn_texpr      = TParallel inh.inh_ids (mkPar synl.syn_texpr synr.syn_texpr)
          , syn_pattern_match_vars = synl.syn_pattern_match_vars ++ synr.syn_pattern_match_vars }
        , chnr)

  mkParN mkPar app ctxs args inh chn
    = case args of
        [arg=:(App _)]
          | exprIsListConstr arg
            # exprs        = fromStatic arg
            # (ss, _, chn) = let f e (ss, n, chn)
                                  # (syn, chn) = mkBlueprint e (addInhId inh n) chn
                                  = ([syn:ss], n + 1, chn)
                             in  foldr f ([], 0, chn) exprs
            # (listArg, pdss) = toStatic (map (\s -> s.syn_annot_expr) ss) chn.chn_predef_symbols
            # (app, chn)  = wrapParallelN (App {app & app_args = [listArg]}) inh {chn & chn_predef_symbols = pdss} // TODO  Should this stay?
            = ( { syn_annot_expr = app
                , syn_texpr      = TParallel inh.inh_ids (mkPar (T (map (\s -> s.syn_texpr) ss)))
                , syn_pattern_match_vars = foldr (\syn acc -> syn.syn_pattern_match_vars ++ acc) [] ss}
              , chn)
          | otherwise // Is regular function application
              # (doc, menv) = ppExpression arg chn.chn_module_env
              # ppStr       = ppCompact doc
              # chn         = {chn & chn_module_env = menv}
              # (app, chn)  = wrapParallelN (App app) inh chn
              = ({ syn_annot_expr = app
                 , syn_texpr      = TParallel inh.inh_ids (mkPar (PP ppStr))
                 , syn_pattern_match_vars = []}, chn)
        [arg=:(Var _)]
          # (doc, menv) = ppExpression arg chn.chn_module_env
          # ppStr       = ppCompact doc
          # chn         = {chn & chn_module_env = menv}
          # (app, chn)  = wrapParallelN (App app) inh chn
          = ({ syn_annot_expr = app
             , syn_texpr      = TParallel inh.inh_ids (mkPar (PP ppStr))
             , syn_pattern_match_vars = []}, chn)
        _ = abort "mkParN args fallthrough; shouldn't happen"

  // TODO Look at this some more
  mkGetShare app ctxs args=:[App {app_symb, app_args}:_] inh chn
    = mkShareApp app Get app_symb app_args chn
  mkGetShare app ctxs args=:[Var v] inh chn
    = mkShareVar app Get v chn

  mkSetShare app ctxs args=:[a1=:(App _):App {app_symb, app_args}:_] inh chn
    # (ppe1, menv) = ppExpression a1 chn.chn_module_env
    = mkShareApp app (Set (ppCompact ppe1)) app_symb app_args {chn & chn_module_env = menv}
  mkSetShare app ctxs args=:[a1=:(App _): Var v:_] inh chn
    # (ppe1, menv) = ppExpression a1 chn.chn_module_env
    = mkShareVar app (Set (ppCompact ppe1)) v {chn & chn_module_env = menv}
  mkSetShare app ctxs args=:[Var v:_] inh chn
    = mkShareVar app (Set "TODO") v chn

  mkUpdShare app ctxs args=:[a1=:(App _):App {app_symb, app_args}:_] inh chn
    # (ppe1, menv) = ppExpression a1 chn.chn_module_env
    = mkShareApp app (Upd (ppCompact ppe1)) app_symb app_args {chn & chn_module_env = menv}
  mkUpdShare app ctxs args=:[a1=:(App _) : Var v : _] inh chn
    # (ppe1, menv) = ppExpression a1 chn.chn_module_env
    = mkShareVar app (Upd (ppCompact ppe1)) v {chn & chn_module_env = menv}

  mkShareApp app tsh app_symb app_args chn
    # (ads, menv) = mapSt ppExpression app_args chn.chn_module_env
    # (var, vars) =
        if (app_symb.symb_ident.id_name == "sharedStore")
          (case ads of
             []       -> ("mkShare: should not happen", [])
             [ad:ads] -> (ppCompact ad, ads))
          (app_symb.symb_ident.id_name, ads)
    = ({ syn_annot_expr = App app
       , syn_texpr      = TShare tsh var (map ppCompact vars)
       , syn_pattern_match_vars = []}
      , {chn & chn_module_env = menv})

  mkShareVar app tsh var chn
    # (bvd, menv) = ppBoundVar var chn.chn_module_env
    = ({ syn_annot_expr = App app
       , syn_texpr      = TShare tsh (ppCompact bvd) []
       , syn_pattern_match_vars = []}
      , {chn & chn_module_env = menv})

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
      # (syne, chn)   = mkBlueprint (getFunRhs fd) (addInhId inh 0) chn
      # menv          = updateWithAnnot app.app_symb syne.syn_annot_expr chn.chn_module_env
      # chn           = { chn & chn_module_env = menv}
      = ({ syn_annot_expr = e @ es
         , syn_texpr      = TVar [] "TODO @"
         , syn_pattern_match_vars = syne.syn_pattern_match_vars}, chn)
  | otherwise    =  abort "atC: otherwise case" // TODO : pretty print function application
  where
    zwf eVar eVal menv
      # (fvl, menv) = ppFreeVar eVar menv
      # (fvr, menv) = ppExpression eVal menv
      = ((ppCompact fvl, ppCompact fvr), menv)
mkBlueprint (e @ es) _ chn = ({ syn_annot_expr = e @ es
                              , syn_texpr      = TVar [] "TODO @"
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
    # (tys, chn)    = letTypes lt.let_info_ptr chn
    # (binds, menv) = flattenBinds lt chn.chn_module_env
    # tyenv         = zipSt (\(PPCleanExpr v, _) t tyenv -> 'DM'.put v t tyenv) binds tys inh.inh_tyenv // TODO This probably won't work for arbitrary patterns, so we actually need to be a bit smarter here and extract all variables from the patterns, instead of just PP'ing the pattern and using that as index
    // TODO : Represent the bindings in any way possible, not just PP
    # (syn, chn)    = mkBlueprint lt.let_expr (addInhId {inh & inh_tyenv = tyenv} 0) {chn & chn_module_env = menv}
    = ({ syn_annot_expr = Let {lt & let_expr = syn.syn_annot_expr}
       , syn_texpr      = TLet binds syn.syn_texpr
       , syn_pattern_match_vars = syn.syn_pattern_match_vars}, chn)
    where
    flattenBinds lt menv
      = foldrSt f (getLetBinds lt) ([], menv)
      where
      f bnd (xs, menv)
        # (rhs, menv) = exprToTCleanExpr bnd.lb_src menv
        = ([(PPCleanExpr bnd.lb_dst.fv_ident.id_name, TCleanExpr [] rhs):xs], menv)
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
        # (syn, chn)   = mkAlts` 0 ap.ap_expr chn
        # (fvds, menv) = mapSt (exprToTCleanExpr o FreeVar) ap.ap_vars chn.chn_module_env
        # clexpr       = case fvds of
                           []   -> PPCleanExpr ""
                           args -> AppCleanExpr TNonAssoc ap.ap_symbol.glob_object.ds_ident.id_name args // TODO Associativity
        = ({ syn_annot_expr = Case {cs & case_guards = AlgebraicPatterns gi [{ap & ap_expr = syn.syn_annot_expr}]}
           , syn_texpr      = syn.syn_texpr
           , syn_pattern_match_vars = [(bv, clexpr) : syn.syn_pattern_match_vars]}, {chn & chn_module_env = menv})
      _
        # ((guards, syns), chn) = mkAlts cs.case_guards chn
        # ((def, syns), chn)    = case cs.case_default of
                                    Yes def
                                      # (syn, chn) = mkAlts` (numGuards cs.case_guards) def chn
                                      = case syns of
                                          [(PPCleanExpr "True", _)]
                                            = ((Yes syn.syn_annot_expr, [(PPCleanExpr "False", syn):syns]), chn)
                                          _ = ((Yes syn.syn_annot_expr, [(PPCleanExpr "_", syn):syns]), chn)
                                    _ = ((No, syns), chn)
        = ({ syn_annot_expr = Case {cs & case_default = def, case_guards = guards}
           , syn_texpr      = TCaseOrIf (TCleanExpr [] (PPCleanExpr (ppCompact ed))) (map (\(d, s) -> (d, s.syn_texpr)) syns)
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
        # menv        = chn.chn_module_env
        # (apd, menv) = mkAp ap.ap_symbol ap.ap_vars menv
        # chn         = {chn & chn_module_env = menv}
        # (syn, chn)  = mkAlts` n ap.ap_expr chn
        # ap          = {ap & ap_expr = syn.syn_annot_expr}
        = (([ap:aps], [(apd, syn):syns], n + 1), chn)
        where
        mkAp sym []   menv = (PPCleanExpr (ppCompact ('PPrint'.text sym.glob_object.ds_ident.id_name)), menv)
        mkAp sym vars menv
          # (fvds, menv) = mapSt (exprToTCleanExpr o FreeVar) vars menv
          // TODO TNonAssoc?
          = (AppCleanExpr TNonAssoc (ppCompact ('PPrint'.text sym.glob_object.ds_ident.id_name)) fvds, menv)
  mkAlts c=:(BasicPatterns bt bps) chn
    # ((bps, syns, _), chn) = foldr f (([], [], 0), chn) bps
    = ((BasicPatterns bt bps, syns), chn)
    where
      f bp ((bps, syns, n), chn)
        # (syn, chn)  = mkAlts` n bp.bp_expr chn
        # bp          = {bp & bp_expr = syn.syn_annot_expr}
        = (([bp:bps], [(PPCleanExpr (ppCompact (ppBasicValue bp.bp_value)), syn):syns], n + 1), chn)
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
mkBlueprint expr=:(BasicExpr bv) _ chn
  = ({ syn_annot_expr = expr
     , syn_texpr      = TCleanExpr [] (PPCleanExpr (ppCompact (ppBasicValue bv)))
     , syn_pattern_match_vars = []}, chn)
mkBlueprint expr _ chn = ({ syn_annot_expr = expr
                          , syn_texpr      = TCleanExpr [] (PPCleanExpr "(mkBlueprint fallthrough)")
                          , syn_pattern_match_vars = []}, chn)

mkEdge :: App Int InhExpression *ChnExpression -> *(Maybe TCleanExpr, SynExpression, *ChnExpression)
mkEdge app=:{app_symb, app_args} n inh chn
  # (siIsTask, menv) = symbIdentIsTask app_symb chn.chn_module_env
  | identIsLambda app_symb.symb_ident
    # ((args, tFd), menv) = reifyArgsAndDef app_symb menv
    # patid               = last [freeVarName x \\ x <- args | x.fv_def_level == -1]
    # (syne, chn)         = mkBlueprint (getFunRhs tFd) (addInhId inh n) { chn & chn_module_env = menv }
    # menv                = updateWithAnnot app_symb syne.syn_annot_expr chn.chn_module_env
    = (Just (PPCleanExpr patid), {syne & syn_annot_expr = App app}, {chn & chn_module_env = menv})
  | siIsTask
    # ((args, tFd), menv) = reifyArgsAndDef app_symb menv
    # (lbl, menv) = case drop (length app_args) args of
                      [] = (Nothing, menv)
                      [x:_]
                        # (d, menv) = ppFreeVar x menv
                        = (Just (PPCleanExpr (ppCompact d)), menv)
    # (syn, chn)  = mkBlueprint (App app) (addInhId inh n) {chn & chn_module_env = menv}
    = (lbl, syn, chn)
  | otherwise
    # (d, menv) = ppApp app menv
    = (Nothing
      , { syn_annot_expr = App app
        , syn_texpr      = TVar [] (ppCompact d)
        , syn_pattern_match_vars = []}
      , {chn & chn_module_env = menv})

// TODO Relate the match_vars from the body to the vars from the arguments
funToGraph :: FunDef FunDef [(String, ParsedExpr)] *ModuleEnv *Heaps *PredefinedSymbols
           -> *(Maybe ([(TCleanExpr, TCleanExpr)], TExpr, Expression), *ModuleEnv, *Heaps, *PredefinedSymbols)
funToGraph fd=:{fun_ident=fun_ident, fun_body = TransformedBody tb} fd_cpy list_comprehensions menv heaps predef_symbols = mkBody
  where
  mkBody
    # inh             = mkInhExpr fun_ident.id_name list_comprehensions
    # chn             = mkChnExpr predef_symbols menv heaps
    # (argTys, tyenv) = zipWithSt (\arg t st -> ((arg, t), 'DM'.put arg.fv_ident.id_name t st)) tb.tb_args (funArgTys fd_cpy) 'DM'.newMap
    # (syn, chn)      = mkBlueprint tb.tb_rhs {inh & inh_tyenv = tyenv} chn
    = ( Just (map (\(arg, ty) -> (mkArgPP syn.syn_pattern_match_vars arg, typeToTCleanExpr ty)) argTys, syn.syn_texpr, syn.syn_annot_expr)
      , chn.chn_module_env, chn.chn_heaps, chn.chn_predef_symbols)
  mkArgPP pmvars arg
    = case arg.fv_ident.id_name of
        "_x"
          = case [clexpr \\ (bv, clexpr) <- pmvars | bv.var_info_ptr == arg.fv_info_ptr] of
              []    -> PPCleanExpr "(shouldn't happen)"
              [x:_] -> x
        idnm
          = PPCleanExpr idnm
funToGraph _ _ _ menv heaps predef_symbols = (Nothing, menv, heaps, predef_symbols)
