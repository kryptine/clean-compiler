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
To reconstruct list comprehensions:
- Look for a top-level function starting with c; and call it f
- The argument of the lifted function is the list from which you draw elements, but is has a generated name.
  The original name of the generator variable (if any) can be found in this call site of the comprehension function.
- The left-hand side (before the \\) of the comprehension is the first argument to the _Cons case
- ...
- Throw away f
- Replace all occurences of f with the reconstructed expression
- Repeat
*/

//funToListCompr fd
  //| fd.fun_ident.id_name.[0] == "c" =  // Is a list comprehension
  //| otherwise                       = Nothing

//edgeErr :: String (Maybe Int) Expression (Maybe Int) Expression *ChnExpression -> *(SynExpression, *ChnExpression)
//edgeErr errmsg lid lexpr rid rexpr chn
  //# (err1, chn) = nodeErr lid lexpr chn
  //# (err2, chn) = nodeErr rid rexpr chn
  //= abort ("Cannot create " +++ errmsg
           //+++ " between left expression\n\t" +++ err1
           //+++ " and right expression\n\t" +++ err2 +++ "\n")

// TODO: Check whether nodes already exist. How? Perhaps uniquely number all
// expressions first and attach that ID to the graph nodes? Or just by task
// name? Latter probably easiest.

// As for recursion: merge nodes map to tail-recursive call of the corresponding
// function in the let binding in the original Gin paper. Here, we also allow it
// to recurse to the original function.
//
// If arguments to a recursive call are somehow different from the variables
// that have been passed to the original function, an assignment let block must
// be generated.

// TODO: Look up fun_type in FunDef to get an `Optional SymbolType`. Get the
// length of the symbol type's st_context to determine how many contexts there
// are. Drop these from the beginning of the argument list.


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

withTwo :: App [Expression] (Expression Expression *ChnExpression -> *(SynExpression, *ChnExpression)) InhExpression *ChnExpression -> *(SynExpression, *ChnExpression)
withTwo app []        _ _   chn = ({syn_annot_expr = App app, syn_texpr = TVar [] "TODO withTwo []"}, chn)
withTwo app [_]       _ _   chn = ({syn_annot_expr = App app, syn_texpr = TVar [] "TODO withTwo [_]"}, chn)
withTwo app [x1:x2:_] f inh chn = f x1 x2 chn

wrapTaskApp :: Expression InhExpression *ChnExpression -> *(Expression, *ChnExpression)
wrapTaskApp origExpr inh chn
  # (ok, pdss) = pdssAreDefined [PD_tonicWrapApp, PD_tonicWrapAppLam1, PD_tonicWrapAppLam2, PD_tonicWrapAppLam3, PD_ConsSymbol, PD_NilSymbol] chn.chn_predef_symbols
  # chn        = {chn & chn_predef_symbols = pdss}
  | not ok     = (origExpr, chn)
  | otherwise
      #! (rem, menv)  = case origExpr of
                         App app -> argsRemaining app chn.chn_module_env
                         _       -> (0, chn.chn_module_env)
      # icl          = menv.me_icl_module
      # nm           = icl.icl_name.id_name
      # (ids, pdss)  = toStatic (map mkInt inh.inh_ids) chn.chn_predef_symbols
      # (expr, pdss) = appPredefinedSymbol (findWrap rem)
                         [ mkStr nm
                         , mkStr inh.inh_curr_task_name
                         , ids
                         , origExpr
                         ] SK_Function pdss
      = ( App expr
        , {chn & chn_predef_symbols = pdss
               , chn_module_env = {menv & me_icl_module = icl}})
  where
  findWrap :: Int -> Int
  findWrap 0 = PD_tonicWrapApp
  findWrap 1 = PD_tonicWrapAppLam1
  findWrap 2 = PD_tonicWrapAppLam2
  findWrap 3 = PD_tonicWrapAppLam3
  findWrap n = abort ("No tonicWrapLam" +++ toString n)

wrapParallel :: Expression InhExpression *ChnExpression -> *(Expression, *ChnExpression)
wrapParallel origExpr=:(App app) inh chn
  # (ok, pdss) = pdssAreDefined [PD_tonicWrapParallel, PD_ConsSymbol, PD_NilSymbol] chn.chn_predef_symbols
  # chn        = {chn & chn_predef_symbols = pdss}
  | not ok     = (origExpr, chn)
  | otherwise
      # menv         = chn.chn_module_env
      # icl          = menv.me_icl_module
      # nm           = icl.icl_name.id_name
      # (ids, pdss)  = toStatic (map mkInt inh.inh_ids) chn.chn_predef_symbols
      # (expr, pdss) = appPredefinedSymbol PD_tonicWrapParallel
                         [ mkStr nm
                         , mkStr inh.inh_curr_task_name
                         , ids
                         , App {app & app_args = []}
                         , hd app.app_args
                         ] SK_Function pdss
      = ( App expr
        , {chn & chn_predef_symbols = pdss
               , chn_module_env = {menv & me_icl_module = icl}})
wrapParallel origExpr inh chn = (origExpr, chn)

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
        = (AppCleanExpr app.app_symb.symb_ident.id_name tces, menv)
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
        "return"   -> mkReturn    app ctxs args inh chn
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
      = ({syn_annot_expr = App app, syn_texpr = TCleanExpr [] apptcle}, chn)
  where
  mkBind app ctxs args inh chn
    = withTwo app args f inh chn
    where
    f lhsExpr rhsExpr=:(App rhsApp) chn
      # (synl, chnl)      = mkBlueprint lhsExpr (addInhId inh 0) chn
      # (lbl, synr, chnr) = mkEdge rhsApp 1 inh chnl
      = ({ syn_annot_expr = App { app & app_args = ctxs ++ [synl.syn_annot_expr, synr.syn_annot_expr] }
         , syn_texpr = TBind synl.syn_texpr lbl synr.syn_texpr}, chnr)
    f lhsExpr rhsExpr chn
      # (tce, menv) = exprToTCleanExpr rhsExpr chn.chn_module_env
      = ({ syn_annot_expr = App { app & app_args = ctxs ++ [lhsExpr, rhsExpr] }
         , syn_texpr = TCleanExpr inh.inh_ids tce}, {chn & chn_module_env = menv})

  mkReturn app ctxs args=:[e:_] inh chn
    # (syn, chn) = mkBlueprint e (addInhId inh 0) chn
    = ({ syn_annot_expr = App {app & app_args = ctxs ++ [syn.syn_annot_expr]}
       , syn_texpr = TReturn syn.syn_texpr}, chn)

  mkAssign app ctxs args inh chn
    = withTwo app args f inh chn
    where
    f u=:(App a) t chn
      # (syn, chn)  = mkBlueprint t (addInhId inh 0) chn
      # menv        = chn.chn_module_env
      # (tu, menv)  = case (a.app_symb.symb_ident.id_name, a.app_args) of
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
      # chn         = {chn & chn_module_env = menv}
      # (app`, chn) = wrapTaskApp (App {app & app_args = ctxs ++ [u, syn.syn_annot_expr]}) inh chn
      = ({syn_annot_expr = app`, syn_texpr = TAssign tu syn.syn_texpr}, chn)
    f u t chn
      # (syn, chn)  = mkBlueprint t (addInhId inh 0) chn
      # (ppu, menv) = ppExpression u chn.chn_module_env
      # (tu, menv)  = (TUVariableUser (ppCompact ppu), menv)
      # chn         = {chn & chn_module_env = menv}
      # (app`, chn) = wrapTaskApp (App {app & app_args = ctxs ++ [u, syn.syn_annot_expr]}) inh chn
      = ({syn_annot_expr = app`, syn_texpr = TAssign tu syn.syn_texpr}, chn)

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
                  , syn_texpr = TStep synl.syn_texpr (map T scs)}
                  , {chn & chn_predef_symbols = pdss})
            | otherwise = doPP synl chn arg
          (arg=:(Var _)) = doPP synl chn arg
      where
      doPP synl chn arg
        # (doc, menv) = ppExpression arg chn.chn_module_env
        # ppStr       = ppCompact doc
        # chn         = {chn & chn_module_env = menv}
        = ({syn_annot_expr = App {app & app_args = ctxs ++ [synl.syn_annot_expr, arg]}
          , syn_texpr = TStep synl.syn_texpr [PP ppStr]}, chn)
    extractAction app=:{app_args=[BasicExpr (BVS str):_]}
      | app.app_symb.symb_ident.id_name == "Action" = str
    extractAction _ = "(no action)"
    mkStepCont contApp n chn =
      case appFunName contApp of
        "ifValue"
          # [(App fApp):(App tApp):_] = contApp.app_args // TODO Bah
          # ((_, fAppArgs), menv)     = dropAppContexts fApp chn.chn_module_env
          # (ppFAppArgs, menv)        = mapSt ppExpression fAppArgs menv
          # ((fArgFunArgs, _), menv)  = reifyArgsAndDef fApp.app_symb menv
          # remFArgs                  = drop (length fAppArgs) fArgFunArgs
          # (ppHdRemFArgs, menv)      = ppFreeVar (hd remFArgs) menv // TODO Bah
          # (ppTlRemFArgs, menv)      = mapSt ppFreeVar (tl remFArgs) menv // TODO Bah
          # (lbl, syn, chn)           = mkEdge tApp n inh {chn & chn_module_env = menv}
          = (IfValue (PPCleanExpr (ppCompact ppHdRemFArgs)) fApp.app_symb.symb_ident.id_name
              (map ppCompact (ppFAppArgs ++ [ppHdRemFArgs:ppTlRemFArgs])) lbl syn.syn_texpr
            , {contApp & app_args = [App fApp, syn.syn_annot_expr]}, chn)
        "hasValue"
          # [(App tApp):_]  = contApp.app_args // TODO Bah
          # (lbl, syn, chn) = mkEdge tApp n inh chn
          = (HasValue lbl syn.syn_texpr, {contApp & app_args = [syn.syn_annot_expr]}, chn)
        "ifStable"
          # [(App tApp):_]  = contApp.app_args // TODO Bah
          # (lbl, syn, chn) = mkEdge tApp n inh chn
          = (IfStable lbl syn.syn_texpr, {contApp & app_args = [syn.syn_annot_expr]}, chn)
        "ifUnstable"
          # [(App tApp):_]  = contApp.app_args // TODO Bah
          # (lbl, syn, chn) = mkEdge tApp n inh chn
          = (IfUnstable lbl syn.syn_texpr, {contApp & app_args = [syn.syn_annot_expr]}, chn)
        "ifCond"
          # [cond:(App tApp):_] = contApp.app_args // TODO Bah
          # (lbl, syn, chn)     = mkEdge tApp n inh chn
          # (d, menv)           = ppExpression cond chn.chn_module_env
          = (IfCond (ppCompact d) lbl syn.syn_texpr, {contApp & app_args = [cond, syn.syn_annot_expr]}, { chn & chn_module_env = menv })
        "always"
          # (syn, chn) = mkBlueprint (hd contApp.app_args) (addInhId inh n) chn
          = (Always syn.syn_texpr, {contApp & app_args = [syn.syn_annot_expr]}, chn)
        fn
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
    = ({syn_annot_expr = app`, syn_texpr = TTaskApp inh.inh_ids dclnm (appFunName app) (map (TCleanExpr []) ps)}, chn)

  mkTransform app ctxs args inh chn
    = withTwo app args f inh chn
    where
    f l r=:(App {app_symb, app_args}) chn
      # (syn, chn)           = mkBlueprint l (addInhId inh 0) chn
      # (ppl, menv)          = mapSt ppExpression app_args chn.chn_module_env
      # ((funArgs, _), menv) = reifyArgsAndDef app_symb menv
      # ([_:a:as], menv)     = mapSt ppFreeVar funArgs menv // FIXME : Dirty patter matching
      # chn                  = {chn & chn_module_env = menv}
      = ({ syn_annot_expr = App {app & app_args = ctxs ++ [syn.syn_annot_expr, r]}
         , syn_texpr = TTransform syn.syn_texpr (ppCompact a) (map ppCompact (ppl ++ [a:as])) }, chn)

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
          , syn_texpr = TParallel inh.inh_ids (mkPar synl.syn_texpr synr.syn_texpr)}
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
            = ( { syn_annot_expr = App {app & app_args = [listArg]}
                , syn_texpr = TParallel inh.inh_ids (mkPar (T (map (\s -> s.syn_texpr) ss)))}
              , {chn & chn_predef_symbols = pdss})
          | otherwise // Is regular function application
              # (doc, menv) = ppExpression arg chn.chn_module_env
              # ppStr       = ppCompact doc
              # chn         = {chn & chn_module_env = menv}
              # (app, chn)  = wrapParallel (App app) inh chn
              = ({ syn_annot_expr = app
                 , syn_texpr      = TParallel inh.inh_ids (mkPar (PP ppStr))}, chn)
        _ = abort "mkParN args fallthrough; shouldn't happen"

  mkGetShare app ctxs args=:[App {app_symb, app_args}:_] inh chn
    = mkShare app Get app_symb app_args chn

  mkSetShare app ctxs args=:[a1=:(App _):App {app_symb, app_args}:_] inh chn
    # (ppe1, menv) = ppExpression a1 chn.chn_module_env
    = mkShare app (Set (ppCompact ppe1)) app_symb app_args {chn & chn_module_env = menv}

  mkUpdShare app ctxs args=:[a1=:(App _):App {app_symb, app_args}:_] inh chn
    # (ppe1, menv) = ppExpression a1 chn.chn_module_env
    = mkShare app (Upd (ppCompact ppe1)) app_symb app_args {chn & chn_module_env = menv}

  mkShare app tsh app_symb app_args chn
    # (ads, menv) = mapSt ppExpression app_args chn.chn_module_env
    # (var, vars) =
        if (app_symb.symb_ident.id_name == "sharedStore")
          (case ads of
             []       -> ("mkShare: should not happen", [])
             [ad:ads] -> (ppCompact ad, ads))
          (app_symb.symb_ident.id_name, ads)
    = ({syn_annot_expr = App app, syn_texpr = TShare tsh var (map ppCompact vars)}
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
      = ({syn_annot_expr = e @ es, syn_texpr = TVar [] "TODO @"}, chn)
  | otherwise    =  abort "atC: otherwise case" // TODO : pretty print function application
  where
    zwf eVar eVal menv
      # (fvl, menv) = ppFreeVar eVar menv
      # (fvr, menv) = ppExpression eVal menv
      = ((ppCompact fvl, ppCompact fvr), menv)
mkBlueprint (e @ es) _ chn = ({syn_annot_expr = e @ es, syn_texpr = TVar [] "TODO @"}, chn)
mkBlueprint (Let lt) inh chn
  # mexpr = listToMaybe [ bnd.lb_src \\ bnd <- getLetBinds lt
                        | bnd.lb_dst.fv_ident.id_name == "_case_var"]
  = mkLet mexpr lt inh chn
  where
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
       , syn_texpr = TLet binds syn.syn_texpr}, chn)
    where
    flattenBinds lt menv
      = foldrSt f (getLetBinds lt) ([], menv)
      where
      f bnd (xs, menv)
        # (pprhs, menv) = ppExpression bnd.lb_src menv
        = ([(PPCleanExpr bnd.lb_dst.fv_ident.id_name, ppCompact pprhs):xs], menv)
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

  // TODO Refactor this. Also fix default case for If. Also persist numbering?
mkBlueprint (Case cs) inh chn
  # inh                   = {inh & inh_case_expr = Nothing }
  # (ed, menv)            = ppExpression caseExpr chn.chn_module_env
  # ((guards, syns), chn) = mkAlts cs.case_guards {chn & chn_module_env = menv}
  # ((def, syns), chn)    = case cs.case_default of
                              Yes def
                                # (syn, chn) = mkAlts` def chn
                                = ((Yes syn.syn_annot_expr, [(PPCleanExpr "_", syn):syns]), chn)
                              _ = ((No, syns), chn)
  = ({ syn_annot_expr = Case {cs & case_default = def, case_guards = guards}
     , syn_texpr = TCaseOrIf (ppCompact ed) (map (\(d, s) -> (d, s.syn_texpr)) syns)}, chn)
  where
  caseExpr = fromMaybe cs.case_expr inh.inh_case_expr
  mkAlts c=:(AlgebraicPatterns gi aps) chn
    # ((aps, syns), chn) = foldr f (([], []), chn) aps
    = ((AlgebraicPatterns gi aps, syns), chn)
    where
      f ap ((aps, syns), chn)
        # menv        = chn.chn_module_env
        # (apd, menv) = mkAp ap.ap_symbol ap.ap_vars menv
        # chn         = {chn & chn_module_env = menv}
        # (syn, chn)  = mkAlts` ap.ap_expr chn
        # ap          = {ap & ap_expr = syn.syn_annot_expr}
        = (([ap:aps], [(apd, syn):syns]), chn)
        where
        mkAp sym []   menv = (PPCleanExpr (ppCompact ('PPrint'.text sym.glob_object.ds_ident.id_name)), menv)
        mkAp sym vars menv
          # (fvds, menv) = mapSt (exprToTCleanExpr o FreeVar) vars menv
          = (AppCleanExpr (ppCompact ('PPrint'.text sym.glob_object.ds_ident.id_name)) fvds, menv)
  mkAlts c=:(BasicPatterns bt bps) chn
    # ((bps, syns), chn) = foldr f (([], []), chn) bps
    = ((BasicPatterns bt bps, syns), chn)
    where
      f bp ((bps, syns), chn)
        # menv        = chn.chn_module_env
        # (bvd, menv) = ppBasicValue bp.bp_value menv
        # chn         = {chn & chn_module_env = menv}
        # (syn, chn)  = mkAlts` bp.bp_expr chn
        # bp          = {bp & bp_expr = syn.syn_annot_expr}
        = (([bp:bps], [(PPCleanExpr (ppCompact bvd), syn):syns]), chn)
  mkAlts c chn = ((c, []), chn)

  mkAlts` :: Expression ChnExpression -> (SynExpression, ChnExpression)
  mkAlts` expr chn
    # (syn, chn) = mkBlueprint expr (addInhId inh 0) chn
    # menv       = chn.chn_module_env
    # (d, menv)  = ppExpression expr menv
    # chn        = {chn & chn_module_env = menv}
    = (syn, chn)

mkBlueprint (Var bv) inh chn
  | varIsTask bv inh
      # (var`, chn) = wrapTaskApp (Var bv) inh chn
      = ({syn_annot_expr = var`, syn_texpr = TVar inh.inh_ids bv.var_ident.id_name}, chn)
  | otherwise = ({syn_annot_expr = Var bv, syn_texpr = TVar [] bv.var_ident.id_name}, chn)
mkBlueprint expr=:(BasicExpr bv) _ chn
  # (ppbv, menv) = ppBasicValue bv chn.chn_module_env
  # chn          = {chn & chn_module_env = menv}
  = ({syn_annot_expr = expr, syn_texpr = TCleanExpr [] (PPCleanExpr (ppCompact ppbv))}, chn)

//mkBlueprint expr=:(DictionariesFunction _ _ _) _ chn = ({syn_annot_expr = expr, syn_texpr = TCleanExpr [] "1"}, chn)
//mkBlueprint expr=:(Selection _ _ _)            _ chn = ({syn_annot_expr = expr, syn_texpr = TCleanExpr [] "2"}, chn)
//mkBlueprint expr=:(Update _ _ _)               _ chn = ({syn_annot_expr = expr, syn_texpr = TCleanExpr [] "3"}, chn)
//mkBlueprint expr=:(RecordUpdate _ _ _)         _ chn = ({syn_annot_expr = expr, syn_texpr = TCleanExpr [] "4"}, chn)
//mkBlueprint expr=:(TupleSelect _ _ _)          _ chn = ({syn_annot_expr = expr, syn_texpr = TCleanExpr [] "5"}, chn)
//mkBlueprint expr=:(Conditional _)              _ chn = ({syn_annot_expr = expr, syn_texpr = TCleanExpr [] "7"}, chn)
//mkBlueprint expr=:(AnyCodeExpr _ _ _)          _ chn = ({syn_annot_expr = expr, syn_texpr = TCleanExpr [] "8"}, chn)
//mkBlueprint expr=:(ABCCodeExpr _ _)            _ chn = ({syn_annot_expr = expr, syn_texpr = TCleanExpr [] "9"}, chn)
//mkBlueprint expr=:(MatchExpr _ _)              _ chn = ({syn_annot_expr = expr, syn_texpr = TCleanExpr [] "10"}, chn)
//mkBlueprint expr=:(IsConstructor _ _ _ _ _ _)  _ chn = ({syn_annot_expr = expr, syn_texpr = TCleanExpr [] "11"}, chn)
//mkBlueprint expr=:(FreeVar _)                  _ chn = ({syn_annot_expr = expr, syn_texpr = TCleanExpr [] "12"}, chn)
//mkBlueprint expr=:(Constant _ _ _)             _ chn = ({syn_annot_expr = expr, syn_texpr = TCleanExpr [] "13"}, chn)
//mkBlueprint expr=:(ClassVariable _)            _ chn = ({syn_annot_expr = expr, syn_texpr = TCleanExpr [] "14"}, chn)
//mkBlueprint expr=:(DynamicExpr _)              _ chn = ({syn_annot_expr = expr, syn_texpr = TCleanExpr [] "15"}, chn)
//mkBlueprint expr=:(TypeCodeExpression _)       _ chn = ({syn_annot_expr = expr, syn_texpr = TCleanExpr [] "16"}, chn)
//mkBlueprint expr=:(TypeSignature _ _)          _ chn = ({syn_annot_expr = expr, syn_texpr = TCleanExpr [] "17"}, chn)
//mkBlueprint expr=:(EE)                         _ chn = ({syn_annot_expr = expr, syn_texpr = TCleanExpr [] "18"}, chn)
//mkBlueprint expr=:(NoBind _)                   _ chn = ({syn_annot_expr = expr, syn_texpr = TCleanExpr [] "19"}, chn)
//mkBlueprint expr=:(FailExpr _)                 _ chn = ({syn_annot_expr = expr, syn_texpr = TCleanExpr [] "20"}, chn)
mkBlueprint expr _ chn = ({syn_annot_expr = expr, syn_texpr = TCleanExpr [] (PPCleanExpr "(mkBlueprint fallthrough)")}, chn)

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
    = (Nothing, {syn_annot_expr = App app, syn_texpr = TVar [] (ppCompact d)}
      , {chn & chn_module_env = menv})

// TODO: We need to split this up: one part of this should generate the graph
// for the FunDef and the other part should generate the init and stop nodes.
// Yet another part should just get the right-hand side Expression of a FunDef
// so we can just cata it.
funToGraph :: FunDef *ModuleEnv *Heaps *PredefinedSymbols
           -> *(Maybe ([(VariableName, TypeName)], TExpr, Expression), *ModuleEnv, *Heaps, *PredefinedSymbols)
funToGraph fd=:{fun_ident=fun_ident, fun_body = TransformedBody tb} menv heaps predef_symbols = mkBody
  where
  mkBody
    # inh             = mkInhExpr fun_ident.id_name
    # chn             = mkChnExpr predef_symbols menv heaps
    # (argTys, tyenv) = zipWithSt (\arg t st -> ((arg, t), 'DM'.put arg.fv_ident.id_name t st)) tb.tb_args (funArgTys fd) 'DM'.newMap
    # (syn, chn)      = mkBlueprint tb.tb_rhs {inh & inh_tyenv = tyenv} chn
    = ( Just (map (\(arg, ty) -> (arg.fv_ident.id_name, ppCompact (ppType ty))) argTys, syn.syn_texpr, syn.syn_annot_expr) //Just g, syn.syn_annot_expr)
      , chn.chn_module_env, chn.chn_heaps, chn.chn_predef_symbols)
funToGraph _ menv heaps predef_symbols = (Nothing, menv, heaps, predef_symbols)
