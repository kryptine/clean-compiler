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
import Data.Map

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
withTwo app [x1:x2:_] f inh chn = f x1 x2 chn
withTwo app _         _ inh chn = ({syn_annot_expr = App app, syn_texpr = TVar "withTwo TODO"}, chn)

annotExpr :: Expression TExpr InhExpression *ChnExpression -> *(SynExpression, *ChnExpression)
annotExpr origExpr texpr inh chn
  # (tune_symb, predefs)        = (chn.chn_predef_symbols)![PD_tonicWrapApp]
  # chn                         = {chn & chn_predef_symbols = predefs}
  | predefIsUndefined tune_symb = ({syn_annot_expr = origExpr, syn_texpr = texpr}, chn)
  | otherwise                   = annotExpr` origExpr texpr inh chn
  where
  annotExpr` origApp=:(App app) texpr inh chn
    # (rem, menv)   = argsRemaining app chn.chn_module_env
    # (appApp, chn) = mkTuneApp rem origApp {chn & chn_module_env = menv}
    = ({syn_annot_expr = App appApp, syn_texpr = texpr}, chn)
  annotExpr` origVar=:(Var _) texpr inh chn
    # (bvApp, chn) = mkTuneApp 0 origVar chn
    = ({syn_annot_expr = App bvApp, syn_texpr = texpr}, chn)
  mkTuneApp rem origExpr chn
    # menv         = chn.chn_module_env
    # icl          = menv.me_icl_module
    # nm           = icl.icl_name.id_name
    # (ids, pdss)  = toStatic (map mkInt inh.inh_ids) chn.chn_predef_symbols
    # (expr, pdss) = appPredefinedSymbol (findWrap rem)
                       [ mkStr nm
                       , mkStr inh.inh_curr_task_name
                       , ids
                       , origExpr
                       ] SK_Function pdss
    = (expr, {chn & chn_predef_symbols = pdss
                  , chn_module_env = {menv & me_icl_module = icl}})
  findWrap 0 = PD_tonicWrapApp
  findWrap 1 = PD_tonicWrapAppLam1
  findWrap 2 = PD_tonicWrapAppLam2
  findWrap 3 = PD_tonicWrapAppLam3
  findWrap n = abort ("No tonicWrapLam" +++ toString n)

//annotExpr :: App TExpr InhExpression *ChnExpression -> *(SynExpression, *ChnExpression)
//annotExpr origApp texpr inh chn
  //# (tune_symb, predefs) = (chn.chn_predef_symbols)![PD_tonicWrapApp]
  //# chn                  = {chn & chn_predef_symbols = predefs}
  //| predefIsUndefined tune_symb = ({syn_annot_expr = App origApp, syn_texpr = texpr}, chn)
  //| otherwise
    //# (rem, menv) = argsRemaining origApp chn.chn_module_env
    //# (app, chn)  = mkTuneApp rem origApp {chn & chn_module_env = menv}
    //= ({syn_annot_expr = App app, syn_texpr = texpr}, chn)
  //where
  //mkTuneApp rem app chn
    //# menv        = chn.chn_module_env
    //# icl         = menv.me_icl_module
    //# nm          = icl.icl_name.id_name
    //# (ids, pdss) = toStatic (map mkInt inh.inh_ids) chn.chn_predef_symbols
    //# (app, pdss) = appPredefinedSymbol (findWrap rem)
                      //[ mkStr nm
                      //, mkStr inh.inh_curr_task_name
                      //, ids
                      //, App origApp
                      //] SK_Function pdss
    //= (app, {chn & chn_predef_symbols = pdss
                 //, chn_module_env = {menv & me_icl_module = icl}})
  //findWrap 0 = PD_tonicWrapApp
  //findWrap 1 = PD_tonicWrapAppLam1
  //findWrap 2 = PD_tonicWrapAppLam2
  //findWrap 3 = PD_tonicWrapAppLam3
  //findWrap n = abort ("No tonicWrapLam" +++ toString n)

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
  = case get bv.var_ident.id_name inh.inh_tyenv of
      Nothing -> False
      Just t  -> typeIsTask t

varIsListOfTask :: BoundVar InhExpression -> Bool
varIsListOfTask bv inh
  = case get bv.var_ident.id_name inh.inh_tyenv of
      Nothing -> False
      Just t  -> typeIsListOfTask t

mkGraphAlg :: *(ExpressionAlg InhExpression *ChnExpression SynExpression)
mkGraphAlg
  =  {  app = appC, at = atC, letE = letC, caseE = caseC, var = varC
     ,  selection            = \sk e ss       _ chn -> ({syn_annot_expr = Selection sk e ss           , syn_texpr = TCleanExpr "Selection sk e ss           "}, chn)
     ,  update               = \e1 ss e2      _ chn -> ({syn_annot_expr = Update e1 ss e2             , syn_texpr = TCleanExpr "Update e1 ss e2             "}, chn)
     ,  recordUpdate         = \gd e bs       _ chn -> ({syn_annot_expr = RecordUpdate gd e bs        , syn_texpr = TCleanExpr "RecordUpdate gd e bs        "}, chn)
     ,  tupleSelect          = \ds i e        _ chn -> ({syn_annot_expr = TupleSelect ds i e          , syn_texpr = TCleanExpr "TupleSelect ds i e          "}, chn)
     ,  basicExpr            = \bv            _ chn -> ({syn_annot_expr = BasicExpr bv                , syn_texpr = TCleanExpr "BasicExpr bv                "}, chn)
     ,  conditional          = \c             _ chn -> ({syn_annot_expr = Conditional c               , syn_texpr = TCleanExpr "Conditional c               "}, chn)
     ,  anyCodeExpr          = \cb cf ss      _ chn -> ({syn_annot_expr = AnyCodeExpr cb cf ss        , syn_texpr = TCleanExpr "AnyCodeExpr cb cf ss        "}, chn)
     ,  abcCodeExpr          = \ss b          _ chn -> ({syn_annot_expr = ABCCodeExpr ss b            , syn_texpr = TCleanExpr "ABCCodeExpr ss b            "}, chn)
     ,  matchExpr            = \gd e          _ chn -> ({syn_annot_expr = MatchExpr gd e              , syn_texpr = TCleanExpr "MatchExpr gd e              "}, chn)
     ,  isConstructor        = \e gd n gi i p _ chn -> ({syn_annot_expr = IsConstructor e gd n gi i p , syn_texpr = TCleanExpr "IsConstructor e gd n gi i p "}, chn)
     ,  freeVar              = \v             _ chn -> ({syn_annot_expr = FreeVar v                   , syn_texpr = TCleanExpr "FreeVar v                   "}, chn)
     ,  dictionariesFunction = \xs e at       _ chn -> ({syn_annot_expr = DictionariesFunction xs e at, syn_texpr = TCleanExpr "DictionariesFunction xs e at"}, chn)
     ,  constant             = \si i prio     _ chn -> ({syn_annot_expr = Constant si i prio          , syn_texpr = TCleanExpr "Constant si i prio          "}, chn)
     ,  classVariable        = \vip           _ chn -> ({syn_annot_expr = ClassVariable vip           , syn_texpr = TCleanExpr "ClassVariable vip           "}, chn)
     ,  dynamicExpr          = \de            _ chn -> ({syn_annot_expr = DynamicExpr de              , syn_texpr = TCleanExpr "DynamicExpr de              "}, chn)
     ,  typeCodeExpression   = \t             _ chn -> ({syn_annot_expr = TypeCodeExpression t        , syn_texpr = TCleanExpr "TypeCodeExpression t        "}, chn)
     ,  typeSignature        = \f e           _ chn -> ({syn_annot_expr = TypeSignature f e           , syn_texpr = TCleanExpr "TypeSignature f e           "}, chn)
     ,  ee                   = \              _ chn -> ({syn_annot_expr = EE                          , syn_texpr = TCleanExpr "EE                          "}, chn)
     ,  noBind               = \eip           _ chn -> ({syn_annot_expr = NoBind eip                  , syn_texpr = TCleanExpr "NoBind eip                  "}, chn)
     ,  failExpr             = \i             _ chn -> ({syn_annot_expr = FailExpr i                  , syn_texpr = TCleanExpr "FailExpr i                  "}, chn)
     }
  where
  appC app inh chn
    # (idIsTask, menv) = symbIdentIsTask app.app_symb chn.chn_module_env
    # (appD, menv)     = ppApp app menv
    # chn              = {chn & chn_module_env = menv}
    | idIsTask
      # ((ctxs, args), menv) = dropAppContexts app chn.chn_module_env
      # chn                  = { chn & chn_module_env = menv }
      = case appFunName app of
          ">>="         -> mkBind      app ctxs args inh chn
          ">>|"         -> mkBind      app ctxs args inh chn
          "return"      -> mkReturn    app ctxs args inh chn
          "@:"          -> mkAssign    app ctxs args inh chn
          "@"           -> mkTransform app ctxs args inh chn
          //">>*"         -> mkStep      app ctxs args inh chn
          "anyTask"     -> mkParSumN   app ctxs args inh chn
          "-||-"        -> mkParSum2   app ctxs args inh chn
          "||-"         -> mkParSumR   app ctxs args inh chn
          "-||"         -> mkParSumL   app ctxs args inh chn
          "allTasks"    -> mkParProdN  app ctxs args inh chn
          "-&&-"        -> mkParProd2  app ctxs args inh chn
          "get"         -> mkGetShare  app ctxs args inh chn
          "set"         -> mkSetShare  app ctxs args inh chn
          "upd"         -> mkUpdShare  app ctxs args inh chn
          _             -> mkTaskApp   app ctxs args inh chn
    | otherwise = ({syn_annot_expr = App app, syn_texpr = TCleanExpr (ppCompact appD)}, chn)
    where
    mkBind app ctxs args inh chn
      = withTwo app args f inh chn
      where
      f lhsExpr rhsExpr=:(App rhsApp) chn
        # (synl, chnl)      = exprCata mkGraphAlg lhsExpr (addInhId inh 0) chn
        # (lbl, synr, chnr) = mkEdge rhsApp 1 inh chnl
        = ({ syn_annot_expr = App { app & app_args = ctxs ++ [synl.syn_annot_expr, synr.syn_annot_expr] }
           , syn_texpr = TBind synl.syn_texpr lbl synr.syn_texpr}, chnr)
      f lhsExpr rhsExpr chn
        # (d, menv) = ppExpression rhsExpr chn.chn_module_env
        = ({ syn_annot_expr = App { app & app_args = ctxs ++ [lhsExpr, rhsExpr] }
           , syn_texpr = TVar (ppCompact d)}, {chn & chn_module_env = menv})

    mkReturn app ctxs args=:[e:_] inh chn
      # (syn, chn) = exprCata mkGraphAlg e inh chn
      = ({ syn_annot_expr = App {app & app_args = ctxs ++ [syn.syn_annot_expr]}
         , syn_texpr = TReturn syn.syn_texpr}, chn)

    mkAssign app ctxs args inh chn
      = withTwo app args f inh chn
      where
      f u t chn
        # (syn, chn) = exprCata mkGraphAlg t (addInhId inh 0) chn
        // TODO Complex user parsing
        # (ud, menv) = ppExpression u chn.chn_module_env
        # chn        = {chn & chn_module_env = menv}
        = annotExpr (App {app & app_args = ctxs ++ [u, syn.syn_annot_expr]}) (TAssign (TUUserWithIdent (ppCompact ud)) syn.syn_texpr) inh chn

    // TODO : Test
    mkStep app ctxs args inh chn
      = withTwo app args f inh chn
      where
      f l r chn
        # (synl, chn) = exprCata mkGraphAlg l (addInhId inh 0) chn
        = case r of
            (arg=:(App _))
              | exprIsListConstr arg
                  # exprs               = fromStatic arg
                  # (scs, syns, chn, _) = let f e=:(App a=:{app_args=[App btnOrCont:asTl]}) (scs, syns, chn, n)
                                                | appFunName a == "OnAction"
                                                # [App contApp:_] = asTl // TODO Bah
                                                # (sf, syn, chn)  = mkStepCont contApp n chn
                                                # action          = extractAction btnOrCont
                                                = ([StepOnAction action sf:scs], [syn:syns], chn, n + 1)
                                                | appFunName a == "OnValue"
                                                # [App contApp:_] = asTl // TODO Bah
                                                # (sf, syn, chn)  = mkStepCont contApp n chn
                                                = ([StepOnValue sf:scs], [syn:syns], chn, n + 1)
                                                | appFunName a == "OnException"
                                                # (lbl, syn, chn) = mkEdge btnOrCont n inh chn
                                                = ([StepOnException lbl syn.syn_texpr:scs], [syn:syns], chn, n + 1)
                                                | appFunName a == "OnAllExceptions"
                                                # (lbl, syn, chn) = mkEdge btnOrCont n inh chn
                                                = ([StepOnException lbl syn.syn_texpr:scs], [syn:syns], chn, n + 1)
                                              f _ (scs, syns, chn, n) = (scs, syns, chn, n + 1)
                                          in  foldr f ([], [], chn, 1) exprs
                  # (stArgs, pdss) = toStatic (map (\s -> s.syn_annot_expr) syns) chn.chn_predef_symbols
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
            = (IfValue (ppCompact ppHdRemFArgs) fApp.app_symb.symb_ident.id_name
                (map ppCompact (ppFAppArgs ++ [ppHdRemFArgs:ppTlRemFArgs])) lbl syn.syn_texpr
              , syn, chn)
          "hasValue"
            # [(App tApp):_]  = contApp.app_args // TODO Bah
            # (lbl, syn, chn) = mkEdge tApp n inh chn
            = (HasValue lbl syn.syn_texpr, syn, chn)
          "ifStable"
            # [(App tApp):_]  = contApp.app_args // TODO Bah
            # (lbl, syn, chn) = mkEdge tApp n inh chn
            = (IfStable lbl syn.syn_texpr, syn, chn)
          "ifUnstable"
            # [(App tApp):_]  = contApp.app_args // TODO Bah
            # (lbl, syn, chn) = mkEdge tApp n inh chn
            = (IfUnstable lbl syn.syn_texpr, syn, chn)
          "ifCond"
            # [cond:(App tApp):_] = contApp.app_args // TODO Bah
            # (lbl, syn, chn)     = mkEdge tApp n inh chn
            # (d, menv)           = ppExpression cond chn.chn_module_env
            = (IfCond (ppCompact d) lbl syn.syn_texpr, syn, { chn & chn_module_env = menv })
          "always"
            # (syn, chn) = exprCata mkGraphAlg (hd contApp.app_args) (addInhId inh n) chn
            = (Always syn.syn_texpr, syn, chn)

    mkTaskApp app ctxs args inh chn
    // TODO Cata the args
      # (ps, menv) = mapSt ppExpression args chn.chn_module_env
      # chn        = {chn & chn_module_env = menv}
      # appArgs    = map ppCompact ps  // TODO : When do we pprint a Clean expr? And when do we generate a subgraph?
      = annotExpr (App app) (TTaskApp inh.inh_ids (appFunName app) (map TVar appArgs)) inh chn
      //# (ss, chn) = let f e (ss, chn)
                         //# (syn, chn) = exprCata mkGraphAlg e inh chn
                         //= ([syn:ss], chn)
                    //in  foldr f ([], chn) args
      //= annotExpr (App {app & app_args = ctxs ++ map (\s -> s.syn_annot_expr) ss})
                  //(TTaskApp inh.inh_ids (appFunName app) (map (\s -> s.syn_texpr) ss)) inh chn

    mkTransform app ctxs args inh chn
      = withTwo app args f inh chn
      where
      f l r=:(App {app_symb, app_args}) chn
        # (syn, chn)           = exprCata mkGraphAlg l inh chn
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
        # (synl, chnl) = exprCata mkGraphAlg l (addInhId inh 0) chn
        # (synr, chnr) = exprCata mkGraphAlg r (addInhId inh 1) chnl
        = ( { syn_annot_expr = App {app & app_args = ctxs ++ [synl.syn_annot_expr, synr.syn_annot_expr]}
            , syn_texpr = TParallel (mkPar synl.syn_texpr synr.syn_texpr)}
          , chnr)

    mkParN mkPar app ctxs args inh chn
      = case args of
          [arg=:(App _):_]
            | exprIsListConstr arg
              # exprs        = fromStatic arg
              # (ss, _, chn) = let f e (ss, n, chn)
                                    # (syn, chn) = exprCata mkGraphAlg e {inh & inh_ids = inh.inh_ids ++ [n]} chn
                                    = ([syn:ss], n + 1, chn)
                               in  foldr f ([], 0, chn) exprs
              # (listArg, pdss) = toStatic (map (\s -> s.syn_annot_expr) ss) chn.chn_predef_symbols
              = ( { syn_annot_expr = App {app & app_args = [listArg]}
                  , syn_texpr = TParallel (mkPar (T (map (\s -> s.syn_texpr) ss)))}
                , {chn & chn_predef_symbols = pdss})
            | otherwise = doPP arg
          [arg=:(Var _):_] = doPP arg
      where
      doPP arg
        # (doc, menv) = ppExpression arg chn.chn_module_env
        # ppStr       = ppCompact doc
        # chn         = {chn & chn_module_env = menv}
        = ({syn_annot_expr = App app, syn_texpr = TParallel (mkPar (PP ppStr))}, chn)

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
  atC e [] inh chn = abort "atC: no args" // TODO e is a non-applied higher order function. What do we do with this?
  atC e=:(App app) es inh chn
    // TODO : Introduce lets in the graph for all variables that are being applied
    | identIsLambda app.app_symb.symb_ident
        # (mfd, menv)   = reifyFunDef app.app_symb chn.chn_module_env
        # fd            = fromMaybe (abort ("atC: failed to reify " +++ app.app_symb.symb_ident.id_name)) mfd
        # letargs       = drop (length app.app_args) (getFunArgs fd)
        # (binds, menv) = zipWithSt zwf letargs es menv
        # chn           = { chn & chn_module_env = menv }
        # (syne, chn)   = exprCata mkGraphAlg (getFunRhs fd) inh chn
        # menv          = updateWithAnnot app.app_symb syne.syn_annot_expr chn.chn_module_env
        # chn           = { chn & chn_module_env = menv}
        = ({syn_annot_expr = e @ es, syn_texpr = TVar "TODO @"}, chn)
    | otherwise    =  abort "atC: otherwise case" // TODO : pretty print function application
    where
      zwf eVar eVal menv
        # (fvl, menv) = ppFreeVar eVar menv
        # (fvr, menv) = ppExpression eVal menv
        = ((ppCompact fvl, ppCompact fvr), menv)

  atC e es _ chn = ({syn_annot_expr = e @ es, syn_texpr = TVar "TODO @"}, chn)

  letC lt inh chn
    # mexpr = listToMaybe [ bnd.lb_src \\ bnd <- getLetBinds lt
                          | bnd.lb_dst.fv_ident.id_name == "_case_var"]
    = mkLet mexpr lt inh chn
    where
    mkLet (Just expr) lt inh chn
      # (syn, chn) = exprCata mkGraphAlg lt.let_expr {inh & inh_case_expr = Just expr } chn
      # l          = {lt & let_expr = syn.syn_annot_expr}
      = ({syn & syn_annot_expr = Let l}, chn)
    mkLet Nothing lt inh chn
      # (tys, chn)    = letTypes lt.let_info_ptr chn
      # (binds, menv) = flattenBinds lt chn.chn_module_env
      # tyenv         = zipSt (\(v, _) t tyenv -> put v t tyenv) binds tys inh.inh_tyenv // TODO This probably won't work for arbitrary patterns, so we actually need to be a bit smarter here and extract all variables from the patterns, instead of just PP'ing the pattern and using that as index
      // TODO : Represent the bindings in any way possible, not just PP
      # (syn, chn)    = exprCata mkGraphAlg lt.let_expr {inh & inh_tyenv = tyenv} {chn & chn_module_env = menv}
      = ({ syn_annot_expr = Let {lt & let_expr = syn.syn_annot_expr}
         , syn_texpr = TLet binds syn.syn_texpr}, chn)
      where
      flattenBinds lt menv
        = foldrSt f (getLetBinds lt) ([], menv)
        where
        f bnd (xs, menv)
          # (pprhs, menv) = ppExpression bnd.lb_src menv
          = ([(bnd.lb_dst.fv_ident.id_name, PP (ppCompact pprhs)):xs], menv)
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
  caseC cs inh chn
    # inh                   = {inh & inh_case_expr = Nothing }
    # (ed, menv)            = ppExpression caseExpr chn.chn_module_env
    # ((guards, syns), chn) = mkAlts cs.case_guards {chn & chn_module_env = menv}
    # ((def, syns), chn)    = case cs.case_default of
                                Yes def
                                  # (syn, chn) = mkAlts` def chn
                                  = ((Yes syn.syn_annot_expr, [("_", syn):syns]), chn)
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
          = (([ap:aps], [(ppCompact apd, syn):syns]), chn)
          where
          mkAp sym []   menv = ('PPrint'.text sym.glob_object.ds_ident.id_name, menv)
          mkAp sym vars menv
            # (fvds, menv) = mapSt ppFreeVar vars menv
            = ('PPrint'.text sym.glob_object.ds_ident.id_name 'PPrint'. <+> 'PPrint'.hcat fvds, menv)
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
          = (([bp:bps], [(ppCompact bvd, syn):syns]), chn)
    mkAlts c chn = ((c, []), chn)

    mkAlts` :: Expression ChnExpression -> (SynExpression, ChnExpression)
    mkAlts` expr chn
      # (syn, chn) = exprCata mkGraphAlg expr inh chn
      # menv       = chn.chn_module_env
      # (d, menv)  = ppExpression expr menv
      # chn        = {chn & chn_module_env = menv}
      = (syn, chn)

  // TODO Determine whether it's a Task a or [Task a]
  // We can do so by maintaining an environment. At lets and lambdas, store the bound variable and its type in the env
  varC bv inh chn
    | varIsTask bv inh       = annotExpr (Var bv) (TVar bv.var_ident.id_name) inh chn
    | varIsListOfTask bv inh = ({syn_annot_expr = Var bv, syn_texpr = TVar bv.var_ident.id_name}, chn) // TODO Annotate with special wrapper (or just wrap with a map... have to see)
    | otherwise              = ({syn_annot_expr = Var bv, syn_texpr = TVar bv.var_ident.id_name}, chn)

mkEdge :: App Int InhExpression *ChnExpression -> *(Maybe String, SynExpression, *ChnExpression)
mkEdge app=:{app_symb, app_args} n inh chn
  # (siIsTask, menv) = symbIdentIsTask app_symb chn.chn_module_env
  | identIsLambda app_symb.symb_ident
    # ((args, tFd), menv) = reifyArgsAndDef app_symb menv
    # patid               = last [freeVarName x \\ x <- args| x.fv_def_level == -1]
    # (syne, chn)         = exprCata mkGraphAlg (getFunRhs tFd) (addInhId inh n) { chn & chn_module_env = menv }
    # menv                = updateWithAnnot app_symb syne.syn_annot_expr chn.chn_module_env
    = (Just patid, {syne & syn_annot_expr = App app}, {chn & chn_module_env = menv})
  | siIsTask
    # ((args, tFd), menv) = reifyArgsAndDef app_symb menv
    # (lbl, menv) = case drop (length app_args) args of
                      [] = (Nothing, menv)
                      [x:_]
                        # (d, menv) = ppFreeVar x menv
                        = (Just (ppCompact d), menv)
    # (syn, chn)  = exprCata mkGraphAlg (App app) (addInhId inh n) {chn & chn_module_env = menv}
    = (lbl, syn, chn)
  | otherwise
    # (d, menv) = ppApp app menv
    = (Nothing, {syn_annot_expr = App app, syn_texpr = TVar (ppCompact d)}
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
    # (argTys, tyenv) = zipWithSt (\arg t st -> ((arg, t), put arg.fv_ident.id_name t st)) tb.tb_args (funArgTys fd) newMap
    # (syn, chn)      = exprCata mkGraphAlg tb.tb_rhs {inh & inh_tyenv = tyenv} chn
    = ( Just (map (\(arg, ty) -> (arg.fv_ident.id_name, ppCompact (ppType ty))) argTys, syn.syn_texpr, syn.syn_annot_expr) //Just g, syn.syn_annot_expr)
      , chn.chn_module_env, chn.chn_heaps, chn.chn_predef_symbols)
funToGraph _ menv heaps predef_symbols = (Nothing, menv, heaps, predef_symbols)
