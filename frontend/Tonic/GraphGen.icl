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
withTwo app _         _ inh chn = ({syn_annot_expr = App app, syn_texpr = Nothing}, chn)

annotExpr :: App (Maybe SymbIdent) (Maybe [Expression]) InhExpression
             *ChnExpression SynExpression
          -> *(SynExpression, *ChnExpression)
annotExpr app mbRepSI mbArgs inh chn syn
  # (tune_symb, predefs) = (chn.chn_predef_symbols)![PD_tonicWrapApp]
  | predefIsUndefined tune_symb = (syn, {chn & chn_predef_symbols = predefs})
  | otherwise
      # (papp, menv) = isPartialApp app chn.chn_module_env
      # chn          = {chn & chn_module_env = menv, chn_predef_symbols = predefs}
      | papp         = (syn, chn)
      | otherwise
        # (app, chn) = mkTuneApp chn
        = ({syn & syn_annot_expr = App app}, chn)
  where
  mkTuneApp chn
    # menv = chn.chn_module_env
    # icl  = menv.me_icl_module
    # nm   = icl.icl_name.id_name
    # menv = {menv & me_icl_module = icl}
    # chn         = {chn & chn_module_env = menv}
    # (app, pdss) = appPredefinedSymbol PD_tonicWrapApp
                      [ mkStr nm
                      , mkStr inh.inh_curr_task_name
                      , mkStr (ppExprId inh.inh_ids)
                      , App {app & app_symb = fromMaybe app.app_symb mbRepSI
                                 , app_args = fromMaybe app.app_args mbArgs}
                      ] SK_Function chn.chn_predef_symbols
    # chn         = {chn & chn_predef_symbols = pdss}
    = (app, chn)

ppExprId :: ExprId -> String
ppExprId eid = foldr (\x xs -> toString x +++ "." +++ xs) "" eid

getModuleName :: *ChnExpression -> *(String, *ChnExpression)
getModuleName chn
  # menv = chn.chn_module_env
  # icl  = menv.me_icl_module
  # nm   = icl.icl_name.id_name
  # menv = {menv & me_icl_module = icl}
  # chn  = {chn & chn_module_env = menv}
  = (nm, chn)

lastElem :: [a] -> a
lastElem [x]    = x
lastElem [_:xs] = lastElem xs

varIsTask :: VarInfoPtr *ChnExpression -> *(Bool, *ChnExpression)
varIsTask varptr chn
  # heaps = chn.chn_heaps
  # (vi, var_heap) = readPtr varptr heaps.hp_var_heap
  # chn = {chn & chn_heaps = {heaps & hp_var_heap = var_heap}}
  = case vi of
      VI_Type aty _ -> (atypeIsTask aty, chn)
      _             -> (False, chn)

varIsTaskFun :: VarInfoPtr *ChnExpression -> *(Bool, *ChnExpression)
varIsTaskFun varptr chn
  # heaps = chn.chn_heaps
  # (vi, var_heap) = readPtr varptr heaps.hp_var_heap
  # chn = {chn & chn_heaps = {heaps & hp_var_heap = var_heap}}
  = case vi of
      VI_FAType _ aty _    -> (atypeIsTask aty, chn)
      VI_FATypeC _ aty _ _ -> (atypeIsTask aty, chn)
      _                    -> (False, chn)

mkGraphAlg :: *(ExpressionAlg InhExpression *ChnExpression SynExpression)
mkGraphAlg
  =  {  app = appC, at = atC, letE = letC, caseE = caseC, var = varC
     ,  selection            = \sk e ss       _ chn -> (mkSynExpr (Selection sk e ss           ), chn)
     ,  update               = \e1 ss e2      _ chn -> (mkSynExpr (Update e1 ss e2             ), chn)
     ,  recordUpdate         = \gd e bs       _ chn -> (mkSynExpr (RecordUpdate gd e bs        ), chn)
     ,  tupleSelect          = \ds i e        _ chn -> (mkSynExpr (TupleSelect ds i e          ), chn)
     ,  basicExpr            = \bv            _ chn -> (mkSynExpr (BasicExpr bv                ), chn)
     ,  conditional          = \c             _ chn -> (mkSynExpr (Conditional c               ), chn)
     ,  anyCodeExpr          = \cb cf ss      _ chn -> (mkSynExpr (AnyCodeExpr cb cf ss        ), chn)
     ,  abcCodeExpr          = \ss b          _ chn -> (mkSynExpr (ABCCodeExpr ss b            ), chn)
     ,  matchExpr            = \gd e          _ chn -> (mkSynExpr (MatchExpr gd e              ), chn)
     ,  isConstructor        = \e gd n gi i p _ chn -> (mkSynExpr (IsConstructor e gd n gi i p ), chn)
     ,  freeVar              = \v             _ chn -> (mkSynExpr (FreeVar v                   ), chn)
     ,  dictionariesFunction = \xs e at       _ chn -> (mkSynExpr (DictionariesFunction xs e at), chn)
     ,  constant             = \si i prio     _ chn -> (mkSynExpr (Constant si i prio          ), chn)
     ,  classVariable        = \vip           _ chn -> (mkSynExpr (ClassVariable vip           ), chn)
     ,  dynamicExpr          = \de            _ chn -> (mkSynExpr (DynamicExpr de              ), chn)
     ,  typeCodeExpression   = \t             _ chn -> (mkSynExpr (TypeCodeExpression t        ), chn)
     ,  typeSignature        = \f e           _ chn -> (mkSynExpr (TypeSignature f e           ), chn)
     ,  ee                   = \              _ chn -> (mkSynExpr (EE                          ), chn)
     ,  noBind               = \eip           _ chn -> (mkSynExpr (NoBind eip                  ), chn)
     ,  failExpr             = \i             _ chn -> (mkSynExpr (FailExpr i                  ), chn)
     }
  where
  appC app inh chn // TODO Take arity into account: if a task is partially applied, wrap it in a lambda and annotate that
    # (idIsTask, menv) = symbIdentIsTask app.app_symb chn.chn_module_env
    # chn = {chn & chn_module_env = menv}
    | idIsTask
      # ((ctxs, args), menv) = dropAppContexts app chn.chn_module_env
      # chn                  = { chn & chn_module_env = menv }
      = case appFunName app of
          ">>="       -> mkBind       app ctxs args              inh chn
          ">>|"       -> mkBind       app ctxs args              inh chn
          "return"    -> mkReturn     app ctxs args              inh chn
          "@:"        -> mkAssign     app ctxs args              inh chn
          "@"         -> mkTransform  app ctxs args              inh chn
          ">>*"       -> mkStep       app ctxs args              inh chn
          "-||-"      -> mkParBinApp  app ctxs args "sumn"       inh chn // TODO Ugh
          "||-"       -> mkParBinApp  app ctxs args "sumr"       inh chn // TODO Ugh
          "-||"       -> mkParBinApp  app ctxs args "suml"       inh chn // TODO Ugh
          "-&&-"      -> mkParBinApp  app ctxs args "prod"       inh chn // TODO Ugh
          "anyTask"   -> mkParListApp app ctxs args "sumn"       inh chn // TODO Ugh
          "allTasks"  -> mkParListApp app ctxs args "prod"       inh chn // TODO Ugh
          _           -> mkTaskApp    app ctxs args              inh chn
    | otherwise = (mkSynExpr (App app), chn)
    where
    mkBind app ctxs args inh chn
      = withTwo app args f inh chn
      where
      f lhsExpr rhsExpr chn
        # (synl, chnl) = exprCata mkGraphAlg lhsExpr {inh & inh_ids = inh.inh_ids ++ [0]} chn
        # (edgeLbl, (synr, chnr))
            = case (exprIsLambda rhsExpr, rhsExpr) of
                (True, App rhsApp)
                  # ((funArgs, rhsfd), menv) = reifyArgsAndDef rhsApp.app_symb chnl.chn_module_env
                  # patid       = lastElem [freeVarName x \\ x <- funArgs| x.fv_def_level == -1]
                  # (syne, chn) = exprCata mkGraphAlg (getFunRhs rhsfd) {inh & inh_ids = inh.inh_ids ++ [1]} { chnl & chn_module_env = menv }
                  # menv        = updateWithAnnot rhsApp.app_symb syne.syn_annot_expr chn.chn_module_env
                  = (Just patid, (({syne & syn_annot_expr = rhsExpr}, {chn & chn_module_env = menv})))
                _ = (Nothing, (exprCata mkGraphAlg rhsExpr {inh & inh_ids = inh.inh_ids ++ [1]} chnl))
        # app` = { app & app_args = ctxs ++ [synl.syn_annot_expr, synr.syn_annot_expr] }
        = case (synl.syn_texpr, synr.syn_texpr) of
            (Just l, Just r) -> ({syn_annot_expr = App app`, syn_texpr = Just (TBind (T l) edgeLbl (T r))}, chnr)
            (Just l, _)      -> ({syn_annot_expr = App app`, syn_texpr = Just (TBind (T l) edgeLbl (PP "TODO PP RHS"))}, chnr)
            (_, Just r)      -> ({syn_annot_expr = App app`, syn_texpr = Just (TBind (PP "TODO PP LHS") edgeLbl (T r))}, chnr)
            (_, _)           -> ({syn_annot_expr = App app`, syn_texpr = Just (TBind (PP "TODO PP LHS") edgeLbl (PP "TODO PP RHS"))}, chnr)

    // TODO Support subgraphs in return
    mkReturn app ctxs args inh chn
      # (mn, chn)  = getModuleName chn
      # (ppd, chn) = case args of
                       [x:_] -> mkRet x chn
                       _     -> abort "mkReturn: should not happen"
      = ({syn_annot_expr = App app, syn_texpr = Just (TReturn (PP ppd))}, chn)
      where
      // In case of a function application, we want to inspect the type of the
      // function. If it is a task or a list, treat it differently than any
      // other type.
      mkRet (BasicExpr bv) chn
        # (bvd, menv) = ppBasicValue bv chn.chn_module_env
        = (ppCompact bvd, {chn & chn_module_env = menv})
      mkRet (Var bv)       chn = (bv.var_ident.id_name, chn)
      mkRet e              chn
        # (d, menv) = ppExpression e chn.chn_module_env
        # chn = {chn & chn_module_env = menv}
        = (ppCompact d, chn)

    mkAssign app ctxs args inh chn
      = withTwo app args f inh chn
      where
      f u t chn
        # (syn, chn) = exprCata mkGraphAlg t {inh & inh_ids = inh.inh_ids ++ [0]} chn
        // TODO Complex user parsing
        # (ud, menv) = ppExpression u chn.chn_module_env
        # chn        = {chn & chn_module_env = menv}
        = case syn.syn_texpr of
            Just texpr
              -> annotExpr app Nothing Nothing inh chn {syn & syn_texpr = Just (TAssign (TUUserWithIdent (ppCompact ud)) (T texpr))}
            _ -> abort "mkAssign: no texpr for rhs"

    // TODO : Implement this correctly
    mkStep app ctxs args inh chn
      = withTwo app args f inh chn
      where
      f l r chn
        # (syn, chn) = exprCata mkGraphAlg l {inh & inh_ids = inh.inh_ids ++ [0]} chn
        = case r of
            (arg=:(App _))
              | exprIsListConstr arg
                  # exprs           = fromStatic arg
                  //# (star1id, g)    = addNode (mkGNode GStepStar) chn.chn_graph
                  //# (star2id, g)    = addNode (mkGNode GStepStar) g
                  //# chn             = {chn & chn_graph = g}
                  # (gs, syns, chn) = let f e=:(App a=:{app_args=[App btnOrCont:es]}) (gs, syns, chn)
                                            | appFunName a == "OnAction"
                                            # action = extractAction btnOrCont
                                            # [App contApp:_] = es // TODO bluh
                                            # (seId, (syn, chn)) =
                                                case appFunName contApp of
                                                  "ifValue"
                                                    # [(App fargApp):t:_]  = contApp.app_args // TODO Bah
                                                    # (syn, chn)           = exprCata mkGraphAlg t inh chn
                                                    # (ps, menv)           = mapSt ppExpression app.app_args chn.chn_module_env
                                                    # ((funArgs, _), menv) = reifyArgsAndDef fargApp.app_symb menv
                                                    # ([a:as], menv)       = mapSt ppFreeVar funArgs menv
                                                    # chn                  = {chn & chn_module_env = menv}
                                                    //# (seId, g)            = addNode (mkGNode (GStepElem (StepOnAction action StepIfValue))) chn.chn_graph
                                                    //# (cndId, g)           = addNode (mkGNode (GStepCond {tifv_funName = appFunName fargApp, tifv_args = map ppCompact [a:as]})) g
                                                    //# g                    = addEdge (mkEdge (ppCompact a)) (seId, cndId) g
                                                    //# chn                  = {chn & chn_graph = g}
                                                    = (0, (syn, chn))
                                                  "always"
                                                    # [t:_]      = contApp.app_args // TODO This too
                                                    # (syn, chn) = exprCata mkGraphAlg t inh chn
                                                    //# (seId, g)  = addNode (mkGNode (GStepElem (StepOnAction action StepAlways))) chn.chn_graph
                                                    //# chn        = {chn & chn_graph = g}
                                                    = (0, (syn, chn))
                                            = ([seId:gs], [syn:syns], chn)
                                            | appFunName a == "OnValue"
                                            // TODO : Implement
                                            = (gs, syns, chn)
                                            | appFunName a == "OnException"
                                            // TODO : Implement
                                            = (gs, syns, chn)
                                            | appFunName a == "OnAllExceptions"
                                            // TODO : Implement
                                            = (gs, syns, chn)
                                          f _ (gs, syns, chn) = (gs, syns, chn)
                                      in  foldr f ([], [], chn) exprs
                  = annotExpr app Nothing Nothing inh chn (mkSynExpr (App app))
              //| otherwise
                  //# (n, g) = addNode (mkGNode (GStep [])) chn.chn_graph // TODO
                  //= (mkSingleIdSynExpr (Just n), {chn & chn_graph = g})
                  // TODO
            //(vararg=:(Var bv))
              //# (syn, chn)  = exprCata mkGraphAlg vararg inh chn
              //# nid         = fromMaybe -1 syn.syn_node_id
              //# (mod, menv) = (chn.chn_module_env)!me_icl_module
              //# chn         = {chn & chn_module_env = menv}
              //= annotExpr nid app Nothing (Just (App app)) inh chn (mkSingleIdSynExpr (Just nid))
            _ = (mkSynExpr (App app), chn)
      extractAction app=:{app_args=[BasicExpr (BVS str):_]}
        | app.app_symb.symb_ident.id_name == "Action" = str
      extractAction _ = "(no action)"

    mkTaskApp app ctxs args inh chn
      # (ps, menv) = mapSt ppExpression args chn.chn_module_env
      # chn        = {chn & chn_module_env = menv}
      # appArgs    = map ppCompact ps  // TODO : When do we pprint a Clean expr? And when do we generate a subgraph?
      = annotExpr app Nothing Nothing inh chn {syn_annot_expr = App app, syn_texpr = Just (TTaskApp inh.inh_ids (appFunName app) appArgs)}

    mkTransform app ctxs args inh chn
      = withTwo app args f inh chn
      where
      f l (App {app_symb, app_args}) chn
        # (syn, chn)           = exprCata mkGraphAlg l inh chn
        # (ppl, menv)          = mapSt ppExpression app_args chn.chn_module_env
        # ((funArgs, _), menv) = reifyArgsAndDef app_symb menv
        # ([_:a:as], menv)     = mapSt ppFreeVar funArgs menv // FIXME : Dirty patter matching
        # chn                  = {chn & chn_module_env = menv}
        = case syn.syn_texpr of
            Just t -> ({syn_annot_expr = App app, syn_texpr = Just (TTransform (T t) (ppCompact a) (map ppCompact (ppl ++ [a:as]))) }, chn)
            _      -> (mkSynExpr (App app), chn)

    mkParBinApp app ctxs args t inh chn
      = withTwo app args f inh chn
      where
      f l r chn
        # (synr, chnr) = exprCata mkGraphAlg r inh chn // & chn_graph = emptyGraphWithLastId (getLastId chn.chn_graph)}
        //# g            = addStartStop synr.syn_node_id chnr.chn_graph
        # (synl, chnl) = exprCata mkGraphAlg l inh chnr // {chnr & chn_graph = emptyGraphWithLastId (getLastId chnr.chn_graph)}
        //# g            = addStartStop synl.syn_node_id chnl.chn_graph
        //# (pid, g)     = addNode (mkGNode (GParallel join [Subgraph chnl.chn_graph, Subgraph chnr.chn_graph])) (setLastId chn.chn_graph (getLastId chnl.chn_graph))
        //= case (synl.syn_node_id, synr.syn_node_id) of
            //(Just _, Just _)
        = annotExpr app Nothing Nothing inh chnl (mkSynExpr (App app))
            //(lid, rid)
              //= edgeErr "bin app edge" lid l rid r chnl
        // TODO : If there are no two elems in the list, the expr is eta-reduced, so we need to pprint it instead of throwing an error

    // TODO : Can be eta-reduced
    // TODO : In the case where we have
    //    anyTask [someTask, otherTask]
    // we just split, have two nodes someTask and otherTask, then a merge again.
    // Only when the list anyTask is applied to is a list comprehension we generate
    // a more detailed graph with content. Only in that case, there is just one
    // new node (and not even a chain of nodes). We know exactly how many nodes
    // we will get and can therefore link to the join node
    mkParListApp app ctxs args t inh chn
      = case args of
          [arg=:(App _):_]
            | exprIsListConstr arg
                # exprs        = fromStatic arg
                # (ss, _, chn) = let f e (ss, n, chn)
                                      # (syn, chn) = exprCata mkGraphAlg e {inh & inh_ids = inh.inh_ids ++ [n]} chn
                                      = ([syn:ss], n + 1, chn)
                                 in  foldr f ([], 0, chn) exprs
                # (listArg, pdss) = toStatic (map (\s -> s.syn_annot_expr) ss) chn.chn_predef_symbols
                # tExpr = case (t, map (\s -> s.syn_texpr) ss) of // TODO Bah
                            ("suml", [Just l:Just r:_])
                              = ParSum (T (ParSumL (T l) (T r)))
                            ("sumr", [Just l:Just r:_])
                              = ParSum (T (ParSumR (T l) (T r)))
                            ("sumn", ss`)
                              = ParSum (T (ParSumN (T (map fromJust ss`)))) // TODO Bah
                            ("prod", ss`)
                              = ParProd (T (map fromJust ss`)) // TODO Bah
                = ({syn_annot_expr = App {app & app_args = [listArg]}, syn_texpr = Just (TParallel tExpr)}, {chn & chn_predef_symbols = pdss}) // annotExpr app Nothing (Just exprs) inh chn (mkSynExpr (App app))
            | otherwise
                # (doc, menv) = ppExpression arg chn.chn_module_env
                # ppStr       = ppCompact doc
                # chn         = {chn & chn_module_env = menv}
                # tExpr = case t of // TODO Bah
                            "prod"
                              = ParProd (PP ppStr)
                            _ = ParSum (PP ppStr)
                = ({syn_annot_expr = App app, syn_texpr = Just (TParallel tExpr)}, chn)
          [arg=:(Var _):_] // TODO test
            # (doc, menv) = ppExpression arg chn.chn_module_env
            # ppStr       = ppCompact doc
            # chn         = {chn & chn_module_env = menv}
            # tExpr = case t of // TODO Bah
                        "prod"
                          = ParProd (PP ppStr)
                        _ = ParSum (PP ppStr)
            = ({syn_annot_expr = App app, syn_texpr = Just (TParallel tExpr)}, chn)

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
        //# (lid, g)      = addNode (mkGNode (GLet {GLet | glet_binds = binds})) chn.chn_graph
        # (syne, chn)   = exprCata mkGraphAlg (getFunRhs fd) inh chn // { chn & chn_graph = g }
        //# g             = case syne.syn_node_id of
                            //Just eid -> addEmptyEdge (lid, eid) chn.chn_graph
                            //_        -> chn.chn_graph
        # menv          = updateWithAnnot app.app_symb syne.syn_annot_expr chn.chn_module_env
        # chn           = { chn & chn_module_env = menv} //, chn_graph = g }
        = (mkSynExpr (e @ es), chn)
    | otherwise    =  abort "atC: otherwise case" // TODO : pretty print function application
    where
      zwf eVar eVal menv
        # (fvl, menv) = ppFreeVar eVar menv
        # (fvr, menv) = ppExpression eVal menv
        = ((ppCompact fvl, ppCompact fvr), menv)

  atC e es _ chn = (mkSynExpr (e @ es), chn)
  //atC _ _ _ _ = abort "atC: something else than App"

  //atC (Var _)                       _ _ _ = abort "atC: var"
  //atC (App _)                       _ _ _ = abort "atC: app"
  //atC (_ @ _)                       _ _ _ = abort "atC: @"
  //atC (Let _)                       _ _ _ = abort "atC: let"
  //atC (Case _)                      _ _ _ = abort "atC: case"
  //atC (Selection _ _ _)             _ _ _ = abort "atC: selection"
  //atC (Update _ _ _)                _ _ _ = abort "atC: update"
  //atC (RecordUpdate _ _ _)          _ _ _ = abort "atC: recordupdate"
  //atC (TupleSelect _ _ _)           _ _ _ = abort "atC: tupleselect"
  //atC (BasicExpr _)                 _ _ _ = abort "atC: basicExpr"
  //atC (Conditional _)               _ _ _ = abort "atC: conditional"
  //atC (AnyCodeExpr _ _ _)           _ _ _ = abort "atC: anycodeexpr"
  //atC (ABCCodeExpr _ _)             _ _ _ = abort "atC: abccodeexpr"
  //atC (MatchExpr _ _)               _ _ _ = abort "atC: matchexpr"
  //atC (IsConstructor _ _ _ _ _ _)   _ _ _ = abort "atC: isConstructor"
  //atC (FreeVar _)                   _ _ _ = abort "atC: FreeVar"
  //atC (DictionariesFunction  _ _ _) _ _ _ = abort "atC: DictionariesFunction"
  //atC (Constant _ _ _)              _ _ _ = abort "atC: Constant"
  //atC (ClassVariable _)             _ _ _ = abort "atC: ClassVariable"
  //atC (DynamicExpr _)               _ _ _ = abort "atC: DynamicExpr"
  //atC (TypeCodeExpression _)        _ _ _ = abort "atC: TypeCodeExpression"
  //atC (TypeSignature _ _)           _ _ _ = abort "atC: TypeSignature"
  //atC EE                            _ _ _ = abort "atC: EE"
  //atC (NoBind _)                    _ _ _ = abort "atC: NoBind"
  //atC (FailExpr _)                  _ _ _ = abort "atC: FailExpr"

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
      # (binds, menv) = mkGLetBinds lt chn.chn_module_env
      // TODO : Represent the bindings in any way possible, not just PP
      # (syn, chn)    = exprCata mkGraphAlg lt.let_expr inh {chn & chn_module_env = menv}
      # l = {lt & let_expr = syn.syn_annot_expr}
      # t = case syn.syn_texpr of
              Just t -> T t
              _      -> PP "TODO: PP the expression insted"
      = ({syn & syn_annot_expr = Let l, syn_texpr = Just (TLet binds t)}, chn)

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

  // TODO : Update cases, both rhss and matching expr
  // TODO : Do we need to beware of case blocks that actually resemble if statements? These get re-sugared later in the pipeline (probably for more efficient code)
  //caseC cs inh chn = ({mkSynExpr & syn_annot_expr = Just (Case cs)}, chn)

  caseC cs inh chn
    # inh           = {inh & inh_case_expr = Nothing }
    # (ed, menv)    = ppExpression caseExpr chn.chn_module_env
    //# (ni, g)       = addNode (mkGNode (GDecision CaseDecision (ppCompact ed))) chn.chn_graph
    # (guards, chn) = mkAlts 0 cs.case_guards {chn & chn_module_env = menv} //, chn_graph = g}
    # (def, chn)    = case cs.case_default of
                        Yes def
                          # (syn, chn) = mkAlts` 0 ('PPrint'.text "_") def chn
                          = (Yes syn.syn_annot_expr, chn)
                        _ = (No, chn)
    # cs`           = {cs & case_default = def, case_guards = guards}
    = (mkSynExpr (Case cs`), chn)
    where
    caseExpr = fromMaybe cs.case_expr inh.inh_case_expr
    mkAlts ni c=:(AlgebraicPatterns gi aps) chn
      # (aps, chn) = foldr f ([], chn) aps
      = (AlgebraicPatterns gi aps, chn)
      where
        f ap (aps, chn)
          # menv        = chn.chn_module_env
          # (apd, menv) = mkAp ap.ap_symbol ap.ap_vars menv
          # chn         = {chn & chn_module_env = menv}
          # (syn, chn)  = mkAlts` 0 apd ap.ap_expr chn
          # ap          = {ap & ap_expr = syn.syn_annot_expr}
          = ([ap:aps], chn)
          where
          mkAp sym []   menv = ('PPrint'.text sym.glob_object.ds_ident.id_name, menv)
          mkAp sym vars menv
            # (fvds, menv) = mapSt ppFreeVar vars menv
            = ('PPrint'.text sym.glob_object.ds_ident.id_name 'PPrint'. <+> 'PPrint'.hcat fvds, menv)
    mkAlts ni c=:(BasicPatterns bt bps) chn
      # (bps, chn) = foldr f ([], chn) bps
      = (BasicPatterns bt bps, chn)
      where
        f bp (bps, chn)
          # menv        = chn.chn_module_env
          # (bvd, menv) = ppBasicValue bp.bp_value menv
          # chn         = {chn & chn_module_env = menv}
          # (syn, chn)  = mkAlts` ni bvd bp.bp_expr chn
          # bp          = {bp & bp_expr = syn.syn_annot_expr}
          = ([bp:bps], chn)
    mkAlts ni c chn = (c, chn)

    mkAlts` :: Int Doc Expression ChnExpression -> (SynExpression, ChnExpression)
    mkAlts` ni lblDoc expr chn
      # (syn, chn) = exprCata mkGraphAlg expr inh chn
      # menv       = chn.chn_module_env
      # (d, menv)  = ppExpression expr menv
      # chn        = {chn & chn_module_env = menv}
      //# g          = addEdge (mkEdge (ppCompact lblDoc)) (ni, fromMaybe (trace_n (ppCompact d) abort "Failed to add edge from decision node to branch") syn.syn_node_id) chn.chn_graph
      = (syn, chn) // {chn & chn_graph = g})

  // TODO Determine whether it's a Task a or [Task a]
  // We can do so by maintaining an environment. At lets and lambdas, store the bound variable and its type in the env
  varC bv inh chn
    # (isTask, chn) = varIsTask bv.var_info_ptr chn
    | isTask    = ({syn_annot_expr = Var bv, syn_texpr = Just (TVar bv.var_ident.id_name)}, chn)
    | otherwise = ({syn_annot_expr = Var bv, syn_texpr = Just (TVar bv.var_ident.id_name)}, chn)

// TODO: We need to split this up: one part of this should generate the graph
// for the FunDef and the other part should generate the init and stop nodes.
// Yet another part should just get the right-hand side Expression of a FunDef
// so we can just cata it.
funToGraph :: FunDef *ModuleEnv *Heaps *PredefinedSymbols -> *(([(VariableName, TypeName)], Maybe TExpr, Maybe Expression), *ModuleEnv, *Heaps, *PredefinedSymbols)
funToGraph fd=:{fun_ident=fun_ident, fun_body = TransformedBody tb} menv heaps predef_symbols = mkBody
  where
  mkBody
    # inh        = mkInhExpr fun_ident.id_name
    # chn        = mkChnExpr predef_symbols menv heaps
    # (syn, chn) = exprCata mkGraphAlg tb.tb_rhs inh chn
    = ( (map (\(arg, ty) -> (arg.fv_ident.id_name, ppType ty)) (zip2 tb.tb_args (funArgTys fd)), syn.syn_texpr, Just syn.syn_annot_expr) //Just g, syn.syn_annot_expr)
      , chn.chn_module_env, chn.chn_heaps, chn.chn_predef_symbols)
funToGraph _ menv heaps predef_symbols = (([], Nothing, Nothing), menv, heaps, predef_symbols)
