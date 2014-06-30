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


/*
TODO:
GiN does not do eta-reduction. I.e., it only supports either a `f >>= \x -> e`
or `f >>| e` bind, but never a `f >>= g` bind. If we want to support the
latter, we must eta-expand `g`.
*/


edgeErr :: String (Maybe Int) Expression (Maybe Int) Expression *ChnExpression -> *(SynExpression, *ChnExpression)
edgeErr errmsg lid lexpr rid rexpr chn
  # (err1, chn) = nodeErr lid lexpr chn
  # (err2, chn) = nodeErr rid rexpr chn
  = abort ("Cannot create " +++ errmsg
           +++ " between left expression\n\t" +++ err1
           +++ " and right expression\n\t" +++ err2 +++ "\n")

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

sugarListCompr :: App *ModuleEnv -> *(GListComprehension, *ModuleEnv)
sugarListCompr app menv
  # ((_, xs), menv) = dropAppContexts app menv
  # gen             = last xs
  # (mfd, menv)     = reifyFunDef app.app_symb menv
  # funDef          = fromMaybe (abort $ "sugarListCompr: failed to find function definition for " +++ app.app_symb.symb_ident.id_name) mfd
  = case getFunRhs funDef of
      Case {Case | case_guards=(AlgebraicPatterns _
             [{AlgebraicPattern | ap_vars=[sel:_], ap_expr=(App {App | app_args=[expr:_]})}:_])}
               = mkLC sel expr gen menv
      Case {Case | case_guards=(AlgebraicPatterns _
             [{AlgebraicPattern | ap_vars=[sel:_], ap_expr=(Case _)}:_])}
               = abort "sugar Algebraic Case"
      Case {Case | case_guards=(BasicPatterns _ _)} = abort "sugar Basic"
      Case {Case | case_guards=(NewTypePatterns _ _)} = abort "sugar NewType"
      Case {Case | case_guards=(DynamicPatterns _)} = abort "sugar Dynamic"
      Case {Case | case_guards=(OverloadedListPatterns _ _ _)} = abort "sugar OverloadedList"
      Case {Case | case_guards=(NoPattern)} = abort "sugar NoPattern"
      _        = (err, menv)
  where
  err     = abort "Invalid list comprehension"
  mkLC sel expr gen menv
    # (od, menv)  = ppExpression expr menv
    # (gd, menv)  = ppExpression gen menv
    # (fvd, menv) = ppFreeVar sel menv
    = ({ GListComprehension
      | output = ppCompact od
      , guard = Nothing
      , comprElem = [{cePattern = ppCompact fvd, ceType = SeqComp /* TODO */, ceInput = ppCompact gd}]
       //selector = 
      //, input = GCleanExpression $ ppCompact gd
      }, menv)

  //{ GListComprehension
  //| output = GCleanExpression "output"
  //, guard = Nothing
  //, selector = "selector"
  //, input = GCleanExpression "input"
  //}

/*



*/

withTwo :: App [Expression] (Expression Expression *ChnExpression -> *(SynExpression, *ChnExpression)) InhExpression *ChnExpression -> *(SynExpression, *ChnExpression)
withTwo app [x1:x2:_] f inh chn = f x1 x2 chn
withTwo app _         _ inh chn = ({mkSynExpr & syn_annot_expr = Just (App app)}, chn)

annotExpr :: Int App (Maybe SymbIdent) (Maybe [Expression]) InhExpression *ChnExpression SynExpression -> *(SynExpression, *ChnExpression)
annotExpr nodeId app mbRepSI mbArgs inh chn syn
  # (tune_symb, predefs) = (chn.chn_predef_symbols)![PD_tonicTune]
  | predefIsUndefined tune_symb = (syn, {chn & chn_predef_symbols = predefs})
  | otherwise
      # (papp, menv) = isPartialApp app chn.chn_module_env
      # chn          = {chn & chn_module_env = menv, chn_predef_symbols = predefs}
      | papp         = (syn, chn)
      | otherwise
        # (app, chn) = mkTuneApp tune_symb chn
        = ({syn & syn_annot_expr = Just (App app)}, chn)
  where
  mkTuneApp tune_symb chn
    # (mod, menv) = (chn.chn_module_env)!me_icl_module
    = (appPredefinedSymbol "tonicTune" tune_symb
         [ mkStr mod.icl_name.id_name
         , mkStr inh.inh_curr_task_name
         , mkInt nodeId
         , App {app & app_symb = fromMaybe app.app_symb mbRepSI
                    , app_args = fromMaybe app.app_args mbArgs}
         ]
      , { chn & chn_module_env = menv})

mkTonicInfo :: String Int (Maybe String) InhExpression -> TonicInfo
mkTonicInfo modname nodeId mval inh =
  { tonicModuleName  = modname
  , tonicTaskName    = inh.inh_curr_task_name
  , tonicValAsStr    = mval
  , tonicNodeId      = nodeId
  }

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

import StdDebug

instance toString VarInfo where
  toString (VI_Empty) = "VI_Empty"
  toString (VI_Type _ _) = "VI_Type"
  toString (VI_FAType _ _ _) = "VI_FAType"
  toString (VI_FATypeC _ _ _ _) = "VI_FATypeC"
  toString (VI_FPC) = "VI_FPC"
  toString (VI_Occurrence _) = "VI_Occurrence"
  toString (VI_UsedVar _) = "VI_UsedVar"
  toString (VI_Expression _) = "VI_Expression"
  toString (VI_Variable _ _) = "VI_Variable"
  toString (VI_LiftedVariable _) = "VI_LiftedVariable"
  toString (VI_Count _ _) = "VI_Count"
  toString (VI_Ref _) = "VI_Ref"
  toString (VI_AccVar _ _) = "VI_AccVar"
  toString (VI_Alias _) = "VI_Alias"
  toString (VI_RefFromTupleSel0 _) = "VI_RefFromTupleSel0"
  toString (VI_RefFromArrayUpdate _ _) = "VI_RefFromArrayUpdate"
  toString (VI_RefFromArrayUpdateToTupleSelector2 _ _ _) = "VI_RefFromArrayUpdateToTupleSelector2"
  toString (VI_RefFromArrayUpdateOfTupleElem2 _ _) = "VI_RefFromArrayUpdateOfTupleElem2"
  toString (VI_FreeVar _ _ _ _) = "VI_FreeVar"
  toString (VI_BoundVar _) = "VI_BoundVar"
  toString (VI_LocalVar) = "VI_LocalVar"
  toString (VI_ClassVar _ _ _) = "VI_ClassVar"
  toString (VI_EmptyConstructorClassVar) = "VI_EmptyConstructorClassVar"
  toString (VI_ForwardClassVar _) = "VI_ForwardClassVar"
  toString (VI_Forward _) = "VI_Forward"
  toString (VI_LetVar _) = "VI_LetVar"
  toString (VI_LetExpression _) = "VI_LetExpression"
  toString (VI_CaseOrStrictLetVar _) = "VI_CaseOrStrictLetVar"
  toString (VI_StrictLetVar) = "VI_StrictLetVar"
  toString (VI_CorrespondenceNumber _) = "VI_CorrespondenceNumber"
  toString (VI_SequenceNumber _) = "VI_SequenceNumber"
  toString (VI_AliasSequenceNumber _) = "VI_AliasSequenceNumber"
  toString (VI_Used) = "VI_Used"
  toString (VI_PropagationType _) = "VI_PropagationType"
  toString (VI_ExpandedType _) = "VI_ExpandedType"
  toString (VI_Record _) = "VI_Record"
  toString (VI_Pattern _) = "VI_Pattern"
  toString (VI_TypeCodeVariable _) = "VI_TypeCodeVariable"
  toString (VI_DynamicValueAlias _) = "VI_DynamicValueAlias"
  toString (VI_Body _ _ _ _ _) = "VI_Body"
  toString (VI_ExpressionOrBody _ _ _ _ _ _) = "VI_ExpressionOrBody"
  toString (VI_Dictionary _ _ _) = "VI_Dictionary"
  toString (VI_Extended _ _) = "VI_Extended"
  toString (VI_CPSExprVar _) = "VI_CPSExprVar"
  toString (VI_Labelled_Empty _) = "VI_Labelled_Empty"
  toString (VI_LocalLetVar) = "VI_LocalLetVar"

varIsTask :: VarInfoPtr *ChnExpression -> *(Bool, *ChnExpression)
varIsTask varptr chn
  # heaps = chn.chn_heaps
  # (vi, var_heap) = readPtr varptr heaps.hp_var_heap
  # chn = {chn & chn_heaps = trace_n (toString vi) {heaps & hp_var_heap = var_heap}}
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
  =  {  mkExprAlg mkSynExpr
     &  app = appC, at = atC, letE = letC, caseE = caseC, var = varC
     //,  var                   = \bv             _ chn -> ({mkSynExpr & syn_annot_expr = Just (Var bv)}, chn)
     ,  selection             = \sk e ss        _ chn -> ({mkSynExpr & syn_annot_expr = Just (Selection sk e ss)},    chn)
     ,  update                = \e1 ss e2       _ chn -> ({mkSynExpr & syn_annot_expr = Just (Update e1 ss e2)},      chn)
     ,  recordUpdate          = \gd e bs        _ chn -> ({mkSynExpr & syn_annot_expr = Just (RecordUpdate gd e bs)}, chn)
     ,  tupleSelect           = \ds i e         _ chn -> ({mkSynExpr & syn_annot_expr = Just (TupleSelect ds i e)},   chn)
     ,  basicExpr             = \bv             _ chn -> ({mkSynExpr & syn_annot_expr = Just (BasicExpr bv)},  chn)
     ,  conditional           = \c              _ chn -> ({mkSynExpr & syn_annot_expr = Just (Conditional c)}, chn)
     ,  anyCodeExpr           = \cb cf ss       _ chn -> ({mkSynExpr & syn_annot_expr = Just (AnyCodeExpr cb cf ss)}, chn)
     ,  abcCodeExpr           = \ss b           _ chn -> ({mkSynExpr & syn_annot_expr = Just (ABCCodeExpr ss b)}, chn)
     ,  matchExpr             = \gd e           _ chn -> ({mkSynExpr & syn_annot_expr = Just (MatchExpr gd e)},   chn)
     ,  isConstructor         = \e gd n gi i p  _ chn -> ({mkSynExpr & syn_annot_expr = Just (IsConstructor e gd n gi i p)},  chn)
     ,  freeVar               = \v              _ chn -> ({mkSynExpr & syn_annot_expr = Just (FreeVar v)}, chn)
     ,  dictionariesFunction  = \xs e at        _ chn -> ({mkSynExpr & syn_annot_expr = Just (DictionariesFunction xs e at)}, chn)
     ,  constant              = \si i prio      _ chn -> ({mkSynExpr & syn_annot_expr = Just (Constant si i prio)},   chn)
     ,  classVariable         = \vip            _ chn -> ({mkSynExpr & syn_annot_expr = Just (ClassVariable vip)},    chn)
     ,  dynamicExpr           = \de             _ chn -> ({mkSynExpr & syn_annot_expr = Just (DynamicExpr de)},       chn)
     ,  typeCodeExpression    = \t              _ chn -> ({mkSynExpr & syn_annot_expr = Just (TypeCodeExpression t)}, chn)
     ,  typeSignature         = \f e            _ chn -> ({mkSynExpr & syn_annot_expr = Just (TypeSignature f e)},    chn)
     ,  ee                    = \               _ chn -> ({mkSynExpr & syn_annot_expr = Just EE},           chn)
     ,  noBind                = \eip            _ chn -> ({mkSynExpr & syn_annot_expr = Just (NoBind eip)}, chn)
     ,  failExpr              = \i              _ chn -> ({mkSynExpr & syn_annot_expr = Just (FailExpr i)}, chn)
     }
  where
  appC app inh chn // TODO Take arity into account: if a task is partially applied, wrap it in a lambda and annotate that
    # (idIsTask, menv) = symbIdentIsTask app.app_symb chn.chn_module_env
    # chn = {chn & chn_module_env = menv}
    | idIsTask
      # ((ctxs, args), menv)  = dropAppContexts app chn.chn_module_env
      # chn                   = { chn & chn_module_env = menv }
      = case appFunName app of // TODO `parallel`
          ">>="       -> mkBind       app ctxs args              inh chn
          "return"    -> mkReturn     app ctxs args              inh chn
          ">>|"       -> mkBindNoLam  app ctxs args              inh chn
          "@:"        -> mkAssign     app ctxs args              inh chn
          ">>*"       -> mkStep       app ctxs args              inh chn
          "-||-"      -> mkParBinApp  app ctxs args DisFirstBin  inh chn
          "||-"       -> mkParBinApp  app ctxs args DisRight     inh chn
          "-||"       -> mkParBinApp  app ctxs args DisLeft      inh chn
          "-&&-"      -> mkParBinApp  app ctxs args ConPair      inh chn
          "anyTask"   -> mkParListApp app ctxs args DisFirstList inh chn
          "allTasks"  -> mkParListApp app ctxs args ConAll       inh chn
          _           -> mkTaskApp    app ctxs args              inh chn
    | otherwise
        # (nid, g) = addNode (mkGNode GArbitraryExpression) chn.chn_graph
        = ({mkSingleIdSynExpr (Just nid) & syn_annot_expr = Just (App app)}, {chn & chn_graph = g})
    where
    mkBindNoLam app ctxs args inh chn
      = withTwo app args f inh chn
      where
      f lhsExpr rhsExpr chn // TODO We probably need a two-pass scheme to properly deal with replacing variables in the graph, since we need both the successor and predecessor ID
        # (synl, chnl)  = exprCata mkGraphAlg lhsExpr inh chn
        # (synr, chnr)  = exprCata mkGraphAlg rhsExpr inh chnl
        = case (synl.syn_node_id, synr.syn_node_id) of
            (Just lx, Just rn)
              # g    = addEdge emptyEdge (lx, rn) chnr.chn_graph
              # app` = case (synl.syn_annot_expr, synr.syn_annot_expr) of
                         (Just la, Just ra) -> { app & app_args = ctxs ++ [la, ra]}
                         (Just la, _)       -> { app & app_args = ctxs ++ [la, rhsExpr]}
                         _                  -> app
              = ({mkSingleIdSynExpr synl.syn_node_id & syn_annot_expr = Just (App app`)}, chnr)
            (lid, rid)
              = edgeErr "bind edge (>>|)" lid lhsExpr rid rhsExpr chnr

    // TODO Combine the nolam and lam cases? They are very similar...
    // when the RHS is not a lambda, it is simply the nolam case
    mkBind app ctxs args inh chn
      = withTwo app args f inh chn
      where
      f lhsExpr rhsExpr chn
        # (synl, chnl)    = exprCata mkGraphAlg lhsExpr inh chn
        # ((synr, chnr), edge)
            = case (exprIsLambda rhsExpr, rhsExpr) of
                (True, App rhsApp)
                  # (mfd, menv)    = reifyFunDef rhsApp.app_symb chnl.chn_module_env
                  # (rSym, menv)   = ppSymbIdent rhsApp.app_symb menv
                  # (mRhsTy, menv) = reifySymbIdentSymbolType rhsApp.app_symb menv
                  # rhsfd          = fromMaybe (abort $ "mkBind: failed to find function definition for " +++ ppCompact rSym) mfd
                  # args           = getFunArgs rhsfd
                  # rhsTy          = fromMaybe (abort "mkBind: failed to reify SymbolType") mRhsTy
                  # funArgs        = snd $ dropContexts rhsTy args
                  # patid          = lastElem [freeVarName x \\ x <- funArgs| x.fv_def_level == -1]
                  # (syne, chn)    = exprCata mkGraphAlg (getFunRhs rhsfd) inh { chnl & chn_module_env = menv }
                  # menv           = updateWithAnnot rhsApp.app_symb syne.syn_annot_expr chn.chn_module_env
                  = (({syne & syn_annot_expr = Nothing}, {chn & chn_module_env = menv}), mkEdge patid)
                _ = (exprCata mkGraphAlg rhsExpr inh chnl, emptyEdge)
        = case (synl.syn_node_id, synr.syn_node_id) of
            (Just lx, Just rn)
              # g                    = addEdge edge (lx, rn) chnr.chn_graph
              # chnr                 = {chnr & chn_graph = g}
              # (mod, menv)          = (chnr.chn_module_env)!me_icl_module
              # chnr                 = {chnr & chn_module_env = menv}
              # (bind_symb, predefs) = (chnr.chn_predef_symbols)![PD_tonicBind]
              # chnr                 = {chnr & chn_predef_symbols = predefs}
              # bs                   = mkPredefSymbIdent "tonicBind" bind_symb
              # pref                 = [ mkStr mod.icl_name.id_name, mkStr inh.inh_curr_task_name
                                       , mkInt lx, mkInt rn
                                       ]
              # app`                 = case (synl.syn_annot_expr, synr.syn_annot_expr) of
                                         (Just la, Just ra) -> { app & app_symb = bs, app_args = ctxs ++ pref ++ [la, ra] }
                                         (Just la, _)       -> { app & app_symb = bs, app_args = ctxs ++ pref ++ [la, rhsExpr] }
                                         _                  -> app
              = ({mkSingleIdSynExpr synl.syn_node_id & syn_annot_expr = Just (App app`)}, chnr)
            (lid, rid)
              = edgeErr "bind edge (>>=)" lid lhsExpr rid rhsExpr chnr

    mkReturn app ctxs args inh chn
      # (mn, chn)  = getModuleName chn
      # (ppd, chn) = case args of
                       [x:_] -> mkRet x chn
                       _     -> (ArbitraryOrUnknownExpr, chn)
      # (n, g)     = addNodeWithIndex (\ni -> { GNode
                                              | nodeType      = GReturn ppd
                                              , nodeTonicInfo = Just $ mkTonicInfo mn ni Nothing inh
                                              }) chn.chn_graph
      = ({mkSingleIdSynExpr (Just n) & syn_annot_expr = Just (App app)}, {chn & chn_graph = g})
      where
      // In case of a function application, we want to inspect the type of the
      // function. If it is a task or a list, treat it differently than any
      // other type.
      mkRet (BasicExpr bv) chn
        # (bvd, menv) = ppBasicValue bv chn.chn_module_env
        = (VarOrExpr (ppCompact bvd), {chn & chn_module_env = menv})
      mkRet (Var bv)       chn = (VarOrExpr bv.var_ident.id_name, chn)
      mkRet e              chn
        | False /* TODO Check if e is Task */ = (Subgraph undef, chn)
        | otherwise
            = (ArbitraryOrUnknownExpr, chn)

    // TODO Delimit assigned task somehow. Subgraph?
    mkAssign app ctxs args inh chn
      = withTwo app args f inh chn
      where
      f u t chn
        # (syn, chn)  = exprCata mkGraphAlg t inh chn
        # (ud, menv)  = ppExpression u chn.chn_module_env
        # chn         = {chn & chn_module_env = menv}
        # (lid, g)    = addNode (mkGNode (GAssign (ppCompact ud))) chn.chn_graph
        # chn         = {chn & chn_graph = g}
        //# (syn, chn)  = exprCata mkGraphAlg t inh {chn & chn_graph = g, chn_module_env = menv}
        = case syn.syn_node_id of
            Just r
              # g = addEmptyEdge (r, lid) chn.chn_graph
              = annotExpr r app Nothing Nothing inh {chn & chn_graph = g} syn
            _ = edgeErr "assign edge" (Just lid) u Nothing t chn

    // TODO : Implement this correctly
    mkStep app ctxs args inh chn
      = withTwo app args f inh chn
      where
      f l r chn
        = case r of
            (arg=:(App app))
              | exprIsListConstr arg
                  # exprs          = listExprToList arg
                  # (aes, gs, chn) = let f e=:(App app`=:{app_args=[App app``:contExpr]}) (xs, gs, chn)
                                           | app`.app_symb.symb_ident.id_name == "OnAction"
                                           # action = extractAction app``
                                           // TODO do not recurse on e, but on the inner expression
                                           # (syn, chn`) = exprCata mkGraphAlg e inh {chn & chn_graph = emptyGraphWithLastId (getLastId chn.chn_graph)}
                                           # aes         = case syn.syn_annot_expr of
                                                             Just ae -> [ae:xs]
                                                             _       -> xs
                                           = (aes, [ArbitraryOrUnknownExpr:gs], {chn` & chn_graph = setLastId chn.chn_graph (getLastId chn`.chn_graph)})
                                           | app`.app_symb.symb_ident.id_name == "OnValue"
                                           // TODO : Implement
                                           = (xs , gs, chn)
                                           | app`.app_symb.symb_ident.id_name == "OnException"
                                           // TODO : Implement
                                           = (xs , gs, chn)
                                         f _ (xs, gs, chn) = (xs, gs, chn)
                                     in  foldr f ([], [], chn) exprs
                  # (pid, g)       = addNode (mkGNode (GStep (map (\g` -> StepElem (StepOnValue {stepContFilter = StepAlways, stepContLbl = Nothing, stepContNode = GArbitraryExpression /* TODO */})) gs))) chn.chn_graph
                  = annotExpr pid app Nothing (Just exprs) inh {chn & chn_graph = g} (mkSingleIdSynExpr (Just pid))
              | otherwise
                  # (n, g) = addNode (mkGNode (GStep [])) chn.chn_graph // TODO
                  = (mkSingleIdSynExpr (Just n), {chn & chn_graph = g})
                  // TODO
            //(vararg=:(Var bv))
              //# (syn, chn)  = exprCata mkGraphAlg vararg inh chn
              //# nid         = fromMaybe -1 syn.syn_node_id
              //# (mod, menv) = (chn.chn_module_env)!me_icl_module
              //# chn         = {chn & chn_module_env = menv}
              //= annotExpr nid app Nothing (Just (App app)) inh chn (mkSingleIdSynExpr (Just nid))
            _ = ({mkSynExpr & syn_annot_expr = Just (App app)}, chn)
      extractAction app=:{app_args=[BasicExpr (BVS str):_]}
        | app.app_symb.symb_ident.id_name == "Action" = str
      extractAction _ = "(no action)"




        //# (synl, chnl) = exprCata mkGraphAlg l inh chn
        //// The second argument to step can be any list; a hardcoded list, a list comprehension, a reference to a list constant or a list function, you name it....
        //// For example, in the case of a list comprehension, would we generate subgraphs in the comprehsion body?
        //// If it is a function/constant, we should reify it and inline it
        //# (synr, chnr) = exprCata mkGraphAlg r inh chnl // TODO: This needs heavy work; is completely wrong, copied from mkbinapp
        //= case (synl.syn_node_id, synr.syn_node_id) of
            //(Just l, Just r)
              //# g = addEdge emptyEdge (l, r) chnr.chn_graph
              //= annotExpr l app Nothing Nothing inh { chnr & chn_graph = g} synr
            //(lid, rid)
              //= edgeErr "step edge" lid l rid r chnr
        //// TODO : If there are no two elems in the list, the expr is eta-reduced, so we need to pprint it instead of throwing an error

    mkTaskApp app ctxs args inh chn
      # (mn, chn)  = getModuleName chn
      # (ps, menv) = mapSt ppExpression args chn.chn_module_env
      //# menv       = trace_n ("\nmkTaskApp trace:\n" +++ foldr (\x xs -> ppCompact x +++ xs) "" ps +++ "\n") menv
      # chn        = {chn & chn_module_env = menv}
      # appArgs    = map ppCompact ps  // TODO: When do we pprint a Clean expr? And when do we generate a subgraph?
      # (an, g)    = addNodeWithIndex (\ni -> { GNode
                                              | nodeType      = GTaskApp (appFunName app) appArgs
                                              , nodeTonicInfo = Just $ mkTonicInfo mn ni Nothing inh
                                              }) chn.chn_graph
      = annotExpr an app Nothing Nothing inh { chn & chn_graph = g } (mkSingleIdSynExpr (Just an))

    mkParBinApp app ctxs args join inh chn
      = withTwo app args f inh chn
      where
      f l r chn
        # (synr, chnr) = exprCata mkGraphAlg r inh {chn & chn_graph = emptyGraphWithLastId (getLastId chn.chn_graph)}
        # g            = addStartStop synr.syn_node_id chnr.chn_graph
        # (synl, chnl) = exprCata mkGraphAlg l inh {chnr & chn_graph = emptyGraphWithLastId (getLastId chnr.chn_graph)}
        # g            = addStartStop synl.syn_node_id chnl.chn_graph
        # (pid, g)     = addNode (mkGNode (GParallel join [Subgraph chnl.chn_graph, Subgraph chnr.chn_graph])) (setLastId chn.chn_graph (getLastId chnl.chn_graph))
        = case (synl.syn_node_id, synr.syn_node_id) of
            (Just _, Just _)
              = annotExpr pid app Nothing Nothing inh { chnl & chn_graph = g} (mkSingleIdSynExpr (Just pid))
            (lid, rid)
              = edgeErr "bin app edge" lid l rid r chnl
        // TODO : If there are no two elems in the list, the expr is eta-reduced, so we need to pprint it instead of throwing an error

    // TODO : Can be eta-reduced
    // TODO : In the case where we have
    //    anyTask [someTask, otherTask]
    // we just split, have two nodes someTask and otherTask, then a merge again.
    // Only when the list anyTask is applied to is a list comprehension we generate
    // a more detailed graph with content. Only in that case, there is just one
    // new node (and not even a chain of nodes). We know exactly how many nodes
    // we will get and can therefore link to the join node
    mkParListApp app ctxs args join inh chn
      = case args of
          [arg=:(App app):_]
            | exprIsListConstr arg
                # exprs          = listExprToList arg
                # (aes, gs, chn) = let f e (xs, gs, chn)
                                         # (syn, chn`) = exprCata mkGraphAlg e inh {chn & chn_graph = emptyGraphWithLastId (getLastId chn.chn_graph)}
                                         # g           = addStartStop syn.syn_node_id chn`.chn_graph
                                         # aes         = case syn.syn_annot_expr of
                                                           Just ae -> [ae:xs]
                                                           _       -> xs
                                         = (aes, [Subgraph chn`.chn_graph /* TODO g */:gs], {chn` & chn_graph = setLastId chn.chn_graph (getLastId chn`.chn_graph)})
                                    in  foldr f ([], [], chn) exprs
                # (pid, g)       = addNode (mkGNode (GParallel join gs)) chn.chn_graph
                = annotExpr pid app Nothing (Just exprs) inh {chn & chn_graph = g} (mkSingleIdSynExpr (Just pid))
            | otherwise
                # (n, g) = addNode (mkGNode (GParallel join [ArbitraryOrUnknownExpr])) chn.chn_graph
                = (mkSingleIdSynExpr (Just n), {chn & chn_graph = g})
            //| isListCompr app.app_symb.symb_ident.id_name
                //# (lc, menv) = sugarListCompr app chn.chn_module_env
                //# (nid, g)   = addNode (mkGNode (GListComprehension lc)) (emptyGraphWithLastId (getLastId chn.chn_graph))
                //# (pid, g)   = addNode (mkGNode (GParallel join [Subgraph g])) chn.chn_graph
                //= annotExpr pid app Nothing Nothing inh {chn & chn_graph = g, chn_module_env = menv} (mkSingleIdSynExpr (Just pid))
          [vararg=:(Var bv):as] // TODO test
            # (syn, chn)  = exprCata mkGraphAlg vararg inh chn
            # nid         = fromMaybe -1 syn.syn_node_id
            # (mod, menv) = (chn.chn_module_env)!me_icl_module
            # chn         = {chn & chn_module_env = menv}
            # (tonicVarToListOfTask_symb, predefs) = (chn.chn_predef_symbols)![PD_tonicVarToListOfTask]
            # tatSI = mkPredefSymbIdent "tonicVarToListOfTask" tonicVarToListOfTask_symb
            = annotExpr nid app Nothing (Just (ctxs ++ [App (appPredefinedSymbol "tonicVarToListOfTask" tonicVarToListOfTask_symb [mkStr mod.icl_name.id_name, mkStr inh.inh_curr_task_name, mkInt nid, vararg])])) inh {chn & chn_predef_symbols = predefs} (mkSingleIdSynExpr (Just nid))
          _ = ({mkSynExpr & syn_annot_expr = Just (App app)}, chn)

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
        # (lid, g)      = addNode (mkGNode (GLet {GLet | glet_binds = binds})) chn.chn_graph
        # (syne, chn)   = exprCata mkGraphAlg (getFunRhs fd) inh { chn & chn_graph = g }
        # g             = case syne.syn_node_id of
                            Just eid -> addEmptyEdge (lid, eid) chn.chn_graph
                            _        -> chn.chn_graph
        # menv          = updateWithAnnot app.app_symb syne.syn_annot_expr chn.chn_module_env
        # chn           = { chn & chn_module_env = menv, chn_graph = g }
        = ({mkSingleIdSynExpr (Just lid) & syn_annot_expr = Just (e @ es)}, chn)
    | otherwise    =  abort "atC: otherwise case" // TODO : pretty print function application
    where
      zwf eVar eVal menv
        # (fvl, menv) = ppFreeVar eVar menv
        # (fvr, menv) = ppExpression eVal menv
        = ((ppCompact fvl, ppCompact fvr), menv)

  atC e es _ chn = ({mkSynExpr & syn_annot_expr = Just (e @ es)}, chn)
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
      # l          = case syn.syn_annot_expr of
                       Just ae -> {lt & let_expr = ae}
                       _       -> lt
      = ({syn & syn_annot_expr = Just (Let l)}, chn)
    mkLet Nothing lt inh chn
      # (binds, menv) = mkGLetBinds lt chn.chn_module_env
      # (lid, g)      = addNode (mkGNode (GLet {GLet | glet_binds = binds})) chn.chn_graph
      // TODO : Represent the bindings in any way possible, not just PP
      # (syn, chn)    = exprCata mkGraphAlg lt.let_expr inh {chn & chn_graph = g, chn_module_env = menv}
      = case syn.syn_node_id of
          Just n
            # g = addEmptyEdge (lid, n) chn.chn_graph
            # l = case syn.syn_annot_expr of
                    Just ae -> {lt & let_expr = ae}
                    _       -> lt
            = ({syn & syn_annot_expr = Just (Let l)}, {chn & chn_graph = g})
          _ = abort "Failed to add let edge; no synthesized ID from let body"

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
    # (ni, g)       = addNode (mkGNode (GDecision CaseDecision (ppCompact ed))) chn.chn_graph
    # (guards, chn) = mkAlts ni cs.case_guards {chn & chn_module_env = menv, chn_graph = g}
    # (def, chn)    = case cs.case_default of
                        Yes def
                          # (syn, chn) = mkAlts` ni ('PPrint'.text "_") def chn
                          = case syn.syn_annot_expr of
                              Just e -> (Yes e, chn)
                              _      -> (No, chn)
                        _ = (No, chn)
    # cs`           = {cs & case_default = def, case_guards = guards}
    = ({mkSingleIdSynExpr (Just ni) & syn_annot_expr = Just (Case cs`)}, chn)
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
          # (syn, chn)  = mkAlts` ni apd ap.ap_expr chn
          # ap          = case syn.syn_annot_expr of
                            Just e -> {ap & ap_expr = e}
                            _      -> ap
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
          # bp          = case syn.syn_annot_expr of
                            Just e -> {bp & bp_expr = e}
                            _      -> bp
          = ([bp:bps], chn)
    mkAlts ni c chn = (c, chn)

    mkAlts` :: Int Doc Expression ChnExpression -> (SynExpression, ChnExpression)
    mkAlts` ni lblDoc expr chn
      # (syn, chn) = exprCata mkGraphAlg expr inh chn
      # menv       = chn.chn_module_env
      # (d, menv)  = ppExpression expr menv
      # chn        = {chn & chn_module_env = menv}
      # g          = addEdge (mkEdge (ppCompact lblDoc)) (ni, fromMaybe (trace_n (ppCompact d) abort "Failed to add edge from decision node to branch") syn.syn_node_id) chn.chn_graph
      = (syn, {chn & chn_graph = g})

  // TODO Determine whether it's a Task a or [Task a]
  // We can do so by maintaining an environment. At lets and lambdas, store the bound variable and its type in the env
  varC bv inh chn
    # (isTask, chn) = varIsTask bv.var_info_ptr chn
    # (mn, chn)     = getModuleName chn
    # (nid, g)      = addNodeWithIndex (\ni -> { GNode
                                               | nodeType      = GVar bv.var_ident.id_name
                                               , nodeTonicInfo = Just $ mkTonicInfo mn ni Nothing inh
                                               }) chn.chn_graph
    # syn           = mkSingleIdSynExpr (Just nid)
    # chn           = {chn & chn_graph = g}
    = case isTask of
        True
          # (tonicVarToSingleTask_symb, predefs) = (chn.chn_predef_symbols)![PD_tonicVarToSingleTask]
          # chn         = {chn & chn_predef_symbols = predefs}
          # tatSI       = mkPredefSymbIdent "tonicVarToSingleTask" tonicVarToSingleTask_symb
          # (mod, menv) = (chn.chn_module_env)!me_icl_module
          # chn         = {chn & chn_module_env = menv}
          # varexpr     = App (appPredefinedSymbol "tonicVarToSingleTask" tonicVarToSingleTask_symb [mkStr mod.icl_name.id_name, mkStr inh.inh_curr_task_name, mkInt nid, Var bv])
          = ({syn & syn_annot_expr = Just varexpr}, chn)
        _ = (syn, chn)

/*

a >>| b >>| c

==

(>>|) ((>>|) a b) c

==

(>>|)
  ((>>|)
    a
    b)
  c

~

a -- b -- c

b: pred a, succ c

*/

nodeErr :: (Maybe Int) Expression *ChnExpression -> *(String, *ChnExpression)
nodeErr mn expr chn
  # (doc, menv) = ppExpression expr chn.chn_module_env
  # chn = { chn & chn_module_env = menv}
  = (ppCompact doc +++ "\n" +++
    (maybe "for which its ID is unknown" (\n -> "with node ID " +++ toString n) mn)
    , chn)

addEmptyEdge :: (Int,Int) u:GinGraph -> v:GinGraph, [u <= v]
addEmptyEdge e g = addEdge emptyEdge e g

addNode` :: GNode Expression *ChnExpression -> *(SynExpression, *ChnExpression)
addNode` node annot chn
  # (n, g) = addNode node chn.chn_graph
  = (mkSingleIdSynExpr (Just n), { chn & chn_graph = g })

// TODO: We need to split this up: one part of this should generate the graph
// for the FunDef and the other part should generate the init and stop nodes.
// Yet another part should just get the right-hand side Expression of a FunDef
// so we can just cata it.
funToGraph :: FunDef *ModuleEnv *Heaps *PredefinedSymbols -> *(([String], Maybe GinGraph, Maybe Expression), *ModuleEnv, *Heaps, *PredefinedSymbols)
funToGraph fd=:{fun_ident=fun_ident, fun_body = TransformedBody tb} menv heaps predef_symbols = mkBody
  where
  mkBody
    # inh        = mkInhExpr fun_ident.id_name
    # chn        = mkChnExpr emptyGraph predef_symbols menv heaps
    # (syn, chn) = exprCata mkGraphAlg tb.tb_rhs inh chn
    # g          = addStartStop syn.syn_node_id chn.chn_graph
    = ( (map (\x -> x.fv_ident.id_name) tb.tb_args, Just g, syn.syn_annot_expr)
      , chn.chn_module_env, chn.chn_heaps, chn.chn_predef_symbols)
funToGraph _ menv heaps predef_symbols = (([], Nothing, Nothing), menv, heaps, predef_symbols)

addStartStop eid g
  # (initId, g)  = addNode (mkGNode GInit) g
  # g            = maybe g (\firstId -> addEmptyEdge (initId, firstId) g) eid
  # leafs        = leafNodes g
  # (stopId, g)  = addNode (mkGNode GStop) g
  = foldr (\nid g_ -> addEmptyEdge (nid, stopId) g_) g leafs

instance toString GNode where
	toString n = toString n.nodeType

instance toString GNodeType where
  toString GInit = "GInit"
  toString GStop = "GStop"
  toString (GDecision _ _) = "GDecision"
  toString (GLet _) = "GLet"
  //toString GParallelSplit = "GParallelSplit"
  //toString (GParallelJoin _) = "GParallelJoin"
  toString (GTaskApp _ _) = "GTaskApp"
  toString (GReturn _) = "GReturn"
  toString (GAssign _) = "GAssign"
  toString (GStep _) = "GStep"
  //toString (GListComprehension _) = "GListComprehension"
  toString (GVar _) = "GVar"

