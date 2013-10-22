implementation module Tonic.GraphGen

// Task Oriented Notation Illustrated on a Canvas

//import syntax, checksupport, StdFile
//from CoclSystemDependent import DirectorySeparator, ensureCleanSystemFilesExists

import syntax, predef

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

//import Tonic.Tonic

import StdMisc
import StdDebug

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

sugarListCompr :: App *ModuleEnv -> *(GListComprehension, *ModuleEnv)
sugarListCompr app menv
  # ((_, xs), menv) = dropAppContexts app menv
  # gen             = last xs
  # (mfd, menv)     = reifyFunDef app.app_symb.symb_ident.id_name menv
  # (fidx, funDef)  = fromMaybe (abort $ "sugarListCompr: failed to find function definition for " +++ app.app_symb.symb_ident.id_name) mfd
  = case getFunRhs funDef of
      Case {Case | case_guards=(AlgebraicPatterns _
             [{AlgebraicPattern | ap_vars=[sel:_], ap_expr=(App {App | app_args=[expr:_]})}:_])}
               = mkLC sel expr gen menv
      _        = (err, menv)
  where
  err     = abort "Invalid list comprehension"
  mkLC sel expr gen menv
    # (od, menv)  = ppDebugExpression expr menv
    # (gd, menv)  = ppDebugExpression gen menv
    # (fvd, menv) = ppFreeVar sel menv
    = ({ GListComprehension
      | output = GCleanExpression $ ppCompact od
      , guard = Nothing
      , selector = ppCompact fvd
      , input = GCleanExpression $ ppCompact gd
      }, menv)

  //{ GListComprehension
  //| output = GCleanExpression "output"
  //, guard = Nothing
  //, selector = "selector"
  //, input = GCleanExpression "input"
  //}

class MkNode e where
  mkNode :: e GNodeType -> GNode

instance MkNode App where
  mkNode app nt = {GNode|nodeType = nt}

instance MkNode Let where
  mkNode lt nt = {GNode|nodeType = nt}

withTwo :: App [Expression] (Expression Expression *ChnExpression -> *(SynExpression, *ChnExpression)) InhExpression *ChnExpression -> *(SynExpression, *ChnExpression)
withTwo app [x1:x2:_] f inh chn = f x1 x2 chn
withTwo app _         _ inh chn = annotExpr (App app) inh chn mkSynExpr

annotExpr :: Expression InhExpression *ChnExpression SynExpression -> *(SynExpression, *ChnExpression)
annotExpr expr inh chn syn
  | inh.inh_tune_symb.pds_def == NoIndex || inh.inh_tune_symb.pds_module == NoIndex = (syn, chn)
  | otherwise
      # (app, chn) = mkTuneApp chn
      = ({syn & syn_annot_expr = Just (App app)}, chn)
  where
  mkTuneApp chn
    # [uid:uids]  = chn.chn_uniqs
    # (mod, menv) = (chn.chn_module_env)!me_icl_module
    = ({ App
       | app_symb = { SymbIdent
                    | symb_ident = { Ident
                                   | id_name = "tonicTune"
                                   , id_info = nilPtr}
                    , symb_kind  = SK_Function
                                     { Global
                                     | glob_object = inh.inh_tune_symb.pds_def
                                     , glob_module = inh.inh_tune_symb.pds_module}}
       , app_args = [ mkStr mod.icl_name.id_name
                    , mkStr inh.inh_curr_task_name
                    , mkInt uid
                    , expr]
       , app_info_ptr = nilPtr}
      , { chn & chn_module_env = menv, chn_uniqs = uids })
  mkStr str = BasicExpr (BVS ("\"" +++ str +++ "\""))
  mkInt i   = BasicExpr (BVInt i)

mkGraphAlg :: *(ExpressionAlg InhExpression *ChnExpression SynExpression)
mkGraphAlg
  =  {  mkExprAlg mkSynExpr
     &  app = appC, at = atC, letE = letC,  caseE = caseC, conditional = condC
     }
  where
  appC app inh chn
    # (idIsTask, menv) = identIsTask app.app_symb.symb_ident.id_name chn.chn_module_env
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
    | isListCompr app.app_symb.symb_ident.id_name
        # (lco, menv) = sugarListCompr app chn.chn_module_env
        = addNode` (mkNode app (GListComprehension lco)) (App app) { chn & chn_module_env = menv }
    | otherwise = annotExpr (App app) inh chn mkSynExpr
    where
    mkBindNoLam app ctxs args inh chn
      = withTwo app args f inh chn
      where
      f lhsExpr rhsExpr chn
        # (synl, chnl)  = exprCata mkGraphAlg lhsExpr inh chn
        # (synr, chnr)  = exprCata mkGraphAlg rhsExpr inh chnl
        = case (synl.syn_entry_id, synl.syn_exit_id, synr.syn_entry_id, synr.syn_exit_id) of
            (Just _, Just lx, Just rn, Just _)
              # g = addEdge emptyEdge (lx, rn) chnr.chn_graph
              = annotExpr (App app) inh { chnr & chn_graph = g } (mkSingleIdSynExpr synl.syn_entry_id)
            (_, lid, rid, _)
              = edgeErr "bind edge" lid lhsExpr rid rhsExpr chnr

    mkBind app ctxs args inh chn
      = withTwo app args f inh chn
      where
      f lhsExpr rhsExpr chn
        # (synl, chnl)    = exprCata mkGraphAlg lhsExpr inh chn
        # ((synr, chnr), edge)
            = case (exprIsLambda rhsExpr, rhsExpr) of
                (True, App rhsApp)
                  # (mfd, menv)   = reifyFunDef rhsApp.app_symb.symb_ident.id_name chnl.chn_module_env
                  # (rSym, menv)  = ppSymbIdent rhsApp.app_symb menv
                  # (fidx, rhsfd) = fromMaybe (abort $ "mkGraphAlg #1: failed to find function definition for " +++ ppCompact rSym) mfd
                  # (mst, menv)   = reifySymbolType rhsApp.app_symb.symb_ident.id_name menv
                  # rhsTy         = fromMaybe (abort $ "mkGraphAlg #2: failed to find symbol type for " +++ ppCompact rSym) mst
                  # patid         = case [x \\ x <- snd $ dropContexts rhsTy (getFunArgs rhsfd) | x.fv_def_level == -1] of
                                      [x:_] -> freeVarName x
                                      _     -> abort "Invalid bind"
                  # synchn        = exprCata mkGraphAlg (getFunRhs rhsfd) inh { chnl & chn_module_env = menv }
                  = (updateWithAnnot fidx synchn, mkEdge patid)
                _ = (exprCata mkGraphAlg rhsExpr inh chnl, emptyEdge)
        = case (synl.syn_entry_id, synl.syn_exit_id, synr.syn_entry_id, synr.syn_exit_id) of
            (Just _, Just lx, Just rn, Just _)
              # g    = addEdge edge (lx, rn) chnr.chn_graph
              # app` = case (synl.syn_annot_expr, synr.syn_annot_expr) of
                         (Just la, Just ra) -> { app & app_args = ctxs ++ [la, ra] }
                         _                  -> app
              = annotExpr (App app`) inh { chnr & chn_graph = g } (mkSingleIdSynExpr synl.syn_entry_id)
            (_, lid, rid, _)
              = edgeErr "bind edge" lid lhsExpr rid rhsExpr chnr

    mkReturn app ctxs args inh chn
      # (ppd, chn) = case args of
                       [x:_] -> mkRet x chn
                       _     -> (GCleanExpression "", chn)
      # (n, g)     = addNode (mkNode app (GReturn ppd)) chn.chn_graph
      = annotExpr (App app) inh {chn & chn_graph = g} (mkSingleIdSynExpr (Just n))
      where
      // In case of a function application, we want to inspect the type of the
      // function. If it is a task or a list, treat it differently than any
      // other type.
      mkRet (BasicExpr bv) chn
        # (bvd, menv) = ppBasicValue bv chn.chn_module_env
        = (GCleanExpression $ ppCompact bvd, {chn & chn_module_env = menv})
      mkRet (Var bv)       chn = (GCleanExpression bv.var_ident.id_name, chn)
      mkRet e              chn
        # (d, menv) = ppExpression e chn.chn_module_env
        = (GCleanExpression $ ppCompact d, {chn & chn_module_env = menv})
         //# chn = exprCata mkGraphAlg e chn
         //= (GGraphExpression (GGraph chn.chn_graph), chn)

    mkAssign app ctxs args inh chn
      = withTwo app args f inh chn
      where
      f u t chn
         # (ud, menv)  = ppDebugExpression u chn.chn_module_env
         # (lid, g)    = addNode (mkNode app (GAssign (ppCompact ud))) chn.chn_graph
         # (syn, chn)  = exprCata mkGraphAlg t inh {chn & chn_graph = g, chn_module_env = menv}
         = case syn.syn_entry_id of
             Just r
               # g = addEmptyEdge (lid, r) chn.chn_graph
               = annotExpr (App app) inh {chn & chn_graph = g} syn
             _ = edgeErr "assign edge" (Just lid) u Nothing t chn

    mkStep app ctxs args inh chn
      = withTwo app args f inh chn
      where
      f l r chn
        # (synl, chnl) = exprCata mkGraphAlg l inh chn
        // The second argument to step can be any list; a hardcoded list, a list comprehension, a reference to a list constant or a list function, you name it....
        // For example, in the case of a list comprehension, would we generate subgraphs in the comprehsion body?
        // If it is a function/constant, we should reify it and inline it
        # (synr, chnr) = exprCata mkGraphAlg r inh chnl // TODO: This needs heavy work; is completely wrong, copied from mkbinapp
        = case (synl.syn_entry_id, synr.syn_entry_id) of
            (Just l, Just r)
              # g = addEdge emptyEdge (l, r) chnr.chn_graph
              = annotExpr (App app) inh { chnr & chn_graph = g} synr
            (lid, rid)
              = edgeErr "step edge" lid l rid r chnr
        // TODO: If there are no two elems in the list, the expr is eta-reduced, so we need to pprint it instead of throwing an error

    mkTaskApp app ctxs args inh chn
      # (ps, menv) = mapSt ppDebugExpression args chn.chn_module_env
      # chn        = {chn & chn_module_env = menv}
      # appArgs    = map (GCleanExpression o ppCompact) ps  // TODO: When do we pprint a Clean expr? And when do we generate a subgraph?
      # (an, g)    = addNode (mkNode app ((GTaskApp (appFunName app)) appArgs)) chn.chn_graph
      = annotExpr (App app) inh { chn & chn_graph = g } (mkSingleIdSynExpr (Just an))

    mkBinApp app ctxs args pat inh chn
      = withTwo app args f inh chn
      where
      f l r chn
        # (synl, chnl) = exprCata mkGraphAlg l inh chn
        # (synr, chnr) = exprCata mkGraphAlg r inh chnl
        = case (synl.syn_entry_id, synr.syn_entry_id) of
            (Just l, Just r)
              # g = addEdge (maybe emptyEdge mkEdge pat) (l, r) chnr.chn_graph
              = annotExpr (App app) inh { chnr & chn_graph = g } synr
            (lid, rid)
              = edgeErr "bin app edge" lid l rid r chnr
        // TODO: If there are no two elems in the list, the expr is eta-reduced, so we need to pprint it instead of throwing an error

    mkParBinApp app ctxs args join inh chn
      = withTwo app args f inh chn
      where
      f l r chn
        # (sid, g)      = addNode (mkNode app GParallelSplit) chn.chn_graph
        # (jid, g)      = addNode (mkNode app (GParallelJoin join)) g
        # (synl, chnl)  = exprCata mkGraphAlg l inh {chn & chn_graph = g}
        # (synr, chnr)  = exprCata mkGraphAlg r inh chnl
        = case (synl.syn_entry_id, synr.syn_entry_id) of
            (Just l, Just r)
              # g = addEmptyEdge (sid, l) chnr.chn_graph
              # g = addEmptyEdge (sid, r) g
              # g = addEmptyEdge (l, jid) g
              # g = addEmptyEdge (r, jid) g
              = annotExpr (App app) inh { chnr & chn_graph = g} synr
            (lid, rid)
              = edgeErr "bin app edge" lid l rid r chnr
        // TODO: If there are no two elems in the list, the expr is eta-reduced, so we need to pprint it instead of throwing an error

    // TODO: Can be eta-reduced
    // TODO: In the case where we have
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
                # exprs     = listExprToList arg
                # (sid, g)  = addNode (mkNode app GParallelSplit) chn.chn_graph
                # (jid, g)  = addNode (mkNode app (GParallelJoin join)) g
                # chn       = {chn & chn_graph = g}
                # chn       = let f sid e chn
                                   # (syn, chn)  = exprCata mkGraphAlg e inh chn
                                   # g           = addEmptyEdge (sid, fromMaybe (abort "Failed to add parallel node") syn.syn_entry_id) chn.chn_graph
                                   # g           = addEmptyEdge (fromMaybe (abort "Failed to add parallel node") syn.syn_entry_id, jid) g
                                   = {chn & chn_graph = g}
                              in  foldr (f sid) chn exprs
                = annotExpr (App app) inh chn (mkDualIdSynExpr (Just sid) (Just jid))
            | isListCompr app.app_symb.symb_ident.id_name
                # (sid, g)    = addNode (mkNode app GParallelSplit) chn.chn_graph
                # (jid, g)    = addNode (mkNode app (GParallelJoin join)) g
                # (lc, menv)  = sugarListCompr app chn.chn_module_env
                # (nid, g)    = addNode (mkNode app (GListComprehension lc)) g
                # g           = addEmptyEdge (sid, nid) g
                # g           = addEmptyEdge (nid, jid) g
                = annotExpr (App app) inh {chn & chn_graph = g, chn_module_env = menv} (mkDualIdSynExpr (Just sid) (Just jid))
            | otherwise = mkTaskApp app ctxs args inh chn
          _ = annotExpr (App app) inh chn mkSynExpr

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
    // TODO: Introduce lets in the graph for all variables that are being applied
    | identIsLambda app.app_symb.symb_ident
        # (mfd, menv)    = reifyFunDef app.app_symb.symb_ident.id_name chn.chn_module_env
        # (fidx, fd)     = fromMaybe (abort ("atC: failed to reify " +++ app.app_symb.symb_ident.id_name)) mfd
        # letargs        = drop (length app.app_args) (getFunArgs fd)
        # (binds, menv)  = zipWithSt zwf letargs es menv
        # chn            = { chn & chn_module_env = menv }
        # (lid, g)       = addNode (mkNode app (GLet {GLet | glet_binds = binds})) chn.chn_graph
        //# g = addEmptyEdge (lid, chn.chn_merge_id) g
        = annotExpr (e @ es) inh { chn & chn_graph = g } (mkSingleIdSynExpr (Just lid))
    | otherwise    =  abort "atC: otherwise case" // TODO : pretty print function application
    where
      zwf eVar eVal menv
        # (fvl, menv) = ppFreeVar eVar menv
        # (fvr, menv) = ppExpression eVal menv
        = ((ppCompact fvl, ppCompact fvr), menv)
  atC _ _ _ _ = abort "atC: something else than App"

  letC lt inh chn
    # mexpr  = listToMaybe  [  bnd.lb_src \\ bnd <- getLetBinds lt
                            |  bnd.lb_dst.fv_ident.id_name == "_case_var"]
    = case mexpr of
        Just expr -> exprCata mkGraphAlg lt.let_expr {inh & inh_case_expr = Just expr } chn
        _         -> mkLet lt inh chn
    where
    mkLet lt inh chn
      # (binds, menv) = mkGLetBinds lt chn.chn_module_env
      # (lid, g)      = addNode (mkNode lt (GLet {GLet | glet_binds = binds})) chn.chn_graph
      // TODO: Represent the bindings in any way possible, not just PP
      # (syn, chn)    = exprCata mkGraphAlg lt.let_expr inh {chn & chn_graph = g, chn_module_env = menv}
      = case syn.syn_entry_id of
          Just n
            # g = addEmptyEdge (lid, n) chn.chn_graph
            = annotExpr (Let lt) inh {chn & chn_graph = g} (mkSingleIdSynExpr (Just lid))
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
  caseC cs inh chn
    # (alts, menv) = mkAlts cs chn.chn_module_env
    = mkDecision (Case cs) CaseDecision caseExpr alts inh {chn & chn_module_env = menv}
    where
    caseExpr = fromMaybe cs.case_expr inh.inh_case_expr
    mkAlts cs menv
      # (alts, menv) = mkAlts` cs.case_guards menv
      = (alts ++ optional [] (\e -> [('PPrint'.text "_", e)]) cs.case_default, menv)
    mkAlts` (AlgebraicPatterns _ aps) menv  = mapSt f aps menv
      where
      f ap menv
        # (x, menv) = mkAp ap.ap_symbol ap.ap_vars menv
        = ((x, ap.ap_expr), menv)
      mkAp sym []   menv = ('PPrint'.text sym.glob_object.ds_ident.id_name, menv)
      mkAp sym vars menv
        # (fvds, menv) = mapSt ppFreeVar vars menv
        = ('PPrint'.text sym.glob_object.ds_ident.id_name 'PPrint'. <+> 'PPrint'.hcat fvds, menv)
    mkAlts` (BasicPatterns _ bps) menv
      = mapSt f bps menv
      where f bp menv
              # (bvd, menv) = ppBasicValue bp.bp_value menv
              = ((bvd, bp.bp_expr), menv)

  // TODO: It appears as if conditionals are desugared to case blocks before we
  // get to them... Is this a remnant from old compiler versions?
  condC c inh chn
    # if_else = fromOptional (abort "`if` should have two branches") c.if_else
    = mkDecision (Conditional c) IfDecision c.if_cond [('PPrint'.text "True", c.if_then), ('PPrint'.text "False", if_else)] inh chn

  mkDecision annot dt expr alts inh chn
    # inh         = {inh & inh_case_expr = Nothing }
    # (ed, menv)  = ppDebugExpression expr chn.chn_module_env
    # (ni, g)     = addNode {GNode|nodeType=GDecision dt (ppCompact ed)} chn.chn_graph
    # chn         = foldr (mkAlt ni) {chn & chn_module_env = menv, chn_graph = g} alts
    //= annotExpr annot inh chn (mkSingleIdSynExpr (Just ni)) // TODO FIXME: This fails...:(
    = (mkSingleIdSynExpr (Just ni), chn)
    where
    mkAlt ni (lbl, e) chn
      # (syn, chn)  = exprCata mkGraphAlg e inh chn
      # g           = addEdge (mkEdge (ppCompact lbl)) (ni, fromMaybe (abort "Failed to add decision node") syn.syn_entry_id) chn.chn_graph
      = {chn & chn_graph = g}

listExprToList :: Expression -> [Expression]
listExprToList (App app) =
  case app.app_symb.symb_ident.id_name of
    "_Cons" ->
      case app.app_args of
        [head:tail:_] -> [head : listExprToList tail]
        _             -> abort "listExprToList should not happen"
    "_Nil"  -> []
    _       -> abort "listExprToList: App is not a list"
listExprToList _ = []

nodeErr :: (Maybe Int) Expression *ChnExpression -> *(String, *ChnExpression)
nodeErr mn expr chn
  # (doc, menv) = ppDebugExpression expr chn.chn_module_env
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
funToGraph :: PredefinedSymbol FunDef *ModuleEnv -> *(Maybe GinGraph, *ModuleEnv)
funToGraph pds fd=:{fun_ident=fun_ident, fun_body = TransformedBody tb} menv = mkBody
  where
  mkBody // TODO cb.cb_args
    # inh          = mkInhExpr fun_ident.id_name pds
    # chn          = mkChnExpr emptyGraph [0..] menv
    # (syn, chn)   = exprCata mkGraphAlg tb.tb_rhs inh chn
    # (initId, g)  = addNode {GNode|nodeType=GInit} chn.chn_graph
    # g            = addStartEdge syn.syn_entry_id initId g
    # g            = addStopEdges g
    = (Just g, chn.chn_module_env)

  addStopEdges g
    # leafs        = leafNodes g
    # (stopId, g)  = addNode {GNode|nodeType=GStop} g
    = foldr (\nid g_ -> addEmptyEdge (nid, stopId) g_) g leafs

  addStartEdge mfirstId initId g
    = maybe g (\firstId -> addEmptyEdge (initId, firstId) g) mfirstId

funToGraph _ _ fun_defs = (Nothing, fun_defs)

instance toString GNode where
	toString n = toString n.nodeType

instance toString GNodeType where
  toString GInit = "GInit"
  toString GStop = "GStop"
  toString (GDecision _ _) = "GDecision"
  toString (GLet _) = "GLet"
  toString GParallelSplit = "GParallelSplit"
  toString (GParallelJoin _) = "GParallelJoin"
  toString (GTaskApp _ _) = "GTaskApp"
  toString (GReturn _) = "GReturn"
  toString (GAssign _) = "GAssign"
  toString GStep = "GStep"
  toString (GListComprehension _) = "GListComprehension"


//prettyAlg :: InhExpression -> ExpressionAlg Doc
//prettyAlg chn =
  //let
    //varC bv = pp chn bv
    //appC app
      //# args = dropAppContexts app chn.chn_module_env
      //= let ppargs xs = 'PPrint'.hcat $ intersperse ('PPrint'.text " ") $ map (pp chn) xs
        //in  (case args of
               //[]     -> pp inh app.app_symb
               //[x:xs] -> if (isInfix chn.chn_module_env app.app_symb)
                           //(pp inh x 'PPrint'. <+> pp inh app.app_symb 'PPrint'. <+> ppargs xs)
                           //(pp inh app.app_symb 'PPrint'. <+> ppargs args))
    //basicC bv = pp inh bv
    //defaultC = 'PPrint'.empty
    //selectionC _ expr sels = pp inh expr 'PPrint'. <-> 'PPrint'.char '.' 'PPrint'. <-> 'PPrint'.hcat (intersperse ('PPrint'.char '.') $ map (pp inh) sels)
    //updateC _ _ _ = 'PPrint'.text "update"
    //recordUpdateC _ _ _ = 'PPrint'.text "recordUpdate"
    //tupleSelectC _ _ _ = 'PPrint'.text "tupleSelect"

  //in { mkExprAlg 'PPrint'.empty
     //& var = varC, app = appC, basicExpr = basicC, selection = selectionC
     //, recordUpdate = recordUpdateC, update = updateC, tupleSelect = tupleSelectC }


/*
Task assignment drawing: Needs a stick.png with a stick figure (can be PDF?)
digraph G {
   rankdir=LR;

    subgraph clusterUser {label="User"; labelloc="b"; peripheries=0; user};
    user [shapefile="stick.png", peripheries=0, style=invis];

    login [label="Log In", shape=ellipse];

    user->login [arrowhead=none];
}
*/

