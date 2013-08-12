implementation module Tonic.GraphGen

// Task Oriented Notation Illustrated on a Canvas

//import syntax, checksupport, StdFile
//from CoclSystemDependent import DirectorySeparator, ensureCleanSystemFilesExists

import syntax

import StdFunc
////import Tonic.TonicAG
import Tonic.Util
import Tonic.AbsSyn
//import Tonic.Pretty

import Data.Func
import Data.Maybe
import Data.List
import Data.Graph

import qualified Text.PPrint as PPrint

import Tonic.Pretty

import StdMisc
import StdDebug

//import Data.Func, Data.Functor, Data.Graph, Data.Maybe, Text
//from Data.List import zipWith, intersperse
//import StdDebug
/*
To reconstruct lambda functions:
- Look for a top-level function starting with \; and call it f
- Throw away the arguments that came from an outer scope (recognizable, negative index?)
- Add the remaining arguments as lambda arguments
- Convert lambda body as usual
- Throw away f
- Replace all occurences of f with the reconstructed expression
- Repeat
*/
// funToLam = undef

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


edgeErr :: ModuleEnv String (Maybe Int) Expression (Maybe Int) Expression -> a
edgeErr menv errmsg lid lexpr rid rexpr = abort ("Cannot create " +++ errmsg
  +++ " between left expression\n\t" +++ nodeErr menv lid lexpr
  +++ " and right expression\n\t" +++ nodeErr menv rid rexpr +++ "\n")

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

connectId :: InhExpression SynExpression -> (Maybe Int, SynExpression)
connectId inh syn
  | syn.syn_rec_node  = (Just inh.inh_merge_id, { syn & syn_rec_node = False })
  | otherwise         = (syn.syn_nid, syn)


// TODO: Check if we need more connectId applications
mkGraphAlg :: InhExpression -> ExpressionAlg SynExpression
mkGraphAlg inh =
  let
  appC app
    | identIsTask inh.inh_module_env app.app_symb.symb_ident =
        case appFunName app of // TODO `parallel`
          ">>="       -> mkBind app inh.inh_graph
          "return"    -> mkReturn app inh.inh_graph
          ">>|"       -> mkBinApp app Nothing inh.inh_graph
          "@:"        -> mkAssign app inh.inh_graph
          ">>*"       -> mkStep app inh.inh_graph
          "-||-"      -> mkParBinApp app DisFirstBin inh.inh_graph
          "||-"       -> mkParBinApp app DisRight inh.inh_graph
          "-||"       -> mkParBinApp app DisLeft inh.inh_graph
          "-&&-"      -> mkParBinApp app ConPair inh.inh_graph
          "anyTask"   -> mkParListApp app DisFirstList inh.inh_graph
          "allTasks"  -> mkParListApp app ConAll inh.inh_graph
          _           -> mkTaskApp app inh.inh_graph
    | otherwise               = mkSynExpr` inh.inh_graph
    where
    mkBind app g
    // TODO: Check with funIsLam if the right-hand function is a lambda. If so,
    // do what we currently do and reify the lambda and continue graph generation.
    // If not, don't reify and just generate a task application node and be done.
      # nodictargs = dropAppContexts app inh.inh_module_env
      # (lhsExpr, rhsApp) =
          case nodictargs of
            [e:App rhsApp:_]  -> (e, rhsApp)
            // TODO: Do not throw an error: bind can be eta-reduced
            _                 -> abort ("Invalid bind: " +++ (intercalateString " " $ map (\x -> "'" +++ mkPretty inh.inh_module_env x +++ "'") nodictargs))
      # rhsfd  = fromMaybe (abort $ "mkGraphAlg #1: failed to find function definition for " +++ mkPretty inh.inh_module_env rhsApp.app_symb)
               $ reifyFunDef inh.inh_module_env rhsApp.app_symb.symb_ident
      # rhsTy  = fromMaybe (abort $ "mkGraphAlg #2: failed to find symbol type for " +++ mkPretty inh.inh_module_env rhsApp.app_symb)
               $ reifySymbolType inh.inh_module_env rhsApp.app_symb.symb_ident
      # patid  = withHead freeVarName (abort "Invalid bind") $ dropContexts rhsTy rhsfd.gfd_args
      # synl   = exprCata (mkGraphAlg inh) lhsExpr
      # synr   = exprCata (mkGraphAlg {inh & inh_graph = synl.syn_graph}) rhsfd.gfd_rhs
      = case (synl.syn_nid, synr.syn_nid) of
          (Just l, Just r)  -> persistHasRec [synl, synr] $ mkSynExpr synl.syn_nid $ addEdge (mkEdge patid) (l, r) synr.syn_graph // TODO: Is this always the correct node id to synthesize?
          (lid, rid)        -> edgeErr inh.inh_module_env "bind edge" lid lhsExpr rid rhsfd.gfd_rhs

    mkReturn app g
      // TODO No error: eta-reduction
      # node   = GReturn $ withHead f (abort "Invalid return") $ dropAppContexts app inh.inh_module_env
      = addNode` node g
      where
      // In case of a function application, we want to inspect the type of the
      // function. If it is a task or a list, treat it differently than any
      // other type. But how can we get the type of an arbitrary expression?
      f (BasicExpr bv)  = GCleanExpression $ mkPretty inh.inh_module_env bv
      f (Var bv)        = GCleanExpression bv.var_ident.id_name
      f e               = GGraphExpression (GGraph (exprCata (mkGraphAlg {inh & inh_graph = g}) e).syn_graph)

    mkAssign app g =
      let mkAssign` u t
            # (lid, g)  = addNode (GAssign (mkPretty inh.inh_module_env u)) g
            # synt      = exprCata (mkGraphAlg {inh & inh_graph = g}) t
            = maybe (err lid) (\r -> persistHasRec [synt] $ mkSynExpr` (addEmptyEdge (lid, r) synt.syn_graph)) synt.syn_nid
            where
            err lid = edgeErr inh.inh_module_env "assign edge" (Just lid) u Nothing t
      // TODO: If there are no two elems in the list, the expr is eta-reduced, so we need to pprint it instead of throwing an error
      in withTwo mkAssign` (abort "Illegal task assignment") app.app_args

    mkStep app g = mkSynExpr` g // TODO
    mkTaskApp app g
      | appFunName app == inh.inh_curr_task_name  = mkRec
      | otherwise                                 = mkTask
      where
      mkRec = { mkSynExpr` g & syn_has_recs = True, syn_rec_node = True }
      mkTask
        # appArgs  = map (GCleanExpression o (mkPretty inh.inh_module_env)) app.app_args  // TODO: When do we pprint a Clean expr? And when do we generate a subgraph?
        # (an, g)  = addNode (GTaskApp (appFunName app) appArgs) g
        = mkSynExpr (Just an) g

    mkBinApp app pat g =
      let mkBinApp` l r
            # synl = exprCata (mkGraphAlg {inh & inh_graph = g}) l
            # synr = exprCata (mkGraphAlg {inh & inh_graph = synl.syn_graph}) r
            = case (synl.syn_nid, synr.syn_nid) of
                (Just l, Just r)  -> persistHasRec [synl, synr] $ mkSynExpr` (addEdge (maybe emptyEdge mkEdge pat) (l, r) synr.syn_graph)
                (lid, rid)        -> edgeErr inh.inh_module_env "bin app edge" lid l rid r
      // TODO: If there are no two elems in the list, the expr is eta-reduced, so we need to pprint it instead of throwing an error
      in  withTwo mkBinApp` (abort "Should not happen: invalid binary application") app.app_args

    mkParBinApp app join g =
      let mkBinApp` l r
            # (sid, g)  = addNode GParallelSplit g
            # (jid, g)  = addNode (GParallelJoin join) g
            # synl      = exprCata (mkGraphAlg {inh & inh_graph = g}) l
            # synr      = exprCata (mkGraphAlg {inh & inh_graph = synl.syn_graph}) r
            = case (synl.syn_nid, synr.syn_nid) of
                (Just l, Just r)
                  # g = addEmptyEdge (sid, l) synr.syn_graph
                  # g = addEmptyEdge (sid, r) g
                  # g = addEmptyEdge (l, jid) g
                  # g = addEmptyEdge (r, jid) g
                  = persistHasRec [synl, synr] $ mkSynExpr` g
                (lid, rid) = edgeErr inh.inh_module_env "bin app edge" lid l rid r
      // TODO: If there are no two elems in the list, the expr is eta-reduced, so we need to pprint it instead of throwing an error
      in  withTwo mkBinApp` (abort "Should not happen: invalid binary application") app.app_args

    // TODO: Can be eta-reduced
    // TODO: In the case where we have
    //    anyTask [someTask, otherTask]
    // we just split, have two nodes someTask and otherTask, then a merge again.
    // Only when the list anyTask is applied to is a list comprehension we generate
    // a more detailed graph with content. Only in that case, there is just one
    // new node (and not even a chain of nodes). We know exactly how many nodes
    // we will get and can therefor link to the join node
    mkParListApp app join g =
      let mkParApp` arg
            | exprIsListConstr arg
                # exprs     = listExprToList arg
                # (sid, g)  = addNode GParallelSplit g
                # (jid, g)  = addNode (GParallelJoin join) g
                # (hr, g)   = let f sid e (hr, g_)
                                   # synx         = exprCata (mkGraphAlg {inh & inh_graph = g_}) e
                                   # (mid, synx)  = connectId inh synx
                                   # g = addEmptyEdge (sid, fromMaybe (abort "Failed to add parallel node") mid) synx.syn_graph
                                   # g = addEmptyEdge (fromMaybe (abort "Failed to add parallel node") mid, jid) synx.syn_graph
                                   = (  synx.syn_has_recs || hr, g)
                              in  foldr (f sid) (False, g) exprs
                = { mkSynExpr (Just sid) g & syn_has_recs = hr }
            | exprIsListCompr arg
                # (nid, g) = addNode GListComprehension g
                = mkSynExpr (Just nid) g // TODO
            | otherwise = mkTaskApp app g
      in withHead mkParApp` (abort "mkParListApp TODO") $ dropAppContexts app inh.inh_module_env

    //# (ni, g) = addNode (GDecision dt (mkPretty inh.inh_module_env expr)) inh.inh_graph
    //# (hr, g) = foldr (f ni) (False, g) alts
    //= { mkSynExpr (Just ni) g & syn_has_recs = hr }
    //where
    //f ni (lbl, e) (hr, gx)
      //# synx         = exprCata (mkGraphAlg {inh & inh_graph = gx}) e
      //# (mid, synx)  = connectId inh synx
      //=  (  synx.syn_has_recs || hr
         //,  addEdge (mkEdge lbl) (ni, fromMaybe (abort "Failed to add decision node") mid) synx.syn_graph)

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
  atC e [] = abort "atC: no args" // TODO e is a non-applied higher order function. What do we do with this?
  atC e=:(App app) es
    // TODO: Introduce lets in the graph for all variables that are being applied
    | identIsLam app.app_symb.symb_ident =
        let fd       = fromMaybe err $ reifyFunDef inh.inh_module_env app.app_symb.symb_ident
            letargs  = drop (length app.app_args) fd.gfd_args
            binds    = zipWith (\eVar eVal -> mkGLetBind (mkPretty inh.inh_module_env eVar) eVal) letargs es
            err      = abort ("atC: failed to reify " +++ app.app_symb.symb_ident.id_name)
            mkRec
              # (lid, g) = addNode (GLet binds) inh.inh_graph
              # g = addEmptyEdge (lid, inh.inh_merge_id) g
              = { mkSynExpr (Just lid) g & syn_has_recs = True }
            mkAt
              # (lid, g) = addNode (GLet binds) inh.inh_graph
              = abort ("atC mkAt for gfd_name" +++ fd.GFunDef.gfd_name +++ " and curr_task_nm " +++ inh.inh_curr_task_name)
        in  case fd.gfd_rhs of
              App appRhs  -> if (appRhs.app_symb.symb_ident.id_name == inh.inh_curr_task_name) mkRec mkAt
              _           -> mkAt
    | otherwise    =  abort "atC: otherwise case" // TODO : pretty print function application
  atC _ _ = abort "atC: something else than App"

  letC lt
    # glet         = mkGLet inh.inh_module_env lt
    # mexpr        = listToMaybe  [  bnd.glb_src \\ bnd <- glet.glet_binds
                                  |  bnd.glb_dst == "_case_var"]
    = case mexpr of
        Just expr -> exprCata (mkGraphAlg {inh & inh_case_expr = Just expr}) glet.glet_expr
        _         -> mkLet glet
    where
    err = abort "Failed to add let edge; no synthesized ID from let body"
    mkLet glet
      # (lid, g)     = addNode (GLet glet.glet_binds) inh.inh_graph
      // TODO: Represent the bindings in any way possible, not just PP
      # syn2         = exprCata (mkGraphAlg {inh & inh_graph = g}) lt.let_expr
      # (mid, syn3)  = connectId inh syn2
      # g            = maybe err (\n -> addEmptyEdge (lid, n) syn3.syn_graph) mid
      = persistHasRec [syn3] $ mkSynExpr (Just lid) g // TODO: Correct gid?

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
  caseC cs = mkDecision CaseDecision caseExpr (mkAlts cs)
    where
    caseExpr = fromMaybe cs.case_expr inh.inh_case_expr
    mkAlts cs = mkAlts` cs.case_guards ++ optional [] (\e -> [('PPrint'.text "_", e)]) cs.case_default
    mkAlts` (AlgebraicPatterns _ aps)  = map (\ap -> (mkAp ap.ap_symbol ap.ap_vars, ap.ap_expr)) aps
      where
      mkAp sym []   = ppAg inh.inh_module_env sym.glob_object.ds_ident
      mkAp sym vars = ppAg inh.inh_module_env sym.glob_object.ds_ident 'PPrint'. <+>
                      'PPrint'.hcat (map (ppAg inh.inh_module_env) vars)
    mkAlts` (BasicPatterns _ bps)      = map (\bp -> (ppAg inh.inh_module_env bp.bp_value, bp.bp_expr)) bps

  // TODO: It appears as if conditionals are desugared to case blocks before we
  // get to them... Is this a remnant from old compiler versions?
  condC c
    # if_else = fromOptional (abort "`if` should have two branches") c.if_else
    = mkDecision IfDecision c.if_cond [('PPrint'.text "True", c.if_then), ('PPrint'.text "False", if_else)]

  mkDecision dt expr alts
    # inh     = {inh & inh_case_expr = Nothing }
    # (ni, g) = addNode (GDecision dt (mkPretty inh.inh_module_env expr)) inh.inh_graph
    # (hr, g) = foldr (f ni) (False, g) alts
    = { mkSynExpr (Just ni) g & syn_has_recs = hr }
    where
    f ni (lbl, e) (hr, gx)
      # synx         = exprCata (mkGraphAlg {inh & inh_graph = gx}) e
      # (mid, synx)  = connectId inh synx
      =  (  synx.syn_has_recs || hr
         ,  addEdge (mkEdge (ppCompact lbl)) (ni, fromMaybe (abort "Failed to add decision node") mid) synx.syn_graph)

  in
  {  mkExprAlg (mkSynExpr` inh.inh_graph)
  &  app = appC, at = atC, letE = letC, caseE = caseC, conditional = condC
  }

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

nodeErr :: ModuleEnv (Maybe Int) Expression -> String
nodeErr menv mn expr = mkPretty menv expr +++ "\n" +++
  maybe "for which its ID is unknown" (\n -> "with node ID " +++ toString n) mn

addEmptyEdge :: (Int, Int) GinGraph -> GinGraph
addEmptyEdge e g = addEdge emptyEdge e g

addNode` :: GNode GinGraph -> SynExpression
addNode` node graph
  # (n, g) = addNode node graph
  = mkSynExpr (Just n) g

// TODO: We need to split this up: one part of this should generate the graph
// for the FunDef and the other part should generate the init and stop nodes.
// Yet another part should just get the right-hand side Expression of a FunDef
// so we can just cata it.
funToGraph :: FunDef {#FunDef} IclModule {#DclModule} -> Optional GGraph
funToGraph {fun_ident=fun_ident, fun_body = TransformedBody tb} fun_defs icl_module dcl_modules
  = Yes $ GGraph mkBody
  where
  mkBody // TODO cb.cb_args
    # (mergeId, g)  = addNode GMerge emptyGraph
    # inh           = mkInhExpr (mkModuleEnv fun_defs icl_module dcl_modules) g mergeId fun_ident.id_name Nothing
    # syn           = exprCata (mkGraphAlg inh) tb.tb_rhs
    # g             = syn.syn_graph
    # (initId, g)   = addNode GInit g
    # g             = if syn.syn_has_recs
                        (mkRec syn.syn_nid initId mergeId g)
                        (mkNonrec syn.syn_nid initId mergeId g)
    = addStopEdges g

  addStopEdges g
    # leafs        = leafNodes g
    # (stopId, g)  = addNode GStop g
    = foldr (\nid g_ -> addEmptyEdge (nid, stopId) g_) g leafs

  mkRec mfirstId initId mergeId g
    # g = addEmptyEdge (initId, mergeId) g
    = maybe g (\firstId -> addEmptyEdge (mergeId, firstId) g) mfirstId

  mkNonrec mfirstId initId mergeId g
    # g = removeNode mergeId g
    = maybe g (\firstId -> addEmptyEdge (initId, firstId) g) mfirstId

funToGraph _ _ _ _ = No

instance toString GNode where
  toString GInit = "GInit"
  toString GStop = "GStop"
  toString (GDecision _ _) = "GDecision"
  toString GMerge = "GMerge"
  toString (GLet _) = "GLet"
  toString GParallelSplit = "GParallelSplit"
  toString (GParallelJoin _) = "GParallelJoin"
  toString (GTaskApp _ _) = "GTaskApp"
  toString (GReturn _) = "GReturn"
  toString (GAssign _) = "GAssign"
  toString GStep = "GStep"
  toString GListComprehension = "GListComprehension"


//prettyAlg :: InhExpression -> ExpressionAlg Doc
//prettyAlg inh =
  //let
    //varC bv = pp inh bv
    //appC app
      //# args = dropAppContexts app inh.inh_module_env
      //= let ppargs xs = 'PPrint'.hcat $ intersperse ('PPrint'.text " ") $ map (pp inh) xs
        //in  (case args of
               //[]     -> pp inh app.app_symb
               //[x:xs] -> if (isInfix inh.inh_module_env app.app_symb)
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

