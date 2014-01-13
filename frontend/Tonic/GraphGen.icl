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
withTwo app _         _ inh chn = ({mkSynExpr & syn_annot_expr = Just (App app)}, chn) // annotExpr (App app) inh chn mkSynExpr

// Annotation functionality temporarily disabled
annotExpr :: (Int, Int) Expression InhExpression *ChnExpression SynExpression -> *(SynExpression, *ChnExpression)
annotExpr (entry, exit) expr inh chn syn = (syn, chn)
  //| inh.inh_tune_symb.pds_def == NoIndex || inh.inh_tune_symb.pds_module == NoIndex = (syn, chn)
  //| otherwise
      //# (papp, menv) = partialApp expr chn.chn_module_env
      //# chn          = {chn & chn_module_env = menv}
      //| papp         = (syn, chn)
      //| otherwise
        //# (app, chn)   = mkTuneApp chn
        //= ({syn & syn_annot_expr = Just (App app)}, chn)
  //where
  //mkTuneApp chn
    //# (mod, menv) = (chn.chn_module_env)!me_icl_module
    //= ({ App
       //| app_symb = { SymbIdent
                    //| symb_ident = { Ident
                                   //| id_name = "tonicTune"
                                   //, id_info = nilPtr}
                    //, symb_kind  = SK_Function
                                     //{ Global
                                     //| glob_object = inh.inh_tune_symb.pds_def
                                     //, glob_module = inh.inh_tune_symb.pds_module}}
       //, app_args = [ mkStr mod.icl_name.id_name
                    //, mkStr inh.inh_curr_task_name
                    //, mkInt entry
                    //, mkInt exit
                    //, expr]
       //, app_info_ptr = nilPtr}
      //, { chn & chn_module_env = menv })
  //mkStr str = BasicExpr (BVS ("\"" +++ str +++ "\""))
  //mkInt i   = BasicExpr (BVInt i)
  //partialApp (App app) menv
    //# (mft, menv) = reifyFunType app.app_symb.symb_ident.id_name menv
    //= case mft of
        //Just ft
          //# ((_, args), menv) = dropAppContexts app menv
          //= (length args < ft.ft_arity, menv)
        //_ = (False, menv)
  //partialApp _ menv        = (False, menv)

mkGraphAlg :: *(ExpressionAlg InhExpression *ChnExpression SynExpression)
mkGraphAlg
  =  {  mkExprAlg mkSynExpr
     &  app = appC, at = atC, letE = letC,  caseE = caseC
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
          //">>*"       -> mkStep       app ctxs args              inh chn
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
    | otherwise = ({mkSynExpr & syn_annot_expr = Just (App app)}, chn)
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
              = annotExpr (lx, rn) (App app) inh { chnr & chn_graph = g } (mkSingleIdSynExpr synl.syn_entry_id)
            (_, lid, rid, _)
              = edgeErr "bind edge (>>|)" lid lhsExpr rid rhsExpr chnr

    mkBind app ctxs args inh chn
      //# (d, menv) = ppDebugApp app chn.chn_module_env
      //# menv = trace_n ("\nmkBind trace:\n" +++ ppCompact d +++ "\n") menv
      //= withTwo app args f inh {chn & chn_module_env = menv}
      = withTwo app args f inh chn
      where
      f lhsExpr rhsExpr chn
        //# (dl, menv) = ppDebugExpression lhsExpr chn.chn_module_env
        //# (dr, menv) = ppDebugExpression rhsExpr menv
        //# menv = trace_n ("\nmkBind trace:\n- " +++ ppCompact dl +++ "\n- " +++ ppCompact dr) menv
        //# (synl, chnl)    = exprCata mkGraphAlg lhsExpr inh {chn & chn_module_env = menv}
        # (synl, chnl)    = exprCata mkGraphAlg lhsExpr inh chn
        # ((synr, chnr), edge)
            = case (exprIsLambda rhsExpr, rhsExpr) of
                (True, App rhsApp)
                  # (mfd, menv)    = reifyFunDef rhsApp.app_symb chnl.chn_module_env
                  # (rSym, menv)   = ppSymbIdent rhsApp.app_symb menv
                  # rhsfd          = fromMaybe (abort $ "mkGraphAlg #1: failed to find function definition for " +++ ppCompact rSym) mfd
                  # (rhsTy, menv)  = reifySymbIdentType rhsApp.app_symb menv
                  # patid          = case [x \\ x <- snd $ dropContexts rhsTy (getFunArgs rhsfd) | x.fv_def_level == -1] of
                                       [x:_] -> freeVarName x
                                       _     -> abort "Invalid bind"
                  # (syne, chn)    = exprCata mkGraphAlg (getFunRhs rhsfd) inh { chnl & chn_module_env = menv }
                  # menv           = case symbIdentObjectIdx rhsApp.app_symb of
                                       Just sid -> updateWithAnnot sid syne.syn_annot_expr chn.chn_module_env
                                       _        -> abort "mkBind: cannot reify symb ident"
                  = ((syne, {chn & chn_module_env = menv}), mkEdge patid)
                _ = (exprCata mkGraphAlg rhsExpr inh chnl, emptyEdge)
        = case (synl.syn_entry_id, synl.syn_exit_id, synr.syn_entry_id, synr.syn_exit_id) of
            (Just _, Just lx, Just rn, Just _)
              # g    = addEdge edge (lx, rn) chnr.chn_graph
              # app` = case (synl.syn_annot_expr, synr.syn_annot_expr) of
                         (Just la, Just ra) -> { app & app_args = ctxs ++ [la, ra] }
                         _                  -> app
              = annotExpr (lx, rn) (App app`) inh { chnr & chn_graph = g } (mkSingleIdSynExpr synl.syn_entry_id)
            (_, lid, rid, _)
              = edgeErr "bind edge (>>=)" lid lhsExpr rid rhsExpr chnr

    mkReturn app ctxs args inh chn
      # (ppd, chn) = case args of
                       [x:_] -> mkRet x chn
                       _     -> (GCleanExpression "", chn)
      # (n, g)     = addNode (mkNode app (GReturn ppd)) chn.chn_graph
      = annotExpr (n, n) (App app) inh {chn & chn_graph = g} (mkSingleIdSynExpr (Just n))
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
         # (ud, menv)  = ppExpression u chn.chn_module_env
         # (lid, g)    = addNode (mkNode app (GAssign (ppCompact ud))) chn.chn_graph
         # (syn, chn)  = exprCata mkGraphAlg t inh {chn & chn_graph = g, chn_module_env = menv}
         = case syn.syn_entry_id of
             Just r
               # g = addEmptyEdge (lid, r) chn.chn_graph
               = annotExpr (r, r) (App app) inh {chn & chn_graph = g} syn
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
              = annotExpr (l, r) (App app) inh { chnr & chn_graph = g} synr
            (lid, rid)
              = edgeErr "step edge" lid l rid r chnr
        // TODO: If there are no two elems in the list, the expr is eta-reduced, so we need to pprint it instead of throwing an error

    mkTaskApp app ctxs args inh chn
      # (ps, menv) = mapSt ppExpression args chn.chn_module_env
      //# menv       = trace_n ("\nmkTaskApp trace:\n" +++ foldr (\x xs -> ppCompact x +++ xs) "" ps +++ "\n") menv
      # chn        = {chn & chn_module_env = menv}
      # appArgs    = map (GCleanExpression o ppCompact) ps  // TODO: When do we pprint a Clean expr? And when do we generate a subgraph?
      # (an, g)    = addNode (mkNode app ((GTaskApp (appFunName app)) appArgs)) chn.chn_graph
      = annotExpr (an, an) (App app) inh { chn & chn_graph = g } (mkSingleIdSynExpr (Just an))

    mkBinApp app ctxs args pat inh chn
      = withTwo app args f inh chn
      where
      f l r chn
        # (synl, chnl) = exprCata mkGraphAlg l inh chn
        # (synr, chnr) = exprCata mkGraphAlg r inh chnl
        = case (synl.syn_entry_id, synr.syn_entry_id) of
            (Just l, Just r)
              # g = addEdge (maybe emptyEdge mkEdge pat) (l, r) chnr.chn_graph
              = annotExpr (l, r) (App app) inh { chnr & chn_graph = g } synr
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
        = case (synl.syn_entry_id, synl.syn_exit_id, synr.syn_entry_id, synr.syn_exit_id) of //(synl.syn_entry_id, synr.syn_entry_id) of
            (Just le, Just lx, Just re, Just rx)
              # g = addEmptyEdge (sid, le) chnr.chn_graph
              # g = addEmptyEdge (sid, re) g
              # g = addEmptyEdge (lx, jid) g
              # g = addEmptyEdge (rx, jid) g
              = annotExpr (sid, jid) (App app) inh { chnr & chn_graph = g} (mkDualIdSynExpr (Just sid) (Just jid))
            (_, lid, rid, _)
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
                # exprs      = listExprToList arg
                # (sid, g)   = addNode (mkNode app GParallelSplit) chn.chn_graph
                # (jid, g)   = addNode (mkNode app (GParallelJoin join)) g
                # chn        = {chn & chn_graph = g}
                # (aes, chn) = let f sid e (xs, chn)
                                    # (syn, chn)  = exprCata mkGraphAlg e inh chn
                                    # g           = addEmptyEdge (sid, fromMaybe (abort "Failed to add parallel node") syn.syn_entry_id) chn.chn_graph
                                    # g           = addEmptyEdge (fromMaybe (abort "Failed to add parallel node") syn.syn_entry_id, jid) g
                                    # aes         = case syn.syn_annot_expr of
                                                      Just ae -> [ae:xs]
                                                      _       -> xs
                                    = (aes, {chn & chn_graph = g})
                               in  foldr (f sid) ([], chn) exprs
                = annotExpr (sid, jid) (App {app & app_args = exprs} ) inh chn (mkDualIdSynExpr (Just sid) (Just jid))
            | isListCompr app.app_symb.symb_ident.id_name
                # (sid, g)    = addNode (mkNode app GParallelSplit) chn.chn_graph
                # (jid, g)    = addNode (mkNode app (GParallelJoin join)) g
                # (lc, menv)  = sugarListCompr app chn.chn_module_env
                # (nid, g)    = addNode (mkNode app (GListComprehension lc)) g
                # g           = addEmptyEdge (sid, nid) g
                # g           = addEmptyEdge (nid, jid) g
                = annotExpr (sid, jid) (App app) inh {chn & chn_graph = g, chn_module_env = menv} (mkDualIdSynExpr (Just sid) (Just jid))
            | otherwise = mkTaskApp app ctxs args inh chn
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
    // TODO: Introduce lets in the graph for all variables that are being applied
    | identIsLambda app.app_symb.symb_ident
        # (mfd, menv)   = reifyFunDef app.app_symb chn.chn_module_env
        # fd            = fromMaybe (abort ("atC: failed to reify " +++ app.app_symb.symb_ident.id_name)) mfd
        # letargs       = drop (length app.app_args) (getFunArgs fd)
        # (binds, menv) = zipWithSt zwf letargs es menv
        # chn           = { chn & chn_module_env = menv }
        # (lid, g)      = addNode (mkNode app (GLet {GLet | glet_binds = binds})) chn.chn_graph
        # (syne, chn)   = exprCata mkGraphAlg (getFunRhs fd) inh { chn & chn_graph = g }
        # g             = case syne.syn_entry_id of
                            Just eid -> addEmptyEdge (lid, eid) chn.chn_graph
                            _        -> chn.chn_graph
        # menv          = case symbIdentObjectIdx app.app_symb of
                            Just sid -> updateWithAnnot sid syne.syn_annot_expr chn.chn_module_env
                            _        -> abort "atC: no app_symb idx"
        # chn           = { chn & chn_module_env = menv, chn_graph = g }
        = annotExpr (lid, lid) (e @ es) inh chn ({syne & syn_entry_id = Just lid, syn_exit_id = Just lid}) // mkSingleIdSynExpr (Just lid)) // TODO Do something with syne?
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
      //= annotExpr (Let l) inh chn syn // TODO WHY DOESNT THIS WORK?
      = (syn, chn)
    mkLet Nothing lt inh chn
      # (binds, menv) = mkGLetBinds lt chn.chn_module_env
      # (lid, g)      = addNode (mkNode lt (GLet {GLet | glet_binds = binds})) chn.chn_graph
      // TODO: Represent the bindings in any way possible, not just PP
      # (syn, chn)    = exprCata mkGraphAlg lt.let_expr inh {chn & chn_graph = g, chn_module_env = menv}
      = case syn.syn_entry_id of
          Just n
            # g = addEmptyEdge (lid, n) chn.chn_graph
            # l = case syn.syn_annot_expr of
                    Just ae -> {lt & let_expr = ae}
                    _       -> lt
            = annotExpr (lid, lid) (Let l) inh {chn & chn_graph = g} (mkSingleIdSynExpr (Just lid))
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

  // TODO: Update cases, both rhss and matching expr
  // TODO: Do we need to beware of case blocks that actually resemble if statements? These get re-sugared later in the pipeline (probably for more efficient code)
  caseC cs inh chn
    # (alts, menv) = mkAlts cs chn.chn_module_env
    # chn          = {chn & chn_module_env = menv}
    # inh          = {inh & inh_case_expr = Nothing }
    # (ed, menv)   = ppExpression caseExpr chn.chn_module_env
    # (ni, g)      = addNode {GNode|nodeType=GDecision CaseDecision (ppCompact ed)} chn.chn_graph
    # chn          = foldr (mkAlt ni) {chn & chn_module_env = menv, chn_graph = g} alts
    //= annotExpr (Case cs) inh chn (mkSingleIdSynExpr (Just ni)) // TODO FIXME: This fails...:(
    = (mkSingleIdSynExpr (Just ni), chn)
    where
    mkAlt ni (lbl, e) chn
      # (syn, chn)  = exprCata mkGraphAlg e inh chn
      # g           = addEdge (mkEdge (ppCompact lbl)) (ni, fromMaybe (abort "Failed to add decision node") syn.syn_entry_id) chn.chn_graph
      = {chn & chn_graph = g}
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
funToGraph :: PredefinedSymbol FunDef *ModuleEnv *Heaps -> *(([String], Maybe GinGraph, Maybe Expression), *ModuleEnv, *Heaps)
funToGraph pds fd=:{fun_ident=fun_ident, fun_body = TransformedBody tb} menv heaps = mkBody
  where
  mkBody
    # inh          = mkInhExpr fun_ident.id_name pds
    # chn          = mkChnExpr emptyGraph [0..] menv heaps
    # (syn, chn)   = exprCata mkGraphAlg tb.tb_rhs inh chn
    # (initId, g)  = addNode {GNode|nodeType=GInit} chn.chn_graph
    # g            = addStartEdge syn.syn_entry_id initId g
    # g            = addStopEdges g
    = ((map (\x -> x.fv_ident.id_name) tb.tb_args, Just g, syn.syn_annot_expr), chn.chn_module_env, chn.chn_heaps)

  addStopEdges g
    # leafs        = leafNodes g
    # (stopId, g)  = addNode {GNode|nodeType=GStop} g
    = foldr (\nid g_ -> addEmptyEdge (nid, stopId) g_) g leafs

  addStartEdge mfirstId initId g
    = maybe g (\firstId -> addEmptyEdge (initId, firstId) g) mfirstId

funToGraph _ _ menv heaps = (([], Nothing, Nothing), menv, heaps)

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

