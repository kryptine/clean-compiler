implementation module GinTonic

// Task Oriented Notation Illustrated on a Canvas

import syntax, checksupport, StdFile
from CoclSystemDependent import DirectorySeparator, ensureCleanSystemFilesExists

import Func, Graph, Maybe
import StdDebug

ginTonic :: IclModule {#DclModule} *FrontendTuple !*Files -> *(*FrontendTuple, !*Files)
ginTonic iclmod dcl_modules tpl files
  # (ok, files)          = ensureCleanSystemFilesExists csf_directory_path files
  # (ok, tonicf, files)  = fopen (csf_directory_path +++ {DirectorySeparator} +++ ("tonic-" +++ iclmod.icl_name.id_name +++ ".dot")) FWriteText files
  # (tstr, tpl)          = ginTonic` iclmod dcl_modules tpl
  //| True = abort tstr
  # tonicf               = fwrites tstr tonicf
  # (ok, files)          = fclose tonicf files
  = (tpl, files)
  where csf_directory_path = "Clean System Files"

foldrArr :: (a b -> b) b (arr a) -> b | Array arr a
foldrArr f b arr = foldrArr` 0 f b arr
  where
  arrSz = size arr
  foldrArr` n f b arr
    | n < arrSz  = f (select arr n) (foldrArr` (n + 1) f b arr)
    | otherwise  = b

ginTonic` :: IclModule {#DclModule} *FrontendTuple -> *(String, *FrontendTuple)
ginTonic` iclmod dcl_modules tpl=:(ok, fun_defs, array_instances, common_defs, imported_funs, type_def_infos, heaps, predef_symbols, error,out)
  = (foldrArr appDefInfo "" fun_defs, tpl)
  where
  appDefInfo fd rest
    | funIsTask fd && fd.fun_info.fi_def_level == 1  = defToStr fd +++ "\n" +++ rest
    | otherwise                                      = rest
  defToStr fd  = optional "Nothing happened" f (funToGraph fd fun_defs iclmod dcl_modules)
    where f (g, so, si) = mkTaskDot fd.fun_ident.id_name so si g

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

funIsTask :: FunDef -> Bool
funIsTask fd =
  case (fd.fun_type, fd.fun_kind) of
    (Yes st, FK_Function _)  -> symTyIsTask st
    _                        -> False

funIsLam :: FunDef -> Bool
funIsLam fd
  | size fnm > 0  = fnm.[0] == '\\'
  | otherwise     = False
  where fnm = fd.fun_ident.id_name

symTyIsTask :: SymbolType -> Bool
symTyIsTask st =
  case st.st_result.at_type of
    TA   tsi _     -> symTyIsTask` tsi
    TAS  tsi _  _  -> symTyIsTask` tsi
    _              -> False
  where symTyIsTask` tsi = tsi.type_ident.id_name == "Task"

symIdIsTask :: SymbIdent -> Bool
symIdIsTask si =
  case si.symb_kind of
    SK_Function gi  -> True // TODO FIXME gi.glob_object :: Global Index
    SK_GeneratedFunction fiptr idx  -> True // TODO FIXME gi.glob_object :: Global Index
    _               -> False

identIsTask :: Ident -> Bool
identIsTask id = abort "identIsTask not implemented" // TODO

findInArr :: (e -> Bool) (a e) -> Maybe e | Array a e
findInArr p arr = findInArr` 0 p arr
  where
  arrSz = size arr
  findInArr` n p arr
    | n < arrSz
      #  elem = select arr n
      =  if (p elem) (Just elem) (findInArr` (n + 1) p arr)
    | otherwise  = Nothing

reifyFunDef :: {#FunDef} IclModule {#DclModule} SymbIdent -> FunDef
reifyFunDef fun_defs icl_module dcl_modules si =
  case findInArr (\fd -> fd.fun_ident == ident) fun_defs of
    Just fd  -> fd
    _        -> abort ("Failed to reify " +++ ident.id_name)
  where ident = si.symb_ident

//reifyFunType :: IclModule {#DclModule} Ident -> SymbolType
//reifyFunType icl_module dcl_modules ident =
  //case findInArr (\fd -> fd.fun_ident == ident) icl_module.icl_functions of
    //Just fd  ->
      //case fd.fun_type of
        //Yes st  -> undef
        //_       -> failReify
    //_        -> failReify
  //where failReify = abort ("Failed to reify " +++ ident.id_name)
// TODO look up in icl_module.icl_common
// TODO Add DclModule and look up in dcl_module.dcl_functions and dcl_common

getFunArgVars :: FunDef -> [FreeVar]
getFunArgVars fd =
  case fd.fun_body of
    TransformedBody tb  -> tb.tb_args
    _                   -> []

getFunRhs :: FunDef -> Expression
getFunRhs fd =
  case fd.fun_body of
    TransformedBody tb  -> tb.tb_rhs
    _                   -> abort "Need TransformedBody"

/*
TODO:
GiN does not do eta-reduction. I.e., it only supports either a `f >>= \x -> e`
or `f >>| e` bind, but never a `f >>= g` bind. If we want to support the
latter, we must eta-expand `g`.
*/

:: ExpressionAlg a =
  {  var                   :: BoundVar -> a                                                 // Var
  ,  app                   :: App -> a                                                      // App
  ,  at                    :: a [a] -> a                                                    // (@)
  ,  letE                  :: Let -> a                                                      // Let
  ,  caseE                 :: Case -> a                                                     // Case
  ,  selection             :: SelectorKind a [Selection] -> a                               // Selection
  ,  update                :: a [Selection] a -> a                                          // Update
  ,  recordUpdate          :: (Global DefinedSymbol) a [Bind a (Global FieldSymbol)] -> a   // RecordUpdate
  ,  tupleSelect           :: DefinedSymbol Int a -> a                                      // TupleSelect
  ,  basicExpr             :: BasicValue -> a                                               // BasicExpr
  ,  conditional           :: Conditional -> a                                              // Conditional
  ,  anyCodeExpr           :: (CodeBinding BoundVar) (CodeBinding FreeVar) [String] -> a    // AnyCodeExpr
  ,  abcCodeExpr           :: [String] Bool -> a                                            // ABCCodeExpr
  ,  matchExpr             :: (Global DefinedSymbol) a -> a                                 // MatchExpr
  ,  isConstructor         :: a (Global DefinedSymbol) Int GlobalIndex Ident Position -> a  // IsConstructor
  ,  freeVar               :: FreeVar -> a                                                  // FreeVar
  ,  dictionariesFunction  :: [(FreeVar,AType)] a AType -> a                                // DictionariesFunction
  ,  constant              :: SymbIdent Int Priority -> a                                   // Constant
  ,  classVariable         :: VarInfoPtr -> a                                               // ClassVariable
  ,  dynamicExpr           :: DynamicExpr -> a                                              // DynamicExpr
  ,  typeCodeExpression    :: TypeCodeExpression -> a                                       // TypeCodeExpression
  ,  typeSignature         :: (Int Int -> (AType,Int,Int)) a -> a                           // TypeSignature
  ,  ee                    :: a                                                             // EE
  ,  noBind                :: ExprInfoPtr -> a                                              // NoBind
  ,  failExpr              :: !Ident -> a                                                    // FailExpr
  }

exprCata :: (ExpressionAlg a) Expression -> a
exprCata alg (Var bv                      ) = alg.var bv
exprCata alg (App a                       ) = alg.app a
exprCata alg (l @ rs                      ) = alg.at (exprCata alg l) (map (exprCata alg) rs)
exprCata alg (Let l                       ) = alg.letE l
exprCata alg (Case c                      ) = alg.caseE c
exprCata alg (Selection sk e ss           ) = alg.selection sk (exprCata alg e) ss
exprCata alg (Update e1 ss e2             ) = alg.update (exprCata alg e1) ss (exprCata alg e2)
exprCata alg (RecordUpdate gd e bs        ) = alg.recordUpdate gd (exprCata alg e) (map (\b -> {b & bind_src=exprCata alg b.bind_src}) bs)
exprCata alg (TupleSelect ds i e          ) = alg.tupleSelect ds i (exprCata alg e)
exprCata alg (BasicExpr bv                ) = alg.basicExpr bv
exprCata alg (Conditional c               ) = alg.conditional c
exprCata alg (AnyCodeExpr cb cf ss        ) = alg.anyCodeExpr cb cf ss
exprCata alg (ABCCodeExpr ss b            ) = alg.abcCodeExpr ss b
exprCata alg (MatchExpr gd e              ) = alg.matchExpr gd (exprCata alg e)
exprCata alg (IsConstructor e gd n gi i p ) = alg.isConstructor (exprCata alg e) gd n gi i p
exprCata alg (FreeVar v                   ) = alg.freeVar v
exprCata alg (DictionariesFunction xs e at) = alg.dictionariesFunction xs (exprCata alg e) at
exprCata alg (Constant si i prio          ) = alg.constant si i prio
exprCata alg (ClassVariable vip           ) = alg.classVariable vip
exprCata alg (DynamicExpr de              ) = alg.dynamicExpr de
exprCata alg (TypeCodeExpression t        ) = alg.typeCodeExpression t
exprCata alg (TypeSignature f e           ) = alg.typeSignature f (exprCata alg e)
exprCata alg (EE                          ) = alg.ee
exprCata alg (NoBind eip                  ) = alg.noBind eip
exprCata alg (FailExpr i                  ) = alg.failExpr i

mkExprAlg :: a -> ExpressionAlg a
mkExprAlg defaultC =
  {  ExpressionAlg
  |  var                   = \_ ->            defaultC
  ,  app                   = \_ ->            defaultC
  ,  at                    = \_ _ ->          defaultC
  ,  letE                  = \_ ->            defaultC
  ,  caseE                 = \_ ->            defaultC
  ,  selection             = \_ _ _ ->        defaultC
  ,  update                = \_ _ _ ->        defaultC
  ,  recordUpdate          = \_ _ _ ->        defaultC
  ,  tupleSelect           = \_ _ _ ->        defaultC
  ,  basicExpr             = \_ ->            defaultC
  ,  conditional           = \_ ->            defaultC
  ,  anyCodeExpr           = \_ _ _ ->        defaultC
  ,  abcCodeExpr           = \_ _ ->          defaultC
  ,  matchExpr             = \_ _ ->          defaultC
  ,  isConstructor         = \_ _ _ _ _ _ ->  defaultC
  ,  freeVar               = \_ ->            defaultC
  ,  dictionariesFunction  = \_ _ _ ->        defaultC
  ,  constant              = \_ _ _ ->        defaultC
  ,  classVariable         = \_ ->            defaultC
  ,  dynamicExpr           = \_ ->            defaultC
  ,  typeCodeExpression    = \_ ->            defaultC
  ,  typeSignature         = \_ _ ->          defaultC
  ,  ee                    =                  defaultC
  ,  noBind                = \_ ->            defaultC
  ,  failExpr              = \_ ->            defaultC
  }

:: GinGraph :== Graph GNode GEdge

// InhExpression and SynExpression need strict fields in order to prevent a bus
// error caused by huge thunks
:: InhExpression =
  {  inh_fun_defs        :: !{#FunDef}
  ,  inh_icl_module      :: !IclModule
  ,  inh_dcl_modules     :: !{#DclModule}
  ,  inh_graph           :: !GinGraph
  ,  inh_source_id       :: !Int
  ,  inh_sink_id         :: !Int
  ,  inh_curr_task_name  :: !String
  }

:: SynExpression =
  {  syn_nid        :: !Maybe Int
  ,  syn_graph      :: !GinGraph
  ,  syn_rec_nodes  :: ![NodeIndex]
  }

/*
Inherited attributes:
- icl_module :: IclModule

Chained attributes:
- graph :: GinGraph

Synthesized attributes:
- nid :: Maybe Int
*/
mkSynExpr :: (Maybe Int) GinGraph -> SynExpression
mkSynExpr mn gr =
  {  SynExpression
  |  syn_nid        = mn
  ,  syn_graph      = gr
  ,  syn_rec_nodes  = []
  }

mkSynExpr` :: GinGraph -> SynExpression
mkSynExpr` gr = mkSynExpr Nothing gr

mkInhExpr :: {#FunDef} IclModule {#DclModule} GinGraph Int Int String -> InhExpression
mkInhExpr fun_defs icl_module dcl_modules gg so si nm =
  {  InhExpression
  |  inh_fun_defs        = fun_defs
  ,  inh_icl_module      = icl_module
  ,  inh_dcl_modules     = dcl_modules
  ,  inh_graph           = gg
  ,  inh_source_id       = so
  ,  inh_sink_id         = si
  ,  inh_curr_task_name  = nm
  }

withHead :: (a -> b) b [a] -> b
withHead _  b  []       = b
withHead f  _  [x : _]  = f x

withTwo :: (a a -> b) b [a] -> b
withTwo f  _  [x : y : _]  = f x y
withTwo _  b  _            = b

fromOptional :: a (Optional a) -> a
fromOptional x  No       = x
fromOptional _  (Yes x)  = x

optional :: b (a -> b) (Optional a) -> b
optional b  _  No       = b
optional _  f  (Yes x)  = f x

appFunName :: App -> String
appFunName app = app.app_symb.symb_ident.id_name

freeVarName :: FreeVar -> String
freeVarName fv = fv.fv_ident.id_name

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
mkGraphAlg :: InhExpression -> ExpressionAlg SynExpression
mkGraphAlg inh =
  let
  appC app
    | symIdIsTask app.app_symb  =
        case appFunName app of // TODO `parallel`
          ">>="       -> mkBind app inh.inh_graph
          ">>|"       -> mkBinApp app Nothing inh.inh_graph
          "@:"        -> mkAssign app inh.inh_graph
          "return"    -> mkReturn app inh.inh_graph
          ">>*"       -> mkStep app inh.inh_graph
          "-||-"      -> mkParBinApp app.app_args (GParallelJoin DisFirstBin) inh.inh_graph
          "||-"       -> mkParBinApp app.app_args (GParallelJoin DisRight) inh.inh_graph
          "-||"       -> mkParBinApp app.app_args (GParallelJoin DisLeft) inh.inh_graph
          "-&&-"      -> mkParBinApp app.app_args (GParallelJoin ConPair) inh.inh_graph
          "anyTask"   -> mkParApp app.app_args (GParallelJoin DisFirstList) inh.inh_graph
          "allTasks"  -> mkParApp app.app_args (GParallelJoin ConAll) inh.inh_graph
          _           -> mkTaskApp app inh.inh_graph
    | otherwise               = mkSynExpr` inh.inh_graph
    where
    mkBind app g
    // TODO: Rework
    // The second element of the list is _not_ the lambda variable, but the
    // reference to the entire lifted lambda expression. (assuming it is even
    // a lambda expression).
    // In case of a lambda expression, we first need to reify the function and
    // do the rest there.
    // In case of a function...?
      # argvars  =
          case app.app_args of
            [_:App rhsApp:_]  -> getFunArgVars (reifyFunDef inh.inh_fun_defs inh.inh_icl_module inh.inh_dcl_modules rhsApp.app_symb)
            _                 -> abort ("Expression not supported or invalid bind: " +++ concatStrings (intersperse " " $ map (\x -> "'" +++ mkPretty x +++ "'") app.app_args))
      # patid    = withHead freeVarName (abort "Invalid bind") argvars
      = mkBinApp app (Just patid) g
    mkAssign app g =
      let mkAssign` u t
            # synnd  = addNode` (GAssign (mkPretty u)) g
            # synt   = exprCata (mkGraphAlg {inh & inh_graph = synnd.syn_graph}) t
            = addEdge` synt.syn_nid synnd.syn_nid Nothing synt.syn_graph
      in  mkSynExpr` (withTwo mkAssign` (abort "Illegal task assignment") app.app_args)
    mkReturn app g
      # syn   = withHead (exprCata (mkGraphAlg {inh & inh_graph = g})) (abort "Invalid return") app.app_args
      # node  = GReturn (GGraphExpression (GGraph syn.syn_graph))
      = addNode` node g
    mkStep app g = mkSynExpr` g // TODO
    mkTaskApp app g // TODO: When do we pprint a Clean expr? And when do we generate a subgraph?
      # appArgs  = map (GCleanExpression o mkPretty) app.app_args
      # syn      = addNode` (GTaskApp (appFunName app) appArgs) g
      = case (appFunName app == inh.inh_curr_task_name, syn.syn_nid) of
          (True, Just newid)  -> {syn & syn_rec_nodes = [newid:syn.syn_rec_nodes]}
          _                   -> syn
    mkBinApp app pat g =
      let mkBinApp` l r
            # synl = exprCata (mkGraphAlg {inh & inh_graph = g}) l
            # synr = exprCata (mkGraphAlg {inh & inh_graph = synl.syn_graph}) r
            = addEdge` synl.syn_nid synr.syn_nid pat synr.syn_graph
      in  mkSynExpr` (withTwo mkBinApp` (abort "Should not happen: invalid binary application") app.app_args)
    mkParApp appargs join g
      # synsplit    = addNode` GParallelSplit g
      # (g`, nids)  = foldr (f synsplit.syn_nid) (synsplit.syn_graph, []) appargs
      # synjoin     = addNode` join g`
      = mkSynExpr` (foldr (\n g_ -> addEdge` (Just n) synjoin.syn_nid Nothing g_) g` [n_ \\ Just n_ <- nids])
      where
      f splitId e (gx, xs)
        # synx  = exprCata (mkGraphAlg {inh & inh_graph = gx}) e
        # g     = addEdge` splitId synx.syn_nid Nothing synx.syn_graph
        = (g, [synx.syn_nid : xs])
    mkParBinApp appargs join g =
      withTwo  (\l r -> mkParApp [l, r] join g)
               (abort "Should not happen: invalid binary application") appargs
  letC lt
    # syn1  = addNode` (GLet (mkGLet lt)) inh.inh_graph
    // TODO: Represent the bindings in any way possible, not just PP
    # syn2  = exprCata (mkGraphAlg {inh & inh_graph = syn1.syn_graph}) lt.let_expr
    # g     = addEdge` syn1.syn_nid syn2.syn_nid Nothing syn2.syn_graph
    = mkSynExpr syn1.syn_nid g // TODO: Correct gid?

  caseC cs
    # (ni, g) = addNode` (GDecision CaseDecision (mkPretty cs.case_expr)) inh.inh_graph // TODO: Add edges
    = mkSynExpr` (mkDecision CaseDecision cs.case_expr (mkAlts cs))
    where
    mkAlts cs = mkAlts` cs.case_guards ++ optional [] (\e -> [("_", e)]) cs.case_default
    mkAlts` (AlgebraicPatterns _ aps)  = map (\ap -> (mkAp ap.ap_symbol ap.ap_vars, ap.ap_expr)) aps
      where
      mkAp sym []   = mkPretty sym.glob_object.ds_ident
      mkAp sym vars = ('PP'.display o 'PP'.renderCompact) (pretty sym.glob_object.ds_ident 'PP'. <+> pretty vars)
    mkAlts` (BasicPatterns _ bps)      = map (\bp -> (mkPretty bp.bp_value, bp.bp_expr)) bps

  condC c
    # if_else = fromOptional (abort "`if` should have two branches") c.if_else
    = mkSynExpr` (mkDecision IfDecision c.if_cond [("True", c.if_then), ("False", if_else)])

  mkDecision dt expr alts
    # (ni, g) = addNode (GDecision dt (mkPretty expr)) inh.inh_graph
    = foldr (f ni) g alts
    where
    f ni (lbl, e) gx
      # synx = exprCata (mkGraphAlg {inh & inh_graph = gx}) e
      = addEdge` (Just ni) synx.syn_nid (Just lbl) synx.syn_graph

  in
  {  mkExprAlg (mkSynExpr` inh.inh_graph)
  &  app = appC, letE = letC, caseE = caseC, conditional = condC
  }

defaultEdge :: GEdge
defaultEdge = {GEdge | edge_pattern = Nothing }

addDefaultEdge :: (Int, Int) GinGraph -> GinGraph
addDefaultEdge e g = addEdge defaultEdge e g

addEdge` :: (Maybe Int) (Maybe Int) (Maybe String) GinGraph -> GinGraph
addEdge` (Just l)  (Just r)  ep  g  = addEdge {edge_pattern = ep} (l, r) g
addEdge` Nothing   Nothing   _   _  = abort "Invalid edge: both nodes missing"
addEdge` Nothing   _         _   _  = abort "Invalid edge: source node missing"
addEdge` _         Nothing   _   _  = abort "Invalid edge: target node missing"

addNode` :: GNode GinGraph -> SynExpression
addNode` node graph
  # (n, g) = addNode node graph
  = mkSynExpr (Just n) g

mkPretty :: (a -> String) | Pretty a
mkPretty = 'PP'.display o 'PP'.renderCompact o pretty

funToGraph :: FunDef {#FunDef} IclModule {#DclModule} -> Optional (GGraph, Int, Int)
funToGraph {fun_ident=fun_ident, fun_body = TransformedBody tb} fun_defs icl_module dcl_modules
  # (soid, g)  = addNode GInit emptyGraph // TODO: Do this afterwards instead? Would allow us to use the source/sink stuff
  # (siid, g)  = addNode GStop g
  = Yes (GGraph (mkBody soid siid g), soid, siid)
  where
  mkBody soid siid g // TODO cb.cb_args
    # inh  = mkInhExpr fun_defs icl_module dcl_modules g soid siid fun_ident.id_name
    # syn  = exprCata (mkGraphAlg inh) tb.tb_rhs
    # g    = syn.syn_graph
    # g    = if (isEmpty syn.syn_rec_nodes) g (addRecs syn.syn_rec_nodes g)
    = maybe g (addNewSource g soid) (sourceNode g)

  addRecs recs g
    # (nid, g`) = addNode GMerge g
    = foldr (\n -> addEdge defaultEdge (nid, n)) g` recs

  addNewSource g newSource oldSource = addEdge defaultEdge (newSource, oldSource) g

funToGraph _ _ _ _ = No

:: GPattern :== String

mkGLet :: Let -> GLet
mkGLet lt =
  {  GLet
  |  glet_strict_binds  = map mkGLetBinds lt.let_strict_binds
  ,  glet_lazy_binds    = map mkGLetBinds lt.let_lazy_binds
  ,  glet_expr          = lt.let_expr
  }

mkGLetBinds :: LetBind -> GLetBind
mkGLetBinds lb =
  {  GLetBind
  |  glb_dst = mkPretty lb.lb_dst
  ,  glb_src = lb.lb_src
  }

:: GLet =
  {  glet_strict_binds   :: ![GLetBind]
  ,  glet_lazy_binds     :: ![GLetBind]
  ,  glet_expr           :: !Expression
  }

:: GLetBind =
  {  glb_dst       :: !String
  ,  glb_src       :: !Expression
  }

:: DecisionType = IfDecision | CaseDecision

:: GNode
  =  GInit
  |  GStop
  |  GDecision DecisionType !GCleanExpression
  |  GMerge
  |  GLet GLet
  |  GParallelSplit
  |  GParallelJoin GJoinType
  |  GTaskApp GIdentifier ![GExpression]
  |  GReturn !GExpression
  |  GAssign GCleanExpression
  |  GStep

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

:: GJoinType
  =  DisFirstBin
  |  DisFirstList
  |  DisLeft
  |  DisRight
  |  ConAll
  |  ConPair

:: GEdge = { edge_pattern :: !Maybe GPattern }

:: GGraph = GGraph GinGraph

from PPrint import class Pretty(..), instance Pretty [a], :: Doc
import qualified PPrint as PP

instance Pretty Expression where
  pretty expr = exprCata prettyAlg expr

instance Pretty Ident where
  pretty i = 'PP'.text i.id_name

instance Pretty BoundVar where
  pretty bv = pretty bv.var_ident

instance Pretty FreeVar where
  pretty fv = pretty fv.fv_ident

instance Pretty SymbIdent where
  pretty si = pretty si.symb_ident

instance Pretty BasicValue where
  pretty (BVI str)  = 'PP'.text str
  pretty (BVInt i)  = 'PP'.int i
  pretty (BVC str)  = 'PP'.text str
  pretty (BVB b)    = 'PP'.bool b
  pretty (BVR str)  = 'PP'.text str
  pretty (BVS str)  = 'PP'.text str

instance Pretty String where
  pretty str = 'PP'.text str

prettyAlg :: ExpressionAlg Doc
prettyAlg =
  let
    varC bv = pretty "(Var)" 'PP'. <+> pretty bv
    appC app
      # args = foldr (\x xs -> pretty x 'PP'. <+> xs) 'PP'.empty app.app_args
      | length app.app_args > 0  = pretty "(App)" 'PP'. <+> pretty app.app_symb 'PP'. <+> args
      | otherwise                = pretty "(App)" 'PP'. <+> pretty app.app_symb
    defaultC = 'PP'.empty
  in {mkExprAlg 'PP'.empty & var = varC, app = appC }


getNodeData` :: Int GinGraph -> GNode
getNodeData` n g = fromMaybe err (getNodeData n g)
  where err = abort ("No data for node " +++ toString n)

mkTaskDot :: String Int Int GGraph -> String
mkTaskDot funnm startid endid (GGraph g) = "digraph " +++ funnm +++ " {\n" +++
  mkNodes +++ "\n" +++
  mkEdges +++ "\n}"
  where
  mkNodes = concatStrings (map (nodeToDot g) (nodeIndices g))
  mkEdges = concatStrings (map edgeToDot (edgeIndices g))
  edgeToDot ei=:(l, r) = mkDotNodeLbl l +++ " -> " +++ mkDotNodeLbl r +++ mkDotArgs [mkDotAttrKV "label" edgeLbl] // TODO: Use different arrow for task assignment
    where edgeLbl = maybe "" (\e -> fromMaybe "" e.edge_pattern) $ getEdgeData ei g

mkDotAttrKV :: String String -> String
mkDotAttrKV k v = k +++ "=" +++ "\"" +++ v +++ "\""

mkDotArgs :: [String] -> String
mkDotArgs attrs = " [" +++ concatStrings (intersperse ", " attrs) +++ "];\n"

mkDotNodeLbl :: Int -> String
mkDotNodeLbl n = "node" +++ toString n

nodeToDot :: GinGraph Int -> String
nodeToDot g currIdx =
  case currNode of
    GInit                 -> blackNode [shape "triangle"]
    GStop                 -> blackNode [shape "box"]
    (GDecision _ expr)    -> whiteNode [shape "diamond", label expr]
    GMerge                -> blackNode [shape "diamond", width ".25", height ".25"]
    (GLet glt)            -> whiteNode [shape "box", label "(let expr goes here)"] // TODO: Rounded corners
    GParallelSplit        -> whiteNode [shape "circle", label "Parallel split"]
    (GParallelJoin jt)    -> whiteNode [shape "circle", label (mkJoinLbl jt)]
    (GTaskApp tid exprs)  -> whiteNode [shape "box", label tid] // TODO: complex contents with extra bar
    (GReturn expr)        -> whiteNode [shape "oval", label "(return expression goes here)"]
    (GAssign usr)         -> let  idxStr = toString currIdx
                                  usrStr = "user" +++ idxStr
                             in   "subgraph clusterUser" +++ idxStr +++ "{ label=" +++ usr +++ "; labelloc=b; peripheries=0; " +++ usrStr +++ "}" +++
                                  usrStr +++ mkDotArgs [ mkDotAttrKV "shapefile" "\"stick.png\""
                                                       , mkDotAttrKV "peripheries" "0"
                                                       , style "invis" ]
    GStep                 -> whiteNode [shape "circle", label "Step"]
  where
  currNode         = getNodeData` currIdx g
  whiteNode attrs  = mkDotNode [fontcolor "black", fillcolor "white", style "filled", label "" : attrs]
  blackNode attrs  = mkDotNode [fontcolor "white", fillcolor "black", style "filled", label "" : attrs]
  mkDotNode attrs  = mkDotNodeLbl currIdx +++ mkDotArgs attrs
  shape v      = mkDotAttrKV "shape" v
  label v      = mkDotAttrKV "label" v
  color v      = mkDotAttrKV "color" v
  fillcolor v  = mkDotAttrKV "fillcolor" v
  fontcolor v  = mkDotAttrKV "fontcolor" v
  width v      = mkDotAttrKV "width" v
  height v     = mkDotAttrKV "height" v
  style v      = mkDotAttrKV "style" v
  mkJoinLbl DisFirstBin   = "First result from two tasks"
  mkJoinLbl DisFirstList  = "First result from list of tasks"
  mkJoinLbl DisLeft       = "Left result"
  mkJoinLbl DisRight      = "Right result"
  mkJoinLbl ConAll        = "All results"
  mkJoinLbl ConPair       = "Pair of results"


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
concatStrings :: [String] -> .String
concatStrings l = updateS 0 l (createArray (sum [size s \\ s <- l]) ' ')
  where
    updateS :: !Int [{#Char}] *{#Char} -> *{#Char}
    updateS i [] s
      =  s
    updateS i [h : t] s
      =  updateS (i + size h) t {s & [pos] = c \\ c <-: h & pos <- [i..]}

intersperse :: a [a] -> [a]
intersperse i []      = []
intersperse i [x]     = [x]
intersperse i [x:xs]  = [x,i:intersperse i xs]

// TODO: Everything below is copied from other modules. It should eventually be
// removed.

// FIXME Copied from GiN Syntax.dcl
//:: GNode =
  //{  identifier   :: !GResourceId
  //,  name         :: !GIdentifier
  //,  actualParams :: ![GExpression]
  //,  visible      :: !Bool
  //,  nodeType     :: !GNodeType
  //,  position     :: !GPosition
  //}


//:: GEdge =
  //{  identifier :: !GResourceId
  //,  pattern    :: !Maybe GPattern
  //}


:: GResourceId :== String
//:: GPosition =
  //{ x :: Real
  //, y :: Real
  //}
:: GExpression
  =  GUndefinedExpression
  |  GGraphExpression GGraph
  |  GListExpression [GExpression]
  |  GListComprehensionExpression GListComprehension
  |  GCleanExpression GCleanExpression

:: GCleanExpression :== String

:: GListComprehension =
  {  output    :: GExpression
  ,  guard     :: Maybe GCleanExpression
  ,  selector  :: GPattern
  ,  input     :: GExpression
  }

:: GModuleKind
  =  GCleanModule Bindings
  //|  GGraphicalModule [GDefinition]

// Graph definition
:: GModule =
  { name        :: GIdentifier
  , types       :: [GTypeDefinition]
  , moduleKind  :: GModuleKind
  , imports     :: [GImport]
  }

:: GImport :== String

:: Bindings :== [Binding]

:: Binding = NodeBinding NodeBinding | ParallelBinding ParallelBinding

:: NodeBinding =
  { declaration  :: GDeclaration
  , parameterMap :: NBParameterMap
  }

:: NBParameterMap
  = NBBuiltIn
  | NBPrefixApp
  | NBInfixApp //AFix APrecedence

:: ParallelBinding =
  { split           :: GDeclaration
  , merge           :: GDeclaration
  , type            :: GTypeExpression
  , fixedNrBranches :: Maybe Int
  //, parameterMap    :: AExpression PBParameter
  }

//:: PBParameter
  //= PBSplitParameter ParameterPosition
  //| PBMergeParameter ParameterPosition
  //| PBBranch BranchPosition
  //| PBBranchList

:: ParameterPosition :== Int
:: BranchPosition :== Int

:: GDeclaration =
  { name                :: GIdentifier
  , title               :: Maybe String
  , description         :: Maybe String
  , formalParams        :: [GFormalParameter]
  , returnType          :: GTypeExpression
  , returnDescription   :: Maybe String
  }

//:: GDefinition =
  //{ declaration :: GDeclaration
  //, body        :: ORYXDiagram
  //}


// FIXME Copied from GiN Types.dcl
:: GIdentifier :== String
:: GTypeDefinition =
  { name :: GIdentifier
  , rhs  :: GTypeRhs
  }

:: GTypeRhs
  = GAlgebraicTypeRhs [GDataConstructor]
  | GRecordTypeRhs [GRecordField]
  | GSynonymTypeRhs GTypeExpression
  | GAbstractTypeRhs

:: GDataConstructor =
  { name      :: GIdentifier
  , arguments :: [GTypeExpression]
  }

:: GRecordField =
  { name :: GIdentifier
  , type :: GTypeExpression
  }

:: GTypeExpression
  = GConstructor GIdentifier
  | GList GTypeExpression
  | GTuple [GTypeExpression]
  | GTypeApplication [GTypeExpression]
  | GTypeVariable GTypeVariable
  | GFunction GTypeExpression GTypeExpression
  | GUndefinedTypeExpression

:: GTypeVariable :== String

:: GFormalParameter =
  { name          :: GIdentifier
  , title         :: Maybe String
  , description   :: Maybe String
  , type          :: GTypeExpression
  , defaultValue  :: Maybe String
  , visible       :: Bool
  }
