implementation module GinTonic

// Task Oriented Notation Illustrated on a Canvas

import syntax, checksupport, StdFile
from CoclSystemDependent import DirectorySeparator, ensureCleanSystemFilesExists

//import tonic

from PPrint import class Pretty(..), instance Pretty [a], :: Doc
import qualified PPrint as PP

import Func, Functor, Graph, Maybe, Text
from List import zipWith
import StdDebug

ginTonic :: IclModule {#DclModule} *FrontendTuple !*Files -> *(*FrontendTuple, !*Files)
ginTonic icl_module dcl_modules tpl files
  # iclname                = icl_module.icl_name.id_name
  | isSystemModule iclname = (tpl, files)
  # (ok, files)            = ensureCleanSystemFilesExists csf_directory_path files
  # (ok, tonicf, files)    = fopen (csf_directory_path +++ {DirectorySeparator} +++ ("tonic-" +++ iclname +++ ".dot")) FWriteText files
  # (tstr, tpl)            = ginTonic` icl_module dcl_modules tpl
  //| True = abort tstr
  # tonicf                 = fwrites tstr tonicf
  # (ok, files)            = fclose tonicf files
  = (tpl, files)
  where
  csf_directory_path = "Clean System Files"
  isSystemModule nm = isSystemModule` ["iTasks", "Std", "_"]
    where isSystemModule` = foldr (\x b -> startsWith x nm || b) False

foldrArr :: (a b -> b) b (arr a) -> b | Array arr a
foldrArr f b arr = foldrArr` 0 f b arr
  where
  arrSz = size arr
  foldrArr` n f b arr
    | n < arrSz  = f (select arr n) (foldrArr` (n + 1) f b arr)
    | otherwise  = b

ginTonic` :: IclModule {#DclModule} *FrontendTuple -> *(String, *FrontendTuple)
ginTonic` icl_module dcl_modules tpl=:(ok, fun_defs, array_instances, common_defs, imported_funs, type_def_infos, heaps, predef_symbols, error,out)
  = (mkDotGraph $ foldrArr appDefInfo "" fun_defs, tpl)
  where
  appDefInfo fd rest
    | funIsTask fd && fd.fun_info.fi_def_level == 1  = defToStr fd +++ "\n" +++ rest
    | otherwise                                      = rest
  defToStr fd  = optional "Nothing happened" f (funToGraph fd fun_defs icl_module dcl_modules)
    where f (g, so, si) = mkTaskDot (mkInhExpr fun_defs icl_module dcl_modules emptyGraph 0 0 0 "" Nothing) fd.fun_ident.id_name so si g
  mkDotGraph subgraphs = "digraph " +++ icl_module.icl_name.id_name +++ "{\n" +++ subgraphs +++ "\n}"

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

numFunArgs :: GFunDef -> Int
numFunArgs fd = length fd.gfd_args

funIsTask :: FunDef -> Bool
funIsTask fd =
  case (fd.fun_type, fd.fun_kind) of
    (Yes st, FK_Function _)  -> symTyIsTask st
    _                        -> False

symbIdentIsLam :: SymbIdent -> Bool
symbIdentIsLam si = identIsLam si.symb_ident

identIsLam :: Ident -> Bool
identIsLam ident
  | size fnm > 0  = fnm.[0] == '\\'
  | otherwise     = False
  where fnm = ident.id_name

exprIsLam :: Expression -> Bool
exprIsLam (Var bv)  = identIsLam bv.var_ident
exprIsLam _         = False

symTyIsTask :: SymbolType -> Bool
symTyIsTask st =
  case st.st_result.at_type of
    TA   tsi _     -> symTyIsTask` tsi
    TAS  tsi _  _  -> symTyIsTask` tsi
    _              -> False
  where symTyIsTask` tsi = tsi.type_ident.id_name == "Task"

identIsTask :: {#FunDef} {#DclModule} Ident -> Bool
identIsTask fun_defs dcl_modules ident =
  maybe False symTyIsTask $ reifySymbolType fun_defs dcl_modules ident

findInArr :: (e -> Bool) (a e) -> Maybe e | Array a e
findInArr p arr = findInArr` 0 p arr
  where
  arrSz = size arr
  findInArr` n p arr
    | n < arrSz
      #  elem = select arr n
      =  if (p elem) (Just elem) (findInArr` (n + 1) p arr)
    | otherwise  = Nothing

isInfix :: {#FunDef} IclModule {#DclModule} SymbIdent -> Bool
isInfix fun_defs icl_module dcl_modules si
  # mfd = reifyFunDef fun_defs icl_module si.symb_ident
  # mft = reifyFunType dcl_modules si.symb_ident
  = maybe (maybe (abort "Failed to determine fixity") (\ft -> isInfix` ft.ft_priority) mft) (\fd -> isInfix` fd.gfd_priority) mfd
  where
  isInfix` prio =
    case prio of
      Prio _ _  -> True
      _         -> False

reifyFunType :: {#DclModule} Ident -> Maybe FunType
reifyFunType dcl_modules ident =
  safeHead  [  ft \\ dcl <-: dcl_modules, ft <-: dcl.dcl_functions
            |  ft.ft_ident.id_name == ident.id_name
            ]

reifyFunDef :: {#FunDef} IclModule Ident -> Maybe GFunDef
reifyFunDef fun_defs icl_module ident =
  case findInFunDefs fun_defs of
    Just fd  -> Just $ mkGFunDef fd
    _        -> fmap mkGFunDef $ findInFunDefs icl_module.icl_functions
  where
  identName = ident.id_name
  findInFunDefs fds = findInArr (\fd -> fd.fun_ident.id_name == identName) fds

reifySymbolType :: {#FunDef} {#DclModule} Ident -> Maybe SymbolType
reifySymbolType fun_defs dcl_modules ident =
  case findInArr (\fd -> fd.fun_ident.id_name == ident.id_name) fun_defs of
    Just fd  -> optional findInDcls Just fd.fun_type
    _        -> findInDcls
  where
  findInDcls = maybe Nothing (\ft -> Just ft.ft_type) (reifyFunType dcl_modules ident)

/*
TODO:
GiN does not do eta-reduction. I.e., it only supports either a `f >>= \x -> e`
or `f >>| e` bind, but never a `f >>= g` bind. If we want to support the
latter, we must eta-expand `g`.
*/

//:: ExpressionAlg a =
  //{  var                   :: BoundVar -> a                                                 // Var
  //,  app                   :: App -> a                                                      // App
  //,  at                    :: a [a] -> a                                                    // (@)
  //,  letE                  :: Let -> a                                                      // Let
  //,  caseE                 :: Case -> a                                                     // Case
  //,  selection             :: SelectorKind a [Selection] -> a                               // Selection
  //,  update                :: a [Selection] a -> a                                          // Update
  //,  recordUpdate          :: (Global DefinedSymbol) a [Bind a (Global FieldSymbol)] -> a   // RecordUpdate
  //,  tupleSelect           :: DefinedSymbol Int a -> a                                      // TupleSelect
  //,  basicExpr             :: BasicValue -> a                                               // BasicExpr
  //,  conditional           :: Conditional -> a                                              // Conditional
  //,  anyCodeExpr           :: (CodeBinding BoundVar) (CodeBinding FreeVar) [String] -> a    // AnyCodeExpr
  //,  abcCodeExpr           :: [String] Bool -> a                                            // ABCCodeExpr
  //,  matchExpr             :: (Global DefinedSymbol) a -> a                                 // MatchExpr
  //,  isConstructor         :: a (Global DefinedSymbol) Int GlobalIndex Ident Position -> a  // IsConstructor
  //,  freeVar               :: FreeVar -> a                                                  // FreeVar
  //,  dictionariesFunction  :: [(FreeVar,AType)] a AType -> a                                // DictionariesFunction
  //,  constant              :: SymbIdent Int Priority -> a                                   // Constant
  //,  classVariable         :: VarInfoPtr -> a                                               // ClassVariable
  //,  dynamicExpr           :: DynamicExpr -> a                                              // DynamicExpr
  //,  typeCodeExpression    :: TypeCodeExpression -> a                                       // TypeCodeExpression
  //,  typeSignature         :: (Int Int -> (AType,Int,Int)) a -> a                           // TypeSignature
  //,  ee                    :: a                                                             // EE
  //,  noBind                :: ExprInfoPtr -> a                                              // NoBind
  //,  failExpr              :: Ident -> a                                                    // FailExpr
  //}

//exprCata :: (ExpressionAlg a) Expression -> a
//exprCata alg (Var bv                      ) = alg.var bv
//exprCata alg (App a                       ) = alg.app a
//exprCata alg (l @ rs                      ) = alg.at (exprCata alg l) (map (exprCata alg) rs)
//exprCata alg (Let l                       ) = alg.letE l
//exprCata alg (Case c                      ) = alg.caseE c
//exprCata alg (Selection sk e ss           ) = alg.selection sk (exprCata alg e) ss
//exprCata alg (Update e1 ss e2             ) = alg.update (exprCata alg e1) ss (exprCata alg e2)
//exprCata alg (RecordUpdate gd e bs        ) = alg.recordUpdate gd (exprCata alg e) (map (\b -> {b & bind_src=exprCata alg b.bind_src}) bs)
//exprCata alg (TupleSelect ds i e          ) = alg.tupleSelect ds i (exprCata alg e)
//exprCata alg (BasicExpr bv                ) = alg.basicExpr bv
//exprCata alg (Conditional c               ) = alg.conditional c
//exprCata alg (AnyCodeExpr cb cf ss        ) = alg.anyCodeExpr cb cf ss
//exprCata alg (ABCCodeExpr ss b            ) = alg.abcCodeExpr ss b
//exprCata alg (MatchExpr gd e              ) = alg.matchExpr gd (exprCata alg e)
//exprCata alg (IsConstructor e gd n gi i p ) = alg.isConstructor (exprCata alg e) gd n gi i p
//exprCata alg (FreeVar v                   ) = alg.freeVar v
//exprCata alg (DictionariesFunction xs e at) = alg.dictionariesFunction xs (exprCata alg e) at
//exprCata alg (Constant si i prio          ) = alg.constant si i prio
//exprCata alg (ClassVariable vip           ) = alg.classVariable vip
//exprCata alg (DynamicExpr de              ) = alg.dynamicExpr de
//exprCata alg (TypeCodeExpression t        ) = alg.typeCodeExpression t
//exprCata alg (TypeSignature f e           ) = alg.typeSignature f (exprCata alg e)
//exprCata alg (EE                          ) = alg.ee
//exprCata alg (NoBind eip                  ) = alg.noBind eip
//exprCata alg (FailExpr i                  ) = alg.failExpr i

:: ExpressionAlg a =
  {  var                   :: BoundVar -> a                                                                  // Var
  ,  app                   :: App -> a                                                                       // App
  ,  at                    :: Expression [Expression] -> a                                                   // (@)
  ,  letE                  :: Let -> a                                                                       // Let
  ,  caseE                 :: Case -> a                                                                      // Case
  ,  selection             :: SelectorKind Expression [Selection] -> a                                       // Selection
  ,  update                :: Expression [Selection] Expression -> a                                         // Update
  ,  recordUpdate          :: (Global DefinedSymbol) Expression [Bind Expression (Global FieldSymbol)] -> a  // RecordUpdate
  ,  tupleSelect           :: DefinedSymbol Int Expression -> a                                              // TupleSelect
  ,  basicExpr             :: BasicValue -> a                                                                // BasicExpr
  ,  conditional           :: Conditional -> a                                                               // Conditional
  ,  anyCodeExpr           :: (CodeBinding BoundVar) (CodeBinding FreeVar) [String] -> a                     // AnyCodeExpr
  ,  abcCodeExpr           :: [String] Bool -> a                                                             // ABCCodeExpr
  ,  matchExpr             :: (Global DefinedSymbol) Expression -> a                                         // MatchExpr
  ,  isConstructor         :: Expression (Global DefinedSymbol) Int GlobalIndex Ident Position -> a          // IsConstructor
  ,  freeVar               :: FreeVar -> a                                                                   // FreeVar
  ,  dictionariesFunction  :: [(FreeVar,AType)] Expression AType -> a                                        // DictionariesFunction
  ,  constant              :: SymbIdent Int Priority -> a                                                    // Constant
  ,  classVariable         :: VarInfoPtr -> a                                                                // ClassVariable
  ,  dynamicExpr           :: DynamicExpr -> a                                                               // DynamicExpr
  ,  typeCodeExpression    :: TypeCodeExpression -> a                                                        // TypeCodeExpression
  ,  typeSignature         :: (Int Int -> (AType,Int,Int)) Expression -> a                                   // TypeSignature
  ,  ee                    :: a                                                                              // EE
  ,  noBind                :: ExprInfoPtr -> a                                                               // NoBind
  ,  failExpr              :: Ident -> a                                                                     // FailExpr
  }

exprCata :: (ExpressionAlg a) Expression -> a
exprCata alg (Var bv                      ) = alg.var bv
exprCata alg (App a                       ) = alg.app a
exprCata alg (l @ rs                      ) = alg.at l rs
exprCata alg (Let l                       ) = alg.letE l
exprCata alg (Case c                      ) = alg.caseE c
exprCata alg (Selection sk e ss           ) = alg.selection sk e ss
exprCata alg (Update e1 ss e2             ) = alg.update e1 ss e2
exprCata alg (RecordUpdate gd e bs        ) = alg.recordUpdate gd e bs
exprCata alg (TupleSelect ds i e          ) = alg.tupleSelect ds i e
exprCata alg (BasicExpr bv                ) = alg.basicExpr bv
exprCata alg (Conditional c               ) = alg.conditional c
exprCata alg (AnyCodeExpr cb cf ss        ) = alg.anyCodeExpr cb cf ss
exprCata alg (ABCCodeExpr ss b            ) = alg.abcCodeExpr ss b
exprCata alg (MatchExpr gd e              ) = alg.matchExpr gd e
exprCata alg (IsConstructor e gd n gi i p ) = alg.isConstructor e gd n gi i p
exprCata alg (FreeVar v                   ) = alg.freeVar v
exprCata alg (DictionariesFunction xs e at) = alg.dictionariesFunction xs e at
exprCata alg (Constant si i prio          ) = alg.constant si i prio
exprCata alg (ClassVariable vip           ) = alg.classVariable vip
exprCata alg (DynamicExpr de              ) = alg.dynamicExpr de
exprCata alg (TypeCodeExpression t        ) = alg.typeCodeExpression t
exprCata alg (TypeSignature f e           ) = alg.typeSignature f e
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
  ,  inh_init_id         :: !Int
  ,  inh_stop_id         :: !Int
  ,  inh_merge_id        :: !Int
  ,  inh_curr_task_name  :: !String
  ,  inh_case_expr       :: !Maybe Expression
  }

:: SynExpression =
  {  syn_nid        :: !Maybe Int
  ,  syn_graph      :: !GinGraph
  ,  syn_has_recs   :: !Bool
  ,  syn_rec_node   :: !Bool
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
  ,  syn_has_recs   = False
  ,  syn_rec_node   = False
  }

mkSynExpr` :: GinGraph -> SynExpression
mkSynExpr` gr = mkSynExpr Nothing gr

mkInhExpr :: {#FunDef} IclModule {#DclModule} GinGraph Int Int Int String (Maybe Expression) -> InhExpression
mkInhExpr fun_defs icl_module dcl_modules gg initId stopId mergeId nm ce =
  {  InhExpression
  |  inh_fun_defs        = fun_defs
  ,  inh_icl_module      = icl_module
  ,  inh_dcl_modules     = dcl_modules
  ,  inh_graph           = gg
  ,  inh_init_id         = initId
  ,  inh_stop_id         = stopId
  ,  inh_merge_id        = mergeId
  ,  inh_curr_task_name  = nm
  ,  inh_case_expr       = ce
  }

withHead :: (a -> b) b [a] -> b
withHead _  b  []       = b
withHead f  _  [x : _]  = f x

safeHead :: [a] -> Maybe a
safeHead []    = Nothing
safeHead [x:_] = Just x

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

edgeErr :: InhExpression String (Maybe Int) Expression (Maybe Int) Expression -> a
edgeErr inh errmsg lid lexpr rid rexpr = abort ("Cannot create " +++ errmsg
  +++ " between left expression\n\t" +++ nodeErr inh lid lexpr
  +++ " and right expression\n\t" +++ nodeErr inh rid rexpr +++ "\n")

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

dropContexts :: SymbolType [a] -> [a]
dropContexts st xs
  # lst = numContexts st
  | lst > length xs = xs
  = drop lst xs

numContexts :: SymbolType -> Int
numContexts st = length st.st_context

connectId :: InhExpression SynExpression -> (Maybe Int, SynExpression)
connectId inh syn
  | syn.syn_rec_node  = (Just inh.inh_merge_id, { syn & syn_rec_node = False })
  | otherwise         = (syn.syn_nid, syn)

persistHasRec :: [SynExpression] SynExpression -> SynExpression
persistHasRec ss syn = { syn & syn_has_recs = has }
 where has = foldr (\s b -> s.syn_has_recs || b) False ss

// TODO: Check if we need more connectId applications
mkGraphAlg :: InhExpression -> ExpressionAlg SynExpression
mkGraphAlg inh =
  let
  appC app
    | identIsTask inh.inh_fun_defs inh.inh_dcl_modules app.app_symb.symb_ident =
        case appFunName app of // TODO `parallel`
          ">>="       -> mkBind app inh.inh_graph
          "return"    -> mkReturn app inh.inh_graph
          ">>|"       -> mkBinApp app Nothing inh.inh_graph
          "@:"        -> mkAssign app inh.inh_graph
          ">>*"       -> mkStep app inh.inh_graph
          "-||-"      -> mkParBinApp app.app_args DisFirstBin inh.inh_graph
          "||-"       -> mkParBinApp app.app_args DisRight inh.inh_graph
          "-||"       -> mkParBinApp app.app_args DisLeft inh.inh_graph
          "-&&-"      -> mkParBinApp app.app_args ConPair inh.inh_graph
          "anyTask"   -> mkParApp app.app_args DisFirstList inh.inh_graph
          "allTasks"  -> mkParApp app.app_args ConAll inh.inh_graph
          _           -> mkTaskApp app inh.inh_graph
    | otherwise               = mkSynExpr` inh.inh_graph
    where
    mkBind app g // TODO: Take dictionary into account
    // TODO: Rework
    // The second element of the list is _not_ the lambda variable, but the
    // reference to the entire lifted lambda expression. (assuming it is even
    // a lambda expression).
    // In case of a lambda expression, we first need to reify the function and
    // do the rest there.
    // In case of a function...?

    // TODO: Check with funIsLam if the right-hand function is a lambda. If so,
    // do what we currently do and reify the lambda and continue graph generation.
    // If not, don't reify and just generate a task application node and be done.
      # funTy      = fromMaybe (abort "mkGraphAlg: failed to find symbol type (1)") 
                   $ reifySymbolType inh.inh_fun_defs inh.inh_dcl_modules app.app_symb.symb_ident
      # nodictargs = dropContexts funTy app.app_args
      # (lhsExpr, rhsApp) =
          case nodictargs of
            [e:App rhsApp:_]  -> (e, rhsApp)
            _                 -> abort ("Invalid bind: " +++ concatStrings (intersperse " " $ map (\x -> "'" +++ mkPretty inh x +++ "'") nodictargs))
      # rhsfd  = fromMaybe (abort $ "mkGraphAlg #1: failed to find function definition for " +++ mkPretty inh rhsApp.app_symb)
               $ reifyFunDef inh.inh_fun_defs inh.inh_icl_module rhsApp.app_symb.symb_ident
      # rhsTy  = fromMaybe (abort $ "mkGraphAlg #2: failed to find symbol type for " +++ mkPretty inh rhsApp.app_symb)
               $ reifySymbolType inh.inh_fun_defs inh.inh_dcl_modules rhsApp.app_symb.symb_ident
      # patid  = withHead freeVarName (abort "Invalid bind") $ dropContexts rhsTy rhsfd.gfd_args
      # synl   = exprCata (mkGraphAlg inh) lhsExpr
      # synr   = exprCata (mkGraphAlg {inh & inh_graph = synl.syn_graph}) rhsfd.gfd_rhs
      = case (synl.syn_nid, synr.syn_nid) of
          (Just l, Just r)  -> persistHasRec [synl, synr] $ mkSynExpr synl.syn_nid $ addEdge (mkEdge patid) (l, r) synr.syn_graph // TODO: Is this always the correct node id to synthesize?
          (lid, rid)        -> edgeErr inh "bind edge" lid lhsExpr rid rhsfd.gfd_rhs

    mkReturn app g // TODO: Take dictionary into account
      # funTy  = fromMaybe (abort $ "mkGraphAlg #3: failed to find symbol type for " +++ mkPretty inh app.app_symb)
               $ reifySymbolType inh.inh_fun_defs inh.inh_dcl_modules app.app_symb.symb_ident
      # node   = GReturn $ withHead f (abort "Invalid return") $ dropContexts funTy app.app_args
      = addNode` node g
      where
      // In case of a function application, we want to inspect the type of the
      // function. If it is a task or a list, treat it differently than any
      // other type. But how can we get the type of an arbitrary expression?
      f (BasicExpr bv)  = GCleanExpression $ mkPretty inh bv
      f (Var bv)        = GCleanExpression bv.var_ident.id_name
      f e               = GGraphExpression (GGraph (exprCata (mkGraphAlg {inh & inh_graph = g}) e).syn_graph)

    mkAssign app g =
      let mkAssign` u t
            # (lid, g)  = addNode (GAssign (mkPretty inh u)) g
            # synt      = exprCata (mkGraphAlg {inh & inh_graph = g}) t
            = maybe (err lid) (\r -> persistHasRec [synt] $ mkSynExpr` (addEdge emptyEdge (lid, r) synt.syn_graph)) synt.syn_nid
            where
            err lid = edgeErr inh "assign edge" (Just lid) u Nothing t
      in withTwo mkAssign` (abort "Illegal task assignment") app.app_args

    mkStep app g = mkSynExpr` g // TODO
    mkTaskApp app g
      | appFunName app == inh.inh_curr_task_name  = mkRec
      | otherwise                                 = mkTask
      where
      mkRec = { mkSynExpr` g & syn_has_recs = True, syn_rec_node = True }
      mkTask
        # appArgs  = map (GCleanExpression o (mkPretty inh)) app.app_args  // TODO: When do we pprint a Clean expr? And when do we generate a subgraph?
        # (an, g)  = addNode (GTaskApp (appFunName app) appArgs) g
        = mkSynExpr (Just an) g

    mkBinApp app pat g =
      let mkBinApp` l r
            # synl = exprCata (mkGraphAlg {inh & inh_graph = g}) l
            # synr = exprCata (mkGraphAlg {inh & inh_graph = synl.syn_graph}) r
            = case (synl.syn_nid, synr.syn_nid) of
                (Just l, Just r)  -> persistHasRec [synl, synr] $ mkSynExpr` (addEdge (maybe emptyEdge mkEdge pat) (l, r) synr.syn_graph)
                (lid, rid)        -> edgeErr inh "bin app edge" lid l rid r
      in  withTwo mkBinApp` (abort "Should not happen: invalid binary application") app.app_args

    mkParApp appargs join g
      # (sid, g`)   = addNode GParallelSplit g
      # (g`, nids)  = foldr (f sid) (g`, []) appargs
      # (jid, g`)   = addNode (GParallelJoin join) g`
      = mkSynExpr (Just sid) (foldr (\n g_ -> addEdge emptyEdge (n, jid) g_) g` [n_ \\ Just n_ <- nids])
      where
      f splitId e (gx, xs)
        # synx          = exprCata (mkGraphAlg {inh & inh_graph = gx}) e
        # (mid, synx`)  = connectId inh synx
        # g             = addEdge emptyEdge (splitId, fromMaybe (abort "Failed to add split edge") mid) synx`.syn_graph
        = (g, [mid : xs])

    mkParBinApp appargs join g =
      withTwo  (\l r -> mkParApp [l, r] join g)
               (abort "Should not happen: invalid binary application") appargs


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
        let fd       = fromMaybe err $ reifyFunDef inh.inh_fun_defs inh.inh_icl_module app.app_symb.symb_ident
            letargs  = drop (length app.app_args) fd.gfd_args
            binds    = zipWith (\eVar eVal -> mkGLetBind (mkPretty inh eVar) eVal) letargs es
              //{  GLetBind
                                               //|  glb_dst = mkPretty inh eVar
                                               //,  glb_src = eVal
                                               //} ) letargs es
            err      = abort ("atC: failed to reify " +++ app.app_symb.symb_ident.id_name)
            mkRec
              # (lid, g) = addNode (GLet binds) inh.inh_graph
              # g = addEmptyEdge (lid, inh.inh_merge_id) g
              = { mkSynExpr (Just lid) g & syn_has_recs = True }
            mkAt
              # (lid, g) = addNode (GLet binds) inh.inh_graph
              = abort ("atC mkAt for gfd_name" +++ fd.gfd_name +++ " and curr_task_nm " +++ inh.inh_curr_task_name)
        in  case fd.gfd_rhs of
              App appRhs  -> if (appRhs.app_symb.symb_ident.id_name == inh.inh_curr_task_name) mkRec mkAt
              _           -> mkAt
    | otherwise    =  abort "atC: otherwise case" // TODO : pretty print function application
  atC _ _ = abort "atC: something else than App"
  //atC` e es // TODO: Do something with es
    //# fd = if (exprIsLam e) ()
    //# syne = exprCata (mkGraphAlg inh) e
    //= persistHasRec [syne] $ mkSynExpr syne.syn_nid syne.syn_graph //inh.inh_graph
//:: GLetBind =
  //{  glb_dst       :: !String
  //,  glb_src       :: !Expression
  //}
  letC lt // TODO: Special case for _case_var
    # glet         = mkGLet inh lt
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
      # g            = maybe err (\n -> addEdge emptyEdge (lid, n) syn3.syn_graph) mid
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
    mkAlts cs = mkAlts` cs.case_guards ++ optional [] (\e -> [("_", e)]) cs.case_default
    mkAlts` (AlgebraicPatterns _ aps)  = map (\ap -> (mkAp ap.ap_symbol ap.ap_vars, ap.ap_expr)) aps
      where
      mkAp sym []   = mkPretty inh sym.glob_object.ds_ident
      mkAp sym vars = ('PP'.display o 'PP'.renderCompact) (pp inh sym.glob_object.ds_ident 'PP'. <+> pp inh vars)
    mkAlts` (BasicPatterns _ bps)      = map (\bp -> (mkPretty inh bp.bp_value, bp.bp_expr)) bps

  // TODO: It appears as if conditionals are desugared to case blocks before we
  // get to them... Is this a remnant from old compiler versions?
  condC c
    # if_else = fromOptional (abort "`if` should have two branches") c.if_else
    = mkDecision IfDecision c.if_cond [("True", c.if_then), ("False", if_else)]

  mkDecision dt expr alts
    # inh     = {inh & inh_case_expr = Nothing }
    # (ni, g) = addNode (GDecision dt (mkPretty inh expr)) inh.inh_graph
    # (hr, g) = foldr (f ni) (False, g) alts
    = { mkSynExpr (Just ni) g & syn_has_recs = hr }
    where
    f ni (lbl, e) (hr, gx)
      # synx         = exprCata (mkGraphAlg {inh & inh_graph = gx}) e
      # (mid, synx)  = connectId inh synx
      =  (  synx.syn_has_recs || hr
         ,  addEdge (mkEdge lbl) (ni, fromMaybe (abort "Failed to add decision node") mid) synx.syn_graph)

  in
  {  mkExprAlg (mkSynExpr` inh.inh_graph)
  &  app = appC, at = atC, letE = letC, caseE = caseC, conditional = condC
  }

nodeErr :: InhExpression (Maybe Int) Expression -> String
nodeErr inh mn expr = mkPretty inh expr +++ "\n" +++
  maybe "for which its ID is unknown" (\n -> "with node ID " +++ toString n) mn

emptyEdge :: GEdge
emptyEdge = {GEdge | edge_pattern = Nothing }

mkEdge :: String -> GEdge
mkEdge str = {GEdge | edge_pattern = Just str }

addEmptyEdge :: (Int, Int) GinGraph -> GinGraph
addEmptyEdge e g = addEdge emptyEdge e g

addNode` :: GNode GinGraph -> SynExpression
addNode` node graph
  # (n, g) = addNode node graph
  = mkSynExpr (Just n) g

mkPretty :: InhExpression -> (a -> String) | PP a
mkPretty inh = 'PP'.display o 'PP'.renderCompact o (pp inh)

:: GFunDef =
  {  gfd_name      :: !String
  ,  gfd_args      :: ![FreeVar]
  ,  gfd_rhs       :: !Expression
  ,  gfd_type      :: !Optional SymbolType
  ,  gfd_priority  :: Priority
  }

mkGFunDef :: FunDef -> GFunDef
mkGFunDef fd=:{fun_body = TransformedBody tb} =
  {  GFunDef
  |  gfd_name      = fd.fun_ident.id_name
  ,  gfd_args      = tb.tb_args
  ,  gfd_rhs       = tb.tb_rhs
  ,  gfd_type      = fd.fun_type
  ,  gfd_priority  = fd.fun_priority
  }
mkGFunDef _ = abort "mkGFunDef: need a TransformedBody"

// TODO: We need to split this up: one part of this should generate the graph
// for the FunDef and the other part should generate the init and stop nodes.
// Yet another part should just get the right-hand side Expression of a FunDef
// so we can just cata it.
funToGraph :: FunDef {#FunDef} IclModule {#DclModule} -> Optional (GGraph, Int, Int)
funToGraph {fun_ident=fun_ident, fun_body = TransformedBody tb} fun_defs icl_module dcl_modules
  # (initId, g)   = addNode GInit emptyGraph // TODO: Do this afterwards instead? Would allow us to use the source/sink stuff
  # (stopId, g)   = addNode GStop g
  # (mergeId, g)  = addNode GMerge g
  = Yes (GGraph (mkBody initId stopId mergeId g), initId, stopId)
  where
  mkBody initId stopId mergeId g // TODO cb.cb_args
    # inh  = mkInhExpr fun_defs icl_module dcl_modules g initId stopId mergeId fun_ident.id_name Nothing
    # syn  = exprCata (mkGraphAlg inh) tb.tb_rhs
    # g    = syn.syn_graph
    # g    = if syn.syn_has_recs
               (addEdge emptyEdge (initId, mergeId) g) // TODO: Move all outgoing edges from init to merge
               (removeNode mergeId g)
    = maybe g (addNewSource g initId) (sourceNode g)

  addNewSource g newSource oldSource = addEdge emptyEdge (newSource, oldSource) g

funToGraph _ _ _ _ = No

:: GPattern :== String

mkGLet :: InhExpression Let -> GLet
mkGLet inh lt =
  {  GLet
  |  glet_binds  = map (mkGLetBinds inh) (lt.let_lazy_binds ++ lt.let_strict_binds)
  ,  glet_expr   = lt.let_expr
  }

mkGLetBind :: String Expression -> GLetBind
mkGLetBind str expr =
  {  GLetBind
  |  glb_dst = str
  ,  glb_src = expr
  }

mkGLetBinds :: InhExpression LetBind -> GLetBind
mkGLetBinds inh lb =
  {  GLetBind
  |  glb_dst = mkPretty inh lb.lb_dst
  ,  glb_src = lb.lb_src
  }

:: GLet =
  {  glet_binds  :: ![GLetBind]
  ,  glet_expr   :: !Expression
  }

:: GLetBind =
  {  glb_dst     :: !String
  ,  glb_src     :: !Expression
  }

:: DecisionType = IfDecision | CaseDecision

:: GNode
  =  GInit
  |  GStop
  |  GDecision DecisionType !GCleanExpression
  |  GMerge
  |  GLet [GLetBind]
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

class PP a where
  pp :: InhExpression a -> Doc

instance PP [a] | PP a where
  pp inh xs = 'PP'.list (map (pp inh) xs)

instance PP Expression where
  pp inh expr = exprCata (prettyAlg inh) expr
  //pp expr = exprCata debugPPAlg expr

instance PP Ident where
  pp _ i = 'PP'.text i.id_name

instance PP BoundVar where
  pp inh bv = pp inh bv.var_ident

instance PP FreeVar where
  pp inh fv = pp inh fv.fv_ident

instance PP SymbIdent where
  pp inh si = pp inh si.symb_ident

instance PP BasicValue where
  pp _ (BVI str)  = 'PP'.text str
  pp _ (BVInt i)  = 'PP'.int i
  pp _ (BVC str)  = 'PP'.text str
  pp _ (BVB b)    = 'PP'.bool b
  pp _ (BVR str)  = 'PP'.text str
  pp _ (BVS str)  = 'PP'.text str

instance PP DefinedSymbol where
  pp inh ds = pp inh ds.ds_ident

instance PP (Global a) | PP a where
  pp inh glob = pp inh glob.glob_object

instance PP Selection where
  pp inh (RecordSelection gds _)      = pp inh gds
  pp _ (ArraySelection _ _ _)         = 'PP'.text "TODO: ArraySelection"
  pp _ (DictionarySelection _ _ _ _)  = 'PP'.text "TODO: DictionarySelection"

instance PP GExpression where
  pp _ GUndefinedExpression      = 'PP'.text "undef"
  pp _ (GGraphExpression graph)  = 'PP'.text "TODO: render a subgraph (and don't PP one)"
  pp _ (GListExpression ges)     = 'PP'.text "TODO: render a list expression (and don't PP one)"
  pp _ (GListComprehensionExpression glc)  = 'PP'.text "TODO: render a list comprehension expression (and don't PP one)"
  pp _ (GCleanExpression ce)     = 'PP'.text ce

instance PP GLet where
  pp inh gl = 'PP'.vcat (map (pp inh) gl.glet_binds)

instance PP GLetBind where
  pp inh lb = 'PP'.text lb.glb_dst 'PP'. <+> 'PP'.equals 'PP'. <+> pp inh lb.glb_src

prettyAlg :: InhExpression -> ExpressionAlg Doc
prettyAlg inh =
  let
    varC bv = pp inh bv
    appC app
      = let ppargs xs = 'PP'.hcat $ intersperse ('PP'.text " ") $ map (pp inh) xs
        in  (case app.app_args of
               []     -> pp inh app.app_symb
               [x:xs] -> if (isInfix inh.inh_fun_defs inh.inh_icl_module inh.inh_dcl_modules app.app_symb)
                           (pp inh x 'PP'. <+> pp inh app.app_symb 'PP'. <+> ppargs xs)
                           (pp inh app.app_symb 'PP'. <+> ppargs app.app_args))
    basicC bv = pp inh bv
    defaultC = 'PP'.empty
    selectionC _ expr sels = pp inh expr 'PP'. <-> 'PP'.char '.' 'PP'. <-> 'PP'.hcat (intersperse ('PP'.char '.') $ map (pp inh) sels)
    updateC _ _ _ = 'PP'.text "update"
    recordUpdateC _ _ _ = 'PP'.text "recordUpdate"
    tupleSelectC _ _ _ = 'PP'.text "tupleSelect"

  in { mkExprAlg 'PP'.empty
     & var = varC, app = appC, basicExpr = basicC, selection = selectionC
     , recordUpdate = recordUpdateC, update = updateC, tupleSelect = tupleSelectC }

debugPPAlg :: InhExpression -> ExpressionAlg Doc
debugPPAlg inh =
  let
    varC bv = 'PP'.text "<Var>" 'PP'. <+> pp inh bv
    appC app
      # args = 'PP'.hcat $ intersperse ('PP'.text ", ") $ map (pp inh) app.app_args
      = 'PP'.text "<App>" 'PP'. <+> pp inh app.app_symb 'PP'. <+> 'PP'.brackets args
    basicC bv = 'PP'.text "<BasicValue>" 'PP'. <+> pp inh bv
    defaultC = 'PP'.empty
    selectionC _ expr sels = 'PP'.text "<Selection>" 'PP'. <+> pp inh expr 'PP'. <-> 'PP'.char '.' 'PP'. <-> 'PP'.hcat (intersperse ('PP'.char '.') $ map (pp inh) sels)
    //updateC _ _ _ = 'PP'.text "update"
    //recordUpdateC _ _ _ = 'PP'.text "recordUpdate"
    //tupleSelectC _ _ _ = 'PP'.text "tupleSelect"

  in { mkExprAlg 'PP'.empty
     & var = varC, app = appC, basicExpr = basicC, selection = selectionC }
     //, recordUpdate = recordUpdateC, update = updateC, tupleSelect = tupleSelectC }

getNodeData` :: Int GinGraph -> GNode
getNodeData` n g = fromMaybe err (getNodeData n g)
  where err = abort ("No data for node " +++ toString n)

mkTaskDot :: InhExpression String Int Int GGraph -> String
mkTaskDot inh funnm startid endid (GGraph g) = "subgraph cluster_" +++ funnm +++ " {\n label=\"" +++ funnm  +++ "\"  color=\"black\";\n" +++
  mkNodes +++ "\n" +++
  mkEdges +++ "\n}"
  where
  mkNodes = concatStrings (map (nodeToDot inh funnm g) (nodeIndices g))
  mkEdges = concatStrings (map edgeToDot (edgeIndices g))
  edgeToDot ei=:(l, r) = mkDotNodeLbl funnm l +++ " -> " +++ mkDotNodeLbl funnm r +++ mkDotArgs [mkDotAttrKV "label" edgeLbl] // TODO: Use different arrow for task assignment
    where edgeLbl = maybe "" (\e -> fromMaybe "" e.edge_pattern) $ getEdgeData ei g

mkDotAttrKV :: String String -> String
mkDotAttrKV k v = k +++ "=" +++ "\"" +++ v +++ "\""

mkDotArgs :: [String] -> String
mkDotArgs attrs = " [" +++ concatStrings (intersperse ", " attrs) +++ "];\n"

mkDotNodeLbl :: String Int -> String
mkDotNodeLbl funnm n = funnm +++ "_node_" +++ toString n

nodeToDot :: InhExpression String GinGraph Int -> String
nodeToDot inh funnm g currIdx =
  case currNode of
    GInit                 -> blackNode [shape "triangle", width ".25", height ".25"]
    GStop                 -> blackNode [shape "box", width ".2", height ".2"]
    (GDecision _ expr)    -> whiteNode [shape "diamond", label expr]
    GMerge                -> blackNode [shape "diamond", width ".25", height ".25"]
    (GLet glt)            -> whiteNode [shape "box", label (concatStrings $ intersperse "\n" $ map (mkPretty inh) glt)] // TODO: Rounded corners
    GParallelSplit        -> whiteNode [shape "circle", label "Parallel split"]
    (GParallelJoin jt)    -> whiteNode [shape "circle", label (mkJoinLbl jt)]
    (GTaskApp tid exprs)  -> whiteNode [shape "box", label tid] // TODO: complex contents with extra bar
    (GReturn expr)        -> whiteNode [shape "oval", label (mkPretty inh expr)]
    (GAssign usr)         -> let  idxStr = toString currIdx
                                  usrStr = "user" +++ idxStr
                             in   "subgraph cluster_user" +++ idxStr +++ "{ label=" +++ usr +++ "; labelloc=b; peripheries=0; " +++ usrStr +++ "}" +++
                                  usrStr +++ mkDotArgs [ mkDotAttrKV "shapefile" "\"stick.png\""
                                                       , mkDotAttrKV "peripheries" "0"
                                                       , style "invis" ]
    GStep                 -> whiteNode [shape "circle", label "Step"]
  where
  currNode         = getNodeData` currIdx g
  whiteNode attrs  = mkDotNode [fontcolor "black", fillcolor "white", style "filled", label "" : attrs]
  blackNode attrs  = mkDotNode [fontcolor "white", fillcolor "black", style "filled", label "" : attrs]
  mkDotNode attrs  = mkDotNodeLbl funnm currIdx +++ mkDotArgs attrs
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
