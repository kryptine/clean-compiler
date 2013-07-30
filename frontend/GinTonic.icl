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
    | otherwise                                        = rest
  defToStr fd  = optional "Nothing happened" f (funToGraph fd iclmod dcl_modules)
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
// Reverse transformListComprehension in frontend/postparse.icl
/*
makeNilExpression :: Int *CollectAdmin -> (ParsedExpr,*CollectAdmin)
makeNilExpression predef_nil_index ca
	#! nil_id = predefined_idents.[predef_nil_index]
	= (PE_Ident nil_id, ca)

makeConsExpression :: Int ParsedExpr ParsedExpr *CollectAdmin -> (ParsedExpr,*CollectAdmin)
makeConsExpression predef_cons_index a1 a2 ca
	#! cons_id = predefined_idents.[predef_cons_index]
	= (PE_List [PE_Ident cons_id, a1, a2], ca)

transformListComprehension :: Int Int ParsedExpr [Qualifier] *CollectAdmin -> (ParsedExpr, *CollectAdmin)
transformListComprehension predef_cons_index predef_nil_index expr qualifiers ca
  # (transformed_qualifiers, ca) = mapSt transformQualifier qualifiers ca
    (success, ca) = makeConsExpression predef_cons_index expr (last transformed_qualifiers).tq_continue ca
    (nil, ca) = makeNilExpression predef_nil_index ca
    transformed_qualifiers
      =  [  {qual & tq_success = success, tq_end = end}
         \\  qual <- transformed_qualifiers
         &  success <- [qual.tq_call \\ qual <- tl transformed_qualifiers] ++ [success]
         &  end <- [nil : [qual.tq_continue \\ qual <- transformed_qualifiers]]
         ]
  = makeComprehensions transformed_qualifiers success [] ca

makeComprehensions :: [TransformedQualifier] ParsedExpr [ParsedExpr] *CollectAdmin -> (ParsedExpr, *CollectAdmin)
makeComprehensions [] success _ ca
	=	(success, ca)
makeComprehensions [{tq_generators,tq_let_defs,tq_filter, tq_end, tq_call, tq_lhs_args, tq_fun_id, tq_fun_pos} : qualifiers] success threading ca
	# (success, ca) = makeComprehensions qualifiers success threading ca
	# failure		= PE_List [PE_Ident tq_fun_id : threading ++ rhs_continuation_args_from_generators tq_generators]
	  rhs	 		= build_rhs tq_generators success tq_let_defs tq_filter failure tq_end tq_fun_pos
	  parsed_def 	= MakeNewParsedDef tq_fun_id tq_lhs_args rhs tq_fun_pos
	= (PE_Let (LocalParsedDefs [parsed_def]) tq_call, ca)
	where
		build_rhs :: [TransformedGenerator] ParsedExpr LocalDefs (Optional ParsedExpr) ParsedExpr ParsedExpr Position -> Rhs
		build_rhs [generator : generators] success let_defs optional_filter failure end fun_pos
			#	rhs2 = foldr (case_end end)
						(case_with_default generator.tg_case2 generator.tg_element generator.tg_element_is_uselect generator.tg_pattern
							(foldr (case_pattern failure) rhs generators)
							failure)
						generators
			=	case_with_default generator.tg_case1 generator.tg_case_end_expr False generator.tg_case_end_pattern rhs2 end
			where
				rhs
					=	case optional_filter of
							Yes filter
								-> {rhs_alts = GuardedAlts [
										{alt_nodes = [], alt_guard = filter, alt_expr = UnGuardedExpr
												{ewl_nodes = [], ewl_expr = success, ewl_locals	= LocalParsedDefs [], ewl_position = NoPos },
											alt_ident = { id_name ="_f;" +++ toString line_nr +++ ";", id_info = nilPtr },
										 alt_position = NoPos}] No
									,	rhs_locals	= let_defs}
							No
								-> {rhs_alts=UnGuardedExpr {ewl_nodes=[],ewl_expr=success,ewl_locals=LocalParsedDefs [],ewl_position=NoPos},rhs_locals=let_defs}
				(LinePos _ line_nr) = fun_pos

		case_end :: ParsedExpr TransformedGenerator Rhs -> Rhs
		case_end end {tg_case1, tg_case_end_expr, tg_case_end_pattern} rhs
			=	case_with_default tg_case1 tg_case_end_expr False tg_case_end_pattern rhs end
	
		case_pattern :: ParsedExpr TransformedGenerator Rhs -> Rhs
		case_pattern failure {tg_case2, tg_element,tg_element_is_uselect, tg_pattern} rhs
			=	case_with_default tg_case2 tg_element tg_element_is_uselect tg_pattern rhs failure

		case_with_default :: Ident ParsedExpr Bool ParsedExpr Rhs ParsedExpr -> Rhs
		case_with_default case_ident expr expr_is_uselect pattern=:(PE_Ident ident) rhs=:{rhs_alts=UnGuardedExpr ung_exp=:{ewl_nodes,ewl_expr,ewl_locals=LocalParsedDefs [],ewl_position},rhs_locals=LocalParsedDefs []} default_rhs
			# new_node={ndwl_strict=False,ndwl_def={bind_src=expr,bind_dst=pattern},ndwl_locals=LocalParsedDefs [],ndwl_position=ewl_position}
			= {rhs & rhs_alts=UnGuardedExpr {ung_exp & ewl_nodes=[new_node:ewl_nodes]}}
		case_with_default case_ident expr True pattern=:(PE_Tuple [PE_Ident ident1,ident2_exp=:PE_Ident ident2]) rhs=:{rhs_alts=UnGuardedExpr ung_exp=:{ewl_nodes,ewl_expr,ewl_locals=LocalParsedDefs [],ewl_position},rhs_locals=LocalParsedDefs []} default_rhs
			# new_node1={ndwl_strict=False,ndwl_def={bind_src=expr,bind_dst=pattern},ndwl_locals=LocalParsedDefs [],ndwl_position=ewl_position}
			# new_node2={ndwl_strict=True,ndwl_def={bind_src=ident2_exp,bind_dst=ident2_exp},ndwl_locals=LocalParsedDefs [],ndwl_position=ewl_position}
			= {rhs & rhs_alts=UnGuardedExpr {ung_exp & ewl_nodes=[new_node1,new_node2:ewl_nodes]}}
		case_with_default case_ident expr expr_is_uselect PE_Empty rhs default_rhs
			= rhs
		case_with_default case_ident expr expr_is_uselect pattern rhs default_rhs
			=	exprToRhs (PE_Case case_ident expr
					[	{calt_pattern = pattern, calt_rhs = rhs, calt_position=NoPos}
					,	{calt_pattern = PE_WildCard, calt_rhs = exprToRhs default_rhs, calt_position=NoPos}
					])
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

reifyFunDef :: IclModule {#DclModule} Ident -> FunDef
reifyFunDef icl_module dcl_modules ident =
  case findInArr (\fd -> fd.fun_ident == ident) icl_module.icl_functions of
    Just fd  -> fd
    _        -> abort ("Failed to reify " +++ ident.id_name)

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
  {  var                   :: BoundVar -> a                         // Var
  ,  app                   :: App -> a                              // App
  ,  at                    :: a [a] -> a                            // (@)
  ,  letE                  :: Let -> a                              // Let
  ,  caseE                 :: Case -> a                             // Case
  ,  selection             :: SelectorKind a [Selection] -> a       // Selection
  ,  update                :: a [Selection] a -> a                  // Update
  ,  recordUpdate          :: (Global DefinedSymbol) a [Bind a (Global FieldSymbol)] -> a   // RecordUpdate
  ,  tupleSelect           :: DefinedSymbol Int a -> a              // TupleSelect
  ,  basicExpr             :: BasicValue -> a                       // BasicExpr
  ,  conditional           :: Conditional -> a                      // Conditional
  ,  anyCodeExpr           :: (CodeBinding BoundVar) (CodeBinding FreeVar) [String] -> a    // AnyCodeExpr
  ,  abcCodeExpr           :: [String] Bool -> a                    // ABCCodeExpr
  ,  matchExpr             :: (Global DefinedSymbol) a -> a         // MatchExpr
  ,  isConstructor         :: a (Global DefinedSymbol) Int GlobalIndex Ident Position -> a  // IsConstructor
  ,  freeVar               :: FreeVar -> a                          // FreeVar
  ,  dictionariesFunction  :: [(FreeVar,AType)] a AType -> a        // DictionariesFunction
  ,  constant              :: SymbIdent Int Priority -> a           // Constant
  ,  classVariable         :: VarInfoPtr -> a                       // ClassVariable
  ,  dynamicExpr           :: DynamicExpr -> a                      // DynamicExpr
  ,  typeCodeExpression    :: TypeCodeExpression -> a               // TypeCodeExpression
  ,  typeSignature         :: (Int Int -> (AType,Int,Int)) a -> a   // TypeSignature
  ,  ee                    :: a                                     // EE
  ,  noBind                :: ExprInfoPtr -> a                      // NoBind
  ,  failExpr              :: Ident -> a                            // FailExpr
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

:: InhExpression =
  {  inh_icl_module      :: !IclModule
  ,  inh_dcl_modules     :: !{#DclModule}
  ,  inh_graph           :: !GinGraph
  ,  inh_source_id       :: !Int
  ,  inh_sink_id         :: !Int
  ,  inh_curr_task_name  :: !String
  }

:: SynExpression =
  {  syn_nid        :: Maybe Int
  ,  syn_graph      :: !GinGraph
  ,  syn_rec_nodes  :: [NodeIndex]
  }

/*
Inherited attributes:
- iclModule :: IclModule

Chained attributes:
- graph :: GinGraph

Synthesized attributes:
- gid :: Maybe Int
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

mkInhExpr :: IclModule {#DclModule} GinGraph Int Int String -> InhExpression
mkInhExpr icl_module dcl_modules gg so si nm =
  {  InhExpression
  |  inh_icl_module      = icl_module
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
      # patid =
          case app.app_args of
            [_:Var bv:_]  ->
              withHead  (\x -> x.fv_ident.id_name) (abort "No fun args for bind rhs")
                        (getFunArgVars (reifyFunDef inh.inh_icl_module inh.inh_dcl_modules bv.var_ident))
            _ -> abort "Expression not supported or invalid bind"
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

mkEdge :: GEdge
mkEdge = {GEdge | edge_pattern = Nothing }

addEdge` :: (Maybe Int) (Maybe Int) (Maybe String) GinGraph -> GinGraph
addEdge` (Just l)  (Just r)  ep  g  = addEdge {edge_pattern = ep} (l, r) g
addEdge` _         _         _   _  = abort "Invalid edge"

addNode` :: GNode GinGraph -> SynExpression
addNode` node graph
  # (n, g) = addNode node graph
  = mkSynExpr (Just n) g

mkPretty :: (a -> String) | Pretty a
mkPretty = 'PP'.display o 'PP'.renderCompact o pretty

funToGraph :: FunDef IclModule {#DclModule} -> Optional (GGraph, Int, Int)
funToGraph fd icl_module dcl_modules = funBodyToGraph fd.fun_ident.id_name fd.fun_body icl_module dcl_modules

funBodyToGraph :: String FunctionBody IclModule {#DclModule} -> Optional (GGraph, Int, Int)
funBodyToGraph fun_name (TransformedBody tb) icl_module dcl_modules
  # (soid, g)  = addNode GInit emptyGraph
  # (siid, g)  = addNode GStop g
  = Yes (GGraph (mkBody soid siid g), soid, siid)
  where
  mkBody soid siid g // TODO cb.cb_args
    # inh  = mkInhExpr icl_module dcl_modules g soid siid fun_name
    # syn  = exprCata (mkGraphAlg inh) tb.tb_rhs
    # g`   = syn.syn_graph
    = if (isEmpty syn.syn_rec_nodes) g` (addRecs syn.syn_rec_nodes g`)

  addRecs recs g
    # (nid, g`) = addNode GMerge g
    = foldr (\n -> addEdge mkEdge (nid, n)) g` recs

funBodyToGraph fun_name _ _ _ = No

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

prettyAlg :: ExpressionAlg Doc
prettyAlg =
  let
    varC bv = pretty bv
    appC app
      # args = foldr (\x xs -> pretty x 'PP'. <+> xs) 'PP'.empty app.app_args
      | length app.app_args > 0  = pretty app.app_symb 'PP'. <+> args
      | otherwise                = pretty app.app_symb
    defaultC = 'PP'.empty
  in {mkExprAlg 'PP'.empty & var = varC, app = appC }


getNodeData` :: Int GinGraph -> GNode
getNodeData` n g =
  case getNodeData n g of
    Just x  -> x
    _       -> abort ("No data for node " +++ toString n)

mkTaskDot :: String Int Int GGraph -> String
mkTaskDot funnm startid endid (GGraph g) = "digraph " +++ funnm +++ " {\n" +++ mkNodes +++ "\n" +++ mkEdges +++ "\n}"
  where
  mkNodes = concatStrings (map (nodeToDot g) (nodeIndices g))
  mkEdges = concatStrings (map edgeToDot (edgeIndices g))
  edgeToDot (l, r) = mkDotNodeLbl l +++ " -> " +++ mkDotNodeLbl r +++ ";\n" // TODO: Use different arrow for task assignment

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
                                  usrStr +++ " [shapefile=\"stick.png\", peripheries=0, style=invis]"
    GStep                 -> whiteNode [shape "circle", label "Step"]
  where
  currNode         = getNodeData` currIdx g
  whiteNode attrs  = mkDotNode [fontcolor "black", fillcolor "white", style "filled" : attrs]
  blackNode attrs  = mkDotNode [fontcolor "white", fillcolor "black", style "filled" : attrs]
  mkDotNode attrs  = mkDotNodeLbl currIdx +++ " [" +++ concatStrings (intersperse ", " attrs) +++ "];\n"
  shape v      = mkKV "shape" v
  label v      = mkKV "label" v
  color v      = mkKV "color" v
  fillcolor v  = mkKV "fillcolor" v
  fontcolor v  = mkKV "fontcolor" v
  width v      = mkKV "width" v
  height v     = mkKV "height" v
  style v      = mkKV "style" v
  mkKV k v     = k +++ "=" +++ v
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
