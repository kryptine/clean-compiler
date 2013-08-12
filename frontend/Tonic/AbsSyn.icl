implementation module Tonic.AbsSyn

import syntax
import Data.Graph
import Data.Maybe
import Tonic.Pretty

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

mkInhExpr :: ModuleEnv GinGraph Int String (Maybe Expression) -> InhExpression
mkInhExpr menv gg mergeId nm ce =
  {  InhExpression
  |  inh_module_env      = menv
  ,  inh_graph           = gg
  ,  inh_merge_id        = mergeId
  ,  inh_curr_task_name  = nm
  ,  inh_case_expr       = ce
  }

mkModuleEnv :: {#FunDef} IclModule {#DclModule} -> ModuleEnv
mkModuleEnv fun_defs icl_module dcl_modules =
  {  ModuleEnv
  |  me_dcl_modules  = dcl_modules
  ,  me_icl_module   = icl_module
  ,  me_fun_defs     = fun_defs
  }

mkGLet :: ModuleEnv Let -> GLet
mkGLet menv lt =
  {  GLet
  |  glet_binds  = map (mkGLetBinds menv) (lt.let_lazy_binds ++ lt.let_strict_binds)
  ,  glet_expr   = lt.let_expr
  }

mkGLetBind :: String Expression -> GLetBind
mkGLetBind str expr =
  {  GLetBind
  |  glb_dst = str
  ,  glb_src = expr
  }

mkGLetBinds :: ModuleEnv LetBind -> GLetBind
mkGLetBinds menv lb =
  {  GLetBind
  |  glb_dst = mkPretty menv lb.lb_dst
  ,  glb_src = lb.lb_src
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

emptyEdge :: GEdge
emptyEdge = {GEdge | edge_pattern = Nothing }

mkEdge :: String -> GEdge
mkEdge str = {GEdge | edge_pattern = Just str }
