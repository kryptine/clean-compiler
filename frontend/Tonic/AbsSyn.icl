implementation module Tonic.AbsSyn

import syntax, predef, checksupport
import Data.Func
import Data.Graph
import Data.Maybe
//import Tonic.Tonic
import Tonic.Pretty
import iTasks.Framework.Tonic.AbsSyn

exprCata :: *(ExpressionAlg inh *chn syn) Expression inh *chn -> *(syn, *chn)
exprCata alg (Var bv                      ) inh chn = alg.var bv inh chn
exprCata alg (App a                       ) inh chn = alg.app a inh chn
exprCata alg (l @ rs                      ) inh chn = alg.at l rs inh chn
exprCata alg (Let l                       ) inh chn = alg.letE l inh chn
exprCata alg (Case c                      ) inh chn = alg.caseE c inh chn
exprCata alg (Selection sk e ss           ) inh chn = alg.selection sk e ss inh chn
exprCata alg (Update e1 ss e2             ) inh chn = alg.update e1 ss e2 inh chn
exprCata alg (RecordUpdate gd e bs        ) inh chn = alg.recordUpdate gd e bs inh chn
exprCata alg (TupleSelect ds i e          ) inh chn = alg.tupleSelect ds i e inh chn
exprCata alg (BasicExpr bv                ) inh chn = alg.basicExpr bv inh chn
exprCata alg (Conditional c               ) inh chn = alg.conditional c inh chn
exprCata alg (AnyCodeExpr cb cf ss        ) inh chn = alg.anyCodeExpr cb cf ss inh chn
exprCata alg (ABCCodeExpr ss b            ) inh chn = alg.abcCodeExpr ss b inh chn
exprCata alg (MatchExpr gd e              ) inh chn = alg.matchExpr gd e inh chn
exprCata alg (IsConstructor e gd n gi i p ) inh chn = alg.isConstructor e gd n gi i p inh chn
exprCata alg (FreeVar v                   ) inh chn = alg.freeVar v inh chn
exprCata alg (DictionariesFunction xs e at) inh chn = alg.dictionariesFunction xs e at inh chn
exprCata alg (Constant si i prio          ) inh chn = alg.constant si i prio inh chn
exprCata alg (ClassVariable vip           ) inh chn = alg.classVariable vip inh chn
exprCata alg (DynamicExpr de              ) inh chn = alg.dynamicExpr de inh chn
exprCata alg (TypeCodeExpression t        ) inh chn = alg.typeCodeExpression t inh chn
exprCata alg (TypeSignature f e           ) inh chn = alg.typeSignature f e inh chn
exprCata alg (EE                          ) inh chn = alg.ee inh chn
exprCata alg (NoBind eip                  ) inh chn = alg.noBind eip inh chn
exprCata alg (FailExpr i                  ) inh chn = alg.failExpr i inh chn

mkInhExpr :: String -> InhExpression
mkInhExpr ctn =
  { InhExpression
  | inh_curr_task_name = ctn
  , inh_case_expr      = Nothing
  , inh_is_bind_lam    = False
  , inh_ids            = [0]
  }

mkChnExpr :: *PredefinedSymbols *ModuleEnv *Heaps -> *ChnExpression
mkChnExpr predef_symbols menv heaps =
  { ChnExpression
  | //chn_graph          = gg
    chn_module_env     = menv
  , chn_predef_symbols = predef_symbols
  , chn_heaps          = heaps
  }

mkModuleEnv :: ModuleN !*{#FunDef} IclModule {#DclModule} -> *ModuleEnv
mkModuleEnv main_dcl_module_n fun_defs icl_module dcl_modules =
  {  ModuleEnv
  |  me_main_dcl_module_n = main_dcl_module_n
  ,  me_dcl_modules  = dcl_modules
  ,  me_icl_module   = icl_module
  ,  me_fun_defs     = fun_defs
  }

//mkGLet :: Let *ModuleEnv -> *(GLet, *ModuleEnv)
//mkGLet lt menv
  //# (bs, menv) = mapSt mkGLetBinds (lt.let_lazy_binds ++ lt.let_strict_binds) menv
  //= ({  GLet
     //|  glet_binds  = bs
     //,  glet_expr   = lt.let_expr
     //}, menv)

//mkGLetBind :: String Expression -> GLetBind
//mkGLetBind str expr =
  //{  GLetBind
  //|  glb_dst = str
  //,  glb_src = expr
  //}

//mkGLetBinds :: LetBind *ModuleEnv -> *(GLetBind, *ModuleEnv)
//mkGLetBinds lb menv
  //# (doc, menv) = ppFreeVar lb.lb_dst menv
  //= ({  GLetBind
     //|  glb_dst = ppCompact doc
     //,  glb_src = lb.lb_src
     //}, menv)
