implementation module Tonic.AbsSyn

import syntax, predef, checksupport
from overloading import :: InstanceTree
import Data.Func
import Data.Graph
import Data.Maybe
import Data.Map
//import Tonic.Tonic
import Tonic.Pretty
import iTasks.Framework.Tonic.AbsSyn

mkInhExpr :: !String ![(String, ParsedExpr)] !{#{!InstanceTree}} !{#CommonDefs} -> InhExpression
mkInhExpr ctn list_comprehensions tree cds =
  { InhExpression
  | inh_curr_task_name = ctn
  , inh_case_expr      = Nothing
  , inh_is_bind_lam    = False
  , inh_ids            = [0]
  , inh_tyenv          = newMap
  , inh_list_compr     = list_comprehensions
  , inh_instance_tree  = tree
  , inh_common_defs    = cds
  }

mkChnExpr :: *PredefinedSymbols *ModuleEnv *Heaps -> *ChnExpression
mkChnExpr predef_symbols menv heaps =
  { ChnExpression
  | //chn_graph          = gg
    chn_module_env     = menv
  , chn_predef_symbols = predef_symbols
  , chn_heaps          = heaps
  }

mkModuleEnv :: ModuleN !*{#FunDef} !*{#FunDef} IclModule {#DclModule} -> *ModuleEnv
mkModuleEnv main_dcl_module_n fun_defs fun_defs_cpy icl_module dcl_modules =
  {  ModuleEnv
  |  me_main_dcl_module_n = main_dcl_module_n
  ,  me_dcl_modules  = dcl_modules
  ,  me_icl_module   = icl_module
  ,  me_fun_defs     = fun_defs
  ,  me_fun_defs_cpy = fun_defs_cpy
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

