implementation module Tonic.AbsSyn

import syntax, predef, checksupport
from overloading import :: InstanceTree
import Data.Func
import Data.Graph
import Data.Maybe
import Data.Map
from Data.Set import :: Set
import qualified Data.Set as DS
//import Tonic.Tonic
import Tonic.Pretty
import iTasks._Framework.Tonic.AbsSyn

mkInhExpr :: !Int ![(String, ParsedExpr)] !{#{!InstanceTree}} !{#CommonDefs} -> InhExpression
mkInhExpr funIdx list_comprehensions tree cds =
  { InhExpression
  | inh_case_expr      = Nothing
  , inh_tyenv          = newMap
  , inh_list_compr     = list_comprehensions
  , inh_instance_tree  = tree
  , inh_common_defs    = cds
  , inh_uid            = [0]
  , inh_fun_idx        = funIdx
  }

mkChnExpr :: !FunDef *PredefinedSymbols *ModuleEnv *Heaps -> *ChnExpression
mkChnExpr fd predef_symbols menv heaps =
  { ChnExpression
  | chn_module_env     = menv
  , chn_predef_symbols = predef_symbols
  , chn_heaps          = heaps
  , chn_fundef         = fd
  }

mkSynExpr :: !TExpr !Expression -> SynExpression
mkSynExpr te expr =
  { SynExpression
  | syn_texpr              = te
  , syn_annot_expr         = expr
  , syn_pattern_match_vars = []
  , syn_bound_vars         = newMap
  , syn_cases              = []
  }

mkModuleEnv :: ModuleN !*{#FunDef} !*{#FunDef} !{!Group} IclModule {#DclModule} -> *ModuleEnv
mkModuleEnv main_dcl_module_n fun_defs fun_defs_cpy groups icl_module dcl_modules =
  { ModuleEnv
  | me_main_dcl_module_n = main_dcl_module_n
  , me_dcl_modules       = dcl_modules
  , me_icl_module        = icl_module
  , me_fun_defs          = fun_defs
  , me_fun_defs_cpy      = fun_defs_cpy
  , me_groups            = groups
  }

