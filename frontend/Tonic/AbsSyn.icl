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

mkInhExpr :: !Int ![(String, ParsedExpr)] !{#{!InstanceTree}} !{#CommonDefs} ![String] -> InhExpression
mkInhExpr funIdx list_comprehensions tree cds tonicFiles =
  { InhExpression
  | inh_case_expr      = Nothing
  , inh_tyenv          = newMap
  , inh_list_compr     = list_comprehensions
  , inh_instance_tree  = tree
  , inh_common_defs    = cds
  , inh_uid            = [0]
  , inh_fun_idx        = funIdx
  , inh_bind_var       = Nothing
  , inh_cases          = newMap
  , inh_is_top_bind    = True
  , inh_tonic_files    = tonicFiles
  , inh_parent_fun_mod = ""
  , inh_bound_vars     = newMap
  }

mkChnExpr :: ModuleN !*{#FunDef} !*{#FunDef} !{!Group} IclModule {#DclModule} *PredefinedSymbols *Heaps -> *ChnExpression
mkChnExpr main_dcl_module_n fun_defs fun_defs_cpy groups icl_module dcl_modules predef_symbols heaps =
  { ChnExpression
  | chn_predef_symbols    = predef_symbols
  , chn_heaps             = heaps
  , chn_main_dcl_module_n = main_dcl_module_n
  , chn_dcl_modules       = dcl_modules
  , chn_icl_module        = icl_module
  , chn_fun_defs          = fun_defs
  , chn_fun_defs_cpy      = fun_defs_cpy
  , chn_groups            = groups
  }

mkSynExpr :: !TExpr !Expression -> SynExpression
mkSynExpr te expr =
  { SynExpression
  | syn_texpr              = te
  , syn_annot_expr         = expr
  , syn_pattern_match_vars = []
  , syn_bound_vars         = newMap
  , syn_cases              = newMap
  }
