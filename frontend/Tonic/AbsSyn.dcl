definition module Tonic.AbsSyn

from syntax import :: Expression (..), :: BoundVar, :: App {..}, :: Let, :: Case,
  :: SelectorKind, :: Selection, :: FreeVar {..}, :: Global, :: SymbIdent, :: Priority,
  :: VarInfoPtr, :: DynamicExpr, :: Ptr, :: VarInfo, :: CodeBinding, :: DefinedSymbol,
  :: Bind, :: Position, :: AType, :: Env, :: Ident, :: Level, :: ExprInfoPtr, :: ExprInfo,
  :: TypeCodeExpression, :: GlobalIndex, :: Conditional, :: BasicValue, :: FieldSymbol,
  :: IclModule, :: DclModule, :: FunDef, :: Optional, :: SymbolType, :: LetBind,
  :: ModuleN, :: Type, :: ParsedExpr, :: CommonDefs
from checksupport import :: Heaps
from overloading import :: InstanceTree
from Data.Graph import :: Graph
from Data.Maybe import :: Maybe
from Text.JSON import generic JSONEncode, :: JSONNode
from Data.Map import :: Map
from Data.Set import :: Set
from predef import :: PredefinedSymbol, :: PredefinedSymbols
from iTasks._Framework.Tonic.AbsSyn import :: TExpr, :: ExprId, :: TypeName, :: ModuleName, :: TaskName, :: VariableName //, :: TCleanExpr

// InhExpression and ChnExpression need strict fields in order to prevent a bus
// error caused by huge thunks
:: InhExpression =
  { inh_curr_task_name :: !String
  , inh_case_expr      :: !Maybe Expression
  , inh_is_bind_lam    :: !Bool
  , inh_tyenv          :: !Map String Type
  , inh_list_compr     :: ![(String, ParsedExpr)]
  , inh_instance_tree  :: !{#{!InstanceTree}}
  , inh_common_defs    :: !{#CommonDefs}
  , inh_app_ctx        :: !(String, String)
  , inh_vars_in_scope  :: !Set String
  }

:: *ChnExpression =
  { chn_module_env     :: !*ModuleEnv
  , chn_heaps          :: !*Heaps
  , chn_predef_symbols :: !*PredefinedSymbols
  , chn_ids            :: !ExprId
  }

:: SynExpression =
  { syn_texpr              :: !TExpr
  , syn_annot_expr         :: !Expression
  , syn_pattern_match_vars :: ![(BoundVar, TExpr)]
  }

:: *ModuleEnv =
  { me_main_dcl_module_n :: !Int
  , me_fun_defs          :: !*{#FunDef}
  , me_fun_defs_cpy      :: !*{#FunDef}
  , me_icl_module        :: !IclModule
  , me_dcl_modules       :: !{#DclModule}
  }

mkInhExpr :: !(Set String) !String ![(String, ParsedExpr)] !{#{!InstanceTree}} !{#CommonDefs} -> InhExpression

mkChnExpr :: *PredefinedSymbols *ModuleEnv *Heaps -> *ChnExpression

mkModuleEnv :: ModuleN !*{#FunDef} !*{#FunDef} IclModule {#DclModule} -> *ModuleEnv
