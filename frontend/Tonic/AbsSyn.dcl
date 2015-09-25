definition module Tonic.AbsSyn

from syntax import :: Expression (..), :: BoundVar, :: App {..}, :: Let, :: Case,
  :: SelectorKind, :: Selection, :: FreeVar {..}, :: Global, :: SymbIdent, :: Priority,
  :: VarInfoPtr, :: DynamicExpr, :: Ptr, :: VarInfo, :: CodeBinding, :: DefinedSymbol,
  :: Bind, :: Position, :: AType, :: Env, :: Ident, :: Level, :: ExprInfoPtr, :: ExprInfo,
  :: TypeCodeExpression, :: GlobalIndex, :: Conditional, :: BasicValue, :: FieldSymbol,
  :: IclModule, :: DclModule, :: FunDef, :: Optional, :: SymbolType, :: LetBind,
  :: ModuleN, :: Type, :: ParsedExpr, :: CommonDefs, :: Index, :: TypeContext
from checksupport import :: Heaps, :: Group
from overloading import :: InstanceTree
from Data.Graph import :: Graph
from Data.Maybe import :: Maybe
from Text.JSON import generic JSONEncode, :: JSONNode
from Data.Map import :: Map
from Data.Set import :: Set
from predef import :: PredefinedSymbol, :: PredefinedSymbols
from iTasks._Framework.Tonic.AbsSyn import :: TExpr, :: ExprId

// InhExpression and ChnExpression need strict fields in order to prevent a bus
// error caused by huge thunks
:: InhExpression =
  { inh_case_expr     :: !Maybe Expression
  , inh_tyenv         :: !Map Int (Type, [TypeContext])
  , inh_list_compr    :: ![(String, ParsedExpr)]
  , inh_instance_tree :: !{#{!InstanceTree}}
  , inh_common_defs   :: !{#CommonDefs}
  , inh_uid           :: !ExprId
  , inh_fun_idx       :: !Int
  , inh_bind_var      :: !Maybe FreeVar
  , inh_cases         :: !Map ExprId (!Bool, !(Map Int BoundVar), !Expression)
  , inh_is_top_bind   :: !Bool
  }

:: *ChnExpression =
  { chn_heaps             :: !*Heaps
  , chn_predef_symbols    :: !*PredefinedSymbols
  , chn_main_dcl_module_n :: !Int
  , chn_fun_defs          :: !*{#FunDef}
  , chn_fun_defs_cpy      :: !*{#FunDef}
  , chn_icl_module        :: !IclModule
  , chn_dcl_modules       :: !{#DclModule}
  , chn_groups            :: !{!Group}
  }

:: SynExpression =
  { syn_texpr              :: !TExpr
  , syn_annot_expr         :: !Expression
  , syn_pattern_match_vars :: ![(BoundVar, TExpr)]
  , syn_bound_vars         :: !Map Int BoundVar
  , syn_cases              :: !Map ExprId (!Bool, !(Map Int BoundVar), !Expression)
  }

mkInhExpr :: !Int ![(String, ParsedExpr)] !{#{!InstanceTree}} !{#CommonDefs} -> InhExpression

mkChnExpr :: ModuleN !*{#FunDef} !*{#FunDef} !{!Group} IclModule {#DclModule} *PredefinedSymbols *Heaps -> *ChnExpression

mkSynExpr :: !TExpr !Expression -> SynExpression
