definition module Tonic.AbsSyn

from syntax import :: Expression (..), :: BoundVar, :: App {..}, :: Let, :: Case,
  :: SelectorKind, :: Selection, :: FreeVar {..}, :: Global, :: SymbIdent, :: Priority,
  :: VarInfoPtr, :: DynamicExpr, :: Ptr, :: VarInfo, :: CodeBinding, :: DefinedSymbol,
  :: Bind, :: Position, :: AType, :: Env, :: Ident, :: Level, :: ExprInfoPtr, :: ExprInfo,
  :: TypeCodeExpression, :: GlobalIndex, :: Conditional, :: BasicValue, :: FieldSymbol,
  :: IclModule, :: DclModule, :: FunDef, :: Optional, :: SymbolType, :: LetBind,
  :: ModuleN, :: Type
from checksupport import :: Heaps
from Data.Graph import :: Graph
from Data.Maybe import :: Maybe
from Text.JSON import generic JSONEncode, :: JSONNode
from Data.Map import :: Map
from predef import :: PredefinedSymbol, :: PredefinedSymbols
from iTasks.Framework.Tonic.AbsSyn import :: TExpr, :: ExprId, :: TypeName, :: ModuleName, :: TaskName, :: VariableName

At e es :== e @ es

:: *ExpressionAlg inh *chn syn =
  {  var                   :: BoundVar inh chn -> *(syn, chn)                                                                  // Var
  ,  app                   :: App inh chn -> *(syn, chn)                                                                       // App
  ,  at                    :: Expression [Expression] inh chn -> *(syn, chn)                                                   // (@)
  ,  letE                  :: Let inh chn -> *(syn, chn)                                                                       // Let
  ,  caseE                 :: Case inh chn -> *(syn, chn)                                                                      // Case
  ,  selection             :: SelectorKind Expression [Selection] inh chn -> *(syn, chn)                                       // Selection
  ,  update                :: Expression [Selection] Expression inh chn -> *(syn, chn)                                         // Update
  ,  recordUpdate          :: (Global DefinedSymbol) Expression [Bind Expression (Global FieldSymbol)] inh chn -> *(syn, chn)  // RecordUpdate
  ,  tupleSelect           :: DefinedSymbol Int Expression inh chn -> *(syn, chn)                                              // TupleSelect
  ,  basicExpr             :: BasicValue inh chn -> *(syn, chn)                                                                // BasicExpr
  ,  conditional           :: Conditional inh chn -> *(syn, chn)                                                               // Conditional
  ,  anyCodeExpr           :: (CodeBinding BoundVar) (CodeBinding FreeVar) [String] inh chn -> *(syn, chn)                     // AnyCodeExpr
  ,  abcCodeExpr           :: [String] Bool inh chn -> *(syn, chn)                                                             // ABCCodeExpr
  ,  matchExpr             :: (Global DefinedSymbol) Expression inh chn -> *(syn, chn)                                         // MatchExpr
  ,  isConstructor         :: Expression (Global DefinedSymbol) Int GlobalIndex Ident Position inh chn -> *(syn, chn)          // IsConstructor
  ,  freeVar               :: FreeVar inh chn -> *(syn, chn)                                                                   // FreeVar
  ,  dictionariesFunction  :: [(FreeVar,AType)] Expression AType inh chn -> *(syn, chn)                                        // DictionariesFunction
  ,  constant              :: SymbIdent Int Priority inh chn -> *(syn, chn)                                                    // Constant
  ,  classVariable         :: VarInfoPtr inh chn -> *(syn, chn)                                                                // ClassVariable
  ,  dynamicExpr           :: DynamicExpr inh chn -> *(syn, chn)                                                               // DynamicExpr
  ,  typeCodeExpression    :: TypeCodeExpression inh chn -> *(syn, chn)                                                        // TypeCodeExpression
  ,  typeSignature         :: (Int Int -> (AType,Int,Int)) Expression inh chn -> *(syn, chn)                                   // TypeSignature
  ,  ee                    :: inh chn -> *(syn, chn)                                                                           // EE
  ,  noBind                :: ExprInfoPtr inh chn -> *(syn, chn)                                                               // NoBind
  ,  failExpr              :: Ident inh chn -> *(syn, chn)                                                                     // FailExpr
  }

// InhExpression and ChnExpression need strict fields in order to prevent a bus
// error caused by huge thunks
:: InhExpression =
  { inh_curr_task_name  :: !String
  , inh_case_expr       :: !Maybe Expression
  , inh_is_bind_lam     :: !Bool
  , inh_ids             :: !ExprId
  , inh_tyenv           :: !Map String Type
  }

:: *ChnExpression =
  {// chn_graph          :: !*GinGraph
    chn_module_env     :: !*ModuleEnv
  , chn_heaps          :: *Heaps
  , chn_predef_symbols :: !*PredefinedSymbols
  }

:: SynExpression =
  { syn_texpr      :: !TExpr
  , syn_annot_expr :: !Expression
  }

:: *ModuleEnv =
  { me_main_dcl_module_n  :: !Int
  , me_fun_defs           :: !*{#FunDef}
  , me_fun_defs_cpy       :: !*{#FunDef}
  , me_icl_module         :: !IclModule
  , me_dcl_modules        :: !{#DclModule}
  }

exprCata :: *(ExpressionAlg inh *chn syn) Expression inh *chn -> *(syn, *chn)

mkInhExpr :: String -> InhExpression

mkChnExpr :: *PredefinedSymbols *ModuleEnv *Heaps -> *ChnExpression

mkModuleEnv :: ModuleN !*{#FunDef} !*{#FunDef} IclModule {#DclModule} -> *ModuleEnv
