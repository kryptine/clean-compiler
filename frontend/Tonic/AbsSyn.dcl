definition module Tonic.AbsSyn

from syntax import :: Expression (..), :: BoundVar, :: App {..}, :: Let, :: Case,
  :: SelectorKind, :: Selection, :: FreeVar {..}, :: Global, :: SymbIdent, :: Priority,
  :: VarInfoPtr, :: DynamicExpr, :: Ptr, :: VarInfo, :: CodeBinding, :: DefinedSymbol,
  :: Bind, :: Position, :: AType, :: Env, :: Ident, :: Level, :: ExprInfoPtr, :: ExprInfo,
  :: TypeCodeExpression, :: GlobalIndex, :: Conditional, :: BasicValue, :: FieldSymbol,
  :: IclModule, :: DclModule, :: FunDef, :: Optional, :: SymbolType, :: LetBind
from Data.Graph import :: Graph
from Data.Maybe import :: Maybe

At e es :== e @ es

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

// InhExpression and SynExpression need strict fields in order to prevent a bus
// error caused by huge thunks
:: InhExpression =
  {  inh_module_env      :: !ModuleEnv
  ,  inh_graph           :: !GinGraph
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

:: ModuleEnv =
  { me_fun_defs     :: !{#FunDef}
  , me_icl_module   :: !IclModule
  , me_dcl_modules  :: !{#DclModule}
  }

:: GFunDef =
  {  gfd_name      :: !String
  ,  gfd_args      :: ![FreeVar]
  ,  gfd_rhs       :: !Expression
  ,  gfd_type      :: !Optional SymbolType
  ,  gfd_priority  :: Priority
  }

:: GinGraph :== Graph GNode GEdge

:: GPattern :== String

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
  |  GListComprehension

:: GJoinType
  =  DisFirstBin
  |  DisFirstList
  |  DisLeft
  |  DisRight
  |  ConAll
  |  ConPair

:: GEdge = { edge_pattern :: !Maybe GPattern }

:: GGraph = GGraph GinGraph

exprCata :: (ExpressionAlg a) Expression -> a

mkExprAlg :: a -> ExpressionAlg a

mkSynExpr :: (Maybe Int) GinGraph -> SynExpression

mkSynExpr` :: GinGraph -> SynExpression

mkInhExpr :: ModuleEnv GinGraph Int String (Maybe Expression) -> InhExpression

mkModuleEnv :: {#FunDef} IclModule {#DclModule} -> ModuleEnv

mkGLet :: InhExpression Let -> GLet

mkGLetBind :: String Expression -> GLetBind

mkGLetBinds :: InhExpression LetBind -> GLetBind

mkGFunDef :: FunDef -> GFunDef

emptyEdge :: GEdge

mkEdge :: String -> GEdge










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
  //|  GListComprehensionExpression GListComprehension
  |  GCleanExpression GCleanExpression

:: GCleanExpression :== String

//:: GListComprehension =
  //{  output    :: GExpression
  //,  guard     :: Maybe GCleanExpression
  //,  selector  :: GPattern
  //,  input     :: GExpression
  //}

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
